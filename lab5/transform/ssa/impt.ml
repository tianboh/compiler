(*
 * Minimal SSA
 *
 * We use dominance frontier to construct minimal SSA. We only insert phi function 
 * for variables at dominance frontier.
 *
 * Alg paper: An Efficient Method of Computing Static Single Assignment Form  
 * Check https://dl.acm.org/doi/pdf/10.1145/75277.75280 for details
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

module Label = Util.Label
module Temp = Var.Temp
open Core

module Make
    (Instr : Sig.SSAInstrInterface)
    (Cfg : Analysis_cfg.Sig.CFGInterface with type i = Instr.instr)
    (Dom : Analysis_dominator.Sig.DominatorInterface with type bbmap = Cfg.bbmap) =
struct
  type phi = { dst : Temp.t; srcs : Temp.t Label.Map.t }
  type ssa_instr = Phi of phi | Instr of Instr.instr

  type ssa_bb = {
    label : Label.t;
    instrs : ssa_instr list;
    preds : Label.t list;
    succs : Label.t list;
  }

  type ssa_bbmap = ssa_bb Label.Map.t

  let get_defs (instr : ssa_instr) : Temp.t list =
    match instr with Phi p -> [ p.dst ] | Instr i -> Instr.get_defs i

  let get_uses (instr : ssa_instr) : Temp.t list =
    match instr with
    | Phi p ->
        Label.Map.fold p.srcs ~init:[] ~f:(fun ~key:_ ~data:t acc -> t :: acc)
    | Instr i -> Instr.get_uses i

  (* Collect every definition of temp. Key is temp, value is definition set. *)
  let collect_tmap (bbmap : Cfg.bbmap) : Label.Set.t Temp.Map.t =
    let tmap = ref Temp.Map.empty in
    Label.Map.iteri bbmap ~f:(fun ~key:label ~data:bb ->
        List.iter bb.instrs ~f:(fun instr ->
            List.iter (Instr.get_defs instr) ~f:(fun temp ->
                tmap :=
                  Temp.Map.update !tmap temp ~f:(function
                    | None -> Label.Set.singleton label
                    | Some set -> Label.Set.add set label))));
    !tmap

  (* This function only insert phi function for temporary. It does not rename
   * any other temporary name in neither LHS nor RHS. This is minimal SSA, 
   * so phi func is only inserted at dominance frontier.*)
  let insert_phi (temp : Temp.t) (defs : Label.Set.t) (bbmap : ssa_bbmap)
      (frontier : Label.Set.t Label.Map.t) : ssa_bbmap =
    let worklist = ref [] in
    let phi_guard = ref Label.Set.empty in
    let worklist_guard = ref Label.Set.empty in
    let ssa_bbmap = ref bbmap in
    Label.Set.iter defs ~f:(fun def ->
        worklist := def :: !worklist;
        worklist_guard := Label.Set.add !worklist_guard def);
    while not (List.is_empty !worklist) do
      let head = List.hd_exn !worklist in
      worklist := List.tl_exn !worklist;
      let head_frontier =
        match Label.Map.find frontier head with
        | Some s -> s
        | None -> Label.Set.empty
      in
      Label.Set.iter head_frontier ~f:(fun node ->
          if not (Label.Set.mem !phi_guard node) then (
            let phi_instr = Phi { dst = temp; srcs = Label.Map.empty } in
            let ssa_bb = Label.Map.find_exn !ssa_bbmap node in
            ssa_bbmap :=
              Label.Map.set !ssa_bbmap ~key:node
                ~data:{ ssa_bb with instrs = phi_instr :: ssa_bb.instrs };
            phi_guard := Label.Set.add !phi_guard node;
            if not (Label.Set.mem !worklist_guard node) then (
              worklist := node :: !worklist;
              worklist_guard := Label.Set.add !worklist_guard node)))
    done;
    !ssa_bbmap

  let rename (ssa_bbmap_init : ssa_bbmap) (entry : Label.t)
      (dom_tree_rev : Label.Set.t Label.Map.t) : ssa_bbmap =
    let (stack : Temp.t list Temp.Map.t ref) = ref Temp.Map.empty in
    let ssa_bbmap = ref ssa_bbmap_init in
    let (root_map : Temp.t Temp.Map.t ref) = ref Temp.Map.empty in
    let init () : unit =
      Label.Map.iter !ssa_bbmap ~f:(fun ssa_bb ->
          List.iter ssa_bb.instrs ~f:(fun instr ->
              let defs =
                match instr with
                | Phi phi -> [ phi.dst ]
                | Instr i -> Instr.get_defs i
              in
              List.iter defs ~f:(fun t ->
                  stack :=
                    Temp.Map.update !stack t ~f:(function
                      | None -> [ t ]
                      | Some i -> i);
                  root_map :=
                    Temp.Map.update !root_map t ~f:(function
                      | None -> t
                      | Some t -> t))))
    in
    let rec search (bb_label : Label.t) (dom_tree_rev : Label.Set.t Label.Map.t)
        : unit =
      (* First handle within current block *)
      let bb = Label.Map.find_exn !ssa_bbmap bb_label in
      let renamed_instrs =
        List.fold_left bb.instrs ~init:[] ~f:(fun acc_instrs instr ->
            (* Rename RHS *)
            let renamed_instr =
              match instr with
              | Phi phi -> Phi phi
              | Instr i ->
                  let uses = Instr.get_uses i in
                  Instr
                    (List.fold_left uses ~init:i ~f:(fun acc temp ->
                         let temp_root = Temp.Map.find_exn !root_map temp in
                         let temp_stack = Temp.Map.find_exn !stack temp_root in
                         let temp_top = List.hd_exn temp_stack in
                         Instr.replace_temp acc temp temp_top))
            in
            (* Rename LHS *)
            let defs =
              match instr with
              | Phi phi -> [ phi.dst ]
              | Instr i -> Instr.get_defs i
            in
            let renamed_instr =
              List.fold_left defs ~init:renamed_instr ~f:(fun acc temp ->
                  let temp_root = Temp.Map.find_exn !root_map temp in
                  let new_temp = Temp.create temp_root.size in
                  root_map :=
                    Temp.Map.set !root_map ~key:new_temp ~data:temp_root;
                  stack :=
                    Temp.Map.update !stack temp_root ~f:(function
                      | None -> failwith "expect valid temp root"
                      | Some s -> new_temp :: s);
                  match acc with
                  | Phi phi -> Phi { phi with dst = new_temp }
                  | Instr i -> Instr (Instr.replace_temp i temp new_temp))
            in
            renamed_instr :: acc_instrs)
        |> List.rev
      in
      ssa_bbmap :=
        Label.Map.update !ssa_bbmap bb_label ~f:(function
          | None -> failwith "expect valid bb in search"
          | Some ssa_bbmap -> { ssa_bbmap with instrs = renamed_instrs });
      (* Then update successor *)
      List.iter bb.succs ~f:(fun succ_label ->
          let succ_bb = Label.Map.find_exn !ssa_bbmap succ_label in
          let instrs =
            List.fold_left succ_bb.instrs ~init:[] ~f:(fun acc_instrs instr ->
                match instr with
                | Phi phi ->
                    let srcs_old = phi.srcs in
                    let temp_root = Temp.Map.find_exn !root_map phi.dst in
                    let temp_stack = Temp.Map.find_exn !stack temp_root in
                    let temp_top = List.hd_exn temp_stack in
                    let srcs =
                      Label.Map.set srcs_old ~key:bb_label ~data:temp_top
                    in
                    Phi { phi with srcs } :: acc_instrs
                | Instr i -> Instr i :: acc_instrs)
            |> List.rev
          in
          let succ_bb_new = { succ_bb with instrs } in
          ssa_bbmap :=
            Label.Map.set !ssa_bbmap ~key:succ_label ~data:succ_bb_new);
      (* Recursive call children in dom tree *)
      let children =
        match Label.Map.find dom_tree_rev bb_label with
        | None -> Label.Set.empty
        | Some s -> s
      in
      Label.Set.iter children ~f:(fun child_label ->
          (* entry block's children in rev idom tree have itself. We don't want infinite loop *)
          if not (Label.equal bb_label child_label) then
            search child_label dom_tree_rev);
      (* Current block process finished, pop current defined temp from stack *)
      List.iter bb.instrs ~f:(fun instr ->
          let defs =
            match instr with
            | Phi phi -> [ phi.dst ]
            | Instr i -> Instr.get_defs i
          in
          List.iter defs ~f:(fun temp ->
              let temp_root = Temp.Map.find_exn !root_map temp in
              let temp_stack_old = Temp.Map.find_exn !stack temp_root in
              let temp_stack = List.tl_exn temp_stack_old in
              stack := Temp.Map.set !stack ~key:temp_root ~data:temp_stack))
    in
    init ();
    search entry dom_tree_rev;
    !ssa_bbmap

  let to_ssa (bbmap : Cfg.bbmap) : ssa_bbmap =
    (* Cfg.pp_bbmap bbmap; *)
    let dom_tree = Dom.build_dt bbmap in
    let frontier = Dom.build_df bbmap dom_tree in
    let (dom_tree_rev : Label.Set.t Label.Map.t ref) = ref Label.Map.empty in
    Label.Map.iteri dom_tree ~f:(fun ~key:bb ~data:idom ->
        dom_tree_rev :=
          Label.Map.update !dom_tree_rev idom ~f:(function
            | None -> Label.Set.singleton bb
            | Some set -> Label.Set.add set bb));
    let tmap = collect_tmap bbmap in
    let ssa_bbmap : ssa_bbmap =
      Label.Map.map bbmap ~f:(fun bb ->
          let ssa_instrs = List.map bb.instrs ~f:(fun instr -> Instr instr) in
          {
            label = bb.label;
            instrs = ssa_instrs;
            preds = bb.preds;
            succs = bb.succs;
          })
    in
    let ssa_bbmap_init =
      Temp.Map.fold tmap ~init:ssa_bbmap ~f:(fun ~key:temp ~data:defs acc ->
          insert_phi temp defs acc frontier)
    in
    let entry_bb = Cfg.get_entry_bb bbmap in
    rename ssa_bbmap_init entry_bb.label !dom_tree_rev

  let from_ssa (bbmap : ssa_bbmap) : Cfg.bbmap =
    (* Store (src, dst) pairs to handle parallel copies correctly *)
    let (phi_moves : (Temp.t * Temp.t) list Label.Map.t ref) =
      ref Label.Map.empty
    in
    Label.Map.iter bbmap ~f:(fun ssa_bb ->
        List.iter ssa_bb.instrs ~f:(function
          | Instr _ -> ()
          | Phi phi ->
              let dst = phi.dst in
              Label.Map.iteri phi.srcs ~f:(fun ~key:pred_label ~data:src ->
                  let moves =
                    match Label.Map.find !phi_moves pred_label with
                    | None -> []
                    | Some s -> s
                  in
                  phi_moves :=
                    Label.Map.set !phi_moves ~key:pred_label
                      ~data:((src, dst) :: moves))));
    let (ret : Cfg.bbmap ref) = ref Label.Map.empty in
    Label.Map.iteri bbmap ~f:(fun ~key:label ~data:ssa_bb ->
        let moves_pairs =
          match Label.Map.find !phi_moves label with None -> [] | Some s -> s
        in
        (* Generate moves using temps to handle parallel copies (swaps) *)
        let reads, writes =
          List.fold_left moves_pairs ~init:([], [])
            ~f:(fun (acc_r, acc_w) (src, dst) ->
              let tmp = Temp.create dst.size in
              let read = Instr.gen_mov src tmp in
              let write = Instr.gen_mov tmp dst in
              (read :: acc_r, write :: acc_w))
        in
        let movs = List.rev reads @ List.rev writes in
        let (instrs_rev : Instr.instr list) =
          List.rev
            (List.filter_map ssa_bb.instrs ~f:(function
              | Phi _ -> None
              | Instr i -> Some i))
        in
        let terminator, body_rev =
          match instrs_rev with
          | [] -> failwith "Block must have at least one instruction"
          | last :: rest -> (last, rest)
        in
        (* Insert moves BEFORE the terminator *)
        let instrs = List.rev body_rev @ movs @ [ terminator ] in
        let (bb : Cfg.bb) =
          { label; preds = ssa_bb.preds; succs = ssa_bb.succs; instrs }
        in
        ret := Label.Map.set !ret ~key:label ~data:bb);
    !ret

  let print_ssa_instr (instr : ssa_instr) : unit =
    let () =
      match instr with
      | Instr i -> printf "%s" (Instr.pp_inst i)
      | Phi phi ->
          printf "%s = " (Temp.name phi.dst);
          Label.Map.iteri phi.srcs ~f:(fun ~key:branch ~data ->
              printf "%s %s, " (Label.name branch) (Temp.name data))
    in
    printf "\n"

  let print_ssa_bbmap (ssa_bbmap : ssa_bbmap) : unit =
    Label.Map.iter ssa_bbmap ~f:(fun ssa_bb ->
        printf "%s\n" (Label.name ssa_bb.label);
        List.iter ssa_bb.instrs ~f:(fun instr ->
            printf "\t";
            print_ssa_instr instr))
end
