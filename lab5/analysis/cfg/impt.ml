(* Implementation for CFG wrapper
 * Provide a instruction module following
 * Sig.InstrInterface, return a module with
 * CFG helper functions.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu> 
 *)

module Label = Util.Label
open Core

let entry_label = Label.label (Some "entry")
let exit_label = Label.label (Some "exit")

module Wrapper (I : Sig.InstrInterface) : Sig.CFGInterface with type i = I.t =
struct
  type set = Label.Set.t
  type map = set Label.Map.t
  type i = I.t

  type bb = {
    label : Label.t;
    instrs : i list;
    preds : Label.t list;
    succs : Label.t list;
  }

  type bbmap = bb Label.Map.t

  let get_entry_bb (bbs : bbmap) : bb = Label.Map.find_exn bbs entry_label
  let get_exit_bb (bbs : bbmap) : bb = Label.Map.find_exn bbs exit_label
  let pp_inst (instr : i) : string = I.pp_inst instr

  let pp_bb (bb : bb) : unit =
    printf "====== %s =====\n%!" (Label.name bb.label);
    printf "instrs:\n%!";
    List.iter bb.instrs ~f:(fun instr -> printf "\t%s\n%!" (pp_inst instr));
    printf "preds:\n%!";
    List.iter bb.preds ~f:(fun pred -> printf "\t%s%!" (Label.name pred));
    printf "\n%!";
    printf "succs:\n%!";
    List.iter bb.succs ~f:(fun succ -> printf "\t%s%!" (Label.name succ));
    printf "\n\n%!"

  let pp_bbmap (bbmap : bbmap) : unit =
    Label.Map.iter bbmap ~f:(fun bb -> pp_bb bb)

  (* Remove illegal format, including
   * 1. Unreachable block.
   *)
  let post_legalize (_bbmap : bbmap) (_order : Label.t list) :
      bbmap * Label.t list =
    let (visited : Label.Set.t ref) = ref Label.Set.empty in
    let rec dfs (u : Label.t) : unit =
      if not (Label.Set.mem !visited u) then (
        visited := Label.Set.add !visited u;
        let bb = Label.Map.find_exn _bbmap u in
        List.iter bb.succs ~f:(fun succ -> dfs succ))
    in
    dfs entry_label;
    let (legal_bbmap : bbmap ref) = ref Label.Map.empty in
    let (legal_order : Label.t list ref) = ref [] in
    legal_order :=
      List.filter _order ~f:(fun label -> Label.Set.mem !visited label);
    List.iter !legal_order ~f:(fun label ->
        let bb = Label.Map.find_exn _bbmap label in
        let preds =
          List.filter bb.preds ~f:(fun pred -> Label.Set.mem !visited pred)
        in
        let succs =
          List.filter bb.succs ~f:(fun succ -> Label.Set.mem !visited succ)
        in
        legal_bbmap :=
          Label.Map.set !legal_bbmap ~key:label ~data:{ bb with preds; succs });
    (!legal_bbmap, !legal_order)

  (* Build a basic block, and add label, instrs info. preds and succss
   * is addad later in _build_ps *)
  let rec _build_bb (instrs : i list) (bb_instrs : i list)
      (bb_label : Label.t option) (bbs : bbmap) : bbmap =
    match instrs with
    | [] -> (
        match bb_label with
        | None -> bbs
        | Some l ->
            let bb =
              { label = l; instrs = List.rev bb_instrs; preds = []; succs = [] }
            in
            let bbs = Label.Map.set bbs ~key:l ~data:bb in
            bbs)
    | h :: t ->
        if I.is_label h then
          match bb_label with
          | None -> _build_bb t [ h ] (Some (I.get_label h)) bbs
          | Some l ->
              let bb =
                {
                  label = l;
                  instrs = List.rev bb_instrs;
                  preds = [];
                  succs = [];
                }
              in
              let bbs = Label.Map.set bbs ~key:l ~data:bb in
              _build_bb t [ h ] (Some (I.get_label h)) bbs
        else _build_bb t (h :: bb_instrs) bb_label bbs

  (* update predecessors and successors for each bb *)
  let rec _build_ps (label_order : Label.t list) (bbmap : bbmap) : bbmap =
    match label_order with
    | [] -> bbmap
    | h :: t ->
        let bb = Label.Map.find_exn bbmap h in
        let succs =
          List.fold_left bb.instrs ~init:bb.succs ~f:(fun acc h ->
              if I.is_jump h || I.is_cjump h then I.get_targets h @ acc else acc)
        in
        (* Update successor fields of bb *)
        let bbmap =
          Label.Map.update bbmap h ~f:(function
            | Some bb -> { bb with succs }
            | None -> failwith "update non-exist label")
        in
        (* Update predecessor field of bb's successor *)
        let bbmap =
          List.fold_left succs ~init:bbmap ~f:(fun acc_map succ ->
              Label.Map.update acc_map succ ~f:(function
                | Some succ_bb -> { succ_bb with preds = h :: succ_bb.preds }
                | None ->
                    let err_msg = sprintf "bb %s not found" (Label.name succ) in
                    failwith err_msg))
        in
        _build_ps t bbmap

  (* Block with no successor is predecessor of exit block. This happens
   * when block is terminated with a return instruction.
   * Their successors will be updated, but no jump instruction is added. *)
  let _handle_exit (bbmap : bbmap) : bbmap =
    (* Gather blocks with no successors. *)
    let non_succ_bb_list =
      Label.Map.fold bbmap ~init:[] ~f:(fun ~key:_ ~data acc ->
          if List.is_empty data.succs && not (Label.equal data.label exit_label)
          then data :: acc
          else acc)
    in
    (* Update these block successors field and exit block predecessor field *)
    List.fold_left non_succ_bb_list ~init:bbmap ~f:(fun acc_map bb ->
        let new_succs = exit_label :: bb.succs in
        let acc_map =
          Label.Map.update acc_map bb.label ~f:(function
            | Some bb -> { bb with succs = new_succs }
            | None -> failwith "update non-exist label")
        in
        Label.Map.update acc_map exit_label ~f:(function
          | Some exit_bb -> { exit_bb with preds = bb.label :: exit_bb.preds }
          | None -> failwith "update non-exist label"))

  let eliminate_fall_through (instrs : I.t list) : I.t list =
    let rec helper (acc_instrs : I.t list) (instrs : I.t list) : I.t list =
      match instrs with
      | [] -> List.rev acc_instrs
      | h :: t ->
          if I.is_label h then
            match acc_instrs with
            (* h is entry label *)
            | [] -> helper (h :: acc_instrs) t
            | prev_instr :: _ ->
                if
                  I.is_jump prev_instr || I.is_cjump prev_instr
                  || I.is_return prev_instr
                then helper (h :: acc_instrs) t
                else
                  let jump_instr = I.gen_jump (I.get_label h) in
                  helper (h :: jump_instr :: acc_instrs) t
          else helper (h :: acc_instrs) t
    in
    helper [] instrs

  let rec add_synthetic_label (next_synth_id : int) (acc_instrs : I.t list)
      (instrs : I.t list) : I.t list =
    match instrs with
    | [] -> List.rev acc_instrs
    | h :: t ->
        if I.is_terminator h then
          match t with
          | [] -> List.rev (h :: acc_instrs)
          | next :: _ ->
              if I.is_label next then
                add_synthetic_label next_synth_id (h :: acc_instrs) t
              else
                let synth_label =
                  Label.label (Some ("synth" ^ string_of_int next_synth_id))
                in
                let synth_label_instr = I.gen_label synth_label in
                add_synthetic_label (next_synth_id + 1) (h :: acc_instrs)
                  (synth_label_instr :: t)
        else add_synthetic_label next_synth_id (h :: acc_instrs) t

  let split_id = ref 0

  (* Make sure each terminator is followed by a label. If not, add a synthetic label after it 
   * This function ensures even unreachable instructions have a label, therefore they are
   * in their own block. *)

  let has_edge (u_label : Label.t) (v_label : Label.t) (bbmap : bbmap) : bool =
    let u_bb = Label.Map.find_exn bbmap u_label in
    List.mem u_bb.succs v_label ~equal:Label.equal

  let is_critical_edge (u_label : Label.t) (v_label : Label.t) (bbmap : bbmap) :
      bool =
    let u_bb = Label.Map.find_exn bbmap u_label in
    let v_bb = Label.Map.find_exn bbmap v_label in
    let edge_uv_exist = has_edge u_label v_label bbmap in
    let src_has_multi_dests =
      if List.length u_bb.succs > 1 then true else false
    in
    let dest_has_multi_srcs =
      if List.length v_bb.preds > 1 then true else false
    in
    edge_uv_exist && src_has_multi_dests && dest_has_multi_srcs

  let split_edge (u_label : Label.t) (v_label : Label.t) (bbmap : bbmap) :
      bbmap * Label.t =
    let u_bb_old = Label.Map.find_exn bbmap u_label in
    let v_bb_old = Label.Map.find_exn bbmap v_label in
    assert (has_edge u_label v_label bbmap);
    let label_name = sprintf "split_%d" !split_id in
    split_id := !split_id + 1;
    let new_label = Label.label' label_name in
    let new_bb : bb =
      {
        label = new_label;
        instrs = [ I.gen_label new_label; I.gen_jump v_label ];
        preds = [ u_label ];
        succs = [ v_label ];
      }
    in
    let u_bb_instrs =
      List.fold_left u_bb_old.instrs ~init:[] ~f:(fun acc instr ->
          let new_instr =
            if
              I.is_jump instr
              && List.mem (I.get_targets instr) v_label ~equal:Label.equal
            then I.replace_target instr new_label
            else if
              I.is_cjump instr
              && List.mem (I.get_targets instr) v_label ~equal:Label.equal
            then I.replace_ctarget instr v_label new_label
            else instr
          in
          new_instr :: acc)
      |> List.rev
    in
    let u_bb_new_succs =
      new_label
      :: List.filter u_bb_old.succs ~f:(fun x -> not (Label.equal x v_label))
    in
    let u_bb_new =
      { u_bb_old with instrs = u_bb_instrs; succs = u_bb_new_succs }
    in
    let v_bb_new_preds =
      new_label
      :: List.filter v_bb_old.preds ~f:(fun x -> not (Label.equal x u_label))
    in
    let v_bb_new = { v_bb_old with preds = v_bb_new_preds } in
    let bbmap = Label.Map.set bbmap ~key:u_label ~data:u_bb_new in
    let bbmap = Label.Map.set bbmap ~key:v_label ~data:v_bb_new in
    let bbmap = Label.Map.set bbmap ~key:new_label ~data:new_bb in
    (bbmap, new_label)

  let split_critical_edges (bbmap : bbmap) (orders : Label.t list) :
      bbmap * Label.t list =
    let critical_edges : (Label.t * Label.t) list =
      List.fold_right orders ~init:[] ~f:(fun u_label acc ->
          let u_bb = Label.Map.find_exn bbmap u_label in
          List.fold_right u_bb.succs ~init:acc ~f:(fun v_label acc_inner ->
              if is_critical_edge u_label v_label bbmap then
                (u_label, v_label) :: acc_inner
              else acc_inner))
    in
    List.fold_left critical_edges ~init:(bbmap, orders)
      ~f:(fun (current_bbmap, current_orders) edge ->
        let u_label, v_label = edge in
        let new_bbmap, new_label = split_edge u_label v_label current_bbmap in
        let new_orders =
          List.fold_right current_orders ~init:[] ~f:(fun l acc ->
              if Label.equal l u_label then l :: new_label :: acc else l :: acc)
        in
        (new_bbmap, new_orders))

  let pre_legalize (_instrs : i list) : i list =
    eliminate_fall_through _instrs |> add_synthetic_label 0 []

  (* Build basic blocks with entry and exit block *)
  let build_bb (_instrs : i list) : bbmap * Label.t list =
    let instrs_w_ee =
      (I.gen_label entry_label :: _instrs) @ [ I.gen_label exit_label ]
    in
    let instrs = pre_legalize instrs_w_ee in
    let orders =
      List.fold_left instrs ~init:[] ~f:(fun acc h ->
          if I.is_label h then I.get_label h :: acc else acc)
      |> List.rev
    in
    let bbmap = _build_bb instrs [] None Label.Map.empty in
    let bbmap, orders = split_critical_edges bbmap orders in
    (* List.iter instrs ~f:(fun instr -> printf "%s\n%!" (I.pp_inst instr)); *)
    let bbmap = bbmap |> _build_ps orders |> _handle_exit in
    post_legalize bbmap orders

  let to_instrs (bbs : bbmap) (order : Label.t list) =
    List.filter order ~f:(fun label ->
        if Label.equal label entry_label || Label.equal label exit_label then
          false
        else true)
    |> List.map ~f:(fun l ->
           let bb = Label.Map.find_exn bbs l in
           bb.instrs)
    |> List.concat

  let get_rpo (bbs : bbmap) : Label.t list =
    let entry = get_entry_bb bbs in
    let visited = ref Label.Set.empty in
    let order = ref [] in
    let rec dfs (u_label : Label.t) : unit =
      if not (Label.Set.mem !visited u_label) then (
        visited := Label.Set.add !visited u_label;
        let u_bb = Label.Map.find_exn bbs u_label in
        List.iter u_bb.succs ~f:dfs;
        order := u_label :: !order)
    in
    dfs entry.label;
    !order
end
