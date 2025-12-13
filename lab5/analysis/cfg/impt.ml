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
  let legalize (_bbmap : bbmap) (_order : Label.t list) : bbmap * Label.t list =
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

  (* Build basic blocks with entry and exit block *)
  let build_bb (instrs : i list) : bbmap * Label.t list =
    let label_order =
      List.fold_left instrs ~init:[] ~f:(fun acc h ->
          if I.is_label h then I.get_label h :: acc else acc)
      |> List.rev
    in
    let bbmap = _build_bb instrs [] None Label.Map.empty in
    let entry_block =
      {
        label = entry_label;
        instrs = [];
        preds = [];
        succs = [ List.hd_exn label_order ];
      }
    in
    let exit_block =
      { label = exit_label; instrs = []; preds = []; succs = [] }
    in
    let bbmap =
      bbmap
      |> Label.Map.set ~key:entry_label ~data:entry_block
      |> Label.Map.set ~key:exit_label ~data:exit_block
    in
    (* List.iter instrs ~f:(fun instr -> printf "%s\n%!" (I.pp_inst instr)); *)
    let bbmap =
      bbmap
      |> _build_ps ((entry_label :: label_order) @ [ exit_label ])
      |> _handle_exit
    in
    let order = (entry_label :: label_order) @ [ exit_label ] in
    legalize bbmap order

  let to_instrs (bbs : bbmap) (order : Label.t list) =
    List.map order ~f:(fun l ->
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
