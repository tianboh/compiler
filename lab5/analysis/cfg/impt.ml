(* Implementation for CFG wrapper
 * Provide a instruction module following
 * Sig.InstrInterface, return a module with
 * CFG helper functions.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu> 
 *)

module Label = Util.Label
open Core

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

  let entry_label = Label.label (Some "entry")
  let exit_label = Label.label (Some "exit")
  let get_entry (bbs : bbmap) : bb = Label.Map.find_exn bbs entry_label
  let get_exit (bbs : bbmap) : bb = Label.Map.find_exn bbs exit_label

  let add_entry_exit (instrs : i list) =
    (I.label entry_label :: instrs) @ [ I.label exit_label ]

  (* Make sure no fallthrough between basic blocks. 
   * Add unconditional jump instr if fallthrough is detected. *)
  let rec eliminate_fallthrough (acc_instrs : i list) (instrs : i list) : i list
      =
    match instrs with
    | [] -> List.rev acc_instrs
    | h :: t ->
        if I.is_label h then
          match acc_instrs with
          (* h is entry label *)
          | [] -> eliminate_fallthrough (h :: acc_instrs) t
          | prev_instr :: _ ->
              if
                I.is_jump prev_instr || I.is_cjump prev_instr
                || I.is_return prev_instr
              then eliminate_fallthrough (h :: acc_instrs) t
              else
                let jump_instr = I.jump (I.get_label h) in
                eliminate_fallthrough (h :: jump_instr :: acc_instrs) t
        else eliminate_fallthrough (h :: acc_instrs) t

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
              _build_bb t [ h ] (Some l) bbs
        else _build_bb t (h :: bb_instrs) bb_label bbs

  (* update predecessors and successors for each bb *)
  let rec _build_ps (label_order : Label.t list) (bbmap : bbmap) : bbmap =
    match label_order with
    | [] -> bbmap
    | h :: t ->
        let bb = Label.Map.find_exn bbmap h in
        let succs =
          List.fold_left bb.instrs ~init:[] ~f:(fun acc h ->
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
                | None -> failwith "Predecessor bb not found"))
        in
        _build_ps t bbmap

  (* Block with no successor is predecessor of exit block. This happens
   * when block is terminated with a return instruction.
   * Their successors will be updated, but no jump instruction is added. *)
  let _handl_exit (bbmap : bbmap) : bbmap =
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
  let build_bb (instrs : i list) : bbmap =
    let instrs = add_entry_exit instrs |> eliminate_fallthrough [] in
    let bbs = Label.Map.empty in
    let label_order =
      List.fold_left instrs ~init:[] ~f:(fun acc h ->
          if I.is_label h then I.get_label h :: acc else acc)
      |> List.rev
    in
    let bbmap =
      _build_bb instrs [] None bbs |> _build_ps label_order |> _handl_exit
    in
    bbmap

  let to_instrs (bbs : bbmap) (order : Label.t list) =
    List.map order ~f:(fun l ->
        let bb = Label.Map.find_exn bbs l in
        bb.instrs)
    |> List.concat
end
