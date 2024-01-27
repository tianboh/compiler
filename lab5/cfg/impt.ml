(* Implementation for CFG wrapper
 * Provide a instruction module following
 * Sig.InstrInterface, return a module with
 * CFG helper functions.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu> 
 *)
[@@@warning "-27"]
[@@@warning "-39"]
[@@@warning "-32"]

module Label = Util.Label
open Core

module Wrapper (I : Sig.InstrInterface) : Sig.CFGInterface with type i = I.t = struct
  type set = Label.Set.t
  type map = set Label.Map.t
  type i = I.t

  type bb =
    { label : Label.t
    ; instrs : i list
    }

  type bbmap = bb Label.Map.t

  let entry_label = Label.label (Some "entry")
  let exit_label = Label.label (Some "exit")
  let entry_bb = { label = entry_label; instrs = [ I.label entry_label ] }
  let exit_bb = { label = exit_label; instrs = [ I.label exit_label ] }
  let get_entry () : bb = entry_bb
  let get_exit () : bb = exit_bb
  let add_entry_exit (instrs : i list) = entry_bb.instrs @ instrs @ exit_bb.instrs

  (* A basic block should end up with one of following possibilities
   * 1) Jump or conditional jump
   * 2) Return 
   *)
  let has_fall_through (instrs : i list) (pre_opt : i option) : bool =
    let rec helper (instrs : i list) (pre_opt : i option) (res : bool) : bool =
      match instrs with
      | [] -> res
      | h :: t ->
        if I.is_label h
        then (
          match pre_opt with
          | None -> if List.length t > 0 then helper t (Some h) res else false
          | Some pre ->
            if I.is_jump pre || I.is_return pre
            then helper t (Some h) res
            else helper t (Some h) true)
        else helper t (Some h) res
    in
    helper instrs pre_opt false
  ;;

  (* Eliminate fall through between block and block. 
   * Only use jump/cjump to go through blocks.
   * This helps to build control flow graph, and these 
   * redundant jumps will be eliminated in optimization pass. *)
  let rec eliminate_fall_through (instrs : i list) (acc : i list) : i list =
    match instrs with
    | [] -> List.rev acc
    | h :: t ->
      if I.is_label h
      then (
        let pre_opt = List.hd acc in
        match pre_opt with
        | None ->
          if List.length t > 0
          then eliminate_fall_through t (h :: acc)
          else I.ret () :: h :: acc
        | Some pre ->
          if I.is_jump pre || I.is_return pre
          then eliminate_fall_through t (h :: acc)
          else (
            let l = I.get_label h in
            let jp = I.jump l in
            eliminate_fall_through t (h :: jp :: acc)))
      else eliminate_fall_through t (h :: acc)
  ;;

  let rec _build_bb
      (instrs : i list)
      (bb_instrs : i list)
      (bb_label : Label.t option)
      (bbs : bbmap)
      : bbmap
    =
    match instrs with
    | [] ->
      (match bb_label with
      | None -> bbs
      | Some l ->
        let bb = { label = l; instrs = List.rev bb_instrs } in
        let bbs = Label.Map.set bbs ~key:l ~data:bb in
        bbs)
    | h :: t ->
      if I.is_label h
      then (
        match bb_label with
        | None -> _build_bb t [ h ] (Some (I.get_label h)) bbs
        | Some l ->
          let bb = { label = l; instrs = List.rev bb_instrs } in
          let bbs = Label.Map.set bbs ~key:l ~data:bb in
          _build_bb t [ h ] (Some l) bbs)
      else _build_bb t (h :: bb_instrs) bb_label bbs
  ;;

  let build_bb (instrs : i list) : bbmap =
    if has_fall_through instrs None
    then failwith "build_bb need to eliminate fall through edge first.";
    let bb_instrs = [] in
    let bb_label = None in
    let bbs = Label.Map.empty in
    _build_bb instrs bb_instrs bb_label bbs
  ;;

  let build_ino (bbs : bbmap) : map * map =
    if has_fall_through instrs None
    then failwith "build_ino need to eliminate fall through edge first.";
    failwith ""
  ;;

  let split_critical_edge (bbs : bbmap) (ins : map) (outs : map) = failwith ""

  let postorder (visited : set) (cur_label : Label.t) (outs : map) (acc : Label.t list) =
    failwith ""
  ;;

  let to_instrs (bbs : bbmap) = failwith ""
end
