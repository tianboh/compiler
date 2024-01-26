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
        | None -> eliminate_fall_through t (h :: acc)
        | Some pre ->
          if I.is_jump pre || I.is_return pre
          then eliminate_fall_through t (h :: acc)
          else (
            let l = I.get_label h in
            let jp = I.jump l in
            eliminate_fall_through t (h :: jp :: acc)))
      else eliminate_fall_through t (h :: acc)
  ;;

  let rec build_bb (instrs : i list) (bb : i list) bbs : bbmap =
    match instrs with
    | [] -> bbs
    | h :: t -> failwith ""
  ;;

  let build_ino (instrs : i list) = failwith ""
  let split_critical_edge (bbs : bbmap) (ins : map) (outs : map) = failwith ""

  let postorder (visited : set) (cur_label : Label.t) (outs : map) (acc : Label.t list) =
    failwith ""
  ;;

  let to_instrs (bbs : bbmap) = failwith ""
end
