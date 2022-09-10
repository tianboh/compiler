(* 
    This module generates information for register allocation 
    based on pseudo assembly code. The target format program is 
    declared in json_reader.Lab1_checkpoint.ml

    The basic idea is to generate infocmrtion including 
    "define", "use", "live_out", "move" and "line_num" info
    for each pseudo assembly instruction.
*)
open Core

module StrSet : Set.S
;;

(* type line =
  { uses : StrSet.t
  ; define : string
  ; live_out : StrSet.t
  ; move : bool
  ; line_number : int
  }
;; *)

(* val gen_forward : Assem.Pseudo.instr list ->
    (int, line) Base.Hashtbl.t -> int -> (int, line) Base.Hashtbl.t *)

val gen_regalloc_info: Assem.Pseudo.instr list -> Json_reader.Lab1_checkpoint.program