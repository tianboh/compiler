(* 
    This module generates information for register allocation 
    based on pseudo assembly code. The target format program is 
    declared in json_reader.Lab1_checkpoint.ml

    The basic idea is to generate infocmrtion including 
    "define", "use", "live_out", "move" and "line_num" info
    for each pseudo assembly instruction.
*)
open Core

module TempSet : Set.S
module AS = Assem.Pseudo
module Inst_reg_info = Json_reader.Lab1_checkpoint
;;

type line =
  { uses : TempSet.t
  ; define : TempSet.t
  ; live_out : TempSet.t
  ; move : bool
  ; line_number : int
  }
;;

type temps_info = line list
;;

(* Return None if define field is empty else Some Temp.t *)
val get_def : line -> Temp.t option
;;

val gen_forward : AS.instr list ->
  (int, line) Base.Hashtbl.t -> int -> (int, line) Base.Hashtbl.t
;;

val gen_backward : AS.instr list ->
  (int, line) Base.Hashtbl.t -> int -> TempSet.t -> (int, line) Base.Hashtbl.t
;;
  
val transform_json_to_temp : Inst_reg_info.program -> line list
;;

val print_lines : line list -> unit
(* val gen_regalloc_info: Assem.Pseudo.instr list -> Json_reader.Lab1_checkpoint.program *)