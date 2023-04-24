(* 
  This module generates information for register allocation 
  based on pseudo assembly code. The target format program is 
  declared in json_reader.Lab1_checkpoint.ml

  The basic idea is to generate infocmrtion including 
  "define", "use", "live_out", "move" and "line_num" info
  for each pseudo assembly instruction.
*)
(* open Core *)

open Core
module Inst_reg_info = Json_reader.Lab1_checkpoint
module AS = Inst.Pseudo
module Temp = Var.Temp
module Register = Var.X86_reg

type line =
  { uses : Temp.Set.t
  ; define : Temp.Set.t
  ; live_out : Temp.Set.t
  ; move : bool
  ; line_number : int
  }

type temps_info = line list

(* Return None if define field is empty else Some Temp.t *)
val get_def : line -> Temp.t option

(* val gen_forward
  :  AS.instr list
  -> (int, line) Base.Hashtbl.t
  -> int
  -> (int, line) Base.Hashtbl.t *)

val gen_backward
  :  AS.instr list
  -> (int, line) Base.Hashtbl.t
  -> int
  -> Temp.Set.t
  -> (int, line) Base.Hashtbl.t

val transform_json_to_temp : Inst_reg_info.program -> line list

val transform_temps_to_json
  :  (Temp.t * Register.t) option list
  -> Inst_reg_info.allocations

val print_TempSet : (Temp.t, Temp.comparator_witness) Set_intf.Set.t -> unit
val print_line : line -> unit
val print_lines : line list -> unit
val gen_regalloc_info : AS.instr list -> line list
val gen_regalloc_info' : AS.instr list -> line list
