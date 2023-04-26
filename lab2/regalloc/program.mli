(* 
  This module generates information for register allocation 
  based on pseudo assembly code. The target format program is 
  declared in json_reader.Lab1_checkpoint.ml

  The basic idea is to generate infocmrtion including 
  "define", "use", "live_out", "move" and "line_num" info
  for each pseudo assembly instruction.
*)
(* open Core *)

module Inst_reg_info = Json_reader.Lab1_checkpoint
module AS = Inst.Pseudo
module Temp = Var.Temp
module IG = Interference_graph
module Register = Var.X86_reg

type line =
  { uses : IG.Vertex.Set.t
  ; define : IG.Vertex.Set.t
  ; live_out : IG.Vertex.Set.t
  ; move : bool
  ; line_number : int
  }

type temps_info = line list

(* Return None if define field is empty else Some Temp.t *)
val get_def : line -> IG.Vertex.t option

val transform_json_to_temp : Inst_reg_info.program -> line list

val transform_vertices_to_json
  : (IG.Vertex.t * Register.t) option list -> (string * string) option list

val print_VertexSet : (IG.Vertex.t, IG.Vertex.comparator_witness) Base.Set.t -> unit
val print_line : line -> unit
val print_lines : line list -> unit
val gen_regalloc_info : AS.instr list -> (line * AS.instr) list
