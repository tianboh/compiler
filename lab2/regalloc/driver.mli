module Temp = Var.Temp
module Register = Var.X86_reg
module Reg_info = Program
module AS = Inst.Pseudo
module IG = Interference_graph
open Core

type reg = Register.t
type temp = Temp.t

val print_adj : 
  (IG.Vertex.t, (IG.Vertex.t, IG.Vertex.comparator_witness) Base.Set.t,
  IG.Vertex.comparator_witness)
  Map_intf.Map.t -> unit

val print_vertex_to_reg : (IG.Vertex.t, reg, IG.Vertex.comparator_witness) Map_intf.Map.t -> unit

val regalloc : AS.instr list -> (IG.Vertex.t * reg) option list

val regalloc_ckpt : Reg_info.line list -> (IG.Vertex.t * reg) option list