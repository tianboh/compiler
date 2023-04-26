module Temp = Var.Temp
module Memory = Var.Memory
module Register = Var.X86_reg
module Reg_info = Program
module AS = Inst.Pseudo
module IG = Interference_graph

type reg = Register.t
val eax : reg
val edx : reg
val ecx : reg
type dest =
  | Reg of Register.t
  | Mem of Memory.t

val regalloc : AS.instr list -> (IG.Vertex.t * dest) option list

module Lazy : sig
  val trans_operand : AS.operand -> IG.Vertex.Set.t
  val collect_vertex : AS.instr list -> IG.Vertex.Set.t -> IG.Vertex.Set.t
  val gen_result_dummy :
    IG.Vertex.Set.t -> (IG.Vertex.t * dest) option list
end

module Print : sig
  val print_adj : IG.Vertex.Set.t IG.Vertex.Map.t -> unit
  val print_vertex_to_dest : dest IG.Vertex.Map.t -> unit
end

module Helper : sig
  val build_vtx_vtxs :
    IG.Vertex.Set.t IG.Vertex.Map.t ->
    IG.Vertex.t -> IG.Vertex.Set.t -> IG.Vertex.Set.t IG.Vertex.Map.t
  val precolor :
    IG.Vertex.Set.t IG.Vertex.Map.t ->
    IG.Vertex.t ->
    IG.Vertex.Set.t ->
    IG.Vertex.Set.t -> AS.instr -> IG.Vertex.Set.t IG.Vertex.Map.t
  val build_graph :
    (Reg_info.line * AS.instr) list ->
    IG.Vertex.Set.t IG.Vertex.Map.t -> IG.Vertex.Set.t IG.Vertex.Map.t
  val gen_vertex_table : Reg_info.line list -> int IG.Vertex.Map.t
end