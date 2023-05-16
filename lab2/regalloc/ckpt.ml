open Driver
open Core
module Temp = Var.Temp
module Memory = Var.Memory
module Register = Var.X86_reg
module Reg_info = Program
module AS = Inst.Pseudo
module IG = Interference_graph

let transform_vertex_to_json (vertex : (IG.Vertex.t * dest) option) =
  match vertex with
  | None -> None
  | Some (vtx, dest) ->
    (match dest with
    | Reg reg -> Some (IG.Print.pp_vertex vtx, Register.reg_to_str ~layout:DWORD reg)
    | Mem m -> Some (IG.Print.pp_vertex vtx, Memory.mem_to_str m))
;;

let transform_vertices_to_json (vertices : (IG.Vertex.t * dest) option list) =
  List.map vertices ~f:(fun x -> transform_vertex_to_json x)
;;

let regalloc_ckpt (prog : Program.line list) : (IG.Vertex.t * dest) option list =
  let prog_dummy = List.map prog ~f:(fun x -> x, AS.Comment "") in
  let adj = Helper.build_graph prog_dummy IG.Vertex.Map.empty in
  let seq = seo adj prog in
  let vertex_to_reg = IG.Vertex.Map.empty in
  let color = greedy seq adj vertex_to_reg in
  gen_result color prog
;;
