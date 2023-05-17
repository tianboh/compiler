open Driver
open Core
module Temp = Var.Temp
module Memory = Var.Memory
module Register = Var.X86_reg
module Reg_info = Program
module AS = Middle.Inst
module IG = Interference_graph
module Inst_reg_info = Json_reader.Lab1_checkpoint

let gen_VertexSet (l : string list) =
  let rec _gen_VertexList (l : string list) (res : IG.Vertex.t list) =
    match l with
    | [] -> res
    | h :: t ->
      (match h with
      | "" -> _gen_VertexList t res
      | _ ->
        (match h.[1] with
        | 't' ->
          let str_l = String.split_on_chars ~on:[ 't' ] h in
          let idx = Int.of_string (List.last_exn str_l) in
          let temp = Temp.of_int idx in
          _gen_VertexList t (IG.Vertex.T.Temp temp :: res)
        | 'r' | 's' | 'e' ->
          let reg = Register.str_to_reg h in
          _gen_VertexList t (IG.Vertex.T.Reg reg :: res)
        | _ -> _gen_VertexList t res))
  in
  let l = _gen_VertexList l [] in
  IG.Vertex.Set.of_list l
;;

(* When read from json file(l1 checkpoint), we need to transform
   the information from string info to line declared in this file.
   We will ignore register string during transformation because we
   only need to assign temp to registers.
*)
let transform_str_to_temp (line : Inst_reg_info.line) : Program.line =
  { define = gen_VertexSet [ line.define ]
  ; uses = gen_VertexSet line.uses
  ; live_out = gen_VertexSet line.live_out
  ; move = line.move
  ; line_number = line.line_number
  }
;;

let transform_json_to_temp (program : Inst_reg_info.program) =
  List.map program ~f:(fun line -> transform_str_to_temp line)
;;

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
  (* Print.print_adj adj;
  printf "SEO order\n";
  let seq_l = List.map seq ~f:(fun x -> IG.Print.pp_vertex x) in
  List.iter ~f:(printf "%s ") seq_l;
  Print.print_vertex_to_dest color;
  printf "\n"; *)
  gen_result color prog
;;
