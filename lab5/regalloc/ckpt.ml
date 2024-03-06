open Core
module Temp = Var.Temp
module Size = Var.Size
module Register = Var.X86_reg.Logic
module IG = Interference_graph
module Inst_reg_info = Json_reader.Lab1_checkpoint
module Abs_asm = Abs_asm.Inst
module OpSet = Set.Make (Abs_asm.Op)

let gen_VertexSet (l : string list) =
  let rec _gen_VertexList (l : string list) (res : Abs_asm.Op.t list) =
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
          let temp = Temp.create' idx in
          _gen_VertexList t (Abs_asm.Op.Temp temp :: res)
        | 'r' | 's' | 'e' ->
          let reg = Register.str_to_reg h in
          _gen_VertexList t (Abs_asm.Op.Reg reg :: res)
        | _ -> _gen_VertexList t res))
  in
  let l = _gen_VertexList l [] in
  OpSet.of_list l
;;

(* When read from json file(l1 checkpoint), we need to transform
   the information from string info to line declared in this file.
   We will ignore register string during transformation because we
   only need to assign temp to registers.
*)
let transform_str_to_temp (line : Inst_reg_info.line) : Abs_asm.line =
  { defines = gen_VertexSet [ line.define ] |> OpSet.to_list
  ; uses = gen_VertexSet line.uses |> OpSet.to_list
  ; live_out = gen_VertexSet line.live_out |> OpSet.to_list
  ; move = line.move
  }
;;

(* { uses : Op.t list; defines : Op.t list; live_out : Op.t list; move : bool } *)

let transform_json_to_temp (program : Inst_reg_info.program) : Abs_asm.line list =
  List.map program ~f:(fun line -> transform_str_to_temp line)
;;

let transform_vertex_to_json (vertex : (IG.Vertex.t * Driver.dest) option) =
  match vertex with
  | None -> None
  | Some (vtx, dest) ->
    (match dest with
    | Reg reg ->
      let reg_hard : Var.X86_reg.Hard.t = { data = reg; size = `DWORD } in
      Some (IG.Print.pp_vertex vtx, Var.X86_reg.Hard.pp reg_hard)
    | Spill s -> Some (IG.Print.pp_vertex vtx, Var.X86_reg.Spill.pp s))
;;

let transform_vertices_to_json (vertices : (IG.Vertex.t * Driver.dest) option list) =
  List.map vertices ~f:(fun x -> transform_vertex_to_json x)
;;

let regalloc_ckpt (lines : Abs_asm.line list) : (IG.Vertex.t * Driver.dest) option list =
  (* let adj, roots = Driver.Helper.build_graph lines in
  let seq = Driver.seo adj in
  let vertex_to_reg = IG.Vertex.Map.empty in
  let color = Driver.greedy seq adj vertex_to_reg in *)
  (* Print.print_adj adj;
  printf "SEO order\n";
  let seq_l = List.map seq ~f:(fun x -> IG.Print.pp_vertex x) in
  List.iter ~f:(printf "%s ") seq_l;
  Print.print_vertex_to_dest color;
  printf "\n"; *)
  Driver.gen_result lines false
;;
