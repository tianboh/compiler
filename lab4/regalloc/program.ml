(*
  This module generates information for register allocation
  based on pseudo assembly code. The target format program is
  declared in json_reader.Lab1_checkpoint.ml

  The basic idea is to generate infocmrtion including
  "defines", "use", "live_out", "move" and "line_num" info
  for each pseudo assembly instruction.

  Pseudo assembly instruction list -> register allocation info
*)
open Core
module Abs_asm = Abs_asm.Inst
module Temp = Var.Temp
module IG = Interference_graph
module Register = Var.X86_reg.Logic

type line =
  { uses : IG.Vertex.Set.t
  ; defs : IG.Vertex.Set.t
  ; live_out : IG.Vertex.Set.t
  ; move : bool
  ; line_number : int
  }

(* Return all the temporary/register in line.defines *)
let get_defs line = line.defs
let get_uses line = line.uses

type temps_info = line list

let empty_line line_num live_out =
  { uses = IG.Vertex.Set.empty
  ; defs = IG.Vertex.Set.empty
  ; live_out
  ; move = false
  ; line_number = line_num
  }
;;

(* Transform pseudo operands of type temp, imm, reg to reg/temp set*)
let gen_VertexSet (l : Abs_asm.Op.t list) =
  let rec _filter_imm (l : Abs_asm.Op.t list) (res : IG.Vertex.t list) =
    match l with
    | [] -> res
    | h :: t ->
      (match h with
      | Imm _ | Above_frame _ -> _filter_imm t res
      | Temp temp -> _filter_imm t (IG.Vertex.T.Temp temp :: res)
      | Reg r -> _filter_imm t (IG.Vertex.T.Reg r :: res))
  in
  let l = _filter_imm l [] in
  IG.Vertex.Set.of_list l
;;

let print_VertexSet (ts : IG.Vertex.Set.t) =
  IG.Vertex.Set.iter ts ~f:(fun t -> printf "%s " (IG.Print.pp_vertex t))
;;

let print_line (line : line) =
  printf "{def: ";
  print_VertexSet line.defs;
  printf "\nuses: ";
  print_VertexSet line.uses;
  printf "\nlive_out: ";
  print_VertexSet line.live_out;
  printf "\nmove: %b" line.move;
  printf "\nline_number: %d}\n\n" line.line_number
;;

let print_lines (l : (line * Abs_asm.instr) list) =
  List.iter l ~f:(fun tuple ->
      let line, inst = tuple in
      printf "%s\n" (Abs_asm.pp_inst inst);
      print_line line)
;;

(* Generate defines, use, move, liveout, line number. *)
let rec gen_forward
    (inst_list : Abs_asm.instr list)
    (inst_info : (int, line * Abs_asm.instr) Base.Hashtbl.t)
    (line_num : int)
    live_out_map
  =
  let helper (line : Abs_asm.line) lo (move : bool) inst_info h line_num =
    let line_empty = empty_line line_num lo in
    let defs = gen_VertexSet line.defines in
    let uses = gen_VertexSet line.uses in
    let live_out = IG.Vertex.Set.union lo uses in
    let line = { line_empty with defs; uses; live_out; move } in
    Hashtbl.set inst_info ~key:line_num ~data:(line, h);
    inst_info
  in
  match inst_list with
  | [] -> inst_info
  | h :: t ->
    let live_out = Int.Map.find_exn live_out_map line_num in
    (match h with
    | Abs_asm.Binop binop ->
      let inst_info = helper binop.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Mov mov ->
      let inst_info = helper mov.line live_out true inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Cast cast ->
      let inst_info = helper cast.line live_out true inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.CJump cjp ->
      let inst_info = helper cjp.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Jump jp ->
      let inst_info = helper jp.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Ret ret ->
      let inst_info = helper ret.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Label label ->
      let inst_info = helper label.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Fcall fcall ->
      let inst_info = helper fcall.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Pop pop ->
      let inst_info = helper pop.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Push push ->
      let inst_info = helper push.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Load load ->
      let inst_info = helper load.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Store store ->
      let inst_info = helper store.line live_out false inst_info h line_num in
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Directive _ | Abs_asm.Comment _ ->
      gen_forward t inst_info line_num live_out_map)
;;

let gen_regalloc_info (inst_list : Abs_asm.instr list) =
  let inst_info = Hashtbl.create (module Int) in
  let liveness = Liveness.gen_liveness inst_list in
  let inst_info = gen_forward inst_list inst_info 0 liveness in
  let inst_no_sort = List.sort (Hashtbl.keys inst_info) ~compare:Int.compare in
  let ret = List.map inst_no_sort ~f:(fun no -> Hashtbl.find_exn inst_info no) in
  (* let lines =
    List.fold_left ret ~init:[] ~f:(fun acc line ->
        let reginfo, _ = line in
        reginfo :: acc)
    |> List.rev
  in
  List.iter lines ~f:(fun line -> print_line line);
  printf "%s\n" (Abs_asm.pp_insts inst_list "");
  let lines = List.zip_exn lines inst_list in
  print_lines lines; *)
  ret
;;
