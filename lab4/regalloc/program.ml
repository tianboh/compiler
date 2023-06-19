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
module Memory = Var.Memory

type line =
  { uses : IG.Vertex.Set.t
  ; defines : IG.Vertex.Set.t
  ; live_out : IG.Vertex.Set.t
  ; move : bool
  ; line_number : int
  }

(* Return all the temporary/register in line.defines *)
let get_defs line = line.defines
let get_uses line = line.uses

type temps_info = line list

let empty_line line_num live_out =
  { uses = IG.Vertex.Set.empty
  ; defines = IG.Vertex.Set.empty
  ; live_out
  ; move = false
  ; line_number = line_num
  }
;;

(* Transform pseudo operands of type temp, imm, reg to reg/temp set*)
let gen_VertexSet (l : Abs_asm.operand list) =
  let rec _filter_imm (l : Abs_asm.operand list) (res : IG.Vertex.t list) =
    match l with
    | [] -> res
    | h :: t ->
      (match h with
      | Imm _ | Above_frame _ | Below_frame _ -> _filter_imm t res
      | Temp temp -> _filter_imm t (IG.Vertex.T.Temp temp :: res)
      | Reg r -> _filter_imm t (IG.Vertex.T.Reg r.reg :: res))
  in
  let l = _filter_imm l [] in
  IG.Vertex.Set.of_list l
;;

let print_VertexSet (ts : IG.Vertex.Set.t) =
  IG.Vertex.Set.iter ts ~f:(fun t -> printf "%s " (IG.Print.pp_vertex t))
;;

let print_line (line : line) =
  printf "{def: ";
  print_VertexSet line.defines;
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
  match inst_list with
  | [] -> inst_info
  | h :: t ->
    let live_out = Int.Map.find_exn live_out_map line_num in
    let line = empty_line line_num live_out in
    (match h with
    | Abs_asm.Binop binop ->
      let def = gen_VertexSet binop.line.defines in
      let uses = gen_VertexSet binop.line.uses in
      let line =
        { line with
          defines = def
        ; uses
        ; live_out = IG.Vertex.Set.union line.live_out uses
        }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Mov mov ->
      let def = gen_VertexSet mov.line.defines in
      let uses = gen_VertexSet mov.line.uses in
      let line =
        { line with
          defines = def
        ; uses
        ; move = true
        ; live_out = IG.Vertex.Set.union line.live_out uses
        }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.CJump cjp ->
      let defines = gen_VertexSet cjp.line.defines in
      let uses = gen_VertexSet cjp.line.uses in
      let line =
        { line with defines; uses; live_out = IG.Vertex.Set.union line.live_out uses }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Jump jp ->
      let defines = gen_VertexSet jp.line.defines in
      let uses = gen_VertexSet jp.line.uses in
      let line =
        { line with defines; uses; live_out = IG.Vertex.Set.union line.live_out uses }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Ret ret ->
      let defines = gen_VertexSet ret.line.defines in
      let uses = gen_VertexSet ret.line.uses in
      let line =
        { line with defines; uses; live_out = IG.Vertex.Set.union line.live_out uses }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Label _ ->
      let defines = IG.Vertex.Set.empty in
      let uses = IG.Vertex.Set.empty in
      let line =
        { line with defines; uses; live_out = IG.Vertex.Set.union line.live_out uses }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Fcall fcall ->
      let def = gen_VertexSet fcall.line.defines in
      let uses = gen_VertexSet fcall.line.uses in
      let line =
        { line with
          defines = def
        ; uses
        ; live_out = IG.Vertex.Set.union line.live_out uses
        }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Pop pop ->
      let uses = gen_VertexSet pop.line.uses in
      let line =
        { line with
          defines = gen_VertexSet pop.line.defines
        ; uses
        ; move = false
        ; live_out = IG.Vertex.Set.union line.live_out uses
        }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Push push ->
      let uses = gen_VertexSet push.line.uses in
      let line =
        { line with
          defines = gen_VertexSet push.line.defines
        ; uses
        ; move = false
        ; live_out = IG.Vertex.Set.union line.live_out uses
        }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | Abs_asm.Assert asrt ->
      let uses = gen_VertexSet asrt.line.uses in
      let line =
        { line with
          defines = gen_VertexSet asrt.line.defines
        ; uses
        ; move = false
        ; live_out = IG.Vertex.Set.union line.live_out uses
        }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
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
