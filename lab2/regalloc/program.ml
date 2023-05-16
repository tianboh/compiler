(*
  This module generates information for register allocation
  based on pseudo assembly code. The target format program is
  declared in json_reader.Lab1_checkpoint.ml

  The basic idea is to generate infocmrtion including
  "define", "use", "live_out", "move" and "line_num" info
  for each pseudo assembly instruction.

  Pseudo assembly instruction list -> register allocation info
*)
open Core
module Inst_reg_info = Json_reader.Lab1_checkpoint
module AS = Inst.Pseudo
module Temp = Var.Temp
module IG = Interference_graph
module Register = Var.X86_reg
module Memory = Var.Memory
(* open Var.Layout *)

type line =
  { uses : IG.Vertex.Set.t
  ; define : IG.Vertex.Set.t
  ; live_out : IG.Vertex.Set.t
  ; move : bool
  ; line_number : int
  }

(* Return None if define field is empty else Some Temp.t *)
let get_def line =
  if IG.Vertex.Set.is_empty line.define
  then None
  else (
    let l = IG.Vertex.Set.to_list line.define in
    Some (List.last_exn l))
;;

type temps_info = line list

let empty_line line_num live_out =
  { uses = IG.Vertex.Set.empty
  ; define = IG.Vertex.Set.empty
  ; live_out
  ; move = false
  ; line_number = line_num
  }
;;

(* Transform pseudo operands of type temp and imm to temp set*)
let gen_VertexSet (l : AS.operand list) =
  let rec _filter_imm (l : AS.operand list) (res : IG.Vertex.t list) =
    match l with
    | [] -> res
    | h :: t ->
      (match h with
      | Imm _ -> _filter_imm t res
      | Temp temp -> _filter_imm t (IG.Vertex.T.Temp temp :: res))
  in
  let l = _filter_imm l [] in
  IG.Vertex.Set.of_list l
;;

let print_VertexSet (ts : IG.Vertex.Set.t) =
  IG.Vertex.Set.iter ts ~f:(fun t -> printf "%s " (IG.Print.pp_vertex t))
;;

let print_line (line : line) =
  let () = printf "\n{def: " in
  let () = print_VertexSet line.define in
  let () = printf "\nuses: " in
  let () = print_VertexSet line.uses in
  let () = printf "\nlive_out: " in
  let () = print_VertexSet line.live_out in
  let () = printf "\nmove: %b" line.move in
  printf "\nline_number: %d}\n" line.line_number
;;

let print_lines (lines : line list) = List.iter lines ~f:(fun line -> print_line line)

(* Generate define, use, move, liveout, line number. *)
let rec gen_forward
    (inst_list : AS.instr list)
    (inst_info : (int, line * AS.instr) Base.Hashtbl.t)
    (line_num : int)
    live_out_map
  =
  match inst_list with
  | [] -> inst_info
  | h :: t ->
    let live_out = Int.Map.find_exn live_out_map line_num in
    let line = empty_line line_num live_out in
    (match h with
    | AS.Binop binop ->
      let def = gen_VertexSet [ binop.dest ] in
      let uses = gen_VertexSet [ binop.lhs; binop.rhs ] in
      let line =
        { line with
          define = def
        ; uses
        ; live_out = IG.Vertex.Set.union line.live_out uses
        }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | AS.Mov mov ->
      let def = gen_VertexSet [ mov.dest ] in
      let uses = gen_VertexSet [ mov.src ] in
      let line =
        { line with
          define = def
        ; uses
        ; move = true
        ; live_out = IG.Vertex.Set.union line.live_out uses
        }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | AS.CJump cjp ->
      let define = gen_VertexSet [] in
      let uses = gen_VertexSet [ cjp.lhs; cjp.rhs ] in
      let line =
        { line with define; uses; live_out = IG.Vertex.Set.union line.live_out uses }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | AS.Jump _ ->
      let define = gen_VertexSet [] in
      let uses = gen_VertexSet [] in
      let line =
        { line with define; uses; live_out = IG.Vertex.Set.union line.live_out uses }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | AS.Ret ret ->
      let define = gen_VertexSet [] in
      let uses = gen_VertexSet [ ret.var ] in
      let line =
        { line with define; uses; live_out = IG.Vertex.Set.union line.live_out uses }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | AS.Label _ ->
      let define = IG.Vertex.Set.empty in
      let uses = IG.Vertex.Set.empty in
      let line =
        { line with define; uses; live_out = IG.Vertex.Set.union line.live_out uses }
      in
      Hashtbl.set inst_info ~key:line_num ~data:(line, h);
      gen_forward t inst_info (line_num + 1) live_out_map
    | _ -> gen_forward t inst_info line_num live_out_map)
;;

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
          let temp = Temp.create_no idx in
          _gen_VertexList t (IG.Vertex.T.Temp temp :: res)
        | 'r' | 's' ->
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
let transform_str_to_temp (line : Inst_reg_info.line) =
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

let gen_regalloc_info (inst_list : AS.instr list) =
  let inst_info = Hashtbl.create (module Int) in
  let liveness = Liveness.gen_liveness inst_list in
  let inst_info = gen_forward inst_list inst_info 0 liveness in
  let inst_no_sort = List.sort (Hashtbl.keys inst_info) ~compare:Int.compare in
  let ret = List.map inst_no_sort ~f:(fun no -> Hashtbl.find_exn inst_info no) in
  (* let lines =
    List.fold_left ret ~init:[] ~f:(fun acc line ->
        let reginfo, _ = line in
        reginfo :: acc)
  in
  let () = print_lines lines in *)
  ret
;;
