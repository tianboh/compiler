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
module AS = Assem.Pseudo

module StrSet = Set.Make(String)

type line =
  { uses : StrSet.t
  ; define : StrSet.t
  ; live_out : StrSet.t
  ; move : bool
  ; line_number : int
  }
;;

let empty_line line_num =
  { uses = StrSet.empty
  ; define = StrSet.empty
  ; live_out = StrSet.empty
  ; move = false
  ; line_number = line_num
  }
;;

(* Generate define, use, move, line number *)
let rec gen_forward (inst_list : AS.instr list) 
                    (inst_info : (int, line) Base.Hashtbl.t) 
                    (line_num : int) = 
  match inst_list with
  | [] -> inst_info
  | h :: t -> 
    let line = empty_line line_num in
    match h with
    | AS.Binop binop -> 
      let def = StrSet.of_list [AS.format_operand binop.dest] in
      let uses = StrSet.of_list (List.map ~f:AS.format_operand [binop.lhs; binop.rhs]) in
      let line = {line with define = def; uses = uses} in
      Hashtbl.set inst_info ~key:line_num ~data:line;
      gen_forward t inst_info (line_num + 1)
    | AS.Mov mov -> 
      let def = StrSet.of_list [AS.format_operand mov.dest] in
      let uses = StrSet.of_list [AS.format_operand mov.src] in
      let line = {line with define = def; uses = uses; move = true} in
      Hashtbl.set inst_info ~key:line_num ~data:line;
      gen_forward t inst_info (line_num + 1)
    | AS.Directive _ | AS.Comment _ -> 
      gen_forward t inst_info line_num
  ;;


(* Generate liveout *)
let rec gen_backward inst_list inst_info line_num (cur_alive_set : StrSet.t) = match inst_list with
  | [] -> inst_info
  | h :: t -> 
    let line = Hashtbl.find_exn inst_info line_num in
    let cur_alive_set = StrSet.diff cur_alive_set line.define in
    let cur_alive_set = StrSet.union cur_alive_set line.uses in
    match h with
    | AS.Binop _ | AS.Mov _ -> 
      let line = {line with live_out = cur_alive_set} in
      Hashtbl.set inst_info ~key:line_num ~data:line;
      gen_backward t inst_info (line_num - 1) cur_alive_set
    | AS.Directive _ | AS.Comment _ -> 
      gen_backward t inst_info line_num cur_alive_set
;;

let format_line (line : line) : Inst_reg_info.line = 
  let define_l = StrSet.to_list line.define in
  let define = match define_l with
  | [] -> ""
  | h :: _ -> h
  in
  { uses = StrSet.to_list line.uses
  ; define = define
  ; live_out = StrSet.to_list line.live_out
  ; move = line.move
  ; line_number = line.line_number
  }
;;

let dump_json (inst_info : (int, line) Base.Hashtbl.t) : Inst_reg_info.program = 
  let line_num = Hashtbl.keys inst_info in
  let line_num = List.sort line_num ~compare:Int.compare in
  List.map line_num ~f:(fun no -> 
    let line = Hashtbl.find_exn inst_info no in
    format_line line)
;;

let gen_regalloc_info (inst_list : AS.instr list) = 
  let inst_info = Hashtbl.create (module Int) in
  let inst_info = gen_forward (inst_list) (inst_info) (0) in
  let inst_list_rev = List.rev inst_list in
  let live_out = StrSet.empty in
  let inst_info = gen_backward inst_list_rev inst_info (Hashtbl.length inst_info -1) live_out in
  dump_json inst_info
;;
