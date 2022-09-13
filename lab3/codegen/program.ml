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

module TempSet = Set.Make(Temp)
type line =
  { uses : TempSet.t
  ; define : TempSet.t
  ; live_out : TempSet.t
  ; move : bool
  ; line_number : int
  }
;;

(* Return None if define field is empty else Some Temp.t *)
let get_def line = 
  if TempSet.is_empty line.define then None
  else 
    let l = TempSet.to_list line.define in
    Some (List.last_exn l)
;;

type temps_info = line list
;;

let empty_line line_num =
  { uses = TempSet.empty
  ; define = TempSet.empty
  ; live_out = TempSet.empty
  ; move = false
  ; line_number = line_num
  }
;;

(* Transform pseudo operands of type temp and imm to temp set*)
let gen_TempSet (l : AS.operand list)  = 
  let rec _filter_imm (l : AS.operand list) (res : Temp.t list) = match l with
    | [] -> res
    | h :: t ->
      match h with
      | Imm _ -> _filter_imm t res
      | Temp temp -> _filter_imm t ([temp]@res) in
  let l = _filter_imm l [] in
  TempSet.of_list l

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
      let def = gen_TempSet [binop.dest] in
      let uses = gen_TempSet [binop.lhs; binop.rhs] in
      let line = {line with define = def; uses = uses} in
      Hashtbl.set inst_info ~key:line_num ~data:line;
      gen_forward t inst_info (line_num + 1)
    | AS.Mov mov -> 
      let def = gen_TempSet [mov.dest] in
      let uses = gen_TempSet [mov.src] in
      let line = {line with define = def; uses = uses; move = true} in
      Hashtbl.set inst_info ~key:line_num ~data:line;
      gen_forward t inst_info (line_num + 1)
    | AS.Directive _ | AS.Comment _ -> 
      gen_forward t inst_info line_num
  ;;


(* Generate liveout *)
let rec gen_backward inst_list inst_info line_num (cur_alive_set : TempSet.t) = match inst_list with
  | [] -> inst_info
  | h :: t -> 
    let line = Hashtbl.find_exn inst_info line_num in
    let cur_alive_set = TempSet.diff cur_alive_set line.define in
    let cur_alive_set = TempSet.union cur_alive_set line.uses in
    match h with
    | AS.Binop _ | AS.Mov _ -> 
      let line = {line with live_out = cur_alive_set} in
      Hashtbl.set inst_info ~key:line_num ~data:line;
      gen_backward t inst_info (line_num - 1) cur_alive_set
    | AS.Directive _ | AS.Comment _ -> 
      gen_backward t inst_info line_num cur_alive_set
;;

let gen_TempSet (l : string list) = 
  let rec _gen_TempList (l : string list) (res : Temp.t list) = match l with
  | [] -> res
  | h :: t -> 
    match h with
    | "" -> _gen_TempList t res
    | _ -> 
      match h.[1] with
      | 't' -> 
        let str_l = String.split_on_chars ~on:['t'] h in
        let idx = Int.of_string (List.last_exn str_l) in
        let temp = Temp.create_no idx in
        _gen_TempList t ([temp]@res)
      | _ -> _gen_TempList t res in
    let l = _gen_TempList l [] in
    TempSet.of_list l
;;

(* When read from json file(l1 checkpoint), we need to transform 
   the information from string info to line declared in this file. 
   We will ignore register string during transformation because we
   only need to assign temp to registers. 
*)
let transform_str_to_temp (line : Inst_reg_info.line) = 
  {
    define = gen_TempSet [line.define]
    ; uses = gen_TempSet line.uses
    ; live_out = gen_TempSet line.live_out
    ; move = line.move
    ; line_number = line.line_number
  }
;;

let transform_json_to_temp (program : Inst_reg_info.program) = 
  List.map program ~f:(fun line -> transform_str_to_temp line)
;;

let print_TempSet (ts : TempSet.t) = 
  TempSet.iter ts ~f:(fun t -> printf "%s " (Temp.name t))
;;

let print_line (line : line) = 
  let () = printf "\n{def: " in
  let () = print_TempSet line.define in
  let () = printf "\nuses: " in
  let () = print_TempSet line.uses in
  let () = printf "\nlive_out: " in
  let () = print_TempSet line.live_out in
  let () = printf "\nmove: %b" line.move in
  printf "\nline_number: %d}\n" line.line_number
;;

let print_lines (lines : line list) = 
  List.iter lines ~f:(fun line -> print_line line)
;;

(* let format_line (line : line) : Inst_reg_info.line = 
  let define_l = TempSet.to_list line.define in
  let define = match define_l with
  | [] -> ""
  | h :: _ -> h
  in
  { uses = TempSet.to_list line.uses
  ; define = define
  ; live_out = TempSet.to_list line.live_out
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
  let live_out = TempSet.empty in
  let inst_info = gen_backward inst_list_rev inst_info (Hashtbl.length inst_info -1) live_out in
  dump_json inst_info
;; *)
