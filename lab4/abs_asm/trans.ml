(* L3 x86 abstract assembly code
 * Transfrom from Ir_tree Inst to x86 Inst with convention
 * This is done by providing each instruction with different
 * defines/uses operand. Compared with Ir_tree Inst, this
 * layer has extra register type for operand. 
 *
 * For each function, we provide prologue and epilogue.
 * prologue and epilogue will save and restore callee-saved
 * registers, rsp and rbp. Function return will jump to 
 * epilogue and then return to make sure frame is properly
 * restored.
 *
 * For each function call, caller will use move temp, reg to
 * follow x86 calling convention. Caller-saved registers are
 * properly defined in the fcall statements. So that it is
 * preferred to be used within the function.
 *
 * In a word, caller and callee saved registers are properly
 * defined through defines/uses info. Then regalloc alg will
 * makes sure they will be the same state after function call.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
open Core
module Src = Quads.Inst
module Dest = Inst
module Reg = Var.X86_reg.Logic
module Size = Var.Size
open Inst

type line = Dest.line
type instr = Dest.instr

let rax = Reg.RAX
let rcx = Reg.RCX
let rdx = Reg.RDX
let empty_line () : Dest.line = { defines = []; uses = []; live_out = []; move = false }

let trans_binop (op : Src.bin_op) : Dest.bin_op =
  match op with
  | Plus -> Plus
  | Minus -> Minus
  | Times -> Times
  | Divided_by -> Divided_by
  | Modulo -> Modulo
  | And -> And
  | Or -> Or
  | Xor -> Xor
  | Right_shift -> Right_shift
  | Left_shift -> Left_shift
  | Equal_eq -> Equal_eq
  | Greater -> Greater
  | Greater_eq -> Greater_eq
  | Less -> Less
  | Less_eq -> Less_eq
  | Not_eq -> Not_eq
;;

let trans_operand (operand : Src.operand) : Dest.operand =
  match operand with
  | Imm i -> Dest.Imm i
  | Temp t -> Dest.Temp t
;;

let get_size (operand : Src.operand) : Size.primitive =
  match operand with
  | Imm _ -> DWORD
  | Temp t -> t.size
;;

let get_size' (operand : Dest.operand) : Size.primitive =
  match operand with
  | Imm _ -> DWORD
  | Temp t -> t.size
  | Reg r -> r.size
  | Above_frame _ -> QWORD
  | Below_frame _ -> DWORD
;;

(* Generate x86 instr with binop convention *)
let[@warning "-8"] gen_binop (Src.Binop bin) =
  let op, dest, lhs, rhs =
    ( trans_binop bin.op
    , trans_operand bin.dest
    , trans_operand bin.lhs
    , trans_operand bin.rhs )
  in
  let size = get_size' dest in
  let defines =
    match op with
    | Times -> [ dest; Dest.Reg { reg = rax; size } ]
    | Divided_by | Modulo ->
      [ dest; Dest.Reg { reg = rax; size }; Dest.Reg { reg = rdx; size } ]
    | Right_shift | Left_shift -> [ dest; Dest.Reg { reg = rcx; size } ]
    | Equal_eq | Greater | Greater_eq | Less | Less_eq | Not_eq ->
      [ dest; Dest.Reg { reg = rax; size } ]
    | _ -> [ dest ]
  in
  let uses = [ lhs; rhs ] in
  let line = ({ defines; uses; live_out = []; move = false } : Dest.line) in
  [ Dest.Binop { op; dest; lhs; rhs; line } ]
;;

let[@warning "-8"] gen_move (Src.Mov move) =
  let dest, src = trans_operand move.dest, trans_operand move.src in
  let line = { defines = [ dest ]; uses = [ src ]; live_out = []; move = true } in
  [ Dest.Mov { dest; src; line } ]
;;

let[@warning "-8"] gen_jump (Src.Jump jump) =
  let line = empty_line () in
  [ Dest.Jump { target = jump.target; line } ]
;;

let[@warning "-8"] gen_cjump (Src.CJump cjump) =
  let lhs, rhs = trans_operand cjump.lhs, trans_operand cjump.rhs in
  let op = trans_binop cjump.op in
  let line = { defines = []; uses = [ lhs; rhs ]; live_out = []; move = false } in
  [ Dest.CJump
      { lhs
      ; op
      ; rhs
      ; target_true = cjump.target_true
      ; target_false = cjump.target_false
      ; line
      }
  ]
;;

let[@warning "-8"] gen_ret (Src.Ret ret) (exit_label : Label.t) =
  let line = empty_line () in
  let mov =
    match ret.var with
    | None -> []
    | Some var ->
      let src = trans_operand var in
      let size = get_size' src in
      let line_mov =
        { line with
          defines = [ Dest.Reg { reg = rax; size } ]
        ; uses = [ src ]
        ; move = true
        }
      in
      [ Dest.Mov { dest = Dest.Reg { reg = rax; size }; src; line = line_mov } ]
  in
  Dest.Jump { target = exit_label; line } :: mov
;;

let[@warning "-8"] gen_asrt (Src.Assert asrt) =
  let line = empty_line () in
  let var = trans_operand asrt in
  let size = get_size' var in
  let line =
    { line with
      defines = [ Dest.Reg { reg = rax; size } ]
    ; uses = [ trans_operand asrt ]
    }
  in
  [ Dest.Assert { var; line } ]
;;

let param_map base idx size : Dest.operand =
  match idx with
  | 0 -> Dest.Reg { reg = RDI; size }
  | 1 -> Dest.Reg { reg = RSI; size }
  | 2 -> Dest.Reg { reg = RDX; size }
  | 3 -> Dest.Reg { reg = RCX; size }
  | 4 -> Dest.Reg { reg = R8; size }
  | 5 -> Dest.Reg { reg = R9; size }
  | _ -> Dest.Above_frame { offset = base + Size.type_size_byte QWORD; size = QWORD }
;;

let gen_scope = function
  | Src.Internal -> Dest.Internal
  | Src.External -> Dest.External
;;

let set_size (operand : operand) (size : Size.primitive) : operand =
  match operand with
  | Imm i -> Imm i
  | Temp t -> Temp { t with size }
  | Reg r -> Reg { r with size }
  | Above_frame i -> Above_frame { i with size }
  | Below_frame i -> Below_frame { i with size }
;;

(* Generate x86 instr with function call convention *)
let[@warning "-8"] gen_fcall (Src.Fcall fcall) =
  let func_name = fcall.func_name in
  let dest =
    match fcall.dest with
    | Some dest -> Some (trans_operand (Src.Temp dest))
    | None -> None
  in
  let args = List.map fcall.args ~f:(fun arg -> trans_operand arg) in
  let args_size = List.map args ~f:(fun arg -> get_size' arg) in
  let l1, l2 = List.length args_size, List.length Reg.parameters in
  let args_size =
    if l1 < l2
    then args_size @ List.init (l2 - l1) ~f:(fun _ -> Size.QWORD)
    else List.take args_size l2
  in
  let x86_regs = (rax :: Reg.caller_saved) @ Reg.parameters in
  let sizes =
    match dest with
    | Some dest -> [ get_size' dest; QWORD; QWORD ] @ args_size
    | None -> [ Size.QWORD; QWORD; QWORD ] @ args_size
  in
  let ts = List.zip_exn x86_regs sizes in
  let defines =
    List.map ts ~f:(fun t ->
        let reg, size = t in
        Dest.Reg { reg; size })
  in
  let base = ref 0 in
  let uses =
    List.mapi fcall.args ~f:(fun idx arg ->
        let size = get_size arg in
        let op = param_map !base idx size in
        base := if idx < 6 then 0 else !base + Size.type_size_byte size;
        op)
  in
  let line = ({ defines; uses; live_out = []; move = false } : Dest.line) in
  base := 0;
  let params =
    List.mapi fcall.args ~f:(fun idx arg ->
        let src = trans_operand arg in
        let size = get_size' src in
        if idx < 6
        then (
          let dest = param_map !base idx size in
          let defines = [ dest ] in
          let uses = [ src ] in
          let line = ({ defines; uses; live_out = []; move = true } : Dest.line) in
          let mov = Dest.Mov { dest; src; line } in
          mov)
        else (
          let defines = [] in
          let uses = [ src ] in
          let line = ({ defines; uses; live_out = []; move = false } : Dest.line) in
          let push = Dest.Push { var = src; line } in
          push))
  in
  let scope = gen_scope fcall.scope in
  let fcall = Dest.Fcall { func_name; args; line; scope } in
  match dest with
  | None -> fcall :: params
  | Some dest ->
    let ret_size = get_size' dest in
    let ret_line =
      ({ defines = [ dest ]
       ; uses = [ Dest.Reg { reg = rax; size = ret_size } ]
       ; live_out = []
       ; move = true
       }
        : Dest.line)
    in
    let ret =
      Dest.Mov { dest; src = Dest.Reg { reg = rax; size = ret_size }; line = ret_line }
    in
    ret :: fcall :: params
;;

(* Generate instruction with x86 conventions *)
let rec gen_body (program : Src.instr list) (res : Dest.instr list) (exit_label : Label.t)
    : Dest.instr list
  =
  match program with
  | [] -> List.rev res
  | h :: t ->
    let inst =
      match h with
      | Binop bin -> gen_binop (Binop bin)
      | Mov move -> gen_move (Mov move)
      | Jump jump -> gen_jump (Jump jump)
      | CJump cjump -> gen_cjump (CJump cjump)
      | Ret ret -> gen_ret (Ret ret) exit_label
      | Label l -> [ Dest.Label { label = l; line = empty_line () } ]
      | Directive dir -> [ Dest.Directive dir ]
      | Comment cmt -> [ Dest.Comment cmt ]
      | Assert asrt -> gen_asrt (Assert asrt)
      | Fcall fcall -> gen_fcall (Fcall fcall)
    in
    gen_body t (inst @ res) exit_label
;;

(* Generate move instruction for callee-saved register of define info *)
let save_callee () : Dest.instr list =
  let size = Size.QWORD in
  List.fold Reg.callee_saved ~init:[] ~f:(fun acc r ->
      let t = Temp.create size in
      let line =
        { defines = [ Dest.Temp t ]
        ; uses = [ Dest.Reg { reg = r; size } ]
        ; move = true
        ; live_out = []
        }
      in
      let mov = Dest.Mov { dest = Dest.Temp t; src = Dest.Reg { reg = r; size }; line } in
      mov :: acc)
  |> List.rev
;;

(* Generate move instruction for callee-saved register of uses info 
 * Then, return the function *)
let gen_epilogue (prologue : Dest.instr list) : Dest.instr list =
  let restore =
    List.rev prologue
    |> List.map ~f:(fun inst ->
           let dest, src =
             match inst with
             | Dest.Mov mov -> mov.src, mov.dest
             | _ -> failwith "mov missing"
           in
           let line =
             { defines = [ dest ]; uses = [ src ]; live_out = []; move = true }
           in
           Dest.Mov { dest; src; line })
  in
  let line = empty_line () in
  let line_ret = { line with uses = [ Dest.Reg { reg = rax; size = QWORD } ] } in
  let ret = Dest.Ret { line = line_ret } in
  restore @ [ ret ]
;;

let cast (src : operand) (size : Size.primitive) : Dest.instr list * operand =
  let size' = get_size' src in
  if phys_equal size' size
  then [], src
  else (
    let dest = set_size src size in
    let line = { defines = [ dest ]; uses = [ src ]; live_out = []; move = true } in
    [ Mov { dest; src; line } ], dest)
;;

(* Generate assigning parameter passing code. Parameters are passed through
 * registers(first 6 parameters) or memories(rest parameters)  during function call. *)
let gen_pars (pars : Temp.t list) : Dest.instr list =
  let base = ref 0 in
  List.mapi pars ~f:(fun idx par ->
      if idx < 6
      then (
        let size = get_size (Src.Temp par) in
        let src = param_map !base idx size in
        let dest = trans_operand (Src.Temp par) in
        let line = { defines = [ dest ]; uses = [ src ]; live_out = []; move = true } in
        [ Mov { dest; src; line } ])
      else (
        let exp_size = get_size (Src.Temp par) in
        (* expected size, may not be QWORD but above_frame can only pass by QWORD *)
        let src = param_map !base idx exp_size in
        let cast_size, src' = cast src exp_size in
        let dest = trans_operand (Src.Temp par) in
        let line = { defines = [ dest ]; uses = [ src' ]; live_out = []; move = true } in
        base := !base + Size.type_size_byte QWORD;
        cast_size @ [ Mov { dest; src = src'; line } ]))
  |> List.concat
;;

let gen_section (prefix : string) (fname : Symbol.t) (content : Dest.instr list)
    : Dest.section * Label.t
  =
  let label = Label.label (Some (prefix ^ Symbol.name fname)) in
  let name = Dest.Label { label; line = empty_line () } in
  { name; content }, label
;;

let gen_program prologue body epilogue : instr list =
  let prologue = prologue.name :: prologue.content in
  let body = body.name :: body.content in
  let epilogue = epilogue.name :: epilogue.content in
  prologue @ body @ epilogue
;;

(* Let register allocation alg handle prologue and epilogue. *)
let rec gen (program : Src.program) (res : Dest.program) : Dest.program =
  match program with
  | [] -> List.rev res
  | h :: t ->
    let pars = gen_pars h.pars in
    let save = save_callee () in
    let epilogue_content = gen_epilogue save in
    let prologue, _ = gen_section "pro_" h.func_name (save @ pars) in
    let epilogue, exit_label = gen_section "epi_" h.func_name epilogue_content in
    let body_content = gen_body h.body [] exit_label in
    let body, _ = gen_section "body_" h.func_name body_content in
    let prog = gen_program prologue body epilogue in
    let fdefn = { func_name = "_c0_" ^ Symbol.name h.func_name; body = prog } in
    gen t (fdefn :: res)
;;
