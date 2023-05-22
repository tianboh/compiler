(* L3 x86 convention
 * Transfrom from Middle Inst to x86 Inst with convention
 * This is done by providing each instruction with different
 * defines/uses operand. Compared with Middle Inst, this
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
module Src = Middle.Inst
module Dest = Inst
module Reg = Var.X86_reg
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

(* Generate x86 instr with binop convention *)
let[@warning "-8"] gen_binop (Src.Binop bin) =
  let op, dest, lhs, rhs =
    ( trans_binop bin.op
    , trans_operand bin.dest
    , trans_operand bin.lhs
    , trans_operand bin.rhs )
  in
  let defines =
    match op with
    | Times -> [ dest; Dest.Reg rax ]
    | Divided_by | Modulo -> [ dest; Dest.Reg rax; Dest.Reg rdx ]
    | Right_shift | Left_shift -> [ dest; Dest.Reg rcx ]
    | Equal_eq | Greater | Greater_eq | Less | Less_eq | Not_eq -> [ dest; Dest.Reg rax ]
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

let[@warning "-8"] gen_ret (Src.Ret ret) =
  let line = empty_line () in
  let uses_ret = List.map Register.callee_saved ~f:(fun r -> Dest.Reg r) in
  let line_ret = { line with uses = Dest.Reg rax :: uses_ret } in
  let mov =
    match ret.var with
    | None -> []
    | Some var ->
      let src = trans_operand var in
      let line_mov =
        { line with defines = [ Dest.Reg rax ]; uses = [ src ]; move = true }
      in
      [ Dest.Mov { dest = Dest.Reg rax; src; line = line_mov } ]
  in
  Dest.Ret { line = line_ret } :: mov
;;

let[@warning "-8"] gen_asrt (Src.Assert asrt) =
  let line = empty_line () in
  let line = { line with defines = [ Dest.Reg rax ]; uses = [ trans_operand asrt ] } in
  let var = trans_operand asrt in
  [ Dest.Assert { var; line } ]
;;

let param_map idx : Dest.operand =
  match idx with
  | 0 -> Dest.Reg RDI
  | 1 -> Dest.Reg RSI
  | 2 -> Dest.Reg RDX
  | 3 -> Dest.Reg RCX
  | 4 -> Dest.Reg R8
  | 5 -> Dest.Reg R9
  | _ -> failwith "not support passing >6 params yet"
;;

(* Generate x86 instr with function call convention *)
let[@warning "-8"] gen_fcall (Src.Fcall fcall) =
  let func_name = fcall.func_name in
  let dest = trans_operand (Src.Temp fcall.dest) in
  let args = List.map fcall.args ~f:(fun arg -> trans_operand arg) in
  let x86_regs = Reg.caller_saved @ Reg.parameters in
  let defines = dest :: List.map x86_regs ~f:(fun reg -> Dest.Reg reg) in
  let uses = List.mapi fcall.args ~f:(fun idx _ -> param_map idx) in
  let line = ({ defines; uses; live_out = []; move = false } : Dest.line) in
  let movs =
    List.mapi fcall.args ~f:(fun idx arg ->
        let dest = param_map idx in
        let src = trans_operand arg in
        let defines = [ dest ] in
        let uses = [ src ] in
        let line = ({ defines; uses; live_out = []; move = true } : Dest.line) in
        let mov = Dest.Mov { dest; src; line } in
        mov)
  in
  let fcall = Dest.Fcall { func_name; args; line } in
  let ret_line =
    ({ defines = [ dest ]; uses = [ Dest.Reg rax ]; live_out = []; move = true }
      : Dest.line)
  in
  let ret = Dest.Mov { dest; src = Dest.Reg rax; line = ret_line } in
  ret :: fcall :: List.rev movs
;;

(* Generate instruction with x86 conventions *)
let rec gen_body (program : Src.instr list) (res : Dest.instr list) : Dest.instr list =
  match program with
  | [] -> List.rev res
  | h :: t ->
    let inst =
      match h with
      | Binop bin -> gen_binop (Binop bin)
      | Mov move -> gen_move (Mov move)
      | Jump jump -> gen_jump (Jump jump)
      | CJump cjump -> gen_cjump (CJump cjump)
      | Ret ret -> gen_ret (Ret ret)
      | Label l -> [ Dest.Label { label = l; line = empty_line () } ]
      | Directive dir -> [ Dest.Directive dir ]
      | Comment cmt -> [ Dest.Comment cmt ]
      | Assert asrt -> gen_asrt (Assert asrt)
      | Fcall fcall -> gen_fcall (Fcall fcall)
    in
    gen_body t (inst @ res)
;;

(* Generate move instruction for callee-saved register of define info
 * Then *)
let gen_prologue () : Dest.instr list =
  List.fold Register.callee_saved ~init:[] ~f:(fun acc r ->
      let t = Temp.create () in
      let line =
        { defines = [ Dest.Temp t ]; uses = [ Dest.Reg r ]; move = true; live_out = [] }
      in
      let mov = Dest.Mov { dest = Dest.Temp t; src = Dest.Reg r; line } in
      mov :: acc)
  |> List.rev
;;

(* Generate move instruction for callee-saved register of uses info *)
let gen_epilogue (prologue : Dest.instr list) : Dest.instr list =
  List.rev prologue
  |> List.map ~f:(fun inst ->
         let dest =
           match inst with
           | Dest.Mov mov -> mov.src
           | _ -> failwith "mov missing"
         in
         let src =
           match inst with
           | Dest.Mov mov -> mov.dest
           | _ -> failwith "mov missing"
         in
         let line = { defines = [ dest ]; uses = [ src ]; live_out = []; move = true } in
         Dest.Mov { dest; src; line })
;;

(* Generate assigning parameter passing code. Parameters are passed through
 * registers or memories during function call. *)
let gen_pars (pars : Temp.t list) : Dest.instr list =
  List.mapi pars ~f:(fun idx par ->
      let src = param_map idx in
      let dest = trans_operand (Src.Temp par) in
      let line = { defines = [ dest ]; uses = [ src ]; live_out = []; move = true } in
      Mov { dest; src; line })
;;

(* Let register allocation alg handle prologue and epilogue. *)
let rec gen (program : Src.program) (res : Dest.program) : Dest.program =
  match program with
  | [] -> List.rev res
  | h :: t ->
    let pars = gen_pars h.pars in
    let pro = gen_prologue () in
    let body = gen_body h.body [] in
    let epi = gen_epilogue pro in
    gen t ({ func_name = h.func_name; body = pars @ pro @ body @ epi } :: res)
;;
