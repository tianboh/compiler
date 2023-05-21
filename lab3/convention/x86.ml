(* L2 x86 convention
 * Transfrom from Middle Inst to x86 Inst with convention
 * This is done by providing each instruction with different
 * defines/uses operand. Compared with Middle Inst, this
 * layer has extra register type for operand. 
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

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
  Dest.Binop { op; dest; lhs; rhs; line }
;;

let[@warning "-8"] gen_move (Src.Mov move) =
  let dest, src = trans_operand move.dest, trans_operand move.src in
  let line = { defines = [ dest ]; uses = [ src ]; live_out = []; move = true } in
  Dest.Mov { dest; src; line }
;;

let[@warning "-8"] gen_jump (Src.Jump jump) =
  let line = empty_line () in
  Dest.Jump { target = jump.target; line }
;;

let[@warning "-8"] gen_cjump (Src.CJump cjump) =
  let lhs, rhs = trans_operand cjump.lhs, trans_operand cjump.rhs in
  let op = trans_binop cjump.op in
  let line = { defines = []; uses = [ lhs; rhs ]; live_out = []; move = false } in
  Dest.CJump
    { lhs
    ; op
    ; rhs
    ; target_true = cjump.target_true
    ; target_false = cjump.target_false
    ; line
    }
;;

let[@warning "-8"] gen_ret (Src.Ret ret) =
  let line = empty_line () in
  let line = { line with defines = [ Dest.Reg rax ]; uses = [ trans_operand ret.var ] } in
  let var = trans_operand ret.var in
  Dest.Ret { var; line }
;;

(* Generate instruction with x86 conventions *)
let rec gen (program : Src.program) (res : Dest.program) : Dest.program =
  match program with
  | [] -> List.rev res
  | h :: t ->
    (match h with
    | Binop bin ->
      let bin' = gen_binop (Binop bin) in
      gen t (bin' :: res)
    | Mov move ->
      let move' = gen_move (Mov move) in
      gen t (move' :: res)
    | Jump jump ->
      let jump' = gen_jump (Jump jump) in
      gen t (jump' :: res)
    | CJump cjump ->
      let cjump' = gen_cjump (CJump cjump) in
      gen t (cjump' :: res)
    | Ret ret ->
      let ret' = gen_ret (Ret ret) in
      gen t (ret' :: res)
    | Label l ->
      let l' = Dest.Label { label = l; line = empty_line () } in
      gen t (l' :: res)
    | Directive dir ->
      let dir' = Dest.Directive dir in
      gen t (dir' :: res)
    | Comment cmt ->
      let cmt' = Dest.Comment cmt in
      gen t (cmt' :: res))
;;
