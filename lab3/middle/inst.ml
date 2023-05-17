(* L2 Compiler
 * Assembly language
 * Created: Kaustuv Chaudhuri <kaustuv+@andrew.cmu.edu>
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu>
 * Modified By: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Pseudo assembly code feature
 * 1) 3-operand format instructions and arbitrarily many temps.
 * These temps will be mapped to registers eventually.
 * 2) Compared with IR, pseudo assembly code is more low-level
 * because there is no statement anymore. In fact, IR statement
 * is more of instruction and IR exp is more of operand.
 * 3) Also, the operand for instruction is not nested anymore.
 * For example, IR level support:
 *   type exp = | binop {op; lhs : exp; rhs : exp}
 * However, in pseudo code assembly, operand of binop can only 
 * be of Imm, Temp or reg.
 *)
open Core
module Register = Var.X86_reg
module Temp = Var.Temp
module Label = Util.Label

(* Notice that pure pseudo assembly does not assign register to each temp, so 
 * operand does not contain register type. Register is assigned in x86 assemb. 
 *  
 * However, when we use gen_pseudo_x86 function, the operand will contain x86 
 * register because of some conventions.
 *)
type operand =
  | Imm of Int32.t
  | Temp of Temp.t

type bin_op =
  | Plus
  | Minus
  | Times
  | Divided_by
  | Modulo
  | And
  | Or
  | Xor
  | Right_shift
  | Left_shift
  | Equal_eq
  | Greater
  | Greater_eq
  | Less
  | Less_eq
  | Not_eq

type instr =
  | Binop of
      { op : bin_op
      ; dest : operand
      ; lhs : operand
      ; rhs : operand
      }
  | Mov of
      { dest : operand
      ; src : operand
      }
  | Jump of { target : Label.t }
  | CJump of
      { (*Jump if cond == 1*)
        lhs : operand
      ; op : bin_op
      ; rhs : operand
      ; target : Label.t
      }
  | Ret of { var : operand }
  | Label of Label.t
  | Directive of string
  | Comment of string

(* functions that format assembly output *)

let pp_binop = function
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Divided_by -> "/"
  | Modulo -> "%"
  | And -> "&"
  | Or -> "|"
  | Xor -> "^"
  | Right_shift -> ">>"
  | Left_shift -> "<<"
  | Equal_eq -> "=="
  | Greater -> ">"
  | Greater_eq -> ">="
  | Less -> "<"
  | Less_eq -> "<="
  | Not_eq -> "!="
;;

let pp_operand = function
  | Imm n -> "$" ^ Int32.to_string n
  | Temp t -> Temp.name t
;;

let pp_instr = function
  | Binop binop ->
    sprintf
      "%s <-- %s %s %s"
      (pp_operand binop.dest)
      (pp_operand binop.lhs)
      (pp_binop binop.op)
      (pp_operand binop.rhs)
  | Mov mv -> sprintf "%s <-- %s" (pp_operand mv.dest) (pp_operand mv.src)
  | Jump jp -> sprintf "jump %s" (Label.name jp.target)
  | CJump cjp ->
    sprintf
      "cjump(%s %s %s) %s"
      (pp_operand cjp.lhs)
      (pp_binop cjp.op)
      (pp_operand cjp.rhs)
      (Label.name cjp.target)
  | Label label -> sprintf "%s" (Label.content label)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Ret ret -> sprintf "return %s" (pp_operand ret.var)
;;

let rec pp_program (program : instr list) res =
  match program with
  | [] -> res
  | h :: t ->
    let inst_str = pp_instr h ^ "\n" in
    let res = res ^ inst_str in
    pp_program t res
;;
