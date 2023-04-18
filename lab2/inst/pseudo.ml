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
open Var.Layout

(* Notice that pure pseudo assembly does not assign register to each temp, so 
 * operand does not contain register type. Register is assigned in x86 assemb. 
 *  
 * However, when we use gen_pseudo_x86 function, the operand will contain x86 
 * register because of some conventions.
 *)
type operand =
  | Imm of Int32.t
  | Temp of Temp.t
  | Reg of Register.t

type bin_op =
  | Plus
  | Minus
  | Times
  | Divided_by
  | Modulo
  | And
  | Or
  | Hat
  | Right_shift
  | Left_shift
  | Equal_eq
  | Greater
  | Greater_eq
  | Less
  | Less_eq
  | Not_eq

(* | T.Hat -> check https://www.madwizard.org/programming/snippets?id=36 *)

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
        cond : operand
      ; target : Label.t
      }
  | Ret of { var : operand }
  | Label of Label.t
  | Directive of string
  | Comment of string

(* functions that format assembly output *)

let format_binop = function
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Divided_by -> "/"
  | Modulo -> "%"
  | And -> "&"
  | Or -> "|"
  | Hat -> "^"
  | Right_shift -> ">>"
  | Left_shift -> "<<"
  | Equal_eq -> "=="
  | Greater -> ">"
  | Greater_eq -> ">="
  | Less -> "<"
  | Less_eq -> "<="
  | Not_eq -> "!="
;;

let format_operand = function
  | Imm n -> "$" ^ Int32.to_string n
  | Temp t -> Temp.name t
  | Reg r -> Register.reg_to_str ~layout:DWORD r
;;

let format = function
  | Binop binop ->
    sprintf
      "%s <-- %s %s %s"
      (format_operand binop.dest)
      (format_operand binop.lhs)
      (format_binop binop.op)
      (format_operand binop.rhs)
  | Mov mv -> sprintf "%s <-- %s" (format_operand mv.dest) (format_operand mv.src)
  | Jump jp -> sprintf "jump %s" (Label.name jp.target)
  | CJump cjp -> sprintf "cjump(%s) %s" (format_operand cjp.cond) (Label.name cjp.target)
  | Label label -> sprintf "%s" (Label.name label)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Ret ret -> sprintf "return %s" (format_operand ret.var)
;;
