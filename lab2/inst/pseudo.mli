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
 * because there is no statement anymore.
 * 3) Also, the operand for instruction is not nested anymore.
 * For example, IR level support:
 *   type exp = | binop {op; lhs : exp; rhs : exp}
 * However, in pseudo code assembly, operand of binop can only 
 * be of Imm, Temp or reg.
 *)
module Register = Var.X86_reg
module Temp = Var.Temp
module Label = Util.Label

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

type instr =
  (* dest <- lhs op rhs *)
  | Binop of
      { op : bin_op
      ; dest : operand
      ; lhs : operand
      ; rhs : operand
      }
  (* dest <- src *)
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
  | Label of Label.t
  (* Assembly directive. *)
  | Directive of string
  (* Human-friendly comment. *)
  | Comment of string

val format : instr -> string
val format_operand : operand -> string
