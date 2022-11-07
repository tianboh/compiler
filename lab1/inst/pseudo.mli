(* L1 Compiler
 * Assembly language
 * Author: Kaustuv Chaudhuri <kaustuv+@andrew.cmu.edu>
 * Modified By: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Currently just a pseudo language with 3-operand
 * instructions and arbitrarily many temps
 *
*)
module Register = Var.X86_reg
module Temp = Var.Temp

type operand =
  | Imm of Int32.t
  | Temp of Temp.t
  | Reg of Register.t

type bin_op =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | And
  | Or
  | Pand
  | Por
  | Pxor

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
  (* Assembly directive. *)
  | Directive of string
  (* Human-friendly comment. *)
  | Comment of string

val format : instr -> string

val format_operand : operand -> string