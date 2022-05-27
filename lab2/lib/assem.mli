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

type reg = 
  | EAX
  | EBX
  | ECX
  | EDX
  | ESI
  | EDI
  | EBP
  | ESP
  | E8D
  | E9D
  | E10D
  | E11D
  | E12D
  | E13D
  | E14D
  | E15D

type operand =
  | Imm of Int32.t
  | Reg of reg
  | Temp of Temp.t

type operation =
  | Add
  | Sub
  | Mul
  | Div
  | Mod

type instr =
  (* dest <- lhs op rhs *)
  | Binop of
      { op : operation
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

val reg_to_str : reg -> string

val str_to_reg : string -> reg