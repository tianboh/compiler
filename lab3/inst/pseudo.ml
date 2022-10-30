(* L1 Compiler
 * Assembly language
 * Author: Kaustuv Chaudhuri <kaustuv+@andrew.cmu.edu>
 * Modified By: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Currently just a pseudo language with 3-operand
 * instructions and arbitrarily many temps
*)
open Core
module Register = Var.X86_reg
module Temp = Var.Temp
open Var.Layout

(* Notice that pure pseudo assembly does not assign register to each temp, so 
   operand does not contain register type. Register is assigned in x86 assemb. 
   
   However, when we use gen_pseudo_x86 function, the operand will contain x86 register
   because of some conventions.
*)
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
  | Directive of string
  | Comment of string

(* functions that format assembly output *)


let format_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | And -> "&&"
  | Or -> "||"
  | Pand -> "&"
  | Por -> "|"
  | Pxor -> "^"
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
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;

(* let gen_x86_operand (op : operand) (reg_alloc_info : Register.t Temp.Map.t) : X86.operand = match op with
  | Temp t -> X86.Reg (Temp.Map.find_exn reg_alloc_info t)
  | Imm i -> X86.Imm i
;; *)

(* let gen_x86_inst (inst) : = match inst with
  | Binop bin_op -> 
      { op = X86.Binop
      ; dest = X86.operand
      ; lhs : X86.operand
      ; rhs : X86.operand
      }
  | Mov mov ->  of
      { dest : Temp.t
      ; src : operand
      }
  | Directive dir -> of string
  | Comment cmt -> of string *)

;;