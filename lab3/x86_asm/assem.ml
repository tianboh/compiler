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

type bin_op =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | And
  | Or

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

let reg_to_str = function
  | EAX  -> "%eax"
  | EBX  -> "%ebx"
  | ECX  -> "%ecx"
  | EDX  -> "%edx"
  | ESI  -> "%esi"
  | EDI  -> "%edi"
  | EBP  -> "%ebp"
  | ESP  -> "%esp"
  | E8D  -> "%e8d"
  | E9D  -> "%e9d"
  | E10D -> "%e10d"
  | E11D -> "%e11d"
  | E12D -> "%e12d"
  | E13D -> "%e13d"
  | E14D -> "%e14d"
  | E15D -> "%e15d"
;;

let str_to_reg = function
  | "%eax" -> EAX 
  | "%ebx" -> EBX 
  | "%ecx" -> ECX 
  | "%edx" -> EDX 
  | "%esi" -> ESI 
  | "%edi" -> EDI 
  | "%ebp" -> EBP 
  | "%esp" -> ESP 
  | "%e8d" -> E8D 
  | "%e9d" -> E9D 
  | "%e10d" -> E10D
  | "%e11d" -> E11D
  | "%e12d" -> E12D
  | "%e13d" -> E13D
  | "%e14d" -> E14D
  | "%e15d" -> E15D
  | _ -> EAX
;;


let format_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | And -> "&&"
  | Or -> "||"
;;

let format_operand = function
  | Imm n -> "$" ^ Int32.to_string n
  | Temp t -> Temp.name t
  | Reg r -> reg_to_str r
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
