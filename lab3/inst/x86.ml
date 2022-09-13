(* 
  L1 x86 assembly   
*)

open Core
module Register = Register.X86_reg.Register

type operand =
  | Imm of Int32.t
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
  | Reg r -> Register.reg_to_str r
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
