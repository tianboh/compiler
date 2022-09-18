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
      ; dest : Register.t
      ; lhs : operand
      ; rhs : operand
      }
  | Mov of
      { dest : Register.t
      ; src : operand
      }
  | Ret
  | Directive of string
  | Comment of string

(* functions that format assembly output *)


(* x <- x bin_op y *)
let format_binop = function
  | Add -> "addl"
  | Sub -> "subl"
  | Mul -> "mul"
  | Div -> "div"
  | Mod -> "div"
  | And -> "&&"
  | Or -> "||"
  | Pand -> "and"
  | Por -> "or"
  | Pxor -> "xor"
;;

let format_operand = function
  | Imm n -> "$" ^ Int32.to_string n
  | Reg r -> Register.reg_to_str r
;;

let format = function
  (* It's quite tricky for the order of binary operand here. 
     dest <- dest(lhs_operand) bin_op rhs_operand equivalents to assembly code
     bin_op rhs_operand, dest
  *)
  | Binop binop ->
    sprintf
      "%s %s, %s"
      (format_binop binop.op)
      (format_operand binop.rhs)
      (format_operand (Reg binop.dest))
  | Mov mv -> sprintf "movl %s, %s"  (format_operand mv.src) (format_operand (Reg mv.dest))
  | Ret -> sprintf "ret"
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;
