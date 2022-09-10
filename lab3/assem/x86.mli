module Register = Register.X86_reg

type operand =
| Imm of Int32.t
| Reg of Register.reg
| Temp of Temp.t

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
