module Register = Register.X86_reg.Register

type operand =
[ `Imm of Int32.t
| `Reg of Register.t]

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
    (* | Add of {src:[`Reg of Register.t]; dest:[`Reg of Register.t]} *)
    (* dest <- lhs op rhs *)
    | Binop of
        { op : bin_op
        ; dest : [`Reg of Register.t]
        ; lhs : operand
        ; rhs : operand
        }
    (* dest <- src *)
    | Mov of
        { dest : [`Reg of Register.t]
        ; src : [`Reg of Register.t]
        }
    | Ret
    (* Assembly directive. *)
    | Directive of string
    (* Human-friendly comment. *)
    | Comment of string

val format : instr -> string
