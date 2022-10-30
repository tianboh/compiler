module Register = Var.X86_reg
module Memory = Var.Memory
open Var.Layout

type operand =
  | Imm of Int32.t
  | Reg of Register.t
  | Mem of Memory.t

type instr =
  | Add of {src:operand; dest:operand; layout:layout}
  | Sub of {src:operand; dest:operand; layout:layout}
  | Mul of {src:operand; layout:layout}
  | Div of {src:operand; layout:layout}
  | Mod of {src:operand; layout:layout}
    (* dest <- lhs op rhs *)
    (* | Binop of
        { op : bin_op
        ; dest : [`Reg of Register.t]
        ; lhs : operand
        ; rhs : operand
        } *)
    (* dest <- src *)
    | Mov of {dest:operand; src:operand; layout:layout}
    | Cvt of {layout:layout}
    | Ret
    (* Assembly directive. *)
    | Directive of string
    (* Human-friendly comment. *)
    | Comment of string

val format_prologue : int -> string

val format_epilogue : unit -> string

val format : instr -> string

val format_operand : operand -> layout -> string

val safe_mov : operand -> operand -> layout -> instr list

val safe_add : operand -> operand -> layout -> instr list

val safe_sub : operand -> operand -> layout -> instr list
