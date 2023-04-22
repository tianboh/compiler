module Register = Var.X86_reg
module Memory = Var.Memory
module Label = Util.Label

open Var.Layout

type operand =
  | Imm of Int32.t
  | Reg of Register.t
  | Mem of Memory.t

type instr =
  | Add of
      { src : operand
      ; dest : operand
      ; layout : layout
      }
  | Sub of
      { src : operand
      ; dest : operand
      ; layout : layout
      }
  | Mul of
      { src : operand
      ; dest : operand
      ; layout : layout
      } (* Destination is form of EDX:EAX by default. Only one operand required. *)
  | Div of
      { src : operand
      ; layout : layout
      }
  (* temp := EDX:EAX / SRC;
            IF temp > FFFFFFFFH
                THEN #DE; (* Divide error *)
            ELSE
                EAX := temp;
                EDX := EDX:EAX MOD SRC;
            FI; *)
  | Mod of
      { src : operand
      ; layout : layout
      } (* Similar as above, but use edx after div.*)
  | Mov of
      { dest : operand
      ; src : operand
      ; layout : layout
      }
  | Cvt of { layout : layout } (*could be cdq, cqo, etc based on size it wants to extend. EDX:EAX := sign-extend of EAX *)
  | Ret
  | Pop of
      { reg : operand
      ; layout : layout
      }
  | Push of
      { reg : operand
      ; layout : layout
      }
  | Cmp of
      { lhs : operand
      ; rhs : operand
      ; layout : layout
      }
  | LAHF (* Load: AH := flags SF ZF xx AF xx PF xx CF *)
  | SAHF (* Store AH into flags SF ZF xx AF xx PF xx CF *)
  | Label of Label.t
  | Jump of Label.t
  (* Conditional jump family *)
  | JE of Label.t (* Jump if equal, ZF = 1 *)
  | JNE of Label.t (* Jump if not equal, ZF = 0 *)
  | JL of Label.t (* Jump if less, <, SF <> OF *)
  | JLE of Label.t (* Jump if less or equal, <=, ZF = 1 or SF <> OF *)
  | JG of Label.t (* Jump if greater, >, ZF = 0 and SF = OF *)
  | JGE of Label.t (* Jump if greater or equal, >=, SF = OF *)
  (* SETCC family. Notice it can only set 8-bit operand to register, 
   * so it only works for %al, %bl, %cl and %dl. We use %al by default. *)
  | SETE of
      { (* Set byte if equal (ZF=1). layout is a placeholder for dest,
         * it can only be BYTE *)
        dest : operand
      ; layout : layout
      }
  | SETNE of
      { dest : operand
      ; layout : layout
      }
  | SETL of
      { dest : operand
      ; layout : layout
      }
  | SETLE of
      { dest : operand
      ; layout : layout
      }
  | SETG of
      { dest : operand
      ; layout : layout
      }
  | SETGE of
      { dest : operand
      ; layout : layout
      }
  | AND of
      { (* bitwise and *)
        src : operand
      ; dest : operand
      ; layout : layout
      }
  | OR of
      { (* bitwise and *)
        src : operand
      ; dest : operand
      ; layout : layout
      }
  | XOR of
      { src : operand
      ; dest : operand
      ; layout : layout
      }
  | SAL of
      { src : operand
      ; dest : operand
      ; layout : layout
      }
  | SAR of
      { src : operand
      ; dest : operand
      ; layout : layout
      }
  | GDB of string
  | Directive of string
  | Comment of string

val format_prologue : int -> string
val format_epilogue : unit -> string
val format : instr -> string
val format_operand : operand -> layout -> string
val safe_mov : operand -> operand -> layout -> instr list
val safe_add : operand -> operand -> layout -> instr list
val safe_sub : operand -> operand -> layout -> instr list
val safe_and : operand -> operand -> layout -> instr list
val safe_or : operand -> operand -> layout -> instr list
val safe_xor : operand -> operand -> layout -> instr list
val safe_sal : operand -> operand -> layout -> Label.t -> instr list
val safe_sar : operand -> operand -> layout -> Label.t -> instr list
val safe_ret : operand -> layout -> instr list
val safe_cmp : operand -> operand -> layout -> Register.t  -> instr list