(* L3 x86 assembly 
 * 
 * Provide function call based on l2
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
module Register = Var.X86_reg.Hard
module Memory = Var.Memory
module Label = Util.Label
module Symbol = Util.Symbol
module Size = Var.Size

type scope =
  | Internal
  | External

type operand =
  | Imm of Int32.t
  | Reg of Register.t
  | Mem of Memory.t

type instr =
  | Add of
      { src : operand
      ; dest : operand
      ; size : Size.t
      }
  | Sub of
      { src : operand
      ; dest : operand
      ; size : Size.t
      }
  | Mul of
      { src : operand
      ; dest : operand
      ; size : Size.t
      } (* Destination is form of EDX:EAX by default. Only one operand required. *)
  | Div of
      { src : operand
      ; size : Size.t
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
      ; size : Size.t
      } (* Similar as above, but use edx after div.*)
  | Mov of
      { dest : operand
      ; src : operand
      ; size : Size.t
      }
  | Cvt of { size : Size.t } (*could be cdq, cqo, etc based on size it wants to extend. EDX:EAX := sign-extend of EAX *)
  | Ret
  | Pop of
      { var : operand
      ; size : Size.t
      }
  | Push of
      { var : operand
      ; size : Size.t
      }
  | Cmp of
      { lhs : operand
      ; rhs : operand
      ; size : Size.t
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
      { (* Set byte if equal (ZF=1). size is a placeholder for dest,
         * it can only be BYTE *)
        dest : operand
      ; size : Size.t
      }
  | SETNE of
      { dest : operand
      ; size : Size.t
      }
  | SETL of
      { dest : operand
      ; size : Size.t
      }
  | SETLE of
      { dest : operand
      ; size : Size.t
      }
  | SETG of
      { dest : operand
      ; size : Size.t
      }
  | SETGE of
      { dest : operand
      ; size : Size.t
      }
  | AND of
      { (* bitwise and *)
        src : operand
      ; dest : operand
      ; size : Size.t
      }
  | OR of
      { (* bitwise and *)
        src : operand
      ; dest : operand
      ; size : Size.t
      }
  | XOR of
      { src : operand
      ; dest : operand
      ; size : Size.t
      }
  | SAL of
      { (* Inst size is same as dest. 
         * Immediate is 8bit, memory/register(%cl) is 16bit *)
        src : operand
      ; dest : operand
      ; size : Size.t
      }
  | SAR of
      { (* Inst size is same as dest. 
         * Immediate is 8bit, memory/register(%cl) is 16bit *)
        src : operand
      ; dest : operand
      ; size : Size.t
      }
  | Fcall of
      { func_name : Symbol.t
      ; scope : scope
      }
  | Abort
  | Fname of string
  | GDB of string
  | Directive of string
  | Comment of string

type fdefn =
  { func_name : Symbol.t
  ; body : instr list
  }

type program = fdefn list

let format_operand (oprd : operand) =
  match oprd with
  | Imm n -> "$" ^ Int32.to_string n
  | Reg r -> Register.reg_to_str r
  | Mem m -> Memory.mem_to_str m
;;

let format_operand_size (oprd : operand) : Size.t =
  match oprd with
  | Imm _ -> DWORD
  | Reg r -> r.size
  | Mem m -> m.size
;;

let format_inst (size : Size.t) =
  match size with
  | BYTE -> "b"
  | WORD -> "w"
  | DWORD -> "l"
  | QWORD -> ""
  | VOID -> ""
;;

let format_scope = function
  | Internal -> "_c0_"
  | External -> ""
;;

(* functions that format assembly output *)
let format = function
  (* We use AT&T x86 convention to generate x86 assembly code. *)
  | Add add ->
    sprintf
      "add%s %s, %s"
      (format_inst add.size)
      (format_operand add.src)
      (format_operand add.dest)
  | Sub sub ->
    sprintf
      "sub%s %s, %s"
      (format_inst sub.size)
      (format_operand sub.src)
      (format_operand sub.dest)
  | Mul mul ->
    sprintf
      "imul%s %s, %s"
      (format_inst mul.size)
      (format_operand mul.src)
      (format_operand mul.dest)
  | Div div -> sprintf "idiv%s %s" (format_inst div.size) (format_operand div.src)
  | Mod m -> sprintf "div %s" (format_operand m.src)
  | Cvt cvt ->
    (match cvt.size with
    | VOID | BYTE -> failwith "nothing to extend for byte/void"
    | WORD -> "cwd"
    | DWORD -> "cdq"
    | QWORD -> "cqo")
  | Mov mv ->
    sprintf
      "mov%s %s, %s"
      (format_inst (format_operand_size mv.dest))
      (* (format_inst mv.size) *)
      (format_operand mv.src)
      (format_operand mv.dest)
  | Ret -> "ret"
  | Push push -> sprintf "push%s %s" (format_inst push.size) (format_operand push.var)
  | Pop pop -> sprintf "pop%s %s" (format_inst pop.size) (format_operand pop.var)
  | Cmp cmp ->
    sprintf
      "cmp%s %s, %s"
      (format_inst cmp.size)
      (format_operand cmp.rhs)
      (format_operand cmp.lhs)
  | LAHF -> "lahf"
  | SAHF -> "sahf"
  | Label l -> Label.content l
  | Jump jp -> sprintf "jmp %s" (Label.name jp)
  | JE je -> sprintf "je %s" (Label.name je)
  | JNE jne -> sprintf "jne %s" (Label.name jne)
  | JL jl -> sprintf "jl %s" (Label.name jl)
  | JLE jle -> sprintf "jle %s" (Label.name jle)
  | JG jg -> sprintf "jg %s" (Label.name jg)
  | JGE jge -> sprintf "jge %s" (Label.name jge)
  | SETE sete -> sprintf "sete %s" (format_operand sete.dest)
  | SETNE setne -> sprintf "setne %s" (format_operand setne.dest)
  | SETL setl -> sprintf "setl %s" (format_operand setl.dest)
  | SETLE setle -> sprintf "setle %s" (format_operand setle.dest)
  | SETG setg -> sprintf "setg %s" (format_operand setg.dest)
  | SETGE setge -> sprintf "setge %s" (format_operand setge.dest)
  | AND a ->
    sprintf
      "and%s %s, %s"
      (format_inst a.size)
      (format_operand a.src)
      (format_operand a.dest)
  | OR a ->
    sprintf
      "or%s %s, %s"
      (format_inst a.size)
      (format_operand a.src)
      (format_operand a.dest)
  | XOR xor ->
    sprintf
      "xor%s %s, %s"
      (* (format_inst xor.size) *)
      (format_inst (format_operand_size xor.dest))
      (format_operand xor.src)
      (format_operand xor.dest)
  | SAR sar ->
    sprintf
      "sar%s %s, %s"
      (format_inst sar.size)
      (format_operand sar.src)
      (format_operand sar.dest)
  | SAL sal ->
    sprintf
      "sal%s %s, %s"
      (format_inst sal.size)
      (format_operand sal.src)
      (format_operand sal.dest)
  | Fcall fcall ->
    sprintf "call %s%s" (format_scope fcall.scope) (Symbol.name fcall.func_name)
  | Fname fname -> sprintf "%s:" fname
  | Abort -> sprintf "call abort"
  | GDB gdb -> sprintf "%s" gdb
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;
