(* L2 x86 assembly 
 * 
 * Provide new instruction compared with L1
 * 1) Operation related: 
 * 2) Control flow related:
 * 3) Flag related: 
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
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
  | AND of
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
  | Directive of string
  | Comment of string

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_mov (dest : operand) (src : operand) (layout : layout) =
  match dest, src with
  | Mem dest, Mem src ->
    [ Mov { dest = Reg (Register.swap ()); src = Mem src; layout }
    ; Mov { dest = Mem dest; src = Reg (Register.swap ()); layout }
    ]
  | _ -> [ Mov { dest; src; layout } ]
;;

let safe_add (dest : operand) (src : operand) (layout : layout) =
  match dest, src with
  | Mem dest, Mem src ->
    [ Mov { dest = Reg (Register.swap ()); src = Mem src; layout }
    ; Add { dest = Mem dest; src = Reg (Register.swap ()); layout }
    ]
  | _ -> [ Add { dest; src; layout } ]
;;

let safe_sub (dest : operand) (src : operand) (layout : layout) =
  match dest, src with
  | Mem dest, Mem src ->
    [ Mov { dest = Reg (Register.swap ()); src = Mem src; layout }
    ; Sub { dest = Mem dest; src = Reg (Register.swap ()); layout }
    ]
  | _ -> [ Sub { dest; src; layout } ]
;;

let safe_ret (dest : operand) (layout : layout) =
  (* insts = [ "mov %rbp, %rsp"; "pop %rbp"; "ret" ] *)
  [ Mov { dest = Reg (Register.create_no 1); src = dest; layout = DWORD }
  ; Mov { dest = Reg (Register.create_no 8); src = Reg (Register.create_no 7); layout }
  ; Pop { reg = Reg (Register.create_no 7); layout = QWORD }
  ; Ret
  ]
;;

(* Prepare for conditional jump. *)
let safe_cmp (lhs : operand) (rhs : operand) (layout : layout) (swap : Register.t) =
  (* | Not_eq ->
      [ AS_x86.Mov { dest; src = eax; layout = DWORD }
      ; AS_x86.Mov { dest = AS_x86.Reg swap; src = lhs; layout = DWORD }
      ; AS_x86.XOR { dest = eax; src = eax; layout = DWORD }
      ; AS_x86.Cmp { lhs = AS_x86.Reg swap; rhs; layout = DWORD }
      ; AS_x86.SETNE { dest = eax; layout = BYTE }
      ; AS_x86.Mov { dest = AS_x86.Reg swap; src = eax; layout = DWORD }
      ; AS_x86.Mov { dest = eax; src = dest; layout = DWORD }
      ; AS_x86.Mov { dest; src = AS_x86.Reg swap; layout = DWORD }
      ] *)
  (* [ Mov { dest = swap_reg; src = Mem lhs_mem; layout }
    ; Cmp { lhs = swap_reg; rhs = Mem rhs_mem; layout }
    ; Mov { dest = Mem lhs_mem; src = swap_reg; layout }
    ] *)
  match lhs, rhs with
  | Mem _, Mem _ ->
    [ Mov { dest = Reg swap; src = lhs; layout }; Cmp { lhs = Reg swap; rhs; layout } ]
  | _ -> [ Cmp { lhs; rhs; layout } ]
;;

(* prologue for a callee function. Handle callee-saved registers and allocate space for local variables *)
let format_prologue (var_cnt : int) =
  let var_size = var_cnt * 8 in
  let insts = [ "\tpush %rbp"; "mov %rsp, %rbp"; sprintf "sub $%d, %%rsp" var_size ] in
  String.concat ~sep:"\n\t" insts
;;

(* epilogue for a callee function. Restore callee-saved registers and deallocate local variables. *)
let format_epilogue () =
  let insts = [ "mov %rbp, %rsp"; "pop %rbp"; "ret" ] in
  String.concat ~sep:"\n\t" insts
;;

let format_operand (oprd : operand) (layout : layout) =
  match oprd with
  | Imm n -> "$" ^ Int32.to_string n
  | Reg r -> Register.reg_to_str ~layout r
  | Mem m -> Memory.mem_to_str m
;;

let format_inst (layout : layout) =
  match layout with
  | BYTE -> "b"
  | WORD -> "w"
  | DWORD -> "l"
  | QWORD -> ""
;;

(* functions that format assembly output *)
let format = function
  (* We use AT&T x86 convention to generate x86 assembly code. *)
  | Add add ->
    sprintf
      "add%s %s, %s"
      (format_inst add.layout)
      (format_operand add.src add.layout)
      (format_operand add.dest add.layout)
  | Sub sub ->
    sprintf
      "sub%s %s, %s"
      (format_inst sub.layout)
      (format_operand sub.src sub.layout)
      (format_operand sub.dest sub.layout)
  | Mul mul ->
    sprintf
      "imul%s %s, %s"
      (format_inst mul.layout)
      (format_operand mul.src mul.layout)
      (format_operand mul.dest mul.layout)
  | Div div ->
    sprintf "idiv%s %s" (format_inst div.layout) (format_operand div.src div.layout)
  | Mod m -> sprintf "div %s" (format_operand m.src m.layout)
  | Cvt cvt ->
    (match cvt.layout with
    | BYTE -> failwith "nothing to extend for byte"
    | WORD -> "cwd"
    | DWORD -> "cdq"
    | QWORD -> "cqo")
  | Mov mv ->
    sprintf
      "mov%s %s, %s"
      (format_inst mv.layout)
      (format_operand mv.src mv.layout)
      (format_operand mv.dest mv.layout)
  | Ret -> "ret"
  | Push push ->
    sprintf "push%s %s" (format_inst push.layout) (format_operand push.reg push.layout)
  | Pop pop ->
    sprintf "pop%s %s" (format_inst pop.layout) (format_operand pop.reg pop.layout)
  | Cmp cmp ->
    sprintf
      "cmp%s %s, %s"
      (format_inst cmp.layout)
      (format_operand cmp.rhs cmp.layout)
      (format_operand cmp.lhs cmp.layout)
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
  | SETE sete -> sprintf "sete %s" (format_operand sete.dest sete.layout)
  | SETNE setne -> sprintf "setne %s" (format_operand setne.dest setne.layout)
  | AND a ->
    sprintf
      "and%s %s, %s"
      (format_inst a.layout)
      (format_operand a.src a.layout)
      (format_operand a.dest a.layout)
  | XOR xor ->
    sprintf
      "xor%s %s, %s"
      (format_inst xor.layout)
      (format_operand xor.src xor.layout)
      (format_operand xor.dest xor.layout)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;
