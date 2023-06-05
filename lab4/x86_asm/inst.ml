(* L3 x86 assembly 
 * 
 * Provide function call based on l2
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
module Register = Var.X86_reg
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

let shift_maximum_bit = Int32.of_int_exn 31 (* inclusive *)

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_mov (dest : operand) (src : operand) (size : Size.t) =
  match dest, src with
  | Mem dest, Mem src ->
    [ Mov { dest = Reg Register.swap; src = Mem src; size }
    ; Mov { dest = Mem dest; src = Reg Register.swap; size }
    ]
  | _ -> [ Mov { dest; src; size } ]
;;

let safe_add (dest : operand) (src : operand) (size : Size.t) =
  match dest, src with
  | Mem dest, Mem src ->
    [ Mov { dest = Reg Register.swap; src = Mem src; size }
    ; Add { dest = Mem dest; src = Reg Register.swap; size }
    ]
  | _ -> [ Add { dest; src; size } ]
;;

let safe_sub (dest : operand) (src : operand) (size : Size.t) =
  match dest, src with
  | Mem dest, Mem src ->
    [ Mov { dest = Reg Register.swap; src = Mem src; size }
    ; Sub { dest = Mem dest; src = Reg Register.swap; size }
    ]
  | _ -> [ Sub { dest; src; size } ]
;;

let safe_and (dest : operand) (src : operand) (size : Size.t) =
  match dest, src with
  | Mem dest, Mem src ->
    [ Mov { dest = Reg Register.swap; src = Mem src; size }
    ; AND { dest = Mem dest; src = Reg Register.swap; size }
    ]
  | _ -> [ AND { dest; src; size } ]
;;

let safe_or (dest : operand) (src : operand) (size : Size.t) =
  match dest, src with
  | Mem dest, Mem src ->
    [ Mov { dest = Reg Register.swap; src = Mem src; size }
    ; OR { dest = Mem dest; src = Reg Register.swap; size }
    ]
  | _ -> [ OR { dest; src; size } ]
;;

let safe_xor (dest : operand) (src : operand) (size : Size.t) =
  match dest, src with
  | Mem dest, Mem src ->
    [ Mov { dest = Reg Register.swap; src = Mem src; size }
    ; XOR { dest = Mem dest; src = Reg Register.swap; size }
    ]
  | _ -> [ XOR { dest; src; size } ]
;;

(* shift bit should be [0, 31] *)
let shift_check (shift_bit : operand) (fpe_label : Label.t) =
  [ Cmp { lhs = shift_bit; rhs = Imm shift_maximum_bit; size = DWORD }
  ; JG fpe_label
  ; Cmp { lhs = shift_bit; rhs = Imm Int32.zero; size = DWORD }
  ; JL fpe_label
  ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sal (dest : operand) (src : operand) (size : Size.t) (fpe_label : Label.t) =
  match dest, src with
  | _, Reg _ | _, Mem _ ->
    let ecx = Register.RCX in
    (* when src is register/memory, SAL can only use %cl to shift. *)
    (Mov { dest = Reg ecx; src; size } :: shift_check (Reg ecx) fpe_label)
    @ [ SAL { dest; src = Reg ecx; size } ]
  | _ -> shift_check src fpe_label @ [ SAL { dest; src; size = BYTE } ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sar (dest : operand) (src : operand) (size : Size.t) (fpe_label : Label.t) =
  match dest, src with
  | _, Reg _ | _, Mem _ ->
    let ecx = Register.RCX in
    (* when src is register/memory, SAR can only use %cl to shift. *)
    (Mov { dest = Reg ecx; src; size } :: shift_check (Reg ecx) fpe_label)
    @ [ SAR { dest; src = Reg ecx; size } ]
  | _ -> shift_check src fpe_label @ [ SAR { dest; src; size = BYTE } ]
;;

let safe_ret (size : Size.t) =
  (* insts = [ "mov %rbp, %rsp"; "pop %rbp"; "ret" ] *)
  [ Mov { dest = Reg Register.RSP; src = Reg Register.RBP; size }
  ; Pop { var = Reg Register.RBP; size = QWORD }
  ; Ret
  ]
;;

(* Prepare for conditional jump. *)
let safe_cmp (lhs : operand) (rhs : operand) (size : Size.t) (swap : Register.t) =
  match lhs, rhs with
  | Mem _, Mem _ ->
    [ Mov { dest = Reg swap; src = lhs; size }; Cmp { lhs = Reg swap; rhs; size } ]
  | _ -> [ Cmp { lhs; rhs; size } ]
;;

let format_operand (oprd : operand) (size : Size.t) =
  match oprd with
  | Imm n -> "$" ^ Int32.to_string n
  | Reg r -> Register.reg_to_str ~size r
  | Mem m -> Memory.mem_to_str m
;;

let format_inst (size : Size.t) =
  match size with
  | BYTE -> "b"
  | WORD -> "w"
  | DWORD -> "l"
  | QWORD -> ""
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
      (format_operand add.src add.size)
      (format_operand add.dest add.size)
  | Sub sub ->
    sprintf
      "sub%s %s, %s"
      (format_inst sub.size)
      (format_operand sub.src sub.size)
      (format_operand sub.dest sub.size)
  | Mul mul ->
    sprintf
      "imul%s %s, %s"
      (format_inst mul.size)
      (format_operand mul.src mul.size)
      (format_operand mul.dest mul.size)
  | Div div ->
    sprintf "idiv%s %s" (format_inst div.size) (format_operand div.src div.size)
  | Mod m -> sprintf "div %s" (format_operand m.src m.size)
  | Cvt cvt ->
    (match cvt.size with
    | BYTE -> failwith "nothing to extend for byte"
    | WORD -> "cwd"
    | DWORD -> "cdq"
    | QWORD -> "cqo")
  | Mov mv ->
    sprintf
      "mov%s %s, %s"
      (format_inst mv.size)
      (format_operand mv.src mv.size)
      (format_operand mv.dest mv.size)
  | Ret -> "ret"
  | Push push ->
    sprintf "push%s %s" (format_inst push.size) (format_operand push.var push.size)
  | Pop pop -> sprintf "pop%s %s" (format_inst pop.size) (format_operand pop.var pop.size)
  | Cmp cmp ->
    sprintf
      "cmp%s %s, %s"
      (format_inst cmp.size)
      (format_operand cmp.rhs cmp.size)
      (format_operand cmp.lhs cmp.size)
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
  | SETE sete -> sprintf "sete %s" (format_operand sete.dest sete.size)
  | SETNE setne -> sprintf "setne %s" (format_operand setne.dest setne.size)
  | SETL setl -> sprintf "setl %s" (format_operand setl.dest setl.size)
  | SETLE setle -> sprintf "setle %s" (format_operand setle.dest setle.size)
  | SETG setg -> sprintf "setg %s" (format_operand setg.dest setg.size)
  | SETGE setge -> sprintf "setge %s" (format_operand setge.dest setge.size)
  | AND a ->
    sprintf
      "and%s %s, %s"
      (format_inst a.size)
      (format_operand a.src a.size)
      (format_operand a.dest a.size)
  | OR a ->
    sprintf
      "or%s %s, %s"
      (format_inst a.size)
      (format_operand a.src a.size)
      (format_operand a.dest a.size)
  | XOR xor ->
    sprintf
      "xor%s %s, %s"
      (format_inst xor.size)
      (format_operand xor.src xor.size)
      (format_operand xor.dest xor.size)
  | SAR sar ->
    sprintf
      "sar%s %s, %s"
      (format_inst sar.size)
      (format_operand sar.src BYTE)
      (format_operand sar.dest sar.size)
  | SAL sal ->
    sprintf
      "sal%s %s, %s"
      (format_inst sal.size)
      (format_operand sal.src BYTE)
      (format_operand sal.dest sal.size)
  | Fcall fcall ->
    sprintf "call %s%s" (format_scope fcall.scope) (Symbol.name fcall.func_name)
  | Fname fname -> sprintf "%s:" fname
  | Abort -> sprintf "call abort"
  | GDB gdb -> sprintf "%s" gdb
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;