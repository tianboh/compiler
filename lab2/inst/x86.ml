(* 
 * L1 x86 assembly   
 *)

open Core
module Register = Var.X86_reg
module Memory = Var.Memory
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
  | Cvt of { layout : layout } (*could be cdq, cqo, etc based on size it wants to extend.*)
  | Ret
  | Pop of
      { reg : operand
      ; layout : layout
      }
  | Push of
      { reg : operand
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
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;
