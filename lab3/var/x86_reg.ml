(* 
 * This file is a register module. 
 * It will create register by sequence after the first 16 x86 determined register.
 *)
open Core
open Layout

type t =
  | RAX
  | RBX
  | RCX
  | RDX
  | RSI
  | RDI
  | RBP
  | RSP
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
[@@deriving compare, sexp, hash]

(* 
 * ESP(7) and EBP(8) are used to store stack pointer and base pointer respectively, 
 * we should not assign these two registers for general purpose use like register allocation. 
 * We also preserver r15(15) as a swap register, and do not assign it for register allocation.
 * We also preserve EAX(1) and EDX(4) because they are treated special in mul, mod, and mul op.
 * ECX(3) is preserved for left/right shift.
 *)
let special_use = function
  | RAX | RCX | RDX | RSP | RBP | R15 -> true
  | _ -> false
;;

let num_reg = 16

let reg_to_str ?(layout = DWORD) (reg : t) =
  match reg, layout with
  | RAX, BYTE -> "%al"
  | RBX, BYTE -> "%bl"
  | RCX, BYTE -> "%cl"
  | RDX, BYTE -> "%dl"
  | RSI, BYTE -> failwith "cannot access low 8-bit in %rsi"
  | RDI, BYTE -> failwith "cannot access low 8-bit in %rdi"
  | RBP, BYTE -> failwith "cannot access low 8-bit in %rbp"
  | RSP, BYTE -> failwith "cannot access low 8-bit in %rsp"
  | RAX, WORD -> "%ax"
  | RBX, WORD -> "%bx"
  | RCX, WORD -> "%cx"
  | RDX, WORD -> "%dx"
  | RSI, WORD -> "%si"
  | RDI, WORD -> "%di"
  | RBP, WORD -> "%bp"
  | RSP, WORD -> "%sp"
  | R8, WORD -> "%r8w"
  | R9, WORD -> "%r9w"
  | R10, WORD -> "%r10w"
  | R11, WORD -> "%r11w"
  | R12, WORD -> "%r12w"
  | R13, WORD -> "%r13w"
  | R14, WORD -> "%r14w"
  | R15, WORD -> "%r15w"
  | RAX, DWORD -> "%eax"
  | RBX, DWORD -> "%ebx"
  | RCX, DWORD -> "%ecx"
  | RDX, DWORD -> "%edx"
  | RSI, DWORD -> "%esi"
  | RDI, DWORD -> "%edi"
  | RBP, DWORD -> "%ebp"
  | RSP, DWORD -> "%esp"
  | R8, DWORD -> "%r8d"
  | R9, DWORD -> "%r9d"
  | R10, DWORD -> "%r10d"
  | R11, DWORD -> "%r11d"
  | R12, DWORD -> "%r12d"
  | R13, DWORD -> "%r13d"
  | R14, DWORD -> "%r14d"
  | R15, DWORD -> "%r15d"
  | RAX, QWORD -> "%rax"
  | RBX, QWORD -> "%rbx"
  | RCX, QWORD -> "%rcx"
  | RDX, QWORD -> "%rdx"
  | RSI, QWORD -> "%rsi"
  | RDI, QWORD -> "%rdi"
  | RBP, QWORD -> "%rbp"
  | RSP, QWORD -> "%rsp"
  | R8, QWORD -> "%r8"
  | R9, QWORD -> "%r9"
  | R10, QWORD -> "%r10"
  | R11, QWORD -> "%r11"
  | R12, QWORD -> "%r12"
  | R13, QWORD -> "%r13"
  | R14, QWORD -> "%r14"
  | R15, QWORD -> "%r15"
  | _ -> failwith "illegal access"
;;

let reg_idx = function
  | RAX -> 0
  | RBX -> 1
  | RCX -> 2
  | RDX -> 3
  | RSI -> 4
  | RDI -> 5
  | RBP -> 6
  | RSP -> 7
  | R8 -> 8
  | R9 -> 9
  | R10 -> 10
  | R11 -> 11
  | R12 -> 12
  | R13 -> 13
  | R14 -> 14
  | R15 -> 15
;;

let idx_reg = function
  | 0 -> RAX
  | 1 -> RBX
  | 2 -> RCX
  | 3 -> RDX
  | 4 -> RSI
  | 5 -> RDI
  | 6 -> RBP
  | 7 -> RSP
  | 8 -> R8
  | 9 -> R9
  | 10 -> R10
  | 11 -> R11
  | 12 -> R12
  | 13 -> R13
  | 14 -> R14
  | 15 -> R15
  | _ -> failwith "invalid index for reg"
;;

let tmp_to_reg (tmp : Temp.t) = -Temp.value tmp

let str_to_reg (str : string) =
  match String.lowercase str with
  | "%rax" | "%eax" | "%ax" | "%al" -> RAX
  | "%rbx" | "%ebx" | "%bx" | "%bl" -> RBX
  | "%rcx" | "%ecx" | "%cx" | "%cl" -> RCX
  | "%rdx" | "%edx" | "%dx" | "%dl" -> RDX
  | "%rsi" | "%esi" | "%si" -> RSI
  | "%rdi" | "%edi" | "%di" -> RDI
  | "%rbp" | "%ebp" | "%bp" -> RBP
  | "%rsp" | "%esp" | "%sp" -> RSP
  | "%r8" | "%r8d" | "%r8w" | "%r8b" -> R8
  | "%r9" | "%r9d" | "%r9w" | "%r9b" -> R9
  | "%r10" | "%r10d" | "%r10w" | "%r10b" -> R10
  | "%r11" | "%r11d" | "%r11w" | "%r11b" -> R11
  | "%r12" | "%r12d" | "%r12w" | "%r12b" -> R12
  | "%r13" | "%r13d" | "%r13w" | "%r13b" -> R13
  | "%r14" | "%r14d" | "%r14w" | "%r14b" -> R14
  | "%r15" | "%r15d" | "%r15w" | "%r15b" -> R15
  | _ -> failwith "not x86-64 register"
;;

let swap = R15
let base_pointer = RBP
let callee_saved = [ RBX; RDI; RSI; RSP; RBP ]
let caller_saved = [ RAX; RCX; RDX ]
