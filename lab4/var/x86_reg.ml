(* 
 * This file is a register module for x86. 
 * There are only 16 general purpuse registers.
 * function names and registers names are self-explained.
 *
 * Author: Tianbo Hao<tianboh@alumni.cmu.edu>
 *)
open Core

(* Logical register is used for register allocation.
 * RAX, EAX, AX is treated as the same. *)
module Logic = struct
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

  let num_reg = 16

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

  let reg_to_str ?(size = `DWORD) (reg : t) =
    match reg, size with
    | RAX, `BYTE -> "%al"
    | RBX, `BYTE -> "%bl"
    | RCX, `BYTE -> "%cl"
    | RDX, `BYTE -> "%dl"
    | RSI, `BYTE -> failwith "cannot access low 8-bit in %rsi"
    | RDI, `BYTE -> failwith "cannot access low 8-bit in %rdi"
    | RBP, `BYTE -> failwith "cannot access low 8-bit in %rbp"
    | RSP, `BYTE -> failwith "cannot access low 8-bit in %rsp"
    | RAX, `WORD -> "%ax"
    | RBX, `WORD -> "%bx"
    | RCX, `WORD -> "%cx"
    | RDX, `WORD -> "%dx"
    | RSI, `WORD -> "%si"
    | RDI, `WORD -> "%di"
    | RBP, `WORD -> "%bp"
    | RSP, `WORD -> "%sp"
    | R8, `WORD -> "%r8w"
    | R9, `WORD -> "%r9w"
    | R10, `WORD -> "%r10w"
    | R11, `WORD -> "%r11w"
    | R12, `WORD -> "%r12w"
    | R13, `WORD -> "%r13w"
    | R14, `WORD -> "%r14w"
    | R15, `WORD -> "%r15w"
    | RAX, `DWORD -> "%eax"
    | RBX, `DWORD -> "%ebx"
    | RCX, `DWORD -> "%ecx"
    | RDX, `DWORD -> "%edx"
    | RSI, `DWORD -> "%esi"
    | RDI, `DWORD -> "%edi"
    | RBP, `DWORD -> "%ebp"
    | RSP, `DWORD -> "%esp"
    | R8, `DWORD -> "%r8d"
    | R9, `DWORD -> "%r9d"
    | R10, `DWORD -> "%r10d"
    | R11, `DWORD -> "%r11d"
    | R12, `DWORD -> "%r12d"
    | R13, `DWORD -> "%r13d"
    | R14, `DWORD -> "%r14d"
    | R15, `DWORD -> "%r15d"
    | RAX, `QWORD -> "%rax"
    | RBX, `QWORD -> "%rbx"
    | RCX, `QWORD -> "%rcx"
    | RDX, `QWORD -> "%rdx"
    | RSI, `QWORD -> "%rsi"
    | RDI, `QWORD -> "%rdi"
    | RBP, `QWORD -> "%rbp"
    | RSP, `QWORD -> "%rsp"
    | R8, `QWORD -> "%r8"
    | R9, `QWORD -> "%r9"
    | R10, `QWORD -> "%r10"
    | R11, `QWORD -> "%r11"
    | R12, `QWORD -> "%r12"
    | R13, `QWORD -> "%r13"
    | R14, `QWORD -> "%r14"
    | R15, `QWORD -> "%r15"
    | _ ->
      failwith
        (sprintf "illegal access %d with size %s" (reg_idx reg) (Size.pp_size size))
  ;;

  let swap = R15
  let callee_saved = [ RBX; R12; R13; R14; R15 ]
  let caller_saved = [ R10; R11 ]
  let parameters = [ RDI; RSI; RDX; RCX; R8; R9 ]
  let heap_base = R10
  let heap_index = R9

  (* ESP(6) and EBP(7) are used to store stack pointer and base pointer respectively, 
   * we should not assign these two registers for general purpose use like register allocation. 
   * R15(15) is swap register, and do not assign it for register allocation. *)
  let special_use = function
    | RBP | RSP | R15 -> true
    | _ -> false
  ;;
end

(* Hard register is logical register attached with size information
 * 1) used for x86 convention.
 * 2) register allocation result. *)
module Hard = struct
  type t =
    { reg : Logic.t
    ; size : Size.primitive
    }
  [@@deriving compare, sexp, hash]

  let reg_to_str (reg : t) : string = Logic.reg_to_str ~size:reg.size reg.reg
  let reg_idx (reg : t) : int = Logic.reg_idx reg.reg

  let idx_reg (idx : int) (size : Size.primitive) : t =
    let reg = Logic.idx_reg idx in
    { reg; size }
  ;;
end
