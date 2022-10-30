(* 
 * This file is a register module. 
 * It will create register by sequence after the first 16 x86 determined register.
*)

open Core
open Layout

module T = struct
  type t = int [@@deriving sexp, compare, hash]
end
include T

include Comparable.Make (T)

(* 
   ESP(7) and EBP(8) are used to store stack pointer and base pointer respectively, 
   we should not assign these two registers for general purpose use like register allocation. 
   We also preserver r16(16) as a swap register, and do not assign it for register allocation.
*)
let special_use = function
| 7 | 8 | 15 -> true
| _ -> false
;;

let alloc_cnt = ref 0

let num_gen_reg = 15

let create_no (n : int) : t = 
  incr alloc_cnt;
  let t = n in
  t
;;

(* find minimum available register with neighbor nbr *)
let find_min_available (nbr : Set.t) : int =
  let rec helper (idx : t ) (nbr : Set.t) = 
    if special_use idx 
      then helper (idx + 1) nbr
      else 
        if Set.mem nbr idx
          then helper (idx + 1) nbr
          else idx
  in
  helper 5 nbr
;;

(* We only have 15 general purpose register, and we obey x86 64bit register name format.
   For register greater than 15, we spill them to memory, and we name them as %sxxx where
   xxx is index of that register. So xxx is >= 16.   
*)
let name (t : int) (layout : layout) = 
  if t < 16 
    then match layout with
      | BYTE -> "%r" ^ string_of_int t ^ "b"
      | WORD -> "%r" ^ string_of_int t ^ "w"
      | DWORD -> "%r" ^ string_of_int t ^ "d"
      | QWORD -> "%r" ^ string_of_int t
  else
    "%s" ^ string_of_int t

let reg_to_str ?(layout=DWORD) (idx : int) = match idx, layout with
  | 1, BYTE  -> "%al"
  | 2, BYTE  -> "%bl"
  | 3, BYTE  -> "%cl"
  | 4, BYTE  -> "%dl"
  | 5, BYTE  -> failwith "cannot access low 8-bit in %rsi"
  | 6, BYTE  -> failwith "cannot access low 8-bit in %rdi"
  | 7, BYTE  -> failwith "cannot access low 8-bit in %rbp"
  | 8, BYTE  -> failwith "cannot access low 8-bit in %rsp"
  | 1, WORD  -> "%ax"
  | 2, WORD  -> "%bx"
  | 3, WORD  -> "%cx"
  | 4, WORD  -> "%dx"
  | 5, WORD  -> "%si"
  | 6, WORD  -> "%di"
  | 7, WORD  -> "%bp"
  | 8, WORD  -> "%sp"
  | 1, DWORD  -> "%eax"
  | 2, DWORD  -> "%ebx"
  | 3, DWORD  -> "%ecx"
  | 4, DWORD  -> "%edx"
  | 5, DWORD  -> "%esi"
  | 6, DWORD  -> "%edi"
  | 7, DWORD  -> "%ebp"
  | 8, DWORD  -> "%esp"
  | 1, QWORD  -> "%rax"
  | 2, QWORD  -> "%rbx"
  | 3, QWORD  -> "%rcx"
  | 4, QWORD  -> "%rdx"
  | 5, QWORD  -> "%rsi"
  | 6, QWORD  -> "%rdi"
  | 7, QWORD  -> "%rbp"
  | 8, QWORD  -> "%rsp"
  | _ -> name idx layout
;;

let reg_idx (t : t) : int = t

let str_to_reg (str : string) = match str with
| "%rax" | "%eax" | "%ax" | "%al" -> 1
| "%rbx" | "%ebx" | "%bx" | "%bl" -> 2
| "%rcx" | "%ecx" | "%cx" | "%cl" -> 3
| "%rdx" | "%edx" | "%dx" | "%dl" -> 4
| "%rsi" | "%esi" | "%si" -> 5
| "%rdi" | "%edi" | "%di" -> 6
| "%rbp" | "%ebp" | "%bp" -> 7
| "%rsp" | "%esp" | "%sp" -> 8
| "%r9"  | "%r9d" | "%r9w" | "%r9b" -> 9
| "%r10" | "%r10d"| "%r10w"| "%r10b"-> 10
| "%r11" | "%r11d"| "%r11w"| "%r11b"-> 11
| "%r12" | "%r12d"| "%r12w"| "%r12b"-> 12
| "%r13" | "%r13d"| "%r13w"| "%r13b"-> 13
| "%r14" | "%r14d"| "%r14w"| "%r14b"-> 14
| "%r15" | "%r15d"| "%r15w"| "%r15b"-> 15
| s ->
  let str_l = String.split_on_chars ~on:['s'] s in
  Int.of_string (List.last_exn str_l)
;;

let swap () = 15
;;

(* 
  callee-saved registers are EBX(2), EDI(6), and ESI(5) 
  ESP(8) and EBP(7) will also be preserved by the calling convention, 
  but need not be pushed on the stack during calling a function.   
*)
let callee_saved () = Set.of_list [2; 6; 5; 8; 7]
;;

(* Caller-saved register are EAX(1), ECX(3), and EDX(4) *)
let caller_saved () = Set.of_list [1; 3; 4]
;;

let reg_to_tmp idx = Temp.create_no (-idx)
;;

let tmp_to_reg (tmp : Temp.t) = -(Temp.value tmp)
;;

(* number of spilled register so far *)
let num_spill_reg () =
  if !alloc_cnt < 16 then 0
  else !alloc_cnt - 15
;;

let need_spill t = if t <= num_gen_reg then false else true
;;

let get_base_pointer () = 7

let spilled_idx (t : t) : int = t - num_gen_reg