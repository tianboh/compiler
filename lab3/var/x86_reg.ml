(* 
   This file is a register module. 
   It will create register by sequence after the first 16 x86 determined register.
*)

open Core
(* module Temp = Temp.Temp *)

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
let name (t : int) = 
  if t < 16 
    then "%r" ^ string_of_int t
  else
    "%s" ^ string_of_int t

let reg_to_str (idx : int) = match idx with
  | 1  -> "%rax"
  | 2  -> "%rbx"
  | 3  -> "%rcx"
  | 4  -> "%rdx"
  | 5  -> "%rsi"
  | 6  -> "%rdi"
  | 7  -> "%rbp"
  | 8  -> "%rsp"
  | _ -> name idx
;;

let str_to_reg (str : string) = match str with
| "%rax" -> 1
| "%rbx" -> 2
| "%rcx" -> 3
| "%rdx" -> 4
| "%rsi" -> 5
| "%rdi" -> 6
| "%rbp" -> 7
| "%rsp" -> 8
| "%r9"  -> 9
| "%r10" -> 10
| "%r11" -> 11
| "%r12" -> 12
| "%r13" -> 13
| "%r14" -> 14
| "%r15" -> 15
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