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
| 7 | 8 | 16 -> true
| _ -> false
;;

let alloc_cnt = ref 0

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
  helper 3 nbr
;;

let name t = 
  "%r" ^ string_of_int t ^ "d"

let reg_to_str (idx : int) = match idx with
  | 1  -> "%eax"
  | 2  -> "%edx"
  | 3  -> "%ebx"
  | 4  -> "%ecx"
  | 5  -> "%esi"
  | 6  -> "%edi"
  | 7  -> "%ebp"
  | 8  -> "%esp"
  | _ -> name idx
;;

let str_to_reg (str : string) = match str with
| "%eax" -> 1
| "%edx" -> 2
| "%ebx" -> 3
| "%ecx" -> 4
| "%esi" -> 5
| "%edi" -> 6
| "%ebp" -> 7
| "%esp" -> 8
| s -> 
  let str_l = String.split_on_chars ~on:['e'] s in
  Int.of_string (List.last_exn str_l)
;;

let swap () = 16
;;

let reg_to_tmp idx = Temp.create_no (-idx)

let tmp_to_reg (tmp : Temp.t) = -(Temp.value tmp)

;;

