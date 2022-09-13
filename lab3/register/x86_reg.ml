(* 
   This file is a register module. 
   It will create register by sequence after the first 16 x86 determined register.
*)

open Core

type t = int [@@deriving sexp, compare, hash]

let counter = ref 1
let reset () = counter := 1

let create () =
  let t = !counter in
  incr counter;
  t
;;

let name t = 
  "%r" ^ string_of_int t

let reg_to_str (idx : int) = match idx with
  | 1  -> "%EAX"
  | 2  -> "%EBX"
  | 3  -> "%ECX"
  | 4  -> "%EDX"
  | 5  -> "%ESI"
  | 6  -> "%EDI"
  | 7  -> "%EDP"
  | 8  -> "%ESP"
  | _ -> name idx
;;

include Comparable.Make (Int)