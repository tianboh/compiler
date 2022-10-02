(* 
   This file is a register module. 
   It will create register by sequence after the first 16 x86 determined register.
*)

open Core
module Temp = Temp.Temp

module Register = struct
  module T = struct
    type t = int [@@deriving sexp, compare, hash]
  end
  include T

  let counter = ref 1
  let reset () = counter := 1

  let create () =
    let t = !counter in
    incr counter;
    t
  ;;

  let create_no (n:int) : t = 
    let t = n in
    t
  ;;

  let create_pp t =
    t + 1
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

  let reg_to_tmp idx = Temp.create_no (-idx)

  let tmp_to_reg (tmp : Temp.t) = -(Temp.value tmp)

  ;;

  include Comparable.Make (T)
end
