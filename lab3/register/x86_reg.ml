(* 
   This file is a register module. 
   It will create register by sequence after the first 16 x86 determined register.
*)

open Core

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
    "%R" ^ string_of_int t

  let reg_to_str (idx : int) = match idx with
    | 1  -> "%eax"
    | 2  -> "%ebx"
    | 3  -> "%ecx"
    | 4  -> "%edx"
    | 5  -> "%esi"
    | 6  -> "%edi"
    | 7  -> "%edp"
    | 8  -> "%esp"
    | _ -> name idx
  ;;

  include Comparable.Make (T)
end
