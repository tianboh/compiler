(* Memory
 * Memory used for x86 convention.
 * Base pointer + offset is the memory adress to inquire. 
 * WARNNING: offset is not index! It should be multiple of 0x8, 0x10, or 0x20.
 * Dataload size is the size to fetch on the memory address.
 * Author: tianboh
 *)

 open Core

 module T = struct
   type t = 
   {  base : int
    ; offset : int
    ; size : int
   }[@@deriving sexp, compare, hash]
 end
 include T
 
 let create base offset size =
   {
    base; offset; size
   }
 ;;
 
 let name t = Printf.sprintf "[0x%08x]%d" t.base t.offset
 
 include Comparable.Make (T)