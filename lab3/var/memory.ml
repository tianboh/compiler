(* Memory
 * Memory used for x86 convention.
 * Base pointer + offset is the memory adress to inquire. 
 * WARNNING: offset is not index! It should be multiple of 0x8, 0x10, or 0x20.
 * Dataload size is the size to fetch on the memory address.
 * Author: tianboh
 *)

open Core
open Layout

module T = struct
  type t =
    { index : int option (* This is a global unique id for memory.*)
    ; base : X86_reg.t
    ; offset : int (* base + offset * size is start address of a variable *)
    ; size : int (* size of corresponding variable, byte as unit.*)
    }
  [@@deriving sexp, compare, hash]
end

include T

let counter = ref 0
let get_allocated_count () = !counter
let reset () = counter := 0

let create index base offset size =
  incr counter;
  { index = Some index; base; offset; size }
;;

let get_mem base offset size = { index = None; base; offset; size }

let mem_to_str t =
  Printf.sprintf "%d(%s)" (t.offset * t.size) (X86_reg.reg_to_str ~layout:QWORD t.base)
;;

let mem_idx_exn (mem : t) =
  match mem.index with
  | None -> failwith "illegal access frame memory"
  | Some idx -> idx
;;

include Comparable.Make (T)
