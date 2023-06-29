(* Memory
 * Memory used for x86 convention.
 * Base pointer + offset is the memory adress to inquire. 
 * WARNNING: offset is not index! It should be multiple of 0x8, 0x10, or 0x20.
 * Dataload size is the size to fetch on the memory address.
 * Author: tianboh
 *)

open Core
(* open Size *)

let ( + ) = Base.Int64.( + )
let ( - ) = Base.Int64.( - )
let ( * ) = Base.Int64.( * )
let ( / ) = Base.Int64.( / )

module T = struct
  type t =
    { index : int option (* This is a global unique id for memory.*)
    ; base : X86_reg.Logic.t
    ; offset : Int64.t (* base + offset is start address of a variable *)
    ; size : Size.primitive (* size of corresponding variable *)
    }
  [@@deriving sexp, compare, hash]
end

include T

let counter = ref 0L
let bias = ref 0L
let get_allocated_count () = !counter

let reset () =
  counter := 0L;
  bias := 0L
;;

let create index base size =
  Int64.incr counter;
  bias := !bias + Size.type_size_byte size;
  { index = Some index; base; size; offset = !bias }
;;

let above_frame base offset size =
  let offset = Int64.neg (offset + Size.type_size_byte `QWORD) in
  { index = None; base; offset; size }
;;

let below_frame base offset size =
  let offset = offset + Size.type_size_byte `QWORD in
  { index = None; base; offset; size }
;;

let mem_to_str t =
  Printf.sprintf
    "%Ld(%s)"
    (Int64.neg t.offset)
    (X86_reg.Logic.reg_to_str ~size:`QWORD t.base)
;;

let mem_idx_exn (mem : t) =
  match mem.index with
  | None -> failwith "illegal access frame memory"
  | Some idx -> idx
;;

include Comparable.Make (T)
