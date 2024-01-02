(* Memory
 * Memory used for x86 convention.
 * Base pointer + offset is the memory adress to inquire. 
 * WARNNING: offset is not index! It should be multiple of 0x8, 0x10, or 0x20.
 * Dataload size is the size to fetch on the memory address.
 *
 * Author: tianboh
 *)

open Core
(* open Size *)

let ( + ) = Base.Int64.( + )
let ( - ) = Base.Int64.( - )
let ( * ) = Base.Int64.( * )
let ( / ) = Base.Int64.( / )

module T = struct
  type reg = X86_reg.Hard.t

  type t =
    { index : int option (* This is a global unique id for memory.*)
    ; base : reg
    ; offset :
        (* base + offset is start address of a variable *)
        [ `Imm of Int64.t | `Reg of reg ]
    }
end

include T

let counter = ref 0L
let bias = ref 0L
let get_allocated_count () = !counter
let rbp : reg = X86_reg.Hard.wrap `QWORD X86_reg.Logic.RBP
let cache : t Int.Table.t = Int.Table.create ()

let reset () : unit =
  Hashtbl.clear cache;
  counter := 0L;
  bias := 0L
;;

(* Create memory in stack. *)
let create index ?(base = rbp) size : t =
  if Hashtbl.mem cache index
  then Hashtbl.find_exn cache index
  else (
    Int64.incr counter;
    bias := !bias + Size.type_size_byte size;
    let mem = { index = Some index; base; offset = `Imm !bias } in
    Hashtbl.add_exn cache ~key:index ~data:mem;
    mem)
;;

let above_frame base offset =
  let offset = Int64.neg (offset + Size.type_size_byte `QWORD) in
  { index = None; base; offset = `Imm offset }
;;

let below_frame base offset =
  let offset = offset + Size.type_size_byte `QWORD in
  { index = None; base; offset = `Imm offset }
;;

let mem_to_str t =
  match t.offset with
  | `Imm imm -> Printf.sprintf "%Ld(%s)" (Int64.neg imm) (X86_reg.Hard.pp t.base)
  | `Reg reg ->
    Printf.sprintf "(%s, %s, 1)" (X86_reg.Hard.pp t.base) (X86_reg.Hard.pp reg)
;;

let mem_idx_exn (mem : t) =
  match mem.index with
  | None -> failwith "illegal access frame memory"
  | Some idx -> idx
;;
