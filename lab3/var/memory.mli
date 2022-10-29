(* 
 * Memory
 * Author: tianboh
 *)

 open Core

 type t [@@deriving compare, sexp, hash]
 (* include Hashtbl.S with type t := t *)
 include Comparable.S with type t := t

 (* returns a unique new memory *)
 val create : int -> X86_reg.t -> int -> int -> t

 (* returns the address of a memory *)
 val mem_to_str : t -> string

 (* transform from spill register to memory *)
 val from_reg : X86_reg.t -> t