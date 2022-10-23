(* 
 * Memory
 * Author: tianboh
 *)

 open Core

 type t [@@deriving compare, sexp, hash]
 (* include Hashtbl.S with type t := t *)
 include Comparable.S with type t := t
 (* resets temp numbering *)
 (* returns a unique new temp *)
 val create : int -> int -> int -> t
 (* returns the name of a temp *)
 val name : t -> string