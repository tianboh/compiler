
open Core

type t [@@deriving compare, sexp, hash]

include Comparable.S with type t := t

(* resets temp numbering *)
val reset : unit -> unit

(* returns a unique new temp *)
val create : unit -> t

(* returns the name of a temp *)
val reg_to_str : t -> string
