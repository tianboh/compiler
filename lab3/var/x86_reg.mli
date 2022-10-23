
open Core
(* module Temp = Temp.Temp *)
type t [@@deriving compare, sexp, hash]

include Comparable.S with type t := t

(* Create a register with index *)
val create_no : int -> t

val find_min_available : Set.t -> int

val name : t -> string

(* returns the name of a temp *)
val reg_to_str : t -> string

val reg_to_tmp : t -> Temp.t

val str_to_reg : string -> t

val special_use : t -> bool

val swap : unit -> t

val tmp_to_reg : Temp.t -> t
