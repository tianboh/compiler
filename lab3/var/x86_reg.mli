
open Core
(* module Temp = Temp.Temp *)
type t [@@deriving compare, sexp, hash]

include Comparable.S with type t := t

(* Create a register with index *)
val create_no : int -> t

val find_min_available : Set.t -> int

(* returns the name of a temp *)
val reg_to_str : t -> string

val reg_to_tmp : t -> Temp.t

val str_to_reg : string -> t

val special_use : t -> bool

val swap : unit -> t

val callee_saved : unit -> Set.t

val caller_saved : unit -> Set.t

val tmp_to_reg : Temp.t -> t

val num_spill_reg : unit -> int

val need_spill : t -> bool

val get_base_pointer : unit -> t

val spilled_idx : t -> int