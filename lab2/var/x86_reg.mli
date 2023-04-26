open Core
open Layout

(* module Temp = Temp.Temp *)
type t [@@deriving compare, sexp, hash]

include Comparable.S with type t := t

(* Create a register with index *)
val create_no : int -> t

(* returns the name of a temp *)
val reg_to_str : ?layout:layout -> t -> string
val reg_idx : t -> int
(* val reg_to_tmp : t -> Temp.t *)
val str_to_reg : string -> t
val swap : unit -> t
val callee_saved : unit -> Set.t
val caller_saved : unit -> Set.t
val num_spill_reg : unit -> int
val need_spill : t -> bool
val get_base_pointer : unit -> t
val spilled_idx : t -> int

(* Number of hard registers *)
val num_gen_reg : int