
open Core
module Temp = Temp.Temp
module Register : sig
    type t [@@deriving compare, sexp, hash]

    include Comparable.S with type t := t

    (* resets temp numbering *)
    val reset : unit -> unit

    (* returns a unique new register *)
    val create : unit -> t

    (* Create a register with index *)
    val create_no : int -> t

    (* Return a register with number equals to numbers + 1 *)
    val create_pp : t -> t

    (* val name : t -> string *)

    (* returns the name of a temp *)
    val reg_to_str : t -> string

    val reg_to_tmp : t -> Temp.t

    val str_to_reg : string -> t

    val tmp_to_reg : Temp.t -> t

end