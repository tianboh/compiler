(* Sized functor. 
 * Input should obey Interface signature.
 * Generated module obeys Sized_Interface signature.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module type Interface = sig
  type t

  val pp : t -> string
end

module type Sized_Interface = sig
  type i

  type t =
    { data : i
    ; size : Size.primitive
    }

  val get_data : t -> i
  val wrap : Size.primitive -> i -> t
  val pp : t -> string
  val get_size : t -> Size.t
  val get_size_p : t -> Size.primitive
end

module Wrapper (M : Interface) : Sized_Interface with type i = M.t = struct
  type i = M.t

  type t =
    { data : i
    ; size : Size.primitive
    }

  let wrap size (exp : i) : t = { data = exp; size }
  let pp (sexp : t) : string = M.pp sexp.data ^ "_" ^ Size.pp_size (sexp.size :> Size.t)
  let get_data sexp : i = sexp.data
  let get_size (sexp : t) : Size.t = (sexp.size :> Size.t)
  let get_size_p (sexp : t) : Size.primitive = sexp.size
end
