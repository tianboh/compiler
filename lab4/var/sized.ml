module type Interface = sig
  type t

  val pp_exp : t -> string
end

module type Sized_Interface = sig
  type i

  type t =
    { data : i
    ; size : Size.primitive
    }

  val get_data : t -> i
  val wrap : Size.primitive -> i -> t
  val pp_sexp : t -> string
  val get_size : t -> Size.t
  val get_size_p : t -> Size.primitive
end

module Wrapper (M : Interface) = struct
  type i = M.t

  type t =
    { data : i
    ; size : Size.primitive
    }

  let wrap size (exp : i) : t = { data = exp; size }

  let pp_sexp (sexp : t) : string =
    M.pp_exp sexp.data ^ "_" ^ Size.pp_size (sexp.size :> Size.t)
  ;;

  let get_data sexp : i = sexp.data
  let get_size (sexp : t) : Size.t = (sexp.size :> Size.t)
  let get_size_p (sexp : t) : Size.primitive = sexp.size
end
