(* General Purpose Address.
 * Works on different levels, including IR, Quads, Abstract assembly.
 * In order to generate this address module at its level,
 * provide operand following signature Op, then Wrapper will
 * return a module following Sig signature.
 *
 * Make sure to expose the type i to outside when calling functor.
 * Check IR inst for example.
 *
 * Author: Tianbo Hao<tianboh@alumni.cmu.edu>
 *)
module type Op = sig
  type t

  val pp : t -> string
end

module type Sig = sig
  type i
  type t

  val of_bisd : i -> i option -> i option -> i option -> t
  val pp : t -> string
end

module Wrapper (M : Op) : Sig with type i = M.t = struct
  type i = M.t

  type t =
    { (* Syntax sugar for x86 memory access. Return: base + index * scale + disp *)
      base : i
    ; index : i option (* used by array and struct *)
    ; scale : i option
    ; disp : i option (* used by array *)
    }

  let of_bisd base index scale disp = { base; index; scale; disp }

  let pp (addr : t) : string =
    let base = M.pp addr.base in
    let helper data =
      match data with
      | Some s -> M.pp s
      | None -> ""
    in
    let index = helper addr.index in
    let scale = helper addr.scale in
    Printf.sprintf "(%s, %s, %s)" base index scale
  ;;
end
