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

  val of_bisd : i -> i option -> Int64.t option -> Int64.t option -> t
  val pp : t -> string
  val get_base : t -> i
  val get_index : t -> i option
  val get_scale : t -> Int64.t option
  val get_disp : t -> Int64.t option
  val get : t -> i * i option * Int64.t option * Int64.t option
end

module Wrapper (M : Op) : Sig with type i = M.t = struct
  type i = M.t

  (* 
   * Intel's Combined Volume Set of Intel® 64 and IA-32 Architectures Software Developer’s Manuals
   * 3.7.5 Specifying an Offset
   * 
   * The offset part of a memory address can be specified directly as a static value (called a displacement) 
   * or through an address computation made up of one or more of the following components:
   *
   * Displacement — An 8-, 16-, or 32-bit value.
   * Base — The value in a general-purpose register.
   * Index — The value in a general-purpose register. [can't be ESP/RSP]
   * Scale factor — A value of 2, 4, or 8 that is multiplied by the index value.
   *)
  type t =
    { (* Syntax sugar for x86 memory access. Return: base + index * scale + disp *)
      base : i
    ; index : i option (* used by array and struct *)
    ; scale : Int64.t option
    ; disp : Int64.t option (* used by array *)
    }

  let of_bisd base index scale disp = { base; index; scale; disp }

  let pp (addr : t) : string =
    let base = M.pp addr.base in
    let helper data print =
      match data with
      | Some s -> print s
      | None -> ""
    in
    let index = helper addr.index M.pp in
    let scale = helper addr.scale Int64.to_string in
    Printf.sprintf "(%s, %s, %s)" base index scale
  ;;

  let get_base addr = addr.base
  let get_index addr = addr.index
  let get_scale addr = addr.scale
  let get_disp addr = addr.disp
  let get addr = addr.base, addr.index, addr.scale, addr.disp
end
