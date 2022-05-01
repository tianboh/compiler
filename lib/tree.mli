(* L1 Compiler
 * IR Trees
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod

type exp =
  | Const of Int32.t
  | Temp of Temp.t
  | Binop of
      { lhs : exp
      ; op : binop
      ; rhs : exp
      }

and stm =
  | Move of
      { dest : Temp.t
      ; src : exp
      }
  | Return of exp

type program = stm list

module Print : sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_program : program -> string
end
