(* L1 Compiler
 * IR Trees
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)
module Temp = Var.Temp
module Label = Util.Label

type binop =
  | Plus
  | Minus
  | Times
  | Divided_by
  | Modulo
  | And
  | Or
  | Xor
  | Right_shift
  | Left_shift
  | Equal_eq
  | Greater
  | Greater_eq
  | Less
  | Less_eq
  | Not_eq

type exp =
  | Const of Int32.t
  | Temp of Temp.t
  | Binop of
      { lhs : exp
      ; op : binop
      ; rhs : exp
      }
  (* Sexp is designed as a counterpart for AST terop.
   * It will execute stm for side effect, like CJump, 
   * and then return exp. *)
  | Sexp of
      { stm : stm
      ; exp : exp
      }

and stm =
  | Move of
      { dest : Temp.t
      ; src : exp
      }
  | Return of exp
  | Jump of Label.t
  | CJump of
      { (* Jump if lhs op rhs is true*)
        lhs : exp
      ; op : binop
      ; rhs : exp
      ; target_stm : Label.t
      }
  | Label of Label.t
  | Seq of
      { head : stm
      ; tail : stm
      }
  | Nop
  | NExp of
      (* NExp only execute expression for potential side effect
       * But it will drop the result after execution. *)
      exp

type program = stm

val is_relop : binop -> bool

module Print : sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_program : program -> string
end
