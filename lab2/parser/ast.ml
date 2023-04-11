(* L2 Compiler
 * Abstract Syntax Trees
 *
 * AUthor: Tianbo Hao
 *
 * Created: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 *
 * Forward compatible fragment of C0
 *)

open Core

(* module Mark = Util.Mark *)
module Symbol = Util.Symbol

type binop =
  (* II *)
  | Plus
  | Minus
  | Times
  | Divided_by
  | Modulo
  | And
  | Or
  | Hat
  | Right_shift
  | Left_shift
  (* IB *)
  | Equal_eq
  | Greater
  | Greater_eq
  | Less
  | Less_eq
  | Not_eq

type exp =
  | Var of Symbol.t
  | Const_int of Int32.t
  | True
  | False
  | Binop of
      { op : binop
      ; lhs : exp
      ; rhs : exp
      }
  | Terop of
      { cond : exp
      ; true_exp : exp
      ; false_exp : exp
      }

type dtype =
  | Int
  | Bool

type stm =
  | Assign of
      { name : Symbol.t
      ; value : exp
      }
  | If of
      { cond : exp
      ; true_stm : stm
      ; false_stm : stm
      }
  | While of
      { cond : exp
      ; body : stm
      }
  | Return of exp
  | Nop
  | Seq of
      { head : stm
      ; tail : stm
      }
  | Declare of
      { t : dtype
      ; name : Symbol.t
      ; tail : stm
      }
  | Sexp of exp
(* This is used for special case in elaboration from CST simp case. *)

type program = stm
