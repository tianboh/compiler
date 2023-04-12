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
module Mark = Util.Mark
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
      ; lhs : mexp
      ; rhs : mexp
      }
  | Terop of
      { cond : mexp
      ; true_exp : mexp
      ; false_exp : mexp
      }

and mexp = exp Mark.t

type dtype =
  | Int
  | Bool

type stm =
  | Assign of
      { name : Symbol.t
      ; value : mexp
      }
  | If of
      { cond : mexp
      ; true_stm : mstm
      ; false_stm : mstm
      }
  | While of
      { cond : mexp
      ; body : mstm
      }
  | Return of mexp
  | Nop
  | Seq of
      { head : mstm
      ; tail : mstm
      }
  | Declare of
      { t : dtype
      ; name : Symbol.t
      ; tail : mstm
      }
  (* This is used for special case in elaboration from CST simp case. *)
  | Sexp of mexp

and mstm = stm Mark.t

type program = mstm
