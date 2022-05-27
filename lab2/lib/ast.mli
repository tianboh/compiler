(* L1 Compiler
 * Abstract Syntax Trees
 * Author: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Forward compatible fragment of C0
 *)

(* Operator *)
type binop =
  | Plus
  | Minus
  | Times
  | Divided_by
  | Modulo

type unop = Negative

(* Expression *)
type exp =
  | Var of Symbol.t
  | Const of Int32.t
  | Binop of
      { op : binop
      ; lhs : mexp
      ; rhs : mexp
      }
  | Unop of
      { op : unop
      ; operand : mexp
      }

(* Expression plus src file location *)
and mexp = exp Mark.t

(* Declaration *)
type decl =
  (* int x; *)
  | New_var of Symbol.t
  (* int x = e; *)
  | Init of Symbol.t * mexp

(* Statement *)
type stm =
  | Declare of decl
  | Assign of Symbol.t * mexp
  | Return of mexp

(* Statement plus src file location *)
and mstm = stm Mark.t

type program = mstm list

(* Print as source, with redundant parentheses *)
module Print : sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_program : program -> string
end
