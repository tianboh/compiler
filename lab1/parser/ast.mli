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
module Mark = Util.Mark
module Symbol = Util.Symbol

(* Operator *)
type binop =
  | Plus
  | Minus
  | Times
  | Divided_by
  | Modulo
  | Logic_and
  | Logic_or
  | Bit_and
  | Bit_or
  | Bit_xor

type unop = Negative

(* Expression *)
type exp =
  | Var of Symbol.t
  | Const_int of Int32.t
  | Const_bool of Bool.t
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

type dtype = 
| Int
| Bool

(* Declaration *)
type decl =
  (* int/bool x; *)
  | New_var of { t : dtype; name : Symbol.t }
  (* int/bool x = e; *)
  | Init of { t : dtype; name : Symbol.t; value : mexp}

(* Statement *)
type stm =
  | Declare of decl
  | Assign of {name : Symbol.t ; value : mexp}
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
