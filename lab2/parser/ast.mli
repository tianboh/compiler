(* L2 Compiler
 * Abstract Syntax Trees
 *
 * Author: Tianbo Hao
 *
 * Created: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Forward compatible fragment of C0
 *)
(* module Mark = Util.Mark *)
module Symbol = Util.Symbol

(* Operator *)
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

(* Expression *)
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

(* Expression plus src file location *)
(* and mexp = exp Mark.t *)

type dtype =
  | Int
  | Bool

(* Declaration *)
(* type decl =
   (* int/bool x; *)
   | New_var of { t : dtype; name : Symbol.t }
   (* int/bool x = e; *)
   | Init of { t : dtype; name : Symbol.t; value : mexp} *)

(* Statement
   * 1) Asign(x,e)
   * 2) if(e,s,s)
   * 3) while(e,s)
   * 4) return(e)
   * 5) nop
   * 6) seq(s,s)
   * 7) declare(x,t,s) *)
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

(* Print as source, with redundant parentheses *)
(* module Print : sig
     val pp_exp : exp -> string
     val pp_stm : stm -> string
     val pp_program : program -> string
   end *)
