(* (* L2 Compiler
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
  | Assign of {name : Symbol.t ; value : mexp}
  | If of {cond : mexp; true_stm : mstm; false_stm : mstm}
  | While of {cond : mexp; body : mstm}
  | Return of mexp
  | Nop
  | Seq of {head_stm : mstm; tail_stm : mstm}
  | Declare of {t : dtype; name : Symbol.t; tail_stm : mstm}

(* Statement plus src file location *)
and mstm = stm Mark.t

type program = mstm list

(* Print as source, with redundant parentheses *)
module Print : sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_program : program -> string
end *)
