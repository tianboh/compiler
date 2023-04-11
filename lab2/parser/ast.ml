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

type exp =
  | Var of Symbol.t
  | Const_int of Int32.t
  | Const_bool of Bool.t
  | Binop of
    { op : binop
    ; lhs : exp
    ; rhs : exp
    }
  | Unop of
    { op : unop
    ; operand : exp
    }

type dtype = 
  | Int
  | Bool

type stm =
  | Assign of {name : Symbol.t ; value : exp}
  | If of {cond : exp; true_stm : stm; false_stm : stm}
  | While of {cond : exp; body : stm}
  | Return of exp
  | Nop
  | Seq of {head_stm : stm; tail_stm : stm}
  | Declare of {t : dtype; name : Symbol.t; tail_stm : stm}

type program = stm
