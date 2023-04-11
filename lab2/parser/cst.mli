(* L2 Compiler
 * Concrete Syntax Trees
 * Author: Tianbo Hao, Alex Vaynberg
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
  | And_and
  | Or_or
  | And
  | Or
  | Hat
  | Right_shift
  | Left_shift
  
type unop = 
  | Negative
  | Excalmation_mark (* ! *)
  | Dash_mark (* ~ *)

type postop = 
  | Plus_plus
  | Minus_minus
 (* Expression *)
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
  | Unop of
    { op : unop
    ; operand : mexp
    }
  | Ter of 
    { cond : mexp;
      true_exp : mexp;
      false_exp : mexp;
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

type stm =
  | Simp of simp
  | Control of control
  | Block of block

and simp = 
  | Assign of {name : Symbol.t ; value : mexp}
  | Declare of decl
  | Exp of mexp

and control = 
  | If of {cond : mexp; s_t : stm; s_f : stm option}
  | While of {cond : mexp; body : stm}
  | For of {init : simp option; cond : mexp; iter : simp option; body : stm}
  | Return of mexp

and mstm = stm Mark.t

and stms = stm list

and mstms = mstm list

and block = mstms

type program = block

 (* Print as source, with redundant parentheses *)
 module Print : sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_ctl : control -> string
  val pp_simp : simp -> string
  val pp_program : program -> string
 end
 