(* L2 Compiler
 * Concrete Syntax Trees
 *
 * Concrete Syntax Tree(CST) is transformed from parser directly.
 * So almost every grammer rule corresponds to a CST type here
 * We have below CST type based on Grammer L2, which is shown in lab2 handout
 * program
 * type
 * decl
 * stmts
 * stmt
 * simp
 * lvalue
 * control
 * exp
 * asop
 * binop
 * unop
 * postop
 * 
 * We omit below due to
 * block: this will lead to recursive reference between cst type and mly type
 * simpopt: we can handle empty in mly, so don't bother it CST
 * elseopt: same as above
 * intconst: handled in mly
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
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
 
 type unop = Negative

 (* Notice that the subexpressions of an expression are marked.
  * (That is, the subexpressions are of type exp Mark.t, not just
  * type exp.) This means that source code location (a src_span) is
  * associated with the subexpression. Currently, the typechecker uses
  * this source location to print more helpful error messages.
  *
  * It's the parser and lexer's job to associate src_span locations with each
  * ast. It's instructive, but not necessary, to closely read the source code
  * for c0_parser.mly, c0_lexer.mll, and parse.ml to get a good idea of how
  * src_spans are created.
  *
  * Check out the Mark module for ways of converting a marked expression into
  * the original expression or to the src_span location. You could also just
  * look at how the typechecker gets the src_span from an expression when it
  * prints error messages.
  *
  * It's completely possible to remove Marks entirely from your compiler, but
  * it will be harder to figure out typechecking errors for later labs.
  *)
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
 
 and mexp = exp Mark.t
 
 type dtype = 
 | Int
 | Bool
 
 type decl =
   | New_var of { t : dtype; name : Symbol.t }
   | Init of { t : dtype; name : Symbol.t; value : mexp}
 

(* Statement
 type stm =
   | Declare of decl
   | Assign of {name : Symbol.t ; value : mexp}
   | Return of mexp
 
 (* Statement plus src file location *)
 and mstm = stm Mark.t
 
 type program = mstm list
*)

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

 and stms = 
    | []
    | Concat of {head : mstm; tail : stms}
 
 and block = stms

 type program = block
 
 module Print = struct
   let pp_binop = function
     | Plus -> "+"
     | Minus -> "-"
     | Times -> "*"
     | Divided_by -> "/"
     | Modulo -> "%"
     | And_and -> "&&"
     | Or_or -> "||"
     | And -> "&"
     | Or -> "|"
     | Hat -> "^"
   ;;
 
   let pp_unop = function
     | Negative -> "-"
   ;;
 
   let rec pp_exp = function
     | Var id -> Symbol.name id
     | Const_int c -> Int32.to_string c
     | True -> "True"
     | False -> "False"
     | Unop unop -> sprintf "%s(%s)" (pp_unop unop.op) (pp_mexp unop.operand)
     | Binop binop ->
       sprintf "(%s %s %s)" (pp_mexp binop.lhs) (pp_binop binop.op) (pp_mexp binop.rhs)
     | Ter ter_exp -> 
       sprintf "%s ? %s : %s" (pp_mexp ter_exp.cond) (pp_mexp ter_exp.true_exp) (pp_mexp ter_exp.false_exp)
 
   and pp_mexp e = pp_exp (Mark.data e)
 
   let pp_dtype = function
   | Int -> "int"
   | Bool -> "bool"
 
   let pp_decl = function
     | New_var id -> sprintf "%s %s;" (pp_dtype id.t) (Symbol.name id.name)
     | Init id -> sprintf "%s %s = %s;" (pp_dtype id.t) (Symbol.name id.name) (pp_mexp id.value)
   ;;

  let pp_simp = function
    | Assign id -> sprintf "%s = %s;" (Symbol.name id.name) (pp_mexp id.value)
    | Declare d -> pp_decl d
    | Exp e -> pp_mexp e

  let rec pp_stm = function
    | Simp s -> pp_simp s
    | Control c -> pp_ctl c
    | Block b -> pp_blk b

  and pp_ctl = function
  | If if_stm -> 
    let else_stm = (match if_stm.s_f with | Some s -> sprintf "%s" (pp_stm s) | None -> "" ) in
    sprintf "if(%s){%s}else{%s}" (pp_mexp if_stm.cond) (pp_stm if_stm.s_t) else_stm
  | While while_stm -> 
    sprintf "while(%s){%s}" (pp_mexp while_stm.cond) (pp_stm while_stm.body)
  | For for_stm -> 
    let init, iter = (
      match for_stm.init, for_stm.iter with 
      | None, None -> "", ""
      | Some init, None -> pp_simp init, ""
      | None, Some iter -> "", pp_simp iter
      | Some init, Some iter -> pp_simp init, pp_simp iter
      ) in
    sprintf "for(%s; %s; %s){%s}" init (pp_mexp for_stm.cond) iter (pp_stm for_stm.body)
  | Return e -> sprintf "return %s;" (pp_mexp e)

  and pp_blk = function
  | [] -> ""
  | Concat concat -> 
    sprintf "%s" (pp_mstm concat.head) ^ pp_blk concat.tail
 
   and pp_mstm stm = pp_stm (Mark.data stm)
   (* and pp_stms stms = String.concat (List.map ~f:(fun stm -> pp_mstm stm ^ "\n") stms) *)

   and pp_block stms = "{\n" ^ pp_blk stms ^ "}"
   let pp_program block = pp_block block
 end
 