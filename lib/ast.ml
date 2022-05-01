(* L1 Compiler
 * Abstract Syntax Trees
 * Author: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 *
 * Forward compatible fragment of C0
 *)

open Core

type binop =
  | Plus
  | Minus
  | Times
  | Divided_by
  | Modulo

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

and mexp = exp Mark.t

type decl =
  | New_var of Symbol.t
  | Init of Symbol.t * mexp

type stm =
  | Declare of decl
  | Assign of Symbol.t * mexp
  | Return of mexp

and mstm = stm Mark.t

type program = mstm list

module Print = struct
  let pp_binop = function
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Divided_by -> "/"
    | Modulo -> "%"
  ;;

  let pp_unop = function
    | Negative -> "-"
  ;;

  let rec pp_exp = function
    | Var id -> Symbol.name id
    | Const c -> Int32.to_string c
    | Unop unop -> sprintf "%s(%s)" (pp_unop unop.op) (pp_mexp unop.operand)
    | Binop binop ->
      sprintf "(%s %s %s)" (pp_mexp binop.lhs) (pp_binop binop.op) (pp_mexp binop.rhs)

  and pp_mexp e = pp_exp (Mark.data e)

  let pp_decl = function
    | New_var id -> sprintf "int %s;" (Symbol.name id)
    | Init (id, e) -> sprintf "int %s = %s;" (Symbol.name id) (pp_mexp e)
  ;;

  let rec pp_stm = function
    | Declare d -> pp_decl d
    | Assign (id, e) -> sprintf "%s = %s;" (Symbol.name id) (pp_mexp e)
    | Return e -> sprintf "return %s;" (pp_mexp e)

  and pp_mstm stm = pp_stm (Mark.data stm)
  and pp_stms stms = String.concat (List.map ~f:(fun stm -> pp_mstm stm ^ "\n") stms)

  let pp_program stms = "{\n" ^ pp_stms stms ^ "}"
end
