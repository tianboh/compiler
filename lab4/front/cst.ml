(* L3 Compiler
 * Concrete Syntax Trees
 *
 * We provide new features for L3 grammar based on L2
 * 1) function declaration and function defination.
 * 2) type alias system. including new type for "ident", 
 * which is used by type alias, and "void", which is a 
 * choice for function return type.
 *
 * Author: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu>
 *
 * Forward compatible fragment of C0
 *)

open Core
module Mark = Util.Mark
module Symbol = Util.Symbol

(* 
 * We distinguish binary op based on its inputs and output
 * 1) II: input is integer and output is integer
 * 2) IB: input is integer and output is bool, like >, ==, etc.
 * 3) BB: input is bool and output is bool, like && ||
 *)
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
  (* BB *)
  | And_and
  | Or_or
  (* IB *)
  | Equal_eq
  | Greater
  | Greater_eq
  | Less
  | Less_eq
  | Not_eq

(* They are not used in CST because they are parsed to binop in mly *)
type unop =
  | Negative
  | Excalmation_mark
  (* "!" logical not *)
  | Dash_mark
(* "~" bitwise not *)

(* They are not used as well, reason as unop. *)
type postop =
  | Plus_plus
  | Minus_minus

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
  | Terop of
      { cond : mexp
      ; true_exp : mexp
      ; false_exp : mexp
      }
  | Fcall of
      { func_name : Symbol.t
      ; args : mexp list
      }

and mexp = exp Mark.t

type dtype =
  | Int
  | Bool
  | Ctype of Symbol.t (* for custom type alias *)
  | Void

type decl =
  | New_var of
      { t : dtype
      ; name : Symbol.t
      }
  | Init of
      { t : dtype
      ; name : Symbol.t
      ; value : mexp
      }

type stm =
  | Simp of simp
  | Control of control
  | Block of block

and simp =
  | Assign of
      { name : Symbol.t
      ; value : mexp
      }
  | Declare of decl
  | Sexp of mexp

and msimp = simp Mark.t

and control =
  | If of
      { cond : mexp
      ; true_stm : mstm
      ; false_stm : mstm option
      }
  | While of
      { cond : mexp
      ; body : mstm
      }
  | For of
      { init : msimp option
      ; cond : mexp
      ; iter : msimp option
      ; body : mstm
      }
  | Return of mexp option
  | Assert of mexp

and mstm = stm Mark.t

and mstms = mstm list

and block = mstms

and param =
  { t : dtype
  ; i : Symbol.t
  }

and gdecl =
  | Fdecl of
      { ret_type : dtype
      ; func_name : Symbol.t
      ; par_type : param list
      }
  | Fdefn of
      { ret_type : dtype
      ; func_name : Symbol.t
      ; par_type : param list
      ; blk : block
      }
  | Typedef of
      { t : dtype
      ; t_var : Symbol.t
      }

type program = gdecl list

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
    | Right_shift -> ">>"
    | Left_shift -> "<<"
    | Equal_eq -> "=="
    | Greater -> ">"
    | Greater_eq -> ">="
    | Less -> "<"
    | Less_eq -> "<="
    | Not_eq -> "!="
  ;;

  let pp_unop = function
    | Negative -> "-"
    | Excalmation_mark -> "!"
    | Dash_mark -> "~"
  ;;

  let rec pp_exp = function
    | Var id -> Symbol.name id
    | Const_int c -> Int32.to_string c
    | True -> "True"
    | False -> "False"
    | Unop unop -> sprintf "%s(%s)" (pp_unop unop.op) (pp_mexp unop.operand)
    | Binop binop ->
      sprintf "(%s %s %s)" (pp_mexp binop.lhs) (pp_binop binop.op) (pp_mexp binop.rhs)
    | Terop ter_exp ->
      sprintf
        "%s ? %s : %s"
        (pp_mexp ter_exp.cond)
        (pp_mexp ter_exp.true_exp)
        (pp_mexp ter_exp.false_exp)
    | Fcall fcall ->
      sprintf
        "%s(%s)"
        (Symbol.name fcall.func_name)
        (List.map fcall.args ~f:(fun arg -> pp_mexp arg) |> String.concat ~sep:",")

  and pp_mexp e = pp_exp (Mark.data e)

  let pp_dtype = function
    | Int -> "int"
    | Bool -> "bool"
    | Void -> "void"
    | Ctype ident -> Symbol.name ident
  ;;

  let pp_decl = function
    | New_var id -> sprintf "%s %s;" (pp_dtype id.t) (Symbol.name id.name)
    | Init id ->
      sprintf "%s %s = %s;" (pp_dtype id.t) (Symbol.name id.name) (pp_mexp id.value)
  ;;

  let pp_simp = function
    | Assign id -> sprintf "%s = %s;" (Symbol.name id.name) (pp_mexp id.value)
    | Declare d -> pp_decl d
    | Sexp e -> "Sexp " ^ pp_mexp e ^ ";"
  ;;

  let rec pp_stm = function
    | Simp s -> pp_simp s
    | Control c -> pp_ctl c
    | Block b -> pp_blk b

  and pp_ctl = function
    | If if_stm ->
      let else_stm =
        match if_stm.false_stm with
        | Some s -> sprintf "%s" (pp_mstm s)
        | None -> ""
      in
      sprintf
        "if(%s){%s}else{%s}"
        (pp_mexp if_stm.cond)
        (pp_mstm if_stm.true_stm)
        else_stm
    | While while_stm ->
      sprintf "while(%s){%s}" (pp_mexp while_stm.cond) (pp_mstm while_stm.body)
    | For for_stm ->
      let init, iter =
        match for_stm.init, for_stm.iter with
        | None, None -> "", ""
        | Some init, None -> pp_msimp init, ""
        | None, Some iter -> "", pp_msimp iter
        | Some init, Some iter -> pp_msimp init, pp_msimp iter
      in
      sprintf "for(%s %s; %s){%s}" init (pp_mexp for_stm.cond) iter (pp_mstm for_stm.body)
    | Return e ->
      (match e with
      | Some e -> sprintf "return %s;" (pp_mexp e)
      | None -> "return")
    | Assert e -> sprintf "assert(%s)" (pp_mexp e)

  and pp_blk = function
    | [] -> ""
    | h :: t -> sprintf "%s" (pp_mstm h) ^ pp_blk t

  and pp_param param = sprintf " %s %s" (pp_dtype param.t) (Symbol.name param.i)

  and pp_gdecl = function
    | Fdecl fdecl ->
      sprintf
        "%s %s(%s);"
        (pp_dtype fdecl.ret_type)
        (Symbol.name fdecl.func_name)
        (List.map fdecl.par_type ~f:pp_param |> String.concat ~sep:",")
    | Fdefn fdefn ->
      sprintf
        "%s %s(%s)%s"
        (pp_dtype fdefn.ret_type)
        (Symbol.name fdefn.func_name)
        (List.map fdefn.par_type ~f:pp_param |> String.concat ~sep:",")
        (pp_block fdefn.blk)
    | Typedef typedef ->
      sprintf "typedef %s %s" (pp_dtype typedef.t) (Symbol.name typedef.t_var)

  and pp_mstm stm = pp_stm (Mark.data stm)
  and pp_msimp msimp = pp_simp (Mark.data msimp)
  and pp_block stms = "{\n" ^ pp_blk stms ^ "}"

  let pp_program program = List.map program ~f:pp_gdecl |> String.concat ~sep:"\n\n"
end
