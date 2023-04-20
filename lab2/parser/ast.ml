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
  (* This is used for special case in elaboration from CST simp case. 
   * Also expression as statement is legal according to 
   * https://c0.cs.cmu.edu/docs/c0-reference.pdf Section 6.2,
   * Such a statement evaluates e, incurring all of its effects, 
   * and then discards the return value if there is any *)
  | Sexp of mexp

and mstm = stm Mark.t

type program = mstm

module Print = struct
  let pp_dtype = function
    | Int -> "int"
    | Bool -> "bool"
  ;;

  let pp_binop = function
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Divided_by -> "/"
    | Modulo -> "%"
    | And -> "&"
    | Or -> "|"
    | Hat -> "^"
    | Right_shift -> ">>"
    | Left_shift -> "<<"
    (* IB *)
    | Equal_eq -> "=="
    | Greater -> ">"
    | Greater_eq -> ">="
    | Less -> "<"
    | Less_eq -> "<="
    | Not_eq -> "!="
  ;;

  let rec pp_exp = function
    | Var id -> Symbol.name id
    | Const_int c -> Int32.to_string c
    | True -> "1"
    | False -> "0"
    | Binop binop ->
      sprintf "(%s %s %s)" (pp_mexp binop.lhs) (pp_binop binop.op) (pp_mexp binop.rhs)
    | Terop terop ->
      sprintf
        "(%s ? %s : %s)"
        (pp_mexp terop.cond)
        (pp_mexp terop.true_exp)
        (pp_mexp terop.false_exp)

  and pp_mexp e = pp_exp (Mark.data e)

  let rec pp_stm = function
    | Assign asn_ast ->
      sprintf "%s = %s;" (Symbol.name asn_ast.name) (pp_mexp asn_ast.value)
    | If if_ast ->
      sprintf
        "if(%s){ %s } else { %s }"
        (pp_mexp if_ast.cond)
        (pp_mstm if_ast.true_stm)
        (pp_mstm if_ast.false_stm)
    | While while_ast ->
      sprintf "while(%s){%s}" (pp_mexp while_ast.cond) (pp_mstm while_ast.body)
    | Return ret -> sprintf "return %s" (pp_mexp ret)
    | Nop -> ""
    | Seq seq_ast -> sprintf "%s %s" (pp_mstm seq_ast.head) (pp_mstm seq_ast.tail)
    | Declare decl_ast ->
      sprintf
        "%s %s; %s"
        (pp_dtype decl_ast.t)
        (Symbol.name decl_ast.name)
        (pp_mstm decl_ast.tail)
    | Sexp sexp -> pp_mexp sexp

  and pp_mstm stm = pp_stm (Mark.data stm) ^ "\n"
  (* and pp_stms stms = String.concat (List.map ~f:(fun stm -> pp_mstm stm ^ "\n") stms) *)

  let pp_program stms = "{\n" ^ pp_mstm stms ^ "}"
end
