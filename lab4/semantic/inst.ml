(* Typed Syntax Trees for L4
 *
 * This syntax tree has almost the same structure
 * as AST, but each expression is annotated with a type
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *
 * Forward compatible fragment of C0
 *)

open Core
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

type asnop =
  | Asn
  | Plus_asn
  | Minus_asn
  | Times_asn
  | Div_asn
  | Mod_asn
  | And_asn
  | Hat_asn
  | Or_asn
  | Left_shift_asn
  | Right_shift_asn

type dtype =
  | Int
  | Bool
  | Void
  | NULL
  | Pointer of dtype
  | Array of dtype
  | Struct of Symbol.t

type 'a typed =
  { dtype : dtype
  ; data : 'a
  }

type lvalue =
  | Ident of Symbol.t
  | LVDot of
      { struct_obj : tlvalue
      ; field : Symbol.t
      }
  | LVDeref of { ptr : tlvalue }
  | LVNth of
      { arr : tlvalue
      ; index : texp
      }

and tlvalue = lvalue typed

and exp =
  | Var of Symbol.t
  | Const_int of Int32.t
  | True
  | False
  | Binop of
      { op : binop
      ; lhs : texp
      ; rhs : texp
      }
  | Terop of
      { cond : texp
      ; true_exp : texp
      ; false_exp : texp
      }
  | Fcall of
      { func_name : Symbol.t
      ; args : texp list
      }
  | EDot of
      { struct_obj : texp
      ; field : Symbol.t
      }
  | EDeref of { ptr : texp }
  | ENth of
      { arr : texp
      ; index : texp
      }
  | NULL
  | Alloc of { t : dtype }
  | Alloc_arr of
      { t : dtype
      ; e : texp
      }

and texp = exp typed

type stm =
  | Assign of
      { name : tlvalue
      ; value : texp
      ; op : asnop
      }
  | If of
      { cond : texp
      ; true_stm : stm
      ; false_stm : stm
      }
  | While of
      { cond : texp
      ; body : stm
      }
  | Return of texp option
  | Nop
  | Seq of
      { head : stm
      ; tail : stm
      }
  | Declare of
      { t : dtype
      ; name : Symbol.t
      ; value : texp option
      ; tail : stm
      }
  | Sexp of texp
  | Assert of texp

type param =
  { t : dtype
  ; i : Symbol.t
  }

type field =
  { t : dtype
  ; i : Symbol.t
  }

type gdecl =
  | Fdecl of
      { ret_type : dtype
      ; func_name : Symbol.t
      ; pars : param list
      }
  | Fdefn of
      { ret_type : dtype
      ; func_name : Symbol.t
      ; pars : param list
      ; blk : stm
      }
  | Typedef of
      { t : dtype
      ; t_var : Symbol.t
      }
  | Sdecl of { struct_name : Symbol.t }
  | Sdefn of
      { struct_name : Symbol.t
      ; fields : field list
      }

type program = gdecl list

module Print = struct
  let rec pp_dtype = function
    | Int -> "int"
    | Bool -> "bool"
    | Void -> "void"
    | Pointer ptr -> "*" ^ pp_dtype ptr
    | Array arr -> pp_dtype arr ^ "[]"
    | NULL -> "NULL"
    | Struct s -> "struct " ^ Symbol.name s
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
    | True -> "true"
    | False -> "false"
    | Binop binop ->
      sprintf "(%s %s %s)" (pp_texp binop.lhs) (pp_binop binop.op) (pp_texp binop.rhs)
    | Terop terop ->
      sprintf
        "(%s ? %s : %s)"
        (pp_texp terop.cond)
        (pp_texp terop.true_exp)
        (pp_texp terop.false_exp)
    | Fcall fcall ->
      sprintf
        "%s(%s)"
        (Symbol.name fcall.func_name)
        (List.map fcall.args ~f:(fun arg -> pp_texp arg) |> String.concat ~sep:",")
    | EDot edot -> sprintf "%s.%s" (pp_texp edot.struct_obj) (Symbol.name edot.field)
    | EDeref ederef -> sprintf "*%s" (pp_texp ederef.ptr)
    | ENth enth -> sprintf "%s[%s]" (pp_texp enth.arr) (pp_texp enth.index)
    | NULL -> "NULL"
    | Alloc alloc -> sprintf "alloc(%s)" (pp_dtype alloc.t)
    | Alloc_arr alloc_arr ->
      sprintf "alloc_array(%s, %s)" (pp_dtype alloc_arr.t) (pp_texp alloc_arr.e)

  and pp_texp e = pp_exp e.data

  let rec pp_lvalue = function
    | Ident ident -> Symbol.name ident
    | LVDot dot -> sprintf "%s.%s" (pp_tlvalue dot.struct_obj) (Symbol.name dot.field)
    | LVDeref deref -> sprintf "*%s" (pp_tlvalue deref.ptr)
    | LVNth nth -> sprintf "%s[%s]" (pp_tlvalue nth.arr) (pp_texp nth.index)

  and pp_tlvalue tlv = pp_lvalue tlv.data

  let rec pp_stm = function
    | Assign asn_ast ->
      sprintf "Assign (%s = %s;)" (pp_tlvalue asn_ast.name) (pp_texp asn_ast.value)
    | If if_ast ->
      sprintf
        "if(%s){ %s } else { %s }"
        (pp_texp if_ast.cond)
        (pp_stm if_ast.true_stm)
        (pp_stm if_ast.false_stm)
    | While while_ast ->
      sprintf "while(%s){%s}" (pp_texp while_ast.cond) (pp_stm while_ast.body)
    | Return ret ->
      (match ret with
      | Some ret -> sprintf "return %s" (pp_texp ret)
      | None -> sprintf "return")
    | Nop -> ""
    | Seq seq_ast -> sprintf "%s %s" (pp_stm seq_ast.head) (pp_stm seq_ast.tail)
    | Declare decl_ast ->
      sprintf
        "decl{%s %s; %s}"
        (pp_dtype decl_ast.t)
        (Symbol.name decl_ast.name)
        (pp_stm decl_ast.tail)
    | Sexp sexp -> "Sexp " ^ pp_texp sexp ^ ";"
    | Assert e -> sprintf "assert(%s)" (pp_texp e)
  ;;

  let pp_param (param : param) = sprintf "%s %s" (pp_dtype param.t) (Symbol.name param.i)
  let pp_field (field : field) = sprintf "%s %s" (pp_dtype field.t) (Symbol.name field.i)

  let pp_gdecl = function
    | Fdecl fdecl ->
      sprintf
        "%s %s(%s);"
        (pp_dtype fdecl.ret_type)
        (Symbol.name fdecl.func_name)
        (List.map fdecl.pars ~f:pp_param |> String.concat ~sep:",")
    | Fdefn fdefn ->
      sprintf
        "%s %s(%s)%s"
        (pp_dtype fdefn.ret_type)
        (Symbol.name fdefn.func_name)
        (List.map fdefn.pars ~f:pp_param |> String.concat ~sep:",")
        (pp_stm fdefn.blk)
    | Typedef typedef ->
      sprintf "typedef %s %s" (pp_dtype typedef.t) (Symbol.name typedef.t_var)
    | Sdefn sdefn ->
      sprintf
        "struct %s{%s}"
        (Symbol.name sdefn.struct_name)
        (List.map sdefn.fields ~f:pp_field |> String.concat ~sep:"; ")
    | Sdecl sdecl -> sprintf "struct %s;" (Symbol.name sdecl.struct_name)
  ;;

  let pp_program program = List.map program ~f:pp_gdecl |> String.concat ~sep:"\n\n"
end
