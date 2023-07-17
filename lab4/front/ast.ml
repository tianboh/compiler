(* L4 Compiler
 * Abstract Syntax Trees for L4
 *  - gdecl as a higher level for statement.
 *  - struct, pointer, array. 
 *  - new syntax for lvalue
 *
 * Created: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
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

type binop =
  (* II *)
  [ `Plus
  | `Minus
  | `Times
  | `Divided_by
  | `Modulo
  | `And
  | `Or
  | `Hat
  | `Right_shift
  | `Left_shift
  | (* IB *)
    `Equal_eq
  | `Greater
  | `Greater_eq
  | `Less
  | `Less_eq
  | `Not_eq
  ]

type asnop =
  [ `Asn
  | `Plus_asn
  | `Minus_asn
  | `Times_asn
  | `Div_asn
  | `Mod_asn
  | `And_asn
  | `Hat_asn
  | `Or_asn
  | `Left_shift_asn
  | `Right_shift_asn
  ]

type dtype =
  [ `Int
  | `Bool
  | `Void
  | `NULL
  | `Pointer of dtype
  | `Array of dtype
  | `Struct of Symbol.t
  ]

type lvalue =
  | Ident of Symbol.t
  | LVDot of
      { struct_obj : mlvalue
      ; field : Symbol.t
      }
  | LVDeref of { ptr : mlvalue }
  | LVNth of
      { arr : mlvalue
      ; index : mexp
      }

and mlvalue = lvalue Mark.t

and exp =
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
  | Fcall of
      { func_name : Symbol.t
      ; args : mexp list
      }
  | EDot of
      { struct_obj : mexp
      ; field : Symbol.t
      }
  | EDeref of { ptr : mexp }
  | ENth of
      { arr : mexp
      ; index : mexp
      }
  | NULL
  | Alloc of { t : dtype }
  | Alloc_arr of
      { t : dtype
      ; e : mexp
      }

and mexp = exp Mark.t

type stm =
  | Assign of
      { name : mlvalue
      ; value : mexp
      ; op : asnop
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
  | Return of mexp option
  | Nop
  | Seq of
      { head : mstm
      ; tail : mstm
      }
  | Declare of
      { t : dtype
      ; name : Symbol.t
      ; value : mexp option
      ; tail : mstm
      }
  (* This is used for special case in elaboration from CST simp case. 
   * Also expression as statement is legal according to 
   * https://c0.cs.cmu.edu/docs/c0-reference.pdf Section 6.2,
   * Such a statement evaluates e, incurring all of its effects, 
   * and then discards the return value if there is any *)
  | Sexp of mexp
  | Assert of mexp

and mstm = stm Mark.t

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
      ; scope : [ `External | `C0 ]
      }
  | Fdefn of
      { ret_type : dtype
      ; func_name : Symbol.t
      ; pars : param list
      ; blk : mstm
      ; scope : [ `External | `C0 ]
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
    | `Int -> "int"
    | `Bool -> "bool"
    | `Void -> "void"
    | `Pointer ptr -> "*" ^ pp_dtype ptr
    | `Array arr -> pp_dtype arr ^ "[]"
    | `NULL -> "NULL"
    | `Struct s -> "struct " ^ Symbol.name s
  ;;

  let pp_binop = function
    | `Plus -> "+"
    | `Minus -> "-"
    | `Times -> "*"
    | `Divided_by -> "/"
    | `Modulo -> "%"
    | `And -> "&"
    | `Or -> "|"
    | `Hat -> "^"
    | `Right_shift -> ">>"
    | `Left_shift -> "<<"
    (* IB *)
    | `Equal_eq -> "=="
    | `Greater -> ">"
    | `Greater_eq -> ">="
    | `Less -> "<"
    | `Less_eq -> "<="
    | `Not_eq -> "!="
  ;;

  let rec pp_exp = function
    | Var id -> Symbol.name id
    | Const_int c -> Int32.to_string c
    | True -> "true"
    | False -> "false"
    | Binop binop ->
      sprintf "(%s %s %s)" (pp_mexp binop.lhs) (pp_binop binop.op) (pp_mexp binop.rhs)
    | Terop terop ->
      sprintf
        "(%s ? %s : %s)"
        (pp_mexp terop.cond)
        (pp_mexp terop.true_exp)
        (pp_mexp terop.false_exp)
    | Fcall fcall ->
      sprintf
        "%s(%s)"
        (Symbol.name fcall.func_name)
        (List.map fcall.args ~f:(fun arg -> pp_mexp arg) |> String.concat ~sep:",")
    | EDot edot -> sprintf "%s.%s" (pp_mexp edot.struct_obj) (Symbol.name edot.field)
    | EDeref ederef -> sprintf "*%s" (pp_mexp ederef.ptr)
    | ENth enth -> sprintf "%s[%s]" (pp_mexp enth.arr) (pp_mexp enth.index)
    | NULL -> "NULL"
    | Alloc alloc -> sprintf "alloc(%s)" (pp_dtype alloc.t)
    | Alloc_arr alloc_arr ->
      sprintf "alloc_array(%s, %s)" (pp_dtype alloc_arr.t) (pp_mexp alloc_arr.e)

  and pp_mexp e = pp_exp (Mark.data e)

  let rec pp_lvalue = function
    | Ident ident -> Symbol.name ident
    | LVDot dot -> sprintf "%s.%s" (pp_mlvalue dot.struct_obj) (Symbol.name dot.field)
    | LVDeref deref -> sprintf "*%s" (pp_mlvalue deref.ptr)
    | LVNth nth -> sprintf "%s[%s]" (pp_mlvalue nth.arr) (pp_mexp nth.index)

  and pp_mlvalue mlv = pp_lvalue (Mark.data mlv)

  let rec pp_stm = function
    | Assign asn_ast ->
      sprintf "Assign (%s = %s;)" (pp_mlvalue asn_ast.name) (pp_mexp asn_ast.value)
    | If if_ast ->
      sprintf
        "if(%s){ %s } else { %s }"
        (pp_mexp if_ast.cond)
        (pp_mstm if_ast.true_stm)
        (pp_mstm if_ast.false_stm)
    | While while_ast ->
      sprintf "while(%s){%s}" (pp_mexp while_ast.cond) (pp_mstm while_ast.body)
    | Return ret ->
      (match ret with
      | Some ret -> sprintf "return %s" (pp_mexp ret)
      | None -> sprintf "return")
    | Nop -> ""
    | Seq seq_ast -> sprintf "%s %s" (pp_mstm seq_ast.head) (pp_mstm seq_ast.tail)
    | Declare decl_ast ->
      sprintf
        "decl{%s %s; %s}"
        (pp_dtype decl_ast.t)
        (Symbol.name decl_ast.name)
        (pp_mstm decl_ast.tail)
    | Sexp sexp -> "Sexp " ^ pp_mexp sexp ^ ";"
    | Assert e -> sprintf "assert(%s)" (pp_mexp e)

  and pp_mstm stm = pp_stm (Mark.data stm) ^ "\n"

  (* and pp_stms stms = String.concat (List.map ~f:(fun stm -> pp_mstm stm ^ "\n") stms) *)
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
        (pp_mstm fdefn.blk)
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
