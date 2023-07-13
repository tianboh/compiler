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

type 'a typed =
  { dtype : dtype
  ; data : 'a
  }

type exp =
  [ `Var of Symbol.t
  | `Const_int of Int32.t
  | `True
  | `False
  | `Binop of binexp
  | `Terop of terexp
  | `Fcall of fcall
  | `Dot of dot
  | `Deref of deref
  | `Nth of nth
  | `NULL
  | `Alloc of alloc
  | `Alloc_arr of alloc_arr
  ]

and binexp =
  { op : binop
  ; lhs : texp
  ; rhs : texp
  }

and terexp =
  { cond : texp
  ; true_exp : texp
  ; false_exp : texp
  }

and fcall =
  { func_name : Symbol.t
  ; args : texp list
  }

and dot =
  { struct_obj : texp
  ; field : Symbol.t
  }

and deref = { ptr : texp }

and alloc = { dtype : dtype }

and alloc_arr =
  { etype : dtype
  ; nitems : texp
  }

and nth =
  { arr : texp
  ; index : texp
  }

and texp = exp typed

type stm =
  | Assign of
      { name : texp
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

type param = Symbol.t typed

type field =
  { t : dtype
  ; i : Symbol.t
  }

type fdefn =
  { ret_type : dtype
  ; func_name : Symbol.t
  ; pars : param list
  ; blk : stm
  }

type program = fdefn list

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

  let rec pp_exp : exp -> string = function
    | `Var id -> Symbol.name id
    | `Const_int c -> Int32.to_string c
    | `True -> "true"
    | `False -> "false"
    | `Binop binop ->
      sprintf "(%s %s %s)" (pp_texp binop.lhs) (pp_binop binop.op) (pp_texp binop.rhs)
    | `Terop terop ->
      sprintf
        "(%s ? %s : %s)"
        (pp_texp terop.cond)
        (pp_texp terop.true_exp)
        (pp_texp terop.false_exp)
    | `Fcall (fcall : fcall) ->
      sprintf
        "%s(%s)"
        (Symbol.name fcall.func_name)
        (List.map fcall.args ~f:(fun arg -> pp_texp arg) |> String.concat ~sep:",")
    | `Dot dot -> sprintf "%s.%s" (pp_texp dot.struct_obj) (Symbol.name dot.field)
    | `Deref deref -> sprintf "*%s" (pp_texp deref.ptr)
    | `Nth nth -> sprintf "%s[%s]" (pp_texp nth.arr) (pp_texp nth.index)
    | `NULL -> "NULL"
    | `Alloc alloc -> sprintf "alloc(%s)" (pp_dtype alloc.dtype)
    | `Alloc_arr (alloc_arr : alloc_arr) ->
      sprintf "alloc_array(%s, %s)" (pp_dtype alloc_arr.etype) (pp_texp alloc_arr.nitems)

  and pp_texp e = pp_exp e.data

  let rec pp_stm = function
    | Assign asn_ast ->
      sprintf "Assign (%s = %s;)" (pp_texp asn_ast.name) (pp_texp asn_ast.value)
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

  let pp_param (param : param) =
    sprintf "%s %s" (pp_dtype param.dtype) (Symbol.name param.data)
  ;;

  let pp_field (field : field) = sprintf "%s %s" (pp_dtype field.t) (Symbol.name field.i)

  let pp_fdefn fdefn =
    sprintf
      "%s %s(%s)%s"
      (pp_dtype fdefn.ret_type)
      (Symbol.name fdefn.func_name)
      (List.map fdefn.pars ~f:pp_param |> String.concat ~sep:",")
      (pp_stm fdefn.blk)
  ;;

  let pp_program program = List.map program ~f:pp_fdefn |> String.concat ~sep:"\n\n"
end
