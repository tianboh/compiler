(* L4 Compiler
 * Concrete Syntax Trees
 *
 * We provide new features for L4 grammar based on L3
 *  - struct
 *  - array
 *  - pointer
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

type unop =
  | Negative
  (* "!" logical not *)
  | Excalmation_mark
  (* "~" bitwise not *)
  | Dash_mark

type postop =
  | Plus_plus
  | Minus_minus

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
  | Dot of
      { struct_obj : mexp
      ; field : Symbol.t
      }
  | Arrow of
      { struct_ptr : mexp
      ; field : Symbol.t
      }
  | Deref of { ptr : mexp }
  | Nth of
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

and dtype =
  | Int
  | Bool
  | Ctype of Symbol.t (* for custom type alias *)
  | Void
  | Pointer of dtype
  | Array of dtype
  | Struct of Symbol.t

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
      { name : mexp
      ; value : mexp
      ; op : asnop
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

type param =
  { t : dtype
  ; i : Symbol.t
  }

type field =
  { t : dtype
  ; i : Symbol.t
  }

and gdecl =
  | Fdecl of
      { (* Internal indicate c0 function, external indicate c function *)
        ret_type : dtype
      ; func_name : Symbol.t
      ; par_type : param list
      ; scope : [ `Internal | `External ]
      }
  | Fdefn of
      { (* Internal indicate c0 function, external indicate c function *)
        ret_type : dtype
      ; func_name : Symbol.t
      ; par_type : param list
      ; blk : block
      ; scope : [ `Internal | `External ]
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

  let pp_asnop = function
    | Asn -> "="
    | Plus_asn -> "+="
    | Minus_asn -> "-="
    | Times_asn -> "*="
    | Div_asn -> "/="
    | Mod_asn -> "%="
    | And_asn -> "&="
    | Hat_asn -> "^="
    | Or_asn -> "|="
    | Left_shift_asn -> "<<="
    | Right_shift_asn -> ">>="
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
    | Dot dot -> sprintf "%s.%s" (pp_mexp dot.struct_obj) (Symbol.name dot.field)
    | Arrow arrow -> sprintf "%s->%s" (pp_mexp arrow.struct_ptr) (Symbol.name arrow.field)
    | Deref deref -> sprintf "*%s" (pp_mexp deref.ptr)
    | Nth nth -> sprintf "%s[%s]" (pp_mexp nth.arr) (pp_mexp nth.index)
    | NULL -> "NULL"
    | Alloc alloc -> sprintf "alloc(%s)" (pp_dtype alloc.t)
    | Alloc_arr alloc_arr ->
      sprintf "alloc_arracy(%s, %s)" (pp_dtype alloc_arr.t) (pp_mexp alloc_arr.e)

  and pp_mexp e = pp_exp (Mark.data e)

  and pp_dtype = function
    | Int -> "int"
    | Bool -> "bool"
    | Void -> "void"
    | Ctype ident -> Symbol.name ident
    | Pointer p -> "*" ^ pp_dtype p
    | Array arr -> pp_dtype arr ^ "[]"
    | Struct s -> sprintf "struct %s" (Symbol.name s)
  ;;

  let pp_decl = function
    | New_var id -> sprintf "%s %s;" (pp_dtype id.t) (Symbol.name id.name)
    | Init id ->
      sprintf "%s %s = %s;" (pp_dtype id.t) (Symbol.name id.name) (pp_mexp id.value)
  ;;

  let pp_simp = function
    | Assign asn ->
      sprintf "%s %s %s;" (pp_mexp asn.name) (pp_asnop asn.op) (pp_mexp asn.value)
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

  and pp_param (param : param) = sprintf " %s %s" (pp_dtype param.t) (Symbol.name param.i)
  and pp_field (field : field) = sprintf "%s %s" (pp_dtype field.t) (Symbol.name field.i)

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
    | Sdefn sdefn ->
      sprintf
        "struct %s{%s}"
        (Symbol.name sdefn.struct_name)
        (List.map sdefn.fields ~f:pp_field |> String.concat ~sep:"; ")
    | Sdecl sdecl -> sprintf "struct %s;" (Symbol.name sdecl.struct_name)

  and pp_mstm stm = pp_stm (Mark.data stm)
  and pp_msimp msimp = pp_simp (Mark.data msimp)
  and pp_block stms = "{\n" ^ pp_blk stms ^ "}"

  let pp_program program = List.map program ~f:pp_gdecl |> String.concat ~sep:"\n\n"
end
