(* L3 Compiler
 * IR Trees
 *
 * IR tree is a COMPAT version for AST. So it is robust
 * enough to support multiple back-end implemntation.
 * Compared with AST, IR tree has following feature
 *
 * Expression-level:
 * 1) Only have integer data type (AST also has boolean,
 * though both IR and AST do not have logical operation).
 * 2) Do not have ternary operator anymore.
 *
 * Statement-level:
 * 1) Use Jump and CJump to replace AST "while" and "if".
 * 2) No "declare" anymore.
 *
 * Function-level
 * We only keep track of fdefn and get rid of fdecl and typedef.
 * Also, the return type for fdefn is omitted because once
 * typecheck is done, remaining function can only return bool/int
 * as an RHS expression. Since bool and int is treated equally
 * in IR, we can safely ignore return type.
 *
 * We use Integer zero to denote false and one to denote true in IR
 * Other integer cannot be treated as a boolean in CJump.
 * 
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module Temp = Var.Temp
module Label = Util.Label
module Symbol = Util.Symbol

type binop =
  | Plus
  | Minus
  | Times
  | Divided_by
  | Modulo
  | And
  | Or
  | Xor
  | Right_shift
  | Left_shift
  | Equal_eq
  | Greater
  | Greater_eq
  | Less
  | Less_eq
  | Not_eq

type exp =
  | Const of Int32.t
  | Temp of Temp.t
  | Binop of
      { lhs : exp
      ; op : binop
      ; rhs : exp
      }

and stm =
  | Move of
      { dest : Temp.t
      ; src : exp
      }
  | Effect of
      { dest : Temp.t
      ; lhs : exp
      ; op : binop
      ; rhs : exp
      }
  | Fcall of
      { dest : Temp.t
      ; func_name : Symbol.t
      ; args : exp list
      }
  | Return of exp
  | Jump of Label.t
  | CJump of
      { (* Jump to target_true if lhs op rhs is true. 
         * Otherwise to target_false *)
        lhs : exp
      ; op : binop
      ; rhs : exp
      ; target_true : Label.t
      ; target_false : Label.t
      }
  | Label of Label.t
  | Nop
  | Assert of exp

type fdefn =
  { func_name : Symbol.t
  ; temps : Temp.t list
  ; body : stm list
  }

type program = fdefn list

module type PRINT = sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_stms : stm list -> string
  val pp_fdefn : fdefn -> string
  val pp_program : program -> string
end

module Print : PRINT = struct
  let sprintf = Printf.sprintf

  let pp_binop = function
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Divided_by -> "/"
    | Modulo -> "%"
    | And -> "&"
    | Or -> "|"
    | Xor -> "^"
    | Right_shift -> ">>"
    | Left_shift -> "<<"
    | Equal_eq -> "=="
    | Greater -> ">"
    | Greater_eq -> ">="
    | Less -> "<"
    | Less_eq -> "<="
    | Not_eq -> "!="
  ;;

  let rec pp_exp = function
    | Const x -> Int32.to_string x
    | Temp t -> Temp.name t
    | Binop binop ->
      sprintf "(%s %s %s)" (pp_exp binop.lhs) (pp_binop binop.op) (pp_exp binop.rhs)

  and pp_stm = function
    | Move mv -> Temp.name mv.dest ^ "  <--  " ^ pp_exp mv.src ^ "\n"
    | Effect eft ->
      sprintf
        "effect %s <- %s %s %s\n"
        (Temp.name eft.dest)
        (pp_exp eft.lhs)
        (pp_binop eft.op)
        (pp_exp eft.rhs)
    | Fcall c ->
      let dest = Temp.name c.dest in
      let func_name = Symbol.name c.func_name in
      let args = List.map (fun arg -> pp_exp arg) c.args |> String.concat ", " in
      sprintf "%s <- %s(%s)" dest func_name args
    | Return e -> "return " ^ pp_exp e ^ "\n"
    | Jump j -> "jump " ^ Label.name j ^ "\n"
    | CJump cj ->
      sprintf
        "cjump(%s %s %s) target_true:%s, target_false %s \n"
        (pp_exp cj.lhs)
        (pp_binop cj.op)
        (pp_exp cj.rhs)
        (Label.name cj.target_true)
        (Label.name cj.target_false)
    | Label l -> Label.content l ^ "\n"
    | Nop -> "nop" ^ "\n"
    | Assert asrt -> sprintf "assert(%s)\n" (pp_exp asrt)

  and pp_stms (stms : stm list) =
    List.map (fun stm -> pp_stm stm) stms |> String.concat "\n"
  ;;

  let pp_fdefn fdefn =
    let func_name = Symbol.name fdefn.func_name in
    let pars_str =
      List.map (fun temp -> Temp.name temp) fdefn.temps |> String.concat ", "
    in
    sprintf "%s(%s)\n" func_name pars_str ^ pp_stms fdefn.body
  ;;

  let pp_program program =
    List.map (fun fdefn -> pp_fdefn fdefn) program |> String.concat "\n"
  ;;
end
