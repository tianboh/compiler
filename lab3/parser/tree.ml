(* L2 Compiler
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
 * We use Integer zero to denote false and one to denote true in IR
 * Other integer cannot be treated as a boolean in CJump.
 * 
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 * Created: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)
module Temp = Var.Temp
module Label = Util.Label

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

let is_relop = function
  | Equal_eq | Greater | Greater_eq | Less | Less_eq | Not_eq -> true
  | _ -> false
;;

type exp =
  | Const of Int32.t
  | Temp of Temp.t
  | Binop of
      { lhs : exp
      ; op : binop
      ; rhs : exp
      }
  (* Sexp is designed as a counterpart for AST terop.
   * It will execute stm for side effect, like CJump, 
   * and then return exp. *)
  | Sexp of
      { stm : stm
      ; exp : exp
      }

and stm =
  | Move of
      { dest : Temp.t
      ; src : exp
      }
  | Return of exp
  | Jump of Label.t
  | CJump of
      { (* Jump if lhs op rhs is true*)
        lhs : exp
      ; op : binop
      ; rhs : exp
      ; target_stm : Label.t
      }
  | Label of Label.t
  | Seq of
      { head : stm
      ; tail : stm
      }
  | Nop
  | NExp of
      (* NExp only execute expression for potential side effect
       * But it will drop the result after execution. *)
      exp

type program = stm

module type PRINT = sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_program : program -> string
end

module Print : PRINT = struct
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
      Printf.sprintf
        "(%s %s %s)"
        (pp_exp binop.lhs)
        (pp_binop binop.op)
        (pp_exp binop.rhs)
    | Sexp sexp -> Printf.sprintf "(%s %s)" (pp_stm sexp.stm) (pp_exp sexp.exp)

  and pp_stm = function
    | Move mv -> Temp.name mv.dest ^ "  <--  " ^ pp_exp mv.src ^ "\n"
    | Return e -> "return " ^ pp_exp e ^ "\n"
    | Jump j -> "jump " ^ Label.name j ^ "\n"
    | CJump cj ->
      Printf.sprintf
        "cjump(%s %s %s) Target:%s\n"
        (pp_exp cj.lhs)
        (pp_binop cj.op)
        (pp_exp cj.rhs)
        (Label.name cj.target_stm)
    | Label l -> Label.content l ^ "\n"
    | Seq seq -> pp_stm seq.head ^ pp_stm seq.tail
    | Nop -> "nop" ^ "\n"
    | NExp nexp -> pp_exp nexp ^ "\n"
  ;;

  let pp_program program = pp_stm program
end
