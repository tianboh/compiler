(* L1 Compiler
 * IR Trees
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod

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
  | Return of exp

type program = stm list

module type PRINT = sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_program : program -> string
end

module Print : PRINT = struct
  let pp_binop = function
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Mod -> "%"
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
  ;;

  let pp_stm = function
    | Move mv -> Temp.name mv.dest ^ "  <--  " ^ pp_exp mv.src
    | Return e -> "return " ^ pp_exp e
  ;;

  let rec pp_program = function
    | [] -> ""
    | stm :: stms -> pp_stm stm ^ "\n" ^ pp_program stms
  ;;
end
