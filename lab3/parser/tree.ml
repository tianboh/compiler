(* L1 Compiler
 * IR Trees
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
*)
module Temp = Temp.Temp

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Logic_and
  | Logic_or
  | Bit_and
  | Bit_or
  | Bit_xor

type exp =
  | Const_int of Int32.t
  | Const_bool of Bool.t
  | Temp of Temp.t
  | Binop of
      { lhs : exp
      ; op : binop
      ; rhs : exp
      }

type stm =
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
    | Logic_and -> "&&"
    | Logic_or -> "||"
    | Bit_and -> "&"
    | Bit_or -> "|"
    | Bit_xor -> "^"
  ;;

  let rec pp_exp = function
    | Const_int x -> Int32.to_string x
    | Const_bool x -> Bool.to_string x
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
