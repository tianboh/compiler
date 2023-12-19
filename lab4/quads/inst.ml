(* L4 Compiler
 * Quad
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@andrew.cmu.edu>
 * Modified By: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
open Core
module Register = Var.X86_reg.Logic
module Temp = Var.Temp
module Label = Util.Label
module Symbol = Util.Symbol
module Size = Var.Size

type 'a sized =
  { size : Size.primitive
  ; data : 'a
  }

type operand_logic =
  | Imm of Int64.t
  | Temp of Temp.t

type operand = operand_logic sized

type mem =
  { (* Heap memory *)
    base : operand
  ; offset : operand option
  ; size : Size.primitive
  }

type bin_op =
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

type instr =
  | Binop of
      { op : bin_op
      ; dest : operand
      ; lhs : operand
      ; rhs : operand
      }
  | Fcall of
      { func_name : Symbol.t
      ; dest : Temp.t sized option
      ; args : operand list
      ; scope : [ `C0 | `External | `Internal ]
      }
  | Cast of
      { dest : Temp.t sized
      ; src : Temp.t sized
      }
  | Mov of
      { dest : operand
      ; src : operand
      }
  | Jump of { target : Label.t }
  | CJump of
      { (*Jump if cond == 1*)
        lhs : operand
      ; op : bin_op
      ; rhs : operand
      ; target_true : Label.t
      ; target_false : Label.t
      }
  | Ret of { var : operand option }
  | Load of
      { src : mem
      ; dest : Temp.t sized
      }
  | Store of
      { src : operand
      ; dest : mem
      }
  | Label of Label.t
  | Directive of string
  | Comment of string

type fdefn =
  { func_name : Symbol.t
  ; body : instr list
  ; pars : Temp.t sized list
  ; scope : [ `Internal | `C0 ]
  }

type program = fdefn list

(* functions that format assembly output *)

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

let pp_operand (oprd : operand) : string =
  match oprd.data with
  | Imm n -> "$" ^ Int64.to_string n ^ "_" ^ Size.pp_size oprd.size
  | Temp t -> Temp.name' t oprd.size
;;

let pp_memory mem =
  let offset =
    match mem.offset with
    | Some offset -> pp_operand offset
    | None -> ""
  in
  sprintf "%s(%s)_%Ld" offset (pp_operand mem.base) (Size.type_size_byte mem.size)
;;

let pp_inst = function
  | Binop binop ->
    sprintf
      "%s <-- %s %s %s"
      (pp_operand binop.dest)
      (pp_operand binop.lhs)
      (pp_binop binop.op)
      (pp_operand binop.rhs)
  | Mov mv -> sprintf "%s <-- %s" (pp_operand mv.dest) (pp_operand mv.src)
  | Cast cast ->
    sprintf
      "%s <-- %s"
      (Temp.name' cast.dest.data cast.dest.size)
      (Temp.name' cast.src.data cast.src.size)
  | Jump jp -> sprintf "jump %s" (Label.name jp.target)
  | CJump cjp ->
    sprintf
      "cjump(%s %s %s) %s, %s"
      (pp_operand cjp.lhs)
      (pp_binop cjp.op)
      (pp_operand cjp.rhs)
      (Label.name cjp.target_true)
      (Label.name cjp.target_false)
  | Label label -> sprintf "%s" (Label.content label)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Ret ret ->
    (match ret.var with
    | None -> sprintf "return"
    | Some var -> sprintf "return %s" (pp_operand var))
  | Fcall call ->
    (match call.dest with
    | None ->
      sprintf
        "%s%s(%s)"
        (Symbol.pp_scope call.scope)
        (Symbol.name call.func_name)
        (List.map call.args ~f:(fun arg -> pp_operand arg) |> String.concat ~sep:", ")
    | Some dest ->
      sprintf
        "%s <- %s%s(%s)"
        (Temp.name' dest.data dest.size)
        (Symbol.pp_scope call.scope)
        (Symbol.name call.func_name)
        (List.map call.args ~f:(fun arg -> pp_operand arg) |> String.concat ~sep:", "))
  | Load load ->
    sprintf
      "load %s <- %s"
      (Temp.name' load.dest.data load.dest.size)
      (pp_memory load.src)
  | Store store -> sprintf "store %s <- %s" (pp_memory store.dest) (pp_operand store.src)
;;

let pp_fdefn (fdefn : fdefn) =
  let pars_str =
    List.map fdefn.pars ~f:(fun par -> Temp.name' par.data par.size)
    |> String.concat ~sep:", "
  in
  let body_str =
    List.map fdefn.body ~f:(fun inst -> pp_inst inst) |> String.concat ~sep:"\n"
  in
  let func_name = Symbol.pp_scope fdefn.scope ^ Symbol.name fdefn.func_name in
  sprintf "%s(%s)\n%s\n" func_name pars_str body_str
;;

let rec pp_program (program : fdefn list) res =
  match program with
  | [] -> res
  | h :: t ->
    let fdefn_str = pp_fdefn h ^ "\n" in
    let res = res ^ fdefn_str in
    pp_program t res
;;
