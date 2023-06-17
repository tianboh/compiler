(* L3 Compiler
 *
 * This is the immediate layer before regalloc.
 * Based on IR inst, this module provides extra
 * 1) register type for operand
 * 2) above_frame and below_frame for memory access
 * 3) def-use info for each instruction.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
open Var.Size
module Register = Var.X86_reg.Logic
module Temp = Var.Temp
module Label = Util.Label
module Symbol = Util.Symbol

type scope =
  | Internal
  | External

type operand =
  | Imm of Int32.t
  | Temp of Temp.t
  | Reg of Register.t
  | Above_frame of int
  | Below_frame of int

type line =
  { uses : operand list
  ; defines : operand list
  ; live_out : operand list
  ; move : bool
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
      ; line : line
      }
  | Fcall of
      { (* return to rax by convention *)
        func_name : Symbol.t
      ; args : operand list
      ; line : line
      ; scope : scope
      }
  | Mov of
      { dest : operand
      ; src : operand
      ; line : line
      }
  | Jump of
      { target : Label.t
      ; line : line
      }
  | CJump of
      { (*Jump if cond == 1*)
        lhs : operand
      ; op : bin_op
      ; rhs : operand
      ; target_true : Label.t
      ; target_false : Label.t
      ; line : line
      }
  | Ret of { line : line }
  | Label of
      { label : Label.t
      ; line : line
      }
  | Assert of
      { var : operand
      ; line : line
      }
  | Push of
      { var : operand
      ; line : line
      }
  | Pop of
      { var : operand
      ; line : line
      }
  | Directive of string
  | Comment of string

type section =
  { name : instr (* This can only be of type label in instr *)
  ; content : instr list
  }

type fdefn =
  { func_name : string
  ; body : instr list
  }

type program = fdefn list

let to_int_list (operands : operand list) : int list =
  List.fold operands ~init:[] ~f:(fun acc x ->
      match x with
      | Temp t -> t.id :: acc
      | Reg r -> Register.reg_idx r :: acc
      | Above_frame _ | Below_frame _ | Imm _ -> acc)
;;

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

let pp_operand = function
  | Imm n -> "$" ^ Int32.to_string n
  | Temp t -> Temp.name t
  | Reg r -> Register.reg_to_str r
  | Above_frame af -> sprintf "%d(%%rbp)" (af * type_size_bit BYTE)
  | Below_frame bf -> sprintf "-%d(%%rbp)" (bf * type_size_bit BYTE)
;;

let pp_scope = function
  | Internal -> "_c0_"
  | External -> ""
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
  | Jump jp -> sprintf "jump %s" (Label.name jp.target)
  | CJump cjp ->
    sprintf
      "cjump(%s %s %s) target_true: %s, target_false : %s"
      (pp_operand cjp.lhs)
      (pp_binop cjp.op)
      (pp_operand cjp.rhs)
      (Label.name cjp.target_true)
      (Label.name cjp.target_false)
  | Label label -> sprintf "%s" (Label.content label.label)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Ret _ -> sprintf "return"
  | Assert asrt -> sprintf "assert %s" (pp_operand asrt.var)
  | Fcall fcall ->
    sprintf
      "fcall %s%s(%s)"
      (pp_scope fcall.scope)
      (Symbol.name fcall.func_name)
      (List.map fcall.args ~f:(fun arg -> pp_operand arg) |> String.concat ~sep:", ")
  | Push push -> sprintf "push %s" (pp_operand push.var)
  | Pop pop -> sprintf "pop %s " (pp_operand pop.var)
;;

let rec pp_insts (program : instr list) res =
  match program with
  | [] -> res
  | h :: t ->
    let fdefn_str = pp_inst h ^ "\n" in
    let res = res ^ fdefn_str in
    pp_insts t res
;;

let rec pp_program (program : fdefn list) res =
  match program with
  | [] -> res
  | h :: t ->
    let fdefn_str = h.func_name ^ ":\n" ^ pp_insts h.body "" ^ "\n" in
    let res = res ^ fdefn_str in
    pp_program t res
;;
