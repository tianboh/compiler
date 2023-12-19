(* L4 abstract assembly
 *
 * This is the immediate layer before regalloc.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
module Size = Var.Size
module Register = Var.X86_reg.Logic
module Temp = Var.Temp
module Label = Util.Label
module Symbol = Util.Symbol

type imm = Int64.t

type 'a sized =
  { data : 'a
  ; size : Size.primitive
  }

type operand_logic =
  | Imm of imm
  | Temp of Temp.t
  | Reg of Register.t
  | Above_frame of Int64.t
  | Below_frame of Int64.t

type operand = operand_logic sized

type mem =
  { base : Register.t sized
  ; offset : Register.t sized option
  ; size : Size.primitive
  }

type line =
  { uses : operand_logic list
  ; defines : operand_logic list
  ; live_out : operand_logic list
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
      ; scope : [ `C0 | `External | `Internal ]
      }
  | Cast of
      { dest : Temp.t sized
      ; src : Temp.t sized
      ; line : line
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
  | Push of
      { var : operand
      ; line : line
      }
  | Pop of
      { var : operand
      ; line : line
      }
  | Load of
      { src : mem
      ; dest : Temp.t sized
      ; line : line
      }
  | Store of
      { src : operand
      ; dest : mem
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
  ; scope : [ `Internal | `C0 ]
  }

type program = fdefn list

let to_int_list (operands : operand list) : int list =
  List.fold operands ~init:[] ~f:(fun acc x ->
      match x.data with
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

let pp_operand (oprd : operand) =
  match oprd.data with
  | Imm n -> "$" ^ Int64.to_string n
  | Temp t -> Temp.name' t oprd.size
  | Reg r -> Register.reg_to_str r
  | Above_frame af -> sprintf "%Ld(%%rbp)" af
  | Below_frame bf -> sprintf "-%Ld(%%rbp)" bf
;;

let pp_memory mem =
  let base, offset = mem.base, mem.offset in
  let size = mem.size in
  sprintf
    "(%s, %s, %Ld)"
    (Register.reg_to_str ~size:base.size base.data)
    (match offset with
    | Some r -> Register.reg_to_str ~size:r.size r.data
    | None -> "")
    (Size.type_size_byte size)
;;

let pp_inst inst =
  match inst with
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
  | Fcall fcall ->
    sprintf
      "fcall %s%s(%s)"
      (Symbol.pp_scope fcall.scope)
      (Symbol.name fcall.func_name)
      (List.map fcall.args ~f:(fun arg -> pp_operand arg) |> String.concat ~sep:", ")
  | Push push -> sprintf "push %s" (pp_operand push.var)
  | Pop pop -> sprintf "pop %s " (pp_operand pop.var)
  | Load load ->
    sprintf
      "load %s <- %s"
      (Temp.name' load.dest.data load.dest.size)
      (pp_memory load.src)
  | Store store -> sprintf "store %s <- %s" (pp_memory store.dest) (pp_operand store.src)
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
    let func_name = Symbol.pp_scope h.scope ^ h.func_name in
    let fdefn_str = func_name ^ ":\n" ^ pp_insts h.body "" ^ "\n" in
    let res = res ^ fdefn_str in
    pp_program t res
;;
