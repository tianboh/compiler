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

module Op = struct
  type t =
    | Imm of Int64.t
    | Temp of Temp.t
    | Reg of Register.t
    | Above_frame of Int64.t
  [@@deriving sexp, compare, hash]

  let pp = function
    | Imm n -> "$" ^ Int64.to_string n
    | Temp t -> Temp.name t
    | Reg r -> Register.pp r
    | Above_frame af -> sprintf "%Ld(%%rbp)" af
  ;;

  let of_imm i = Imm i
  let of_temp t = Temp t
  let of_reg (reg : Register.t) = Reg reg
  let of_af af = Above_frame af
end

module Sop : Var.Sized.Sized_Interface with type i = Op.t = Var.Sized.Wrapper (Op)
module Addr = Var.Addr.Wrapper (Register)
module Mem = Var.Sized.Wrapper (Addr)

module St = struct
  include Var.Sized.Wrapper (Temp)

  let to_Sop st =
    let size = st.size in
    st.data |> Op.of_temp |> Sop.wrap size
  ;;
end

type line =
  { uses : Op.t list
  ; defines : Op.t list
  ; live_out : Op.t list
  ; move : bool
  }

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

type instr =
  | Binop of
      { op : binop
      ; dest : Sop.t
      ; lhs : Sop.t
      ; rhs : Sop.t
      ; line : line
      }
  | Fcall of
      { (* return to rax by convention *)
        func_name : Symbol.t
      ; args : Sop.t list
      ; line : line
      }
  | Cast of
      { dest : St.t
      ; src : St.t
      ; line : line
      }
  | Mov of
      { dest : Sop.t
      ; src : Sop.t
      ; line : line
      }
  | Jump of
      { target : Label.t
      ; line : line
      }
  | CJump of
      { lhs : Sop.t
      ; op : binop
      ; rhs : Sop.t
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
      { var : Sop.t
      ; line : line
      }
  | Pop of
      { var : Sop.t
      ; line : line
      }
  | Load of
      { src : Mem.t
      ; dest : St.t
      ; line : line
      }
  | Store of
      { src : Sop.t
      ; dest : Mem.t
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
type i = instr

let to_int_list (ops : Op.t list) : int list =
  List.fold ops ~init:[] ~f:(fun acc x ->
      match x with
      | Temp t -> t.id :: acc
      | Reg r -> Register.get_idx r :: acc
      | Above_frame _ | Imm _ -> acc)
;;

(* Functions for CFG interface *)
let is_label = function
  | Label _ -> true
  | _ -> false
;;

let is_jump = function
  | Jump _ -> true
  | _ -> false
;;

let is_cjump = function
  | CJump _ -> true
  | _ -> false
;;

let is_return = function
  | Ret _ -> true
  | _ -> false
;;

let is_raise = function
  | Fcall f -> if phys_equal f.func_name Symbol.Fname.raise then true else false
  | _ -> false
;;

let[@warning "-27"] is_assert (i : instr) : bool = false
let empty_line () = { defines = []; uses = []; live_out = []; move = false }
let label (l : Label.t) = Label { label = l; line = empty_line () }
let jump (target : Label.t) : instr = Jump { target; line = empty_line () }
let ret () : instr = Ret { line = empty_line () }

let get_label (instr : instr) : Label.t =
  match instr with
  | Label l -> l.label
  | _ -> failwith "expect instr to be label"
;;

(* Given jump/conditional jump, return target label list. *)
let next (instr : instr) : Label.t list =
  match instr with
  | Jump jp -> [ jp.target ]
  | CJump cjp -> [ cjp.target_false; cjp.target_true ]
  | _ -> failwith "expect jump or cond jump"
;;

(* Replace target of Jump *)
let replace_target (instr : instr) (target : Label.t) : instr =
  match instr with
  | Jump jp -> Jump { jp with target }
  | _ -> failwith "expect jump for taget"
;;

(* Replace old target to new target for CJump *)
let replace_ctarget (instr : instr) (old_target : Label.t) (new_target : Label.t) : instr =
  match instr with
  | CJump cjp ->
    if Label.equal cjp.target_false old_target
    then CJump { cjp with target_false = new_target }
    else if Label.equal cjp.target_true old_target
    then CJump { cjp with target_true = new_target }
    else failwith "old target do not match to cond jump"
  | _ -> failwith "expect cond jump to replace target"
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

let pp_inst inst =
  match inst with
  | Binop binop ->
    sprintf
      "%s <-- %s %s %s"
      (Sop.pp binop.dest)
      (Sop.pp binop.lhs)
      (pp_binop binop.op)
      (Sop.pp binop.rhs)
  | Mov mv ->
    if Size.compare (mv.dest.size :> Size.t) (mv.src.size :> Size.t) <> 0
    then failwith (sprintf "move mismatch %s <-- %s" (Sop.pp mv.dest) (Sop.pp mv.src));
    sprintf "%s <-- %s" (Sop.pp mv.dest) (Sop.pp mv.src)
  | Cast cast ->
    sprintf
      "cast %s <-- %s"
      (Temp.name' cast.dest.data cast.dest.size)
      (Temp.name' cast.src.data cast.src.size)
  | Jump jp -> sprintf "jump %s" (Label.name jp.target)
  | CJump cjp ->
    sprintf
      "cjump(%s %s %s) target_true: %s, target_false : %s"
      (Sop.pp cjp.lhs)
      (pp_binop cjp.op)
      (Sop.pp cjp.rhs)
      (Label.name cjp.target_true)
      (Label.name cjp.target_false)
  | Label label -> sprintf "%s" (Label.content label.label)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Ret _ -> sprintf "return"
  | Fcall fcall ->
    sprintf
      "fcall %s(%s)"
      (Symbol.name fcall.func_name)
      (List.map fcall.args ~f:(fun arg -> Sop.pp arg) |> String.concat ~sep:", ")
  | Push push -> sprintf "push %s" (Sop.pp push.var)
  | Pop pop -> sprintf "pop %s " (Sop.pp pop.var)
  | Load load ->
    sprintf "load %s <- %s" (Temp.name' load.dest.data load.dest.size) (Mem.pp load.src)
  | Store store -> sprintf "store %s <- %s" (Mem.pp store.dest) (Sop.pp store.src)
;;

let pp_insts (insts : instr list) : string =
  List.map insts ~f:(fun inst -> pp_inst inst) |> String.concat ~sep:"\n"
;;

let rec pp_program (program : fdefn list) res =
  match program with
  | [] -> res
  | h :: t ->
    let head, body =
      match h.body with
      | [] -> failwith "expect func name"
      | h :: t -> h, t
    in
    let fdefn_str = pp_inst head ^ "\n" ^ pp_insts body ^ "\n" in
    let res = res ^ fdefn_str in
    pp_program t res
;;