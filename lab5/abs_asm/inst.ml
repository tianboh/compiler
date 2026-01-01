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

  let pp = function
    | Imm n -> "$" ^ Int64.to_string n
    | Temp t -> Temp.name t
    | Reg r -> Register.pp r
    | Above_frame af -> sprintf "%Ld(%%rbp)" af

  let of_imm i = Imm i
  let of_temp t = Temp t
  let of_reg (reg : Register.t) = Reg reg
  let of_af af = Above_frame af
end

module Sop : Var.Sized.Sized_Interface with type i = Op.t =
  Var.Sized.Wrapper (Op)

module Addr = Var.Addr.Wrapper (Register)
module Mem = Var.Sized.Wrapper (Addr)

let t_to_Sop (t : Temp.t) : Sop.t = t |> Op.of_temp |> Sop.wrap t.size

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
  | Binop of { op : binop; dest : Sop.t; lhs : Sop.t; rhs : Sop.t }
  | Fcall of {
      (* return to rax by convention *)
      func_name : Symbol.t;
      args : Sop.t list;
    }
  | Cast of { dest : Temp.t; src : Temp.t }
  | Mov of { dest : Sop.t; src : Sop.t }
  | Jump of { target : Label.t }
  | CJump of {
      lhs : Sop.t;
      op : binop;
      rhs : Sop.t;
      target_true : Label.t;
      target_false : Label.t;
    }
  | Ret
  | Label of { label : Label.t }
  | Push of { var : Sop.t }
  | Pop of { var : Sop.t }
  | Load of { src : Mem.t; dest : Temp.t }
  | Store of { src : Sop.t; dest : Mem.t }
  | Directive of string
  | Comment of string

let get_targets (instr : instr) : Label.t list =
  match instr with
  | Jump j -> [ j.target ]
  | CJump cj -> [ cj.target_false; cj.target_true ]
  | _ -> []

type section = {
  name : instr; (* This can only be of type label in instr *)
  content : instr list;
}

type fdefn = { func_name : string; body : instr list }
type program = fdefn list
type t = instr

let to_int_list (ops : Op.t list) : int list =
  List.fold ops ~init:[] ~f:(fun acc x ->
      match x with
      | Temp t -> t.id :: acc
      | Reg r -> Register.get_idx r :: acc
      | Above_frame _ | Imm _ -> acc)

(* Functions for CFG interface *)
let is_label = function Label _ -> true | _ -> false
let is_jump = function Jump _ -> true | _ -> false
let is_cjump = function CJump _ -> true | _ -> false
let is_return = function Ret -> true | _ -> false

let is_terminator (instr : t) : bool =
  is_jump instr || is_cjump instr || is_return instr

let has_side_effect (instr : t) : bool =
  match instr with
  | Cast _ | Mov _ | Directive _ | Load _ | Comment _ -> false
  | Label _ | Ret | Store _ | Jump _ | CJump _ | Push _ | Pop _ | Fcall _ ->
      true
  | Binop binop -> (
      match binop.op with Divided_by | Modulo -> true | _ -> false)

let[@warning "-27"] is_assert (i : instr) : bool = false

let get_label (instr : instr) : Label.t =
  match instr with
  | Label l -> l.label
  | _ -> failwith "expect instr to be label"

let gen_ret () : instr = Ret
let gen_label (l : Label.t) = Label { label = l }
let gen_jump (target : Label.t) : t = Jump { target }

let gen_mov (src : Temp.t) (dest : Temp.t) : t =
  Mov
    {
      dest = Op.of_temp dest |> Sop.wrap dest.size;
      src = Op.of_temp src |> Sop.wrap src.size;
    }

let sops_to_ts (sops : Sop.t list) : Temp.t list =
  List.fold_left sops ~init:[] ~f:(fun acc sop ->
      match sop.data with
      | Temp t -> t :: acc
      | Imm _ | Reg _ | Above_frame _ -> acc)

(* Get lhs temporary(s) *)
let get_defs (instr : t) : Temp.t list =
  match instr with
  | Binop binop -> sops_to_ts [ binop.dest ]
  | Cast cast -> [ cast.dest ]
  | Mov mov -> sops_to_ts [ mov.dest ]
  | Load load -> [ load.dest ]
  | Pop pop -> sops_to_ts [ pop.var ]
  | Push _ | CJump _ | Jump _ | Store _ | Ret | Label _ | Directive _
  | Comment _ | Fcall _ ->
      []

(* Get rhs temporary(s) *)
let get_uses (instr : t) : Temp.t list =
  match instr with
  | Binop binop -> sops_to_ts [ binop.lhs; binop.rhs ]
  | Fcall fcall -> sops_to_ts fcall.args
  | Cast cast -> [ cast.src ]
  | Mov mov -> sops_to_ts [ mov.src ]
  | CJump cjump -> sops_to_ts [ cjump.lhs; cjump.rhs ]
  | Push push -> sops_to_ts [ push.var ]
  | Store store -> sops_to_ts [ store.src ]
  | Load _ | Pop _ | Jump _ | Label _ | Ret | Directive _ | Comment _ -> []

(* Given jump/conditional jump, return target label list. *)
let next (instr : instr) : Label.t list =
  match instr with
  | Jump jp -> [ jp.target ]
  | CJump cjp -> [ cjp.target_false; cjp.target_true ]
  | _ -> failwith "expect jump or cond jump"

(* Replace target of Jump *)
let replace_target (instr : instr) (target : Label.t) : instr =
  match instr with
  | Jump _ -> Jump { target }
  | _ -> failwith "expect jump for taget"

(* Replace old target to new target for CJump *)
let replace_ctarget (instr : instr) (old_target : Label.t)
    (new_target : Label.t) : instr =
  match instr with
  | CJump cjp ->
      if Label.equal cjp.target_false old_target then
        CJump { cjp with target_false = new_target }
      else if Label.equal cjp.target_true old_target then
        CJump { cjp with target_true = new_target }
      else failwith "old target do not match to cond jump"
  | _ -> failwith "expect cond jump to replace target"

let replace_sop (sop : Sop.t) (old_temp : Temp.t) (new_temp : Temp.t) : Sop.t =
  match sop.data with
  | Temp t ->
      if Temp.equal t old_temp then
        Sop.wrap new_temp.size (new_temp |> Op.of_temp)
      else sop
  | _ -> sop

let replace_temp (instr : t) (old_temp : Temp.t) (new_temp : Temp.t) : t =
  let r_sop = replace_sop in
  let r_temp temp old_temp new_temp =
    if Temp.equal temp old_temp then new_temp else temp
  in
  match instr with
  | Binop b ->
      Binop
        {
          b with
          dest = r_sop b.dest old_temp new_temp;
          lhs = r_sop b.lhs old_temp new_temp;
          rhs = r_sop b.rhs old_temp new_temp;
        }
  | Fcall f ->
      Fcall
        {
          f with
          args = List.map f.args ~f:(fun arg -> r_sop arg old_temp new_temp);
        }
  | Cast c ->
      Cast
        {
          dest = r_temp c.dest old_temp new_temp;
          src = r_temp c.src old_temp new_temp;
        }
  | Mov m ->
      Mov
        {
          dest = r_sop m.dest old_temp new_temp;
          src = r_sop m.src old_temp new_temp;
        }
  | CJump cjump ->
      CJump
        {
          cjump with
          lhs = r_sop cjump.lhs old_temp new_temp;
          rhs = r_sop cjump.rhs old_temp new_temp;
        }
  | Push push -> Push { var = r_sop push.var old_temp new_temp }
  | Pop pop -> Pop { var = r_sop pop.var old_temp new_temp }
  | Load load -> Load { load with dest = r_temp load.dest old_temp new_temp }
  | Store store -> Store { store with src = r_sop store.src old_temp new_temp }
  | Ret -> Ret
  | Jump j -> Jump j
  | Label l -> Label l
  | Directive dir -> Directive dir
  | Comment cmt -> Comment cmt

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

let pp_inst inst =
  match inst with
  | Binop binop ->
      sprintf "%s <-- %s %s %s" (Sop.pp binop.dest) (Sop.pp binop.lhs)
        (pp_binop binop.op) (Sop.pp binop.rhs)
  | Mov mv ->
      if Size.compare' mv.dest.size mv.src.size <> 0 then
        failwith
          (sprintf "move mismatch %s <-- %s" (Sop.pp mv.dest) (Sop.pp mv.src));
      sprintf "%s <-- %s" (Sop.pp mv.dest) (Sop.pp mv.src)
  | Cast cast ->
      sprintf "cast %s <-- %s" (Temp.name cast.dest) (Temp.name cast.src)
  | Jump jp -> sprintf "jump %s" (Label.name jp.target)
  | CJump cjp ->
      sprintf "cjump(%s %s %s) target_true: %s, target_false : %s"
        (Sop.pp cjp.lhs) (pp_binop cjp.op) (Sop.pp cjp.rhs)
        (Label.name cjp.target_true)
        (Label.name cjp.target_false)
  | Label label -> sprintf "%s" (Label.content label.label)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Ret -> sprintf "return"
  | Fcall fcall ->
      sprintf "fcall %s(%s)"
        (Symbol.name fcall.func_name)
        (List.map fcall.args ~f:(fun arg -> Sop.pp arg)
        |> String.concat ~sep:", ")
  | Push push -> sprintf "push %s" (Sop.pp push.var)
  | Pop pop -> sprintf "pop %s " (Sop.pp pop.var)
  | Load load -> sprintf "load %s <- %s" (Temp.name load.dest) (Mem.pp load.src)
  | Store store ->
      sprintf "store %s <- %s" (Mem.pp store.dest) (Sop.pp store.src)

let rec pp_insts (program : instr list) res =
  match program with
  | [] -> res
  | h :: t ->
      let fdefn_str = pp_inst h ^ "\n" in
      let res = res ^ fdefn_str in
      pp_insts t res

let rec pp_program (program : fdefn list) res =
  match program with
  | [] -> res
  | h :: t ->
      let func_name = h.func_name in
      let fdefn_str = func_name ^ ":\n" ^ pp_insts h.body "" ^ "\n" in
      let res = res ^ fdefn_str in
      pp_program t res
