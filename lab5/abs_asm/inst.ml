(* L5 abstract assembly
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

  let is_temp = function
    | Temp _ -> true
    | _ -> false
  ;;

  let is_reg = function
    | Reg _ -> true
    | _ -> false
  ;;

  let get_temp_exn t =
    match t with
    | Temp t -> t
    | _ -> failwith "expect temp"
  ;;

  let get_reg_exn t =
    match t with
    | Reg r -> r
    | _ -> failwith "expect temp"
  ;;
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

module StMap = Map.Make (St)
module Line = Regalloc_util.Line.Wrapper (Op)

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

type _instr =
  | Binop of
      { op : binop
      ; dest : Sop.t
      ; lhs : Sop.t
      ; rhs : Sop.t
      }
  | Fcall of
      { (* return to rax by convention *)
        func_name : Symbol.t
      ; args : Sop.t list
      }
  | Cast of
      { dest : St.t
      ; src : St.t
      }
  | Move of
      { dest : Sop.t
      ; src : Sop.t
      }
  | Jump of Label.t
  | CJump of
      { lhs : Sop.t
      ; op : binop
      ; rhs : Sop.t
      ; target_true : Label.t
      ; target_false : Label.t
      }
  | Ret
  | Label of Label.t
  | Push of Sop.t
  | Pop of Sop.t
  | Load of
      { src : Mem.t
      ; dest : St.t
      }
  | Store of
      { src : Sop.t
      ; dest : Mem.t
      }
  | Directive of string
  | Comment of string

type instr =
  { data : _instr
  ; line : Line.t
  }

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
type t = St.t [@@deriving sexp, compare, hash]

let to_int_list (ops : Op.t list) : int list =
  List.fold ops ~init:[] ~f:(fun acc x ->
      match x with
      | Temp t -> t.id :: acc
      | Reg r -> Register.get_idx r :: acc
      | Above_frame _ | Imm _ -> acc)
;;

(* Functions for regalloc *)
let is_move (instr : i) : bool =
  match instr.data with
  | Move _ | Cast _ -> true
  | _ -> false
;;

let is_dummy (instr : i) : bool =
  match instr.data with
  | Directive _ | Comment _ -> true
  | _ -> false
;;

let get_cjump_targets_exn (instr : i) : Label.t * Label.t =
  match instr.data with
  | CJump cjp -> cjp.target_true, cjp.target_false
  | _ -> failwith "expect cjump"
;;

let get_jump_target_exn (instr : i) : Label.t =
  match instr.data with
  | Jump jp -> jp
  | _ -> failwith "expect jump"
;;

(* Functions for CFG interface *)
let is_label (instr : i) : bool =
  match instr.data with
  | Label _ -> true
  | _ -> false
;;

let is_jump (instr : i) : bool =
  match instr.data with
  | Jump _ -> true
  | _ -> false
;;

let is_cjump (instr : i) : bool =
  match instr.data with
  | CJump _ -> true
  | _ -> false
;;

let is_return (instr : i) : bool =
  match instr.data with
  | Ret -> true
  | _ -> false
;;

let is_raise (instr : i) : bool =
  match instr.data with
  | Fcall f -> if phys_equal f.func_name Symbol.Fname.raise then true else false
  | _ -> false
;;

let[@warning "-27"] is_assert (i : instr) : bool = false
let empty_line () : Line.t = { defines = []; uses = []; live_out = []; move = Not }
let label (l : Label.t) : i = { data = Label l; line = empty_line () }
let jump (target : Label.t) : i = { data = Jump target; line = empty_line () }
let ret () : i = { data = Ret; line = empty_line () }

let get_label (instr : instr) : Label.t =
  match instr.data with
  | Label l -> l
  | _ -> failwith "expect instr to be label"
;;

(* Given jump/conditional jump, return target label list. *)
let next (instr : instr) : Label.t list =
  match instr.data with
  | Jump jp -> [ jp ]
  | CJump cjp -> [ cjp.target_false; cjp.target_true ]
  | _ -> failwith "expect jump or cond jump"
;;

(* Replace target of Jump *)
let replace_target (instr : instr) (target : Label.t) : instr =
  match instr.data with
  | Jump _ -> { instr with data = Jump target }
  | _ -> failwith "expect jump for taget"
;;

(* Replace old target to new target for CJump *)
let replace_ctarget (instr : instr) (old_target : Label.t) (new_target : Label.t) : instr =
  match instr.data with
  | CJump cjp ->
    if Label.equal cjp.target_false old_target
    then { instr with data = CJump { cjp with target_false = new_target } }
    else if Label.equal cjp.target_true old_target
    then { instr with data = CJump { cjp with target_true = new_target } }
    else failwith "old target do not match to cond jump"
  | _ -> failwith "expect cond jump to replace target"
;;

let filter_st (sop : Sop.t) : t list =
  match sop.data with
  | Imm _ | Reg _ | Above_frame _ -> []
  | Temp t -> [ St.wrap sop.size t ]
;;

(* Functions for SSA, reg alloc instr interface *)
let get_def (instr : i) : t list =
  match instr.data with
  | Binop binop -> filter_st binop.dest
  | Cast cast -> [ cast.dest ]
  | Move move -> filter_st move.dest
  | Pop var -> filter_st var
  | Load load -> [ load.dest ]
  | CJump _
  | Fcall _
  | Jump _
  | Ret
  | Push _
  | Store _
  | Directive _
  | Comment _
  | Label _ -> []
;;

let get_uses (instr : i) : t list =
  match instr.data with
  | Binop binop -> filter_st binop.lhs @ filter_st binop.rhs
  | Fcall fcall -> List.map fcall.args ~f:filter_st |> List.concat
  | Cast cast -> [ cast.src ]
  | Move move -> filter_st move.src
  | CJump cjp -> filter_st cjp.lhs @ filter_st cjp.rhs
  | Push var -> filter_st var
  | Store store -> filter_st store.src
  | Load _ | Label _ | Pop _ | Directive _ | Comment _ | Ret | Jump _ -> []
;;

let sop_is_st (sop : Sop.t) : bool =
  match sop.data with
  | Imm _ | Reg _ | Above_frame _ -> false
  | Temp _ -> true
;;

let sop_to_st_exn (sop : Sop.t) : St.t =
  match sop.data with
  | Imm _ | Reg _ | Above_frame _ -> failwith "expect temp"
  | Temp t -> St.wrap sop.size t
;;

let replace_def (instr : i) (dic : (t * t) list) : i =
  let dic = StMap.of_alist_exn dic in
  match instr.data with
  | Binop binop ->
    if sop_is_st binop.dest
    then (
      let dest_old = sop_to_st_exn binop.dest in
      let dest_new = Map.find_exn dic dest_old in
      let data = Binop { binop with dest = St.to_Sop dest_new } in
      { instr with data })
    else instr
  | Cast cast ->
    let dest = Map.find_exn dic cast.dest in
    let data = Cast { cast with dest } in
    { instr with data }
  | Move move ->
    if sop_is_st move.dest
    then (
      let dest_old = sop_to_st_exn move.dest in
      let dest_new = Map.find_exn dic dest_old in
      let data = Move { move with dest = St.to_Sop dest_new } in
      { instr with data })
    else instr
  | Pop pop ->
    if sop_is_st pop
    then (
      let var_old = sop_to_st_exn pop in
      let var_new = Map.find_exn dic var_old in
      let data = Pop (St.to_Sop var_new) in
      { instr with data })
    else instr
  | Load load ->
    let dest = Map.find_exn dic load.dest in
    let data = Load { load with dest } in
    { instr with data }
  | CJump _
  | Fcall _
  | Jump _
  | Ret
  | Push _
  | Store _
  | Directive _
  | Comment _
  | Label _ -> instr
;;

let _replace_uses (sop : Sop.t) (dic : t StMap.t) : Sop.t =
  if sop_is_st sop
  then (
    let st = sop_to_st_exn sop in
    let new_t = StMap.find_exn dic st in
    St.to_Sop new_t)
  else sop
;;

let replace_uses (instr : i) (dic : (t * t) list) : i =
  let dic =
    List.fold dic ~init:StMap.empty ~f:(fun acc tuple ->
        let src, dest = tuple in
        if StMap.mem acc src
        then (
          let old_dest = StMap.find_exn acc src in
          if phys_equal old_dest dest
          then acc
          else failwith "duplicate src to different dests")
        else StMap.set acc ~key:src ~data:dest)
  in
  match instr.data with
  | Binop binop ->
    let lhs = _replace_uses binop.lhs dic in
    let rhs = _replace_uses binop.rhs dic in
    let data = Binop { binop with lhs; rhs } in
    { instr with data }
  | Fcall fcall ->
    let args = List.map fcall.args ~f:(fun arg -> _replace_uses arg dic) in
    let data = Fcall { fcall with args } in
    { instr with data }
  | Cast cast ->
    let src_sop = _replace_uses (St.to_Sop cast.src) dic in
    (match src_sop.data with
    | Temp t ->
      let src = St.wrap src_sop.size t in
      let data = Cast { cast with src } in
      { instr with data }
    | _ -> failwith "expect cast temp")
  | Move move ->
    let src = _replace_uses move.src dic in
    let data = Move { move with src } in
    { instr with data }
  | CJump cjp ->
    let lhs = _replace_uses cjp.lhs dic in
    let rhs = _replace_uses cjp.rhs dic in
    let data = CJump { cjp with lhs; rhs } in
    { instr with data }
  | Pop pop ->
    let var = _replace_uses pop dic in
    let data = Pop var in
    { instr with data }
  | Store store ->
    let src = _replace_uses store.src dic in
    let data = Store { store with src } in
    { instr with data }
  | Load _ | Push _ | Label _ | Ret | Jump _ | Directive _ | Comment _ -> instr
;;

let new_t (t : t) : t = Temp.create () |> St.wrap t.size

let assign (st : t) (v : Int64.t) : i =
  let dest = Op.of_temp st.data in
  let line : Line.t = { defines = [ dest ]; uses = []; live_out = []; move = Copy } in
  let dest = Sop.wrap st.size dest in
  let src = Sop.wrap st.size (Op.of_imm v) in
  let data = Move { dest; src } in
  { data; line }
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

let pp_inst (inst : i) =
  match inst.data with
  | Binop binop ->
    sprintf
      "%s <-- %s %s %s"
      (Sop.pp binop.dest)
      (Sop.pp binop.lhs)
      (pp_binop binop.op)
      (Sop.pp binop.rhs)
  | Move mv ->
    if Size.compare (mv.dest.size :> Size.t) (mv.src.size :> Size.t) <> 0
    then failwith (sprintf "move mismatch %s <-- %s" (Sop.pp mv.dest) (Sop.pp mv.src));
    sprintf "%s <-- %s" (Sop.pp mv.dest) (Sop.pp mv.src)
  | Cast cast ->
    sprintf
      "cast %s <-- %s"
      (Temp.name' cast.dest.data cast.dest.size)
      (Temp.name' cast.src.data cast.src.size)
  | Jump jp -> sprintf "jump %s" (Label.name jp)
  | CJump cjp ->
    sprintf
      "cjump(%s %s %s) target_true: %s, target_false : %s"
      (Sop.pp cjp.lhs)
      (pp_binop cjp.op)
      (Sop.pp cjp.rhs)
      (Label.name cjp.target_true)
      (Label.name cjp.target_false)
  | Label label -> sprintf "%s" (Label.content label)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Ret -> sprintf "return"
  | Fcall fcall ->
    sprintf
      "fcall %s(%s)"
      (Symbol.name fcall.func_name)
      (List.map fcall.args ~f:(fun arg -> Sop.pp arg) |> String.concat ~sep:", ")
  | Push push -> sprintf "push %s" (Sop.pp push)
  | Pop pop -> sprintf "pop %s " (Sop.pp pop)
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
