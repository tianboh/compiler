(* L5 Compiler
 * Quad
 *
 * Only have instr. More low-level compared with IR.
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

module Op = struct
  type t =
    | Imm of Int64.t
    | Temp of Temp.t
  [@@deriving sexp, compare, hash]

  let pp = function
    | Imm i -> Int64.to_string i
    | Temp t -> Temp.name t
  ;;

  let of_int i = Imm i
  let of_t t = Temp t
end

module rec Sop : sig
  include Var.Sized.Sized_Interface with type i = Op.t

  val to_St : t -> St.t
  val to_t : t -> Temp.t
end = struct
  include Var.Sized.Wrapper (Op)

  let to_t sop : Temp.t =
    match sop.data with
    | Temp t -> t
    | Imm _ -> failwith "imm cannot to t"
  ;;

  let to_St sop =
    match sop.data with
    | Temp t -> St.wrap sop.size t
    | _ -> failwith "to_St expect temp"
  ;;
end

and St : sig
  include Var.Sized.Sized_Interface with type i = Temp.t

  val to_Sop : t -> Sop.t
  val to_t : t -> Temp.t
end = struct
  include Var.Sized.Wrapper (Temp)

  let to_Sop st = st.data |> Op.of_t |> Sop.wrap st.size
  let to_t st = st.data
end

module StMap = Map.Make (St)
module Addr : Var.Addr.Sig with type i = Sop.t = Var.Addr.Wrapper (Sop)
module Mem : Var.Sized.Sized_Interface with type i = Addr.t = Var.Sized.Wrapper (Addr)

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
      ; dest : St.t
      ; lhs : Sop.t
      ; rhs : Sop.t
      }
  | Fcall of
      { func_name : Symbol.t
      ; dest : St.t option
      ; args : Sop.t list
      }
  | Cast of
      { (* Do not generate new temporary. 
         * Only change the size of temporary. *)
        dest : St.t
      ; src : St.t
      }
  | Move of
      { dest : St.t
      ; src : Sop.t
      }
  | Jump of { target : Label.t }
  | CJump of
      { lhs : Sop.t
      ; op : binop
      ; rhs : Sop.t
      ; target_true : Label.t
      ; target_false : Label.t
      }
  | Ret of { var : Sop.t option }
  | Load of
      { src : Mem.t
      ; dest : St.t
      }
  | Store of
      { src : Sop.t
      ; dest : Mem.t
      }
  | Label of Label.t
  | Directive of string
  | Comment of string

type fdefn =
  { func_name : Symbol.t
  ; body : instr list
  ; pars : St.t list
  }

type program = fdefn list
type i = instr
type t = St.t [@@deriving sexp, compare, hash]

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
let label (l : Label.t) = Label l
let jump (target : Label.t) : instr = Jump { target }
let ret () : instr = Ret { var = None }

let get_label (instr : instr) : Label.t =
  match instr with
  | Label l -> l
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
  | Jump _ -> Jump { target }
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

(* Functions for SSA instr interface *)
let get_def = function
  | Binop binop -> [ binop.dest ]
  | Fcall fcall ->
    (match fcall.dest with
    | None -> []
    | Some s -> [ s ])
  | Cast cast -> [ cast.dest ]
  | Move move -> [ move.dest ]
  | Load load -> [ load.dest ]
  | Ret _ | Jump _ | CJump _ | Store _ | Label _ | Directive _ | Comment _ -> []
;;

let _get_uses (sop : Sop.t) : St.t list =
  match sop.data with
  | Imm _ -> []
  | Temp _ -> [ Sop.to_St sop ]
;;

let get_uses = function
  | Binop binop -> _get_uses binop.lhs @ _get_uses binop.rhs
  | Fcall fcall -> List.map fcall.args ~f:_get_uses |> List.concat
  | Cast cast -> [ cast.src ]
  | Move move -> _get_uses move.src
  | CJump cjp -> _get_uses cjp.lhs @ _get_uses cjp.rhs
  | Ret ret ->
    (match ret.var with
    | None -> []
    | Some s -> _get_uses s)
  | Store store -> _get_uses store.src
  | Jump _ | Load _ | Directive _ | Comment _ | Label _ -> []
;;

let replace_def (instr : i) (dic : (t * t) list) : i =
  let dic = StMap.of_alist_exn dic in
  match instr with
  | Move move ->
    let dest_new = Map.find_exn dic move.dest in
    Move { move with dest = dest_new }
  | Binop binop ->
    let dest_new = Map.find_exn dic binop.dest in
    Binop { binop with dest = dest_new }
  | Fcall fcall ->
    (match fcall.dest with
    | None -> instr
    | Some dest ->
      let dest_new = Map.find_exn dic dest in
      Fcall { fcall with dest = Some dest_new })
  | Cast cast ->
    let dest_new = Map.find_exn dic cast.dest in
    Cast { cast with dest = dest_new }
  | Load load ->
    let dest_new = Map.find_exn dic load.dest in
    Load { load with dest = dest_new }
  | Ret _ | Jump _ | CJump _ | Store _ | Label _ | Directive _ | Comment _ -> instr
;;

let _replace_uses (sexp : Sop.t) (dic : St.t StMap.t) : Sop.t =
  match sexp.data with
  | Imm _ -> sexp
  | Temp _ ->
    let st = Sop.to_St sexp in
    let st_ssa = StMap.find_exn dic st in
    St.to_Sop st_ssa
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
          else failwith "duplicate src temp to different dests")
        else StMap.set acc ~key:src ~data:dest)
  in
  match instr with
  | Binop binop ->
    let lhs = _replace_uses binop.lhs dic in
    let rhs = _replace_uses binop.lhs dic in
    Binop { binop with lhs; rhs }
  | Fcall fcall ->
    let args = List.map fcall.args ~f:(fun arg -> _replace_uses arg dic) in
    Fcall { fcall with args }
  | Cast cast ->
    let src = _replace_uses (St.to_Sop cast.src) dic in
    Cast { cast with src = Sop.to_St src }
  | Move move ->
    let src = _replace_uses move.src dic in
    Move { move with src }
  | CJump cjp ->
    let lhs = _replace_uses cjp.lhs dic in
    let rhs = _replace_uses cjp.rhs dic in
    CJump { cjp with lhs; rhs }
  | Ret ret ->
    (match ret.var with
    | None -> Ret ret
    | Some exp ->
      let var = _replace_uses exp dic in
      Ret { var = Some var })
  | Store store ->
    let src = _replace_uses store.src dic in
    Store { store with src }
  | Jump _ | Label _ | Directive _ | Comment _ | Load _ -> instr
;;

let new_t (t : t) = St.wrap t.size (Temp.create ())

let assign (st : t) (v : Int64.t) : i =
  Move { dest = st; src = Sop.wrap st.size (Op.of_int v) }
;;

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

let pp_inst = function
  | Binop binop ->
    sprintf
      "%s <-- %s %s %s"
      (St.pp binop.dest)
      (Sop.pp binop.lhs)
      (pp_binop binop.op)
      (Sop.pp binop.rhs)
  (* | Move mv -> sprintf "%s <-- %s" (Sop.pp mv.dest) (Sop.pp mv.src) *)
  | Move mv ->
    if Size.compare (mv.src.size :> Size.t) (mv.dest.size :> Size.t) <> 0
    then failwith (sprintf "move size mismatch %s -> %s" (Sop.pp mv.src) (St.pp mv.dest));
    sprintf "%s <-- %s" (St.pp mv.dest) (Sop.pp mv.src)
  | Cast cast ->
    sprintf
      "cast %s <-- %s"
      (Temp.name' cast.dest.data cast.dest.size)
      (Temp.name' cast.src.data cast.src.size)
  | Jump jp -> sprintf "jump %s" (Label.name jp.target)
  | CJump cjp ->
    sprintf
      "cjump(%s %s %s) %s, %s"
      (Sop.pp cjp.lhs)
      (pp_binop cjp.op)
      (Sop.pp cjp.rhs)
      (Label.name cjp.target_true)
      (Label.name cjp.target_false)
  | Label label -> sprintf "%s" (Label.content label)
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
  | Ret ret ->
    (match ret.var with
    | None -> sprintf "return"
    | Some var -> sprintf "return %s" (Sop.pp var))
  | Fcall call ->
    (match call.dest with
    | None ->
      sprintf
        "%s(%s)"
        (Symbol.name call.func_name)
        (List.map call.args ~f:(fun arg -> Sop.pp arg) |> String.concat ~sep:", ")
    | Some dest ->
      sprintf
        "%s <- %s(%s)"
        (Temp.name' dest.data dest.size)
        (Symbol.name call.func_name)
        (List.map call.args ~f:(fun arg -> Sop.pp arg) |> String.concat ~sep:", "))
  | Load load ->
    sprintf "load %s <- %s" (Temp.name' load.dest.data load.dest.size) (Mem.pp load.src)
  | Store store -> sprintf "store %s <- %s" (Mem.pp store.dest) (Sop.pp store.src)
;;

let pp_insts (insts : instr list) : string =
  List.map insts ~f:(fun inst -> pp_inst inst) |> String.concat ~sep:"\n"
;;

let pp_fdefn (fdefn : fdefn) =
  let pars_str =
    List.map fdefn.pars ~f:(fun par -> Temp.name' par.data par.size)
    |> String.concat ~sep:", "
  in
  let head, body =
    match fdefn.body with
    | [] -> failwith "expect func label"
    | h :: t -> h, t
  in
  let body_str = List.map body ~f:(fun inst -> pp_inst inst) |> String.concat ~sep:"\n" in
  sprintf "%s(%s)\n%s\n" (pp_inst head) pars_str body_str
;;

let rec pp_program (program : fdefn list) res =
  match program with
  | [] -> res
  | h :: t ->
    let fdefn_str = pp_fdefn h ^ "\n" in
    let res = res ^ fdefn_str in
    pp_program t res
;;
