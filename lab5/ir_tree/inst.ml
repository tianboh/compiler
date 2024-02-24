(* L4 Compiler
 * IR Trees
 *
 * IR has two levels: statement and expression.
 *
 * Each exp is attached with size information.
 * This helps to better adjust instruction size in
 * x86 code generation.
 * 
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module Size = Var.Size
module Temp = Var.Temp
module Label = Util.Label
module Symbol = Util.Symbol
open Core

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
[@@deriving sexp, compare, hash]

module rec Addr : (Var.Addr.Sig with type i = Sexp.t) = Var.Addr.Wrapper (Sexp)

and Exp : sig
  type t =
    | Void
    | Const of Int64.t
    | Temp of Temp.t
    | Binop of
        { lhs : Sexp.t
        ; op : binop
        ; rhs : Sexp.t
        }
    | BISD of Addr.t
  [@@deriving sexp, compare, hash]

  val pp : t -> string
  val pp_binop : binop -> string
  val to_t : t -> Temp.t
  val of_t : Temp.t -> t
  val of_int : Int64.t -> t
  val of_binop : binop -> Sexp.t -> Sexp.t -> t
  val of_void : unit -> t
  val of_bisd : Addr.t -> t
end = struct
  type t =
    | Void
    | Const of Int64.t
    | Temp of Temp.t
    | Binop of
        { lhs : Sexp.t
        ; op : binop
        ; rhs : Sexp.t
        }
    | BISD of Addr.t
  [@@deriving sexp, compare, hash] [@@warning "-37"]

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

  let pp exp =
    match exp with
    | Void -> "void"
    | Const x -> Int64.to_string x
    | Temp t -> Temp.name t
    | Binop binop ->
      Printf.sprintf
        "(%s %s %s)"
        (Sexp.pp binop.lhs)
        (pp_binop binop.op)
        (Sexp.pp binop.rhs)
    | BISD bisd -> Addr.pp bisd
  ;;

  let to_t exp =
    match exp with
    | Temp t -> t
    | _ -> failwith "expect temp"
  ;;

  let of_t (t : Temp.t) : t = Temp t
  let of_int (i : Int64.t) = Const i
  let of_binop op lhs rhs = Binop { op; lhs; rhs }
  let of_void () = Void
  let of_bisd (addr : Addr.t) = BISD addr
end [@warning "-37"]

and Sexp : sig
  include Var.Sized.Sized_Interface with type i = Exp.t

  val to_St : t -> St.t
end = struct
  include Var.Sized.Wrapper (Exp)

  let to_St (sexp : t) : St.t =
    let size = get_size_p sexp in
    let exp = get_data sexp in
    let t = Exp.to_t exp in
    St.wrap size t
  ;;
end

and St : sig
  include Var.Sized.Sized_Interface with type i = Temp.t

  val to_Sexp : t -> Sexp.t
end = struct
  include Var.Sized.Wrapper (Temp)

  let to_Sexp (st : t) : Sexp.t =
    let size = get_size_p st in
    let t = get_data st in
    let exp = Exp.of_t t in
    Sexp.wrap size exp
  ;;
end

module StMap = Map.Make (St)
module Mem : Var.Sized.Sized_Interface with type i = Addr.t = Var.Sized.Wrapper (Addr)

type stm =
  | Cast of
      { (* Do not generate new temporary. 
         * Only change the size of temporary. *)
        dest : St.t
      ; src : Sexp.t
      }
  | Move of
      { dest : St.t
      ; src : Sexp.t
      }
  | Effect of
      { dest : St.t
      ; lhs : Sexp.t
      ; op : binop
      ; rhs : Sexp.t
      }
  | Fcall of
      { dest : St.t option
      ; func_name : Symbol.t
      ; args : Sexp.t list
      }
  | Return of Sexp.t option
  | Jump of Label.t
  | CJump of
      { lhs : Sexp.t
      ; op : binop
      ; rhs : Sexp.t
      ; target_true : Label.t
      ; target_false : Label.t
      }
  | Label of Label.t
  | Nop
  | Assert of Sexp.t
  | Load of
      { src : Mem.t
      ; dest : St.t
      }
  | Store of
      { src : Sexp.t
      ; dest : Mem.t
      }

type fdefn =
  { func_name : Symbol.t
  ; temps : St.t list
  ; body : stm list
  }

type program = fdefn list
type t = stm
type st = St.t

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
  | Return _ -> true
  | _ -> false
;;

let is_raise = function
  | Fcall f -> if phys_equal f.func_name Symbol.Fname.raise then true else false
  | _ -> false
;;

let get_def = function
  | Cast cast -> [ cast.dest ]
  | Move move -> [ move.dest ]
  | Effect effect -> [ effect.dest ]
  | Fcall fcall ->
    (match fcall.dest with
    | None -> []
    | Some s -> [ s ])
  | Load load -> [ load.dest ]
  | Return _ | Jump _ | CJump _ | Label _ | Nop | Assert _ | Store _ -> []
;;

let rec _get_uses (sexp : Sexp.t) : St.t list =
  match sexp.data with
  | Void | Const _ -> []
  | Temp _ -> [ Sexp.to_St sexp ]
  | Binop binop -> _get_uses binop.lhs @ _get_uses binop.rhs
  | BISD bisd ->
    let base = _get_uses (Addr.get_base bisd) in
    let index =
      match Addr.get_index bisd with
      | None -> []
      | Some s -> _get_uses s
    in
    base @ index
;;

let get_uses = function
  | Cast cast -> _get_uses cast.src
  | Move move -> _get_uses move.src
  | Effect effect -> _get_uses effect.lhs @ _get_uses effect.rhs
  | Fcall fcall -> List.fold fcall.args ~init:[] ~f:(fun acc arg -> _get_uses arg @ acc)
  | Return ret ->
    (match ret with
    | None -> []
    | Some ret -> _get_uses ret)
  | CJump cjp -> _get_uses cjp.lhs @ _get_uses cjp.rhs
  | Assert asrt -> _get_uses asrt
  | Store store -> _get_uses store.src
  | Label _ | Jump _ | Load _ | Nop -> []
;;

let replace_def (instr : t) (dic : (st * st) list) : t =
  let dic = StMap.of_alist_exn dic in
  match instr with
  | Cast cast ->
    let dest_new = Map.find_exn dic cast.dest in
    Cast { cast with dest = dest_new }
  | Move move ->
    let dest_new = Map.find_exn dic move.dest in
    Move { move with dest = dest_new }
  | Effect effect ->
    let dest_new = Map.find_exn dic effect.dest in
    Effect { effect with dest = dest_new }
  | Fcall fcall ->
    (match fcall.dest with
    | None -> instr
    | Some dest ->
      let dest_new = Map.find_exn dic dest in
      Fcall { fcall with dest = Some dest_new })
  | Load load ->
    let dest_new = Map.find_exn dic load.dest in
    Load { load with dest = dest_new }
  | Return _ | Jump _ | CJump _ | Label _ | Nop | Assert _ | Store _ -> instr
;;

let rec _replace_uses (sexp : Sexp.t) (dic : St.t StMap.t) : Sexp.t =
  let size = sexp.size in
  match sexp.data with
  | Void | Const _ -> sexp
  | Temp _ ->
    let st = Sexp.to_St sexp in
    let st_ssa = StMap.find_exn dic st in
    St.to_Sexp st_ssa
  | Binop binop ->
    let lhs = _replace_uses binop.lhs dic in
    let rhs = _replace_uses binop.rhs dic in
    Sexp.wrap size (Binop { binop with lhs; rhs })
  | BISD bisd ->
    let base : Sexp.t = _replace_uses (Addr.get_base bisd) dic in
    let index =
      match Addr.get_index bisd with
      | None -> None
      | Some s -> Some (_replace_uses s dic)
    in
    let scale = Addr.get_scale bisd in
    let disp = Addr.get_disp bisd in
    Sexp.wrap size (BISD (Addr.of_bisd base index scale disp))
;;

let replace_uses (instr : t) (dic : (st * st) list) : t =
  let dic = StMap.of_alist_exn dic in
  match instr with
  | Cast cast ->
    let src = _replace_uses cast.src dic in
    Cast { cast with src }
  | Move move ->
    let src = _replace_uses move.src dic in
    Move { move with src }
  | Effect effect ->
    let lhs = _replace_uses effect.lhs dic in
    let rhs = _replace_uses effect.rhs dic in
    Effect { effect with lhs; rhs }
  | Fcall fcall ->
    let args = List.map fcall.args ~f:(fun arg -> _replace_uses arg dic) in
    Fcall { fcall with args }
  | Return ret ->
    (match ret with
    | None -> Return None
    | Some exp ->
      let exp = _replace_uses exp dic in
      Return (Some exp))
  | CJump cjp ->
    let lhs = _replace_uses cjp.lhs dic in
    let rhs = _replace_uses cjp.rhs dic in
    CJump { cjp with lhs; rhs }
  | Assert asrt ->
    let exp = _replace_uses asrt dic in
    Assert exp
  | Store store ->
    let src = _replace_uses store.src dic in
    Store { store with src }
  | Label _ | Jump _ | Load _ | Nop -> instr
;;

let[@warning "-27"] is_assert (i : stm) : bool = false
let label (l : Label.t) = Label l
let jump (target : Label.t) : stm = Jump target
let ret () : stm = Return None

let get_label (stm : stm) : Label.t =
  match stm with
  | Label l -> l
  | _ -> failwith "expect instr to be label"
;;

(* Given jump/conditional jump, return target label list. *)
let next (instr : stm) : Label.t list =
  match instr with
  | Jump jp -> [ jp ]
  | CJump cjp -> [ cjp.target_false; cjp.target_true ]
  | _ -> failwith "expect jump or cond jump"
;;

(* Replace target of Jump *)
let replace_target (instr : stm) (target : Label.t) : stm =
  match instr with
  | Jump _ -> Jump target
  | _ -> failwith "expect jump for taget"
;;

(* Replace old target to new target for CJump *)
let replace_ctarget (instr : stm) (old_target : Label.t) (new_target : Label.t) : stm =
  match instr with
  | CJump cjp ->
    if Label.equal cjp.target_false old_target
    then CJump { cjp with target_false = new_target }
    else if Label.equal cjp.target_true old_target
    then CJump { cjp with target_true = new_target }
    else failwith "old target do not match to cond jump"
  | _ -> failwith "expect cond jump to replace target"
;;

let sprintf = Printf.sprintf
let pp = Sexp.pp
let pp_mem = Mem.pp

let rec pp_inst = function
  | Cast cast -> "cast " ^ St.pp cast.dest ^ "  <--  " ^ pp cast.src
  | Move mv ->
    if Size.compare (Sexp.get_size mv.src) (St.get_size mv.dest) <> 0
    then failwith (sprintf "move size mismatch %s -> %s" (pp mv.src) (St.pp mv.dest));
    St.pp mv.dest ^ "  <--  " ^ pp mv.src
  | Effect eft ->
    sprintf
      "effect %s <- %s %s %s"
      (St.pp eft.dest)
      (pp eft.lhs)
      (Exp.pp_binop eft.op)
      (pp eft.rhs)
  | Fcall c ->
    let func_name = Symbol.name c.func_name in
    let args = List.map ~f:(fun arg -> pp arg) c.args |> String.concat ~sep:", " in
    (match c.dest with
    | Some dest ->
      let dest = St.pp dest in
      sprintf "%s <- %s(%s)" dest func_name args
    | None -> sprintf "%s(%s)" func_name args)
  | Return e ->
    (match e with
    | None -> "return"
    | Some e -> "return " ^ pp e)
  | Jump j -> "jump " ^ Label.name j
  | CJump cj ->
    sprintf
      "cjump(%s %s %s) target_true:%s, target_false %s "
      (pp cj.lhs)
      (Exp.pp_binop cj.op)
      (pp cj.rhs)
      (Label.name cj.target_true)
      (Label.name cj.target_false)
  | Label l -> Label.content l
  | Nop -> "nop"
  | Assert asrt -> sprintf "assert(%s)" (pp asrt)
  | Load ld -> sprintf "load %s <- %s" (St.pp ld.dest) (pp_mem ld.src)
  | Store st -> sprintf "store %s <- %s" (pp_mem st.dest) (pp st.src)

and pp_insts (stms : stm list) =
  List.map ~f:(fun stm -> pp_inst stm) stms |> String.concat ~sep:"\n"
;;

let pp_fdefn fdefn =
  let pars_str =
    List.map ~f:(fun temp -> St.pp temp) fdefn.temps |> String.concat ~sep:", "
  in
  let head, body =
    match fdefn.body with
    | [] -> failwith "expect func label"
    | h :: t -> h, t
  in
  sprintf "%s(%s)\n" (pp_inst head) pars_str ^ pp_insts body
;;

let pp_program program =
  List.map ~f:(fun fdefn -> pp_fdefn fdefn) program |> String.concat ~sep:"\n"
;;
