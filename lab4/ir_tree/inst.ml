(* L4 Compiler
 * IR Trees
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

module rec Addr : Var.Sized.Interface = struct
  type t =
    { (* Syntax sugar for x86 memory access. Return: base + index * scale + disp *)
      base : Sexp.t
    ; index : Sexp.t option (* used by array and struct *)
    ; scale : Sexp.t option
    ; disp : Sexp.t option (* used by array *)
    }

  let pp_exp (addr : t) =
    let base = Sexp.pp_sexp addr.base in
    let helper data =
      match data with
      | Some s -> Sexp.pp_sexp s
      | None -> ""
    in
    let index = helper addr.index in
    let scale = helper addr.scale in
    Printf.sprintf "(%s, %s, %s)" base index scale
  ;;
end

and Exp : sig
  include Var.Sized.Interface

  val pp_binop : binop -> string
end = struct
  type t =
    | Void
    | Const of Int64.t
    (* DWORD for int32 from source code, QWORD for address calculation*)
    | Temp of Temp.t
    | Binop of
        { lhs : Sexp.t
        ; op : binop
        ; rhs : Sexp.t
        }
    | BISD of Addr.t
  [@@warning "-37"]

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

  let pp_exp exp =
    match exp with
    | Void -> "void"
    | Const x -> Int64.to_string x
    | Temp t -> Temp.name t
    | Binop binop ->
      Printf.sprintf
        "(%s %s %s)"
        (Sexp.pp_sexp binop.lhs)
        (pp_binop binop.op)
        (Sexp.pp_sexp binop.rhs)
    | BISD bisd -> Addr.pp_exp bisd
  ;;
end [@warning "-37"]

and Sexp : (Var.Sized.Sized_Interface with type i = Exp.t) = Var.Sized.Wrapper (Exp)
and Mem : (Var.Sized.Sized_Interface with type i = Addr.t) = Var.Sized.Wrapper (Addr)

module St : Var.Sized.Sized_Interface with type i = Temp.t = Var.Sized.Wrapper (Temp)

type stm =
  | Cast of
      { dest : St.t
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
      ; scope : [ `C0 | `External | `Internal ]
      }
  | Return of Sexp.t option
  | Jump of Label.t
  | CJump of
      { (* Jump to target_true if lhs op rhs is true. 
         * Otherwise to target_false *)
        lhs : Sexp.t
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
  ; scope : [ `Internal | `C0 ]
  }

type program = fdefn list

module Print = struct
  let sprintf = Printf.sprintf
  let pp_sexp = Sexp.pp_sexp
  let pp_mem = Mem.pp_sexp

  let rec pp_stm = function
    | Cast cast -> "cast " ^ St.pp_sexp cast.dest ^ "  <--  " ^ pp_sexp cast.src
    | Move mv ->
      if Size.compare (Sexp.get_size mv.src) (St.get_size mv.dest) <> 0
      then
        failwith
          (sprintf "move size mismatch %s -> %s" (pp_sexp mv.src) (St.pp_sexp mv.dest));
      St.pp_sexp mv.dest ^ "  <--  " ^ pp_sexp mv.src
    | Effect eft ->
      sprintf
        "effect %s <- %s %s %s"
        (St.pp_sexp eft.dest)
        (pp_sexp eft.lhs)
        (Exp.pp_binop eft.op)
        (pp_sexp eft.rhs)
    | Fcall c ->
      let scope = Symbol.pp_scope c.scope in
      let func_name = Symbol.name c.func_name in
      let args = List.map (fun arg -> pp_sexp arg) c.args |> String.concat ", " in
      (match c.dest with
      | Some dest ->
        let dest = St.pp_sexp dest in
        sprintf "%s <- %s%s(%s)" dest scope func_name args
      | None -> sprintf "%s%s(%s)" scope func_name args)
    | Return e ->
      (match e with
      | None -> "return\n"
      | Some e -> "return " ^ pp_sexp e ^ "\n")
    | Jump j -> "jump " ^ Label.name j
    | CJump cj ->
      sprintf
        "cjump(%s %s %s) target_true:%s, target_false %s "
        (pp_sexp cj.lhs)
        (Exp.pp_binop cj.op)
        (pp_sexp cj.rhs)
        (Label.name cj.target_true)
        (Label.name cj.target_false)
    | Label l -> Label.content l
    | Nop -> "nop"
    | Assert asrt -> sprintf "assert(%s)" (pp_sexp asrt)
    | Load ld -> sprintf "load %s <- %s" (St.pp_sexp ld.dest) (pp_mem ld.src)
    | Store st -> sprintf "store %s <- %s" (pp_mem st.dest) (pp_sexp st.src)

  and pp_stms (stms : stm list) =
    List.map (fun stm -> pp_stm stm) stms |> String.concat "\n"
  ;;

  let pp_fdefn fdefn =
    let func_name = Symbol.pp_scope fdefn.scope ^ Symbol.name fdefn.func_name in
    let pars_str =
      List.map (fun temp -> St.pp_sexp temp) fdefn.temps |> String.concat ", "
    in
    sprintf "%s(%s)\n" func_name pars_str ^ pp_stms fdefn.body
  ;;

  let pp_program program =
    List.map (fun fdefn -> pp_fdefn fdefn) program |> String.concat "\n"
  ;;
end
