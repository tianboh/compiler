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

type exp =
  | Void
  | Const of
      { v : Int64.t
      ; size : [ `DWORD | `QWORD ]
      }
  (* DWORD for int32 from source code, QWORD for address calculation*)
  | Temp of Temp.t
  | Binop of
      { lhs : exp
      ; op : binop
      ; rhs : exp
      }

(* field of struct, element of array 
 * Never access large type directly. *)
type mem =
  { base : exp
  ; offset : exp option
  ; size : Size.primitive
  }

and stm =
  | Move of
      { dest : Temp.t
      ; src : exp
      }
  | Effect of
      { dest : Temp.t
      ; lhs : exp
      ; op : binop
      ; rhs : exp
      }
  | Fcall of
      { dest : Temp.t option
      ; func_name : Symbol.t
      ; args : exp list
      ; scope : [ `Internal | `External ]
      }
  | Return of exp option
  | Jump of Label.t
  | CJump of
      { (* Jump to target_true if lhs op rhs is true. 
         * Otherwise to target_false *)
        lhs : exp
      ; op : binop
      ; rhs : exp
      ; target_true : Label.t
      ; target_false : Label.t
      }
  | Label of Label.t
  | Nop
  | Assert of exp
  | Load of
      { src : mem
      ; dest : Temp.t
      }
  | Store of
      { src : exp
      ; dest : mem
      }

type fdefn =
  { func_name : Symbol.t
  ; temps : Temp.t list
  ; body : stm list
  }

type program = fdefn list

module type PRINT = sig
  val pp_exp : exp -> string
  val pp_stm : stm -> string
  val pp_stms : stm list -> string
  val pp_fdefn : fdefn -> string
  val pp_program : program -> string
end

module Print : PRINT = struct
  let sprintf = Printf.sprintf

  let pp_scope = function
    | `Internal -> "_c0_"
    | `External -> ""
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

  let rec pp_exp = function
    | Void -> "void"
    | Const x -> Int64.to_string x.v
    | Temp t -> Temp.name t
    | Binop binop ->
      sprintf "(%s %s %s)" (pp_exp binop.lhs) (pp_binop binop.op) (pp_exp binop.rhs)

  and pp_mem mem =
    let offset =
      match mem.offset with
      | Some offset -> pp_exp offset
      | None -> ""
    in
    sprintf "%s[%s]_%Ld" offset (pp_exp mem.base) (Size.type_size_byte mem.size)

  and pp_stm = function
    | Move mv -> Temp.name mv.dest ^ "  <--  " ^ pp_exp mv.src ^ "\n"
    | Effect eft ->
      sprintf
        "effect %s <- %s %s %s\n"
        (Temp.name eft.dest)
        (pp_exp eft.lhs)
        (pp_binop eft.op)
        (pp_exp eft.rhs)
    | Fcall c ->
      let scope = pp_scope c.scope in
      let func_name = Symbol.name c.func_name in
      let args = List.map (fun arg -> pp_exp arg) c.args |> String.concat ", " in
      (match c.dest with
      | Some dest ->
        let dest = Temp.name dest in
        sprintf "%s <- %s%s(%s)" dest scope func_name args
      | None -> sprintf "%s%s(%s)" scope func_name args)
    | Return e ->
      (match e with
      | None -> "return\n"
      | Some e -> "return " ^ pp_exp e ^ "\n")
    | Jump j -> "jump " ^ Label.name j ^ "\n"
    | CJump cj ->
      sprintf
        "cjump(%s %s %s) target_true:%s, target_false %s \n"
        (pp_exp cj.lhs)
        (pp_binop cj.op)
        (pp_exp cj.rhs)
        (Label.name cj.target_true)
        (Label.name cj.target_false)
    | Label l -> Label.content l ^ "\n"
    | Nop -> "nop" ^ "\n"
    | Assert asrt -> sprintf "assert(%s)\n" (pp_exp asrt)
    | Load ld -> sprintf "load %s <- %s" (Temp.name ld.dest) (pp_mem ld.src)
    | Store st -> sprintf "store %s <- %s" (pp_mem st.dest) (pp_exp st.src)

  and pp_stms (stms : stm list) =
    List.map (fun stm -> pp_stm stm) stms |> String.concat "\n"
  ;;

  let pp_fdefn fdefn =
    let func_name = Symbol.name fdefn.func_name in
    let pars_str =
      List.map (fun temp -> Temp.name temp) fdefn.temps |> String.concat ", "
    in
    sprintf "%s(%s)\n" func_name pars_str ^ pp_stms fdefn.body
  ;;

  let pp_program program =
    List.map (fun fdefn -> pp_fdefn fdefn) program |> String.concat "\n"
  ;;
end
