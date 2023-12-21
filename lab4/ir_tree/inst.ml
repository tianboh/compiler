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

type 'a sized =
  { size : Size.primitive
  ; data : 'a
  }

type addr =
  { (* Syntax sugar for x86 memory access. Return: base + index * scale + disp *)
    base : sexp
  ; index : sexp option (* used by array and struct *)
  ; scale : sexp option
  ; disp : sexp option (* used by array *)
  }

and exp =
  | Void
  | Const of Int64.t
  (* DWORD for int32 from source code, QWORD for address calculation*)
  | Temp of Temp.t
  | Binop of
      { lhs : sexp
      ; op : binop
      ; rhs : sexp
      }
  | Addr of addr

and sexp = exp sized

type mem = addr sized

and stm =
  | Cast of
      { dest : Temp.t sized
      ; src : sexp
      }
  | Move of
      { dest : Temp.t sized
      ; src : sexp
      }
  | Effect of
      { dest : Temp.t sized
      ; lhs : sexp
      ; op : binop
      ; rhs : sexp
      }
  | Fcall of
      { dest : Temp.t sized option
      ; func_name : Symbol.t
      ; args : sexp list
      ; scope : [ `C0 | `External | `Internal ]
      }
  | Return of sexp option
  | Jump of Label.t
  | CJump of
      { (* Jump to target_true if lhs op rhs is true. 
         * Otherwise to target_false *)
        lhs : sexp
      ; op : binop
      ; rhs : sexp
      ; target_true : Label.t
      ; target_false : Label.t
      }
  | Label of Label.t
  | Nop
  | Assert of sexp
  | Load of
      { src : mem
      ; dest : Temp.t sized
      }
  | Store of
      { src : sexp
      ; dest : mem
      }

type fdefn =
  { func_name : Symbol.t
  ; temps : Temp.t sized list
  ; body : stm list
  ; scope : [ `Internal | `C0 ]
  }

type program = fdefn list

module type PRINT = sig
  val pp_sexp : sexp -> string
  val pp_stm : stm -> string
  val pp_stms : stm list -> string
  val pp_fdefn : fdefn -> string
  val pp_program : program -> string
end

module Print : PRINT = struct
  let sprintf = Printf.sprintf

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

  let rec pp_sexp (sexp : sexp) =
    match sexp.data with
    | Void -> "void"
    | Const x -> Int64.to_string x ^ "_" ^ Size.pp_size sexp.size
    | Temp t -> Temp.name' t sexp.size
    | Binop binop ->
      sprintf
        "(%s %s %s)_%s"
        (pp_sexp binop.lhs)
        (pp_binop binop.op)
        (pp_sexp binop.rhs)
        (Size.pp_size sexp.size)
    | Addr addr ->
      let mem : mem =
        { data =
            { base = addr.base; index = addr.index; scale = addr.scale; disp = addr.disp }
        ; size = sexp.size
        }
      in
      pp_mem mem

  (* mov (%esi,%ebx,4), %edx     	/* Move the 4 bytes of data at address ESI+4*EBX into EDX. *)
  and pp_mem (mem : mem) =
    let base = pp_sexp mem.data.base in
    let helper data =
      match data with
      | Some s -> pp_sexp s
      | None -> ""
    in
    let index = helper mem.data.index in
    let scale = helper mem.data.scale in
    sprintf "(%s, %s, %s)_%Ld" base index scale (Size.type_size_byte mem.size)

  and pp_stm = function
    | Cast cast ->
      "cast " ^ Temp.name' cast.dest.data cast.dest.size ^ "  <--  " ^ pp_sexp cast.src
    | Move mv ->
      if Size.compare (mv.src.size :> Size.t) (mv.dest.size :> Size.t) <> 0
      then
        failwith
          (sprintf
             "move size mismatch %s -> %s"
             (pp_sexp mv.src)
             (Temp.name' mv.dest.data mv.dest.size));
      Temp.name' mv.dest.data mv.dest.size ^ "  <--  " ^ pp_sexp mv.src
    | Effect eft ->
      sprintf
        "effect %s <- %s %s %s"
        (Temp.name' eft.dest.data eft.dest.size)
        (pp_sexp eft.lhs)
        (pp_binop eft.op)
        (pp_sexp eft.rhs)
    | Fcall c ->
      let scope = Symbol.pp_scope c.scope in
      let func_name = Symbol.name c.func_name in
      let args = List.map (fun arg -> pp_sexp arg) c.args |> String.concat ", " in
      (match c.dest with
      | Some dest ->
        let dest = Temp.name' dest.data dest.size in
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
        (pp_binop cj.op)
        (pp_sexp cj.rhs)
        (Label.name cj.target_true)
        (Label.name cj.target_false)
    | Label l -> Label.content l
    | Nop -> "nop"
    | Assert asrt -> sprintf "assert(%s)" (pp_sexp asrt)
    | Load ld ->
      sprintf "load %s <- %s" (Temp.name' ld.dest.data ld.dest.size) (pp_mem ld.src)
    | Store st -> sprintf "store %s <- %s" (pp_mem st.dest) (pp_sexp st.src)

  and pp_stms (stms : stm list) =
    List.map (fun stm -> pp_stm stm) stms |> String.concat "\n"
  ;;

  let pp_fdefn fdefn =
    let func_name = Symbol.pp_scope fdefn.scope ^ Symbol.name fdefn.func_name in
    let pars_str =
      List.map (fun temp -> Temp.name' temp.data temp.size) fdefn.temps
      |> String.concat ", "
    in
    sprintf "%s(%s)\n" func_name pars_str ^ pp_stms fdefn.body
  ;;

  let pp_program program =
    List.map (fun fdefn -> pp_fdefn fdefn) program |> String.concat "\n"
  ;;
end
