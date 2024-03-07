open Core
module Temp = Var.Temp
module Register = Var.X86_reg.Logic

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

let to_temp_exn (op : t) =
  match op with
  | Temp t -> t
  | _ -> failwith "expect temp"
;;

let to_reg_exn (op : t) =
  match op with
  | Reg t -> t
  | _ -> failwith "expect temp"
;;

let to_int_list (ops : t list) : int list =
  List.fold ops ~init:[] ~f:(fun acc x ->
      match x with
      | Temp t -> t.id :: acc
      | Reg r -> Register.get_idx r :: acc
      | Above_frame _ | Imm _ -> acc)
;;
