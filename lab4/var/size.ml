(* Size for temporary. codegen will use this info to generate suitable
 * instructions for each operand.
 * void is a placeholder for result of void function return. *)
open Core

let ( * ) = Base.Int64.( * )
let ( - ) = Base.Int64.( - )

type primitive =
  [ `VOID
  | `BYTE
  | `WORD
  | `DWORD
  | `QWORD
  ]
[@@deriving sexp, compare, hash]

type t =
  [ primitive
  | `CBYTE of Int64.t
  ]
[@@deriving sexp, compare, hash]

(* Return size of size in bit *)
let type_size_bit = function
  | `VOID -> 0L
  | `BYTE -> 8L
  | `WORD -> 16L
  | `DWORD -> 32L
  | `QWORD -> 64L
  | `CBYTE i -> i * 8L
;;

(* Return size of size in byte *)
let type_size_byte = function
  | `VOID -> 0L
  | `BYTE -> 1L
  | `WORD -> 2L
  | `DWORD -> 4L
  | `QWORD -> 8L
  | `CBYTE i -> i
;;

let byte_to_size = function
  | 0L -> `VOID
  | 1L -> `BYTE
  | 2L -> `WORD
  | 4L -> `DWORD
  | 8L -> `QWORD
  | i -> `CBYTE i
;;

let compare (t1 : t) (t2 : t) : int =
  let s1 = type_size_byte t1 in
  let s2 = type_size_byte t2 in
  let ret = Int64.to_int_exn (s1 - s2) in
  ret
;;

let compare' (t1 : primitive) (t2 : primitive) : int =
  let s1 = type_size_byte t1 in
  let s2 = type_size_byte t2 in
  let ret = Int64.to_int_exn (s1 - s2) in
  ret
;;

let is_primitive (t : t) : bool =
  match t with
  | `CBYTE _ -> false
  | _ -> true
;;

let pp_size = function
  | `VOID -> "void"
  | `BYTE -> "byte"
  | `WORD -> "word"
  | `DWORD -> "dword"
  | `QWORD -> "qword"
  | `CBYTE i -> Printf.sprintf "cbyte%Ld" i
;;
