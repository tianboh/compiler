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
  | `VOID -> Int64.of_int 0
  | `BYTE -> Int64.of_int 8
  | `WORD -> Int64.of_int 16
  | `DWORD -> Int64.of_int 32
  | `QWORD -> Int64.of_int 64
  | `CBYTE i -> i * Int64.of_int 8
;;

(* Return size of size in byte *)
let type_size_byte = function
  | `VOID -> Int64.of_int 0
  | `BYTE -> Int64.of_int 1
  | `WORD -> Int64.of_int 2
  | `DWORD -> Int64.of_int 4
  | `QWORD -> Int64.of_int 8
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

let compare (t1 : t) (t2 : t) =
  let s1 = type_size_byte t1 in
  let s2 = type_size_byte t2 in
  Int64.to_int_exn (s1 - s2)
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
