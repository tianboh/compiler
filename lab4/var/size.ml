(* Size for temporary. codegen will use this info to generate suitable
 * instructions for each operand.
 * void is a placeholder for result of void function return. *)
open Core

let ( * ) = Base.Int64.( * )

type primitive =
  [ `BYTE
  | `WORD
  | `DWORD
  | `QWORD
  ]
[@@deriving sexp, compare, hash]

type t =
  [ primitive
  | `CBYTE of Int64.t
  | `VOID
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

let pp_size = function
  | `VOID -> "void"
  | `BYTE -> "byte"
  | `WORD -> "word"
  | `DWORD -> "dword"
  | `QWORD -> "qword"
  | `CBYTE i -> Printf.sprintf "cbyte%Ld" i
;;
