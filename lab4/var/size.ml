(* Size for temporary. codegen will use this info to generate suitable
 * instructions for each operand.
 * void is a placeholder for result of void function return. *)

type t =
  | VOID
  | BYTE
  | WORD
  | DWORD
  | QWORD
[@@deriving sexp, compare, hash]

(* Return size of size in bit *)
let type_size_bit = function
  | VOID -> 0
  | BYTE -> 8
  | WORD -> 16
  | DWORD -> 32
  | QWORD -> 64
;;

(* Return size of size in byte *)
let type_size_byte = function
  | VOID -> 0
  | BYTE -> 1
  | WORD -> 2
  | DWORD -> 4
  | QWORD -> 8
;;
