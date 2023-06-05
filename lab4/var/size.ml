(* Provide information for memory size.
 * This is used by memory and register to suit 
 * different size they may interest.  
 *)

type t =
  | BYTE
  | WORD
  | DWORD
  | QWORD

(* Return size of size in bit *)
let type_size_bit = function
  | BYTE -> 8
  | WORD -> 16
  | DWORD -> 32
  | QWORD -> 64
;;

(* Return size of size in byte *)
let type_size_byte = function
  | BYTE -> 1
  | WORD -> 2
  | DWORD -> 4
  | QWORD -> 8
;;
