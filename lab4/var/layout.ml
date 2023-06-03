(* Provide information for memory layout enumerate types.
 * This layout is used by memory and register to suit different size
 * they may interest.  
 *)

type layout =
  | BYTE
  | WORD
  | DWORD
  | QWORD

(* Return size of layout in bit *)
let type_size_bit (t : layout) =
  match t with
  | BYTE -> 8
  | WORD -> 16
  | DWORD -> 32
  | QWORD -> 64
;;

(* Return size of layout in byte *)
let type_size_byte (t : layout) =
  match t with
  | BYTE -> 1
  | WORD -> 2
  | DWORD -> 4
  | QWORD -> 8
;;
