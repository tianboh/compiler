(* Provide information for memory layout enumerate types.
 * This layout is used by memory and register to suit different size
 * they may interest.  
*)

type layout = 
| BYTE
| WORD
| DWORD
| QWORD

(* Return size of layout *)
let type_size (t : layout) = match t with
| BYTE -> 8
| WORD -> 16
| DWORD -> 32
| QWORD -> 64

