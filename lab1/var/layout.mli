
type layout = 
| BYTE
| WORD
| DWORD
| QWORD

val type_size : layout -> int