

type reg = 
  | EAX
  | EBX
  | ECX
  | EDX
  | ESI
  | EDI
  | EBP
  | ESP
  | E8D
  | E9D
  | E10D
  | E11D
  | E12D
  | E13D
  | E14D
  | E15D


let reg_to_str = function
  | EAX  -> "%eax"
  | EBX  -> "%ebx"
  | ECX  -> "%ecx"
  | EDX  -> "%edx"
  | ESI  -> "%esi"
  | EDI  -> "%edi"
  | EBP  -> "%ebp"
  | ESP  -> "%esp"
  | E8D  -> "%e8d"
  | E9D  -> "%e9d"
  | E10D -> "%e10d"
  | E11D -> "%e11d"
  | E12D -> "%e12d"
  | E13D -> "%e13d"
  | E14D -> "%e14d"
  | E15D -> "%e15d"
;;

let str_to_reg = function
  | "%eax" -> EAX 
  | "%ebx" -> EBX 
  | "%ecx" -> ECX 
  | "%edx" -> EDX 
  | "%esi" -> ESI 
  | "%edi" -> EDI 
  | "%ebp" -> EBP 
  | "%esp" -> ESP 
  | "%e8d" -> E8D 
  | "%e9d" -> E9D 
  | "%e10d" -> E10D
  | "%e11d" -> E11D
  | "%e12d" -> E12D
  | "%e13d" -> E13D
  | "%e14d" -> E14D
  | "%e15d" -> E15D
  | _ -> EAX
;;

