
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


val reg_to_str : reg -> string

val str_to_reg : string -> reg

