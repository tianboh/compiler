(* 
  L1 x86 assembly   
*)

open Core
module Register = Var.X86_reg

type operand =
  | Imm of Int32.t
  | Reg of Register.t

type instr =
  | Add of {src:operand; dest:operand}
  | Sub of {src:operand; dest:operand}
  | Mul of {src:operand} (* Destination is form of EDX:EAX by default. Only one operand required. *)
  | Div of {src:operand} (* temp := EDX:EAX / SRC;
                            IF temp > FFFFFFFFH
                                THEN #DE; (* Divide error *)
                            ELSE
                                EAX := temp;
                                EDX := EDX:EAX MOD SRC;
                            FI; *)
  | Mod of {src:operand} (* Similar as above, but use edx after div.*)
  | Mov of
      { dest : operand
      ; src : operand
      }
  | Cdq
  | Ret
  | Directive of string
  | Comment of string

(* functions that format assembly output *)


(* x <- x bin_op y *)
(* let format_binop = function
  | Add -> "addl"
  | Sub -> "subl"
  | Mul -> "mul"
  | Div -> "div"
  | Mod -> "div"
  | And -> "&&"
  | Or -> "||"
  | Pand -> "and"
  | Por -> "or"
  | Pxor -> "xor"
;; *)

let format_operand (oprd : operand) = match oprd with
  | Imm n -> "$" ^ Int32.to_string n
  | Reg r -> Register.reg_to_str r
  (* | _ -> failwith "not supported in x86 operand." *)
;;

let format = function
  (* It's quite tricky for the order of binary operand here. 
     dest <- dest(lhs_operand) bin_op rhs_operand equivalents to assembly code
     bin_op rhs_operand, dest
  *)
  | Add add -> sprintf "add %s, %s" (format_operand add.src) (format_operand add.dest)
  | Sub sub -> sprintf "sub %s, %s" (format_operand sub.src) (format_operand sub.dest)
  | Mul mul -> sprintf "mul %s" (format_operand mul.src)
  | Div div -> sprintf "idiv %s" (format_operand div.src)
  | Mod m -> sprintf "div %s" (format_operand m.src)
  | Cdq -> sprintf "cdq"
  (* | Binop binop ->
    sprintf
      "%s %s, %s"
      (format_binop binop.op)
      (format_operand binop.rhs)
      (format_operand (binop.dest:>[`Imm of int32 | `Reg of Register.t])) *)
  | Mov mv -> sprintf "movl %s, %s"  
                (format_operand mv.src) 
                (format_operand mv.dest)
  | Ret -> sprintf "ret"
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;
