(* 
  L1 x86 assembly   
*)

open Core
module Register = Var.X86_reg
module Memory = Var.Memory

type operand =
  | Imm of Int32.t
  | Reg of Register.t
  | Mem of Memory.t

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

(* prologue for a callee function. Handle callee-saved registers and allocate space for local variables *)
let format_prologue (var_cnt : int) = 
  let var_size = var_cnt * 8 in
  let () = printf "%d" var_size in
  let insts = ["\tpush %rbp";
               "mov %rsp, %rbp";
               sprintf "sub $%d, %%rsp" var_size;
               ] in
  String.concat ~sep:"\n\t" insts
;;

(* epilogue for a callee function. Restore callee-saved registers and deallocate local variables. *)
let format_epilogue () = 
  let insts = ["mov %rbp, %rsp";
               "pop %rbp";
               "ret"] in
  String.concat ~sep:"\n\t" insts
;;

let format_operand (oprd : operand) = match oprd with
  | Imm n -> "$" ^ Int32.to_string n
  | Reg r -> Register.reg_to_str r
  | Mem m -> Memory.mem_to_str m
  (* | _ -> failwith "not supported in x86 operand." *)
;;

(* functions that format assembly output *)
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
  | Mov mv -> 
    (match mv.src, mv.dest with
    | (Imm _, Mem _) -> 
                sprintf "movl %s, %s"  
                (format_operand mv.src) 
                (format_operand mv.dest)
    | _ ->     sprintf "mov %s, %s"  
                (format_operand mv.src) 
                (format_operand mv.dest))
  | Ret -> format_epilogue ()
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;
