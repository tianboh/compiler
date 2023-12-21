(* L3 x86 assembly 
 * 
 * Provide function call based on l2
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
module Register = Var.X86_reg.Logic
module Memory = Var.Memory
module Label = Util.Label
module Symbol = Util.Symbol
module Size = Var.Size

type 'a sized =
  { data : 'a
  ; size : Size.primitive
  }

type operand_logic =
  | Imm of Int64.t
  | Reg of Register.t
  | Mem of Memory.t

type operand = operand_logic sized

type instr =
  | Add of
      { src : operand
      ; dest : operand
      ; size : Size.primitive
      }
  | Sub of
      { src : operand
      ; dest : operand
      ; size : Size.primitive
      }
  | Mul of
      { src : operand
      ; dest : operand
      ; size : Size.primitive
      } (* Destination is form of EDX:EAX by default. Only one operand required. *)
  | Div of
      { src : operand
      ; size : Size.primitive
      }
  (* temp := EDX:EAX / SRC;
            IF temp > FFFFFFFFH
                THEN #DE; (* Divide error *)
            ELSE
                EAX := temp;
                EDX := EDX:EAX MOD SRC;
            FI; *)
  | Mod of
      { src : operand
      ; size : Size.primitive
      } (* Similar as above, but use edx after div.*)
  | Cast of
      { dest : operand
      ; src : operand
      }
  | Mov of
      { dest : operand
      ; src : operand
      ; size : Size.primitive
            (* how many bytes to move from src. size <= dest.size; size <= src.size. *)
      }
  | Cvt of { size : Size.primitive } (*could be cdq, cqo, etc based on size it wants to extend. EDX:EAX := sign-extend of EAX *)
  | Ret
  | Pop of { var : operand }
  | Push of { var : operand }
  | Cmp of
      { lhs : operand
      ; rhs : operand
      ; size : Size.primitive
      }
  | LAHF (* Load: AH := flags SF ZF xx AF xx PF xx CF *)
  | SAHF (* Store AH into flags SF ZF xx AF xx PF xx CF *)
  | Label of Label.t
  | Jump of Label.t
  (* Conditional jump family *)
  | JE of Label.t (* Jump if equal, ZF = 1 *)
  | JNE of Label.t (* Jump if not equal, ZF = 0 *)
  | JL of Label.t (* Jump if less, <, SF <> OF *)
  | JLE of Label.t (* Jump if less or equal, <=, ZF = 1 or SF <> OF *)
  | JG of Label.t (* Jump if greater, >, ZF = 0 and SF = OF *)
  | JGE of Label.t (* Jump if greater or equal, >=, SF = OF *)
  (* SETCC family. Notice it can only set 8-bit operand to register, 
   * so it only works for %al, %bl, %cl and %dl. We use %al by default. *)
  | SETE of
      { (* Set byte if equal (ZF=1). size is a placeholder for dest,
         * it can only be BYTE *)
        dest : operand
      ; size : Size.primitive
      }
  | SETNE of
      { dest : operand
      ; size : Size.primitive
      }
  | SETL of
      { dest : operand
      ; size : Size.primitive
      }
  | SETLE of
      { dest : operand
      ; size : Size.primitive
      }
  | SETG of
      { dest : operand
      ; size : Size.primitive
      }
  | SETGE of
      { dest : operand
      ; size : Size.primitive
      }
  | AND of
      { (* bitwise and *)
        src : operand
      ; dest : operand
      ; size : Size.primitive
      }
  | OR of
      { (* bitwise and *)
        src : operand
      ; dest : operand
      ; size : Size.primitive
      }
  | XOR of
      { src : operand
      ; dest : operand
      ; size : Size.primitive
      }
  | SAL of
      { (* Inst size is same as dest. 
         * Immediate is 8bit, memory/register(%cl) is 16bit *)
        src : operand
      ; dest : operand
      ; size : Size.primitive
      }
  | SAR of
      { (* Inst size is same as dest. 
         * Immediate is 8bit, memory/register(%cl) is 16bit *)
        src : operand
      ; dest : operand
      ; size : Size.primitive
      }
  | Fcall of
      { func_name : Symbol.t
      ; scope : [ `C0 | `External | `Internal ]
      }
  | Abort
  | Fname of
      { name : string
      ; scope : [ `C0 | `External | `Internal ]
      }
  | GDB of string
  | Directive of string
  | Comment of string

type fdefn =
  { func_name : Symbol.t
  ; body : instr list
  }

type program = fdefn list

let get_size (operand : operand) : Size.primitive = operand.size

let pp_operand (oprd : operand) =
  match oprd.data with
  | Imm n -> "$" ^ Int64.to_string n
  | Reg r -> Register.reg_to_str' r oprd.size
  | Mem m -> Memory.mem_to_str m
;;

let pp_inst (size : Size.primitive) =
  match size with
  | `BYTE -> "b"
  | `WORD -> "w"
  | `DWORD -> "l"
  | `QWORD -> "q"
  | `VOID -> ""
;;

let pp_inst' (operand : operand) = pp_inst operand.size

let pp_scope = function
  | `C0 -> Symbol.c0_prefix
  | `External -> ""
  | `Internal -> "_"
;;

(* functions that format assembly output *)
let format = function
  (* We use AT&T x86 convention to generate x86 assembly code. *)
  | Add add ->
    sprintf "add%s %s, %s" (pp_inst add.size) (pp_operand add.src) (pp_operand add.dest)
  | Sub sub ->
    sprintf "sub%s %s, %s" (pp_inst sub.size) (pp_operand sub.src) (pp_operand sub.dest)
  | Mul mul ->
    sprintf "imul%s %s, %s" (pp_inst mul.size) (pp_operand mul.src) (pp_operand mul.dest)
  | Div div -> sprintf "idiv%s %s" (pp_inst div.size) (pp_operand div.src)
  | Mod m -> sprintf "div %s" (pp_operand m.src)
  | Cvt cvt ->
    (match cvt.size with
    | `VOID | `BYTE -> failwith "nothing to extend for byte/void"
    | `WORD -> "cwd"
    | `DWORD -> "cdq"
    | `QWORD -> "cqo")
  | Cast cast ->
    let src_str = pp_operand cast.src in
    let dest_str = pp_operand cast.dest in
    let dest_size = get_size cast.dest in
    let src_size = get_size cast.src in
    if Size.compare (src_size :> Size.t) (dest_size :> Size.t) = 0
    then failwith "cast oprd size match";
    if Size.compare (src_size :> Size.t) (dest_size :> Size.t) < 0
    then (
      match cast.dest.data with
      | Reg _ -> sprintf "movsxd %s, %s" src_str dest_str
      | Mem _ -> sprintf "mov%s %s, %s" (pp_inst src_size) src_str dest_str
      | _ -> failwith "cast dest illegal")
    else (
      let dest_str = pp_operand { cast.dest with size = cast.src.size } in
      sprintf "mov%s %s, %s" (pp_inst src_size) src_str dest_str)
  | Mov mv ->
    let src_str = pp_operand mv.src in
    let dest_str = pp_operand mv.dest in
    let () =
      if Size.compare (mv.src.size :> Size.t) (mv.dest.size :> Size.t) <> 0
      then
        printf
          "move oprd size mismatch mov%s %s, %s\n"
          (pp_inst mv.dest.size)
          src_str
          dest_str
      else ()
    in
    let size = get_size mv.dest in
    (match mv.src.data, mv.dest.data with
    | Imm _, _ | Mem _, _ | Reg _, Reg _ | Reg _, Mem _ ->
      sprintf "mov%s %s, %s" (pp_inst size) src_str dest_str
    | Reg _, Imm _ -> failwith "invalid move")
  | Ret -> "ret"
  | Push push ->
    (match push.var.data with
    | Reg r -> sprintf "push %s" (pp_operand { data = Reg r; size = `QWORD })
    | Mem m -> sprintf "push %s" (pp_operand { data = Mem m; size = `QWORD })
    | Imm i -> sprintf "push %s" (pp_operand { data = Imm i; size = `QWORD }))
  | Pop pop ->
    let oprd = { pop.var with size = `QWORD } in
    sprintf "pop %s" (pp_operand oprd)
  | Cmp cmp ->
    sprintf "cmp%s %s, %s" (pp_inst' cmp.lhs) (pp_operand cmp.rhs) (pp_operand cmp.lhs)
  | LAHF -> "lahf"
  | SAHF -> "sahf"
  | Label l -> Label.content l
  | Jump jp -> sprintf "jmp %s" (Label.name jp)
  | JE je -> sprintf "je %s" (Label.name je)
  | JNE jne -> sprintf "jne %s" (Label.name jne)
  | JL jl -> sprintf "jl %s" (Label.name jl)
  | JLE jle -> sprintf "jle %s" (Label.name jle)
  | JG jg -> sprintf "jg %s" (Label.name jg)
  | JGE jge -> sprintf "jge %s" (Label.name jge)
  | SETE sete -> sprintf "sete %s" (pp_operand sete.dest)
  | SETNE setne -> sprintf "setne %s" (pp_operand setne.dest)
  | SETL setl -> sprintf "setl %s" (pp_operand setl.dest)
  | SETLE setle -> sprintf "setle %s" (pp_operand setle.dest)
  | SETG setg -> sprintf "setg %s" (pp_operand setg.dest)
  | SETGE setge -> sprintf "setge %s" (pp_operand setge.dest)
  | AND a ->
    sprintf "and%s %s, %s" (pp_inst a.size) (pp_operand a.src) (pp_operand a.dest)
  | OR a -> sprintf "or%s %s, %s" (pp_inst a.size) (pp_operand a.src) (pp_operand a.dest)
  | XOR xor ->
    sprintf "xor%s %s, %s" (pp_inst' xor.dest) (pp_operand xor.src) (pp_operand xor.dest)
  | SAR sar ->
    sprintf "sar%s %s, %s" (pp_inst sar.size) (pp_operand sar.src) (pp_operand sar.dest)
  | SAL sal ->
    sprintf "sal%s %s, %s" (pp_inst sal.size) (pp_operand sal.src) (pp_operand sal.dest)
  | Fcall fcall ->
    sprintf "call %s%s" (pp_scope fcall.scope) (Symbol.name fcall.func_name)
  | Fname fname -> sprintf "%s%s:" (Symbol.pp_scope fname.scope) fname.name
  | Abort -> sprintf "call abort"
  | GDB gdb -> sprintf "%s" gdb
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;
