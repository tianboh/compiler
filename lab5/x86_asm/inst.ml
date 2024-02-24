(* L4 x86 assembly 
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
module Register = Var.X86_reg.Logic
module Label = Util.Label
module Symbol = Util.Symbol
module Size = Var.Size
module Addr = Var.Addr.Wrapper (Var.X86_reg.Hard)

module Op = struct
  type t =
    | Imm of Int64.t
    | Reg of Register.t
    | Addr of Addr.t
    (* Stack memory do not appear in the eventual program *)
    | Stack of
        { index : Int64.t
        ; reg : Register.t
        }
  [@@deriving sexp, compare, hash]

  let pp = function
    | Imm i -> Int64.to_string i
    | Reg r -> Register.pp r
    | Addr addr -> Addr.pp addr
    | Stack s -> sprintf "(%s, %Ld, 8)" (Register.reg_to_str' s.reg `QWORD) s.index
  ;;

  let of_imm i = Imm i
  let of_reg r = Reg r
  let of_addr b i s d = Addr (Addr.of_bisd b i s d)
  let of_stack reg index = Stack { index; reg }
end

module Sop = Var.Sized.Wrapper (Op)

module Mem = struct
  include Var.Sized.Wrapper (Addr)

  let to_Sop mem =
    let b, i, s, d = Addr.get mem.data in
    let size = mem.size in
    let addr = Op.of_addr b i s d in
    Sop.wrap size addr
  ;;
end

type instr =
  | Add of
      { src : Sop.t
      ; dest : Sop.t
      ; size : Size.primitive
      }
  | Sub of
      { src : Sop.t
      ; dest : Sop.t
      ; size : Size.primitive
      }
  | Mul of
      { src : Sop.t
      ; dest : Sop.t
      ; size : Size.primitive
      } (* Destination is form of EDX:EAX by default. Only one Sop.t required. *)
  | Div of
      { src : Sop.t
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
      { src : Sop.t
      ; size : Size.primitive
      } (* Similar as above, but use edx after div.*)
  | Cast of
      { dest : Sop.t
      ; src : Sop.t
      }
  | Mov of
      { dest : Sop.t
      ; src : Sop.t
      ; size : Size.primitive
            (* how many bytes to move from src. size <= dest.size; size <= src.size. *)
      }
  | Cvt of { size : Size.primitive } (*could be cdq, cqo, etc based on size it wants to extend. EDX:EAX := sign-extend of EAX *)
  | Ret
  | Pop of { var : Sop.t }
  | Push of { var : Sop.t }
  | Cmp of
      { lhs : Sop.t
      ; rhs : Sop.t
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
  (* SETCC family. Notice it can only set 8-bit Sop.t to register, 
   * so it only works for %al, %bl, %cl and %dl. We use %al by default. *)
  | SETE of
      { (* Set byte if equal (ZF=1). size is a placeholder for dest,
         * it can only be BYTE *)
        dest : Sop.t
      ; size : Size.primitive
      }
  | SETNE of
      { dest : Sop.t
      ; size : Size.primitive
      }
  | SETL of
      { dest : Sop.t
      ; size : Size.primitive
      }
  | SETLE of
      { dest : Sop.t
      ; size : Size.primitive
      }
  | SETG of
      { dest : Sop.t
      ; size : Size.primitive
      }
  | SETGE of
      { dest : Sop.t
      ; size : Size.primitive
      }
  | AND of
      { (* bitwise and *)
        src : Sop.t
      ; dest : Sop.t
      ; size : Size.primitive
      }
  | OR of
      { (* bitwise and *)
        src : Sop.t
      ; dest : Sop.t
      ; size : Size.primitive
      }
  | XOR of
      { src : Sop.t
      ; dest : Sop.t
      ; size : Size.primitive
      }
  | SAL of
      { (* Inst size is same as dest. 
         * Immediate is 8bit, Mem/register(%cl) is 16bit *)
        src : Sop.t
      ; dest : Sop.t
      ; size : Size.primitive
      }
  | SAR of
      { (* Inst size is same as dest. 
         * Immediate is 8bit, Mem/register(%cl) is 16bit *)
        src : Sop.t
      ; dest : Sop.t
      ; size : Size.primitive
      }
  | Fcall of { func_name : Symbol.t }
  | Abort
  | Fname of { name : string }
  | GDB of string
  | Directive of string
  | Comment of string

type fdefn =
  { func_name : Symbol.t
  ; body : instr list
  }

type program = fdefn list

let pp_Sop (oprd : Sop.t) =
  match oprd.data with
  | Op.Imm n -> "$" ^ Int64.to_string n
  | Op.Reg r -> Register.reg_to_str' r oprd.size
  | Op.Addr addr -> Addr.pp addr
  | Op.Stack s -> Op.pp (Op.Stack s)
;;

let pp_inst (size : Size.primitive) =
  match size with
  | `BYTE -> "b"
  | `WORD -> "w"
  | `DWORD -> "l"
  | `QWORD -> "q"
  | `VOID -> ""
;;

let pp_inst' (operand : Sop.t) = pp_inst operand.size

(* functions that format assembly output *)
let format = function
  (* We use AT&T x86 convention to generate x86 assembly code. *)
  | Add add ->
    sprintf "add%s %s, %s" (pp_inst add.size) (pp_Sop add.src) (pp_Sop add.dest)
  | Sub sub ->
    sprintf "sub%s %s, %s" (pp_inst sub.size) (pp_Sop sub.src) (pp_Sop sub.dest)
  | Mul mul ->
    sprintf "imul%s %s, %s" (pp_inst mul.size) (pp_Sop mul.src) (pp_Sop mul.dest)
  | Div div -> sprintf "idiv%s %s" (pp_inst div.size) (pp_Sop div.src)
  | Mod m -> sprintf "div %s" (pp_Sop m.src)
  | Cvt cvt ->
    (match cvt.size with
    | `VOID | `BYTE -> failwith "nothing to extend for byte/void"
    | `WORD -> "cwd"
    | `DWORD -> "cdq"
    | `QWORD -> "cqo")
  | Cast cast ->
    let src_str = pp_Sop cast.src in
    let dest_str = pp_Sop cast.dest in
    let dest_size = cast.dest.size in
    let src_size = cast.src.size in
    if Size.compare (src_size :> Size.t) (dest_size :> Size.t) = 0
    then failwith "cast oprd size match";
    if Size.compare (src_size :> Size.t) (dest_size :> Size.t) < 0
    then (
      match cast.dest.data with
      | Op.Reg _ -> sprintf "movsxd %s, %s" src_str dest_str
      | Op.Addr _ -> sprintf "mov%s %s, %s" (pp_inst src_size) src_str dest_str
      | _ -> failwith "cast dest illegal")
    else (
      let dest_str = pp_Sop { cast.dest with size = cast.src.size } in
      sprintf "mov%s %s, %s" (pp_inst src_size) src_str dest_str)
  | Mov mv ->
    let src_str = pp_Sop mv.src in
    let dest_str = pp_Sop mv.dest in
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
    let size = mv.dest.size in
    (match mv.src.data, mv.dest.data with
    | Imm _, _ | Addr _, _ | Reg _, Reg _ | Reg _, Addr _ ->
      sprintf "mov%s %s, %s" (pp_inst size) src_str dest_str
    | Reg _, Imm _ -> failwith "invalid move"
    | _ -> failwith "stack memory should not appear in the program")
  | Ret -> "ret"
  | Push push ->
    (match push.var.data with
    | Reg r -> sprintf "push %s" (pp_Sop { data = Reg r; size = `QWORD })
    | Addr m -> sprintf "push %s" (pp_Sop { data = Addr m; size = `QWORD })
    | Imm i -> sprintf "push %s" (pp_Sop { data = Imm i; size = `QWORD })
    | Stack _ -> failwith "stack memory do not appear in the program")
  | Pop pop ->
    let oprd = { pop.var with size = `QWORD } in
    sprintf "pop %s" (pp_Sop oprd)
  | Cmp cmp -> sprintf "cmp%s %s, %s" (pp_inst' cmp.lhs) (pp_Sop cmp.rhs) (pp_Sop cmp.lhs)
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
  | SETE sete -> sprintf "sete %s" (pp_Sop sete.dest)
  | SETNE setne -> sprintf "setne %s" (pp_Sop setne.dest)
  | SETL setl -> sprintf "setl %s" (pp_Sop setl.dest)
  | SETLE setle -> sprintf "setle %s" (pp_Sop setle.dest)
  | SETG setg -> sprintf "setg %s" (pp_Sop setg.dest)
  | SETGE setge -> sprintf "setge %s" (pp_Sop setge.dest)
  | AND a -> sprintf "and%s %s, %s" (pp_inst a.size) (pp_Sop a.src) (pp_Sop a.dest)
  | OR a -> sprintf "or%s %s, %s" (pp_inst a.size) (pp_Sop a.src) (pp_Sop a.dest)
  | XOR xor ->
    sprintf "xor%s %s, %s" (pp_inst' xor.dest) (pp_Sop xor.src) (pp_Sop xor.dest)
  | SAR sar ->
    sprintf "sar%s %s, %s" (pp_inst sar.size) (pp_Sop sar.src) (pp_Sop sar.dest)
  | SAL sal ->
    sprintf "sal%s %s, %s" (pp_inst sal.size) (pp_Sop sal.src) (pp_Sop sal.dest)
  | Fcall fcall -> sprintf "call %s" (Symbol.name fcall.func_name)
  | Fname fname -> sprintf "%s:" fname.name
  | Abort -> sprintf "call abort"
  | GDB gdb -> sprintf "%s" gdb
  | Directive dir -> sprintf "%s" dir
  | Comment comment -> sprintf "/* %s */" comment
;;
