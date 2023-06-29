(* L3 Compiler
 * Assembly Code Generator for FAKE assembly
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Use a linear, not quadratic, algorithm.
 *
 * Implements a "convenient munch" algorithm
 * We provide 3 address pseudo and 2 address pseudo based on x86 architecture.
 * the way to convert from 3 address to 2 address is to use same X86_asm.operand for
 * Destination and first X86_asm.operand for binary operation. This makes sense because
 * Each binary op will copy the X86_asm.operand and then calculate. The copied X86_asm.operand will
 * never be used again after calculation. So we can safely store the result to the
 * X86_asm.operand.
 * Notice that for [a <- b + c, d <- b + c ] will not reuse temporary in b and c 
 * in the second execution. The assembly looks like
 * t1 <- some_value for b
 * t2 <- some_value for c
 * t3 <- t1
 * t4 <- t2
 * t5 <- t3 + t4
 * t6 <- t1
 * t7 <- t2
 * t8 <- t6 + t7
 * Therefore, we can reuse t3 as destination of t3 + t4 for x86 add inplace mechanism.
 *)
open Core
module Size = Var.Size
module Src = Abs_asm.Inst
module Register = Var.X86_reg.Logic
module X86_asm = Inst
module Temp = Var.Temp
module Reg = Var.X86_reg.Logic
module Memory = Var.Memory
module Label = Util.Label
module IG = Regalloc.Interference_graph
module Regalloc = Regalloc.Driver

let oprd_ps_to_x86
    (operand : Src.operand)
    (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    : X86_asm.operand
  =
  match operand with
  | Temp t ->
    let dest = IG.Vertex.Map.find_exn reg_alloc_info (IG.Vertex.T.Temp t) in
    (match dest with
    | Regalloc.Reg r -> X86_asm.Reg r
    | Regalloc.Mem m -> X86_asm.Mem m)
  | Imm i -> X86_asm.Imm i
  | Reg r -> X86_asm.Reg r
  (* af + 1 because rsp always point to the next available memory. 
   * The latest available memory is rsp + 8. Remember that caller push parameter and callee
   * push rbp, mov rsp to rbp so in order to access parameters in callee function, 
   * we need to skip the pushed rbp, which is 1. *)
  | Above_frame af -> X86_asm.Mem (Memory.above_frame Reg.RBP af.offset af.size)
  | Below_frame bf -> X86_asm.Mem (Memory.below_frame Reg.RSP bf.offset bf.size)
;;

let rax = Reg.RAX
let rdx = Reg.RDX
let rbp = Reg.RBP
let rsp = Reg.RSP
let fpe_label = Label.label (Some "fpe")
let abort_label = Label.label (Some "abt")
let shift_maximum_bit = Int32.of_int_exn 31 (* inclusive *)

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_mov (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Register.swap; size }; src = Mem src; size }
    ; X86_asm.Mov { dest = Mem dest; src = Reg { reg = Register.swap; size }; size }
    ]
  | _ -> [ Mov { dest; src; size } ]
;;

let safe_add (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Register.swap; size }; src = Mem src; size }
    ; X86_asm.Add { dest = Mem dest; src = Reg { reg = Register.swap; size }; size }
    ]
  | _ -> [ X86_asm.Add { dest; src; size } ]
;;

let safe_sub (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Register.swap; size }; src = Mem src; size }
    ; X86_asm.Sub { dest = Mem dest; src = Reg { reg = Register.swap; size }; size }
    ]
  | _ -> [ Sub { dest; src; size } ]
;;

let safe_and (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Register.swap; size }; src = Mem src; size }
    ; X86_asm.AND { dest = Mem dest; src = Reg { reg = Register.swap; size }; size }
    ]
  | _ -> [ AND { dest; src; size } ]
;;

let safe_or (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Register.swap; size }; src = Mem src; size }
    ; X86_asm.OR { dest = Mem dest; src = Reg { reg = Register.swap; size }; size }
    ]
  | _ -> [ OR { dest; src; size } ]
;;

let safe_xor (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Register.swap; size }; src = Mem src; size }
    ; X86_asm.XOR { dest = Mem dest; src = Reg { reg = Register.swap; size }; size }
    ]
  | _ -> [ XOR { dest; src; size } ]
;;

(* shift bit should be [0, 31] *)
let shift_check (shift_bit : X86_asm.operand) (fpe_label : Label.t) =
  [ X86_asm.Cmp { lhs = shift_bit; rhs = Imm shift_maximum_bit; size = DWORD }
  ; X86_asm.JG fpe_label
  ; X86_asm.Cmp { lhs = shift_bit; rhs = Imm Int32.zero; size = DWORD }
  ; X86_asm.JL fpe_label
  ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sal
    (dest : X86_asm.operand)
    (src : X86_asm.operand)
    (size : Size.primitive)
    (fpe_label : Label.t)
  =
  match src with
  | Reg _ | Mem _ ->
    let ecx = Register.RCX in
    (* when src is register/memory, SAL can only use %cl to shift. *)
    (X86_asm.Mov { dest = Reg { reg = ecx; size }; src; size }
    :: shift_check (Reg { reg = ecx; size }) fpe_label)
    @ [ SAL { dest; src = Reg { reg = ecx; size = BYTE }; size } ]
  | Imm _ ->
    shift_check src fpe_label
    @ [ SAL { dest; src = Inst.set_size src BYTE; size = BYTE } ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sar
    (dest : X86_asm.operand)
    (src : X86_asm.operand)
    (size : Size.primitive)
    (fpe_label : Label.t)
  =
  match src with
  | Reg _ | Mem _ ->
    let ecx = Register.RCX in
    (* when src is register/memory, SAR can only use %cl to shift. *)
    (X86_asm.Mov { dest = Reg { reg = ecx; size }; src; size }
    :: shift_check (Reg { reg = ecx; size }) fpe_label)
    @ [ SAR { dest; src = Reg { reg = ecx; size = BYTE }; size } ]
  | Imm _ -> shift_check src fpe_label @ [ SAR { dest; src; size = BYTE } ]
;;

let safe_ret (size : Size.primitive) =
  (* insts = [ "mov %rbp, %rsp"; "pop %rbp"; "ret" ] *)
  [ X86_asm.Mov { dest = Reg { reg = rsp; size }; src = Reg { reg = rbp; size }; size }
  ; X86_asm.Pop { var = Reg { reg = rbp; size }; size }
  ; X86_asm.Ret
  ]
;;

(* Prepare for conditional jump. *)
let safe_cmp
    (lhs : X86_asm.operand)
    (rhs : X86_asm.operand)
    (size : Size.primitive)
    (swap : X86_asm.operand)
  =
  match lhs, rhs with
  | Mem _, Mem _ ->
    [ X86_asm.Mov { dest = swap; src = lhs; size }
    ; X86_asm.Cmp { lhs = swap; rhs; size }
    ]
  | _ -> [ X86_asm.Cmp { lhs; rhs; size } ]
;;

let gen_x86_relop_bin
    (op : Src.bin_op)
    (dest : X86_asm.operand)
    (lhs : X86_asm.operand)
    (rhs : X86_asm.operand)
    (swap : X86_asm.operand)
  =
  let al = X86_asm.Reg { reg = rax; size = BYTE } in
  let rax = X86_asm.Reg { reg = rax; size = QWORD } in
  let set_inst =
    match op with
    | Less -> [ X86_asm.SETL { dest = al; size = BYTE } ]
    | Less_eq -> [ X86_asm.SETLE { dest = al; size = BYTE } ]
    | Greater -> [ X86_asm.SETG { dest = al; size = BYTE } ]
    | Greater_eq -> [ X86_asm.SETGE { dest = al; size = BYTE } ]
    | Equal_eq -> [ X86_asm.SETE { dest = al; size = BYTE } ]
    | Not_eq -> [ X86_asm.SETNE { dest = al; size = BYTE } ]
    | _ -> failwith "relop cannot handle other op"
  in
  let cmp_inst = safe_cmp lhs rhs DWORD swap in
  [ X86_asm.XOR { dest = rax; src = rax; size = DWORD } ]
  @ cmp_inst
  @ set_inst
  @ [ X86_asm.Mov { dest; src = Inst.set_size rax (Inst.get_size dest); size = DWORD } ]
;;

let gen_x86_inst_bin
    (op : Src.bin_op)
    (dest : X86_asm.operand)
    (lhs : X86_asm.operand)
    (rhs : X86_asm.operand)
    (swap : Reg.t)
  =
  let rax = X86_asm.Reg { reg = rax; size = DWORD } in
  let swap = X86_asm.Reg { reg = swap; size = DWORD } in
  match op with
  | Plus -> safe_mov dest lhs DWORD @ safe_add dest rhs DWORD
  | Minus -> safe_mov dest lhs DWORD @ safe_sub dest rhs DWORD
  | Times ->
    [ X86_asm.Mov { dest = rax; src = lhs; size = DWORD }
    ; X86_asm.Mul { src = rhs; dest = rax; size = DWORD }
    ; X86_asm.Mov { dest; src = rax; size = DWORD }
    ]
  | Divided_by ->
    (* Notice that lhs and rhs may be allocated on rdx. 
     * So we use reg_swap to avoid override in the rdx <- 0. *)
    [ X86_asm.Mov { dest = rax; src = lhs; size = DWORD }
    ; X86_asm.Mov { dest = swap; src = rhs; size = DWORD }
    ; X86_asm.Cvt { size = DWORD }
    ; X86_asm.Div { src = swap; size = DWORD }
    ; X86_asm.Mov { dest; src = rax; size = DWORD }
    ]
  | Modulo ->
    [ X86_asm.Mov { dest = rax; src = lhs; size = DWORD }
    ; X86_asm.Mov { dest = swap; src = rhs; size = DWORD }
    ; X86_asm.Cvt { size = DWORD }
    ; X86_asm.Div { src = swap; size = DWORD }
    ; X86_asm.Mov { dest; src = Reg { reg = rdx; size = DWORD }; size = DWORD }
    ]
  | And -> safe_mov dest lhs DWORD @ safe_and dest rhs DWORD
  | Or -> safe_mov dest lhs DWORD @ safe_or dest rhs DWORD
  | Xor -> safe_mov dest lhs DWORD @ safe_xor dest rhs DWORD
  | Right_shift -> safe_mov dest lhs DWORD @ safe_sar dest rhs DWORD fpe_label
  | Left_shift -> safe_mov dest lhs DWORD @ safe_sal dest rhs DWORD fpe_label
  | Less | Less_eq | Greater | Greater_eq | Equal_eq | Not_eq ->
    gen_x86_relop_bin op dest lhs rhs swap
;;

let rec _codegen_w_reg_rev
    (res : X86_asm.instr list)
    (inst_list : Src.instr list)
    (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    (reg_swap : Reg.t)
  =
  match inst_list with
  | [] -> res
  | h :: t ->
    (* let () = printf "%s\n" (Src.format h) in *)
    (match h with
    | Src.Binop bin_op ->
      let dest = oprd_ps_to_x86 bin_op.dest reg_alloc_info in
      let lhs = oprd_ps_to_x86 bin_op.lhs reg_alloc_info in
      let rhs = oprd_ps_to_x86 bin_op.rhs reg_alloc_info in
      let insts = gen_x86_inst_bin bin_op.op dest lhs rhs reg_swap in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Src.Mov mov ->
      let dest = oprd_ps_to_x86 mov.dest reg_alloc_info in
      let src = oprd_ps_to_x86 mov.src reg_alloc_info in
      let insts = safe_mov dest src DWORD in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Src.Ret _ ->
      let insts = safe_ret QWORD in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Src.Label l ->
      _codegen_w_reg_rev (X86_asm.Label l.label :: res) t reg_alloc_info reg_swap
    | Src.Jump jp ->
      _codegen_w_reg_rev (X86_asm.Jump jp.target :: res) t reg_alloc_info reg_swap
    | Src.CJump cjp ->
      let lhs = oprd_ps_to_x86 cjp.lhs reg_alloc_info in
      let rhs = oprd_ps_to_x86 cjp.rhs reg_alloc_info in
      let target_true = cjp.target_true in
      let target_false = cjp.target_false in
      let cmp_inst =
        safe_cmp lhs rhs DWORD (X86_asm.Reg { reg = reg_swap; size = DWORD })
      in
      let cmp_inst_rev = List.rev cmp_inst in
      let cjp_inst =
        match cjp.op with
        | Equal_eq -> X86_asm.JE target_true
        | Greater -> X86_asm.JG target_true
        | Greater_eq -> X86_asm.JGE target_true
        | Less -> X86_asm.JL target_true
        | Less_eq -> X86_asm.JLE target_true
        | Not_eq -> X86_asm.JNE target_true
        | _ -> failwith "conditional jump op should can only be relop."
      in
      let jp = X86_asm.Jump target_false in
      _codegen_w_reg_rev
        (([ jp; cjp_inst ] @ cmp_inst_rev) @ res)
        t
        reg_alloc_info
        reg_swap
    | Src.Push push ->
      let var = oprd_ps_to_x86 push.var reg_alloc_info in
      let inst_rev = X86_asm.Push { var; size = QWORD } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | Src.Pop pop ->
      let var = oprd_ps_to_x86 pop.var reg_alloc_info in
      let inst_rev = X86_asm.Pop { var; size = QWORD } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | Src.Fcall fcall ->
      let scope = fcall.scope in
      let func_name = fcall.func_name in
      let inst = X86_asm.Fcall { func_name; scope } in
      _codegen_w_reg_rev (inst :: res) t reg_alloc_info reg_swap
    | Src.Assert ast ->
      let var = oprd_ps_to_x86 ast.var reg_alloc_info in
      let insts_rev =
        [ X86_asm.Cmp { lhs = var; rhs = X86_asm.Imm Int32.one; size = QWORD }
        ; X86_asm.JNE abort_label
        ]
        |> List.rev
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | _ -> _codegen_w_reg_rev res t reg_alloc_info reg_swap)
;;

let fpe_handler =
  let ecx = X86_asm.Reg { reg = RCX; size = DWORD } in
  (* We use ecx as zero reg because it is saved for shift. *)
  [ X86_asm.Label fpe_label
  ; X86_asm.Mov { dest = ecx; src = Imm Int32.zero; size = DWORD }
  ; X86_asm.Div { src = ecx; size = DWORD }
  ]
;;

let abort_handler = [ X86_asm.Label abort_label; X86_asm.Abort ]

let gen (fdefn : Src.fdefn) (reg_alloc_info : (IG.Vertex.t * Regalloc.dest) option list)
    : X86_asm.instr list
  =
  let reg_alloc =
    List.fold reg_alloc_info ~init:IG.Vertex.Map.empty ~f:(fun acc x ->
        match x with
        | None -> acc
        | Some x ->
          (match x with
          | temp, reg -> IG.Vertex.Map.set acc ~key:temp ~data:reg))
  in
  let reg_swap = Reg.R15 in
  let res_rev = _codegen_w_reg_rev [] fdefn.body reg_alloc reg_swap in
  let res = List.rev res_rev in
  let mem_cnt = Int32.of_int_exn (8 * Memory.get_allocated_count ()) in
  (* store rbp and rsp at the beginning of each function *)
  let rbp = X86_asm.Reg { reg = rbp; size = QWORD } in
  let rsp = X86_asm.Reg { reg = rsp; size = QWORD } in
  [ X86_asm.Fname fdefn.func_name
  ; X86_asm.Push { var = rbp; size = QWORD }
  ; X86_asm.Mov { dest = rbp; src = rsp; size = QWORD }
  ; X86_asm.Sub { src = X86_asm.Imm mem_cnt; dest = rsp; size = QWORD }
  ]
  @ res
;;
