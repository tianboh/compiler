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
 * the way to convert from 3 address to 2 address is to use same operand for
 * Destination and first operand for binary operation. This makes sense because
 * Each binary op will copy the operand and then calculate. The copied operand will
 * never be used again after calculation. So we can safely store the result to the
 * operand.
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
open Var.Size
module Abs_asm = Abs_asm.Inst
module X86_asm = Inst
module Temp = Var.Temp
module Reg = Var.X86_reg
module Memory = Var.Memory
module Label = Util.Label
module IG = Regalloc.Interference_graph
module Regalloc = Regalloc.Driver

let oprd_ps_to_x86
    (operand : Abs_asm.operand)
    (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    : X86_asm.operand
  =
  match operand with
  | Temp t ->
    let dest =
      match IG.Vertex.Map.find reg_alloc_info (IG.Vertex.T.Temp t) with
      | Some s -> s
      | None ->
        (* Some variable that is only declared but not defined during the whole program. 
         * For example: int a; and no assignment afterwards.
         * In this case, we will use %rax to represent it. Notice that it is only a representation
         * for this uninitialized temporary, and %rax will not be assigned in the following instruction.
         * Therefore, no worry for the return value. *)
        Regalloc.Reg Reg.RAX
    in
    (match dest with
    | Regalloc.Reg r -> X86_asm.Reg r
    | Regalloc.Mem m -> X86_asm.Mem m)
  | Imm i -> X86_asm.Imm i
  | Reg r -> X86_asm.Reg r
  (* af + 1 because rsp always point to the next available memory. 
   * The latest available memory is rsp + 8. Remember that caller push parameter and callee
   * push rbp, mov rsp to rbp so in order to access parameters in callee function, 
   * we need to skip the pushed rbp, which is 1. *)
  | Above_frame af -> X86_asm.Mem (Memory.get_mem Reg.RBP (af + 1) QWORD)
  | Below_frame bf -> X86_asm.Mem (Memory.get_mem Reg.RSP (-bf) DWORD)
;;

let trans_scope = function
  | Abs_asm.Internal -> X86_asm.Internal
  | Abs_asm.External -> X86_asm.External
;;

let rax = X86_asm.Reg Reg.RAX
let rdx = X86_asm.Reg Reg.RDX
let rbp = X86_asm.Reg Reg.RBP
let rsp = X86_asm.Reg Reg.RSP
let fpe_label = Label.label (Some "fpe")
let abort_label = Label.label (Some "abt")

let gen_x86_relop_bin
    (op : Abs_asm.bin_op)
    (dest : X86_asm.operand)
    (lhs : X86_asm.operand)
    (rhs : X86_asm.operand)
    (swap : Reg.t)
  =
  let set_inst =
    match op with
    | Less -> [ X86_asm.SETL { dest = rax; size = BYTE } ]
    | Less_eq -> [ X86_asm.SETLE { dest = rax; size = BYTE } ]
    | Greater -> [ X86_asm.SETG { dest = rax; size = BYTE } ]
    | Greater_eq -> [ X86_asm.SETGE { dest = rax; size = BYTE } ]
    | Equal_eq -> [ X86_asm.SETE { dest = rax; size = BYTE } ]
    | Not_eq -> [ X86_asm.SETNE { dest = rax; size = BYTE } ]
    | _ -> failwith "relop cannot handle other op"
  in
  let cmp_inst = X86_asm.safe_cmp lhs rhs DWORD swap in
  [ X86_asm.XOR { dest = rax; src = rax; size = DWORD } ]
  @ cmp_inst
  @ set_inst
  @ [ X86_asm.Mov { dest; src = rax; size = DWORD } ]
;;

let gen_x86_inst_bin
    (op : Abs_asm.bin_op)
    (dest : X86_asm.operand)
    (lhs : X86_asm.operand)
    (rhs : X86_asm.operand)
    (swap : Reg.t)
  =
  match op with
  | Plus -> X86_asm.safe_mov dest lhs DWORD @ X86_asm.safe_add dest rhs DWORD
  | Minus -> X86_asm.safe_mov dest lhs DWORD @ X86_asm.safe_sub dest rhs DWORD
  | Times ->
    [ X86_asm.Mov { dest = rax; src = lhs; size = DWORD }
    ; X86_asm.Mul { src = rhs; dest = rax; size = DWORD }
    ; X86_asm.Mov { dest; src = rax; size = DWORD }
    ]
  | Divided_by ->
    (* Notice that lhs and rhs may be allocated on rdx. 
     * So we use reg_swap to avoid override in the rdx <- 0. *)
    [ X86_asm.Mov { dest = rax; src = lhs; size = DWORD }
    ; X86_asm.Mov { dest = X86_asm.Reg swap; src = rhs; size = DWORD }
    ; X86_asm.Cvt { size = DWORD }
    ; X86_asm.Div { src = X86_asm.Reg swap; size = DWORD }
    ; X86_asm.Mov { dest; src = rax; size = DWORD }
    ]
  | Modulo ->
    [ X86_asm.Mov { dest = rax; src = lhs; size = DWORD }
    ; X86_asm.Mov { dest = X86_asm.Reg swap; src = rhs; size = DWORD }
    ; X86_asm.Cvt { size = DWORD }
    ; X86_asm.Div { src = X86_asm.Reg swap; size = DWORD }
    ; X86_asm.Mov { dest; src = rdx; size = DWORD }
    ]
  | And -> X86_asm.safe_mov dest lhs DWORD @ X86_asm.safe_and dest rhs DWORD
  | Or -> X86_asm.safe_mov dest lhs DWORD @ X86_asm.safe_or dest rhs DWORD
  | Xor -> X86_asm.safe_mov dest lhs DWORD @ X86_asm.safe_xor dest rhs DWORD
  | Right_shift ->
    X86_asm.safe_mov dest lhs DWORD @ X86_asm.safe_sar dest rhs DWORD fpe_label
  | Left_shift ->
    X86_asm.safe_mov dest lhs DWORD @ X86_asm.safe_sal dest rhs DWORD fpe_label
  | Less | Less_eq | Greater | Greater_eq | Equal_eq | Not_eq ->
    gen_x86_relop_bin op dest lhs rhs swap
;;

let rec _codegen_w_reg_rev
    (res : X86_asm.instr list)
    (inst_list : Abs_asm.instr list)
    (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    (reg_swap : Reg.t)
  =
  match inst_list with
  | [] -> res
  | h :: t ->
    (* let () = printf "%s\n" (Abs_asm.format h) in *)
    (match h with
    | Abs_asm.Binop bin_op ->
      let dest = oprd_ps_to_x86 bin_op.dest reg_alloc_info in
      let lhs = oprd_ps_to_x86 bin_op.lhs reg_alloc_info in
      let rhs = oprd_ps_to_x86 bin_op.rhs reg_alloc_info in
      let insts = gen_x86_inst_bin bin_op.op dest lhs rhs reg_swap in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Abs_asm.Mov mov ->
      let dest = oprd_ps_to_x86 mov.dest reg_alloc_info in
      let src = oprd_ps_to_x86 mov.src reg_alloc_info in
      let insts = X86_asm.safe_mov dest src DWORD in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Abs_asm.Ret _ ->
      let insts = X86_asm.safe_ret QWORD in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Abs_asm.Label l ->
      _codegen_w_reg_rev (X86_asm.Label l.label :: res) t reg_alloc_info reg_swap
    | Abs_asm.Jump jp ->
      _codegen_w_reg_rev (X86_asm.Jump jp.target :: res) t reg_alloc_info reg_swap
    | Abs_asm.CJump cjp ->
      let lhs = oprd_ps_to_x86 cjp.lhs reg_alloc_info in
      let rhs = oprd_ps_to_x86 cjp.rhs reg_alloc_info in
      let target_true = cjp.target_true in
      let target_false = cjp.target_false in
      let cmp_inst = X86_asm.safe_cmp lhs rhs DWORD reg_swap in
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
    | Abs_asm.Push push ->
      let var = oprd_ps_to_x86 push.var reg_alloc_info in
      let inst_rev = X86_asm.Push { var; size = QWORD } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | Abs_asm.Pop pop ->
      let var = oprd_ps_to_x86 pop.var reg_alloc_info in
      let inst_rev = X86_asm.Pop { var; size = QWORD } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | Abs_asm.Fcall fcall ->
      let scope = trans_scope fcall.scope in
      let func_name = fcall.func_name in
      let inst = X86_asm.Fcall { func_name; scope } in
      _codegen_w_reg_rev (inst :: res) t reg_alloc_info reg_swap
    | Abs_asm.Assert ast ->
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
  let ecx = Reg.RCX in
  (* We use ecx as zero reg because it is saved for shift. *)
  [ X86_asm.Label fpe_label
  ; X86_asm.Mov { dest = Reg ecx; src = Imm Int32.zero; size = DWORD }
  ; X86_asm.Div { src = Reg ecx; size = DWORD }
  ]
;;

let abort_handler = [ X86_asm.Label abort_label; X86_asm.Abort ]

let gen
    (fdefn : Abs_asm.fdefn)
    (reg_alloc_info : (IG.Vertex.t * Regalloc.dest) option list)
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
  (* printf "gen prologue\n%!"; *)
  let mem_cnt = Int32.of_int_exn (8 * Memory.get_allocated_count ()) in
  (* printf "mem_cnt %d\n%!" (Int.of_int32_exn mem_cnt); *)
  (* store rbp and rsp at the beginning of each function *)
  [ X86_asm.Fname fdefn.func_name
  ; X86_asm.Push { var = rbp; size = QWORD }
  ; X86_asm.Mov { dest = rbp; src = rsp; size = QWORD }
  ; X86_asm.Sub { src = X86_asm.Imm mem_cnt; dest = rsp; size = QWORD }
  ]
  @ res
;;
