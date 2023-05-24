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
module T = Middle.Tree
module AS = Convention.Inst
module AS_x86 = Inst.X86
module Reg_info = Json_reader.Lab1_checkpoint
module Temp = Var.Temp
module Register = Var.X86_reg
module Memory = Var.Memory
module Label = Util.Label
module IG = Regalloc.Interference_graph
open Var.Layout
module Regalloc = Regalloc.Driver

let oprd_ps_to_x86 (operand : AS.operand) (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    : AS_x86.operand
  =
  match operand with
  | Temp t ->
    let dest =
      match IG.Vertex.Map.find reg_alloc_info (IG.Vertex.T.Temp t) with
      | Some s -> s
      | None ->
        (* Some variable that is only declared but not defined during the whole program. 
         * For example: int a; and no assignment afterwards.
         * In this case, we will use %eax to represent it. Notice that it is only a representation
         * for this uninitialized temporary, and %eax will not be assigned in the following instruction.
         * Therefore, no worry for the return value. *)
        Regalloc.Reg Register.RAX
    in
    (match dest with
    | Regalloc.Reg r -> AS_x86.Reg r
    | Regalloc.Mem m -> AS_x86.Mem m)
  | Imm i -> AS_x86.Imm i
  | Reg r -> AS_x86.Reg r
;;

let eax = AS_x86.Reg Register.RAX
let edx = AS_x86.Reg Register.RDX
let fpe_label = Label.label (Some "fpe")

(* We don't need to store eax because eax is not assigned to any temp.
 * Though eax, edx may be used by div/idiv instruction, once those 
 * instructions are finished, eax, edx will no longer be used. 
 * In a word, eax does not store temporary except ret. *)
let gen_x86_relop_bin
    (op : AS.bin_op)
    (dest : AS_x86.operand)
    (lhs : AS_x86.operand)
    (rhs : AS_x86.operand)
    (swap : Register.t)
  =
  let set_inst =
    match op with
    | Less -> [ AS_x86.SETL { dest = eax; layout = BYTE } ]
    | Less_eq -> [ AS_x86.SETLE { dest = eax; layout = BYTE } ]
    | Greater -> [ AS_x86.SETG { dest = eax; layout = BYTE } ]
    | Greater_eq -> [ AS_x86.SETGE { dest = eax; layout = BYTE } ]
    | Equal_eq -> [ AS_x86.SETE { dest = eax; layout = BYTE } ]
    | Not_eq -> [ AS_x86.SETNE { dest = eax; layout = BYTE } ]
    | _ -> failwith "relop cannot handle other op"
  in
  let cmp_inst = AS_x86.safe_cmp lhs rhs DWORD swap in
  [ AS_x86.XOR { dest = eax; src = eax; layout = DWORD } ]
  @ cmp_inst
  @ set_inst
  @ [ AS_x86.Mov { dest; src = eax; layout = DWORD } ]
;;

let gen_x86_inst_bin
    (op : AS.bin_op)
    (dest : AS_x86.operand)
    (lhs : AS_x86.operand)
    (rhs : AS_x86.operand)
    (swap : Register.t)
  =
  match op with
  | Plus -> AS_x86.safe_mov dest lhs DWORD @ AS_x86.safe_add dest rhs DWORD
  | Minus -> AS_x86.safe_mov dest lhs DWORD @ AS_x86.safe_sub dest rhs DWORD
  | Times ->
    [ AS_x86.Mov { dest = eax; src = lhs; layout = DWORD }
    ; AS_x86.Mul { src = rhs; dest = eax; layout = DWORD }
    ; AS_x86.Mov { dest; src = eax; layout = DWORD }
    ]
  | Divided_by ->
    (* Notice that lhs and rhs may be allocated on edx. 
     * So we use reg_swap to avoid override in the edx <- 0. *)
    [ AS_x86.Mov { dest = eax; src = lhs; layout = DWORD }
    ; AS_x86.Mov { dest = AS_x86.Reg swap; src = rhs; layout = DWORD }
    ; AS_x86.Cvt { layout = DWORD }
    ; AS_x86.Div { src = AS_x86.Reg swap; layout = DWORD }
    ; AS_x86.Mov { dest; src = eax; layout = DWORD }
    ]
  | Modulo ->
    [ AS_x86.Mov { dest = eax; src = lhs; layout = DWORD }
    ; AS_x86.Mov { dest = AS_x86.Reg swap; src = rhs; layout = DWORD }
    ; AS_x86.Cvt { layout = DWORD }
    ; AS_x86.Div { src = AS_x86.Reg swap; layout = DWORD }
    ; AS_x86.Mov { dest; src = edx; layout = DWORD }
    ]
  | And -> AS_x86.safe_mov dest lhs DWORD @ AS_x86.safe_and dest rhs DWORD
  | Or -> AS_x86.safe_mov dest lhs DWORD @ AS_x86.safe_or dest rhs DWORD
  | Xor -> AS_x86.safe_mov dest lhs DWORD @ AS_x86.safe_xor dest rhs DWORD
  | Right_shift ->
    AS_x86.safe_mov dest lhs DWORD @ AS_x86.safe_sar dest rhs DWORD fpe_label
  | Left_shift ->
    AS_x86.safe_mov dest lhs DWORD @ AS_x86.safe_sal dest rhs DWORD fpe_label
  | Less | Less_eq | Greater | Greater_eq | Equal_eq | Not_eq ->
    gen_x86_relop_bin op dest lhs rhs swap
;;

let rec _codegen_w_reg_rev
    res
    inst_list
    (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    (reg_swap : Register.t)
  =
  match inst_list with
  | [] -> res
  | h :: t ->
    (* let () = printf "%s\n" (AS.format h) in *)
    (match h with
    | AS.Binop bin_op ->
      let dest = oprd_ps_to_x86 bin_op.dest reg_alloc_info in
      let lhs = oprd_ps_to_x86 bin_op.lhs reg_alloc_info in
      let rhs = oprd_ps_to_x86 bin_op.rhs reg_alloc_info in
      let insts = gen_x86_inst_bin bin_op.op dest lhs rhs reg_swap in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | AS.Mov mov ->
      let dest = oprd_ps_to_x86 mov.dest reg_alloc_info in
      let src = oprd_ps_to_x86 mov.src reg_alloc_info in
      let insts = AS_x86.safe_mov dest src DWORD in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | AS.Ret _ ->
      let insts = AS_x86.safe_ret QWORD in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | AS.Label l ->
      _codegen_w_reg_rev (AS_x86.Label l.label :: res) t reg_alloc_info reg_swap
    | AS.Jump jp ->
      _codegen_w_reg_rev (AS_x86.Jump jp.target :: res) t reg_alloc_info reg_swap
    | AS.CJump cjp ->
      let lhs = oprd_ps_to_x86 cjp.lhs reg_alloc_info in
      let rhs = oprd_ps_to_x86 cjp.rhs reg_alloc_info in
      let target_true = cjp.target_true in
      let target_false = cjp.target_false in
      let cmp_inst = AS_x86.safe_cmp lhs rhs DWORD reg_swap in
      let cmp_inst_rev = List.rev cmp_inst in
      let cjp_inst =
        match cjp.op with
        | Equal_eq -> AS_x86.JE target_true
        | Greater -> AS_x86.JG target_true
        | Greater_eq -> AS_x86.JGE target_true
        | Less -> AS_x86.JL target_true
        | Less_eq -> AS_x86.JLE target_true
        | Not_eq -> AS_x86.JNE target_true
        | _ -> failwith "conditional jump op should can only be relop."
      in
      let jp = AS_x86.Jump target_false in
      _codegen_w_reg_rev
        (([ jp; cjp_inst ] @ cmp_inst_rev) @ res)
        t
        reg_alloc_info
        reg_swap
    | AS.Push push ->
      let var = oprd_ps_to_x86 push.var reg_alloc_info in
      let inst_rev = AS_x86.Push { var; layout = QWORD } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | AS.Pop pop ->
      let var = oprd_ps_to_x86 pop.var reg_alloc_info in
      let inst_rev = AS_x86.Pop { var; layout = QWORD } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | AS.Fcall _ | AS.Assert _ -> failwith "x86 inst not impl yet"
    | _ -> _codegen_w_reg_rev res t reg_alloc_info reg_swap)
;;

let fpe_handler =
  let ecx = Register.RCX in
  (* We use ecx as zero reg because it is saved for shift. *)
  [ AS_x86.Label fpe_label
  ; AS_x86.Mov { dest = Reg ecx; src = Imm Int32.zero; layout = DWORD }
  ; AS_x86.Div { src = Reg ecx; layout = DWORD }
  ]
;;

let gen (fdefn : AS.fdefn) (reg_alloc_info : (IG.Vertex.t * Regalloc.dest) option list)
    : AS_x86.instr list
  =
  let program = Regalloc.gen_program fdefn in
  let reg_alloc =
    List.fold reg_alloc_info ~init:IG.Vertex.Map.empty ~f:(fun acc x ->
        match x with
        | None -> acc
        | Some x ->
          (match x with
          | temp, reg -> IG.Vertex.Map.set acc ~key:temp ~data:reg))
  in
  let reg_swap = Register.R15 in
  let res_rev = _codegen_w_reg_rev [] program reg_alloc reg_swap in
  let res = List.rev res_rev in
  res @ fpe_handler
;;
