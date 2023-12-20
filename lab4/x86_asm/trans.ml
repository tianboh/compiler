(* L4 Compiler
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
module X86_asm = Inst
module Temp = Var.Temp
module Reg_logic = Var.X86_reg.Logic
module Reg_hard = Var.X86_reg.Hard
module Memory = Var.Memory
module Label = Util.Label
module IG = Regalloc.Interference_graph
module Regalloc = Regalloc.Driver

let trans_operand (operand : Src.operand) (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    : X86_asm.operand
  =
  let size = operand.size in
  match operand.data with
  | Temp t ->
    let dest = IG.Vertex.Map.find_exn reg_alloc_info (IG.Vertex.T.Temp t) in
    (match dest with
    | Regalloc.Reg r -> { data = X86_asm.Reg r; size }
    | Regalloc.Spill s ->
      let data = X86_asm.Mem (Memory.create s.id size) in
      { data; size })
  | Imm i -> { data = X86_asm.Imm i; size }
  | Reg r -> { data = X86_asm.Reg r; size }
  (* The latest available memory is rsp + 8. Remember that caller push parameter and callee
   * push rbp, mov rsp to rbp so in order to access parameters in callee function, 
   * we need to skip the pushed rbp, which is 1. *)
  | Above_frame af ->
    let frame = Memory.above_frame Memory.rbp af in
    { data = X86_asm.Mem frame; size }
  | Below_frame bf ->
    let frame = Memory.below_frame Memory.rbp bf in
    { data = X86_asm.Mem frame; size }
;;

let trans_mem (mem : Src.mem) : Memory.t =
  let base, offset = mem.base, mem.offset in
  let base : Memory.reg = { reg = base.data; size = base.size } in
  match offset with
  | Some offset ->
    let offset : Memory.reg = { reg = offset.data; size = offset.size } in
    { index = None; base; offset = `Reg offset }
  | None ->
    let offset = `Imm 0L in
    { index = None; base; offset }
;;

let rax = Reg_logic.RAX
let rdx = Reg_logic.RDX
let rbp = Reg_logic.RBP
let rsp = Reg_logic.RSP

(* let shift_maximum_bit = Int64.of_int_exn 31 inclusive *)
let abort_label = Util.Label.Handler.sigabrt

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_mov (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest.data, src.data with
  | Mem _, Mem _ ->
    let swap : X86_asm.operand = { data = X86_asm.Reg Reg_logic.swap; size } in
    [ X86_asm.Mov { dest = swap; src; size }; X86_asm.Mov { dest; src = swap; size } ]
  | _ -> [ Mov { dest; src; size } ]
;;

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_cast (dest : X86_asm.operand) (src : X86_asm.operand) =
  match dest.data, src.data with
  | Mem _, Mem _ ->
    let size = src.size in
    let swap : X86_asm.operand = { data = X86_asm.Reg Reg_logic.swap; size } in
    [ X86_asm.Mov { dest = swap; src; size }; X86_asm.Cast { dest; src = swap } ]
  | _ -> [ Cast { dest; src } ]
;;

let safe_add (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest.data, src.data with
  | Mem _, Mem _ ->
    let swap : X86_asm.operand = { data = X86_asm.Reg Reg_logic.swap; size } in
    [ X86_asm.Mov { dest = swap; src; size }; X86_asm.Add { dest; src = swap; size } ]
  | _ -> [ X86_asm.Add { dest; src; size } ]
;;

let safe_sub (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest.data, src.data with
  | Mem _, Mem _ ->
    let swap : X86_asm.operand = { data = X86_asm.Reg Reg_logic.swap; size } in
    [ X86_asm.Mov { dest = swap; src; size }; X86_asm.Sub { dest; src = swap; size } ]
  | _ -> [ Sub { dest; src; size } ]
;;

let safe_and (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest.data, src.data with
  | Mem _, Mem _ ->
    let swap : X86_asm.operand = { data = X86_asm.Reg Reg_logic.swap; size } in
    [ X86_asm.Mov { dest = swap; src; size }; X86_asm.AND { dest; src = swap; size } ]
  | _ -> [ AND { dest; src; size } ]
;;

let safe_or (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest.data, src.data with
  | Mem _, Mem _ ->
    let swap : X86_asm.operand = { data = X86_asm.Reg Reg_logic.swap; size } in
    [ X86_asm.Mov { dest = swap; src; size }; X86_asm.OR { dest; src = swap; size } ]
  | _ -> [ OR { dest; src; size } ]
;;

let safe_xor (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest.data, src.data with
  | Mem _, Mem _ ->
    let swap : X86_asm.operand = { data = X86_asm.Reg Reg_logic.swap; size } in
    [ X86_asm.Mov { dest = swap; src; size }; X86_asm.XOR { dest; src = swap; size } ]
  | _ -> [ XOR { dest; src; size } ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sal (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match src.data with
  | Reg _ | Mem _ ->
    let ecx : X86_asm.operand = { data = X86_asm.Reg Reg_logic.RCX; size = `BYTE } in
    (* when src is register/memory, SAL can only use %cl to shift. *)
    X86_asm.Cast { dest = ecx; src } :: [ SAL { dest; src = ecx; size } ]
  | Imm _ -> [ SAL { dest; src = Inst.set_size src `BYTE; size = `BYTE } ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sar (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match src.data with
  | Reg _ | Mem _ ->
    let ecx : X86_asm.operand = { data = X86_asm.Reg Reg_logic.RCX; size = `BYTE } in
    (* when src is register/memory, SAR can only use %cl to shift. *)
    X86_asm.Cast { dest = ecx; src } :: [ SAR { dest; src = ecx; size } ]
  | Imm _ -> [ SAR { dest; src; size = `BYTE } ]
;;

let safe_ret (size : Size.primitive) =
  (* insts = [ "mov %rbp, %rsp"; "pop %rbp"; "ret" ] *)
  let rbp : X86_asm.operand = { data = X86_asm.Reg Reg_logic.RBP; size } in
  let rsp : X86_asm.operand = { data = X86_asm.Reg Reg_logic.RSP; size } in
  [ X86_asm.Mov { dest = rsp; src = rbp; size }; X86_asm.Pop { var = rbp }; X86_asm.Ret ]
;;

(* Prepare for conditional jump. *)
let safe_cmp
    (lhs : X86_asm.operand)
    (rhs : X86_asm.operand)
    (size : Size.primitive)
    (swap : X86_asm.operand)
  =
  match lhs.data, rhs.data with
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
  let al : X86_asm.operand = { data = X86_asm.Reg rax; size = `BYTE } in
  let rax : X86_asm.operand = { data = X86_asm.Reg rax; size = `QWORD } in
  let set_inst =
    match op with
    | Less -> [ X86_asm.SETL { dest = al; size = `BYTE } ]
    | Less_eq -> [ X86_asm.SETLE { dest = al; size = `BYTE } ]
    | Greater -> [ X86_asm.SETG { dest = al; size = `BYTE } ]
    | Greater_eq -> [ X86_asm.SETGE { dest = al; size = `BYTE } ]
    | Equal_eq -> [ X86_asm.SETE { dest = al; size = `BYTE } ]
    | Not_eq -> [ X86_asm.SETNE { dest = al; size = `BYTE } ]
    | _ -> failwith "relop cannot handle other op"
  in
  let cmp_inst = safe_cmp lhs rhs `DWORD swap in
  [ X86_asm.XOR { dest = rax; src = rax; size = `DWORD } ]
  @ cmp_inst
  @ set_inst
  @ [ X86_asm.Mov { dest; src = Inst.set_size rax (Inst.get_size dest); size = `DWORD } ]
;;

let gen_x86_inst_bin
    (op : Src.bin_op)
    (dest : X86_asm.operand)
    (lhs : X86_asm.operand)
    (rhs : X86_asm.operand)
    (swap : Reg_logic.t)
  =
  let size = Inst.get_size dest in
  let rax : X86_asm.operand = { data = X86_asm.Reg rax; size } in
  let swap : X86_asm.operand = { data = X86_asm.Reg swap; size } in
  match op with
  | Plus -> safe_mov dest lhs size @ safe_add dest rhs size
  | Minus -> safe_mov dest lhs size @ safe_sub dest rhs size
  | Times ->
    [ X86_asm.Mov { dest = rax; src = lhs; size }
    ; X86_asm.Mul { src = rhs; dest = rax; size }
    ; X86_asm.Mov { dest; src = rax; size }
    ]
  | Divided_by ->
    (* Notice that lhs and rhs may be allocated on rdx. 
     * So we use reg_swap to avoid override in the rdx <- 0. *)
    [ X86_asm.Mov { dest = rax; src = lhs; size }
    ; X86_asm.Mov { dest = swap; src = rhs; size }
    ; X86_asm.Cvt { size }
    ; X86_asm.Div { src = swap; size }
    ; X86_asm.Mov { dest; src = rax; size }
    ]
  | Modulo ->
    let rdx : X86_asm.operand = { data = X86_asm.Reg rdx; size } in
    [ X86_asm.Mov { dest = rax; src = lhs; size }
    ; X86_asm.Mov { dest = swap; src = rhs; size }
    ; X86_asm.Cvt { size }
    ; X86_asm.Div { src = swap; size }
    ; X86_asm.Mov { dest; src = rdx; size }
    ]
  | And -> safe_mov dest lhs size @ safe_and dest rhs size
  | Or -> safe_mov dest lhs size @ safe_or dest rhs size
  | Xor -> safe_mov dest lhs size @ safe_xor dest rhs size
  | Right_shift -> safe_mov dest lhs size @ safe_sar dest rhs size
  | Left_shift -> safe_mov dest lhs size @ safe_sal dest rhs size
  | Less | Less_eq | Greater | Greater_eq | Equal_eq | Not_eq ->
    gen_x86_relop_bin op dest lhs rhs swap
;;

let rec _codegen_w_reg_rev
    (res : X86_asm.instr list)
    (inst_list : Src.instr list)
    (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    (reg_swap : Reg_logic.t)
  =
  match inst_list with
  | [] -> res
  | h :: t ->
    (* let () = printf "%s\n" (Src.format h) in *)
    (match h with
    | Binop bin_op ->
      let dest = trans_operand bin_op.dest reg_alloc_info in
      let lhs = trans_operand bin_op.lhs reg_alloc_info in
      let rhs = trans_operand bin_op.rhs reg_alloc_info in
      let insts = gen_x86_inst_bin bin_op.op dest lhs rhs reg_swap in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Cast cast ->
      let dest_oprd : Src.operand =
        { data = Src.Temp cast.dest.data; size = cast.dest.size }
      in
      let src_oprd : Src.operand =
        { data = Src.Temp cast.src.data; size = cast.src.size }
      in
      let dest = trans_operand dest_oprd reg_alloc_info in
      let src = trans_operand src_oprd reg_alloc_info in
      let size = Inst.get_size dest in
      let insts = safe_mov dest src size in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Mov mov ->
      let dest = trans_operand mov.dest reg_alloc_info in
      let src = trans_operand mov.src reg_alloc_info in
      let size = Inst.get_size dest in
      let insts = safe_mov dest src size in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Ret _ ->
      let insts = safe_ret `QWORD in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Label l ->
      _codegen_w_reg_rev (X86_asm.Label l.label :: res) t reg_alloc_info reg_swap
    | Jump jp ->
      _codegen_w_reg_rev (X86_asm.Jump jp.target :: res) t reg_alloc_info reg_swap
    | CJump cjp ->
      let lhs = trans_operand cjp.lhs reg_alloc_info in
      let rhs = trans_operand cjp.rhs reg_alloc_info in
      let target_true = cjp.target_true in
      let target_false = cjp.target_false in
      let swap : X86_asm.operand = { data = X86_asm.Reg reg_swap; size = `DWORD } in
      let cmp_inst = safe_cmp lhs rhs `DWORD swap in
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
    | Push push ->
      let var = trans_operand push.var reg_alloc_info in
      let inst_rev = X86_asm.Push { var } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | Pop pop ->
      let var = trans_operand pop.var reg_alloc_info in
      let inst_rev = X86_asm.Pop { var } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | Fcall fcall ->
      let scope = fcall.scope in
      let func_name = fcall.func_name in
      let inst = X86_asm.Fcall { func_name; scope } in
      _codegen_w_reg_rev (inst :: res) t reg_alloc_info reg_swap
    | Load load ->
      let src = X86_asm.Mem (trans_mem load.src) in
      let size = load.src.size in
      let src_oprd : X86_asm.operand = { data = src; size } in
      let dest_oprd : Src.operand =
        { data = Src.Temp load.dest.data; size = load.dest.size }
      in
      let dest : X86_asm.operand = trans_operand dest_oprd reg_alloc_info in
      let insts_rev =
        match dest.data with
        | X86_asm.Mem _ ->
          let swap : X86_asm.operand = { data = X86_asm.Reg Reg_logic.swap; size } in
          [ X86_asm.Mov { dest; src = swap; size }
          ; X86_asm.Mov { dest = swap; src = src_oprd; size }
          ]
        | _ -> [ X86_asm.Mov { dest; src = src_oprd; size } ]
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Store store ->
      let dest = X86_asm.Mem (trans_mem store.dest) in
      let dest_oprd : X86_asm.operand = { data = dest; size = store.dest.size } in
      let src = trans_operand store.src reg_alloc_info in
      let size = src.size in
      let insts_rev =
        match src.data with
        | X86_asm.Mem _ ->
          let swap : X86_asm.operand = { data = X86_asm.Reg Reg_logic.swap; size } in
          [ X86_asm.Mov { dest = dest_oprd; src = swap; size }
          ; X86_asm.Mov { dest = swap; src; size }
          ]
        | _ -> [ X86_asm.Mov { dest = dest_oprd; src; size } ]
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Directive _ | Comment _ -> _codegen_w_reg_rev res t reg_alloc_info reg_swap)
;;

let abort_handler = [ X86_asm.Label abort_label; X86_asm.Abort ]

let gen (fdefn : Src.fdefn) (reg_alloc_info : (IG.Vertex.t * Regalloc.dest) option list)
    : X86_asm.instr list
  =
  let size = `QWORD in
  let open Base.Int64 in
  let reg_alloc =
    List.fold reg_alloc_info ~init:IG.Vertex.Map.empty ~f:(fun acc x ->
        match x with
        | None -> acc
        | Some x ->
          (match x with
          | temp, reg -> IG.Vertex.Map.set acc ~key:temp ~data:reg))
  in
  let reg_swap = Reg_logic.R15 in
  let res = _codegen_w_reg_rev [] fdefn.body reg_alloc reg_swap |> List.rev in
  let mem_cnt = 8L * Memory.get_allocated_count () in
  let mem_cnt = if mem_cnt % 16L = 0L then mem_cnt else mem_cnt + 8L in
  let mem_cnt_oprd : X86_asm.operand = { data = X86_asm.Imm mem_cnt; size } in
  (* store rbp and rsp at the beginning of each function *)
  let rbp : X86_asm.operand = { data = X86_asm.Reg rbp; size } in
  let rsp : X86_asm.operand = { data = X86_asm.Reg rsp; size } in
  let scope = (fdefn.scope :> [ `C0 | `Internal | `External ]) in
  [ X86_asm.Fname { name = fdefn.func_name; scope }
  ; X86_asm.Push { var = rbp }
  ; X86_asm.Mov { dest = rbp; src = rsp; size }
  ; X86_asm.Sub { src = mem_cnt_oprd; dest = rsp; size }
  ]
  @ res
;;
