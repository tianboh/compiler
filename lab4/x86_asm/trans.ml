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
module Reg = Var.X86_reg.Logic
module Memory = Var.Memory
module Label = Util.Label
module IG = Regalloc.Interference_graph
module Regalloc = Regalloc.Driver

let trans_operand (operand : Src.operand) (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    : X86_asm.operand
  =
  match operand with
  | Temp t ->
    let dest = IG.Vertex.Map.find_exn reg_alloc_info (IG.Vertex.T.Temp t) in
    (match dest with
    | Regalloc.Reg r -> X86_asm.Reg r
    | Regalloc.Mem m -> X86_asm.Mem m)
  | Imm i -> X86_asm.Imm { v = i.v; size = i.size }
  | Reg r -> X86_asm.Reg r
  (* The latest available memory is rsp + 8. Remember that caller push parameter and callee
   * push rbp, mov rsp to rbp so in order to access parameters in callee function, 
   * we need to skip the pushed rbp, which is 1. *)
  | Above_frame af ->
    let base = ({ reg = Reg.RBP; size = `QWORD } : Var.X86_reg.Hard.t) in
    X86_asm.Mem (Memory.above_frame base af.offset af.size)
  | Below_frame bf ->
    let base = ({ reg = Reg.RBP; size = `QWORD } : Var.X86_reg.Hard.t) in
    X86_asm.Mem (Memory.below_frame base bf.offset bf.size)
;;

let trans_mem (mem : Src.mem) : Memory.t =
  let base, offset, size = mem.base, mem.offset, mem.size in
  match offset with
  | Some offset -> { index = None; base; offset = `Reg offset; size }
  | None ->
    let offset = `Imm 0L in
    { index = None; base; offset; size }
;;

let rax = Reg.RAX
let rdx = Reg.RDX
let rbp = Reg.RBP
let rsp = Reg.RSP
let fpe_label = Label.label (Some "fpe")
let abort_label = Label.label (Some "abt")
let shift_maximum_bit = Int64.of_int_exn 31 (* inclusive *)

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_mov (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Reg.swap; size }; src = Mem src; size }
    ; X86_asm.Mov { dest = Mem dest; src = Reg { reg = Reg.swap; size }; size }
    ]
  | _ -> [ Mov { dest; src; size } ]
;;

let safe_add (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Reg.swap; size }; src = Mem src; size }
    ; X86_asm.Add { dest = Mem dest; src = Reg { reg = Reg.swap; size }; size }
    ]
  | _ -> [ X86_asm.Add { dest; src; size } ]
;;

let safe_sub (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Reg.swap; size }; src = Mem src; size }
    ; X86_asm.Sub { dest = Mem dest; src = Reg { reg = Reg.swap; size }; size }
    ]
  | _ -> [ Sub { dest; src; size } ]
;;

let safe_and (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Reg.swap; size }; src = Mem src; size }
    ; X86_asm.AND { dest = Mem dest; src = Reg { reg = Reg.swap; size }; size }
    ]
  | _ -> [ AND { dest; src; size } ]
;;

let safe_or (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Reg.swap; size }; src = Mem src; size }
    ; X86_asm.OR { dest = Mem dest; src = Reg { reg = Reg.swap; size }; size }
    ]
  | _ -> [ OR { dest; src; size } ]
;;

let safe_xor (dest : X86_asm.operand) (src : X86_asm.operand) (size : Size.primitive) =
  match dest, src with
  | Mem dest, Mem src ->
    [ X86_asm.Mov { dest = Reg { reg = Reg.swap; size }; src = Mem src; size }
    ; X86_asm.XOR { dest = Mem dest; src = Reg { reg = Reg.swap; size }; size }
    ]
  | _ -> [ XOR { dest; src; size } ]
;;

(* shift bit should be [0, 31] *)
let shift_check (shift_bit : X86_asm.operand) (fpe_label : Label.t) =
  [ X86_asm.Cmp
      { lhs = shift_bit
      ; rhs = Imm { v = shift_maximum_bit; size = `DWORD }
      ; size = `DWORD
      }
  ; X86_asm.JG fpe_label
  ; X86_asm.Cmp { lhs = shift_bit; rhs = Imm { v = 0L; size = `DWORD }; size = `DWORD }
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
    let ecx = Reg.RCX in
    (* when src is register/memory, SAL can only use %cl to shift. *)
    (X86_asm.Mov { dest = Reg { reg = ecx; size }; src; size }
    :: shift_check (Reg { reg = ecx; size }) fpe_label)
    @ [ SAL { dest; src = Reg { reg = ecx; size = `BYTE }; size } ]
  | Imm _ ->
    shift_check src fpe_label
    @ [ SAL { dest; src = Inst.set_size src `BYTE; size = `BYTE } ]
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
    let ecx = Reg.RCX in
    (* when src is register/memory, SAR can only use %cl to shift. *)
    (X86_asm.Mov { dest = Reg { reg = ecx; size }; src; size }
    :: shift_check (Reg { reg = ecx; size }) fpe_label)
    @ [ SAR { dest; src = Reg { reg = ecx; size = `BYTE }; size } ]
  | Imm _ -> shift_check src fpe_label @ [ SAR { dest; src; size = `BYTE } ]
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
  let al = X86_asm.Reg { reg = rax; size = `BYTE } in
  let rax = X86_asm.Reg { reg = rax; size = `QWORD } in
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
    (swap : Reg.t)
  =
  let size = Inst.get_size dest in
  let rax = X86_asm.Reg { reg = rax; size } in
  let swap = X86_asm.Reg { reg = swap; size } in
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
    [ X86_asm.Mov { dest = rax; src = lhs; size }
    ; X86_asm.Mov { dest = swap; src = rhs; size }
    ; X86_asm.Cvt { size }
    ; X86_asm.Div { src = swap; size }
    ; X86_asm.Mov { dest; src = Reg { reg = rdx; size }; size }
    ]
  | And -> safe_mov dest lhs size @ safe_and dest rhs size
  | Or -> safe_mov dest lhs size @ safe_or dest rhs size
  | Xor -> safe_mov dest lhs size @ safe_xor dest rhs size
  | Right_shift -> safe_mov dest lhs size @ safe_sar dest rhs size fpe_label
  | Left_shift -> safe_mov dest lhs size @ safe_sal dest rhs size fpe_label
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
    | Binop bin_op ->
      let dest = trans_operand bin_op.dest reg_alloc_info in
      let lhs = trans_operand bin_op.lhs reg_alloc_info in
      let rhs = trans_operand bin_op.rhs reg_alloc_info in
      let insts = gen_x86_inst_bin bin_op.op dest lhs rhs reg_swap in
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
      let cmp_inst =
        safe_cmp lhs rhs `DWORD (X86_asm.Reg { reg = reg_swap; size = `DWORD })
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
    | Push push ->
      let var = trans_operand push.var reg_alloc_info in
      let inst_rev = X86_asm.Push { var; size = `QWORD } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | Pop pop ->
      let var = trans_operand pop.var reg_alloc_info in
      let inst_rev = X86_asm.Pop { var; size = `QWORD } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | Fcall fcall ->
      let scope = fcall.scope in
      let func_name = fcall.func_name in
      let inst = X86_asm.Fcall { func_name; scope } in
      _codegen_w_reg_rev (inst :: res) t reg_alloc_info reg_swap
    | Assert ast ->
      let var = trans_operand ast.var reg_alloc_info in
      let size = `QWORD in
      let insts_rev =
        [ X86_asm.Cmp { lhs = var; rhs = X86_asm.Imm { v = 1L; size }; size }
        ; X86_asm.JNE abort_label
        ]
        |> List.rev
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Load load ->
      let src = X86_asm.Mem (trans_mem load.src) in
      let dest = trans_operand (Src.Temp load.dest) reg_alloc_info in
      let size = load.size in
      let insts_rev =
        match dest with
        | X86_asm.Mem _ ->
          let r15 = X86_asm.Reg ({ reg = Reg.swap; size } : Var.X86_reg.Hard.t) in
          [ X86_asm.Mov { dest; src = r15; size }; X86_asm.Mov { dest = r15; src; size } ]
        | _ -> [ X86_asm.Mov { dest; src; size } ]
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Store store ->
      let dest = X86_asm.Mem (trans_mem store.dest) in
      let src = trans_operand store.src reg_alloc_info in
      let size = store.size in
      let insts_rev =
        match src with
        | X86_asm.Mem _ ->
          let r15 = X86_asm.Reg ({ reg = Reg.swap; size } : Var.X86_reg.Hard.t) in
          [ X86_asm.Mov { dest; src = r15; size }; X86_asm.Mov { dest = r15; src; size } ]
        | _ -> [ X86_asm.Mov { dest; src; size } ]
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Directive _ | Comment _ -> _codegen_w_reg_rev res t reg_alloc_info reg_swap)
;;

let fpe_handler =
  let open Util.Symbol.Fname in
  let edi = X86_asm.Reg { reg = RDI; size = `DWORD } in
  [ X86_asm.Label fpe_label
  ; X86_asm.Mov { dest = edi; src = Imm { v = fpe; size = `DWORD }; size = `DWORD }
  ; X86_asm.Fcall { func_name = raise; scope = `Internal }
  ]
;;

let abort_handler = [ X86_asm.Label abort_label; X86_asm.Abort ]

let gen (fdefn : Src.fdefn) (reg_alloc_info : (IG.Vertex.t * Regalloc.dest) option list)
    : X86_asm.instr list
  =
  let open Base.Int64 in
  let reg_alloc =
    List.fold reg_alloc_info ~init:IG.Vertex.Map.empty ~f:(fun acc x ->
        match x with
        | None -> acc
        | Some x ->
          (match x with
          | temp, reg -> IG.Vertex.Map.set acc ~key:temp ~data:reg))
  in
  let reg_swap = Reg.R15 in
  let res = _codegen_w_reg_rev [] fdefn.body reg_alloc reg_swap |> List.rev in
  let mem_cnt = 8L * Memory.get_allocated_count () in
  let mem_cnt = if mem_cnt % 16L = 0L then mem_cnt else mem_cnt + 8L in
  (* store rbp and rsp at the beginning of each function *)
  let size = `QWORD in
  let rbp = X86_asm.Reg { reg = rbp; size } in
  let rsp = X86_asm.Reg { reg = rsp; size } in
  let scope = (fdefn.scope :> [ `C0 | `Internal | `External ]) in
  [ X86_asm.Fname { name = fdefn.func_name; scope }
  ; X86_asm.Push { var = rbp; size }
  ; X86_asm.Mov { dest = rbp; src = rsp; size }
  ; X86_asm.Sub { src = X86_asm.Imm { v = mem_cnt; size }; dest = rsp; size }
  ]
  @ res
;;
