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
module Dest = Inst
module Temp = Var.Temp
module Reg_logic = Var.X86_reg.Logic
module Reg_hard = Var.X86_reg.Hard
module Reg_spill = Var.X86_reg.Spill
module Label = Util.Label
module IG = Regalloc.Interference_graph
module Regalloc = Regalloc.Driver

let trans_operand (operand : Src.Sop.t) (reg_alloc_info : Regalloc.dest IG.Vertex.Map.t)
    : Dest.instr list * Dest.Sop.t
  =
  let size = operand.size in
  match operand.data with
  | Temp t ->
    let dest = IG.Vertex.Map.find_exn reg_alloc_info (IG.Vertex.T.Temp t) in
    (match dest with
    | Regalloc.Reg r -> [], Dest.Op.of_reg r |> Dest.Sop.wrap size
    | Regalloc.Spill s ->
      let size = `QWORD in
      let scale = 8L in
      let id = Reg_spill.get_idx0 s in
      let base = Reg_hard.wrap size Reg_logic.RSP in
      let rbp = Reg_logic.RBP in
      let rbp' = Reg_hard.wrap size rbp in
      let dest = rbp |> Dest.Op.of_reg |> Dest.Sop.wrap size in
      let src = id |> Int64.of_int |> Dest.Op.of_imm |> Dest.Sop.wrap size in
      ( [ Dest.Mov { dest; src; size } ]
      , Dest.Op.of_addr base (Some rbp') (Some scale) None |> Dest.Sop.wrap size ))
  | Imm i -> [], Dest.Op.of_imm i |> Dest.Sop.wrap size
  | Reg r -> [], Dest.Op.of_reg r |> Dest.Sop.wrap size
  | Above_frame af ->
    let size = `QWORD in
    let spill_tot = Reg_spill.get_tot () in
    let idx = Base.Int64.( + ) (Int64.of_int spill_tot) af in
    let scale = 8L in
    let rbp = Reg_logic.RBP in
    let rbp' = Reg_hard.wrap `QWORD rbp in
    let base = Reg_hard.wrap size Reg_logic.RSP in
    let dest = rbp |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    let src = idx |> Dest.Op.of_imm |> Dest.Sop.wrap size in
    ( [ Dest.Mov { dest; src; size } ]
    , Dest.Op.of_addr base (Some rbp') (Some scale) None |> Dest.Sop.wrap size )
;;

let trans_mem (mem : Src.Mem.t) : Dest.Mem.t =
  let size = `QWORD in
  let base, index, scale, disp = Src.Addr.get mem.data in
  let base = Reg_hard.wrap size base in
  let index =
    match index with
    | Some index -> Some (index |> Reg_hard.wrap size)
    | None -> None
  in
  Dest.Addr.of_bisd base index scale disp |> Dest.Mem.wrap mem.size
;;

let rax = Reg_logic.RAX
let rdx = Reg_logic.RDX
let rbp = Reg_logic.RBP
let rsp = Reg_logic.RSP

(* let shift_maximum_bit = Int64.of_int_exn 31 inclusive *)
let abort_label = Util.Label.Handler.sigabrt

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_mov (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Addr _, Dest.Op.Addr _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.Mov { dest; src = swap; size } ]
  | _ -> [ Mov { dest; src; size } ]
;;

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_cast (dest : Dest.Sop.t) (src : Dest.Sop.t) =
  if Size.compare (dest.size :> Size.t) (src.size :> Size.t) = 0
  then []
  else (
    match dest.data, src.data with
    | Dest.Op.Addr _, Dest.Op.Addr _ ->
      let size = src.size in
      let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
      [ Dest.Mov { dest = swap; src; size }; Dest.Cast { dest; src = swap } ]
    | _ -> [ Dest.Cast { dest; src } ])
;;

let safe_add (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Addr _, Dest.Op.Addr _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.Add { dest; src = swap; size } ]
  | _ -> [ Dest.Add { dest; src; size } ]
;;

let safe_sub (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Addr _, Dest.Op.Addr _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.Sub { dest; src = swap; size } ]
  | _ -> [ Sub { dest; src; size } ]
;;

let safe_and (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Addr _, Dest.Op.Addr _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.AND { dest; src = swap; size } ]
  | _ -> [ AND { dest; src; size } ]
;;

let safe_or (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Addr _, Dest.Op.Addr _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.OR { dest; src = swap; size } ]
  | _ -> [ OR { dest; src; size } ]
;;

let safe_xor (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Addr _, Dest.Op.Addr _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.XOR { dest; src = swap; size } ]
  | _ -> [ XOR { dest; src; size } ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sal (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match src.data with
  | Reg _ | Dest.Op.Addr _ ->
    let ecx = Reg_logic.RCX |> Dest.Op.of_reg |> Dest.Sop.wrap `BYTE in
    (* when src is register/memory, SAL can only use %cl to shift. *)
    Dest.Cast { dest = ecx; src } :: [ SAL { dest; src = ecx; size } ]
  | Imm _ -> [ SAL { dest; src; size = `BYTE } ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sar (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match src.data with
  | Reg _ | Dest.Op.Addr _ ->
    let ecx = Reg_logic.RCX |> Dest.Op.of_reg |> Dest.Sop.wrap `BYTE in
    (* when src is register/memory, SAR can only use %cl to shift. *)
    Dest.Cast { dest = ecx; src } :: [ SAR { dest; src = ecx; size } ]
  | Imm _ -> [ SAR { dest; src; size = `BYTE } ]
;;

let safe_ret (size : Size.primitive) =
  (* insts = [ "mov %rbp, %rsp"; "pop %rbp"; "ret" ] *)
  let rbp = Reg_logic.RBP |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  let rsp = Reg_logic.RSP |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  [ Dest.Mov { dest = rsp; src = rbp; size }; Dest.Pop { var = rbp }; Dest.Ret ]
;;

(* Prepare for conditional jump. *)
let safe_cmp
    (lhs : Dest.Sop.t)
    (rhs : Dest.Sop.t)
    (size : Size.primitive)
    (swap : Dest.Sop.t)
  =
  match lhs.data, rhs.data with
  | Dest.Op.Addr _, Dest.Op.Addr _ ->
    [ Dest.Mov { dest = swap; src = lhs; size }; Dest.Cmp { lhs = swap; rhs; size } ]
  | _ -> [ Dest.Cmp { lhs; rhs; size } ]
;;

let gen_x86_relop_bin
    (op : Src.binop)
    (dest : Dest.Sop.t)
    (lhs : Dest.Sop.t)
    (rhs : Dest.Sop.t)
    (swap : Dest.Sop.t)
  =
  let al = Reg_logic.RAX |> Dest.Op.of_reg |> Dest.Sop.wrap `BYTE in
  let rax = Reg_logic.RAX |> Dest.Op.of_reg |> Dest.Sop.wrap `QWORD in
  let set_inst =
    match op with
    | Less -> [ Dest.SETL { dest = al; size = `BYTE } ]
    | Less_eq -> [ Dest.SETLE { dest = al; size = `BYTE } ]
    | Greater -> [ Dest.SETG { dest = al; size = `BYTE } ]
    | Greater_eq -> [ Dest.SETGE { dest = al; size = `BYTE } ]
    | Equal_eq -> [ Dest.SETE { dest = al; size = `BYTE } ]
    | Not_eq -> [ Dest.SETNE { dest = al; size = `BYTE } ]
    | _ -> failwith "relop cannot handle other op"
  in
  let size = lhs.size in
  let cmp_inst = safe_cmp lhs rhs size swap in
  [ Dest.XOR { dest = rax; src = rax; size } ] @ cmp_inst @ set_inst @ safe_cast dest rax
;;

let gen_x86_inst_bin
    (op : Src.binop)
    (dest : Dest.Sop.t)
    (lhs : Dest.Sop.t)
    (rhs : Dest.Sop.t)
    (swap : Reg_logic.t)
  =
  let size = dest.size in
  let rax = Reg_logic.RAX |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  let swap = swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  match op with
  | Plus -> safe_mov dest lhs size @ safe_add dest rhs size
  | Minus -> safe_mov dest lhs size @ safe_sub dest rhs size
  | Times ->
    [ Dest.Mov { dest = rax; src = lhs; size }
    ; Dest.Mul { src = rhs; dest = rax; size }
    ; Dest.Mov { dest; src = rax; size }
    ]
  | Divided_by ->
    (* Notice that lhs and rhs may be allocated on rdx. 
     * So we use reg_swap to avoid override in the rdx <- 0. *)
    [ Dest.Mov { dest = rax; src = lhs; size }
    ; Dest.Mov { dest = swap; src = rhs; size }
    ; Dest.Cvt { size }
    ; Dest.Div { src = swap; size }
    ; Dest.Mov { dest; src = rax; size }
    ]
  | Modulo ->
    let rdx = Reg_logic.RDX |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = rax; src = lhs; size }
    ; Dest.Mov { dest = swap; src = rhs; size }
    ; Dest.Cvt { size }
    ; Dest.Div { src = swap; size }
    ; Dest.Mov { dest; src = rdx; size }
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
    (res : Dest.instr list)
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
      let dest_insts, dest = trans_operand bin_op.dest reg_alloc_info in
      let lhs_insts, lhs = trans_operand bin_op.lhs reg_alloc_info in
      let rhs_insts, rhs = trans_operand bin_op.rhs reg_alloc_info in
      let insts = gen_x86_inst_bin bin_op.op dest lhs rhs reg_swap in
      let insts_rev = List.rev (dest_insts @ lhs_insts @ rhs_insts @ insts) in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Cast cast ->
      let dest_oprd = Src.St.to_Sop cast.dest in
      let src_oprd = Src.St.to_Sop cast.src in
      let dest_insts, dest = trans_operand dest_oprd reg_alloc_info in
      let src_insts, src = trans_operand src_oprd reg_alloc_info in
      let insts = safe_cast dest src in
      let insts_rev = List.rev (dest_insts @ src_insts @ insts) in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Mov mov ->
      let dest_insts, dest = trans_operand mov.dest reg_alloc_info in
      let src_insts, src = trans_operand mov.src reg_alloc_info in
      let size = dest.size in
      let insts = safe_mov dest src size in
      let insts_rev = List.rev (dest_insts @ src_insts @ insts) in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Ret _ ->
      let insts = safe_ret `QWORD in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Label l -> _codegen_w_reg_rev (Dest.Label l.label :: res) t reg_alloc_info reg_swap
    | Jump jp -> _codegen_w_reg_rev (Dest.Jump jp.target :: res) t reg_alloc_info reg_swap
    | CJump cjp ->
      let lhs_insts, lhs = trans_operand cjp.lhs reg_alloc_info in
      let rhs_insts, rhs = trans_operand cjp.rhs reg_alloc_info in
      let size = lhs.size in
      let target_true = cjp.target_true in
      let target_false = cjp.target_false in
      let swap = reg_swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
      let cmp_inst = safe_cmp lhs rhs size swap in
      let cmp_inst_rev = List.rev (lhs_insts @ rhs_insts @ cmp_inst) in
      let cjp_inst =
        match cjp.op with
        | Equal_eq -> Dest.JE target_true
        | Greater -> Dest.JG target_true
        | Greater_eq -> Dest.JGE target_true
        | Less -> Dest.JL target_true
        | Less_eq -> Dest.JLE target_true
        | Not_eq -> Dest.JNE target_true
        | _ -> failwith "conditional jump op should can only be relop."
      in
      let jp = Dest.Jump target_false in
      _codegen_w_reg_rev
        (([ jp; cjp_inst ] @ cmp_inst_rev) @ res)
        t
        reg_alloc_info
        reg_swap
    | Push push ->
      let var_insts, var = trans_operand push.var reg_alloc_info in
      let inst_rev = Dest.Push { var } :: var_insts in
      _codegen_w_reg_rev (inst_rev @ res) t reg_alloc_info reg_swap
    | Pop pop ->
      let var_insts, var = trans_operand pop.var reg_alloc_info in
      let inst_rev = Dest.Pop { var } :: var_insts in
      _codegen_w_reg_rev (inst_rev @ res) t reg_alloc_info reg_swap
    | Fcall fcall ->
      let scope = fcall.scope in
      let func_name = fcall.func_name in
      let inst = Dest.Fcall { func_name; scope } in
      _codegen_w_reg_rev (inst :: res) t reg_alloc_info reg_swap
    | Load load ->
      let src = trans_mem load.src in
      let size = load.src.size in
      let src_oprd = Dest.Mem.to_Sop src in
      let dest_oprd = Src.St.to_Sop load.dest in
      let dest_insts, dest = trans_operand dest_oprd reg_alloc_info in
      let insts_rev =
        match dest.data with
        | Dest.Op.Addr _ ->
          let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
          [ Dest.Mov { dest; src = swap; size }
          ; Dest.Mov { dest = swap; src = src_oprd; size }
          ]
          @ dest_insts
        | _ -> Dest.Mov { dest; src = src_oprd; size } :: dest_insts
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Store store ->
      let dest = trans_mem store.dest in
      let dest_oprd = Dest.Mem.to_Sop dest in
      let src_insts, src = trans_operand store.src reg_alloc_info in
      let size = src.size in
      let insts_rev =
        match src.data with
        | Dest.Op.Addr _ ->
          let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
          [ Dest.Mov { dest = dest_oprd; src = swap; size }
          ; Dest.Mov { dest = swap; src; size }
          ]
          @ src_insts
        | _ -> Dest.Mov { dest = dest_oprd; src; size } :: src_insts
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Directive _ | Comment _ -> _codegen_w_reg_rev res t reg_alloc_info reg_swap)
;;

let abort_handler = [ Dest.Label abort_label; Dest.Abort ]

let gen (fdefn : Src.fdefn) (reg_alloc_info : (IG.Vertex.t * Regalloc.dest) option list)
    : Dest.instr list
  =
  let size = `QWORD in
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
  let mem_cnt = 8 * Reg_spill.get_tot () in
  let mem_cnt = if mem_cnt % 16 = 0 then mem_cnt else mem_cnt + 8 in
  let mem_cnt_oprd = mem_cnt |> Int64.of_int |> Dest.Op.of_imm |> Dest.Sop.wrap size in
  (* store rbp and rsp at the beginning of each function *)
  let rbp = rbp |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  let rsp = rsp |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  let scope = (fdefn.scope :> [ `C0 | `Internal | `External ]) in
  [ Dest.Fname { name = fdefn.func_name; scope }
  ; Dest.Push { var = rbp }
  ; Dest.Mov { dest = rbp; src = rsp; size }
  ; Dest.Sub { src = mem_cnt_oprd; dest = rsp; size }
  ]
  @ res
;;
