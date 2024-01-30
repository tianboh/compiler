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
    : Dest.Sop.t
  =
  let size = operand.size in
  match operand.data with
  | Temp t ->
    let dest = IG.Vertex.Map.find_exn reg_alloc_info (IG.Vertex.T.Temp t) in
    (match dest with
    | Regalloc.Reg r -> Dest.Op.of_reg r |> Dest.Sop.wrap size
    | Regalloc.Spill s ->
      let id = Reg_spill.get_idx1 s in
      -id |> Int64.of_int |> Dest.Op.of_stack Reg_logic.RBP |> Dest.Sop.wrap size)
  | Imm i -> Dest.Op.of_imm i |> Dest.Sop.wrap size
  | Reg r -> Dest.Op.of_reg r |> Dest.Sop.wrap size
  | Above_frame af ->
    (* bias for push %rbp at callee *)
    let push_bias = 1 in
    let idx = Base.Int64.( + ) (Int64.of_int push_bias) af in
    idx |> Dest.Op.of_stack Reg_logic.RBP |> Dest.Sop.wrap size
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
let abort_label = Util.Label.Handler.sigabrt

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_mov (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Stack _, Dest.Op.Stack _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.Mov { dest; src = swap; size } ]
  | _ -> [ Mov { dest; src; size } ]
;;

(* Now we provide safe instruction to avoid source and destination are both memory. *)
let safe_cast (dest : Dest.Sop.t) (src : Dest.Sop.t) =
  if Size.compare (dest.size :> Size.t) (src.size :> Size.t) = 0
  then [ Dest.Mov { dest; src; size = dest.size } ]
  else (
    match dest.data, src.data with
    | Dest.Op.Stack _, Dest.Op.Stack _ ->
      let size = src.size in
      let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
      let swap_ext = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap dest.size in
      [ Dest.Mov { dest = swap; src; size }
      ; Dest.Cast { dest = swap_ext; src = swap }
      ; Dest.Mov { dest; src = swap_ext; size = dest.size }
      ]
    | Dest.Op.Stack _, Dest.Op.Reg r ->
      let r_ext = r |> Dest.Op.of_reg |> Dest.Sop.wrap dest.size in
      [ Dest.Cast { dest = r_ext; src = Dest.Op.of_reg r |> Dest.Sop.wrap src.size }
      ; Dest.Mov { dest; src = r_ext; size = dest.size }
      ]
    | _ -> [ Dest.Cast { dest; src } ])
;;

let safe_add (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Stack _, Dest.Op.Stack _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.Add { dest; src = swap; size } ]
  | _ -> [ Dest.Add { dest; src; size } ]
;;

let safe_sub (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Stack _, Dest.Op.Stack _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.Sub { dest; src = swap; size } ]
  | _ -> [ Sub { dest; src; size } ]
;;

let safe_and (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Stack _, Dest.Op.Stack _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.AND { dest; src = swap; size } ]
  | _ -> [ AND { dest; src; size } ]
;;

let safe_or (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Stack _, Dest.Op.Stack _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.OR { dest; src = swap; size } ]
  | _ -> [ OR { dest; src; size } ]
;;

let safe_xor (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match dest.data, src.data with
  | Dest.Op.Stack _, Dest.Op.Stack _ ->
    let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
    [ Dest.Mov { dest = swap; src; size }; Dest.XOR { dest; src = swap; size } ]
  | _ -> [ XOR { dest; src; size } ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sal (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match src.data with
  | Reg _ | Dest.Op.Stack _ | Dest.Op.Addr _ ->
    let ecx = Reg_logic.RCX |> Dest.Op.of_reg |> Dest.Sop.wrap `BYTE in
    (* when src is register/memory, SAL can only use %cl to shift. *)
    [ Dest.Cast { dest = ecx; src }; SAL { dest; src = ecx; size } ]
  | Imm _ -> [ SAL { dest; src; size = `BYTE } ]
;;

(* Remember that ecx is preserved during register allocation.
 * So we can move src to ecx without store ecx value. *)
let safe_sar (dest : Dest.Sop.t) (src : Dest.Sop.t) (size : Size.primitive) =
  match src.data with
  | Reg _ | Dest.Op.Stack _ | Dest.Op.Addr _ ->
    let ecx = Reg_logic.RCX |> Dest.Op.of_reg |> Dest.Sop.wrap `BYTE in
    (* when src is register/memory, SAR can only use %cl to shift. *)
    [ Dest.Cast { dest = ecx; src }; SAR { dest; src = ecx; size } ]
  | Imm _ -> [ SAR { dest; src; size = `BYTE } ]
;;

let safe_ret () =
  let size = `QWORD in
  let rsp = Reg_logic.RSP |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  let rbp = Reg_logic.RBP |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  [ Dest.Mov { dest = rsp; src = rbp; size }; Pop { var = rbp }; Dest.Ret ]
;;

(* Prepare for conditional jump. *)
let safe_cmp
    (lhs : Dest.Sop.t)
    (rhs : Dest.Sop.t)
    (size : Size.primitive)
    (swap : Dest.Sop.t)
  =
  match lhs.data, rhs.data with
  | Dest.Op.Stack _, Dest.Op.Stack _ ->
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
    (* printf "src:%s\n" (Src.pp_inst h); *)
    (match h with
    | Binop bin_op ->
      let dest = trans_operand bin_op.dest reg_alloc_info in
      let lhs = trans_operand bin_op.lhs reg_alloc_info in
      let rhs = trans_operand bin_op.rhs reg_alloc_info in
      let insts = gen_x86_inst_bin bin_op.op dest lhs rhs reg_swap in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Cast cast ->
      let dest_oprd = Src.St.to_Sop cast.dest in
      let src_oprd = Src.St.to_Sop cast.src in
      let dest = trans_operand dest_oprd reg_alloc_info in
      let src = trans_operand src_oprd reg_alloc_info in
      let insts = safe_cast dest src in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Mov mov ->
      let dest = trans_operand mov.dest reg_alloc_info in
      let src = trans_operand mov.src reg_alloc_info in
      let size = dest.size in
      let insts = safe_mov dest src size in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Ret _ ->
      let insts = safe_ret () in
      let insts_rev = List.rev insts in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Label l -> _codegen_w_reg_rev (Dest.Label l.label :: res) t reg_alloc_info reg_swap
    | Jump jp -> _codegen_w_reg_rev (Dest.Jump jp.target :: res) t reg_alloc_info reg_swap
    | CJump cjp ->
      let lhs = trans_operand cjp.lhs reg_alloc_info in
      let rhs = trans_operand cjp.rhs reg_alloc_info in
      let size = lhs.size in
      let target_true = cjp.target_true in
      let target_false = cjp.target_false in
      let swap = reg_swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
      let cmp_inst = safe_cmp lhs rhs size swap in
      let cmp_inst_rev = List.rev cmp_inst in
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
      let var = trans_operand push.var reg_alloc_info in
      let inst_rev = Dest.Push { var } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
    | Pop pop ->
      let var = trans_operand pop.var reg_alloc_info in
      let inst_rev = Dest.Pop { var } in
      _codegen_w_reg_rev (inst_rev :: res) t reg_alloc_info reg_swap
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
      let dest = trans_operand dest_oprd reg_alloc_info in
      let insts_rev =
        match dest.data with
        | Dest.Op.Stack _ ->
          let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
          [ Dest.Mov { dest; src = swap; size }
          ; Dest.Mov { dest = swap; src = src_oprd; size }
          ]
        | _ -> [ Dest.Mov { dest; src = src_oprd; size } ]
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Store store ->
      let dest = trans_mem store.dest in
      let dest_oprd = Dest.Mem.to_Sop dest in
      let src = trans_operand store.src reg_alloc_info in
      let size = src.size in
      let insts_rev =
        match src.data with
        | Dest.Op.Stack _ ->
          let swap = Reg_logic.swap |> Dest.Op.of_reg |> Dest.Sop.wrap size in
          [ Dest.Mov { dest = dest_oprd; src = swap; size }
          ; Dest.Mov { dest = swap; src; size }
          ]
        | _ -> [ Dest.Mov { dest = dest_oprd; src; size } ]
      in
      _codegen_w_reg_rev (insts_rev @ res) t reg_alloc_info reg_swap
    | Directive _ | Comment _ -> _codegen_w_reg_rev res t reg_alloc_info reg_swap)
;;

let abort_handler = [ Dest.Label abort_label; Dest.Abort ]

(* Transform operand with stack to address. *)
let rec transform (insts_rev : Dest.instr list) (acc : Dest.instr list) : Dest.instr list =
  let helper (sop : Dest.Sop.t) : Dest.instr list * Dest.Sop.t =
    match sop.data with
    | Dest.Op.Stack s ->
      let reg_size = `QWORD in
      let base = Reg_logic.RBP |> Reg_hard.wrap reg_size in
      let disp = Base.Int64.( * ) 8L s.index in
      let addr = Dest.Op.of_addr base None None (Some disp) in
      let mem = Dest.Sop.wrap sop.size addr in
      [], mem
    | _ -> [], sop
  in
  match insts_rev with
  | [] -> acc
  | h :: t ->
    let acc =
      match h with
      | Add add ->
        let src_inst, src = helper add.src in
        let dest_inst, dest = helper add.dest in
        src_inst @ dest_inst @ [ Dest.Add { add with dest; src } ] @ acc
      | Sub sub ->
        let src_inst, src = helper sub.src in
        let dest_inst, dest = helper sub.dest in
        src_inst @ dest_inst @ [ Dest.Sub { sub with dest; src } ] @ acc
      | Mul mul ->
        let src_inst, src = helper mul.src in
        let dest_inst, dest = helper mul.dest in
        src_inst @ dest_inst @ [ Dest.Mul { mul with dest; src } ] @ acc
      | Div div ->
        let src_inst, src = helper div.src in
        src_inst @ [ Dest.Div { div with src } ] @ acc
      | Mod m ->
        let src_inst, src = helper m.src in
        src_inst @ [ Dest.Mod { m with src } ] @ acc
      | Cast cast ->
        let src_inst, src = helper cast.src in
        let dest_inst, dest = helper cast.dest in
        src_inst @ dest_inst @ [ Dest.Cast { dest; src } ] @ acc
      | Mov mov ->
        let src_inst, src = helper mov.src in
        let dest_inst, dest = helper mov.dest in
        src_inst @ dest_inst @ [ Dest.Mov { mov with dest; src } ] @ acc
      | Cvt cvt -> Cvt cvt :: acc
      | Ret -> Ret :: acc
      | Pop pop ->
        let var_inst, var = helper pop.var in
        var_inst @ [ Dest.Pop { var } ] @ acc
      | Push push ->
        let var_inst, var = helper push.var in
        var_inst @ [ Dest.Push { var } ] @ acc
      | Cmp cmp ->
        let lhs_inst, lhs = helper cmp.lhs in
        let rhs_inst, rhs = helper cmp.rhs in
        lhs_inst @ rhs_inst @ [ Dest.Cmp { cmp with lhs; rhs } ] @ acc
      | LAHF -> LAHF :: acc
      | SAHF -> SAHF :: acc
      | Label l -> Label l :: acc
      | Jump j -> Jump j :: acc
      | JE je -> JE je :: acc
      | JNE jne -> JNE jne :: acc
      | JL jl -> JL jl :: acc
      | JLE jle -> JLE jle :: acc
      | JG jg -> JG jg :: acc
      | JGE jge -> JGE jge :: acc
      | SETE sete ->
        let dest_inst, dest = helper sete.dest in
        dest_inst @ [ Dest.SETE { sete with dest } ] @ acc
      | SETNE setne ->
        let dest_inst, dest = helper setne.dest in
        dest_inst @ [ Dest.SETNE { setne with dest } ] @ acc
      | SETL setl ->
        let dest_inst, dest = helper setl.dest in
        dest_inst @ [ Dest.SETL { setl with dest } ] @ acc
      | SETLE setle ->
        let dest_inst, dest = helper setle.dest in
        dest_inst @ [ Dest.SETLE { setle with dest } ] @ acc
      | SETG setg ->
        let dest_inst, dest = helper setg.dest in
        dest_inst @ [ Dest.SETG { setg with dest } ] @ acc
      | SETGE setge ->
        let dest_inst, dest = helper setge.dest in
        dest_inst @ [ Dest.SETGE { setge with dest } ] @ acc
      | AND a ->
        let src_inst, src = helper a.src in
        let dest_inst, dest = helper a.dest in
        src_inst @ dest_inst @ [ Dest.AND { a with dest; src } ] @ acc
      | OR o ->
        let src_inst, src = helper o.src in
        let dest_inst, dest = helper o.dest in
        src_inst @ dest_inst @ [ Dest.OR { o with dest; src } ] @ acc
      | XOR x ->
        let src_inst, src = helper x.src in
        let dest_inst, dest = helper x.dest in
        src_inst @ dest_inst @ [ Dest.XOR { x with dest; src } ] @ acc
      | SAL sal ->
        let src_inst, src = helper sal.src in
        let dest_inst, dest = helper sal.dest in
        src_inst @ dest_inst @ [ Dest.SAL { sal with dest; src } ] @ acc
      | SAR sar ->
        let src_inst, src = helper sar.src in
        let dest_inst, dest = helper sar.dest in
        src_inst @ dest_inst @ [ Dest.SAR { sar with dest; src } ] @ acc
      | Fcall fcall -> Fcall fcall :: acc
      | Abort -> Abort :: acc
      | Fname f -> Fname f :: acc
      | GDB g -> GDB g :: acc
      | Directive d -> Directive d :: acc
      | Comment c -> Comment c :: acc
    in
    transform t acc
;;

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
  let mem_cnt = 8 * Reg_spill.get_tot () in
  let mem_cnt = if mem_cnt % 16 = 0 then mem_cnt else mem_cnt + 8 in
  let mem_cnt_oprd = mem_cnt |> Int64.of_int |> Dest.Op.of_imm |> Dest.Sop.wrap size in
  let res_rev = _codegen_w_reg_rev [] fdefn.body reg_alloc reg_swap in
  let res = transform res_rev [] in
  let rsp = rsp |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  let rbp = rbp |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  [ Dest.Fname { name = fdefn.func_name; scope = `C0 }
  ; Push { var = rbp }
  ; Mov { dest = rbp; src = rsp; size }
  ; Sub { src = mem_cnt_oprd; dest = rsp; size }
  ]
  @ res
;;
