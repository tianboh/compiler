(* L4 x86 abstract assembly code
 * Transfrom from Ir_tree Inst to x86 Inst with convention
 * This is done by providing each instruction with different
 * defines/uses operand. Compared with Ir_tree Inst, this
 * layer has extra register type for operand. 
 *
 * For each function, provide prologue and epilogue.
 * prologue and epilogue will save and restore callee-saved
 * registers, rsp and rbp. Function return will jump to 
 * epilogue and then return to make sure frame is properly
 * restored.
 *
 * For each function call, caller will use move temp, reg to
 * follow x86 calling convention. Caller-saved registers are
 * properly defined in the fcall statements. So that it is
 * preferred to be used within the function.
 *
 * In a word, caller and callee saved registers are properly
 * defined through defines/uses info. Then regalloc alg will
 * makes sure they will be the same state after function call.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
open Core
module Src = Quads.Inst
module Dest = Inst
module Reg = Var.X86_reg.Logic
module Sreg = Var.X86_reg.Hard
module Size = Var.Size
module AbsCFG = Analysis_cfg.Impt.Wrapper (Inst)
module AbsDom = Analysis_dominator.Impt.Make (AbsCFG)
module AbsSSA_internal = Ssa.Impt.Make (Inst) (AbsCFG) (AbsDom)

module AbsSSA = struct
  include AbsSSA_internal

  type instr = Inst.instr
  type cfg_bbmap = AbsCFG.bbmap
  type cfg_set = AbsCFG.set
end

module AbsADCE = Adce.Impt.Make (Inst) (AbsSSA)
open Inst
open Reg

type instr = Dest.instr

let trans_binop (op : Src.binop) : Dest.binop =
  match op with
  | Plus -> Plus
  | Minus -> Minus
  | Times -> Times
  | Divided_by -> Divided_by
  | Modulo -> Modulo
  | And -> And
  | Or -> Or
  | Xor -> Xor
  | Right_shift -> Right_shift
  | Left_shift -> Left_shift
  | Equal_eq -> Equal_eq
  | Greater -> Greater
  | Greater_eq -> Greater_eq
  | Less -> Less
  | Less_eq -> Less_eq
  | Not_eq -> Not_eq

let trans_operand (operand : Src.Sop.t) : Dest.Sop.t =
  let size = operand.size in
  match operand.data with
  | Imm i -> i |> Dest.Op.of_imm |> Dest.Sop.wrap size
  | Temp t -> t |> Dest.Op.of_temp |> Dest.Sop.wrap size

let get_size (operand : Src.Sop.t) : Size.primitive = operand.size
let get_size' (operand : Dest.Sop.t) : Size.primitive = operand.size

(* Generate x86 instr with binop convention *)
let[@warning "-8"] gen_binop_rev (Src.Binop bin) =
  let op, dest, lhs, rhs =
    ( trans_binop bin.op,
      trans_operand (Src.t_to_Sop bin.dest),
      trans_operand bin.lhs,
      trans_operand bin.rhs )
  in
  [ Dest.Binop { op; dest; lhs; rhs } ]

let[@warning "-8"] gen_move_rev (Src.Mov move) =
  let dest, src =
    (trans_operand (Src.t_to_Sop move.dest), trans_operand move.src)
  in
  [ Dest.Mov { dest; src } ]

let[@warning "-8"] gen_jump_rev (Src.Jump jump) =
  [ Dest.Jump { target = jump.target } ]

let[@warning "-8"] gen_cjump_rev (Src.CJump cjump) =
  let lhs, rhs = (trans_operand cjump.lhs, trans_operand cjump.rhs) in
  let op = trans_binop cjump.op in
  let target_true = cjump.target_true in
  let target_false = cjump.target_false in
  [ Dest.CJump { lhs; op; rhs; target_true; target_false } ]

let[@warning "-8"] gen_ret_rev (Src.Ret ret) (exit_label : Label.t) =
  let mov =
    match ret.var with
    | None -> []
    | Some var ->
        let src = trans_operand var in
        let size = get_size' src in
        let dest = RAX |> Dest.Op.of_reg |> Dest.Sop.wrap size in
        [ Dest.Mov { dest; src } ]
  in
  Dest.Jump { target = exit_label } :: mov

let param_map (idx : int) : Dest.Op.t =
  let open Base.Int64 in
  match idx with
  | 0 -> Dest.Op.of_reg RDI
  | 1 -> Dest.Op.of_reg RSI
  | 2 -> Dest.Op.of_reg RDX
  | 3 -> Dest.Op.of_reg RCX
  | 4 -> Dest.Op.of_reg R8
  | 5 -> Dest.Op.of_reg R9
  | _ -> Dest.Op.of_af (Int64.of_int idx - 5L)

let set_size (operand : Dest.Sop.t) (size : Size.primitive) : Dest.Sop.t =
  { operand with size }

(* alignment for %RSP. %RSP is multiple of 16 when calling function *)
let gen_align (rsp : Sreg.t) : Dest.instr =
  let rhs = 8L |> Dest.Op.of_imm |> Dest.Sop.wrap `QWORD in
  let rsp = rsp.data |> Dest.Op.of_reg |> Dest.Sop.wrap rsp.size in
  Dest.Binop { op = Dest.Minus; dest = rsp; lhs = rsp; rhs }

let gen_release (rsp : Dest.Sop.t) (num_par : int) (align_size : int) =
  let rhs =
    ((num_par - 6) * 8) + align_size
    |> Int64.of_int |> Dest.Op.of_imm |> Dest.Sop.wrap `QWORD
  in
  Dest.Binop { op = Dest.Plus; dest = rsp; lhs = rsp; rhs }

let gen_param_pass (params : Src.Sop.t list) : Dest.instr list =
  List.mapi params ~f:(fun idx arg ->
      let src = trans_operand arg in
      let size = get_size' src in
      if idx < 6 then
        let dest = param_map idx in
        Dest.Mov { dest = Dest.Sop.wrap size dest; src }
      else Dest.Push { var = src })

let gen_fret (dest : Dest.Sop.t) =
  let size = dest.size in
  let src : Dest.Sop.t = { data = Dest.Op.of_reg RAX; size } in
  Dest.Mov { dest; src }

(* Generate x86 instr with function call convention *)
let[@warning "-8"] gen_fcall_rev (Src.Fcall fcall) =
  let func_name = fcall.func_name in
  let dest =
    match fcall.dest with
    | Some dest -> Some (trans_operand (Src.t_to_Sop dest))
    | None -> None
  in
  let args = List.map fcall.args ~f:(fun arg -> trans_operand arg) in
  let par_insts = gen_param_pass fcall.args in
  let fcall = Dest.Fcall { func_name; args } in
  let num_par = List.length par_insts in
  let need_align = num_par > 6 && num_par % 2 = 1 in
  let insts =
    match dest with
    | None -> fcall :: par_insts
    | Some dest ->
        let ret = gen_fret dest in
        ret :: fcall :: par_insts
  in
  let insts =
    if need_align then
      let rsp = RSP |> Sreg.wrap `QWORD in
      let align = gen_align rsp in
      insts @ [ align ]
    else insts
  in
  let align_size = if need_align then 8 else 0 in
  let rsp_oprd = RSP |> Dest.Op.of_reg |> Dest.Sop.wrap `QWORD in
  let release = gen_release rsp_oprd num_par align_size in
  if num_par > 6 then release :: insts else insts

(* Move from source operand to destination register *)
let gen_move_rev' (dest : Reg.t) (src : Src.Sop.t) :
    Dest.instr * Sreg.t * Dest.Sop.t =
  let size = `QWORD in
  let reg = Sreg.wrap size dest in
  let dest = dest |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  let src = trans_operand src in
  (Dest.Mov { dest; src }, reg, src)

let[@warning "-8"] gen_load_rev (Src.Load load) : Dest.instr list =
  let size = load.dest.size in
  let base_quad, index_quad, scale, disp = Src.Addr.get load.src.data in
  let base_mov, base_reg, _ = gen_move_rev' heap_base base_quad in
  match index_quad with
  | Some index_quad' ->
      let index_mov, index_reg, _ = gen_move_rev' heap_index index_quad' in
      let src =
        Dest.Addr.of_bisd base_reg.data (Some index_reg.data) scale disp
        |> Dest.Mem.wrap size
      in
      let dest = load.dest in
      let load = Dest.Load { dest; src } in
      [ load; index_mov; base_mov ]
  | None ->
      let src =
        Dest.Addr.of_bisd base_reg.data None scale disp |> Dest.Mem.wrap size
      in
      let dest = load.dest in
      let load = Dest.Load { dest; src } in
      [ load; base_mov ]

let[@warning "-8"] gen_store_rev (Src.Store store) : Dest.instr list =
  let size = store.dest.size in
  let base_quad, index_quad, scale, disp = Src.Addr.get store.dest.data in
  let base_mov, base_reg, _ = gen_move_rev' heap_base base_quad in
  match index_quad with
  | Some index_quad' ->
      let offset_mov, index_reg, _ = gen_move_rev' heap_index index_quad' in
      let dest =
        Dest.Addr.of_bisd base_reg.data (Some index_reg.data) scale disp
        |> Dest.Mem.wrap size
      in
      let src = trans_operand store.src in
      let store = Dest.Store { dest; src } in
      [ store; offset_mov; base_mov ]
  | None ->
      let dest =
        Dest.Addr.of_bisd base_reg.data None scale disp |> Dest.Mem.wrap size
      in
      let src = trans_operand store.src in
      let store = Dest.Store { dest; src } in
      [ store; base_mov ]

let[@warning "-8"] gen_cast_rev (Src.Cast cast) : Dest.instr list =
  let dest = cast.dest in
  let src = cast.src in
  let inst = Dest.Cast { dest; src } in
  [ inst ]

(* Generate instruction with x86 conventions *)
let rec gen_body (program : Src.instr list) (res : Dest.instr list)
    (exit_label : Label.t) : Dest.instr list =
  match program with
  | [] -> List.rev res
  | h :: t ->
      let inst =
        match h with
        | Binop bin -> gen_binop_rev (Binop bin)
        | Cast cast -> gen_cast_rev (Cast cast)
        | Mov move -> gen_move_rev (Mov move)
        | Jump jump -> gen_jump_rev (Jump jump)
        | CJump cjump -> gen_cjump_rev (CJump cjump)
        | Ret ret -> gen_ret_rev (Ret ret) exit_label
        | Label l -> [ Dest.Label { label = l } ]
        | Directive dir -> [ Dest.Directive dir ]
        | Comment cmt -> [ Dest.Comment cmt ]
        | Fcall fcall -> gen_fcall_rev (Fcall fcall)
        | Load load -> gen_load_rev (Load load)
        | Store store -> gen_store_rev (Store store)
      in
      gen_body t (inst @ res) exit_label

(* Generate move instruction for callee-saved register of define info *)
let save_callee () : Dest.instr list =
  let size = `QWORD in
  List.fold callee_saved ~init:[] ~f:(fun acc r ->
      let t = Temp.create size |> Op.of_temp in
      let dest = Dest.Sop.wrap size t in
      let src = r |> Op.of_reg |> Dest.Sop.wrap size in
      let mov = Dest.Mov { dest; src } in
      mov :: acc)
  |> List.rev

(* Generate move instruction for callee-saved register of uses info 
 * Then, return the function *)
let gen_epilogue (prologue : Dest.instr list) : Dest.instr list =
  let restore =
    List.rev prologue
    |> List.map ~f:(fun inst ->
           let dest, src =
             match inst with
             | Dest.Mov mov -> (mov.src, mov.dest)
             | _ -> failwith "mov missing"
           in
           Dest.Mov { dest; src })
  in
  let ret = Dest.Ret in
  restore @ [ ret ]

(* Generate assigning parameter passing code. Parameters are passed through
 * registers(first 6 parameters) or memories(rest parameters) during function call. *)
let gen_pars (pars : Temp.t list) : Dest.instr list =
  List.mapi pars ~f:(fun idx par ->
      let src = param_map idx in
      let dest = par |> Op.of_temp |> Sop.wrap par.size in
      if idx < 6 then [ Mov { dest; src = { data = src; size = par.size } } ]
      else
        let temp_sop =
          Temp.create par.size |> Op.of_temp |> Sop.wrap par.size
        in
        let temp_mem = Sop.wrap par.size src in
        let load = Mov { dest = temp_sop; src = temp_mem } in
        [ load; Mov { dest; src = temp_sop } ])
  |> List.concat

let gen_section (prefix : string) (fname : Symbol.t) (content : Dest.instr list)
    : Dest.section * Label.t =
  let label = Label.label (Some (prefix ^ Symbol.name fname)) in
  let name = Dest.Label { label } in
  ({ name; content }, label)

let gen_program prologue body epilogue : instr list =
  let prologue = prologue.name :: prologue.content in
  let body = body.name :: body.content in
  let epilogue = epilogue.name :: epilogue.content in
  prologue @ body @ epilogue

(* Let register allocation alg handle prologue and epilogue. *)
let rec gen (program : Src.program) (res : Dest.program) : Dest.program =
  match program with
  | [] -> List.rev res
  | h :: t ->
      let pars = gen_pars h.pars in
      let save = save_callee () in
      let epilogue_content = gen_epilogue save in
      let prologue, _ = gen_section "pro_" h.func_name (save @ pars) in
      let epilogue, exit_label =
        gen_section "epi_" h.func_name epilogue_content
      in
      let body_content = gen_body h.body [] exit_label in
      let body, _ = gen_section "body_" h.func_name body_content in
      let prog = gen_program prologue body epilogue in
      (* let bbmap, label_list = AbsCFG.build_bb prog in
      let new_bbmap = AbsSSA.from_ssa ssa in
      let new_prog = AbsCFG.to_instrs new_bbmap label_list in *)
      let bbmap, label_list = AbsCFG.build_bb prog in
      let ssa = AbsSSA.to_ssa bbmap in
      let ssa_adce = AbsADCE.run ssa in
      let new_bbmap = AbsSSA.from_ssa ssa_adce in
      let new_prog = AbsCFG.to_instrs new_bbmap label_list in
      (* let prog = gen_program prologue body epilogue in *)
      let fdefn = { func_name = Symbol.name h.func_name; body = new_prog } in
      gen t (fdefn :: res)
