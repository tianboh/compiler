(* L4 x86 abstract assembly code
 * Transfrom from Ir_tree Inst to x86 Inst with convention
 * This is done by providing each instruction with different
 * defines/uses operand. Compared with Ir_tree Inst, this
 * layer has extra register type for operand. 
 *
 * For each function, we provide prologue and epilogue.
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
open Inst
open Reg

type line = Dest.line
type instr = Dest.instr

let empty_line () : Dest.line = { defines = []; uses = []; live_out = []; move = false }

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
;;

let trans_operand (operand : Src.Sop.t) : Dest.Sop.t =
  let size = operand.size in
  match operand.data with
  | Imm i -> i |> Dest.Op.of_imm |> Dest.Sop.wrap size
  | Temp t -> t |> Dest.Op.of_temp |> Dest.Sop.wrap size
;;

let get_size (operand : Src.Sop.t) : Size.primitive = operand.size
let get_size' (operand : Dest.Sop.t) : Size.primitive = operand.size

(* Generate x86 instr with binop convention *)
let[@warning "-8"] gen_binop_rev (Src.Binop bin) =
  let op, dest, lhs, rhs =
    ( trans_binop bin.op
    , trans_operand (Src.St.to_Sop bin.dest)
    , trans_operand bin.lhs
    , trans_operand bin.rhs )
  in
  let defines =
    match op with
    | Times -> [ dest.data; Dest.Op.of_reg RAX ]
    | Divided_by | Modulo -> [ dest.data; Dest.Op.of_reg RAX; Dest.Op.of_reg RDX ]
    | Right_shift | Left_shift -> [ dest.data; Dest.Op.of_reg RCX ]
    | Equal_eq | Greater | Greater_eq | Less | Less_eq | Not_eq ->
      [ dest.data; Dest.Op.of_reg RAX ]
    | _ -> [ dest.data ]
  in
  let uses = [ lhs.data; rhs.data ] in
  let line = ({ defines; uses; live_out = []; move = false } : Dest.line) in
  [ Dest.Binop { op; dest; lhs; rhs; line } ]
;;

let[@warning "-8"] gen_move_rev (Src.Mov move) =
  let dest, src = trans_operand (Src.St.to_Sop move.dest), trans_operand move.src in
  let defines, uses = [ dest.data ], [ src.data ] in
  let line = { defines; uses; live_out = []; move = true } in
  [ Dest.Mov { dest; src; line } ]
;;

let[@warning "-8"] gen_jump_rev (Src.Jump jump) =
  let line = empty_line () in
  [ Dest.Jump { target = jump.target; line } ]
;;

let[@warning "-8"] gen_cjump_rev (Src.CJump cjump) =
  let lhs, rhs = trans_operand cjump.lhs, trans_operand cjump.rhs in
  let op = trans_binop cjump.op in
  let line =
    { defines = []; uses = [ lhs.data; rhs.data ]; live_out = []; move = false }
  in
  let target_true = cjump.target_true in
  let target_false = cjump.target_false in
  [ Dest.CJump { lhs; op; rhs; target_true; target_false; line } ]
;;

let[@warning "-8"] gen_ret_rev (Src.Ret ret) (exit_label : Label.t) =
  let line = empty_line () in
  let mov =
    match ret.var with
    | None -> []
    | Some var ->
      let src = trans_operand var in
      let size = get_size' src in
      let defines, uses = [ Dest.Op.of_reg RAX ], [ src.data ] in
      let line_mov = { line with defines; uses; move = true } in
      let dest = RAX |> Dest.Op.of_reg |> Dest.Sop.wrap size in
      [ Dest.Mov { dest; src; line = line_mov } ]
  in
  Dest.Jump { target = exit_label; line } :: mov
;;

let param_map (base : Int64.t) (idx : int) : Dest.Op.t =
  let open Base.Int64 in
  match idx with
  | 0 -> Dest.Op.of_reg RDI
  | 1 -> Dest.Op.of_reg RSI
  | 2 -> Dest.Op.of_reg RDX
  | 3 -> Dest.Op.of_reg RCX
  | 4 -> Dest.Op.of_reg R8
  | 5 -> Dest.Op.of_reg R9
  | _ -> Dest.Op.of_af (base + Size.type_size_byte `QWORD)
;;

let set_size (operand : Dest.Sop.t) (size : Size.primitive) : Dest.Sop.t =
  { operand with size }
;;

(* alignment for %RSP. %RSP is multiple of 16 when calling function *)
let gen_align (rsp : Sreg.t) : Dest.instr =
  let defines, uses = [ Dest.Op.Reg rsp.data ], [ Dest.Op.Reg rsp.data ] in
  let line = ({ defines; uses; live_out = []; move = false } : Dest.line) in
  let rhs = 8L |> Dest.Op.of_imm |> Dest.Sop.wrap `QWORD in
  let rsp = rsp.data |> Dest.Op.of_reg |> Dest.Sop.wrap rsp.size in
  Dest.Binop { op = Dest.Minus; dest = rsp; lhs = rsp; rhs; line }
;;

let gen_release (rsp : Dest.Sop.t) (num_par : int) (align_size : int) =
  let defines, uses = [ rsp.data ], [ rsp.data ] in
  let line : Dest.line = { defines; uses; live_out = []; move = false } in
  let rhs =
    ((num_par - 6) * 8) + align_size
    |> Int64.of_int
    |> Dest.Op.of_imm
    |> Dest.Sop.wrap `QWORD
  in
  Dest.Binop { op = Dest.Plus; dest = rsp; lhs = rsp; rhs; line }
;;

let gen_fret (dest : Dest.Sop.t) =
  let defines, uses = [ dest.data ], [ Dest.Op.of_reg RAX ] in
  let line : Dest.line = { defines; uses; live_out = []; move = true } in
  let size = dest.size in
  let src : Dest.Sop.t = { data = Dest.Op.of_reg RAX; size } in
  Dest.Mov { dest; src; line }
;;

(* Generate x86 instr with function call convention *)
let[@warning "-8"] gen_fcall_rev (Src.Fcall fcall) =
  let func_name = fcall.func_name in
  let dest =
    match fcall.dest with
    | Some dest -> Some (trans_operand (Src.St.to_Sop dest))
    | None -> None
  in
  let args = List.map fcall.args ~f:(fun arg -> trans_operand arg) in
  let x86_regs = (RAX :: caller_saved) @ parameters in
  let defines = List.map x86_regs ~f:(fun r -> Dest.Op.of_reg r) in
  let base = ref 0L in
  let uses =
    List.mapi fcall.args ~f:(fun idx arg ->
        let size = get_size arg in
        let op = param_map !base idx in
        base := if idx < 6 then 0L else Base.Int64.( + ) !base (Size.type_size_byte size);
        op)
  in
  let line = ({ defines; uses; live_out = []; move = false } : Dest.line) in
  base := 0L;
  let params =
    List.mapi fcall.args ~f:(fun idx arg ->
        let src = trans_operand arg in
        let size = get_size' src in
        if idx < 6
        then (
          let dest = param_map !base idx in
          let defines = [ dest ] in
          let uses = [ src.data ] in
          let line = ({ defines; uses; live_out = []; move = true } : Dest.line) in
          let mov = Dest.Mov { dest = { data = dest; size }; src; line } in
          mov)
        else (
          let defines = [] in
          let uses = [ src.data ] in
          let line = ({ defines; uses; live_out = []; move = false } : Dest.line) in
          let push = Dest.Push { var = src; line } in
          push))
  in
  let rsp = RSP |> Sreg.wrap `QWORD in
  let fcall = Dest.Fcall { func_name; args; line; scope = fcall.scope } in
  let align = gen_align rsp in
  let num_par = List.length params in
  let need_align = num_par > 6 && num_par % 2 = 1 in
  let insts = if need_align then (fcall :: params) @ [ align ] else fcall :: params in
  let insts =
    match dest with
    | None -> insts
    | Some dest ->
      let ret = gen_fret dest in
      ret :: insts
  in
  let align_size = if need_align then 8 else 0 in
  let rsp_oprd = RSP |> Dest.Op.of_reg |> Dest.Sop.wrap `QWORD in
  let release = gen_release rsp_oprd num_par align_size in
  if num_par > 6 then release :: insts else insts
;;

(* Move from source operand to destination register *)
let gen_move_rev' (dest : Reg.t) (src : Src.Sop.t) : Dest.instr * Sreg.t * Dest.Sop.t =
  let size = `QWORD in
  let reg = Sreg.wrap size dest in
  let dest = dest |> Dest.Op.of_reg |> Dest.Sop.wrap size in
  let src = trans_operand src in
  let defines, uses = [ dest.data ], [ src.data ] in
  let line = { uses; defines; live_out = []; move = true } in
  Dest.Mov { dest; src; line }, reg, src
;;

let[@warning "-8"] gen_load_rev (Src.Load load) : Dest.instr list =
  let size = load.dest.size in
  let base_quad, index_quad, scale, disp = Src.Addr.get load.src.data in
  let base_mov, base_reg, base_src = gen_move_rev' heap_base base_quad in
  match index_quad with
  | Some index_quad' ->
    let index_mov, index_reg, index_src = gen_move_rev' heap_index index_quad' in
    let src =
      Dest.Addr.of_bisd base_reg.data (Some index_reg.data) scale disp
      |> Dest.Mem.wrap size
    in
    let dest = St.wrap load.dest.size load.dest.data in
    let line =
      { uses = [ base_src.data; index_src.data ]
      ; defines =
          [ Op.of_reg base_reg.data; Op.of_reg index_reg.data; Op.of_temp dest.data ]
      ; live_out = []
      ; move = false
      }
    in
    let load = Dest.Load { dest; src; line } in
    [ load; index_mov; base_mov ]
  | None ->
    let src = Dest.Addr.of_bisd base_reg.data None scale disp |> Dest.Mem.wrap size in
    let dest = St.wrap load.dest.size load.dest.data in
    let line =
      { uses = [ base_src.data ]
      ; defines = [ Op.of_reg base_reg.data; Op.of_temp dest.data ]
      ; live_out = []
      ; move = false
      }
    in
    let load = Dest.Load { dest; src; line } in
    [ load; base_mov ]
;;

let[@warning "-8"] gen_store_rev (Src.Store store) : Dest.instr list =
  let size = store.dest.size in
  let base_quad, index_quad, scale, disp = Src.Addr.get store.dest.data in
  let base_mov, base_reg, base_src = gen_move_rev' heap_base base_quad in
  match index_quad with
  | Some index_quad' ->
    let offset_mov, index_reg, index_src = gen_move_rev' heap_index index_quad' in
    let dest =
      Dest.Addr.of_bisd base_reg.data (Some index_reg.data) scale disp
      |> Dest.Mem.wrap size
    in
    let src = trans_operand store.src in
    let line =
      { uses = [ base_src.data; index_src.data; src.data ]
      ; defines = [ Op.of_reg base_reg.data; Op.of_reg index_reg.data ]
      ; live_out = []
      ; move = false
      }
    in
    let store = Dest.Store { dest; src; line } in
    [ store; offset_mov; base_mov ]
  | None ->
    let dest = Dest.Addr.of_bisd base_reg.data None scale disp |> Dest.Mem.wrap size in
    let src = trans_operand store.src in
    let line =
      { uses = [ base_src.data; src.data ]
      ; defines = [ Op.of_reg base_reg.data ]
      ; live_out = []
      ; move = false
      }
    in
    let store = Dest.Store { dest; src; line } in
    [ store; base_mov ]
;;

let[@warning "-8"] gen_cast_rev (Src.Cast cast) : Dest.instr list =
  let dest = Dest.St.wrap cast.dest.size cast.dest.data in
  let src = Dest.St.wrap cast.src.size cast.src.data in
  let line =
    { defines = [ Op.of_temp dest.data ]
    ; uses = [ Op.of_temp src.data ]
    ; move = false
    ; live_out = []
    }
  in
  let inst = Dest.Cast { dest; src; line } in
  [ inst ]
;;

(* Generate instruction with x86 conventions *)
let rec gen_body (program : Src.instr list) (res : Dest.instr list) (exit_label : Label.t)
    : Dest.instr list
  =
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
      | Label l -> [ Dest.Label { label = l; line = empty_line () } ]
      | Directive dir -> [ Dest.Directive dir ]
      | Comment cmt -> [ Dest.Comment cmt ]
      | Fcall fcall -> gen_fcall_rev (Fcall fcall)
      | Load load -> gen_load_rev (Load load)
      | Store store -> gen_store_rev (Store store)
    in
    gen_body t (inst @ res) exit_label
;;

(* Generate move instruction for callee-saved register of define info *)
let save_callee () : Dest.instr list =
  let size = `QWORD in
  List.fold callee_saved ~init:[] ~f:(fun acc r ->
      let t = Temp.create () |> Op.of_temp in
      let defines, uses = [ t ], [ Op.of_reg r ] in
      let line = { defines; uses; move = true; live_out = [] } in
      let dest = Dest.Sop.wrap size t in
      let src = r |> Op.of_reg |> Dest.Sop.wrap size in
      let mov = Dest.Mov { dest; src; line } in
      mov :: acc)
  |> List.rev
;;

(* Generate move instruction for callee-saved register of uses info 
 * Then, return the function *)
let gen_epilogue (prologue : Dest.instr list) : Dest.instr list =
  let restore =
    List.rev prologue
    |> List.map ~f:(fun inst ->
           let dest, src =
             match inst with
             | Dest.Mov mov -> mov.src, mov.dest
             | _ -> failwith "mov missing"
           in
           let line =
             { defines = [ dest.data ]; uses = [ src.data ]; live_out = []; move = true }
           in
           Dest.Mov { dest; src; line })
  in
  let line = empty_line () in
  let line_ret = { line with uses = [ Dest.Op.of_reg RAX ] } in
  let ret = Dest.Ret { line = line_ret } in
  restore @ [ ret ]
;;

(* Generate assigning parameter passing code. Parameters are passed through
 * registers(first 6 parameters) or memories(rest parameters) during function call. *)
let gen_pars (pars : St.t list) : Dest.instr list =
  let base = ref 0L in
  List.mapi pars ~f:(fun idx par ->
      let src = param_map !base idx in
      let dest = par.data |> Op.of_temp |> Sop.wrap par.size in
      let defines = [ dest.data ] in
      if idx < 6
      then (
        let line = { defines; uses = [ src ]; live_out = []; move = true } in
        [ Mov { dest; src = { data = src; size = par.size }; line } ])
      else (
        let temp_sop = Temp.create () |> Op.of_temp |> Sop.wrap par.size in
        let temp_mem = Sop.wrap par.size src in
        let line_load =
          { defines = [ temp_sop.data ]
          ; uses = [ temp_mem.data ]
          ; live_out = []
          ; move = true
          }
        in
        let load = Mov { dest = temp_sop; src = temp_mem; line = line_load } in
        let line = { defines; uses = [ temp_sop.data ]; live_out = []; move = true } in
        base := Base.Int64.( + ) !base (Size.type_size_byte `QWORD);
        [ load; Mov { dest; src = temp_sop; line } ]))
  |> List.concat
;;

let gen_section (prefix : string) (fname : Symbol.t) (content : Dest.instr list)
    : Dest.section * Label.t
  =
  let label = Label.label (Some (prefix ^ Symbol.name fname)) in
  let name = Dest.Label { label; line = empty_line () } in
  { name; content }, label
;;

let gen_program prologue body epilogue : instr list =
  let prologue = prologue.name :: prologue.content in
  let body = body.name :: body.content in
  let epilogue = epilogue.name :: epilogue.content in
  prologue @ body @ epilogue
;;

(* Let register allocation alg handle prologue and epilogue. *)
let rec gen (program : Src.program) (res : Dest.program) : Dest.program =
  match program with
  | [] -> List.rev res
  | h :: t ->
    let pars = List.map h.pars ~f:(fun par -> St.wrap par.size par.data) |> gen_pars in
    let save = save_callee () in
    let epilogue_content = gen_epilogue save in
    let prologue, _ = gen_section "pro_" h.func_name (save @ pars) in
    let epilogue, exit_label = gen_section "epi_" h.func_name epilogue_content in
    let body_content = gen_body h.body [] exit_label in
    let body, _ = gen_section "body_" h.func_name body_content in
    let prog = gen_program prologue body epilogue in
    let scope = h.scope in
    let fdefn = { func_name = Symbol.name h.func_name; body = prog; scope } in
    gen t (fdefn :: res)
;;
