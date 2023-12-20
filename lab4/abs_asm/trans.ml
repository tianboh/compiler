(* L3 x86 abstract assembly code
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
module Size = Var.Size
open Inst

type line = Dest.line
type instr = Dest.instr

let rax = Reg.RAX
let rcx = Reg.RCX
let rdx = Reg.RDX
let empty_line () : Dest.line = { defines = []; uses = []; live_out = []; move = false }

let trans_binop (op : Src.bin_op) : Dest.bin_op =
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

let trans_operand (operand : Src.operand) : Dest.operand =
  let size = operand.size in
  match operand.data with
  | Imm i -> { data = Dest.Imm i; size }
  | Temp t -> { data = Dest.Temp t; size }
;;

let wrap_reg size reg : Reg.t Dest.sized = { data = reg; size }
let wrap_op size (op : Dest.operand_logic) : Dest.operand = { data = op; size }
let get_size (operand : Src.operand) : Size.primitive = operand.size
let get_size' (operand : Dest.operand) : Size.primitive = operand.size

(* Generate x86 instr with binop convention *)
let[@warning "-8"] gen_binop_rev (Src.Binop bin) =
  let op, dest, lhs, rhs =
    ( trans_binop bin.op
    , trans_operand bin.dest
    , trans_operand bin.lhs
    , trans_operand bin.rhs )
  in
  let defines =
    match op with
    | Times -> [ dest.data; Dest.Reg rax ]
    | Divided_by | Modulo -> [ dest.data; Dest.Reg rax; Dest.Reg rdx ]
    | Right_shift | Left_shift -> [ dest.data; Dest.Reg rcx ]
    | Equal_eq | Greater | Greater_eq | Less | Less_eq | Not_eq ->
      [ dest.data; Dest.Reg rax ]
    | _ -> [ dest.data ]
  in
  let uses = [ lhs.data; rhs.data ] in
  let line = ({ defines; uses; live_out = []; move = false } : Dest.line) in
  [ Dest.Binop { op; dest; lhs; rhs; line } ]
;;

let[@warning "-8"] gen_move_rev (Src.Mov move) =
  let dest, src = trans_operand move.dest, trans_operand move.src in
  let line =
    { defines = [ dest.data ]; uses = [ src.data ]; live_out = []; move = true }
  in
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
      let defines, uses = [ Dest.Reg rax ], [ src.data ] in
      let line_mov = { line with defines; uses; move = true } in
      let dest = { data = Dest.Reg rax; size } in
      [ Dest.Mov { dest; src; line = line_mov } ]
  in
  Dest.Jump { target = exit_label; line } :: mov
;;

let param_map (base : Int64.t) (idx : int) : Dest.operand_logic =
  let open Base.Int64 in
  match idx with
  | 0 -> Dest.Reg RDI
  | 1 -> Dest.Reg RSI
  | 2 -> Dest.Reg RDX
  | 3 -> Dest.Reg RCX
  | 4 -> Dest.Reg R8
  | 5 -> Dest.Reg R9
  | _ -> Dest.Above_frame (base + Size.type_size_byte `QWORD)
;;

let set_size (operand : operand) (size : Size.primitive) : operand = { operand with size }

(* alignment for %RSP. %RSP is multiple of 16 when calling function *)
let gen_align (rsp : Reg.t Dest.sized) : Dest.instr =
  let line =
    ({ defines = [ Reg rsp.data ]; uses = [ Reg rsp.data ]; live_out = []; move = false }
      : Dest.line)
  in
  let rhs = wrap_op `QWORD (Dest.Imm 8L) in
  let rsp : Dest.operand = { data = Dest.Reg rsp.data; size = rsp.size } in
  Dest.Binop { op = Dest.Minus; dest = rsp; lhs = rsp; rhs; line }
;;

let gen_release (rsp : operand) (num_par : int) (align_size : int) =
  let line : Dest.line =
    { defines = [ rsp.data ]; uses = [ rsp.data ]; live_out = []; move = false }
  in
  let rhs = wrap_op `QWORD (Dest.Imm (Int64.of_int (((num_par - 6) * 8) + align_size))) in
  Dest.Binop { op = Dest.Plus; dest = rsp; lhs = rsp; rhs; line }
;;

let gen_fret (dest : Dest.operand) =
  let line : Dest.line =
    { defines = [ dest.data ]; uses = [ Dest.Reg rax ]; live_out = []; move = true }
  in
  let size = dest.size in
  let src : operand = { data = Dest.Reg rax; size } in
  Dest.Mov { dest; src; line }
;;

(* Generate x86 instr with function call convention *)
let[@warning "-8"] gen_fcall_rev (Src.Fcall fcall) =
  let func_name = fcall.func_name in
  let dest =
    match fcall.dest with
    | Some dest ->
      Some (trans_operand ({ data = Src.Temp dest.data; size = dest.size } : Src.operand))
    | None -> None
  in
  let args = List.map fcall.args ~f:(fun arg -> trans_operand arg) in
  let x86_regs = (rax :: Reg.caller_saved) @ Reg.parameters in
  let defines = List.map x86_regs ~f:(fun r -> Dest.Reg r) in
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
  let rsp = wrap_reg `QWORD RSP in
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
  let rsp_oprd = { data = Dest.Reg RSP; size = `QWORD } in
  let release = gen_release rsp_oprd num_par align_size in
  if num_par > 6 then release :: insts else insts
;;

(* Move from source operand to destination register *)
let gen_move_rev' (dest : Reg.t) (src : Src.operand)
    : Dest.instr * Dest.Register.t Dest.sized * Dest.operand
  =
  let size = `QWORD in
  let reg = { data = dest; size } in
  let dest = { data = Dest.Reg dest; size } in
  let src = trans_operand src in
  let line =
    { uses = [ src.data ]; defines = [ dest.data ]; live_out = []; move = true }
  in
  Dest.Mov { dest; src; line }, reg, src
;;

let[@warning "-8"] gen_load_rev (Src.Load load) : Dest.instr list =
  let size = load.dest.size in
  let move_base, base_dest, base_src = gen_move_rev' Reg.heap_base load.src.base in
  match load.src.offset with
  | Some offset ->
    let move_offset, offset_dest, offset_src = gen_move_rev' Reg.heap_offset offset in
    let src = ({ base = base_dest; offset = Some offset_dest; size } : Dest.mem) in
    let dest : Temp.t Dest.sized = { data = load.dest.data; size = load.dest.size } in
    let line =
      { uses = [ base_src.data; offset_src.data ]
      ; defines =
          [ Dest.Reg base_dest.data; Dest.Reg offset_dest.data; Dest.Temp dest.data ]
      ; live_out = []
      ; move = false
      }
    in
    let load = Dest.Load { dest; src; line } in
    [ load; move_offset; move_base ]
  | None ->
    let src = ({ base = base_dest; offset = None; size } : Dest.mem) in
    let dest : Temp.t Dest.sized = { data = load.dest.data; size = load.dest.size } in
    let line =
      { uses = [ base_src.data ]
      ; defines = [ Dest.Reg base_dest.data; Dest.Temp dest.data ]
      ; live_out = []
      ; move = false
      }
    in
    let load = Dest.Load { dest; src; line } in
    [ load; move_base ]
;;

let[@warning "-8"] gen_store_rev (Src.Store store) : Dest.instr list =
  let size = store.dest.size in
  let move_base, base_dest, base_src = gen_move_rev' Reg.heap_base store.dest.base in
  match store.dest.offset with
  | Some offset ->
    let move_offset, offset_dest, offset_src = gen_move_rev' Reg.heap_offset offset in
    let dest = ({ base = base_dest; offset = Some offset_dest; size } : Dest.mem) in
    let src = trans_operand store.src in
    let line =
      { uses = [ base_src.data; offset_src.data; src.data ]
      ; defines = [ Dest.Reg base_dest.data; Dest.Reg offset_dest.data ]
      ; live_out = []
      ; move = false
      }
    in
    let store = Dest.Store { dest; src; line } in
    [ store; move_offset; move_base ]
  | None ->
    let dest = ({ base = base_dest; offset = None; size } : Dest.mem) in
    let src = trans_operand store.src in
    let line =
      { uses = [ base_src.data; src.data ]
      ; defines = [ Dest.Reg base_dest.data ]
      ; live_out = []
      ; move = false
      }
    in
    let store = Dest.Store { dest; src; line } in
    [ store; move_base ]
;;

let[@warning "-8"] gen_cast_rev (Src.Cast cast) : Dest.instr list =
  let dest = { data = cast.dest.data; size = cast.dest.size } in
  let src = { data = cast.src.data; size = cast.src.size } in
  let line =
    { defines = [ Dest.Temp dest.data ]
    ; uses = [ Dest.Temp src.data ]
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
  List.fold Reg.callee_saved ~init:[] ~f:(fun acc r ->
      let t = Temp.create () in
      let line =
        { defines = [ Dest.Temp t ]; uses = [ Dest.Reg r ]; move = true; live_out = [] }
      in
      let dest = { data = Dest.Temp t; size } in
      let src = { data = Dest.Reg r; size } in
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
  let line_ret = { line with uses = [ Dest.Reg rax ] } in
  let ret = Dest.Ret { line = line_ret } in
  restore @ [ ret ]
;;

(* Generate assigning parameter passing code. Parameters are passed through
 * registers(first 6 parameters) or memories(rest parameters) during function call. *)
let gen_pars (pars : Temp.t Dest.sized list) : Dest.instr list =
  let base = ref 0L in
  List.mapi pars ~f:(fun idx par ->
      let src = param_map !base idx in
      let dest = { data = Dest.Temp par.data; size = par.size } in
      let defines = [ dest.data ] in
      if idx < 6
      then (
        let line = { defines; uses = [ src ]; live_out = []; move = true } in
        [ Mov { dest; src = { data = src; size = par.size }; line } ])
      else (
        let temp = Temp.create () in
        let temp_op : Dest.operand = { data = Dest.Temp temp; size = par.size } in
        let temp_mem = { data = src; size = par.size } in
        let line_load =
          { defines = [ Dest.Temp temp ]
          ; uses = [ temp_mem.data ]
          ; live_out = []
          ; move = true
          }
        in
        let load = Mov { dest = temp_op; src = temp_mem; line = line_load } in
        let line = { defines; uses = [ temp_op.data ]; live_out = []; move = true } in
        base := Base.Int64.( + ) !base (Size.type_size_byte `QWORD);
        load :: [ Mov { dest; src = temp_op; line } ]))
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
    let pars =
      List.map h.pars ~f:(fun par ->
          let data, size = par.data, par.size in
          { data; size })
      |> gen_pars
    in
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
