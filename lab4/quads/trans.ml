open Core
module Tree = Ir_tree.Inst
module Quads = Inst
module Temp = Var.Temp
module Register = Var.X86_reg.Logic
module Memory = Var.Memory
module Label = Util.Label
module Size = Var.Size
module Fname = Util.Symbol.Fname

let munch_op : Tree.binop -> Quads.bin_op = function
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

let wrap_op size oprd : Quads.operand = { data = oprd; size }

(* munch_exp_acc dest exp rev_acc
 *
 * Suppose we have the statement:
 *   dest <-- exp
 *
 * If the codegened statements for this are:
 *   s1; s2; s3; s4;
 *
 * Then this function returns the result:
 *   s4 :: s3 :: s2 :: s1 :: rev_acc
 *
 * I.e., rev_acc is an accumulator argument where the codegen'ed
 * statements are built in reverse. This allows us to create the
 * statements in linear time rather than quadratic time (for highly
 * nested expressions).
 *)
let rec munch_exp_acc
    (dest : Quads.operand)
    (exp : Tree.sexp)
    (rev_acc : Quads.instr list)
    : Quads.instr list
  =
  match exp.data with
  | Void -> rev_acc
  | Const i -> Mov { dest; src = wrap_op exp.size (Quads.Imm i) } :: rev_acc
  | Temp t -> Mov { dest; src = wrap_op exp.size (Quads.Temp t) } :: rev_acc
  | Binop binop -> munch_binop_acc dest (binop.op, binop.lhs, binop.rhs) rev_acc

(* munch_binop_acc dest (binop, e1, e2) rev_acc
*
* generates instructions to achieve dest <- e1 binop e2
*
* Much like munch_exp, this returns the result of appending the
* instructions in reverse to the accumulator argument, rev_acc.
*)
and munch_binop_acc
    (dest : Quads.operand)
    ((binop, e1, e2) : Tree.binop * Tree.sexp * Tree.sexp)
    (rev_acc : Quads.instr list)
    : Quads.instr list
  =
  let op = munch_op binop in
  (* Notice we fix the left hand side operand and destination the same to meet x86 instruction. *)
  let t1 = Quads.Temp (Temp.create ()) in
  let t1_s : Quads.operand = { data = t1; size = e1.size } in
  let t2 = Quads.Temp (Temp.create ()) in
  let t2_s : Quads.operand = { data = t2; size = e2.size } in
  if Size.compare (t1_s.size :> Size.t) (t2_s.size :> Size.t) <> 0
  then failwith "quad e1 e2 size mismatch";
  let rev_acc' = rev_acc |> munch_exp_acc t1_s e1 |> munch_exp_acc t2_s e2 in
  if Size.compare (e1.size :> Size.t) (dest.size :> Size.t) <> 0
  then (
    let dest' = Quads.Temp (Temp.create ()) in
    let dest'_s : Quads.operand = { data = dest'; size = e1.size } in
    [ Quads.Mov { dest; src = dest'_s }
    ; Quads.Binop { op; dest = dest'_s; lhs = t1_s; rhs = t2_s }
    ]
    @ rev_acc')
  else Quads.Binop { op; dest; lhs = t1_s; rhs = t2_s } :: rev_acc'

(* munch_exp dest exp
 * Generates instructions for dest <-- exp. *)
and munch_exp : Quads.operand -> Tree.sexp -> Quads.instr list =
 fun dest exp ->
  (* Since munch_exp_acc returns the reversed accumulator, we must
   * reverse the list before returning. *)
  List.rev (munch_exp_acc dest exp [])

and[@warning "-8"] munch_effect_rev (Tree.Effect eft) : Quads.instr list =
  let lhs_size = eft.lhs.size in
  let lhs = Quads.Temp (Temp.create ()) in
  let lhs_s : Quads.operand = { data = lhs; size = lhs_size } in
  let op = munch_op eft.op in
  let rhs_size = eft.rhs.size in
  let rhs = Quads.Temp (Temp.create ()) in
  let rhs_s : Quads.operand = { data = rhs; size = rhs_size } in
  let dest_s : Quads.operand =
    { data = Quads.Temp eft.dest.data; size = eft.dest.size }
  in
  let lhs_inst_rev = munch_exp_acc lhs_s eft.lhs [] in
  let rhs_inst_rev = munch_exp_acc rhs_s eft.rhs [] in
  let safety_check_rev =
    match eft.op with
    | Right_shift | Left_shift ->
      let l1 = Label.label None in
      let l2 = Label.label None in
      let l3 = Label.label None in
      let l4 = Label.label None in
      let sigfpe : Quads.operand = { data = Quads.Imm Fname.fpe; size = `DWORD } in
      let zero : Quads.operand = { data = Quads.Imm Int64.zero; size = rhs_size } in
      let shift_bound : Quads.operand =
        { data = Quads.Imm Fname.shift_bound; size = rhs_size }
      in
      [ Quads.Label l4
      ; Quads.Fcall
          { func_name = Fname.raise; dest = None; args = [ sigfpe ]; scope = `Internal }
      ; Quads.Label l3
      ; Quads.Jump { target = l4 }
      ; Quads.Label l2
      ; Quads.CJump
          { lhs = rhs_s
          ; op = Quads.Less
          ; rhs = zero
          ; target_true = l3
          ; target_false = l2
          }
      ; Quads.Label l1
      ; Quads.CJump
          { lhs = rhs_s
          ; op = Quads.Greater
          ; rhs = shift_bound
          ; target_true = l3
          ; target_false = l1
          }
      ]
    | Divided_by | Modulo -> []
    | _ -> failwith "not effect binop"
  in
  ((Quads.Binop { lhs = lhs_s; op; rhs = rhs_s; dest = dest_s } :: safety_check_rev)
  @ rhs_inst_rev)
  @ lhs_inst_rev

(* Return a reversed Quads.instr list. *)
and munch_stm_rev (stm : Tree.stm) : Quads.instr list =
  match stm with
  | Tree.Cast cast ->
    let dest : Temp.t Quads.sized = { data = cast.dest.data; size = cast.dest.size } in
    let temp = Temp.create () in
    let temp_oprd : Quads.operand = { data = Quads.Temp temp; size = cast.dest.size } in
    let move = munch_exp temp_oprd cast.src in
    Quads.Cast { dest; src = { data = temp; size = temp_oprd.size } } :: move
  | Tree.Move mv ->
    let size = mv.dest.size in
    let dest : Quads.operand = { data = Quads.Temp mv.dest.data; size } in
    munch_exp_acc dest mv.src []
  | Tree.Return e ->
    (match e with
    | None -> [ Quads.Ret { var = None } ]
    | Some e ->
      let size = e.size in
      let t = Temp.create () in
      let t_s : Quads.operand = { data = Quads.Temp t; size } in
      let inst = munch_exp_acc t_s e [] in
      Quads.Ret { var = Some t_s } :: inst)
  | Jump jmp -> [ Quads.Jump { target = jmp } ]
  | Tree.CJump cjmp ->
    let lhs_size = cjmp.lhs.size in
    let lhs = Temp.create () in
    let lhs_s : Quads.operand = { data = Quads.Temp lhs; size = lhs_size } in
    let op = munch_op cjmp.op in
    let rhs_size = cjmp.rhs.size in
    let rhs = Temp.create () in
    let rhs_s : Quads.operand = { data = Quads.Temp rhs; size = rhs_size } in
    let lhs_inst_rev = munch_exp_acc lhs_s cjmp.lhs [] in
    let rhs_inst_rev = munch_exp_acc rhs_s cjmp.rhs [] in
    (Quads.CJump
       { lhs = lhs_s
       ; op
       ; rhs = rhs_s
       ; target_true = cjmp.target_true
       ; target_false = cjmp.target_false
       }
    :: rhs_inst_rev)
    @ lhs_inst_rev
  | Tree.Label l -> [ Quads.Label l ]
  | Tree.Nop -> []
  | Tree.Effect eft -> munch_effect_rev (Tree.Effect eft)
  | Tree.Assert asrt ->
    let size = asrt.size in
    let t = Temp.create () in
    let t_s : Quads.operand = { data = Quads.Temp t; size } in
    let inst = munch_exp_acc t_s asrt [] in
    let pass = Label.label None in
    let fail = Label.label None in
    let sigabrt : Quads.operand = { data = Quads.Imm Fname.abrt; size } in
    let one : Quads.operand = { data = Quads.Imm Int64.one; size } in
    [ Quads.Label pass
    ; Quads.Fcall
        { func_name = Fname.raise; dest = None; args = [ sigabrt ]; scope = `Internal }
    ; Quads.Label fail
    ; Quads.CJump
        { lhs = t_s
        ; op = Quads.Equal_eq
        ; rhs = one
        ; target_true = pass
        ; target_false = fail
        }
    ]
    @ inst
  | Tree.Fcall fcall ->
    let args, args_stms_rev =
      List.map fcall.args ~f:(fun arg ->
          let s = arg.size in
          let t = Temp.create () in
          let t_s : Quads.operand = { data = Quads.Temp t; size = s } in
          let e = munch_exp_acc t_s arg [] in
          t_s, e)
      |> List.unzip
    in
    let args_stms_rev = List.concat args_stms_rev in
    let dest : Temp.t Quads.sized option =
      match fcall.dest with
      | None -> None
      | Some s -> Some { data = s.data; size = s.size }
    in
    let func_name = fcall.func_name in
    let call = Quads.Fcall { func_name; args; dest; scope = fcall.scope } in
    call :: args_stms_rev
  | Tree.Load load ->
    let size = `QWORD in
    let base_exp =
      if Base.Int64.( = ) load.src.disp 0L
      then load.src.base
      else (
        let lhs = ({ data = Tree.Const load.src.disp; size } : Tree.sexp) in
        { data = Tree.Binop { lhs; rhs = load.src.base; op = Plus }; size })
    in
    let base = Temp.create () in
    let base_s = wrap_op size (Quads.Temp base) in
    let base_instr = munch_exp_acc base_s base_exp [] in
    let offset, offset_instr =
      match load.src.offset with
      | Some exp ->
        let offset = Temp.create () in
        let offset_s = wrap_op size (Quads.Temp offset) in
        let offset_instr = munch_exp_acc offset_s exp [] in
        Some offset_s, offset_instr
      | None -> None, []
    in
    let mem = ({ base = base_s; offset; size = load.src.size } : Quads.mem) in
    let dest : Temp.t Quads.sized = { data = load.dest.data; size = load.dest.size } in
    let load = Quads.Load { src = mem; dest } in
    (load :: offset_instr) @ base_instr
  | Tree.Store store ->
    let size = `QWORD in
    let base_exp =
      if Base.Int64.( = ) store.dest.disp 0L
      then store.dest.base
      else (
        let lhs = ({ data = Tree.Const store.dest.disp; size } : Tree.sexp) in
        ({ data = Tree.Binop { lhs; rhs = store.dest.base; op = Plus }; size }
          : Tree.sexp))
    in
    let base = Temp.create () in
    let base_s = wrap_op size (Quads.Temp base) in
    let base_instr = munch_exp_acc base_s base_exp [] in
    let offset, offset_instr =
      match store.dest.offset with
      | Some exp ->
        let offset = Temp.create () in
        let offset_s = wrap_op size (Quads.Temp offset) in
        let offset_instr = munch_exp_acc offset_s exp [] in
        Some offset_s, offset_instr
      | None -> None, []
    in
    let mem = ({ base = base_s; offset; size = store.dest.size } : Quads.mem) in
    let src = Temp.create () in
    let src_s = wrap_op store.src.size (Quads.Temp src) in
    let src_instr = munch_exp_acc src_s store.src [] in
    let store = Quads.Store { src = src_s; dest = mem } in
    ((store :: src_instr) @ offset_instr) @ base_instr

and munch_stms stms res =
  match stms with
  | [] -> res |> List.rev
  | h :: t ->
    let stm = munch_stm_rev h in
    munch_stms t (stm @ res)
;;

let gen_fdefn (fdefn : Tree.fdefn) : Quads.fdefn =
  let body = munch_stms fdefn.body [] in
  (* let pars = fdefn.temps in *)
  let pars =
    List.map fdefn.temps ~f:(fun par : Temp.t Quads.sized ->
        { data = par.data; size = par.size })
  in
  { func_name = fdefn.func_name; body; pars; scope = fdefn.scope }
;;

(* To codegen a series of statements, just concatenate the results of
* codegen-ing each statement. *)
let gen (fdefns : Tree.program) : Quads.program =
  List.map fdefns ~f:(fun fdefn -> gen_fdefn fdefn)
;;
