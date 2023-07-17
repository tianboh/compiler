open Core
module Tree = Ir_tree.Inst
module Quads = Inst
module Temp = Var.Temp
module Register = Var.X86_reg.Logic
module Memory = Var.Memory
module Label = Util.Label
module Size = Var.Size

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

(* get Tree.exp size *)
let rec sizeof_exp : Tree.exp -> Size.primitive = function
  | Void -> failwith "void doesn't have esize"
  | Const _ -> `DWORD
  | Temp t -> t.size
  | Binop binop ->
    (match binop.op with
    | Equal_eq | Greater | Greater_eq | Less | Less_eq | Not_eq -> `DWORD
    | Plus
    | Minus
    | Times
    | Divided_by
    | Modulo
    | And
    | Or
    | Xor
    | Right_shift
    | Left_shift -> sizeof_exp binop.lhs)
;;

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
let rec munch_exp_acc (dest : Quads.operand) (exp : Tree.exp) (rev_acc : Quads.instr list)
    : Quads.instr list
  =
  match exp with
  | Void -> rev_acc
  | Const i -> Mov { dest; src = Quads.Imm { v = i.v; size = i.size } } :: rev_acc
  | Temp t -> Mov { dest; src = Quads.Temp t } :: rev_acc
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
    ((binop, e1, e2) : Tree.binop * Tree.exp * Tree.exp)
    (rev_acc : Quads.instr list)
    : Quads.instr list
  =
  let op = munch_op binop in
  (* Notice we fix the left hand side operand and destination the same to meet x86 instruction. *)
  let t1 = Temp.create `DWORD in
  let t2 = Temp.create `DWORD in
  let rev_acc' =
    rev_acc |> munch_exp_acc (Quads.Temp t1) e1 |> munch_exp_acc (Quads.Temp t2) e2
  in
  Quads.Binop { op; dest; lhs = Quads.Temp t1; rhs = Quads.Temp t2 } :: rev_acc'

(* munch_exp dest exp
 * Generates instructions for dest <-- exp. *)
and munch_exp : Quads.operand -> Tree.exp -> Quads.instr list =
 fun dest exp ->
  (* Since munch_exp_acc returns the reversed accumulator, we must
   * reverse the list before returning. *)
  List.rev (munch_exp_acc dest exp [])

(* Return a reversed Quads.instr list. *)
and munch_stm_rev (stm : Tree.stm) : Quads.instr list =
  match stm with
  | Tree.Move mv -> munch_exp_acc (Quads.Temp mv.dest) mv.src []
  | Tree.Return e ->
    (match e with
    | None -> [ Quads.Ret { var = None } ]
    | Some e ->
      let size = sizeof_exp e in
      let t = Temp.create size in
      let inst = munch_exp_acc (Quads.Temp t) e [] in
      Quads.Ret { var = Some (Quads.Temp t) } :: inst)
  | Jump jmp -> [ Quads.Jump { target = jmp } ]
  | Tree.CJump cjmp ->
    let lhs_size = sizeof_exp cjmp.lhs in
    let lhs = Quads.Temp (Temp.create lhs_size) in
    let op = munch_op cjmp.op in
    let rhs_size = sizeof_exp cjmp.rhs in
    let rhs = Quads.Temp (Temp.create rhs_size) in
    let lhs_inst_rev = munch_exp_acc lhs cjmp.lhs [] in
    let rhs_inst_rev = munch_exp_acc rhs cjmp.rhs [] in
    (Quads.CJump
       { lhs; op; rhs; target_true = cjmp.target_true; target_false = cjmp.target_false }
    :: rhs_inst_rev)
    @ lhs_inst_rev
  | Tree.Label l -> [ Quads.Label l ]
  | Tree.Nop -> []
  | Tree.Effect eft ->
    let lhs_size = sizeof_exp eft.lhs in
    let lhs = Quads.Temp (Temp.create lhs_size) in
    let op = munch_op eft.op in
    let rhs_size = sizeof_exp eft.rhs in
    let rhs = Quads.Temp (Temp.create rhs_size) in
    let lhs_inst_rev = munch_exp_acc lhs eft.lhs [] in
    let rhs_inst_rev = munch_exp_acc rhs eft.rhs [] in
    (Quads.Binop { lhs; op; rhs; dest = Quads.Temp eft.dest } :: rhs_inst_rev)
    @ lhs_inst_rev
  | Tree.Assert asrt ->
    let size = sizeof_exp asrt in
    let t = Temp.create size in
    let inst = munch_exp_acc (Quads.Temp t) asrt [] in
    Quads.Assert (Quads.Temp t) :: inst
  | Tree.Fcall fcall ->
    let args, args_stms_rev =
      List.map fcall.args ~f:(fun arg ->
          let s = sizeof_exp arg in
          let t = Quads.Temp (Temp.create s) in
          let e = munch_exp_acc t arg [] in
          t, e)
      |> List.unzip
    in
    let args_stms_rev = List.concat args_stms_rev in
    let call =
      Quads.Fcall
        { func_name = fcall.func_name; args; dest = fcall.dest; scope = fcall.scope }
    in
    call :: args_stms_rev
  | Tree.Load load ->
    let base_exp =
      if phys_equal load.src.disp 0L
      then load.src.base
      else (
        let lhs = Tree.Const { v = load.src.disp; size = `QWORD } in
        Tree.Binop { lhs; rhs = load.src.base; op = Plus })
    in
    let base = Quads.Temp (Temp.create `QWORD) in
    let base_instr = munch_exp_acc base base_exp [] in
    let offset, offset_instr =
      match load.src.offset with
      | Some exp ->
        let offset = Quads.Temp (Temp.create `QWORD) in
        let offset_instr = munch_exp_acc offset exp [] in
        Some offset, offset_instr
      | None -> None, []
    in
    let mem = ({ base; offset; size = load.src.size } : Quads.mem) in
    let load = Quads.Load { src = mem; dest = load.dest } in
    (load :: offset_instr) @ base_instr
  | Tree.Store store ->
    let base_exp =
      if phys_equal store.dest.disp 0L
      then store.dest.base
      else (
        let lhs = Tree.Const { v = store.dest.disp; size = `QWORD } in
        Tree.Binop { lhs; rhs = store.dest.base; op = Plus })
    in
    let base = Quads.Temp (Temp.create `QWORD) in
    let base_instr = munch_exp_acc base base_exp [] in
    let offset, offset_instr =
      match store.dest.offset with
      | Some exp ->
        let offset = Quads.Temp (Temp.create `QWORD) in
        let offset_instr = munch_exp_acc offset exp [] in
        Some offset, offset_instr
      | None -> None, []
    in
    let mem = ({ base; offset; size = store.dest.size } : Quads.mem) in
    let src = Quads.Temp (Temp.create (sizeof_exp store.src)) in
    let src_instr = munch_exp_acc src store.src [] in
    let store = Quads.Store { src; dest = mem } in
    ((store :: src_instr) @ offset_instr) @ base_instr

and munch_stms_rev stms res =
  match stms with
  | [] -> res
  | h :: t ->
    let stm = munch_stm_rev h in
    munch_stms_rev t res @ stm
;;

let gen_fdefn (fdefn : Tree.fdefn) : Quads.fdefn =
  let body = munch_stms_rev fdefn.body [] |> List.rev in
  let pars = fdefn.temps in
  { func_name = fdefn.func_name; body; pars; scope = fdefn.scope }
;;

(* To codegen a series of statements, just concatenate the results of
* codegen-ing each statement. *)
let gen (fdefns : Tree.program) : Quads.program =
  List.map fdefns ~f:(fun fdefn -> gen_fdefn fdefn)
;;
