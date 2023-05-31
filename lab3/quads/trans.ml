open Core
module Tree = Ir_tree.Inst
module Quads = Inst
module Temp = Var.Temp
module Register = Var.X86_reg
module Memory = Var.Memory
module Label = Util.Label

let munch_op = function
  | Tree.Plus -> Quads.Plus
  | Tree.Minus -> Quads.Minus
  | Tree.Times -> Quads.Times
  | Tree.Divided_by -> Quads.Divided_by
  | Tree.Modulo -> Quads.Modulo
  | Tree.And -> Quads.And
  | Tree.Or -> Quads.Or
  | Tree.Xor -> Quads.Xor
  | Tree.Right_shift -> Quads.Right_shift
  | Tree.Left_shift -> Quads.Left_shift
  | Tree.Equal_eq -> Quads.Equal_eq
  | Tree.Greater -> Quads.Greater
  | Tree.Greater_eq -> Quads.Greater_eq
  | Tree.Less -> Quads.Less
  | Tree.Less_eq -> Quads.Less_eq
  | Tree.Not_eq -> Quads.Not_eq
;;

let munch_scope = function
  | Tree.Internal -> Quads.Internal
  | Tree.External -> Quads.External
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
  | Tree.Const i -> Quads.Mov { dest; src = Quads.Imm i } :: rev_acc
  | Tree.Temp t -> Quads.Mov { dest; src = Quads.Temp t } :: rev_acc
  | Tree.Binop binop -> munch_binop_acc dest (binop.op, binop.lhs, binop.rhs) rev_acc

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
  let t1 = Temp.create () in
  let t2 = Temp.create () in
  let rev_acc' =
    rev_acc |> munch_exp_acc (Quads.Temp t1) e1 |> munch_exp_acc (Quads.Temp t2) e2
  in
  Quads.Binop { op; dest; lhs = Quads.Temp t1; rhs = Quads.Temp t2 } :: rev_acc'

and munch_exp : Quads.operand -> Tree.exp -> Quads.instr list =
 (* munch_exp dest exp
  * Generates instructions for dest <-- exp.
  *)
 fun dest exp ->
  (* Since munch_exp_acc returns the reversed accumulator, we must
   * reverse the list before returning. *)
  List.rev (munch_exp_acc dest exp [])

and munch_stm_rev (stm : Tree.stm) =
  (* Return a reversed Quads.instr list. *)
  match stm with
  | Tree.Move mv -> munch_exp_acc (Quads.Temp mv.dest) mv.src []
  | Tree.Return e ->
    (match e with
    | None -> [ Quads.Ret { var = None } ]
    | Some e ->
      let t = Temp.create () in
      let inst = munch_exp_acc (Quads.Temp t) e [] in
      Quads.Ret { var = Some (Quads.Temp t) } :: inst)
  | Jump jmp -> [ Quads.Jump { target = jmp } ]
  | Tree.CJump cjmp ->
    let lhs = Quads.Temp (Temp.create ()) in
    let op = munch_op cjmp.op in
    let rhs = Quads.Temp (Temp.create ()) in
    let lhs_inst_rev = munch_exp_acc lhs cjmp.lhs [] in
    let rhs_inst_rev = munch_exp_acc rhs cjmp.rhs [] in
    (Quads.CJump
       { lhs; op; rhs; target_true = cjmp.target_true; target_false = cjmp.target_false }
    :: rhs_inst_rev)
    @ lhs_inst_rev
  | Tree.Label l -> [ Quads.Label l ]
  | Tree.Nop -> []
  | Tree.Effect eft ->
    let lhs = Quads.Temp (Temp.create ()) in
    let op = munch_op eft.op in
    let rhs = Quads.Temp (Temp.create ()) in
    let lhs_inst_rev = munch_exp_acc lhs eft.lhs [] in
    let rhs_inst_rev = munch_exp_acc rhs eft.rhs [] in
    (Quads.Binop { lhs; op; rhs; dest = Quads.Temp eft.dest } :: rhs_inst_rev)
    @ lhs_inst_rev
  | Tree.Assert asrt ->
    let t = Temp.create () in
    let inst = munch_exp_acc (Quads.Temp t) asrt [] in
    Quads.Assert (Quads.Temp t) :: inst
  | Tree.Fcall fcall ->
    let res =
      List.map fcall.args ~f:(fun arg ->
          let t = Quads.Temp (Temp.create ()) in
          let e = munch_exp_acc t arg [] in
          t, e)
    in
    let args, args_stms = List.unzip res in
    let args_stms_rev = List.rev args_stms |> List.concat in
    let scope = munch_scope fcall.scope in
    let call =
      Quads.Fcall { func_name = fcall.func_name; args; dest = fcall.dest; scope }
    in
    call :: args_stms_rev

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
  { func_name = fdefn.func_name; body; pars }
;;

(* To codegen a series of statements, just concatenate the results of
* codegen-ing each statement. *)
let gen (fdefns : Tree.program) : Quads.program =
  List.map fdefns ~f:(fun fdefn -> gen_fdefn fdefn)
;;
