open Core
module T = Tree
module Temp = Var.Temp
module Register = Var.X86_reg
module Memory = Var.Memory
module Label = Util.Label

let munch_op = function
  | T.Plus -> Inst.Plus
  | T.Minus -> Inst.Minus
  | T.Times -> Inst.Times
  | T.Divided_by -> Inst.Divided_by
  | T.Modulo -> Inst.Modulo
  | T.And -> Inst.And
  | T.Or -> Inst.Or
  | T.Xor -> Inst.Xor
  | T.Right_shift -> Inst.Right_shift
  | T.Left_shift -> Inst.Left_shift
  | T.Equal_eq -> Inst.Equal_eq
  | T.Greater -> Inst.Greater
  | T.Greater_eq -> Inst.Greater_eq
  | T.Less -> Inst.Less
  | T.Less_eq -> Inst.Less_eq
  | T.Not_eq -> Inst.Not_eq
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
let rec munch_exp_acc (dest : Inst.operand) (exp : T.exp) (rev_acc : Inst.instr list)
    : Inst.instr list
  =
  match exp with
  | T.Const i -> Inst.Mov { dest; src = Inst.Imm i } :: rev_acc
  | T.Temp t -> Inst.Mov { dest; src = Inst.Temp t } :: rev_acc
  | T.Binop binop -> munch_binop_acc dest (binop.op, binop.lhs, binop.rhs) rev_acc

(* munch_binop_acc dest (binop, e1, e2) rev_acc
*
* generates instructions to achieve dest <- e1 binop e2
*
* Much like munch_exp, this returns the result of appending the
* instructions in reverse to the accumulator argument, rev_acc.
*)
and munch_binop_acc
    (dest : Inst.operand)
    ((binop, e1, e2) : T.binop * T.exp * T.exp)
    (rev_acc : Inst.instr list)
    : Inst.instr list
  =
  let op = munch_op binop in
  (* Notice we fix the left hand side operand and destination the same to meet x86 instruction. *)
  let t1 = Temp.create () in
  let t2 = Temp.create () in
  let rev_acc' =
    rev_acc |> munch_exp_acc (Inst.Temp t1) e1 |> munch_exp_acc (Inst.Temp t2) e2
  in
  Inst.Binop { op; dest; lhs = Inst.Temp t1; rhs = Inst.Temp t2 } :: rev_acc'

and munch_exp : Inst.operand -> T.exp -> Inst.instr list =
 (* munch_exp dest exp
  * Generates instructions for dest <-- exp.
  *)
 fun dest exp ->
  (* Since munch_exp_acc returns the reversed accumulator, we must
   * reverse the list before returning. *)
  List.rev (munch_exp_acc dest exp [])

and munch_stm_rev (stm : T.stm) =
  (* Return a reversed Inst.instr list. *)
  match stm with
  | T.Move mv -> munch_exp_acc (Inst.Temp mv.dest) mv.src []
  | T.Return e ->
    (match e with
    | None -> [ Inst.Ret { var = None } ]
    | Some e ->
      let t = Temp.create () in
      let inst = munch_exp_acc (Inst.Temp t) e [] in
      Inst.Ret { var = Some (Inst.Temp t) } :: inst)
  | Jump jmp -> [ Inst.Jump { target = jmp } ]
  | T.CJump cjmp ->
    let lhs = Inst.Temp (Temp.create ()) in
    let op = munch_op cjmp.op in
    let rhs = Inst.Temp (Temp.create ()) in
    let lhs_inst_rev = munch_exp_acc lhs cjmp.lhs [] in
    let rhs_inst_rev = munch_exp_acc rhs cjmp.rhs [] in
    (Inst.CJump
       { lhs; op; rhs; target_true = cjmp.target_true; target_false = cjmp.target_false }
    :: rhs_inst_rev)
    @ lhs_inst_rev
  | T.Label l -> [ Inst.Label l ]
  | T.Nop -> []
  | T.Effect eft ->
    let lhs = Inst.Temp (Temp.create ()) in
    let op = munch_op eft.op in
    let rhs = Inst.Temp (Temp.create ()) in
    let lhs_inst_rev = munch_exp_acc lhs eft.lhs [] in
    let rhs_inst_rev = munch_exp_acc rhs eft.rhs [] in
    (Inst.Binop { lhs; op; rhs; dest = Inst.Temp eft.dest } :: rhs_inst_rev)
    @ lhs_inst_rev
  | T.Assert asrt ->
    let t = Temp.create () in
    let inst = munch_exp_acc (Inst.Temp t) asrt [] in
    Inst.Assert (Inst.Temp t) :: inst
  | T.Fcall fcall ->
    let res =
      List.map fcall.args ~f:(fun arg ->
          let t = Inst.Temp (Temp.create ()) in
          let e = munch_exp_acc t arg [] in
          t, e)
    in
    let args, args_stms = List.unzip res in
    let args_stms_rev = List.rev args_stms |> List.concat in
    let call = Inst.Call { func_name = fcall.func_name; args; dest = fcall.dest } in
    call :: args_stms_rev

and munch_stms_rev stms res =
  match stms with
  | [] -> res
  | h :: t ->
    let stm = munch_stm_rev h in
    munch_stms_rev t res @ stm
;;

let gen_fdefn (fdefn : T.fdefn) : Inst.fdefn =
  let body = munch_stms_rev fdefn.body [] |> List.rev in
  let pars = fdefn.temps in
  { func_name = fdefn.func_name; body; pars }
;;

(* To codegen a series of statements, just concatenate the results of
* codegen-ing each statement. *)
let gen (fdefns : T.program) : Inst.program =
  List.map fdefns ~f:(fun fdefn -> gen_fdefn fdefn)
;;
