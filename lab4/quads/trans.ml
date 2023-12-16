open Core
module Tree = Ir_tree.Inst
module Quads = Inst
module Temp = Var.Temp
module Register = Var.X86_reg.Logic
module Memory = Var.Memory
module Label = Util.Label
module Size = Var.Size

let shift_maximum_bit = Int64.of_int_exn 31 (* inclusive *)

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

(* get Tree.sexp size *)
(* let sizeof_exp : Tree.sexp -> Size.primitive = function
  | Void -> failwith "void doesn't have esize"
  | Const i -> (i.size :> Size.primitive)
  | Temp t -> t.size
  | Binop _ -> `DWORD
;; *)

let get_size (op : Inst.operand) =
  match op with
  | Imm i -> (i.size :> Size.primitive)
  | Temp t -> t.size
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
let rec munch_exp_acc
    (dest : Quads.operand)
    (exp : Tree.sexp)
    (rev_acc : Quads.instr list)
    : Quads.instr list
  =
  match exp.data with
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
    ((binop, e1, e2) : Tree.binop * Tree.sexp * Tree.sexp)
    (rev_acc : Quads.instr list)
    : Quads.instr list
  =
  let op = munch_op binop in
  (* Notice we fix the left hand side operand and destination the same to meet x86 instruction. *)
  let size = get_size dest in
  let t1 = Temp.create size in
  let t2 = Temp.create size in
  let rev_acc' =
    rev_acc |> munch_exp_acc (Quads.Temp t1) e1 |> munch_exp_acc (Quads.Temp t2) e2
  in
  Quads.Binop { op; dest; lhs = Quads.Temp t1; rhs = Quads.Temp t2 } :: rev_acc'

(* munch_exp dest exp
 * Generates instructions for dest <-- exp. *)
and munch_exp : Quads.operand -> Tree.sexp -> Quads.instr list =
 fun dest exp ->
  (* Since munch_exp_acc returns the reversed accumulator, we must
   * reverse the list before returning. *)
  List.rev (munch_exp_acc dest exp [])

and[@warning "-8"] munch_effect_rev (Tree.Effect eft) : Quads.instr list =
  let lhs_size = eft.lhs.size in
  let lhs = Quads.Temp (Temp.create lhs_size) in
  let op = munch_op eft.op in
  let rhs_size = eft.rhs.size in
  let rhs = Quads.Temp (Temp.create rhs_size) in
  let lhs_inst_rev = munch_exp_acc lhs eft.lhs [] in
  let rhs_inst_rev = munch_exp_acc rhs eft.rhs [] in
  let safety_check_rev =
    match eft.op with
    | Right_shift | Left_shift ->
      let l1 = Label.label None in
      let l2 = Label.label None in
      let l3 = Label.label None in
      let l4 = Label.label None in
      [ Quads.Label l4
      ; Quads.Fcall
          { func_name = Util.Symbol.Fname.raise
          ; dest = None
          ; args = [ Quads.Imm { v = Util.Symbol.Fname.fpe; size = `DWORD } ]
          ; scope = `Internal
          }
      ; Quads.Label l3
      ; Quads.Jump { target = l4 }
      ; Quads.Label l2
      ; Quads.CJump
          { lhs = rhs
          ; op = Quads.Less
          ; rhs = Quads.Imm { v = Int64.zero; size = `DWORD }
          ; target_true = l3
          ; target_false = l2
          }
      ; Quads.Label l1
      ; Quads.CJump
          { lhs = rhs
          ; op = Quads.Greater
          ; rhs = Quads.Imm { v = shift_maximum_bit; size = `DWORD }
          ; target_true = l3
          ; target_false = l1
          }
      ]
    | Divided_by | Modulo -> []
    | _ -> failwith "not effect binop"
  in
  ((Quads.Binop { lhs; op; rhs; dest = Quads.Temp eft.dest } :: safety_check_rev)
  @ rhs_inst_rev)
  @ lhs_inst_rev

(* Return a reversed Quads.instr list. *)
and munch_stm_rev (stm : Tree.stm) : Quads.instr list =
  match stm with
  | Tree.Move mv -> munch_exp_acc (Quads.Temp mv.dest) mv.src []
  | Tree.Return e ->
    (match e with
    | None -> [ Quads.Ret { var = None } ]
    | Some e ->
      let size = e.size in
      let t = Temp.create size in
      let inst = munch_exp_acc (Quads.Temp t) e [] in
      Quads.Ret { var = Some (Quads.Temp t) } :: inst)
  | Jump jmp -> [ Quads.Jump { target = jmp } ]
  | Tree.CJump cjmp ->
    let lhs_size = cjmp.lhs.size in
    let lhs = Quads.Temp (Temp.create lhs_size) in
    let op = munch_op cjmp.op in
    let rhs_size = cjmp.rhs.size in
    let rhs = Quads.Temp (Temp.create rhs_size) in
    let lhs_inst_rev = munch_exp_acc lhs cjmp.lhs [] in
    let rhs_inst_rev = munch_exp_acc rhs cjmp.rhs [] in
    (Quads.CJump
       { lhs; op; rhs; target_true = cjmp.target_true; target_false = cjmp.target_false }
    :: rhs_inst_rev)
    @ lhs_inst_rev
  | Tree.Label l -> [ Quads.Label l ]
  | Tree.Nop -> []
  | Tree.Effect eft -> munch_effect_rev (Tree.Effect eft)
  | Tree.Assert asrt ->
    let size = `DWORD in
    let t = Temp.create size in
    let inst = munch_exp_acc (Quads.Temp t) asrt [] in
    let pass = Label.label None in
    let fail = Label.label None in
    [ Quads.Label pass
    ; Quads.Fcall
        { func_name = Util.Symbol.Fname.raise
        ; dest = None
        ; args = [ Quads.Imm { v = Util.Symbol.Fname.abrt; size } ]
        ; scope = `Internal
        }
    ; Quads.Label fail
    ; Quads.CJump
        { lhs = Quads.Temp t
        ; op = Quads.Equal_eq
        ; rhs = Quads.Imm { v = Int64.one; size }
        ; target_true = pass
        ; target_false = fail
        }
    ]
    @ inst
  | Tree.Fcall fcall ->
    let args, args_stms_rev =
      List.map fcall.args ~f:(fun arg ->
          let s = arg.size in
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
      if Base.Int64.( = ) load.src.disp 0L
      then load.src.base
      else (
        let lhs =
          ({ data = Tree.Const { v = load.src.disp; size = `QWORD }; size = `QWORD }
            : Tree.sexp)
        in
        { data = Tree.Binop { lhs; rhs = load.src.base; op = Plus }; size = `QWORD })
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
      if Base.Int64.( = ) store.dest.disp 0L
      then store.dest.base
      else (
        let lhs =
          ({ data = Tree.Const { v = store.dest.disp; size = `QWORD }; size = `QWORD }
            : Tree.sexp)
        in
        ({ data = Tree.Binop { lhs; rhs = store.dest.base; op = Plus }; size = `QWORD }
          : Tree.sexp))
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
    let src = Quads.Temp (Temp.create store.src.size) in
    let src_instr = munch_exp_acc src store.src [] in
    let store = Quads.Store { src; dest = mem } in
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
  let pars = fdefn.temps in
  { func_name = fdefn.func_name; body; pars; scope = fdefn.scope }
;;

(* To codegen a series of statements, just concatenate the results of
* codegen-ing each statement. *)
let gen (fdefns : Tree.program) : Quads.program =
  List.map fdefns ~f:(fun fdefn -> gen_fdefn fdefn)
;;
