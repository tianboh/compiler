(* L4 Compiler
 * IR -> Quads 
 *
 * Each instruction do not have nested operand 
 * after transformation.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
module Tree = Ir_tree.Inst
module Quads = Inst
module Temp = Var.Temp
module Register = Var.X86_reg.Logic
module Label = Util.Label
module Size = Var.Size
module Fname = Util.Symbol.Fname
module Op = Quads.Op
module Sop = Quads.Sop
module Sexp = Tree.Sexp
module St = Quads.St

let munch_op : Tree.binop -> Quads.binop = function
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
 *
 * Cast operand(s) to align destination size.
 *)
let rec munch_exp_acc (dest : St.t) (exp : Sexp.t) (rev_acc : Quads.instr list)
    : Quads.instr list
  =
  match exp.data with
  | Void -> rev_acc
  | Const i -> Mov { dest; src = Op.of_int i |> Sop.wrap dest.size } :: rev_acc
  | Temp t ->
    let src, cast_instr = cast_helper dest.size (t |> St.wrap exp.size) in
    (Quads.Mov { dest; src = St.to_Sop src } :: cast_instr) @ rev_acc
  | Binop binop -> munch_binop_acc dest (binop.op, binop.lhs, binop.rhs) rev_acc
  | BISD bisd ->
    let base, index, scale, disp = Tree.Addr.get bisd in
    munch_bisd_acc dest base index scale disp rev_acc

and cast_helper (dest_size : Size.primitive) (st : St.t) : St.t * Quads.instr list =
  if Size.compare (dest_size :> Size.t) (st.size :> Size.t) <> 0
  then (
    let t = St.to_t st in
    let st' = St.wrap dest_size t in
    st', [ Cast { dest = st'; src = st } ])
  else st, []

and munch_bisd_acc
    (dest : St.t)
    (base : Sexp.t)
    (index : Sexp.t option)
    (scale : Int64.t option)
    (disp : Int64.t option)
    (rev_acc : Quads.instr list)
    : Quads.instr list
  =
  let size = dest.size in
  match disp, index, scale with
  | None, None, _ | None, _, None -> munch_exp_acc dest base rev_acc
  | Some disp, None, _ | Some disp, _, None ->
    let t_disp = Temp.create () |> St.wrap size in
    let t_base = Temp.create () |> St.wrap size in
    let rev_acc' =
      rev_acc
      |> munch_exp_acc t_base base
      |> munch_exp_acc t_disp (disp |> Tree.Exp.of_int |> Sexp.wrap size)
    in
    Quads.Binop { op = Plus; dest; lhs = St.to_Sop t_base; rhs = St.to_Sop t_disp }
    :: rev_acc'
  | _, Some index, Some scale ->
    let t_base = Temp.create () |> St.wrap size in
    let t_index = Temp.create () |> St.wrap size in
    let t_scale = Temp.create () |> St.wrap size in
    let t_offset = Temp.create () |> St.wrap size in
    let rev_acc' =
      rev_acc
      |> munch_exp_acc t_base base
      |> munch_exp_acc t_index index
      |> munch_exp_acc t_scale (scale |> Tree.Exp.of_int |> Sexp.wrap size)
    in
    let rev_acc'' =
      Quads.Binop
        { op = Times; dest = t_offset; lhs = St.to_Sop t_index; rhs = St.to_Sop t_scale }
      :: rev_acc'
    in
    (match disp with
    | None ->
      Quads.Binop { op = Plus; dest; lhs = St.to_Sop t_base; rhs = St.to_Sop t_offset }
      :: rev_acc''
    | Some disp ->
      let t_disp = Temp.create () |> St.wrap size in
      let ret =
        rev_acc'' |> munch_exp_acc t_disp (disp |> Tree.Exp.of_int |> Sexp.wrap size)
      in
      let t = Temp.create () |> St.wrap size in
      [ Quads.Binop { op = Plus; dest; lhs = St.to_Sop t; rhs = St.to_Sop t_disp }
      ; Quads.Binop
          { op = Plus; dest = t; lhs = St.to_Sop t_base; rhs = St.to_Sop t_offset }
      ]
      @ ret)

(* munch_binop_acc dest (binop, e1, e2) rev_acc
*
* generates instructions to achieve dest <- e1 binop e2
*
* Much like munch_exp, this returns the result of appending the
* instructions in reverse to the accumulator argument, rev_acc.
*)
and munch_binop_acc
    (dest : St.t)
    ((binop, e1, e2) : Tree.binop * Sexp.t * Sexp.t)
    (rev_acc : Quads.instr list)
    : Quads.instr list
  =
  let op = munch_op binop in
  let t1 = Temp.create () |> St.wrap e1.size in
  let t2 = Temp.create () |> St.wrap e2.size in
  let rev_acc' = rev_acc |> munch_exp_acc t1 e1 |> munch_exp_acc t2 e2 in
  let t1, cast1 = cast_helper dest.size t1 in
  let t2, cast2 = cast_helper dest.size t2 in
  (Quads.Binop { op; dest; lhs = St.to_Sop t1; rhs = St.to_Sop t2 } :: cast2)
  @ cast1
  @ rev_acc'

(* munch_exp dest exp
 * Generates instructions for dest <-- exp. *)
and munch_exp : St.t -> Sexp.t -> Quads.instr list =
 fun dest exp ->
  (* Since munch_exp_acc returns the reversed accumulator, we must
   * reverse the list before returning. *)
  List.rev (munch_exp_acc dest exp [])

and[@warning "-8"] munch_effect_rev (Tree.Effect eft) : Quads.instr list =
  let lhs_size = eft.lhs.size in
  let lhs = Temp.create () |> St.wrap lhs_size in
  let op = munch_op eft.op in
  let rhs_size = eft.rhs.size in
  let rhs = Temp.create () |> St.wrap rhs_size in
  let dest = St.wrap eft.dest.size eft.dest.data in
  let lhs_inst_rev = munch_exp_acc lhs eft.lhs [] in
  let rhs_inst_rev = munch_exp_acc rhs eft.rhs [] in
  let safety_check_rev =
    match eft.op with
    | Right_shift | Left_shift ->
      let l1 = Label.label None in
      let l2 = Label.label None in
      let l3 = Label.label None in
      let l4 = Label.label None in
      let sigfpe = Sop.wrap `DWORD (Op.of_int Fname.fpe) in
      let zero = Sop.wrap rhs_size (Op.of_int 0L) in
      let shift_bound = Sop.wrap rhs_size (Op.of_int Fname.shift_bound) in
      [ Quads.Label l4
      ; Quads.Fcall
          { func_name = Fname.raise; dest = None; args = [ sigfpe ]; scope = `External }
      ; Quads.Label l3
      ; Quads.Jump { target = l4 }
      ; Quads.Label l2
      ; Quads.CJump
          { lhs = St.to_Sop rhs
          ; op = Quads.Less
          ; rhs = zero
          ; target_true = l3
          ; target_false = l2
          }
      ; Quads.Label l1
      ; Quads.CJump
          { lhs = St.to_Sop rhs
          ; op = Quads.Greater
          ; rhs = shift_bound
          ; target_true = l3
          ; target_false = l1
          }
      ]
    | Divided_by | Modulo -> []
    | _ -> failwith "not effect binop"
  in
  ((Quads.Binop { dest; lhs = St.to_Sop lhs; op; rhs = St.to_Sop rhs } :: safety_check_rev)
  @ rhs_inst_rev)
  @ lhs_inst_rev

(* Return a reversed Quads.instr list. *)
and munch_stm_rev (stm : Tree.stm) : Quads.instr list =
  let sexp2st (exp : Sexp.t option) : St.t option =
    match exp with
    | Some e -> Some (Temp.create () |> St.wrap e.size)
    | None -> None
  in
  let st2sop (t : St.t option) : Sop.t option =
    match t with
    | None -> None
    | Some t -> Some (St.to_Sop t)
  in
  let munch_helper (t : St.t option) (exp : Sexp.t option) (rev_acc : Quads.instr list)
      : Quads.instr list
    =
    match t, exp with
    | None, None -> rev_acc
    | Some t, Some exp -> munch_exp_acc t exp rev_acc
    | _ -> failwith "t and exp should consist"
  in
  let get_addr
      (base : Sexp.t)
      (index : Sexp.t option)
      (scale : Int64.t option)
      (disp : Int64.t option)
      : Quads.Addr.t * Quads.instr list
    =
    let t_base = Temp.create () |> St.wrap base.size in
    let t_index = sexp2st index in
    let rev_acc = munch_exp_acc t_base base [] in
    let rev_acc = munch_helper t_index index rev_acc in
    let op_base = St.to_Sop t_base in
    let op_index = st2sop t_index in
    Quads.Addr.of_bisd op_base op_index scale disp, rev_acc
  in
  match stm with
  | Tree.Cast cast ->
    let dest = St.wrap cast.dest.size cast.dest.data in
    let temp = Temp.create () |> St.wrap cast.src.size in
    let move = munch_exp_acc temp cast.src [] in
    Quads.Cast { dest; src = temp } :: move
  | Tree.Move mv ->
    let size, data = mv.dest.size, mv.dest.data in
    let dest = St.wrap size data in
    munch_exp_acc dest mv.src []
  | Tree.Return e ->
    (match e with
    | None -> [ Quads.Ret { var = None } ]
    | Some e ->
      let size = e.size in
      let t = Temp.create () |> St.wrap size in
      let inst = munch_exp_acc t e [] in
      Quads.Ret { var = Some (St.to_Sop t) } :: inst)
  | Jump jmp -> [ Quads.Jump { target = jmp } ]
  | Tree.CJump cjmp ->
    let lhs_size = cjmp.lhs.size in
    let lhs = Temp.create () |> St.wrap lhs_size in
    let op = munch_op cjmp.op in
    let rhs_size = cjmp.rhs.size in
    let rhs = Temp.create () |> St.wrap rhs_size in
    let lhs_inst_rev = munch_exp_acc lhs cjmp.lhs [] in
    let rhs_inst_rev = munch_exp_acc rhs cjmp.rhs [] in
    (Quads.CJump
       { lhs = St.to_Sop lhs
       ; op
       ; rhs = St.to_Sop rhs
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
    let exp = Temp.create () |> St.wrap size in
    let inst = munch_exp_acc exp asrt [] in
    let pass = Label.label None in
    let fail = Label.label None in
    let sigabrt = Fname.abrt |> Quads.Op.of_int |> Quads.Sop.wrap size in
    let one = 1L |> Quads.Op.of_int |> Quads.Sop.wrap size in
    [ Quads.Label pass
    ; Quads.Fcall
        { func_name = Fname.raise; dest = None; args = [ sigabrt ]; scope = `External }
    ; Quads.Label fail
    ; Quads.CJump
        { lhs = St.to_Sop exp
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
          let t = Temp.create () |> St.wrap arg.size in
          let e = munch_exp_acc t arg [] in
          St.to_Sop t, e)
      |> List.unzip
    in
    let args_stms_rev = List.concat args_stms_rev in
    let dest : St.t option =
      match fcall.dest with
      | None -> None
      | Some s -> Some { data = s.data; size = s.size }
    in
    let func_name = fcall.func_name in
    let call = Quads.Fcall { func_name; args; dest; scope = fcall.scope } in
    call :: args_stms_rev
  | Tree.Load load ->
    let base, index, scale, disp = Tree.Addr.get load.src.data in
    let addr, rev_acc = get_addr base index scale disp in
    let mem = Quads.Mem.wrap load.src.size addr in
    let dest = St.wrap load.dest.size load.dest.data in
    let load = Quads.Load { src = mem; dest } in
    load :: rev_acc
  | Tree.Store store ->
    let base, index, scale, disp = Tree.Addr.get store.dest.data in
    let addr, rev_acc = get_addr base index scale disp in
    let mem = Quads.Mem.wrap store.dest.size addr in
    let t_src = Temp.create () |> St.wrap store.src.size in
    let rev_acc = munch_exp_acc t_src store.src rev_acc in
    let src = St.to_Sop t_src in
    let store = Quads.Store { src; dest = mem } in
    store :: rev_acc

and munch_stms stms res =
  match stms with
  | [] -> res |> List.rev
  | h :: t ->
    let stm = munch_stm_rev h in
    munch_stms t (stm @ res)
;;

let gen_fdefn (fdefn : Tree.fdefn) : Quads.fdefn =
  let body = munch_stms fdefn.body [] in
  let pars =
    List.map fdefn.temps ~f:(fun par : St.t -> { data = par.data; size = par.size })
  in
  { func_name = fdefn.func_name; body; pars }
;;

(* To codegen a series of statements, just concatenate the results of
* codegen-ing each statement. *)
let gen (fdefns : Tree.program) : Quads.program =
  List.map fdefns ~f:(fun fdefn -> gen_fdefn fdefn)
;;
