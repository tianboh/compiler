(* Notice the difference between CST and AST
   * CST is basically transferred from source code literaly.
   * AST add more structure statement unit based on CST, and it looks like a tree.
   *
   * Statement level benefit:
   * To be specific, AST classify statement from CST into below
   * 1) Asign(x,e)
   * 2) if(e,s,s)
   * 3) while(e,s)
   * 4) return(e)
   * 5) nop
   * 6) seq(s,s)
   * 7) declare(x,t,s)
   * The obvious advantage is that we can handle variable namespace more efficiently.
   * We can see if the use of x is in a declare statement. Notice that the use of x
   * may be nested in many seq statement in declare(x,t,s).
   * In addition, we will simplify for from CST to while statement in AST.
   * This will reduce the Intermediate Representation.
   *
   * Expression level benefit:
   * 1) logical operation && || ^ can be denoted in ternary expression, so IR does not
   *    logical operation anymore.
   * 2) <binop>= b can be simplified to a = a binop b
   * This can simplify our work in IR level
   * More details can be checked in
   * https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab2.pdf Page 5 and 6
   *
   * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
*)

module Mark = Util.Mark

(* 
 * CST exp -> AST exp
 * Our goal is to 
 * 1) Remove unary op in AST, including -, !, and ~
 * 2) Remove logical-logical op, indicating input and output are both logical ,
 * in AST, including && and ||
 * 3) Now we only have binary and ternary op, translate them to AST exp 
 *)
let rec elab_exp = function
  | Cst.Var var -> Ast.Var var
  | Cst.Const_int i -> Ast.Const_int i
  | Cst.True -> Ast.True
  | Cst.False -> Ast.False
  | Cst.Binop binop -> elab_binop binop.op binop.lhs binop.rhs
  | Cst.Unop unop -> elab_unop unop.op unop.operand
  | Cst.Terop terop -> elab_terop terop.cond terop.true_exp terop.false_exp

(* CST mexp -> AST mexp *)
and elab_mexp (cst_mexp : Cst.mexp) =
  let src_span = Mark.src_span cst_mexp in
  let exp = Mark.data cst_mexp in
  let strip_exp_ast = elab_exp exp in
  Mark.mark' strip_exp_ast src_span

and elab_binop (binop : Cst.binop) (lhs : Cst.mexp) (rhs : Cst.mexp) : Ast.exp =
  let lhs_ast = elab_mexp lhs in
  let rhs_ast = elab_mexp rhs in
  match binop with
  (* Use shortcircuit to handle && and || *)
  | Cst.And_and ->
    Ast.Terop { cond = lhs_ast; true_exp = rhs_ast; false_exp = Mark.naked Ast.False }
  | Cst.Or_or ->
    Ast.Terop { cond = lhs_ast; true_exp = Mark.naked Ast.True; false_exp = rhs_ast }
  (* Rest is only type transformation. *)
  | Cst.Plus -> Ast.Binop { op = Ast.Plus; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Minus -> Ast.Binop { op = Ast.Minus; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Times -> Ast.Binop { op = Ast.Times; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Divided_by -> Ast.Binop { op = Ast.Divided_by; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Modulo -> Ast.Binop { op = Ast.Modulo; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.And -> Ast.Binop { op = Ast.And; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Or -> Ast.Binop { op = Ast.Or; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Hat -> Ast.Binop { op = Ast.Hat; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Right_shift -> Ast.Binop { op = Ast.Right_shift; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Left_shift -> Ast.Binop { op = Ast.Left_shift; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Equal_eq -> Ast.Binop { op = Ast.Equal_eq; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Greater -> Ast.Binop { op = Ast.Greater; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Greater_eq -> Ast.Binop { op = Ast.Greater_eq; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Less -> Ast.Binop { op = Ast.Less; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Less_eq -> Ast.Binop { op = Ast.Less_eq; lhs = lhs_ast; rhs = rhs_ast }
  | Cst.Not_eq -> Ast.Binop { op = Ast.Not_eq; lhs = lhs_ast; rhs = rhs_ast }

and elab_unop (unop : Cst.unop) (operand : Cst.mexp) : Ast.exp =
  let operand_ast = elab_mexp operand in
  match unop with
  | Cst.Negative ->
    let lhs = Mark.naked (Ast.Const_int Int32.zero) in
    Ast.Binop { op = Ast.Minus; lhs; rhs = operand_ast }
  | Cst.Excalmation_mark ->
    Ast.Terop
      { cond = operand_ast
      ; true_exp = Mark.naked Ast.False
      ; false_exp = Mark.naked Ast.True
      }
  | Cst.Dash_mark ->
    let lhs = Mark.naked (Ast.Const_int Int32.min_int) in
    Ast.Binop { op = Ast.Minus; lhs; rhs = operand_ast }

and elab_terop (cond : Cst.mexp) (true_exp : Cst.mexp) (false_exp : Cst.mexp) : Ast.exp =
  let cond_ast = elab_mexp cond in
  let true_exp_ast = elab_mexp true_exp in
  let false_exp_ast = elab_mexp false_exp in
  Ast.Terop { cond = cond_ast; true_exp = true_exp_ast; false_exp = false_exp_ast }
;;

let elab_type = function
  | Cst.Int -> Ast.Int
  | Cst.Bool -> Ast.Bool
;;

let rec elaborate_internal (cst : Cst.program) (acc : Ast.program) : Ast.program =
  match cst with
  | [] -> acc
  | h :: t ->
    let ast_head, cst_tail = elab_stm h t in
    let acc = Ast.Seq { head = acc; tail = ast_head } in
    elaborate_internal cst_tail (Mark.naked acc)

(* Though we are elaborating current statement, the tail is required
 * during process because in some cases, like declare, we need the following 
 * context for AST unit. Also, we need to return the tail after process to 
 * avoid redo elaboration in elaborate_internal function.
 *
 * Return: Elaborated AST statement from CST head and the remaining CST tail.
 *)
and elab_stm (head : Cst.mstm) (tail : Cst.mstms) : Ast.program * Cst.program =
  let src_span = Mark.src_span head in
  match Util.Mark.data head with
  | Cst.Simp simp -> elab_simp simp src_span tail
  | Cst.Control ctl -> elab_control ctl src_span, tail
  | Cst.Block blk -> elaborate_internal blk (Mark.naked Ast.Nop), tail

(* simp: CST simp statement
 * src_span: location of simp in source code, thie will be marked to AST.
 * This is crucial for pinpoint the location during semantic analysis in AST
 * tail: remaining CST statements to process
 * Return AST head and remaining CST tails *)
and elab_simp (simp : Cst.simp) (src_span : Mark.src_span option) (tail : Cst.mstms)
    : Ast.program * Cst.program
  =
  match simp with
  | Cst.Declare decl -> elab_declare decl src_span tail
  | Cst.Assign asn ->
    let asn_ast = Ast.Assign { name = asn.name; value = elab_mexp asn.value } in
    Mark.mark' asn_ast src_span, tail
  | Cst.Exp exp -> Mark.mark' (Ast.Sexp (elab_mexp exp)) src_span, tail

and elab_declare (decl : Cst.decl) (src_span : Mark.src_span option) (tail : Cst.mstms) =
  match decl with
  | New_var var ->
    let ast_tail = elaborate_internal tail (Mark.naked Ast.Nop) in
    let decl_ast =
      Ast.Declare { t = elab_type var.t; name = var.name; tail = ast_tail }
    in
    Mark.mark' decl_ast src_span, []
  | Init init ->
    let ast_tail = elaborate_internal tail (Mark.naked Ast.Nop) in
    let assign = Ast.Assign { name = init.name; value = elab_mexp init.value } in
    let seq = Ast.Seq { head = Mark.mark' assign src_span; tail = ast_tail } in
    let decl_ast =
      Ast.Declare { t = elab_type init.t; name = init.name; tail = Mark.naked seq }
    in
    Mark.mark' decl_ast src_span, []

(* Return: AST statement. *)
and elab_control ctl (src_span : Mark.src_span option) =
  match ctl with
  | If if_stm ->
    let false_stm, _ =
      match if_stm.false_stm with
      | None -> Mark.naked Ast.Nop, []
      | Some s -> elab_stm s []
    in
    let true_stm, _ = elab_stm if_stm.true_stm [] in
    let if_ast = Ast.If { cond = elab_mexp if_stm.cond; true_stm; false_stm } in
    Mark.mark' if_ast src_span
  | While while_stm ->
    let body, _ = elab_stm while_stm.body [] in
    let cond = elab_mexp while_stm.cond in
    let while_ast = Ast.While { cond; body } in
    Mark.mark' while_ast src_span
  (* We elaborate CST "for" to AST "while" for simplicity *)
  | For for_stm ->
    let body_cst =
      match for_stm.iter with
      | None -> Cst.Block [ for_stm.body ]
      | Some simp ->
        let src_span_iter = Mark.src_span simp in
        let iter_cst = Cst.Simp (Mark.data simp) in
        Cst.Block [ for_stm.body; Mark.mark' iter_cst src_span_iter ]
    in
    let src_span_body = Mark.src_span for_stm.body in
    let while_cst =
      Cst.While { cond = for_stm.cond; body = Mark.mark' body_cst src_span_body }
    in
    let for_ast =
      match for_stm.init with
      | None -> elab_control while_cst src_span_body
      | Some init ->
        let src_span_init = Mark.src_span init in
        let init_cst = Cst.Simp (Mark.data init) in
        let init_cst = Mark.mark' init_cst src_span_init in
        let cst_program =
          [ init_cst; Mark.mark' (Cst.Control while_cst) src_span_body ]
        in
        elaborate_internal cst_program (Mark.naked Ast.Nop)
    in
    for_ast
  | Return ret ->
    let src_span_ret = Mark.src_span ret in
    let ret_ast = Mark.mark' (Ast.Return (elab_mexp ret)) src_span_ret in
    ret_ast
;;

let elaborate (cst : Cst.program) : Ast.program =
  elaborate_internal cst (Mark.naked Ast.Nop)
;;
