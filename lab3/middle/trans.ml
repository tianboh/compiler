(* L3 Compiler
 * AST -> IR Translator
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified by: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
open Core
module A = Front.Ast
module S = Util.Symbol.Map
module Symbol = Util.Symbol
module T = Tree
module Label = Util.Label
module Mark = Util.Mark
module Temp = Var.Temp

let trans_binop = function
  (* II *)
  | A.Plus -> T.Plus
  | A.Minus -> T.Minus
  | A.Times -> T.Times
  | A.Divided_by -> T.Divided_by
  | A.Modulo -> T.Modulo
  | A.And -> T.And
  | A.Or -> T.Or
  | A.Hat -> T.Xor
  | A.Right_shift -> T.Right_shift
  | A.Left_shift -> T.Left_shift
  (* IB *)
  | A.Equal_eq -> T.Equal_eq
  | A.Greater -> T.Greater
  | A.Greater_eq -> T.Greater_eq
  | A.Less -> T.Less
  | A.Less_eq -> T.Less_eq
  | A.Not_eq -> T.Not_eq
;;

let gen_cond (exp : T.exp) : T.exp * T.binop * T.exp =
  match exp with
  | T.Const i -> T.Const i, T.Equal_eq, T.Const Int32.one
  | T.Temp t -> T.Temp t, T.Equal_eq, T.Const Int32.one
  | T.Binop binop -> binop.lhs, binop.op, binop.rhs
  | T.Sexp sexp -> T.Sexp sexp, T.Equal_eq, T.Const Int32.one
;;

let rec trans_exp (exp_ast : A.exp) (env : Temp.t S.t) =
  match exp_ast with
  (* after type-checking, id must be declared; do not guard lookup *)
  | A.Var id -> T.Temp (S.find_exn env id)
  | A.Const_int c -> T.Const c
  | A.True -> T.Const Int32.one
  | A.False -> T.Const Int32.zero
  | A.Binop binop ->
    T.Binop
      { op = trans_binop binop.op
      ; lhs = trans_mexp binop.lhs env
      ; rhs = trans_mexp binop.rhs env
      }
  (* 
   * CJump cond label_true
   * label_dummy
   * Jump target_false
   * label_true:
   * a <- true_exp;
   * Jump label_ter_end
   * label_false:
   * a <- false_exp
   * label_ter_end:
   * restcode
   *)
  | A.Terop terop ->
    let cond_raw = trans_mexp terop.cond env in
    let true_exp = trans_mexp terop.true_exp env in
    let false_exp = trans_mexp terop.false_exp env in
    let temp = Temp.create () in
    let label_true = Label.label (Some "terop_true") in
    let label_false = Label.label (Some "terop_false") in
    let label_dummy = Label.label (Some "cjp_dummy") in
    let label_ter_end = Label.label (Some "terop_end") in
    let lhs, op, rhs = gen_cond cond_raw in
    let seq =
      [ T.CJump { lhs; op; rhs; target_stm = label_true }
      ; T.Label label_dummy
      ; T.Jump label_false
      ; T.Label label_true
      ; T.Move { dest = temp; src = true_exp }
      ; T.Jump label_ter_end
      ; T.Label label_false
      ; T.Move { dest = temp; src = false_exp }
      ; T.Label label_ter_end
      ]
    in
    T.Sexp { stm = seq; exp = T.Temp temp }

and trans_mexp mexp env = trans_exp (Mark.data mexp) env

(* env keep trakcs from variable name to temporary. Two things keep in mind
 * 1) variable name can be the same in different scope (scope has no intersection).
 * So env will update in different context. 
 * 2) env is only a map from variable name to temporary, it doesn't care the 
 * content of temporary. So we only add this linkage in declaration. *)
let rec trans_stm_rev (ast : A.mstm) (acc : T.stm list) (env : Temp.t S.t) : T.stm list =
  match Mark.data ast with
  | A.Assign asn_ast ->
    let dest = S.find_exn env asn_ast.name in
    let value = trans_mexp asn_ast.value env in
    T.Move { dest; src = value } :: acc
  | A.If if_ast ->
    (* 
     *  CJump cond label_true
     *  label_false
     *  false_stm
     *  Jump label_conv
     *  label_true
     *  true_stm
     *  label_conv
     *  rest code blah blah
     *)
    let cond_raw = trans_mexp if_ast.cond env in
    let label_false = Label.label (Some "if_false") in
    let label_true = Label.label (Some "if_true") in
    let label_conv = Label.label (Some "if_conv") in
    let false_stm = trans_stm_rev if_ast.false_stm [] env in
    let true_stm = trans_stm_rev if_ast.true_stm [] env in
    let lhs, op, rhs = gen_cond cond_raw in
    (T.Label label_conv :: true_stm)
    @ [ T.Label label_true; T.Jump label_conv ]
    @ false_stm
    @ [ T.Label label_false; T.CJump { lhs; op; rhs; target_stm = label_true } ]
    @ acc
  | A.While while_ast ->
    (* 
     * Jump label_loop_stop
     * label_loop_start
     * body
     * label_loop_stop
     * CJump cond label_loop_start
     * label_loop_dummy
     * rest blah blah *)
    let cond_raw = trans_mexp while_ast.cond env in
    let body = trans_stm_rev while_ast.body [] env in
    let label_loop_start = Label.label (Some "loop_start") in
    let label_loop_stop = Label.label (Some "loop_stop") in
    let label_loop_dummy = Label.label (Some "loop_dummy") in
    let lhs, op, rhs = gen_cond cond_raw in
    [ T.Label label_loop_dummy
    ; T.CJump { lhs; op; rhs; target_stm = label_loop_start }
    ; T.Label label_loop_stop
    ]
    @ body
    @ [ T.Label label_loop_start ]
    @ [ T.Jump label_loop_stop ]
    @ acc
  | A.Return ret_ast ->
    let exp = trans_mexp ret_ast env in
    let ret = T.Return exp in
    [ T.Label (Label.label (Some "afterlife")); ret ] @ acc
  | A.Nop -> T.Nop :: acc
  | A.Seq seq_ast ->
    let head = trans_stm_rev seq_ast.head [] env in
    let tail = trans_stm_rev seq_ast.tail [] env in
    tail @ head @ acc
  | A.Declare decl_ast ->
    let temp = Temp.create () in
    let env' = S.add_exn env ~key:decl_ast.name ~data:temp in
    let tail = trans_stm_rev decl_ast.tail [] env' in
    tail @ acc
  | A.Sexp sexp_ast ->
    let exp = trans_mexp sexp_ast env in
    T.NExp exp :: acc
;;

let translate (program : A.program) : T.program =
  let env = S.empty in
  let blk_rev = trans_stm_rev program [] env in
  List.rev blk_rev
;;
