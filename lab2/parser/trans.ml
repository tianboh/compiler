(* L2 Compiler
 * AST -> IR Translator
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 * Created: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified by: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)
open Core
module A = Ast
module S = Util.Symbol.Map
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
  | A.Hat -> T.Hat
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
  (* a <- true_exp;
   * CJump cond target
   * a <- false_exp
   * target.
   * rest code
   *)
  | A.Terop terop ->
    let cond = trans_mexp terop.cond env in
    let true_exp = trans_mexp terop.true_exp env in
    let false_exp = trans_mexp terop.false_exp env in
    let temp = Temp.create () in
    let label_target = Label.label (Some "terop_true") in
    let asn = T.Move { dest = temp; src = true_exp } in
    let seq_cj =
      T.Seq
        { head =
            T.Seq
              { head = T.CJump { cond; target_stm = label_target }
              ; tail = T.Move { dest = temp; src = false_exp }
              }
        ; tail = T.Label label_target
        }
    in
    let seq = T.Seq { head = asn; tail = seq_cj } in
    T.Sexp { stm = seq; exp = T.Temp temp }

and trans_mexp mexp env = trans_exp (Mark.data mexp) env

(* env keep trakcs from variable name to temporary. Two things keep in mind
 * 1) variable name can be the same in different scope (scope has no intersection).
 * So env will update in different context. 
 * 2) env is only a map from variable name to temporary, it doesn't care the 
 * content of temporary. So we only add this linkage in declaration. *)

let rec trans_stm (ast : A.program) (env : Temp.t S.t) : T.program =
  match Mark.data ast with
  | A.Assign asn_ast ->
    let dest = S.find_exn env asn_ast.name in
    let value = trans_mexp asn_ast.value env in
    T.Move { dest; src = value }
  | A.If if_ast ->
    (* 
     *  CJump cond true_label
     *  false_stm
     *  Jump converge_label
     *  true_label
     *  true_stm
     *  converge_label
     *  rest code blah blah
     *)
    let cond = trans_mexp if_ast.cond env in
    let label_true = Label.label (Some "if_true") in
    let label_conv = Label.label (Some "if_conv") in
    let false_stm = trans_stm if_ast.false_stm env in
    let seq_false =
      T.Seq
        { head = T.CJump { cond; target_stm = label_true }
        ; tail = T.Seq { head = false_stm; tail = T.Jump label_conv }
        }
    in
    let true_stm = trans_stm if_ast.true_stm env in
    let seq_true =
      T.Seq
        { head = T.Label label_true
        ; tail = T.Seq { head = true_stm; tail = T.Label label_conv }
        }
    in
    T.Seq { head = seq_false; tail = seq_true }
  | A.While while_ast ->
    (* 
     * Jump label_loop_stop
     * label_loop_start
     * body
     * label_loop_stop
     * CJump cond label_loop_start *)
    let cond = trans_mexp while_ast.cond env in
    let body = trans_stm while_ast.body env in
    let label_loop_start = Label.label (Some "loop_start") in
    let label_loop_stop = Label.label (Some "loop_stop") in
    let seq1 =
      T.Seq
        { head = T.Label label_loop_stop
        ; tail = T.CJump { cond; target_stm = label_loop_start }
        }
    in
    let seq2 = T.Seq { head = body; tail = seq1 } in
    let seq3 = T.Seq { head = T.Label label_loop_start; tail = seq2 } in
    let seq4 = T.Seq { head = T.Jump label_loop_stop; tail = seq3 } in
    seq4
  | A.Return ret_ast ->
    let exp = trans_mexp ret_ast env in
    T.Return exp
  | A.Nop -> T.Nop
  | A.Seq seq_ast ->
    let head = trans_stm seq_ast.head env in
    let tail = trans_stm seq_ast.tail env in
    T.Seq { head; tail }
  | A.Declare decl_ast ->
    let temp = Temp.create () in
    let env' = S.add_exn env ~key:decl_ast.name ~data:temp in
    let tail = trans_stm decl_ast.tail env' in
    tail
  | A.Sexp sexp_ast ->
    let exp = trans_mexp sexp_ast env in
    T.NExp exp
;;

let translate (stms : A.program) : T.program = trans_stm stms S.empty
