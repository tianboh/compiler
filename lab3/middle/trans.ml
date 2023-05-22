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

(* `Pure is expression that not lead to side-effect
 * `Impure is expression that may lead to side-effect, 
 * like rasing div-zero or other exception
 * `Compare is return boolean value. *)
let trans_binop = function
  | A.Plus -> `Pure T.Plus
  | A.Minus -> `Pure T.Minus
  | A.Times -> `Pure T.Times
  | A.And -> `Pure T.And
  | A.Or -> `Pure T.Or
  | A.Hat -> `Pure T.Xor
  | A.Right_shift -> `Impure T.Right_shift
  | A.Left_shift -> `Impure T.Left_shift
  | A.Divided_by -> `Impure T.Divided_by
  | A.Modulo -> `Impure T.Modulo
  | A.Equal_eq -> `Compare T.Equal_eq
  | A.Greater -> `Compare T.Greater
  | A.Greater_eq -> `Compare T.Greater_eq
  | A.Less -> `Compare T.Less
  | A.Less_eq -> `Compare T.Less_eq
  | A.Not_eq -> `Compare T.Not_eq
;;

let gen_cond (exp : T.exp) : T.exp * T.binop * T.exp =
  match exp with
  | T.Const i -> T.Const i, T.Equal_eq, T.Const Int32.one
  | T.Temp t -> T.Temp t, T.Equal_eq, T.Const Int32.one
  | T.Binop binop -> binop.lhs, binop.op, binop.rhs
;;

(* Return statement lists that include effect(can be empty), 
 * and the pure exp without side-effect *)
let rec trans_exp (exp_ast : A.exp) (env : Temp.t S.t) : T.stm list * T.exp =
  match exp_ast with
  (* after type-checking, id must be declared; do not guard lookup *)
  | A.Var id -> [], T.Temp (S.find_exn env id)
  | A.Const_int c -> [], T.Const c
  | A.True -> [], T.Const Int32.one
  | A.False -> [], T.Const Int32.zero
  | A.Binop binop -> trans_exp_bin (A.Binop binop) env
  (* 
   * CJump cond label_true, label_false
   * label_true:
   * a <- true_exp;
   * Jump label_ter_end
   * label_false:
   * a <- false_exp
   * label_ter_end:
   * restcode
   *)
  | A.Terop terop ->
    let cond_stms, cond_exp = trans_mexp terop.cond env in
    let true_stms, true_exp = trans_mexp terop.true_exp env in
    let false_stms, false_exp = trans_mexp terop.false_exp env in
    let temp = Temp.create () in
    let label_true = Label.label (Some "terop_true") in
    let label_false = Label.label (Some "terop_false") in
    let true_stms = T.Label label_true :: true_stms in
    let false_stms = T.Label label_false :: false_stms in
    let label_ter_end = Label.label (Some "terop_end") in
    let lhs, op, rhs = gen_cond cond_exp in
    let seq =
      cond_stms
      @ [ T.CJump { lhs; op; rhs; target_true = label_true; target_false = label_false } ]
      @ true_stms
      @ [ T.Move { dest = temp; src = true_exp }; T.Jump label_ter_end ]
      @ false_stms
      @ [ T.Move { dest = temp; src = false_exp }; T.Label label_ter_end ]
    in
    seq, T.Temp temp
  | A.Fcall fcall ->
    (* First calculate arguments with potential side effect, then call fcall. *)
    let res =
      List.fold_left fcall.args ~init:[] ~f:(fun acc arg ->
          let arg_stms, arg_exp = trans_mexp arg env in
          (arg_stms, arg_exp) :: acc)
      |> List.rev
    in
    let args_stms =
      List.map res ~f:(fun x ->
          let stms, _ = x in
          stms)
      |> List.concat
    in
    let args_exps =
      List.map res ~f:(fun x ->
          let _, exp = x in
          exp)
    in
    let dest = Temp.create () in
    let call = T.Fcall { dest; args = args_exps; func_name = fcall.func_name } in
    let call_stms = args_stms @ [ call ] in
    call_stms, T.Temp dest

and trans_mexp mexp env = trans_exp (Mark.data mexp) env

and[@warning "-8"] trans_exp_bin (A.Binop binop) env : T.stm list * T.exp =
  let lhs_stm, lhs_exp = trans_mexp binop.lhs env in
  let rhs_stm, rhs_exp = trans_mexp binop.rhs env in
  match trans_binop binop.op with
  | `Pure op -> lhs_stm @ rhs_stm, T.Binop { op; lhs = lhs_exp; rhs = rhs_exp }
  | `Impure op ->
    let dest = Temp.create () in
    ( lhs_stm @ rhs_stm @ [ T.Effect { dest; lhs = lhs_exp; op; rhs = rhs_exp } ]
    , T.Temp dest )
  | `Compare op -> lhs_stm @ rhs_stm, T.Binop { op; lhs = lhs_exp; rhs = rhs_exp }
;;

(* env keep trakcs from variable name to temporary. Two things keep in mind
 * 1) variable name can be the same in different scope (scope has no intersection).
 * So env will update in different context. 
 * 2) env is only a map from variable name to temporary, it doesn't care the 
 * content of temporary. So we only add this linkage in declaration. *)
let rec trans_stm_rev (ast : A.mstm) (acc : T.stm list) (env : Temp.t S.t)
    : T.stm list * Temp.t S.t
  =
  match Mark.data ast with
  | A.Assign asn_ast ->
    let dest = S.find_exn env asn_ast.name in
    let v_stms, v_exp = trans_mexp asn_ast.value env in
    [ T.Move { dest; src = v_exp } ] @ List.rev v_stms @ acc, env
  | A.If if_ast ->
    (* 
     *  CJump cond label_true, label_false
     *  label_false
     *  false_stm
     *  Jump label_conv
     *  label_true
     *  true_stm
     *  label_conv
     *  rest code blah blah
     *)
    let cond_stms, cond_exp = trans_mexp if_ast.cond env in
    let label_false = Label.label (Some "if_false") in
    let label_true = Label.label (Some "if_true") in
    let label_conv = Label.label (Some "if_conv") in
    let false_stm, _ = trans_stm_rev if_ast.false_stm [] env in
    let true_stm, _ = trans_stm_rev if_ast.true_stm [] env in
    let lhs, op, rhs = gen_cond cond_exp in
    ( (T.Label label_conv :: true_stm)
      @ [ T.Label label_true; T.Jump label_conv ]
      @ false_stm
      @ [ T.Label label_false
        ; T.CJump { lhs; op; rhs; target_true = label_true; target_false = label_false }
        ]
      @ List.rev cond_stms
      @ acc
    , env )
  | A.While while_ast ->
    (* 
     * Jump label_loop_stop
     * label_loop_start
     * body
     * label_loop_stop
     * cond_side_effect(optional)
     * CJump cond label_loop_start
     * label_loop_dummy
     * rest blah blah *)
    let cond_stms, cond_exp = trans_mexp while_ast.cond env in
    let body, _ = trans_stm_rev while_ast.body [] env in
    let label_loop_start = Label.label (Some "loop_start") in
    let label_loop_stop = Label.label (Some "loop_stop") in
    let label_loop_dummy = Label.label (Some "loop_dummy") in
    let lhs, op, rhs = gen_cond cond_exp in
    ( [ T.Label label_loop_dummy
      ; T.CJump
          { lhs
          ; op
          ; rhs
          ; target_true = label_loop_start
          ; target_false = label_loop_dummy
          }
      ]
      @ List.rev cond_stms
      @ [ T.Label label_loop_stop ]
      @ body
      @ [ T.Label label_loop_start ]
      @ [ T.Jump label_loop_stop ]
      @ acc
    , env )
  | A.Return ret_ast ->
    (match ret_ast with
    | None -> T.Return None :: acc, env
    | Some ret_ast ->
      let ret_stms, ret_exp = trans_mexp ret_ast env in
      let ret = T.Return (Some ret_exp) in
      (ret :: List.rev ret_stms) @ acc, env)
  | A.Nop -> acc, env
  | A.Seq seq_ast ->
    let head, _ = trans_stm_rev seq_ast.head [] env in
    let tail, _ = trans_stm_rev seq_ast.tail [] env in
    tail @ head @ acc, env
  | A.Declare decl_ast ->
    let temp = Temp.create () in
    let env' = S.add_exn env ~key:decl_ast.name ~data:temp in
    let tail, _ = trans_stm_rev decl_ast.tail [] env' in
    tail @ acc, env'
  | A.Sexp sexp_ast ->
    let sexp_stms, _ = trans_mexp sexp_ast env in
    List.rev sexp_stms @ acc, env
  | A.Assert asrt ->
    let asrt_stms, asrt_exp = trans_mexp asrt env in
    let ret = T.Assert asrt_exp in
    (ret :: List.rev asrt_stms) @ acc, env
;;

let trans_body (program : A.mstm) : T.stm list =
  let env = S.empty in
  let blk_rev, _ = trans_stm_rev program [] env in
  let blk = List.rev blk_rev in
  Tree.Label (Util.Label.label (Some "main")) :: blk
;;

let trans_fdefn func_name (pars : A.param list) blk : T.fdefn =
  let par_list = List.map pars ~f:(fun par -> par.i) in
  let env = S.empty in
  let blk_rev, env = trans_stm_rev blk [] env in
  let blk = List.rev blk_rev in
  let temps = List.map par_list ~f:(fun par -> S.find_exn env par) in
  { func_name; temps; body = blk }
;;

let rec trans_prog (program : A.program) (acc : T.program) : T.program =
  match program with
  | [] -> List.rev acc
  | h :: t ->
    (match h with
    | A.Fdefn fdefn ->
      let fdefn_tree = trans_fdefn fdefn.func_name fdefn.pars fdefn.blk in
      trans_prog t (fdefn_tree :: acc)
    | A.Typedef _ | A.Fdecl _ -> trans_prog t acc)
;;

let translate (program : A.program) : T.program = trans_prog program []
