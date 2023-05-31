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
module AST = Front.Ast
module Tree = Inst
module S = Util.Symbol.Map
module Symbol = Util.Symbol
module Label = Util.Label
module Mark = Util.Mark
module Temp = Var.Temp
module TC = Semantic.Typechecker

let trans_scope = function
  | TC.Internal -> Tree.Internal
  | TC.External -> Tree.External
;;

(* `Pure is expression that not lead to side-effect
 * `Impure is expression that may lead to side-effect, 
 * like rasing div-zero or other exception
 * `Compare is return boolean value. *)
let trans_binop = function
  | AST.Plus -> `Pure Tree.Plus
  | AST.Minus -> `Pure Tree.Minus
  | AST.Times -> `Pure Tree.Times
  | AST.And -> `Pure Tree.And
  | AST.Or -> `Pure Tree.Or
  | AST.Hat -> `Pure Tree.Xor
  | AST.Right_shift -> `Impure Tree.Right_shift
  | AST.Left_shift -> `Impure Tree.Left_shift
  | AST.Divided_by -> `Impure Tree.Divided_by
  | AST.Modulo -> `Impure Tree.Modulo
  | AST.Equal_eq -> `Compare Tree.Equal_eq
  | AST.Greater -> `Compare Tree.Greater
  | AST.Greater_eq -> `Compare Tree.Greater_eq
  | AST.Less -> `Compare Tree.Less
  | AST.Less_eq -> `Compare Tree.Less_eq
  | AST.Not_eq -> `Compare Tree.Not_eq
;;

let gen_cond (exp : Tree.exp) : Tree.exp * Tree.binop * Tree.exp =
  match exp with
  | Tree.Const i -> Tree.Const i, Tree.Equal_eq, Tree.Const Int32.one
  | Tree.Temp t -> Tree.Temp t, Tree.Equal_eq, Tree.Const Int32.one
  | Tree.Binop binop -> binop.lhs, binop.op, binop.rhs
;;

(* Return statement lists that include effect(can be empty), 
 * and the pure exp without side-effect *)
let rec trans_exp (exp_ast : AST.exp) (var_env : Temp.t S.t) (func_env : TC.func S.t)
    : Tree.stm list * Tree.exp
  =
  match exp_ast with
  (* after type-checking, id must be declared; do not guard lookup *)
  | AST.Var id -> [], Tree.Temp (S.find_exn var_env id)
  | AST.Const_int c -> [], Tree.Const c
  | AST.True -> [], Tree.Const Int32.one
  | AST.False -> [], Tree.Const Int32.zero
  | AST.Binop binop -> trans_exp_bin (AST.Binop binop) var_env func_env
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
  | AST.Terop terop ->
    let cond_stms, cond_exp = trans_mexp terop.cond var_env func_env in
    let true_stms, true_exp = trans_mexp terop.true_exp var_env func_env in
    let false_stms, false_exp = trans_mexp terop.false_exp var_env func_env in
    let temp = Temp.create () in
    let label_true = Label.label (Some "terop_true") in
    let label_false = Label.label (Some "terop_false") in
    let true_stms = Tree.Label label_true :: true_stms in
    let false_stms = Tree.Label label_false :: false_stms in
    let label_ter_end = Label.label (Some "terop_end") in
    let lhs, op, rhs = gen_cond cond_exp in
    let seq =
      cond_stms
      @ [ Tree.CJump
            { lhs; op; rhs; target_true = label_true; target_false = label_false }
        ]
      @ true_stms
      @ [ Tree.Move { dest = temp; src = true_exp }; Tree.Jump label_ter_end ]
      @ false_stms
      @ [ Tree.Move { dest = temp; src = false_exp }; Tree.Label label_ter_end ]
    in
    seq, Tree.Temp temp
  | AST.Fcall fcall ->
    (* First calculate arguments with potential side effect, then call fcall. *)
    let res =
      List.fold_left fcall.args ~init:[] ~f:(fun acc arg ->
          let arg_stms, arg_exp = trans_mexp arg var_env func_env in
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
    let func = S.find_exn func_env fcall.func_name in
    let scope = trans_scope func.scope in
    let call =
      Tree.Fcall { dest; args = args_exps; func_name = fcall.func_name; scope }
    in
    let call_stms = args_stms @ [ call ] in
    call_stms, Tree.Temp dest

and trans_mexp mexp var_env func_env = trans_exp (Mark.data mexp) var_env func_env

and[@warning "-8"] trans_exp_bin (AST.Binop binop) var_env func_env
    : Tree.stm list * Tree.exp
  =
  let lhs_stm, lhs_exp = trans_mexp binop.lhs var_env func_env in
  let rhs_stm, rhs_exp = trans_mexp binop.rhs var_env func_env in
  match trans_binop binop.op with
  | `Pure op -> lhs_stm @ rhs_stm, Tree.Binop { op; lhs = lhs_exp; rhs = rhs_exp }
  | `Impure op ->
    let dest = Temp.create () in
    ( lhs_stm @ rhs_stm @ [ Tree.Effect { dest; lhs = lhs_exp; op; rhs = rhs_exp } ]
    , Tree.Temp dest )
  | `Compare op -> lhs_stm @ rhs_stm, Tree.Binop { op; lhs = lhs_exp; rhs = rhs_exp }
;;

(* var_env keep trakcs from variable name to temporary. Two things keep in mind
 * 1) variable name can be the same in different scope (scope has no intersection).
 * So var_env will update in different context. 
 * 2) var_env is only a map from variable name to temporary, it doesn't care the 
 * content of temporary. So we only add this linkage in declaration. *)
let rec trans_stm_rev
    (ast : AST.mstm)
    (acc : Tree.stm list)
    (var_env : Temp.t S.t)
    (func_env : TC.func S.t)
    : Tree.stm list * Temp.t S.t
  =
  match Mark.data ast with
  | AST.Assign asn_ast ->
    let dest = S.find_exn var_env asn_ast.name in
    let v_stms, v_exp = trans_mexp asn_ast.value var_env func_env in
    [ Tree.Move { dest; src = v_exp } ] @ List.rev v_stms @ acc, var_env
  | AST.If if_ast ->
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
    let cond_stms, cond_exp = trans_mexp if_ast.cond var_env func_env in
    let label_false = Label.label (Some "if_false") in
    let label_true = Label.label (Some "if_true") in
    let label_conv = Label.label (Some "if_conv") in
    let false_stm, _ = trans_stm_rev if_ast.false_stm [] var_env func_env in
    let true_stm, _ = trans_stm_rev if_ast.true_stm [] var_env func_env in
    let lhs, op, rhs = gen_cond cond_exp in
    ( (Tree.Label label_conv :: true_stm)
      @ [ Tree.Label label_true; Tree.Jump label_conv ]
      @ false_stm
      @ [ Tree.Label label_false
        ; Tree.CJump
            { lhs; op; rhs; target_true = label_true; target_false = label_false }
        ]
      @ List.rev cond_stms
      @ acc
    , var_env )
  | AST.While while_ast ->
    (* 
     * Jump label_loop_stop
     * label_loop_start
     * body
     * label_loop_stop
     * cond_side_effect(optional)
     * CJump cond label_loop_start
     * label_loop_dummy
     * rest blah blah *)
    let cond_stms, cond_exp = trans_mexp while_ast.cond var_env func_env in
    let body, _ = trans_stm_rev while_ast.body [] var_env func_env in
    let label_loop_start = Label.label (Some "loop_start") in
    let label_loop_stop = Label.label (Some "loop_stop") in
    let label_loop_dummy = Label.label (Some "loop_dummy") in
    let lhs, op, rhs = gen_cond cond_exp in
    ( [ Tree.Label label_loop_dummy
      ; Tree.CJump
          { lhs
          ; op
          ; rhs
          ; target_true = label_loop_start
          ; target_false = label_loop_dummy
          }
      ]
      @ List.rev cond_stms
      @ [ Tree.Label label_loop_stop ]
      @ body
      @ [ Tree.Label label_loop_start ]
      @ [ Tree.Jump label_loop_stop ]
      @ acc
    , var_env )
  | AST.Return ret_ast ->
    (match ret_ast with
    | None -> Tree.Return None :: acc, var_env
    | Some ret_ast ->
      let ret_stms, ret_exp = trans_mexp ret_ast var_env func_env in
      let ret = Tree.Return (Some ret_exp) in
      (ret :: List.rev ret_stms) @ acc, var_env)
  | AST.Nop -> acc, var_env
  | AST.Seq seq_ast ->
    let head, _ = trans_stm_rev seq_ast.head [] var_env func_env in
    let tail, _ = trans_stm_rev seq_ast.tail [] var_env func_env in
    tail @ head @ acc, var_env
  | AST.Declare decl_ast ->
    let temp = Temp.create () in
    let var_env' = S.add_exn var_env ~key:decl_ast.name ~data:temp in
    let tail, _ = trans_stm_rev decl_ast.tail [] var_env' func_env in
    tail @ acc, var_env'
  | AST.Sexp sexp_ast ->
    let sexp_stms, _ = trans_mexp sexp_ast var_env func_env in
    List.rev sexp_stms @ acc, var_env
  | AST.Assert asrt ->
    let asrt_stms, asrt_exp = trans_mexp asrt var_env func_env in
    let ret = Tree.Assert asrt_exp in
    (ret :: List.rev asrt_stms) @ acc, var_env
;;

let trans_fdefn func_name (pars : AST.param list) blk (func_env : TC.func S.t)
    : Tree.fdefn
  =
  let par_list = List.map pars ~f:(fun par -> par.i) in
  let var_env =
    List.fold par_list ~init:S.empty ~f:(fun acc par ->
        let temp = Temp.create () in
        S.add_exn acc ~key:par ~data:temp)
  in
  let blk_rev, var_env = trans_stm_rev blk [] var_env func_env in
  let blk = List.rev blk_rev in
  let temps = List.map par_list ~f:(fun par -> S.find_exn var_env par) in
  { func_name; temps; body = blk }
;;

let rec trans_prog (program : AST.program) (acc : Tree.program) (func_env : TC.func S.t)
    : Tree.program
  =
  match program with
  | [] -> List.rev acc
  | h :: t ->
    (match h with
    | AST.Fdefn fdefn ->
      let fdefn_tree = trans_fdefn fdefn.func_name fdefn.pars fdefn.blk func_env in
      trans_prog t (fdefn_tree :: acc) func_env
    | AST.Typedef _ | AST.Fdecl _ -> trans_prog t acc func_env)
;;

let translate (program : AST.program) (func_env : TC.func S.t) : Tree.program =
  trans_prog program [] func_env
;;
