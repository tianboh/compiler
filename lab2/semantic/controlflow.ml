(* 
 * Controlflow analysis
 *
 * Control flow check is part of semantic analysis.
 * It will check
 * 1) Whether each AST element has return
 * 2) Whether a variable is used before initialization.
 * 
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
module A = Parser.Ast
module S = Util.Symbol.Map
module Symbol = Util.Symbol
module Mark = Util.Mark

let tc_errors : Util.Error_msg.t = Util.Error_msg.create ()

let error ~msg src_span =
  Util.Error_msg.error tc_errors src_span ~msg;
  raise Util.Error_msg.Error
;;

(* Check whether AST node returns by recursively traverse.
 * This is to make sure each path from the beginning of the
 * program will terminate with an return. 
 *
 * Notice that While is treated as never return because we cannot
 * check every case, like how many times it will run in real time.
 * So we treat it conservatively as never return *)
let rec _cf_ret (ast : A.program) : bool =
  match Mark.data ast with
  | A.Assign _ -> false
  | A.If if_ast -> _cf_ret if_ast.true_stm && _cf_ret if_ast.false_stm
  | A.While _ -> false
  | A.Return _ -> true
  | A.Nop -> false
  | A.Seq seq_ast -> _cf_ret seq_ast.head || _cf_ret seq_ast.tail
  | A.Declare decl_ast -> _cf_ret decl_ast.tail
  | Sexp _ -> false
;;

let cf_ret (ast : A.program) : unit =
  if _cf_ret ast then () else error ~msg:(sprintf "Some branch does not return") None
;;

(* env records defined(initialized) variables and declared variables.
 * defined variables are subset of declared variables. *)
type env =
  { var_def : Symbol.Set.t
  ; var_decl : Symbol.Set.t
  }

(* Check whether var is used in exp. Return true if used, false otherwise. *)
let rec use (exp : A.mexp) (var : Symbol.t) : bool =
  match Mark.data exp with
  | A.Var var' -> phys_equal var' var
  | A.Const_int _ -> false
  | A.True -> false
  | A.False -> false
  | A.Binop binop -> use binop.lhs var || use binop.rhs var
  | A.Terop terop ->
    use terop.cond var || use terop.true_exp var || use terop.false_exp var
;;

(* Check whether variable var is live in statement stm
 * Notice that liveness analysis does not require env.
 * We only need to check whether var is used on RHS of the expression *)
let rec live (stm : A.program) (var : Symbol.t) : bool =
  match Mark.data stm with
  | A.Assign asn_ast -> use asn_ast.value var
  | A.If if_ast ->
    use if_ast.cond var || live if_ast.true_stm var || live if_ast.false_stm var
  | A.While while_ast -> use while_ast.cond var || live while_ast.body var
  | A.Return ret_ast -> use ret_ast var
  | A.Nop -> false
  | A.Seq seq_ast ->
    live seq_ast.head var || (live seq_ast.tail var && not (define seq_ast.head var))
  | A.Declare decl_ast ->
    if phys_equal var decl_ast.name then false else live decl_ast.tail var
  | Sexp sexp_ast -> use sexp_ast var

(* Check whether stm defines var *)
and define (stm : A.program) (var : Symbol.t) : bool =
  match Mark.data stm with
  | A.Assign asn_ast -> if phys_equal asn_ast.name var then true else false
  | A.If if_ast -> define if_ast.true_stm var && define if_ast.false_stm var
  | A.While _ -> false
  | A.Return _ -> true
  | A.Nop -> false
  | A.Seq seq_ast -> define seq_ast.head var || define seq_ast.tail var
  | A.Declare decl_ast ->
    if phys_equal decl_ast.name var then false else define decl_ast.tail var
  | Sexp _ -> false
;;

(* This is an expression level check. It is called by
 * _cf_init and check whether variable in exp is used
 * before any declaration(initialization) *)
let rec cf_init_exp (exp : A.mexp) (env : env) : unit =
  let loc = Mark.src_span exp in
  match Mark.data exp with
  | A.Var var ->
    if Symbol.Set.mem env.var_def var
    then ()
    else error ~msg:(sprintf "var %s is used before decl" (Symbol.name var)) loc
  | A.Const_int _ -> ()
  | A.True -> ()
  | A.False -> ()
  | A.Binop binop ->
    let () = cf_init_exp binop.lhs env in
    cf_init_exp binop.rhs env
  | A.Terop terop ->
    let () = cf_init_exp terop.cond env in
    let () = cf_init_exp terop.true_exp env in
    cf_init_exp terop.false_exp env
;;

(* On each control flow path through the program connecting 
 * the use of a variable to its declaration, it must be defined 
 * by an assignment (or initialized) before it is used. This ensures
 * that there will be no references to uninitialized variables. 
 * 
 * Guaranteed by typecheker module:
 * Variables in LHS and RHS exp are declared, and no one
 * is declared multiple times.
 *
 * The check procedure is as follows. Suppose it is an expression.
 * 1) Check the use of variable in RHS. If it uses a variable that is
 * not defined, report an error.
 * 2) Update LHS variable state to env.
 *
 * return: env, the updated environmant after executing current AST stm.
 *)
let rec _cf_init (ast : A.program) (env : env) : env =
  let loc = Mark.src_span ast in
  match Mark.data ast with
  | A.Assign asn_ast ->
    let () = cf_init_exp asn_ast.value env in
    { env with var_def = Symbol.Set.add env.var_def asn_ast.name }
  | A.If if_ast ->
    let () = cf_init_exp if_ast.cond env in
    let env1 = _cf_init if_ast.true_stm env in
    let env2 = _cf_init if_ast.false_stm env in
    { env with var_def = Symbol.Set.inter env1.var_def env2.var_def }
  | A.While while_ast ->
    let _ = (_cf_init while_ast.body env : env) in
    env
  | A.Return _ -> { env with var_def = env.var_decl }
  | A.Nop -> env
  | A.Seq seq_ast ->
    let env' = _cf_init seq_ast.head env in
    _cf_init seq_ast.tail env'
  | A.Declare decl_ast ->
    if live decl_ast.tail decl_ast.name
    then
      error ~msg:(sprintf "var %s is live in decl scope" (Symbol.name decl_ast.name)) loc
    else (
      let env' = { env with var_decl = Symbol.Set.add env.var_decl decl_ast.name } in
      let env_inside = _cf_init decl_ast.tail env' in
      (* We keep track of the declare variable as the same as before because
       * declaration inside inner scope shouldn't reflect to outside scope.
       * As for def, we intersect env.var_def and env_inside.var_def because 
       * env_inside.var_def may contain some variable declared in inner scope *)
      { var_decl = env.var_decl
      ; var_def = Symbol.Set.inter env_inside.var_def env.var_def
      })
  | Sexp sexp ->
    let () = cf_init_exp sexp env in
    env
;;

let cf_init (ast : A.program) : unit =
  let env = { var_decl = Symbol.Set.empty; var_def = Symbol.Set.empty } in
  let _ = (_cf_init ast env : env) in
  ()
;;
