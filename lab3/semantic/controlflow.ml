(* 
 * Controlflow analysis
 *
 * Control flow check is part of semantic analysis.
 * It will check
 * 1) Whether each AST element has return, except function
 * with void return type.
 * 2) Whether a variable is used before initialization.
 * 
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
module A = Front.Ast
module S = Util.Symbol.Map
module Symbol = Util.Symbol
module Set = Util.Symbol.Set
module Mark = Util.Mark
module TC = Typechecker

type param = A.param

(* env records defined(initialized) variables and declared variables in a function.
 * defined variables are subset of declared variables.
 * ret_sig is the expected return type of this function. *)
type env =
  { var_def : Set.t
  ; var_decl : Set.t
  }

let tc_errors : Util.Error_msg.t = Util.Error_msg.create ()

let error ~msg src_span =
  Util.Error_msg.error tc_errors src_span ~msg;
  raise Util.Error_msg.Error
;;

(* Check whether AST node returns by recursively traverse.
 * This is to make sure each path from the beginning of the
 * program will terminate with an return. 
 *
 * Don't worry about the return type and required return type
 * mismatch, this is checked in typechecker. Here, we only
 * make sure that each branch has returned if required return
 * type is not void.
 *
 * Notice that While is treated as never return because we cannot
 * check every case, like how many times it will run in real time.
 * So we treat it conservatively as never return *)
let rec _cf_ret_stm (ast : A.mstm) : bool =
  match Mark.data ast with
  | Assign _ -> false
  | If if_ast -> _cf_ret_stm if_ast.true_stm && _cf_ret_stm if_ast.false_stm
  | While _ -> false
  | Return _ -> true
  | Nop -> false
  | Seq seq_ast -> _cf_ret_stm seq_ast.head || _cf_ret_stm seq_ast.tail
  | Declare decl_ast -> _cf_ret_stm decl_ast.tail
  | Sexp _ | Assert _ -> false
;;

let rec cf_ret (ast : A.program) : unit =
  match ast with
  | [] -> ()
  | h :: t ->
    (match h with
    | Fdefn fdefn ->
      (match fdefn.ret_type with
      | Void -> ()
      | _ ->
        if _cf_ret_stm fdefn.blk then () else error ~msg:"Some branches not return" None)
    | Typedef _ | Fdecl _ ->
      ();
      cf_ret t)
;;

(* Check whether var is used in exp. Return true if used, false otherwise. *)
let rec use (exp : A.mexp) (var : Symbol.t) : bool =
  match Mark.data exp with
  | Var var' -> phys_equal var' var
  | Const_int _ -> false
  | True -> false
  | False -> false
  | Binop binop -> use binop.lhs var || use binop.rhs var
  | Terop terop -> use terop.cond var || use terop.true_exp var || use terop.false_exp var
  | Fcall fcall -> List.fold fcall.args ~init:false ~f:(fun acc arg -> acc || use arg var)
;;

(* Check whether variable var is live in statement stm
 * Notice that liveness analysis does not require env.
 * We only need to check whether var is used on RHS of the expression *)
let rec live (stm : A.mstm) (var : Symbol.t) : bool =
  match Mark.data stm with
  | Assign asn_ast -> use asn_ast.value var
  | If if_ast ->
    use if_ast.cond var || live if_ast.true_stm var || live if_ast.false_stm var
  | While while_ast -> use while_ast.cond var || live while_ast.body var
  | Return ret_ast ->
    (match ret_ast with
    | None -> false
    | Some s -> use s var)
  | Nop -> false
  | Seq seq_ast ->
    live seq_ast.head var || (live seq_ast.tail var && not (define seq_ast.head var))
  | Declare decl_ast ->
    if phys_equal var decl_ast.name then false else live decl_ast.tail var
  | Sexp sexp_ast -> use sexp_ast var
  | Assert ast -> use ast var

(* Check whether stm defines var *)
and define (stm : A.mstm) (var : Symbol.t) : bool =
  match Mark.data stm with
  | Assign asn_ast -> if phys_equal asn_ast.name var then true else false
  | If if_ast -> define if_ast.true_stm var && define if_ast.false_stm var
  | While _ -> false
  | Return _ -> true
  | Seq seq_ast -> define seq_ast.head var || define seq_ast.tail var
  | Declare decl_ast ->
    if phys_equal decl_ast.name var then false else define decl_ast.tail var
  | Sexp _ | Assert _ | Nop -> false
;;

(* This is an expression level check. It is called by
 * cf_stm and check whether variable in exp is used
 * before any declaration(initialization) *)
let rec cf_exp (exp : A.mexp) (env : env) : unit =
  let loc = Mark.src_span exp in
  match Mark.data exp with
  | Var var ->
    if Set.mem env.var_def var
    then ()
    else error ~msg:(sprintf "var %s is used before decl" (Symbol.name var)) loc
  | Const_int _ -> ()
  | True -> ()
  | False -> ()
  | Binop binop ->
    cf_exp binop.lhs env;
    cf_exp binop.rhs env
  | Terop terop ->
    cf_exp terop.cond env;
    cf_exp terop.true_exp env;
    cf_exp terop.false_exp env
  | Fcall fcall -> List.iter fcall.args ~f:(fun arg -> cf_exp arg env)
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
let rec cf_stm (ast : A.mstm) (env : env) : env =
  let loc = Mark.src_span ast in
  match Mark.data ast with
  | Assign asn_ast ->
    cf_exp asn_ast.value env;
    { env with var_def = Set.add env.var_def asn_ast.name }
  | If if_ast ->
    cf_exp if_ast.cond env;
    let env1 = cf_stm if_ast.true_stm env in
    let env2 = cf_stm if_ast.false_stm env in
    { env with var_def = Set.inter env1.var_def env2.var_def }
  | While while_ast ->
    ignore (cf_stm while_ast.body env : env);
    env
  | Return _ -> { env with var_def = env.var_decl }
  | Nop -> env
  | Seq seq_ast ->
    let env' = cf_stm seq_ast.head env in
    cf_stm seq_ast.tail env'
  | Declare decl_ast ->
    if live decl_ast.tail decl_ast.name
    then
      error ~msg:(sprintf "var %s is live in decl scope" (Symbol.name decl_ast.name)) loc
    else (
      let env' = { env with var_decl = Set.add env.var_decl decl_ast.name } in
      let env_inside = cf_stm decl_ast.tail env' in
      (* We keep track of the declare variable as the same as before because
       * declaration inside inner scope shouldn't reflect to outside scope.
       * As for def, we intersect env.var_def and env_inside.var_def because 
       * env_inside.var_def may contain some variable declared in inner scope *)
      { var_decl = env.var_decl
      ; var_def = Set.diff env_inside.var_def (Set.of_list [ decl_ast.name ])
      })
  | Sexp sexp ->
    cf_exp sexp env;
    env
  | Assert aexp ->
    cf_exp aexp env;
    env
;;

(* Don't worry about parameter name conflict, this is checked in typechecker. *)
let init_func_pars (pars : param list) (env : env) : env =
  List.fold_left pars ~init:env ~f:(fun env_acc par ->
      let var = par.i in
      { var_def = Set.add env_acc.var_def var; var_decl = Set.add env_acc.var_decl var })
;;

let cf_fdefn pars blk env =
  let env = init_func_pars pars env in
  ignore (cf_stm blk env : env)
;;

let rec cf_init (ast : A.program) =
  match ast with
  | [] -> ()
  | h :: t ->
    (match h with
    | Fdefn fdefn ->
      let env = { var_decl = Set.empty; var_def = Set.empty } in
      cf_fdefn fdefn.pars fdefn.blk env
    | Fdecl _ | Typedef _ ->
      ();
      cf_init t)
;;
