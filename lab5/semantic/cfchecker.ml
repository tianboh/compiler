(* 
 * Controlflow analysis
 *
 * Control flow check is part of static semantic analysis.
 * 1) Each AST branch has return, except function with void return.
 * 2) Variable is initialized before use. (exp RHS)
 * 
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core
module AST = Front.Ast
module Symbol = Util.Symbol
module Set = Util.Symbol.Set
module Mark = Util.Mark
module TC = Typechecker

type param = AST.param

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
let rec _cf_ret_stm (ast : AST.mstm) : bool * AST.mstm =
  match Mark.data ast with
  | If if_ast ->
    let true_ret, true_stm = _cf_ret_stm if_ast.true_stm in
    let false_ret, false_stm = _cf_ret_stm if_ast.false_stm in
    true_ret && false_ret, Mark.naked (AST.If { if_ast with true_stm; false_stm })
  | Seq seq_ast ->
    let head_ret, head = _cf_ret_stm seq_ast.head in
    (* printf "seq ret:%b, head{%s}\n%!" head_ret (AST.Print.pp_mstm head); *)
    if head_ret
    then (* printf "seq return\n%!"; *)
      true, head
    else (
      let tail_ret, tail = _cf_ret_stm seq_ast.tail in
      (* printf "seq tail{%s}\n%!" (AST.Print.pp_mstm tail); *)
      tail_ret, Mark.naked (AST.Seq { head; tail }))
  | Declare decl_ast ->
    let decl_ret, tail = _cf_ret_stm decl_ast.tail in
    decl_ret, Mark.naked (AST.Declare { decl_ast with tail })
  | While while_ast ->
    let _, body = _cf_ret_stm while_ast.body in
    false, Mark.naked (AST.While { while_ast with body })
  | Return _ -> true, ast
  | Assign _ | Sexp _ | Assert _ | Nop -> false, ast
;;

(* Check if each branch has return.
 * Remove statements after return. *)
let rec cf_ret (ast : AST.program) (acc : AST.program) : AST.program =
  match ast with
  | [] -> List.rev acc
  | h :: t ->
    let gdecl =
      match h with
      | Fdefn fdefn ->
        (match fdefn.ret_type with
        | `Void -> h
        | _ ->
          let has_ret, mstm = _cf_ret_stm fdefn.blk in
          if not has_ret
          then error ~msg:"Some branches not return" None
          else Fdefn { fdefn with blk = mstm })
      | Typedef _ | Fdecl _ | Sdecl _ | Sdefn _ -> h
    in
    cf_ret t (gdecl :: acc)
;;

(* Check whether var is used in exp. Return true if used, false otherwise. *)
let rec use (exp : AST.mexp) (var : Symbol.t) : bool =
  match Mark.data exp with
  | Var var' -> phys_equal var' var
  | Binop binop -> use binop.lhs var || use binop.rhs var
  | Terop terop -> use terop.cond var || use terop.true_exp var || use terop.false_exp var
  | Fcall fcall -> List.fold fcall.args ~init:false ~f:(fun acc arg -> acc || use arg var)
  | EDot dot -> use dot.struct_obj var
  | EDeref deref -> use deref.ptr var
  | ENth nth -> use nth.arr var
  | Alloc_arr alloc_arr -> use alloc_arr.e var
  | Const_int _ | True | False | NULL | Alloc _ -> false
;;

(* Check whether variable var is live in statement stm
 * Notice that liveness analysis does not require env.
 * We only need to check whether var is used on RHS of the expression *)
let rec live (stm : AST.mstm) (var : Symbol.t) : bool =
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
    if phys_equal var decl_ast.name
    then false
    else (
      let c1 = live decl_ast.tail var in
      let c2 =
        match decl_ast.value with
        | None -> false
        | Some v -> use v var
      in
      c1 || c2)
  | Sexp sexp_ast -> use sexp_ast var
  | Assert ast -> use ast var

(* Check whether stm defines var *)
and define (stm : AST.mstm) (var : Symbol.t) : bool =
  match Mark.data stm with
  | Assign asn_ast ->
    (match Mark.data asn_ast.name with
    | Ident lv -> if phys_equal lv var then true else false
    | LVDot _ | LVDeref _ | LVNth _ -> false)
  | If if_ast -> define if_ast.true_stm var && define if_ast.false_stm var
  | Seq seq_ast -> define seq_ast.head var || define seq_ast.tail var
  | Declare decl_ast ->
    if phys_equal decl_ast.name var then false else define decl_ast.tail var
  | Return _ -> true
  | While _ | Sexp _ | Assert _ | Nop -> false
;;

(* This is an expression level check. It is called by
 * cf_stm and check whether variable in exp is used
 * before any declaration(initialization) *)
let rec cf_exp (exp : AST.mexp) (env : env) : unit =
  let loc = Mark.src_span exp in
  match Mark.data exp with
  | Var var ->
    if not (Set.mem env.var_def var)
    then error ~msg:(sprintf "var %s is used before decl" (Symbol.name var)) loc
  | Binop binop ->
    cf_exp binop.lhs env;
    cf_exp binop.rhs env
  | Terop terop ->
    cf_exp terop.cond env;
    cf_exp terop.true_exp env;
    cf_exp terop.false_exp env
  | Fcall fcall -> List.iter fcall.args ~f:(fun arg -> cf_exp arg env)
  | EDot dot -> cf_exp dot.struct_obj env
  | ENth nth -> cf_exp nth.arr env
  | EDeref deref -> cf_exp deref.ptr env
  | Alloc_arr alloc_arr -> cf_exp alloc_arr.e env
  | Const_int _ | True | False | NULL | Alloc _ -> ()
;;

(* Lvalue should in correct state
 * - declare before define
 * - define before use
 * dot, array access, deref only check identifier.
 *)
let rec cf_lvalue
    (lvalue : AST.mlvalue)
    (env : env)
    (asnop : AST.asnop)
    (need_defn : bool)
    : unit
  =
  let loc = Mark.src_span lvalue in
  match Mark.data lvalue with
  | Ident var ->
    (match asnop with
    | `Asn ->
      if not (Set.mem env.var_decl var)
      then error ~msg:(sprintf "var %s is defined before decl" (Symbol.name var)) loc;
      if need_defn && not (Set.mem env.var_def var)
      then error ~msg:(sprintf "var %s should be defined" (Symbol.name var)) loc
    | _ ->
      if not (Set.mem env.var_def var)
      then error ~msg:(sprintf "var %s is used before define" (Symbol.name var)) loc)
  | LVDot dot -> cf_lvalue dot.struct_obj env asnop true
  | LVNth nth -> cf_lvalue nth.arr env asnop true
  | LVDeref deref -> cf_lvalue deref.ptr env asnop true
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
let rec cf_stm (ast : AST.mstm) (env : env) : env =
  let loc = Mark.src_span ast in
  match Mark.data ast with
  | Assign asn_ast ->
    cf_exp asn_ast.value env;
    cf_lvalue asn_ast.name env asn_ast.op false;
    (match Mark.data asn_ast.name with
    | Ident var -> { env with var_def = Set.add env.var_def var }
    | LVDot _ | LVNth _ | LVDeref _ -> env)
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
    let var = decl_ast.name in
    let env' =
      match decl_ast.value with
      | None ->
        if live decl_ast.tail var
        then error ~msg:(sprintf "var %s is live in decl" (Symbol.name var)) loc;
        { env with var_decl = Set.add env.var_decl var }
      | Some v ->
        cf_exp v env;
        { var_decl = Set.add env.var_decl var; var_def = Set.add env.var_def var }
    in
    let env_inside = cf_stm decl_ast.tail env' in
    (* We keep track of the declare variable as the same as before because
     * declaration inside inner scope shouldn't reflect to outside scope.
     * As for def, we intersect env.var_def and env_inside.var_def because 
     * env_inside.var_def may contain some variable declared in inner scope *)
    { var_decl = env.var_decl
    ; var_def = Set.diff env_inside.var_def (Set.of_list [ var ])
    }
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

let rec cf_init (ast : AST.program) =
  match ast with
  | [] -> ()
  | h :: t ->
    (match h with
    | Fdefn fdefn ->
      let env = { var_decl = Set.empty; var_def = Set.empty } in
      cf_fdefn fdefn.pars fdefn.blk env;
      cf_init t
    | Fdecl _ | Typedef _ | Sdecl _ | Sdefn _ -> cf_init t)
;;
