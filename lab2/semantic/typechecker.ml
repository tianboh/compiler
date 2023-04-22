(* L2 Compiler
 * TypeChecker
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 * Created: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * This type checker is part of the semantic analysis
 * It checkes whether each statement and expression is valid
 * 
 * Check https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab2.pdf
 * Section 4.1 for more details.
 *
 * Statement level check
 * 1) Check the expression of statement is of the correct type. 
 * For example, whether the expression of If.cond is Bool type.
 * 2) Check sub-statement is valid of a statement.
 * For example, whether Seq.head and Seq.tail is valid for Seq.
 * 3) Check variable re-declaration error, and assign without declare error.
 *
 * Expression level check
 * 1) Check whether the operand and operator consistent with each other.
 * 
 * We can summarize above checks to two cases
 * 1) Type check in statement and expression
 * 2) Variable declaration check, including re-decl and non-decl.
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Now distinguishes between declarations and initialization
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Should be more up-to-date with modern spec.
 * Modified: Matt Bryant <mbryant@andrew.cmu.edu> Fall 2015
 * Handles undefined variables in unreachable code, significant simplifications
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu> Fall 2018
 * Use records, redo marks.
 *)

open Core
module A = Parser.Ast
module S = Util.Symbol.Map
module Symbol = Util.Symbol
module Mark = Util.Mark

type state =
  | Decl
  | Init

type dtype =
  | Int
  | Bool

type var =
  { state : state
  ; dtype : dtype
  }

type env =
  { vars : var S.t
  ; returns : bool
  }

let tc_errors : Util.Error_msg.t = Util.Error_msg.create ()

let error ~msg src_span =
  Util.Error_msg.error tc_errors src_span ~msg;
  raise Util.Error_msg.Error
;;

let type_cmp t1 t2 =
  match t1, t2 with
  | Int, Int -> true
  | Int, Bool -> false
  | Bool, Int -> false
  | Bool, Bool -> true
;;

(* tc_exp will check if expression is valid
 * including whether the operand and operator consistent. 
 * It will return the type of expression if pass the check.
 * Otherwise, it will report an error and stop. *)
let rec tc_exp (exp : A.mexp) (env : env) : dtype =
  let loc = Mark.src_span exp in
  match Util.Mark.data exp with
  | A.Var var ->
    (match S.find env.vars var with
    | None -> error ~msg:(sprintf "Identifier not declared: `%s`" (Symbol.name var)) loc
    | Some var -> var.dtype)
  | A.Const_int _ -> Int
  | A.True -> Bool
  | A.False -> Bool
  | A.Binop binop ->
    (match binop.op with
    (* Relation op: < <= > >= *)
    | A.Less | A.Less_eq | A.Greater | A.Greater_eq ->
      (match tc_exp binop.lhs env, tc_exp binop.rhs env with
      | Int, Int -> Bool
      | _, _ -> error ~msg:(sprintf "Relation operand should be integer.") loc)
    (* Polyeq op: ==, != *)
    | A.Equal_eq | A.Not_eq ->
      let t1 = tc_exp binop.lhs env in
      let t2 = tc_exp binop.rhs env in
      if type_cmp t1 t2
      then Bool
      else error ~msg:(sprintf "Polyeq operands type mismatch") loc
    (* Rest are int operation *)
    | _ ->
      let t1 = tc_exp binop.lhs env in
      let t2 = tc_exp binop.rhs env in
      (match t1, t2 with
      | Int, Int -> Int
      | _, _ -> error ~msg:(sprintf "Integer binop operands are not integer") loc))
  | A.Terop terop ->
    let t_cond = tc_exp terop.cond env in
    let t1 = tc_exp terop.true_exp env in
    let t2 = tc_exp terop.false_exp env in
    (match t_cond with
    | Int -> error ~msg:(sprintf "Terop condition should be bool") loc
    | Bool ->
      if type_cmp t1 t2
      then t1
      else error ~msg:(sprintf "Terop true and false exp type should be consistent") loc)
;;

let trans_ast_dtype = function
  | A.Int -> Int
  | A.Bool -> Bool
;;

(* 
 * Check AST statements
 * Type checker will traverse the AST from root recursively.
 * It will report once found an error and then terminate.
 * We only use env to check redefination error.
 * We do not check variable use before initialization in this function.
 * It is done in control flow check.
 * ast: AST transformed from source code
 * env: store the variables state: Init, Decl.
 *)
let rec tc_stms (ast : A.program) (env : env) : env =
  let loc = Mark.src_span ast in
  match Mark.data ast with
  | A.Assign asn_ast -> tc_assign asn_ast.name loc asn_ast.value env
  | A.If if_ast -> tc_if if_ast.cond if_ast.true_stm if_ast.false_stm loc env
  | A.While while_ast -> tc_while while_ast.cond while_ast.body loc env
  | A.Return ret_ast -> tc_return ret_ast env
  | A.Nop -> env
  | A.Seq seq_ast ->
    let env = tc_stms seq_ast.head env in
    tc_stms seq_ast.tail env
  | A.Declare decl_ast -> tc_declare decl_ast.t decl_ast.name decl_ast.tail loc env
  | A.Sexp sexp ->
    let _ = (tc_exp sexp env : dtype) in
    env

(* Check following
 * 1) Whether variable name exist in env
 * 2) If exist, then check whether variable type match exp type
 * 3) If match, update env state *)
and tc_assign name loc exp env : env =
  (* Check if variable is in env before assignment. *)
  match S.find env.vars name with
  | None -> error ~msg:(sprintf "Not declared: `%s`" (Symbol.name name)) loc
  | Some var ->
    let exp_type = tc_exp exp env in
    (* Check if expression type and variable type match *)
    if type_cmp exp_type var.dtype
    then (
      (* Type match, Update variable state to initialized. *)
      let env_vars = S.set env.vars ~key:name ~data:{ var with state = Init } in
      { env with vars = env_vars })
    else
      (* expression and variable type mismatch, error *)
      error ~msg:(sprintf "var type and exp type mismatch") loc

and tc_return mexp env =
  let loc = Mark.src_span mexp in
  let exp_type = tc_exp mexp env in
  match exp_type with
  | Int -> { env with returns = true }
  | Bool -> error ~msg:(sprintf "Return type is bool") loc

and tc_if cond true_stm false_stm loc env =
  let cond_type = tc_exp cond env in
  match cond_type with
  | Int -> error ~msg:(sprintf "If cond type is int") loc
  | Bool ->
    let env = tc_stms true_stm env in
    tc_stms false_stm env

and tc_while cond body loc env =
  let cond_type = tc_exp cond env in
  match cond_type with
  | Int -> error ~msg:(sprintf "While cond type is int") loc
  | Bool -> tc_stms body env

(* Declare check is tricky because we will
 * not override old env. Instead, we will return it
 * once we check the tail. *)
and tc_declare decl_type decl_name tail loc env =
  match S.find env.vars decl_name with
  | Some _ -> error ~msg:(sprintf "Declare a variable multiple time") loc
  | None ->
    let vars' =
      S.add_exn
        env.vars
        ~key:decl_name
        ~data:{ state = Decl; dtype = trans_ast_dtype decl_type }
    in
    let env' = { env with vars = vars' } in
    let env'' = (tc_stms tail env' : env) in
    { env'' with vars = S.remove env''.vars decl_name }
;;

let typecheck prog =
  let env = tc_stms prog { vars = S.empty; returns = false } in
  if not env.returns
  then (
    Util.Error_msg.error tc_errors None ~msg:"main does not return";
    raise Util.Error_msg.Error)
;;
