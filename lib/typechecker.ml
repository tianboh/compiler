(* L1 Compiler
 * TypeChecker
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Simple typechecker that checks two properties:
 *  (1) If a variable is initialized, it has previously been declared.
 *  (2) If a variable is used, it has previously been initialized.
 * This is sufficient for now, since only int types are available in L1.
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Now distinguishes between declarations and initialization
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Should be more up-to-date with modern spec.
 * Modified: Matt Bryant <mbryant@andrew.cmu.edu> Fall 2015
 * Handles undefined variables in unreachable code, significant simplifications
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu> Fall 2018
 *   Use records, redo marks.
 *)

open Core
module A = Ast
module S = Symbol.Map

type init_status =
  | Decl
  | Init

type env =
  { vars : init_status S.t
  ; returns : bool
  }

let tc_errors : Error_msg.t = Error_msg.create ()

let rec tc_exp (ast : A.mexp) (vars : init_status S.t) : unit =
  let error ~msg =
    Error_msg.error tc_errors (Mark.src_span ast) ~msg;
    raise Error_msg.Error
  in
  match Mark.data ast with
  | A.Var id ->
    (match S.find vars id with
    | None -> error ~msg:(sprintf "Not declared before use: `%s`" (Symbol.name id))
    | Some Decl ->
      error ~msg:(sprintf "Not initialized before use: `%s`" (Symbol.name id))
    | Some Init -> ())
  | A.Const _ -> ()
  | A.Binop binop ->
    tc_exp binop.lhs vars;
    tc_exp binop.rhs vars
  | A.Unop unop -> tc_exp unop.operand vars
;;

(* tc_stms env ast
 *   env.vars: environment under which to consider the ast, where:
 *     find env.vars id = Some Init if id is declared and initialized
 *     find env.vars id = Some Decl if id is declared but not initialized
 *     find env.vars id = None      if id is not declared
 *
 *   env.returns
 *     whether the previous statements returned.
 *
 *   ast: the sequence of statements to typecheck.
 *)
let rec tc_stms (ast : Ast.mstm list) (env : env) : env =
  match ast with
  | [] -> env
  | stm :: stms ->
    let error ~msg =
      Error_msg.error tc_errors (Mark.src_span stm) ~msg;
      raise Error_msg.Error
    in
    (match Mark.data stm with
    | A.Declare (A.New_var id) ->
      (match S.find env.vars id with
      | Some _ -> error ~msg:(sprintf "Already declared: `%s`" (Symbol.name id))
      | None -> tc_stms stms { env with vars = S.set env.vars ~key:id ~data:Decl })
    | A.Declare (A.Init (id, e)) ->
      (* Since we're creating new statements, we just maintain the
       * source location of the original statement `stm`. This is just
       * for debugging and pretty error messages; we could just use
       * Mark.naked to create a marked expression with no src location
       * information.
       *)
      let remark exp = Mark.map stm ~f:(fun _ -> exp) in
      (* The following translation is sound:
       *
       * int x = expr;  ===>   int x;
       *                       x = expr;
       *
       * This is because the expression can't legally contain the identifier x.
       * NB: This property will no longer hold when function calls are introduced.
       *)
      let stms' =
        remark (A.Declare (A.New_var id)) :: remark (A.Assign (id, e)) :: stms
      in
      tc_stms stms' env
    | A.Assign (id, e) ->
      tc_exp e env.vars;
      (match S.find env.vars id with
      | None ->
        error ~msg:(sprintf "Not declared before initialization: `%s`" (Symbol.name id))
      (* just got initialized *)
      | Some Decl -> tc_stms stms { env with vars = S.set env.vars ~key:id ~data:Init }
      (* already initialized *)
      | Some Init -> tc_stms stms env)
    | A.Return e ->
      tc_exp e env.vars;
      (* Define all variables declared before return *)
      tc_stms stms { vars = S.map env.vars ~f:(fun _ -> Init); returns = true })
;;

let typecheck prog =
  let env = tc_stms prog { vars = S.empty; returns = false } in
  if not env.returns
  then (
    Error_msg.error tc_errors None ~msg:"main does not return";
    raise Error_msg.Error)
;;
