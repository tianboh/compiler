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
module A = Parser.Ast
module S = Util.Symbol.Map
module Symbol = Util.Symbol

type init_status =
  | Decl
  | Init

type env =
  { vars : init_status S.t
  ; returns : bool
  }

let tc_errors : Util.Error_msg.t = Util.Error_msg.create ()

let rec tc_exp (ast : A.mexp) (vars : init_status S.t) : unit =
  let error ~msg =
    Util.Error_msg.error tc_errors (Util.Mark.src_span ast) ~msg;
    raise Util.Error_msg.Error
  in
  match Util.Mark.data ast with
  | A.Var id ->
    (match S.find vars id with
    | None -> error ~msg:(sprintf "Not declared before use: `%s`" (Symbol.name id))
    | Some Decl ->
      error ~msg:(sprintf "Not initialized before use: `%s`" (Symbol.name id))
    | Some Init -> ())
  | A.Const_int _ -> ()
  | A.Const_bool _ -> ()
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
let rec tc_stms (ast : A.mstm list) (env : env) : env =
  match ast with
  | [] -> env
  | stm :: stms ->
    let error ~msg =
      Util.Error_msg.error tc_errors (Util.Mark.src_span stm) ~msg;
      raise Util.Error_msg.Error
    in
    (match Util.Mark.data stm with
    | A.Declare (A.New_var id) ->
      (match S.find env.vars id.name with
      | Some _ -> error ~msg:(sprintf "Already declared: `%s`" (Symbol.name id.name))
      | None -> tc_stms stms { env with vars = S.set env.vars ~key:id.name ~data:Decl })
    | A.Declare (A.Init {t=t; name=name; value=value}) ->
      (* Since we're creating new statements, we just maintain the
       * source location of the original statement `stm`. This is just
       * for debugging and pretty error messages; we could just use
       * Mark.naked to create a marked expression with no src location
       * information.
       *)
      let remark exp = Util.Mark.map stm ~f:(fun _ -> exp) in
      (* The following translation is sound:
       *
       * int x = expr;  ===>   int x;
       *                       x = expr;
       *
       * This is because the expression can't legally contain the identifier x.
       * NB: This property will no longer hold when function calls are introduced.
       *)
      let stms' =
        remark (A.Declare (A.New_var {t; name})) :: remark (A.Assign {name = name; value = value}) :: stms
      in
      tc_stms stms' env
    | A.Assign {name = id; value = e} ->
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
  Util.Error_msg.error tc_errors None ~msg:"main does not return";
    raise Util.Error_msg.Error)
;;
