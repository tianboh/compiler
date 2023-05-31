(* L3 Compiler
 * TypeChecker
 *
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
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
 * 1) operand and operator consistency
 * 
 * Function level check
 * 1) Each function is defined before called
 * 2) Calling exp argument type and defined signature match
 * 3) Parameter conflict with local variables
 * 4) No functions are defined several time
 *
 * We can summarize above checks to two cases
 * 1) Type check in statement and expression
 * 2) Variable declaration check, including re-decl and non-decl.
 *
 * Type alias is already handled in elab, so we don't bother it here.
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Now distinguishes between declarations and definition(initialization)
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Should be more up-to-date with modern spec.
 * Modified: Matt Bryant <mbryant@andrew.cmu.edu> Fall 2015
 * Handles undefined variables in unreachable code, significant simplifications
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu> Fall 2018
 * Use records, redo marks.
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu> May 2023
 *)

open Core
module AST = Front.Ast
module Map = Util.Symbol.Map
module Set = Util.Symbol.Set
module Symbol = Util.Symbol
module Mark = Util.Mark

type state =
  | Decl
  | Defn

type dtype = AST.dtype
type param = AST.param

type scope =
  | Internal
  | External

type var =
  { state : state
  ; dtype : dtype
  }

type func =
  { state : state
  ; pars : param list
  ; ret_type : dtype
  ; scope : scope
  }

type env =
  { vars : var Map.t (* variable decl/def tracker *)
  ; funcs : func Map.t (* function signature *)
  }

(* functions not defined during TC. Check once TC is done. *)
let func_list = ref []
let tc_errors : Util.Error_msg.t = Util.Error_msg.create ()

let error ~msg src_span =
  Util.Error_msg.error tc_errors src_span ~msg;
  raise Util.Error_msg.Error
;;

let type_cmp (t1 : dtype) (t2 : dtype) =
  match t1, t2 with
  | Int, Int -> true
  | Bool, Bool -> true
  | Void, Void -> true
  | _ -> false
;;

(* Check whether element in params1 and params2 has same dtype respectively *)
let tc_signature (params1 : dtype list) (params2 : dtype list) func_name =
  let func_name_s = Symbol.name func_name in
  let param =
    match List.zip params1 params2 with
    | Unequal_lengths ->
      error ~msg:(sprintf "%s redeclared param length mismatch" func_name_s) None
    | Ok res -> res
  in
  List.iter param ~f:(fun t ->
      let d1, d2 = t in
      if not (type_cmp d1 d2)
      then error ~msg:(sprintf "%s redeclared param type mismatch" func_name_s) None)
;;

(* tc_exp will check if an expression is valid
 * including whether the operand and operator consistent. 
 * It will return the type of expression if pass the check.
 * Otherwise, it will report an error and stop. *)
let rec tc_exp (exp : AST.mexp) (env : env) : dtype =
  let loc = Mark.src_span exp in
  match Util.Mark.data exp with
  | AST.Var var ->
    (match Map.find env.vars var with
    | None -> error ~msg:(sprintf "Identifier not declared: `%s`" (Symbol.name var)) loc
    | Some var -> var.dtype)
  | AST.Const_int _ -> Int
  | AST.True -> Bool
  | AST.False -> Bool
  | AST.Binop binop ->
    (match binop.op with
    (* Relation op: < <= > >= *)
    | AST.Less | AST.Less_eq | AST.Greater | AST.Greater_eq ->
      (match tc_exp binop.lhs env, tc_exp binop.rhs env with
      | Int, Int -> Bool
      | _, _ -> error ~msg:"Relation operand should be integer." loc)
    (* Polyeq op: ==, != *)
    | AST.Equal_eq | AST.Not_eq ->
      let t1 = tc_exp binop.lhs env in
      let t2 = tc_exp binop.rhs env in
      if type_cmp t1 t2 && not (type_cmp t1 Void)
      then Bool
      else error ~msg:"Polyeq operands type mismatch" loc
    (* Rest are int operation *)
    | _ ->
      let t1 = tc_exp binop.lhs env in
      let t2 = tc_exp binop.rhs env in
      (match t1, t2 with
      | Int, Int -> Int
      | _, _ -> error ~msg:"Integer binop operands are not integer" loc))
  | AST.Terop terop ->
    let t_cond = tc_exp terop.cond env in
    let t1 = tc_exp terop.true_exp env in
    let t2 = tc_exp terop.false_exp env in
    if type_cmp t1 Void || type_cmp t2 Void then error ~msg:"exp type cannot be void" None;
    (match t_cond with
    | Int | Void -> error ~msg:"Terop condition should be bool" loc
    | Bool ->
      if type_cmp t1 t2 then t1 else error ~msg:"Terop true & false exp type mismatch" loc)
  | AST.Fcall fcall ->
    if Map.mem env.vars fcall.func_name || not (Map.mem env.funcs fcall.func_name)
    then error ~msg:"func and var name conflict/func not defined" None;
    let func = Map.find_exn env.funcs fcall.func_name in
    if phys_equal func.scope Internal && phys_equal func.state Decl
    then func_list := fcall.func_name :: !func_list;
    let expected = List.map func.pars ~f:(fun par -> par.t) in
    let input = List.map fcall.args ~f:(fun arg -> tc_exp arg env) in
    tc_signature input expected fcall.func_name;
    func.ret_type
;;

(* 
 * Check AST statement
 * Type checker will traverse the AST from root recursively.
 * It will report once found an error and then terminate.
 * We only use env to check redefination error.
 * We do not check variable use before initialization in this function.
 * It is done in control flow check.
 * ast: AST transformed from source code
 * env: store the variables state: Defn, Decl.
 * func_name: function this current statement belongs to.
 *)
let rec tc_stm (ast : AST.mstm) (env : env) (func_name : Symbol.t) : env =
  let loc = Mark.src_span ast in
  match Mark.data ast with
  | AST.Assign asn_ast -> tc_assign asn_ast.name loc asn_ast.value env
  | AST.If if_ast -> tc_if if_ast.cond if_ast.true_stm if_ast.false_stm loc env func_name
  | AST.While while_ast -> tc_while while_ast.cond while_ast.body loc env func_name
  | AST.Return ret_ast -> tc_return ret_ast env func_name
  | AST.Nop -> env
  | AST.Seq seq_ast ->
    let env = tc_stm seq_ast.head env func_name in
    tc_stm seq_ast.tail env func_name
  | AST.Declare decl_ast ->
    tc_declare decl_ast.t decl_ast.name decl_ast.tail loc env func_name
  | AST.Sexp sexp ->
    ignore (tc_exp sexp env : dtype);
    env
  | AST.Assert aexp ->
    let dtype = (tc_exp aexp env : dtype) in
    if type_cmp dtype Bool then env else error ~msg:"assert exp type expect bool" loc

(* Check following
 * 1) Whether variable name exist in env
 * 2) If exist, then check whether variable type match exp type
 * 3) If match, update env state *)
and tc_assign name loc exp env : env =
  (* Check if variable is in env before assignment. *)
  match Map.find env.vars name with
  | None -> error ~msg:(sprintf "Not declared: `%s`" (Symbol.name name)) loc
  | Some var ->
    let exp_type = tc_exp exp env in
    if (not (type_cmp exp_type var.dtype)) || type_cmp exp_type Void
    then error ~msg:(sprintf "var type and exp type mismatch/exp type void") loc;
    let env_vars = Map.set env.vars ~key:name ~data:{ var with state = Defn } in
    { env with vars = env_vars }

and tc_return mexp env func_name =
  let func = Map.find_exn env.funcs func_name in
  let oracle_type = func.ret_type in
  let func_name_s = Symbol.name func_name in
  match mexp with
  | Some mexp ->
    let loc = Mark.src_span mexp in
    let exp_type = tc_exp mexp env in
    if type_cmp exp_type Void then error ~msg:"cannot return void exp" None;
    if not (type_cmp oracle_type exp_type)
    then error ~msg:(sprintf "%s return type mismatch" func_name_s) loc;
    env
  | None ->
    if not (type_cmp oracle_type AST.Void)
    then error ~msg:(sprintf "%s ret type expected void, mismatch" func_name_s) None;
    env

and tc_if cond true_stm false_stm loc env func_name =
  let cond_type = tc_exp cond env in
  match cond_type with
  | Int | Void -> error ~msg:(sprintf "If cond type is int/void") loc
  | Bool ->
    let env = tc_stm true_stm env func_name in
    tc_stm false_stm env func_name

and tc_while cond body loc env func_name =
  let cond_type = tc_exp cond env in
  match cond_type with
  | Int | Void -> error ~msg:(sprintf "While cond type is int/void") loc
  | Bool -> tc_stm body env func_name

(* Declare check is tricky because we will not override old env. 
 * Instead, we will return it once we check the tail.
 * We cannot declare a variable with type void. Void can only be used 
 * as return type for a function. *)
and tc_declare decl_type decl_name tail loc env func_name =
  if type_cmp decl_type Void
  then (
    let var_name = Symbol.name decl_name in
    error ~msg:(sprintf "cannot declare variable %s with type void" var_name) None)
  else ();
  match Map.find env.vars decl_name with
  | Some _ -> error ~msg:(sprintf "Declare a variable multiple time") loc
  | None ->
    let vars' =
      Map.add_exn env.vars ~key:decl_name ~data:{ state = Decl; dtype = decl_type }
    in
    let env' = { env with vars = vars' } in
    let env'' = (tc_stm tail env' func_name : env) in
    { env with vars = Map.remove env''.vars decl_name }
;;

(* If a function is already declared before, 
 * check if the old signature and new signature the same
 *)
let tc_redeclare env func_name (pars : param list) ret_type =
  let old_func = Map.find_exn env.funcs func_name in
  let old_dtype = List.map old_func.pars ~f:(fun par -> par.t) in
  let new_dtype = List.map pars ~f:(fun par -> par.t) in
  tc_signature (old_func.ret_type :: old_dtype) (ret_type :: new_dtype) func_name
;;

let tc_pars (pars : param list) =
  ignore
    (List.fold pars ~init:Set.empty ~f:(fun acc par ->
         if Set.mem acc par.i
         then error ~msg:"func parameter name conflict" None
         else Set.add acc par.i)
      : Set.t);
  List.iter pars ~f:(fun par ->
      if phys_equal par.t Void then error ~msg:"no void type for var" None)
;;

(* Rules to follow
 * 1) parameter variable name should not collide. 
 * 2) Function may be declared multiple times, in which case 
 * the declarations must be compatible. Types should be the
 * same, but parameter name are not required to be the same.
 * 3) functions declared in header file cannot be defined
 * in source files again.
 *)
let tc_fdecl ret_type func_name (pars : param list) env scope =
  tc_pars pars;
  if Map.mem env.funcs func_name
  then (
    tc_redeclare env func_name pars ret_type;
    env)
  else
    { env with
      funcs =
        Map.add_exn env.funcs ~key:func_name ~data:{ state = Decl; pars; ret_type; scope }
    }
;;

let pp_env env =
  printf "print env func\n%!";
  Map.iteri env.funcs ~f:(fun ~key:k ~data:d ->
      let pars = List.map d.pars ~f:AST.Print.pp_param |> String.concat ~sep:", " in
      printf "%s %s(%s)\n%!" (AST.Print.pp_dtype d.ret_type) (Util.Symbol.name k) pars)
;;

(* Rules to follow
 * 1) Parameters should not conflict with local variables. We have already elaborated
 * fdefn, so tc_stm is going to check whether parameter and local variable collide.
 * 2) Each function can only be defined once.
 * 3) Each function can only be define in source file, not header file.
 *)
let tc_fdefn ret_type func_name pars blk env scope =
  tc_pars pars;
  if phys_equal scope External
  then error ~msg:"Cannot define function in header file" None;
  let vars =
    List.fold pars ~init:env.vars ~f:(fun acc par ->
        Map.add_exn acc ~key:par.i ~data:{ state = Defn; dtype = par.t })
  in
  let env =
    match Map.find env.funcs func_name with
    | None ->
      let funcs =
        Map.set env.funcs ~key:func_name ~data:{ state = Defn; pars; ret_type; scope }
      in
      { funcs; vars }
    | Some s ->
      (match s.state with
      | Decl ->
        let funcs =
          Map.set env.funcs ~key:func_name ~data:{ state = Defn; pars; ret_type; scope }
        in
        tc_redeclare env func_name pars ret_type;
        { funcs; vars }
      | Defn ->
        error ~msg:(sprintf "function %s already defined." (Symbol.name func_name)) None)
  in
  tc_stm blk env func_name
;;

(* Check if functions used in program are defined eventually. *)
let _tc_post (env : env) =
  let funcs = !func_list in
  List.iter funcs ~f:(fun func ->
      let f = Map.find_exn env.funcs func in
      if phys_equal f.state Decl && phys_equal f.scope Internal
      then error ~msg:"func not defined" None)
;;

let rec _typecheck prog env scope =
  match prog with
  | [] ->
    _tc_post env;
    env
  | h :: t ->
    let env = { env with vars = Map.empty } in
    (match h with
    | AST.Fdecl fdecl ->
      let env = tc_fdecl fdecl.ret_type fdecl.func_name fdecl.pars env scope in
      _typecheck t env scope
    | AST.Fdefn fdefn ->
      let env = tc_fdefn fdefn.ret_type fdefn.func_name fdefn.pars fdefn.blk env scope in
      _typecheck t env scope
    | AST.Typedef _ -> _typecheck t env scope)
;;

(* env
 * | None: typecheck header file
 * | Some env: typecheck source file based on environment from header file. *)
let typecheck (prog : AST.gdecl list) (env : env option) =
  let env, scope =
    match env with
    | None ->
      ( { vars = Map.empty (* variable decl/def tracker *)
        ; funcs = Map.empty (* function signature *)
        }
      , External )
    | Some s -> s, Internal
  in
  _typecheck prog env scope
;;
