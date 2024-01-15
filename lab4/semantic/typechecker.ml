(* L4 Compiler
 * TypeChecker, also generate Type Syntax Tree(TST).
 * TST is just an AST with annotated type for each exp.
 *
 * This type checker is part of the static semantic analysis
 * It checkes whether each statement and expression is valid
 *
 * Statement level check
 * 1) Expression of statement is of the correct type. 
 * For example, whether the expression of If.cond is Bool type.
 * 2) Sub-statement is valid.
 * For example, whether Seq.head and Seq.tail is valid for Seq.
 * 3) No variable re-declaration.
 *
 * Expression level check
 * 1) operand and operator consistency
 * 
 * Function level check
 * 1) Each function is defined before called
 * 2) Calling exp argument type and defined signature match
 * 3) No conflict between parameter and local variables
 * 4) No functions are defined several time
 *
 * We can summarize above checks to two cases
 * 1) Type check in statement and expression(matchness for LHS and RHS)
 * 2) Variable declaration check, including re-decl and non-decl.
 *
 * Type alias is already handled in elab, so we don't bother it here.
 *
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
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
module TST = Inst
module Map = Util.Symbol.Map
module Set = Util.Symbol.Set
module Symbol = Util.Symbol
module Mark = Util.Mark

type state =
  | Decl
  | Defn

type dtype = AST.dtype
type param = AST.param

type var =
  { state : state
  ; dtype : dtype
  }

type func =
  { state : state
  ; pars : param list
  ; ret_type : dtype
  ; scope : [ `C0 | `External ]
  }

type field =
  { name : Symbol.t
  ; dtype : dtype
  }

type c0_struct =
  { fields : field list
  ; state : state
  ; order : int (* the earlier defined, the smaller the number *)
  }

type env =
  { vars : var Map.t (* variable decl/def tracker *)
  ; funcs : func Map.t (* function signature *)
  ; structs : c0_struct Map.t (* struct signature *)
  }

(* functions not defined during TC. Check once TC is done. *)
let func_list = ref []
let tc_errors : Util.Error_msg.t = Util.Error_msg.create ()

let dtype_of_field (s : c0_struct) (field_name : Symbol.t) =
  List.find_map_exn s.fields ~f:(fun field ->
      if phys_equal field.name field_name then Some field.dtype else None)
;;

let error ~msg src_span =
  Util.Error_msg.error tc_errors src_span ~msg;
  raise Util.Error_msg.Error
;;

let rec type_cmp t1 t2 =
  match t1, t2 with
  | `Int, `Int -> true
  | `Bool, `Bool -> true
  | `Void, `Void -> true
  | `NULL, `NULL -> true
  | `NULL, `Pointer _ -> true
  | `Pointer _, `NULL -> true
  | `Pointer p1, `Pointer p2 -> type_cmp p1 p2
  | `Array a1, `Array a2 -> type_cmp a1 a2
  | `Struct s1, `Struct s2 -> phys_equal s1 s2
  | _ -> false
;;

let is_big t =
  match t with
  | `Struct _ -> true
  | _ -> false
;;

let tc_big (dtype : AST.dtype) : unit =
  match dtype with
  | `Struct _ -> failwith "function return cannot be big type"
  | _ -> ()
;;

let rec tc_void (dtype : AST.dtype) : unit =
  match dtype with
  | `Void -> failwith "cannot declare void type"
  | `Pointer t | `Array t -> tc_void t
  | _ -> ()
;;

(* Check match between variable and assign operator. 
 * For now, only check assign with operation, like +=, -=, |=, >>= etc.
 * These assign operator should only deal with integer. *)
let op_cmp (dtype : Inst.dtype) (op : AST.asnop) : bool =
  match op with
  | `Asn -> true
  | _ -> if phys_equal dtype `Int then true else false
;;

(* Check whether element in params1 and params2 has same dtype respectively *)
let tc_signature params1 params2 func_name =
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
let rec tc_exp (exp : AST.mexp) (env : env) : TST.texp =
  let loc = Mark.src_span exp in
  let[@warning "-8"] tc_var (AST.Var var) : TST.texp =
    match Map.find env.vars var with
    | None -> error ~msg:(sprintf "Identifier not declared: `%s`" (Symbol.name var)) loc
    | Some var' ->
      let dtype = var'.dtype in
      { data = `Var var; dtype }
  in
  let[@warning "-8"] tc_binop (AST.Binop binop) : TST.texp =
    match binop.op with
    (* Relation op: < <= > >= *)
    | `Less | `Less_eq | `Greater | `Greater_eq ->
      let lhs, rhs = tc_exp binop.lhs env, tc_exp binop.rhs env in
      (match lhs.dtype, rhs.dtype with
      | `Int, `Int -> { data = `Binop { op = binop.op; lhs; rhs }; dtype = `Bool }
      | _, _ -> error ~msg:"Relation operand should be integer." loc)
    (* Polyeq op: ==, != *)
    | `Equal_eq | `Not_eq ->
      let lhs = tc_exp binop.lhs env in
      let rhs = tc_exp binop.rhs env in
      tc_big lhs.dtype;
      tc_big rhs.dtype;
      if type_cmp lhs.dtype rhs.dtype && not (type_cmp lhs.dtype `Void)
      then { data = `Binop { op = binop.op; lhs; rhs }; dtype = `Bool }
      else error ~msg:"Polyeq operands type mismatch" loc
    (* Rest are int operation *)
    | _ ->
      let lhs = tc_exp binop.lhs env in
      let rhs = tc_exp binop.rhs env in
      (match lhs.dtype, rhs.dtype with
      | `Int, `Int -> { data = `Binop { op = binop.op; lhs; rhs }; dtype = `Int }
      | _, _ -> error ~msg:"Integer binop operands are not integer" loc)
  in
  let[@warning "-8"] tc_terop (AST.Terop terop) : TST.texp =
    let cond = tc_exp terop.cond env in
    match cond.dtype with
    | `Int | `Void | `NULL | `Pointer _ | `Array _ | `Struct _ ->
      error ~msg:"Terop condition should be bool" loc
    | `Bool ->
      let true_exp = tc_exp terop.true_exp env in
      let false_exp = tc_exp terop.false_exp env in
      if type_cmp true_exp.dtype false_exp.dtype
      then
        if type_cmp true_exp.dtype `Void || is_big true_exp.dtype
        then error ~msg:"exp type cannot be void" None
        else { data = `Terop { cond; true_exp; false_exp }; dtype = true_exp.dtype }
      else error ~msg:"Terop true & false exp type mismatch" loc
  in
  let[@warning "-8"] tc_fcall (AST.Fcall fcall) : TST.texp =
    let func_name = fcall.func_name in
    if Map.mem env.vars func_name || not (Map.mem env.funcs func_name)
    then (
      let msg = sprintf "func %s and var name conflict/func not defined" func_name.name in
      error ~msg None);
    let func = Map.find_exn env.funcs func_name in
    if phys_equal func.scope `C0 && phys_equal func.state Decl
    then func_list := func_name :: !func_list;
    let expected = List.map func.pars ~f:(fun par -> par.t) in
    let args = List.map fcall.args ~f:(fun arg -> tc_exp arg env) in
    let args_dtype = args |> List.map ~f:(fun arg -> arg.dtype) in
    tc_signature (args_dtype :> TST.dtype list) (expected :> AST.dtype list) func_name;
    { data = `Fcall { func_name; args }; dtype = func.ret_type }
  in
  let[@warning "-8"] tc_edot (AST.EDot edot) : TST.texp =
    let struct_obj = tc_exp edot.struct_obj env in
    match struct_obj.dtype with
    | `Struct s ->
      let s = Map.find_exn env.structs s in
      let dtype = dtype_of_field s edot.field in
      { data = `Dot { struct_obj; field = edot.field }; dtype }
    | `Int | `Bool | `Void | `NULL | `Pointer _ | `Array _ ->
      error ~msg:"cannot dot access" loc
  in
  let[@warning "-8"] tc_ederef (AST.EDeref ederef) : TST.texp =
    let tderef = tc_exp ederef.ptr env in
    match tderef.dtype with
    | `Pointer ptr ->
      (match ptr with
      | `NULL -> error ~msg:"cannot dereference NULL" loc
      | `Void -> error ~msg:"cannot dereference void" loc
      | `Int | `Bool | `Pointer _ | `Array _ | `Struct _ ->
        { data = `Deref { ptr = tderef }; dtype = ptr })
    | `Int | `Bool | `Void | `NULL | `Array _ | `Struct _ -> error ~msg:"cannot deref" loc
  in
  let[@warning "-8"] tc_enth (AST.ENth enth) : TST.texp =
    let tarr = tc_exp enth.arr env in
    match tarr.dtype with
    | `Array arr ->
      let tidx = tc_exp enth.index env in
      (match tidx.dtype with
      | `Int -> { data = `Nth { arr = tarr; index = tidx }; dtype = arr }
      | _ -> error ~msg:"array index expect int" loc)
    | `Int | `Bool | `Void | `NULL | `Pointer _ | `Struct _ ->
      error ~msg:"cannot [] for non-array" loc
  in
  let[@warning "-8"] tc_alloc (AST.Alloc alloc) : TST.texp =
    match alloc.t with
    | `Int | `Bool | `Pointer _ | `Array _ ->
      { data = `Alloc { dtype = alloc.t }; dtype = `Pointer alloc.t }
    | `Void | `NULL -> error ~msg:"cannot alloc void/null." loc
    | `Struct s ->
      let s' = Map.find_exn env.structs s in
      if phys_equal s'.state Defn
      then { data = `Alloc { dtype = alloc.t }; dtype = `Pointer alloc.t }
      else error ~msg:"alloc undefined struct" loc
  in
  let[@warning "-8"] tc_alloc_arr (AST.Alloc_arr alloc_arr) : TST.texp =
    let nitems = tc_exp alloc_arr.e env in
    (match alloc_arr.t with
    | `Int | `Bool | `Pointer _ | `Array _ -> ()
    | `Void | `NULL -> error ~msg:"cannot alloc_arr void/null." loc
    | `Struct s ->
      let s' = Map.find_exn env.structs s in
      if not (phys_equal s'.state Defn) then error ~msg:"alloc_arr undefined struct" loc);
    match nitems.dtype with
    | `Int ->
      { data = `Alloc_arr { etype = alloc_arr.t; nitems }; dtype = `Array alloc_arr.t }
    | _ -> error ~msg:"alloc_arr size expect int" loc
  in
  match Util.Mark.data exp with
  | Var var -> tc_var (Var var)
  | Const_int i -> { data = `Const_int i; dtype = `Int }
  | True -> { data = `True; dtype = `Bool }
  | False -> { data = `False; dtype = `Bool }
  | Binop binop -> tc_binop (Binop binop)
  | Terop terop -> tc_terop (Terop terop)
  | Fcall fcall -> tc_fcall (Fcall fcall)
  | EDot edot -> tc_edot (EDot edot)
  | EDeref ederef -> tc_ederef (EDeref ederef)
  | ENth enth -> tc_enth (ENth enth)
  | NULL -> { data = `NULL; dtype = `NULL }
  | Alloc alloc -> tc_alloc (Alloc alloc)
  | Alloc_arr alloc_arr -> tc_alloc_arr (Alloc_arr alloc_arr)
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
let rec tc_stm (ast : AST.mstm) (env : env) (func_name : Symbol.t) : TST.stm * env =
  let loc = Mark.src_span ast in
  match Mark.data ast with
  | AST.Assign asn_ast -> tc_assign (AST.Assign asn_ast) env loc
  | AST.If if_ast -> tc_if if_ast.cond if_ast.true_stm if_ast.false_stm loc env func_name
  | AST.While while_ast -> tc_while while_ast.cond while_ast.body loc env func_name
  | AST.Return ret_ast -> tc_return ret_ast env func_name
  | AST.Nop -> TST.Nop, env
  | AST.Seq seq_ast ->
    let head_tst, env = tc_stm seq_ast.head env func_name in
    let tail_tst, env = tc_stm seq_ast.tail env func_name in
    TST.Seq { head = head_tst; tail = tail_tst }, env
  | AST.Declare decl_ast -> tc_declare (AST.Declare decl_ast) loc env func_name
  | AST.Sexp sexp ->
    let tsexp = tc_exp sexp env in
    tc_big tsexp.dtype;
    TST.Sexp tsexp, env
  | AST.Assert aexp ->
    let tasrt = tc_exp aexp env in
    if type_cmp tasrt.dtype `Bool
    then TST.Assert tasrt, env
    else error ~msg:"assert exp type expect bool" loc

and trans_lvalue (lv : AST.lvalue) (env : env) : TST.texp =
  match lv with
  | Ident name ->
    let var = Map.find_exn env.vars name in
    let dtype = var.dtype in
    { data = `Var name; dtype }
  | LVDot lvdot ->
    let struct_obj = trans_lvalue (Mark.data lvdot.struct_obj) env in
    let stype = struct_obj.dtype in
    (match stype with
    | `Struct sname ->
      let s = Map.find_exn env.structs sname in
      let dtype = dtype_of_field s lvdot.field in
      { data = `Dot { struct_obj; field = lvdot.field }; dtype }
    | _ -> failwith "dot access expect a struct type")
  | LVDeref lvderef ->
    let tptr = trans_lvalue (Mark.data lvderef.ptr) env in
    (match tptr.dtype with
    | `Pointer ptr -> { data = `Deref { ptr = tptr }; dtype = ptr }
    | _ -> failwith "deref expect a pointer")
  | LVNth lvnth ->
    let tarr = trans_lvalue (Mark.data lvnth.arr) env in
    (match tarr.dtype with
    | `Array arr ->
      let index = tc_exp lvnth.index env in
      (match index.dtype with
      | `Int -> ()
      | _ -> failwith "expect array index to be int.");
      { data = `Nth { arr = tarr; index }; dtype = arr }
    | _ -> failwith "array access expect array type")

(* Check following
 * 1) Whether variable name exist in env
 * 2) If exist, then check whether variable type match exp type
 * 3) Check match between asnop and var type
 * 4) If all match, update env state
 * Notice that update field or array index or dereference does
 * not define variable itself.
 *)
and[@warning "-8"] tc_assign (AST.Assign asn_ast) (env : env) loc : TST.stm * env =
  (* Check if variable is in env before assignment. *)
  let name = trans_lvalue (Mark.data asn_ast.name) env in
  let value = tc_exp asn_ast.value env in
  let asn_tst = TST.Assign { name; value; op = asn_ast.op } in
  let var_type = name.dtype in
  let val_type = value.dtype in
  tc_big var_type;
  tc_big val_type;
  if (not (type_cmp val_type var_type)) || type_cmp val_type `Void
  then error ~msg:(sprintf "var type and exp type mismatch/exp type void") loc;
  if not (op_cmp var_type asn_ast.op) then error ~msg:"operand and operator mismatch" None;
  match Mark.data asn_ast.name with
  | Ident ident ->
    let env_vars = Map.set env.vars ~key:ident ~data:{ dtype = var_type; state = Defn } in
    asn_tst, { env with vars = env_vars }
  | LVDot _ | LVDeref _ | LVNth _ -> asn_tst, env

and tc_return mexp env func_name =
  let func = Map.find_exn env.funcs func_name in
  let oracle_type = func.ret_type in
  let func_name_s = Symbol.name func_name in
  match mexp with
  | Some mexp ->
    let loc = Mark.src_span mexp in
    let texp = tc_exp mexp env in
    if type_cmp texp.dtype `Void then error ~msg:"cannot return void exp" None;
    if not (type_cmp oracle_type texp.dtype)
    then error ~msg:(sprintf "%s return type mismatch" func_name_s) loc;
    TST.Return (Some texp), env
  | None ->
    if not (type_cmp oracle_type `Void)
    then error ~msg:(sprintf "%s ret type expected void, mismatch" func_name_s) None;
    TST.Return None, env

and tc_if cond true_stm false_stm loc env func_name =
  let cond = tc_exp cond env in
  match cond.dtype with
  | `Int | `Void | `NULL | `Pointer _ | `Array _ | `Struct _ ->
    error ~msg:(sprintf "If cond type is should be bool") loc
  | `Bool ->
    let true_stm, _ = tc_stm true_stm env func_name in
    let false_stm, _ = tc_stm false_stm env func_name in
    TST.If { cond; true_stm; false_stm }, env

and tc_while cond body loc env func_name =
  let cond = tc_exp cond env in
  match cond.dtype with
  | `Int | `Void | `NULL | `Pointer _ | `Array _ | `Struct _ ->
    error ~msg:(sprintf "While cond type should be bool") loc
  | `Bool ->
    let body, _ = tc_stm body env func_name in
    TST.While { cond; body }, env

(* Declare check is tricky because we will not override old env. 
 * Instead, we will return it once we check the tail.
 * We cannot declare a variable with type void. Void can only be used 
 * as return type for a function. *)
and[@warning "-8"] tc_declare (AST.Declare decl) loc env func_name =
  let decl_type, decl_name, tail = decl.t, decl.name, decl.tail in
  tc_big decl_type;
  tc_void decl_type;
  if Map.mem env.vars decl_name then error ~msg:(sprintf "Redeclare a variable ") loc;
  let vars', value =
    match decl.value with
    | None ->
      Map.add_exn env.vars ~key:decl_name ~data:{ state = Decl; dtype = decl_type }, None
    | Some value ->
      let texp = tc_exp value env in
      if (not (type_cmp texp.dtype decl.t)) || type_cmp texp.dtype `Void
      then error ~msg:(sprintf "var type and exp type mismatch/exp type void") loc;
      Map.set env.vars ~key:decl.name ~data:{ state = Defn; dtype = decl_type }, Some texp
  in
  let env' = { env with vars = vars' } in
  let tail_tst, env'' = tc_stm tail env' func_name in
  let env_ret = { env with vars = Map.remove env''.vars decl_name } in
  TST.Declare { t = decl.t; name = decl.name; value; tail = tail_tst }, env_ret
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
      if type_cmp par.t `Void then error ~msg:"no void type for var" None;
      if is_big par.t then error ~msg:"cannot pass big type as parameter" None)
;;

(* Rules to follow
 * 1) parameter variable name should not collide. 
 * 2) Function may be declared multiple times, in which case 
 * the declarations must be compatible. Types should be the
 * same, but parameter name are not required to be the same.
 * 3) Cannot declare int main() in header
 * 4) Cannot use big type as parameter type
 *)
let[@warning "-8"] tc_fdecl (AST.Fdecl fdecl) env =
  let ret_type, func_name, pars = fdecl.ret_type, fdecl.func_name, fdecl.pars in
  if phys_equal fdecl.scope `External
     && phys_equal func_name (Symbol.symbol "main")
     && List.length pars = 0
     && phys_equal ret_type `Int
  then error ~msg:"int main() cannot be declared in header" None;
  tc_pars pars;
  if Map.mem env.funcs func_name
  then (
    tc_redeclare env func_name pars ret_type;
    env)
  else (
    let func = { state = Decl; pars; ret_type; scope = fdecl.scope } in
    let funcs = Map.add_exn env.funcs ~key:func_name ~data:func in
    { env with funcs })
;;

(* As long as sdecl is not defined, declare it. *)
let tc_sdecl (sname : Symbol.t) (env : env) : env =
  let s = { fields = []; state = Decl; order = 0 } in
  match Map.find env.structs sname with
  | None -> { env with structs = Map.add_exn env.structs ~key:sname ~data:s }
  | Some _ -> env
;;

let tc_sdefn (sname : Symbol.t) (fields : AST.field list) (env : env) : env =
  let fields = List.map fields ~f:(fun field -> { name = field.i; dtype = field.t }) in
  ignore
    (List.fold fields ~init:Set.empty ~f:(fun acc field ->
         (match field.dtype with
         | `Int | `Bool | `Pointer _ | `Array _ -> ()
         | `Void | `NULL -> error ~msg:"Void/NULL cannot be struct field" None
         | `Struct s ->
           let s' = Map.find_exn env.structs s in
           if phys_equal s'.state Decl
           then error ~msg:"struct use a field from undefined struct" None);
         if Set.mem acc field.name
         then error ~msg:"struct field name conflict" None
         else Set.add acc field.name)
      : Set.t);
  let s = { fields; state = Defn; order = Map.length env.structs } in
  match Map.find env.structs sname with
  | None -> { env with structs = Map.add_exn env.structs ~key:sname ~data:s }
  | Some s' ->
    (match s'.state with
    | Defn -> error ~msg:"struct already defined" None
    | Decl -> { env with structs = Map.set env.structs ~key:sname ~data:s })
;;

let pp_env env =
  printf "print env func\n%!";
  Map.iteri env.funcs ~f:(fun ~key:k ~data:d ->
      let pars = List.map d.pars ~f:AST.Print.pp_param |> String.concat ~sep:", " in
      printf "%s %s(%s)\n%!" (AST.Print.pp_dtype d.ret_type) (Util.Symbol.name k) pars)
;;

(* Rules to follow
 * 1) Parameters should not conflict with local variables. 
 * 2) Each function can only be defined once.
 * 3) Each function can only be define in source file, not header file.
 * 4) functions declared in header file cannot be defined in source files again.
 *)
let[@warning "-8"] tc_fdefn (AST.Fdefn fdefn) env : TST.fdefn * env =
  let ret_type, func_name, pars, blk, scope =
    fdefn.ret_type, fdefn.func_name, fdefn.pars, fdefn.blk, fdefn.scope
  in
  tc_pars pars;
  if phys_equal scope `External
  then error ~msg:"Cannot define function in header file" None;
  let vars =
    List.fold pars ~init:env.vars ~f:(fun acc par ->
        Map.add_exn acc ~key:par.i ~data:{ state = Defn; dtype = par.t })
  in
  let env =
    match Map.find env.funcs func_name with
    | None ->
      let func = { state = Defn; pars; ret_type; scope } in
      let funcs = Map.set env.funcs ~key:func_name ~data:func in
      { env with funcs; vars }
    | Some s ->
      (match s.state, s.scope with
      | Decl, `C0 ->
        let func = { state = Defn; pars; ret_type; scope } in
        let funcs = Map.set env.funcs ~key:func_name ~data:func in
        tc_redeclare env func_name pars ret_type;
        { env with funcs; vars }
      | _, _ -> error ~msg:(sprintf "%s already defined." (Symbol.name func_name)) None)
  in
  let blk, _ = tc_stm blk env func_name in
  let pars =
    List.map fdefn.pars ~f:(fun par : TST.param -> { dtype = par.t; data = par.i })
  in
  { ret_type; func_name; pars; blk }, env
;;

(* Check after all gdecls are processed
 * 1) functions used in program are defined 
 * 2) provide correct main function defination 
 *)
let _tc_post (env : env) =
  let funcs = !func_list in
  List.iter funcs ~f:(fun func ->
      let f = Map.find_exn env.funcs func in
      if phys_equal f.state Decl && phys_equal f.scope `C0
      then error ~msg:"func not defined" None);
  let cond =
    Map.fold env.funcs ~init:false ~f:(fun ~key:fname ~data:func acc ->
        if phys_equal fname (Symbol.symbol "main")
        then acc || phys_equal func.state Defn
        else acc)
  in
  if not cond then error ~msg:"main not defined" None
;;

let rec _typecheck (ast : AST.gdecl list) (tst : TST.program) env =
  match ast with
  | [] ->
    _tc_post env;
    List.rev tst, env
  | h :: t ->
    let env = { env with vars = Map.empty } in
    (match h with
    | Fdecl fdecl ->
      tc_big fdecl.ret_type;
      let env = tc_fdecl (Fdecl fdecl) env in
      _typecheck t tst env
    | Fdefn fdefn ->
      tc_big fdefn.ret_type;
      let fdefn_tst, env = tc_fdefn (Fdefn fdefn) env in
      _typecheck t (fdefn_tst :: tst) env
    | Typedef _ -> _typecheck t tst env
    | Sdecl sdecl ->
      let env = tc_sdecl sdecl.struct_name env in
      _typecheck t tst env
    | Sdefn sdefn ->
      let env = tc_sdefn sdefn.struct_name sdefn.fields env in
      _typecheck t tst env)
;;

let typecheck (prog : AST.program) : TST.program * env =
  let env =
    { vars = Map.empty (* variable decl/def tracker *)
    ; funcs = Map.empty (* function signature *)
    ; structs = Map.empty (* struct signature *)
    }
  in
  _typecheck prog [] env
;;
