(* L4 Compiler
 * TST -> IR Translator
 *
 * Calculate memory address for dot, deref and array access
 * Provide check before access real memory.
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified by: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
open Core
module TST = Semantic.Inst
module Tree = Inst
module Map = Util.Symbol.Map
module Symbol = Util.Symbol
module Size = Var.Size
module Label = Util.Label
module Mark = Util.Mark
module Temp = Var.Temp
module TC = Semantic.Typechecker
module Exp = Tree.Exp
module St = Tree.St
module Sexp = Tree.Sexp
module Mem = Tree.Mem
module Addr = Tree.Addr

type field =
  { dtype : TST.dtype
  ; offset : Int64.t
  ; size : Size.t
  }

type c0_struct =
  { fields : field Map.t
  ; size : Size.t
  }

type var =
  { temp : Temp.t
  ; dtype : TST.dtype
  }

type env =
  { funcs : TC.func Map.t
  ; structs : c0_struct Map.t
  ; vars : var Map.t
  }

(* Used by lvalue to distinguish variable type *)
type ldest =
  | Mem of Mem.t
  | Temp of Temp.t

let alignment = ref Map.empty

(* Return the alignment requirement for data type
 * Struct alignment depends on the strictest(largest) field *)
let rec align (dtype : TST.dtype) (env : env) : Size.t =
  match dtype with
  | `Int -> `DWORD
  | `Bool -> `DWORD
  | `Void -> `VOID
  | `NULL -> `QWORD
  | `Pointer _ -> `QWORD
  | `Array _ -> `QWORD
  | `Struct sname ->
    if Map.mem !alignment sname
    then Map.find_exn !alignment sname
    else (
      let s = Map.find_exn env.structs sname in
      let m = Map.map s.fields ~f:(fun field -> align field.dtype env) in
      let l = Map.data m in
      let ret =
        match List.max_elt l ~compare:Size.compare with
        | Some s -> s
        | None -> `VOID
      in
      alignment := Map.set !alignment ~key:sname ~data:ret;
      ret)
;;

(* Only struct is large type in C0, others are stored on stack
 * Array is only a reference, not real allocated array content *)
let sizeof_dtype (dtype : TST.dtype) (env : env) : Size.t =
  match dtype with
  | `Int -> `DWORD
  | `Bool -> `DWORD
  | `Void -> `VOID
  | `NULL -> `QWORD
  | `Pointer _ -> `QWORD
  | `Array _ -> `QWORD
  | `Struct sname ->
    let s = Map.find_exn env.structs sname in
    s.size
;;

(* WARNING: some case the input is not small type. remove these uses! *)
let sizeof_dtype' (dtype : TST.dtype) : Size.primitive =
  match dtype with
  | `Int -> `DWORD
  | `Bool -> `DWORD
  | `Void -> `VOID
  | `NULL -> `QWORD
  | `Pointer _ -> `QWORD
  | `Array _ -> `QWORD
  | `Struct _ -> failwith "expect small type"
;;

let is_large = function
  | `Struct _ -> true
  | _ -> false
;;

let get_struct_exn (dtype : TST.dtype) : Symbol.t =
  match dtype with
  | `Struct s -> s
  | _ -> failwith "expect dtype as struct"
;;

let check_base_size (base : Sexp.t) =
  if Size.compare (base.size :> Size.t) `QWORD <> 0 then failwith "base should be qword"
;;

let check_index_size (index : Sexp.t) =
  if Size.compare (index.size :> Size.t) `DWORD <> 0 then failwith "index should be dword"
;;

(* `Pure is expression that not lead to side-effect
 * `Impure is expression that may lead to side-effect, 
 * like rasing div-zero or other exception
 * `Compare is return boolean value. *)
let trans_binop = function
  | `Plus -> `Pure Tree.Plus
  | `Minus -> `Pure Tree.Minus
  | `Times -> `Pure Tree.Times
  | `And -> `Pure Tree.And
  | `Or -> `Pure Tree.Or
  | `Hat -> `Pure Tree.Xor
  | `Right_shift -> `Impure Tree.Right_shift
  | `Left_shift -> `Impure Tree.Left_shift
  | `Divided_by -> `Impure Tree.Divided_by
  | `Modulo -> `Impure Tree.Modulo
  | `Equal_eq -> `Compare Tree.Equal_eq
  | `Greater -> `Compare Tree.Greater
  | `Greater_eq -> `Compare Tree.Greater_eq
  | `Less -> `Compare Tree.Less
  | `Less_eq -> `Compare Tree.Less_eq
  | `Not_eq -> `Compare Tree.Not_eq
;;

let gen_cond (sexp : Sexp.t) : Sexp.t * Tree.binop * Sexp.t =
  let size = Sexp.get_size_p sexp in
  sexp, Tree.Equal_eq, Sexp.wrap size (Exp.of_int 1L)
;;

let c0_raise (signo : St.t) : Tree.fdefn =
  let body =
    [ Tree.Fcall
        { dest = None
        ; func_name = Symbol.Fname.raise
        ; args = [ St.to_Sexp signo ]
        ; scope = `External
        }
    ]
  in
  { func_name = Symbol.Fname.raise; temps = [ signo ]; body; scope = `Internal }
;;

(* Check whether base is 0 *)
let check_null (base : Sexp.t) : Tree.stm list =
  let lhs, op, rhs = base, Tree.Equal_eq, Sexp.wrap `QWORD (Exp.of_int 0L) in
  check_base_size base;
  let target_true = Label.label (Some "is_null") in
  let target_false = Label.label (Some "not_null") in
  [ Tree.CJump { lhs; op; rhs; target_true; target_false }
  ; Tree.Label target_true
  ; Tree.Fcall
      { dest = None
      ; func_name = Symbol.Fname.raise
      ; args = [ Sexp.wrap `DWORD (Exp.of_int Symbol.Fname.usr2) ]
      ; scope = `Internal
      }
  ; Tree.Label target_false
  ]
;;

(* Check whether offset is within [0, array_size), also check whether array base is null.
 * This array_size is number of elements. *)
let check_bound (base : Sexp.t) (index : Sexp.t) : Tree.stm list * Tree.stm list =
  let zero = Sexp.wrap index.size (Exp.of_int 0L) in
  let null_check = check_null base in
  let mem_header : Mem.t = Addr.of_bisd base None None (Some (-8L)) |> Mem.wrap `QWORD in
  let arr_size_t = Temp.create () |> Exp.of_t |> Sexp.wrap index.size in
  let arr_size_s = Sexp.to_St arr_size_t in
  let load = [ Tree.Load { src = mem_header; dest = arr_size_s } ] in
  let target_raise = Label.label (Some "fail_bd_check") in
  let target1 = Label.label (Some "pass_lo_check") in
  let target2 = Label.label (Some "pass_hi_check") in
  let check =
    [ Tree.CJump
        { lhs = index
        ; op = Tree.Greater_eq
        ; rhs = zero
        ; target_false = target_raise
        ; target_true = target1
        }
    ; Tree.Label target1
    ; Tree.CJump
        { lhs = index
        ; op = Tree.Less
        ; rhs = arr_size_t
        ; target_false = target_raise
        ; target_true = target2
        }
    ; Tree.Label target_raise
    ; Tree.Fcall
        { dest = None
        ; func_name = Symbol.Fname.raise
        ; args = [ Sexp.wrap `DWORD (Exp.of_int Symbol.Fname.usr2) ]
        ; scope = `Internal
        }
    ; Tree.Label target2
    ]
  in
  null_check, load @ check
;;

let trans_exp_bin (binop : TST.binexp) (env : env) trans_func : Tree.stm list * Sexp.t =
  let lhs_stm, lhs = trans_func binop.lhs env in
  let rhs_stm, rhs = trans_func binop.rhs env in
  let size = sizeof_dtype' binop.lhs.dtype in
  match trans_binop binop.op with
  | `Pure op -> lhs_stm @ rhs_stm, Sexp.wrap size (Exp.of_binop op lhs rhs)
  | `Impure op ->
    let dest = Temp.create () |> Exp.of_t |> Sexp.wrap size |> Sexp.to_St in
    lhs_stm @ rhs_stm @ [ Tree.Effect { dest; lhs; op; rhs } ], St.to_Sexp dest
  | `Compare op -> lhs_stm @ rhs_stm, Sexp.wrap size (Exp.of_binop op lhs rhs)
;;

let trans_terop (terop : TST.terexp) (env : env) trans_func =
  (* 
   * CJump cond target_true, target_false
   * target_true:
   * a <- true_exp;
   * Jump label_ter_end
   * target_false:
   * a <- false_exp
   * label_ter_end:
   * restcode
   *)
  let cond_stms, cond_exp = trans_func terop.cond env in
  let true_stms, true_exp = trans_func terop.true_exp env in
  let false_stms, false_exp = trans_func terop.false_exp env in
  let size = sizeof_dtype' terop.true_exp.dtype in
  let dest = Temp.create () |> Exp.of_t |> Sexp.wrap size |> Sexp.to_St in
  let target_true = Label.label (Some "terop_true") in
  let target_false = Label.label (Some "terop_false") in
  let true_stms = Tree.Label target_true :: true_stms in
  let false_stms = Tree.Label target_false :: false_stms in
  let label_ter_end = Label.label (Some "terop_end") in
  let lhs, op, rhs = gen_cond cond_exp in
  let seq =
    cond_stms
    @ [ Tree.CJump { lhs; op; rhs; target_true; target_false } ]
    @ true_stms
    @ [ Tree.Move { dest; src = true_exp }; Tree.Jump label_ter_end ]
    @ false_stms
    @ [ Tree.Move { dest; src = false_exp }; Tree.Label label_ter_end ]
  in
  seq, St.to_Sexp dest
;;

let trans_fcall (fcall : TST.fcall) (env : env) trans_func =
  (* First calculate arguments with potential side effect, then call fcall. *)
  let args_stms_ls, args =
    List.fold_left fcall.args ~init:[] ~f:(fun acc arg ->
        let arg_stms, arg_exp = trans_func arg env in
        (arg_stms, arg_exp) :: acc)
    |> List.rev
    |> List.unzip
  in
  let args_stms = List.concat args_stms_ls in
  let func_name = fcall.func_name in
  let func = Map.find_exn env.funcs func_name in
  let scope = (func.scope :> [ `C0 | `Internal | `External ]) in
  let size = sizeof_dtype' func.ret_type in
  match size with
  | `VOID ->
    let call = Tree.Fcall { dest = None; args; func_name; scope } in
    let call_stms = args_stms @ [ call ] in
    call_stms, Sexp.wrap `VOID (Exp.of_void ())
  | _ ->
    let dest = Temp.create () |> Exp.of_t |> Sexp.wrap size |> Sexp.to_St in
    let call = Tree.Fcall { dest = Some dest; args; func_name; scope } in
    let call_stms = args_stms @ [ call ] in
    call_stms, St.to_Sexp dest
;;

let trans_alloc (alloc : TST.alloc) env =
  let size = `DWORD in
  let size_32 =
    sizeof_dtype alloc.dtype env |> Size.type_size_byte |> Exp.of_int |> Sexp.wrap size
  in
  let nitems = Sexp.wrap size (Exp.of_int 1L) in
  let ptr : St.t = Temp.create () |> Exp.of_t |> Sexp.wrap `QWORD |> Sexp.to_St in
  let func_name = Symbol.Fname.calloc in
  let args = [ nitems; size_32 ] in
  [ Tree.Fcall { dest = Some ptr; func_name; args; scope = `External } ], St.to_Sexp ptr
;;

(* alloc size should >= 0 *)
let check_alloc_arr (size : Sexp.t) : Tree.stm list =
  let lhs, op, rhs = size, Tree.Greater_eq, Sexp.wrap `DWORD (Exp.of_int 0L) in
  check_index_size size;
  let target_true = Label.label (Some "arr_size_legal") in
  let target_false = Label.label (Some "arr_size_illegal") in
  [ Tree.CJump { lhs; op; rhs; target_true; target_false }
  ; Tree.Label target_false
  ; Tree.Fcall
      { dest = None
      ; func_name = Symbol.Fname.raise
      ; args = [ Sexp.wrap `DWORD (Exp.of_int Symbol.Fname.usr2) ]
      ; scope = `Internal
      }
  ; Tree.Label target_true
  ]
;;

let trans_alloc_arr (alloc_arr : TST.alloc_arr) env trans_func need_check =
  (* C0 array has 8 byte header to store the array length. But it only take DWORD for the size.
   * To access it, use base + disp. Base is the start addr for array. *)
  let stms, (nitems : Sexp.t) = trans_func alloc_arr.nitems env in
  let check = if need_check then check_alloc_arr nitems else [] in
  let size_4 = nitems.size in
  let esize = sizeof_dtype alloc_arr.etype env |> Size.type_size_byte in
  let func_name = Symbol.Fname.calloc in
  let size_tot =
    Addr.of_bisd (Sexp.wrap size_4 (Exp.of_int 8L)) (Some nitems) (Some esize) None
  in
  let args =
    [ 1L |> Exp.of_int |> Sexp.wrap size_4; size_tot |> Exp.of_bisd |> Sexp.wrap size_4 ]
  in
  let size_8 = `QWORD in
  let ptr_c0 = Temp.create () |> Exp.of_t |> Sexp.wrap size_8 in
  let alloc =
    Tree.Fcall { dest = Some (Sexp.to_St ptr_c0); func_name; args; scope = `External }
  in
  let header = Mem.wrap size_8 (Addr.of_bisd ptr_c0 None None None) in
  let store_size = Tree.Store { dest = header; src = { nitems with size = size_8 } } in
  let ptr_c = Temp.create () |> Exp.of_t |> Sexp.wrap size_8 |> Sexp.to_St in
  let c_addr =
    Addr.of_bisd ptr_c0 None None (Some 8L) |> Exp.of_bisd |> Sexp.wrap size_8
  in
  let move = Tree.Move { dest = ptr_c; src = c_addr } in
  stms @ check @ [ alloc; store_size; move ], St.to_Sexp ptr_c
;;

let trans_mem
    (base : Sexp.t)
    (index : Sexp.t option)
    (scale : Int64.t option)
    (disp : Int64.t option)
    (size : Size.primitive)
    : Tree.stm list * Sexp.t
  =
  let src = Addr.of_bisd base index scale disp |> Mem.wrap size in
  let dest = Temp.create () |> Exp.of_t |> Sexp.wrap size |> Sexp.to_St in
  let load = Tree.Load { src; dest } in
  [ load ], St.to_Sexp dest
;;

(* Return small value, or memory calculation formula *)
let[@warning "-8"] rec trans_exp (need_check : bool) (exp_tst : TST.texp) (env : env)
    : Tree.stm list * Sexp.t
  =
  let size = sizeof_dtype' exp_tst.dtype in
  match exp_tst.data with
  | `Dot dot ->
    trans_dot need_check ({ data = dot; dtype = exp_tst.dtype } : TST.dot TST.typed) env
  | `Nth nth ->
    trans_nth need_check ({ data = nth; dtype = exp_tst.dtype } : TST.nth TST.typed) env
  | `Deref deref -> trans_deref need_check deref.ptr env size
  | `Binop binop -> trans_exp_bin binop env (trans_exp need_check)
  | `Terop terop -> trans_terop terop env (trans_exp need_check)
  | `Postop pop -> trans_postop need_check pop env
  | `Fcall fcall -> trans_fcall fcall env (trans_exp need_check)
  | `Alloc alloc -> trans_alloc alloc env
  | `Alloc_arr alloc_arr ->
    trans_alloc_arr alloc_arr env (trans_exp need_check) need_check
  | `Var id ->
    let var = Map.find_exn env.vars id in
    [], Sexp.wrap size (Exp.of_t var.temp)
  | `Const_int c -> [], Sexp.wrap size (Exp.of_int (Int64.of_int32 c))
  | `True -> [], Sexp.wrap size (Exp.of_int 1L)
  | `False -> [], Sexp.wrap size (Exp.of_int 0L)
  | `NULL -> [], Sexp.wrap size (Exp.of_int 0L)

and trans_deref need_check ptr env size =
  let base_stm, base = trans_exp need_check ptr env in
  check_base_size base;
  let load, dest = trans_mem base None None None size in
  let check = if need_check then check_null base else [] in
  base_stm @ check @ load, dest

and trans_nth need_check (nth : TST.nth TST.typed) env : Tree.stm list * Sexp.t =
  let base_stm, base = trans_exp need_check nth.data.arr env in
  let index_stm, index_exp = trans_exp need_check nth.data.index env in
  check_base_size base;
  check_index_size index_exp;
  let index = Temp.create () |> Exp.of_t |> Sexp.wrap `QWORD in
  let index_stm =
    index_stm @ [ Tree.Cast { dest = Sexp.to_St index; src = index_exp } ]
  in
  let scale = sizeof_dtype nth.dtype env |> Size.type_size_byte in
  let base_check, bound_check = if need_check then check_bound base index else [], [] in
  if is_large nth.dtype
  then
    ( base_stm @ index_stm @ base_check @ bound_check
    , Addr.of_bisd base (Some index) (Some scale) None |> Exp.of_bisd |> Sexp.wrap `QWORD
    )
  else (
    let size = sizeof_dtype' nth.dtype in
    let load, dest = trans_mem base (Some index) (Some scale) None size in
    base_stm @ index_stm @ base_check @ bound_check @ load, dest)

and trans_dot need_check (dot : TST.dot TST.typed) env : Tree.stm list * Sexp.t =
  let s = Map.find_exn env.structs (get_struct_exn dot.data.struct_obj.dtype) in
  let field = Map.find_exn s.fields dot.data.field in
  let offset = Sexp.wrap `QWORD (Exp.of_int field.offset) in
  let base_stm, base =
    let s' = dot.data.struct_obj in
    match s'.data with
    | `Deref deref -> trans_exp need_check deref.ptr env
    | `Dot dot' -> trans_dot need_check { data = dot'; dtype = s'.dtype } env
    | `Nth nth ->
      trans_nth need_check ({ data = nth; dtype = s'.dtype } : TST.nth TST.typed) env
    | _ -> failwith "hmmm, should not happen"
  in
  check_base_size base;
  let check = if need_check then check_null base else [] in
  if is_large dot.dtype
  then
    if Int64.equal field.offset 0L
    then base_stm, base
    else base_stm @ check, Sexp.wrap `QWORD (Exp.of_binop Plus base offset)
  else (
    let size = sizeof_dtype' dot.dtype in
    let load, dest = trans_mem base (Some offset) (Some 1L) None size in
    base_stm @ check @ load, dest)

and trans_postop need_check (pop : TST.postexp) (env : env) =
  let one : TST.texp = { data = `Const_int Int32.one; dtype = `Int } in
  let assign =
    match pop.op with
    | `Plus_plus -> TST.Assign { name = pop.operand; value = one; op = `Plus_asn }
    | `Minus_minus -> TST.Assign { name = pop.operand; value = one; op = `Minus_asn }
  in
  let stms = trans_asnop_rev [] assign need_check env in
  List.rev stms, Exp.of_void () |> Sexp.wrap `VOID

and trans_lvalue (lvalue : TST.texp) (env : env) (need_check : bool)
    : Tree.stm list * Tree.stm list * ldest * [ `Var | `Dot | `Deref | `Nth ]
  =
  let size = sizeof_dtype' lvalue.dtype in
  match lvalue.data with
  | `Var var ->
    let var = Map.find_exn env.vars var in
    [], [], Temp var.temp, `Var
  | `Dot dot ->
    let base_stms, base =
      let s' = dot.struct_obj in
      match s'.data with
      | `Deref deref -> trans_exp need_check deref.ptr env
      | `Dot dot' -> trans_dot need_check { data = dot'; dtype = s'.dtype } env
      | `Nth nth ->
        trans_nth need_check ({ data = nth; dtype = s'.dtype } : TST.nth TST.typed) env
      | _ -> failwith "hmmm, should not happen"
    in
    let s = Map.find_exn env.structs (get_struct_exn dot.struct_obj.dtype) in
    let field = Map.find_exn s.fields dot.field in
    let offset = Sexp.wrap `QWORD (Exp.of_int field.offset) in
    check_base_size base;
    let base_check = if need_check then check_null base else [] in
    let addr = Addr.of_bisd base (Some offset) (Some 1L) None in
    let addr_check =
      if need_check then check_null (addr |> Exp.of_bisd |> Sexp.wrap `QWORD) else []
    in
    base_stms @ base_check, addr_check, Mem (addr |> Mem.wrap size), `Dot
  | `Deref deref ->
    let base_stms, base = trans_exp need_check deref.ptr env in
    check_base_size base;
    let check = if need_check then check_null base else [] in
    base_stms, check, Mem (Addr.of_bisd base None None None |> Mem.wrap size), `Deref
  | `Nth nth ->
    let base_stm, base = trans_exp need_check nth.arr env in
    let index_stm, index_exp = trans_exp need_check nth.index env in
    check_base_size base;
    check_index_size index_exp;
    let index = Temp.create () |> Exp.of_t |> Sexp.wrap `QWORD in
    let index_stm =
      index_stm @ [ Tree.Cast { dest = Sexp.to_St index; src = index_exp } ]
    in
    let scale = sizeof_dtype lvalue.dtype env |> Size.type_size_byte in
    let base_check, bound_check = if need_check then check_bound base index else [], [] in
    ( base_stm @ index_stm
    , base_check @ bound_check
    , Mem (Addr.of_bisd base (Some index) (Some scale) None |> Mem.wrap size)
    , `Nth )
  | _ -> failwith "should not appear as lvalue"

and[@warning "-8"] trans_assign_rev acc (TST.Assign asn_tst) need_check (env : env)
    : Tree.stm list
  =
  let size = sizeof_dtype' asn_tst.value.dtype in
  let dest_stms, dest_check, lhs, ltype = trans_lvalue asn_tst.name env need_check in
  let v_stms, rhs = trans_exp need_check asn_tst.value env in
  match lhs with
  | Temp t ->
    let dest = St.wrap size t in
    let src = rhs in
    (Tree.Move { dest; src } :: List.rev v_stms) @ acc
  | Mem dest ->
    let src, cast =
      if Size.compare' dest.size rhs.size <> 0
      then (
        let dest' = Temp.create () in
        ( Exp.of_t dest' |> Sexp.wrap dest.size
        , [ Tree.Cast { dest = St.wrap dest.size dest'; src = rhs } ] ))
      else rhs, []
    in
    (match ltype with
    | `Nth ->
      ((Tree.Store { dest; src } :: cast) @ List.rev v_stms)
      @ List.rev dest_check
      @ List.rev dest_stms
      @ acc
    | `Deref | `Dot ->
      (((Tree.Store { dest; src } :: cast) @ List.rev dest_check) @ List.rev v_stms)
      @ List.rev dest_stms
      @ acc
    | `Var -> failwith "should not happen")

and[@warning "-8"] trans_assignop_rev
    acc
    (TST.Assign asn_tst)
    need_check
    (env : env)
    p_ip
    op
    : Tree.stm list
  =
  let size = sizeof_dtype' asn_tst.value.dtype in
  let dest_stms, dest_check, lhs, _ = trans_lvalue asn_tst.name env need_check in
  let v_stms, rhs = trans_exp need_check asn_tst.value env in
  match lhs with
  | Temp t ->
    let dest = St.wrap size t in
    (match p_ip with
    | `Pure ->
      let src = Sexp.wrap size (Exp.of_binop op (St.to_Sexp dest) rhs) in
      (Tree.Move { dest; src } :: List.rev v_stms) @ acc
    | `Impure ->
      (Tree.Effect { dest; lhs = St.to_Sexp dest; rhs; op } :: List.rev v_stms) @ acc)
  | Mem mem ->
    let src, src_stm =
      match p_ip with
      | `Pure ->
        let dest = St.wrap size (Temp.create ()) in
        let lhs_temp_stms, lhs_temp =
          [ Tree.Load { src = mem; dest } ], St.to_Sexp dest
        in
        Sexp.wrap size (Exp.of_binop op lhs_temp rhs), dest_check @ lhs_temp_stms
      | `Impure ->
        let t = Temp.create () |> Exp.of_t |> Sexp.wrap size |> Sexp.to_St in
        ( St.to_Sexp t
        , dest_check
          @ [ Tree.Load { src = mem; dest = t }
            ; Tree.Effect { dest = t; lhs = St.to_Sexp t; rhs; op }
            ] )
    in
    ((Tree.Store { dest = mem; src } :: List.rev src_stm) @ List.rev v_stms)
    @ List.rev dest_stms
    @ acc

and[@warning "-8"] trans_asnop_rev acc (TST.Assign asn_tst) need_check (env : env)
    : Tree.stm list
  =
  match asn_tst.op with
  | `Asn -> trans_assign_rev acc (TST.Assign asn_tst) need_check env
  | _ ->
    let p_ip, (op : Tree.binop) =
      match asn_tst.op with
      (* Pure, w.o. effect *)
      | `Plus_asn -> `Pure, Plus
      | `Minus_asn -> `Pure, Minus
      | `Times_asn -> `Pure, Times
      | `And_asn -> `Pure, And
      | `Hat_asn -> `Pure, Xor
      | `Or_asn -> `Pure, Or
      (* Impure, probably w. effect *)
      | `Div_asn -> `Impure, Divided_by
      | `Mod_asn -> `Impure, Modulo
      | `Left_shift_asn -> `Impure, Left_shift
      | `Right_shift_asn -> `Impure, Right_shift
    in
    trans_assignop_rev acc (TST.Assign asn_tst) need_check env p_ip op
;;

(* env.vars keep trakcs from variable name to temporary. Two things keep in mind
 * 1) variable name can be the same in different scope (scope has no intersection).
 * So env.vars will update in different context. 
 * 2) env.vars is only a map from variable name to temporary, it doesn't care the 
 * content of temporary. So we only add this linkage in declaration. *)
let rec trans_stm_rev
    (tst : TST.stm)
    (acc : Tree.stm list)
    (env : env)
    (need_check : bool)
    : Tree.stm list * env
  =
  match tst with
  | TST.Assign asn_tst -> trans_asnop_rev acc (TST.Assign asn_tst) need_check env, env
  | TST.If if_TST ->
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
    let cond_stms, cond_exp = trans_exp need_check if_TST.cond env in
    let label_false = Label.label (Some "if_false") in
    let label_true = Label.label (Some "if_true") in
    let label_conv = Label.label (Some "if_conv") in
    let false_stm, _ = trans_stm_rev if_TST.false_stm [] env need_check in
    let true_stm, _ = trans_stm_rev if_TST.true_stm [] env need_check in
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
    , env )
  | TST.While while_TST ->
    (* 
     * Jump label_loop_stop
     * label_loop_start
     * body
     * label_loop_stop
     * cond_side_effect(optional)
     * CJump cond target_true
     * target_false
     * rest blah blah *)
    let cond_stms, cond_exp = trans_exp need_check while_TST.cond env in
    let body, _ = trans_stm_rev while_TST.body [] env need_check in
    let target_true = Label.label (Some "loop_start") in
    let label_loop_stop = Label.label (Some "loop_stop") in
    let target_false = Label.label (Some "loop_dummy") in
    let lhs, op, rhs = gen_cond cond_exp in
    ( [ Tree.Label target_false; Tree.CJump { lhs; op; rhs; target_true; target_false } ]
      @ List.rev cond_stms
      @ [ Tree.Label label_loop_stop ]
      @ body
      @ [ Tree.Label target_true ]
      @ [ Tree.Jump label_loop_stop ]
      @ acc
    , env )
  | TST.Return ret_TST ->
    (match ret_TST with
    | None -> Tree.Return None :: acc, env
    | Some ret_TST ->
      let ret_stms, ret_exp = trans_exp need_check ret_TST env in
      let ret = Tree.Return (Some ret_exp) in
      (ret :: List.rev ret_stms) @ acc, env)
  | TST.Nop -> acc, env
  | TST.Seq seq_TST ->
    let head, _ = trans_stm_rev seq_TST.head [] env need_check in
    let tail, _ = trans_stm_rev seq_TST.tail [] env need_check in
    tail @ head @ acc, env
  | TST.Declare decl_TST ->
    let size = sizeof_dtype' decl_TST.t in
    let temp = Temp.create () |> Exp.of_t |> Sexp.wrap size |> Sexp.to_St in
    let var = { temp = temp.data; dtype = decl_TST.t } in
    let vars' = Map.add_exn env.vars ~key:decl_TST.name ~data:var in
    let env' = { env with vars = vars' } in
    let tail, _ = trans_stm_rev decl_TST.tail [] env' need_check in
    let mov =
      match decl_TST.value with
      | None -> []
      | Some value ->
        let v_stms, v_exp = trans_exp need_check value env in
        [ Tree.Move { dest = temp; src = v_exp } ] @ List.rev v_stms
    in
    tail @ mov @ acc, env
  | TST.Sexp sexp_TST ->
    let sexp_stms, _ = trans_exp need_check sexp_TST env in
    List.rev sexp_stms @ acc, env
  | TST.Assert asrt ->
    let asrt_stms, asrt_exp = trans_exp need_check asrt env in
    let ret = Tree.Assert asrt_exp in
    (ret :: List.rev asrt_stms) @ acc, env
;;

(* return pad for dtype based on current offset.
 * pad + offset is next closest address for aligned dtype *)
let padding (dtype : TST.dtype) (offset : Int64.t) (env : env) : Int64.t =
  let ( % ) = Base.Int64.( % ) in
  let ( - ) = Base.Int64.( - ) in
  let ( > ) = Base.Int64.( > ) in
  let tsize = align dtype env in
  let tsize_64 = Size.type_size_byte tsize in
  if tsize_64 > 0L
  then (
    match offset % tsize_64 with
    | 0L -> 0L
    | m -> tsize_64 - m)
  else 0L
;;

let trans_struct (s : TC.c0_struct) (env : env) : c0_struct =
  let ( + ) = Base.Int64.( + ) in
  let ( > ) = Base.Int64.( > ) in
  let fields, size =
    List.fold s.fields ~init:(Map.empty, 0L) ~f:(fun acc field ->
        let map, offset = acc in
        let fname, dtype = field.name, field.dtype in
        let pad = padding dtype offset env in
        let offset = offset + pad in
        let fsize = sizeof_dtype dtype env in
        let field = { dtype; offset; size = fsize } in
        let fsize_64 = Size.type_size_byte fsize in
        let offset_next = offset + fsize_64 in
        let offset_next =
          if offset_next > Int64.of_int32_exn Int32.max_value then 0L else offset_next
        in
        Map.set map ~key:fname ~data:field, offset_next)
  in
  { fields; size = Size.byte_to_size size }
;;

let trans_structs (env : TC.env) : env =
  let env_init = { funcs = env.funcs; structs = Map.empty; vars = Map.empty } in
  let order =
    Map.to_alist ~key_order:`Increasing env.structs
    |> List.sort ~compare:(fun s1 s2 ->
           let (_, s1), (_, s2) = s1, s2 in
           s1.order - s2.order)
  in
  let tc_structs_tuples =
    List.filter order ~f:(fun s_tuple ->
        let _, s = s_tuple in
        phys_equal s.state TC.Defn)
  in
  List.fold tc_structs_tuples ~init:env_init ~f:(fun acc tuple ->
      let sname, tc_struct = tuple in
      let s' = trans_struct tc_struct acc in
      { acc with structs = Map.set acc.structs ~key:sname ~data:s' })
;;

let trans_fdefn func_name (pars : TST.param list) blk (env : env) (need_check : bool)
    : Tree.fdefn
  =
  let vars =
    List.fold pars ~init:Map.empty ~f:(fun acc par ->
        let temp = Temp.create () in
        let var = { temp; dtype = par.dtype } in
        Map.add_exn acc ~key:par.data ~data:var)
  in
  let env = { env with vars } in
  let blk_rev, env = trans_stm_rev blk [] env need_check in
  let body = List.rev blk_rev in
  let temps : St.t list =
    List.map pars ~f:(fun par ->
        let var = Map.find_exn env.vars par.data in
        let size = sizeof_dtype' var.dtype in
        let var_s = Sexp.wrap size (Exp.of_t var.temp) |> Sexp.to_St in
        var_s)
  in
  { func_name; temps; body; scope = `C0 }
;;

let rec trans_prog
    (program : TST.program)
    (acc : Tree.program)
    (env : env)
    (need_check : bool)
    : Tree.program
  =
  match program with
  | [] ->
    let t = Temp.create () |> Exp.of_t |> Sexp.wrap `DWORD |> Sexp.to_St in
    List.rev acc @ [ c0_raise t ]
  | fdefn :: t ->
    let fdefn_tree = trans_fdefn fdefn.func_name fdefn.pars fdefn.blk env need_check in
    trans_prog t (fdefn_tree :: acc) env need_check
;;

let translate (program : TST.program) (env : TC.env) (unsafe : bool) : Tree.program =
  let env = trans_structs env in
  trans_prog program [] env (not unsafe)
;;
