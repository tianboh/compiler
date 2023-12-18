(* L4 Compiler
 * TST -> IR Translator
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
  | Mem of Tree.mem
  | Temp of Temp.t

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
    let s = Map.find_exn env.structs sname in
    let m = Map.map s.fields ~f:(fun field -> align field.dtype env) in
    let l = Map.data m in
    (match List.max_elt l ~compare:Size.compare with
    | Some s -> s
    | None -> `VOID)
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

let wrap_exp ?(size = `DWORD) (exp : Tree.exp) : Tree.sexp =
  match exp with
  | Temp temp -> { data = exp; size = temp.size }
  | Const imm -> { data = Tree.Const imm; size = (imm.size :> Size.primitive) }
  | _ -> { data = exp; size }
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

let gen_cond (exp : Tree.sexp) : Tree.sexp * Tree.binop * Tree.sexp =
  (* boolean var is dword in IR *)
  let size = `DWORD in
  match exp.data with
  | Tree.Void -> failwith "void cannot be used as cond"
  | Tree.Const i ->
    ( wrap_exp (Tree.Const { v = i.v; size })
    , Tree.Equal_eq
    , wrap_exp (Tree.Const { v = Int64.one; size }) )
  | Tree.Temp t ->
    wrap_exp (Tree.Temp t), Tree.Equal_eq, wrap_exp (Tree.Const { v = Int64.one; size })
  | Tree.Binop binop -> binop.lhs, binop.op, binop.rhs
;;

let c0_raise (temp : Temp.t) : Tree.fdefn =
  let body =
    [ Tree.Fcall
        { dest = None
        ; func_name = Symbol.Fname.raise
        ; args = [ wrap_exp (Tree.Temp temp) ]
        ; scope = `External
        }
    ]
  in
  { func_name = Symbol.Fname.raise; temps = [ temp ]; body; scope = `Internal }
;;

(* Check whether base is 0 *)
let check_null (base : Tree.sexp) : Tree.stm list =
  let lhs, op, rhs =
    base, Tree.Equal_eq, wrap_exp (Tree.Const { v = 0L; size = `QWORD })
  in
  let target_true = Label.label (Some "is_null") in
  let target_false = Label.label (Some "not_null") in
  [ Tree.CJump { lhs; op; rhs; target_true; target_false }
  ; Tree.Label target_true
  ; Tree.Fcall
      { dest = None
      ; func_name = Symbol.Fname.raise
      ; args = [ wrap_exp (Tree.Const { v = Symbol.Fname.usr2; size = `DWORD }) ]
      ; scope = `Internal
      }
  ; Tree.Label target_false
  ]
;;

(* Check whether offset is within [0, array_size), also check whether array base is null. *)
let check_bound (base : Tree.sexp) (offset : Tree.sexp) : Tree.stm list * Tree.stm list =
  let size = `QWORD in
  let temp = Temp.create size in
  let offset_8 = wrap_exp (Tree.Temp temp) in
  let zero = wrap_exp (Tree.Const { v = 0L; size }) in
  let null_check = check_null base in
  let arr_header_addr = ({ disp = -8L; base; offset = None; size } : Tree.mem) in
  let arr_size = Temp.create size in
  let load = [ Tree.Load { src = arr_header_addr; dest = arr_size } ] in
  let target_raise = Label.label (Some "fail_bd_check") in
  let target1 = Label.label (Some "pass_lo_check") in
  let target2 = Label.label (Some "pass_hi_check") in
  let check =
    [ Tree.Move { dest = temp; src = offset }
    ; Tree.CJump
        { lhs = offset_8
        ; op = Tree.Greater_eq
        ; rhs = zero
        ; target_false = target_raise
        ; target_true = target1
        }
    ; Tree.Label target1
    ; Tree.CJump
        { lhs = offset_8
        ; op = Tree.Less
        ; rhs = wrap_exp (Tree.Temp arr_size)
        ; target_false = target_raise
        ; target_true = target2
        }
    ; Tree.Label target_raise
    ; Tree.Fcall
        { dest = None
        ; func_name = Symbol.Fname.raise
        ; args = [ wrap_exp (Tree.Const { v = Symbol.Fname.usr2; size }) ]
        ; scope = `Internal
        }
    ; Tree.Label target2
    ]
  in
  null_check, load @ check
;;

let trans_exp_bin (binop : TST.binexp) (env : env) trans_func : Tree.stm list * Tree.sexp =
  let lhs_stm, lhs = trans_func binop.lhs env in
  let rhs_stm, rhs = trans_func binop.rhs env in
  let size = sizeof_dtype' binop.lhs.dtype in
  match trans_binop binop.op with
  | `Pure op -> lhs_stm @ rhs_stm, wrap_exp ~size (Tree.Binop { op; lhs; rhs })
  | `Impure op ->
    let dest = Temp.create size in
    lhs_stm @ rhs_stm @ [ Tree.Effect { dest; lhs; op; rhs } ], wrap_exp (Tree.Temp dest)
  | `Compare op -> lhs_stm @ rhs_stm, wrap_exp ~size (Tree.Binop { op; lhs; rhs })
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
  let temp = Temp.create size in
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
    @ [ Tree.Move { dest = temp; src = true_exp }; Tree.Jump label_ter_end ]
    @ false_stms
    @ [ Tree.Move { dest = temp; src = false_exp }; Tree.Label label_ter_end ]
  in
  seq, wrap_exp (Tree.Temp temp)
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
    call_stms, wrap_exp ~size:`VOID Tree.Void
  | _ ->
    let dest = Temp.create size in
    let call = Tree.Fcall { dest = Some dest; args; func_name; scope } in
    let call_stms = args_stms @ [ call ] in
    call_stms, wrap_exp (Tree.Temp dest)
;;

let trans_alloc (alloc : TST.alloc) env =
  let size = `DWORD in
  let size_64 = sizeof_dtype alloc.dtype env |> Size.type_size_byte in
  let size_32 = wrap_exp (Tree.Const { v = size_64; size }) in
  let nitems = wrap_exp (Tree.Const { v = Int64.one; size }) in
  let ptr = Temp.create `QWORD in
  let func_name = Symbol.Fname.calloc in
  let args = [ nitems; size_32 ] in
  ( [ Tree.Fcall { dest = Some ptr; func_name; args; scope = `External } ]
  , wrap_exp (Tree.Temp ptr) )
;;

let trans_alloc_arr (alloc_arr : TST.alloc_arr) env trans_func =
  (* C0 array has 8 byte header to store the array length. 
   * To access it, use base + disp. Base is the start addr for array. *)
  let size = `DWORD in
  let size_64 = sizeof_dtype alloc_arr.etype env |> Size.type_size_byte in
  let size_32 = wrap_exp (Tree.Const { v = size_64; size }) in
  let stms, nitems = trans_func alloc_arr.nitems env in
  let func_name = Symbol.Fname.calloc in
  let ptr_disp, ptr_base = Temp.create `QWORD, Temp.create `QWORD in
  let size_times =
    wrap_exp ~size (Tree.Binop { lhs = nitems; rhs = size_32; op = Times })
  in
  let size_header = wrap_exp (Tree.Const { v = 8L; size }) in
  (* size for array = nitems * esize + 8 *)
  let size_tot = Tree.Binop { lhs = size_times; rhs = size_header; op = Plus } in
  let args = [ wrap_exp (Tree.Const { v = 1L; size }); wrap_exp ~size size_tot ] in
  let alloc = Tree.Fcall { dest = Some ptr_disp; func_name; args; scope = `External } in
  let base = wrap_exp (Tree.Temp ptr_disp) in
  let header = ({ base; offset = None; disp = 0L; size = `QWORD } : Tree.mem) in
  let store_size = Tree.Store { dest = header; src = size_times } in
  let size_header = wrap_exp (Tree.Const { v = 8L; size = `QWORD }) in
  let base_addr =
    wrap_exp ~size:`QWORD (Tree.Binop { lhs = base; rhs = size_header; op = Plus })
  in
  let move = Tree.Move { dest = ptr_base; src = base_addr } in
  stms @ [ alloc; store_size; move ], wrap_exp (Tree.Temp ptr_base)
;;

let trans_mem (base : Tree.sexp) (offset : Tree.sexp option) (size : Size.primitive)
    : Tree.stm list * Tree.sexp
  =
  let src = ({ disp = 0L; base; offset; size } : Tree.mem) in
  let dest = Temp.create size in
  let load = Tree.Load { src; dest } in
  [ load ], wrap_exp (Tree.Temp dest)
;;

(* Return small value, or memory calculation formula *)
let[@warning "-8"] rec trans_exp (need_check : bool) (exp_tst : TST.texp) (env : env)
    : Tree.stm list * Tree.sexp
  =
  let size = sizeof_dtype' exp_tst.dtype in
  match exp_tst.data with
  | `Dot dot ->
    trans_dot need_check ({ data = dot; dtype = exp_tst.dtype } : TST.dot TST.typed) env
  | `Nth nth ->
    trans_nth need_check ({ data = nth; dtype = exp_tst.dtype } : TST.nth TST.typed) env
  | `Deref deref ->
    let base_stm, base = trans_exp need_check deref.ptr env in
    let load, dest = trans_mem base None size in
    let check = if need_check then check_null base else [] in
    base_stm @ check @ load, dest
  | `Binop binop -> trans_exp_bin binop env (trans_exp need_check)
  | `Terop terop -> trans_terop terop env (trans_exp need_check)
  | `Fcall fcall -> trans_fcall fcall env (trans_exp need_check)
  | `Alloc alloc -> trans_alloc alloc env
  | `Alloc_arr alloc_arr -> trans_alloc_arr alloc_arr env (trans_exp need_check)
  | `Var id ->
    let var = Map.find_exn env.vars id in
    [], wrap_exp (Tree.Temp var.temp)
  | `Const_int c -> [], wrap_exp (Tree.Const { v = Int64.of_int32 c; size = `DWORD })
  | `True -> [], wrap_exp (Tree.Const { v = Int64.one; size = `DWORD })
  | `False -> [], wrap_exp (Tree.Const { v = Int64.zero; size = `DWORD })
  | `NULL -> [], wrap_exp (Const { v = Int64.zero; size = `QWORD })

and trans_nth need_check (nth : TST.nth TST.typed) env : Tree.stm list * Tree.sexp =
  let size = sizeof_dtype' nth.dtype in
  let base_stm, base = trans_exp need_check nth.data.arr env in
  let index_stm, index_exp = trans_exp need_check nth.data.index env in
  let scale = size |> Size.type_size_byte in
  let lhs = wrap_exp (Tree.Const { v = scale; size = `DWORD }) in
  let offset = wrap_exp (Tree.Binop { lhs; rhs = index_exp; op = Times }) in
  if is_large nth.dtype
  then
    base_stm, { data = Tree.Binop { lhs = base; rhs = offset; op = Plus }; size = `QWORD }
  else (
    let load, dest = trans_mem base (Some offset) size in
    let base_check, bound_check =
      if need_check then check_bound base offset else [], []
    in
    base_stm @ base_check @ index_stm @ bound_check @ load, dest)

and trans_dot need_check (dot : TST.dot TST.typed) env : Tree.stm list * Tree.sexp =
  let size = sizeof_dtype' dot.dtype in
  let s = Map.find_exn env.structs (get_struct_exn dot.data.struct_obj.dtype) in
  let field = Map.find_exn s.fields dot.data.field in
  let offset = wrap_exp (Tree.Const { v = field.offset; size = `QWORD }) in
  let base_stm, base =
    let s' = dot.data.struct_obj in
    match s'.data with
    | `Deref deref -> trans_exp need_check deref.ptr env
    | `Dot dot' -> trans_dot need_check { data = dot'; dtype = s'.dtype } env
    | `Nth nth ->
      trans_nth need_check ({ data = nth; dtype = s'.dtype } : TST.nth TST.typed) env
    | _ -> failwith "hmmm, should not happen"
  in
  if is_large dot.dtype
  then
    base_stm, { data = Tree.Binop { lhs = base; rhs = offset; op = Plus }; size = `QWORD }
  else (
    let load, dest = trans_mem base (Some offset) size in
    let check = if need_check then check_null base else [] in
    base_stm @ check @ load, dest)
;;

let trans_lvalue (lvalue : TST.texp) (env : env) (need_check : bool)
    : Tree.stm list * ldest
  =
  match lvalue.data with
  | `Var var ->
    let var = Map.find_exn env.vars var in
    [], Temp var.temp
  | `Dot _ | `Deref _ | `Nth _ ->
    let stms, _ = trans_exp need_check lvalue env in
    (match List.last_exn stms with
    | Tree.Load load -> stms, Mem load.src
    | _ -> failwith "need load!")
  | _ -> failwith "should not appear as lvalue"
;;

let[@warning "-8"] trans_asnop acc (TST.Assign asn_tst) need_check (env : env)
    : Tree.stm list * env
  =
  let size = sizeof_dtype' asn_tst.value.dtype in
  let dest_stms, lhs = trans_lvalue asn_tst.name env need_check in
  let v_stms, rhs = trans_exp need_check asn_tst.value env in
  let load_stm, lhs_temp =
    match lhs with
    | Temp var -> [], wrap_exp (Tree.Temp var)
    | Mem mem ->
      let t = Temp.create size in
      let stm = [ Tree.Load { src = mem; dest = t } ] in
      stm, wrap_exp (Tree.Temp t)
  in
  let exp =
    match asn_tst.op with
    (* Pure, w.o. effect *)
    | `Asn -> `Pure rhs.data
    | `Plus_asn -> `Pure (Tree.Binop { lhs = lhs_temp; rhs; op = Plus })
    | `Minus_asn -> `Pure (Tree.Binop { lhs = lhs_temp; rhs; op = Minus })
    | `Times_asn -> `Pure (Tree.Binop { lhs = lhs_temp; rhs; op = Times })
    | `And_asn -> `Pure (Tree.Binop { lhs = lhs_temp; rhs; op = And })
    | `Hat_asn -> `Pure (Tree.Binop { lhs = lhs_temp; rhs; op = Xor })
    | `Or_asn -> `Pure (Tree.Binop { lhs = lhs_temp; rhs; op = Or })
    (* Impure, probably w. effect *)
    | `Div_asn -> `Impure (Tree.Binop { lhs = lhs_temp; rhs; op = Divided_by })
    | `Mod_asn -> `Impure (Tree.Binop { lhs = lhs_temp; rhs; op = Modulo })
    | `Left_shift_asn -> `Impure (Tree.Binop { lhs = lhs_temp; rhs; op = Left_shift })
    | `Right_shift_asn -> `Impure (Tree.Binop { lhs = lhs_temp; rhs; op = Right_shift })
  in
  match lhs with
  | Temp dest ->
    (match exp with
    | `Pure p_exp ->
      (Tree.Move { dest; src = wrap_exp ~size p_exp } :: List.rev v_stms) @ acc, env
    | `Impure (Tree.Binop ip_exp) ->
      ( (Tree.Effect
           { dest; lhs = wrap_exp (Tree.Temp dest); rhs = ip_exp.rhs; op = ip_exp.op }
        :: List.rev v_stms)
        @ acc
      , env ))
  | Mem dest ->
    let src, src_stm =
      match exp with
      | `Pure p_exp -> p_exp, []
      | `Impure (Tree.Binop ip_exp) ->
        let t = Temp.create size in
        ( Tree.Temp t
        , [ Tree.Effect
              { dest = t; lhs = wrap_exp (Tree.Temp t); rhs = ip_exp.rhs; op = ip_exp.op }
          ] )
    in
    ( (((Tree.Store { dest; src = wrap_exp ~size src } :: src_stm) @ load_stm)
      @ List.rev v_stms)
      @ List.rev dest_stms
      @ acc
    , env )
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
  | TST.Assign asn_tst -> trans_asnop acc (TST.Assign asn_tst) need_check env
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
    let temp = Temp.create (sizeof_dtype' decl_TST.t) in
    let var = { temp; dtype = decl_TST.t } in
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
        let temp = Temp.create (sizeof_dtype' par.dtype) in
        let var = { temp; dtype = par.dtype } in
        Map.add_exn acc ~key:par.data ~data:var)
  in
  let env = { env with vars } in
  let blk_rev, env = trans_stm_rev blk [] env need_check in
  let body = List.rev blk_rev in
  let temps =
    List.map pars ~f:(fun par ->
        let var = Map.find_exn env.vars par.data in
        var.temp)
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
  | [] -> List.rev acc @ [ c0_raise (Temp.create `DWORD) ]
  | fdefn :: t ->
    let fdefn_tree = trans_fdefn fdefn.func_name fdefn.pars fdefn.blk env need_check in
    trans_prog t (fdefn_tree :: acc) env need_check
;;

let translate (program : TST.program) (env : TC.env) (need_check : bool) : Tree.program =
  let env = trans_structs env in
  trans_prog program [] env need_check
;;
