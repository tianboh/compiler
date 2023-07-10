(* L4 Compiler
 * AST -> IR Translator
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified by: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
open Core
module AST = Front.Ast
module Tree = Inst
module Map = Util.Symbol.Map
module Symbol = Util.Symbol
module Size = Var.Size
module Label = Util.Label
module Mark = Util.Mark
module Temp = Var.Temp
module TC = Semantic.Typechecker

type field =
  { dtype : AST.dtype
  ; offset : Int64.t
  ; size : Size.t
  }

type struct' =
  { fields : field Map.t
  ; size : Size.t
  }

type var =
  { temp : Temp.t
  ; dtype : AST.dtype
  }

type env =
  { funcs : TC.func Map.t
  ; structs : struct' Map.t
  ; vars : var Map.t
  }

(* Used by lvalue to distinguish variable type *)
type ldest =
  | Heap of
      { loc : Tree.mem
      ; dtype : AST.dtype
      }
  | Stack of
      { temp : Temp.t
      ; dtype : AST.dtype
      }

(* Used by expression to distinguish memory and other type *)
type edest =
  | Pure of
      { exp : Tree.exp
      ; dtype : AST.dtype
      }
  | Impure of
      { loc : Tree.mem
      ; dtype : AST.dtype
      }

(* Return the alignment requirement for data type
 * Struct alignment depends on the strictest(largest) field *)
let rec align (dtype : AST.dtype) (env : env) : Size.t =
  match dtype with
  | AST.Int -> `DWORD
  | AST.Bool -> `DWORD
  | AST.Void -> `VOID
  | AST.NULL -> `DWORD
  | AST.Pointer _ -> `QWORD
  | AST.Array _ -> `QWORD
  | AST.Struct sname ->
    let s = Map.find_exn env.structs sname in
    let m = Map.map s.fields ~f:(fun field -> align field.dtype env) in
    let l = Map.data m in
    (match List.max_elt l ~compare:Size.compare with
    | Some s -> s
    | None -> `VOID)
;;

(* Only struct is large type in C0, others are stored on stack
 * Array is only a reference, not real allocated array content *)
let sizeof_dtype (dtype : AST.dtype) (env : env) : Size.t =
  match dtype with
  | AST.Int -> `DWORD
  | AST.Bool -> `DWORD
  | AST.Void -> `VOID
  | AST.NULL -> `DWORD
  | AST.Pointer _ -> `QWORD
  | AST.Array _ -> `QWORD
  | AST.Struct sname ->
    let s = Map.find_exn env.structs sname in
    s.size
;;

let sizeof_dtype' (dtype : AST.dtype) : Size.primitive =
  match dtype with
  | AST.Int -> `DWORD
  | AST.Bool -> `DWORD
  | AST.Void -> `VOID
  | AST.NULL -> `DWORD
  | AST.Pointer _ -> `QWORD
  | AST.Array _ -> `QWORD
  | AST.Struct _ -> failwith "expect small type"
;;

let rec sizeof_exp (exp : Tree.exp) : Size.primitive =
  match exp with
  | Void -> `VOID
  | Const c -> (c.size :> Size.primitive)
  | Temp t -> t.size
  | Binop binop ->
    (match binop.op with
    | Equal_eq | Greater | Greater_eq | Less | Less_eq | Not_eq -> `DWORD
    | Plus
    | Minus
    | Times
    | Divided_by
    | Modulo
    | And
    | Or
    | Xor
    | Right_shift
    | Left_shift -> sizeof_exp binop.lhs)
;;

let sizeof_edest (dest : edest) : Size.t =
  match dest with
  | Pure pure -> (sizeof_exp pure.exp :> Size.t)
  | Impure mem -> mem.loc.size
;;

let sizeof_edest' (dest : edest) : Size.primitive =
  match dest with
  | Pure pure -> sizeof_exp pure.exp
  | Impure mem ->
    (match mem.loc.size with
    | `CBYTE _ -> failwith "expect a primitive size"
    | `VOID -> `VOID
    | `BYTE -> `BYTE
    | `WORD -> `WORD
    | `DWORD -> `DWORD
    | `QWORD -> `QWORD)
;;

(* `Pure is expression that not lead to side-effect
 * `Impure is expression that may lead to side-effect, 
 * like rasing div-zero or other exception
 * `Compare is return boolean value. *)
let trans_binop = function
  | AST.Plus -> `Pure Tree.Plus
  | AST.Minus -> `Pure Tree.Minus
  | AST.Times -> `Pure Tree.Times
  | AST.And -> `Pure Tree.And
  | AST.Or -> `Pure Tree.Or
  | AST.Hat -> `Pure Tree.Xor
  | AST.Right_shift -> `Impure Tree.Right_shift
  | AST.Left_shift -> `Impure Tree.Left_shift
  | AST.Divided_by -> `Impure Tree.Divided_by
  | AST.Modulo -> `Impure Tree.Modulo
  | AST.Equal_eq -> `Compare Tree.Equal_eq
  | AST.Greater -> `Compare Tree.Greater
  | AST.Greater_eq -> `Compare Tree.Greater_eq
  | AST.Less -> `Compare Tree.Less
  | AST.Less_eq -> `Compare Tree.Less_eq
  | AST.Not_eq -> `Compare Tree.Not_eq
;;

let gen_cond (exp : Tree.exp) : Tree.exp * Tree.binop * Tree.exp =
  match exp with
  | Tree.Void -> failwith "void cannot be used as cond"
  | Tree.Const i ->
    ( Tree.Const { v = i.v; size = `DWORD }
    , Tree.Equal_eq
    , Tree.Const { v = Int64.one; size = `DWORD } )
  | Tree.Temp t -> Tree.Temp t, Tree.Equal_eq, Tree.Const { v = Int64.one; size = `DWORD }
  | Tree.Binop binop -> binop.lhs, binop.op, binop.rhs
;;

let rec trans_exp (exp_ast : AST.exp) (env : env) : Tree.stm list * edest =
  match exp_ast with
  (* after type-checking, id must be declared; do not guard lookup *)
  | AST.Var id ->
    let var = Map.find_exn env.vars id in
    [], Pure { exp = Tree.Temp var.temp; dtype = var.dtype }
  | AST.Const_int c ->
    [], Pure { exp = Tree.Const { v = Int64.of_int32 c; size = `DWORD }; dtype = Int }
  | AST.True ->
    [], Pure { exp = Tree.Const { v = Int64.one; size = `DWORD }; dtype = Bool }
  | AST.False ->
    [], Pure { exp = Tree.Const { v = Int64.zero; size = `DWORD }; dtype = Bool }
  | AST.Binop binop -> trans_exp_bin (AST.Binop binop) env
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
  | AST.Terop terop ->
    let cond_stms, cond_exp = trans_mexp' terop.cond env in
    let true_stms, true_exp = trans_mexp' terop.true_exp env in
    let false_stms, false_exp = trans_mexp' terop.false_exp env in
    let size = sizeof_exp true_exp in
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
    seq, Pure { exp = Tree.Temp temp; dtype = Int }
  | AST.Fcall fcall ->
    (* First calculate arguments with potential side effect, then call fcall. *)
    let args_stms_ls, args =
      List.fold_left fcall.args ~init:[] ~f:(fun acc arg ->
          let arg_stms, arg_exp = trans_mexp' arg env in
          (arg_stms, arg_exp) :: acc)
      |> List.rev
      |> List.unzip
    in
    let args_stms = List.concat args_stms_ls in
    let func_name = fcall.func_name in
    let func = Map.find_exn env.funcs func_name in
    let scope = func.scope in
    let size = sizeof_dtype' func.ret_type in
    (match size with
    | `VOID ->
      let call = Tree.Fcall { dest = None; args; func_name; scope } in
      let call_stms = args_stms @ [ call ] in
      call_stms, Pure { exp = Tree.Void; dtype = func.ret_type }
    | _ ->
      let dest = Temp.create size in
      let call = Tree.Fcall { dest = Some dest; args; func_name; scope } in
      let call_stms = args_stms @ [ call ] in
      call_stms, Pure { exp = Tree.Temp dest; dtype = func.ret_type })
  | AST.EDot dot ->
    let stms, edest = trans_mexp dot.struct_obj env in
    let size, base, offset, dtype =
      match edest with
      | Pure exp ->
        (match exp.dtype with
        | Struct sname ->
          let s = Map.find_exn env.structs sname in
          let field = Map.find_exn s.fields dot.field in
          let base = exp.exp in
          let offset = Tree.Const { v = field.offset; size = `QWORD } in
          field.size, base, offset, field.dtype
        | _ -> failwith "dot access expect struct type")
      | Impure mem ->
        (match mem.dtype with
        | Struct sname ->
          let s = Map.find_exn env.structs sname in
          let field = Map.find_exn s.fields dot.field in
          let base = mem.loc.base in
          let lhs = mem.loc.offset in
          let rhs = Tree.Const { v = field.offset; size = `QWORD } in
          let offset = Tree.Binop { lhs; rhs; op = Plus } in
          field.size, base, offset, field.dtype
        | _ -> failwith "dot access expect struct type")
    in
    let mem = ({ base; offset; size } : Tree.mem) in
    stms, Impure { loc = mem; dtype }
  | AST.EDeref deref ->
    let stms, ptr = trans_mexp deref.ptr env in
    (match ptr with
    | Impure _ -> failwith "attempt to dereference large type in C0"
    | Pure pure ->
      (match pure.dtype with
      | Pointer dtype ->
        let base = pure.exp in
        let offset = Tree.Const { v = Int64.zero; size = `QWORD } in
        let size = (sizeof_exp base :> Size.t) in
        let mem = ({ base; offset; size } : Tree.mem) in
        stms, Impure { loc = mem; dtype }
      | _ -> failwith "attemp to dereference a non-pointer type"))
  | AST.ENth nth ->
    let stms, arr = trans_mexp nth.arr env in
    (match arr with
    | Pure _ -> failwith "expect array type"
    | Impure mem ->
      let base = mem.loc.base in
      let etype =
        match mem.dtype with
        | Array e -> e
        | _ -> failwith "expect array type"
      in
      let esize = sizeof_dtype etype env in
      let esize_64 = Size.type_size_byte esize in
      let esize' = Tree.Const { v = esize_64; size = `QWORD } in
      let index_stm, index = trans_mexp' nth.index env in
      let offset = Tree.Binop { lhs = index; rhs = esize'; op = Times } in
      let mem = ({ base; offset; size = esize } : Tree.mem) in
      stms @ index_stm, Impure { loc = mem; dtype = etype })
  | AST.NULL -> [], Pure { exp = Const { v = Int64.zero; size = `QWORD }; dtype = NULL }
  | AST.Alloc alloc ->
    let size_t = sizeof_dtype alloc.t env in
    let size_64 = Size.type_size_byte size_t in
    let size_32 = Tree.Const { v = size_64; size = `DWORD } in
    let nitems = Tree.Const { v = Int64.one; size = `DWORD } in
    let ptr = Temp.create `QWORD in
    let func_name = Symbol.Function.calloc () in
    let args = [ nitems; size_32 ] in
    ( [ Fcall { dest = Some ptr; func_name; args; scope = `External } ]
    , Pure { exp = Tree.Temp ptr; dtype = Pointer alloc.t } )
  | AST.Alloc_arr alloc_arr ->
    let size_t = sizeof_dtype alloc_arr.t env in
    let size_64 = Size.type_size_byte size_t in
    let size_32 = Tree.Const { v = size_64; size = `DWORD } in
    let stms, nitems = trans_mexp alloc_arr.e env in
    let func_name = Symbol.Function.calloc () in
    let ptr = Temp.create `QWORD in
    (match nitems with
    | Pure pure ->
      let args = [ pure.exp; size_32 ] in
      ( stms @ [ Fcall { dest = Some ptr; func_name; args; scope = `External } ]
      , Pure { exp = Tree.Temp ptr; dtype = Array alloc_arr.t } )
    | Impure mem ->
      let nitems = Temp.create `DWORD in
      let load = Tree.Load { src = mem.loc; dest = nitems } in
      let args = [ Tree.Temp nitems; size_32 ] in
      ( stms @ [ load; Fcall { dest = Some ptr; func_name; args; scope = `External } ]
      , Pure { exp = Tree.Temp ptr; dtype = Array alloc_arr.t } ))

and trans_mexp mexp env : Tree.stm list * edest = trans_exp (Mark.data mexp) env

(* Return statement lists that include effect(can be empty), 
 * and the pure exp without side-effect *)
and trans_mexp' mexp env : Tree.stm list * Tree.exp =
  let stms, edest = trans_mexp mexp env in
  match edest with
  | Pure pure -> stms, pure.exp
  | Impure mem ->
    let size = sizeof_edest' edest in
    let t = Temp.create size in
    let load = Tree.Load { src = mem.loc; dest = t } in
    stms @ [ load ], Tree.Temp t

and[@warning "-8"] trans_exp_bin (AST.Binop binop) (env : env) : Tree.stm list * edest =
  let lhs_stm, lhs_exp = trans_mexp' binop.lhs env in
  let rhs_stm, rhs_exp = trans_mexp' binop.rhs env in
  let size = sizeof_exp lhs_exp in
  match trans_binop binop.op with
  | `Pure op ->
    ( lhs_stm @ rhs_stm
    , Pure { exp = Tree.Binop { op; lhs = lhs_exp; rhs = rhs_exp }; dtype = Int } )
  | `Impure op ->
    let dest = Temp.create size in
    ( lhs_stm @ rhs_stm @ [ Tree.Effect { dest; lhs = lhs_exp; op; rhs = rhs_exp } ]
    , Pure { exp = Tree.Temp dest; dtype = Int } )
  | `Compare op ->
    ( lhs_stm @ rhs_stm
    , Pure { exp = Tree.Binop { op; lhs = lhs_exp; rhs = rhs_exp }; dtype = Bool } )
;;

let rec trans_lvalue (lvalue : AST.lvalue) (stms : Tree.stm list) (env : env)
    : Tree.stm list * ldest
  =
  match lvalue with
  | Ident var ->
    let v = Map.find_exn env.vars var in
    let dtype = v.dtype in
    (match v.dtype with
    | Int | Bool | Void | NULL | Pointer _ -> stms, Stack { temp = v.temp; dtype }
    | Array _ | Struct _ ->
      let base = Tree.Temp v.temp in
      let offset = Tree.Const { v = Int64.zero; size = `DWORD } in
      let size = (v.temp.size :> Size.t) in
      stms, Heap { loc = { base; offset; size }; dtype })
  | LVDot dot ->
    let stms, lv = trans_lvalue (Mark.data dot.struct_obj) stms env in
    (match lv with
    | Stack _ -> failwith "struct should stored on heap, not stack."
    | Heap heap ->
      (match heap.dtype with
      | Struct sname ->
        let s = Map.find_exn env.structs sname in
        let field = Map.find_exn s.fields dot.field in
        let base = heap.loc.base in
        let lhs = heap.loc.offset in
        let rhs = Tree.Const { v = field.offset; size = `QWORD } in
        let offset = Tree.Binop { lhs; op = Tree.Plus; rhs } in
        let dtype = field.dtype in
        stms, Heap { loc = { base; offset; size = field.size }; dtype }
      | _ -> failwith "expect struct for dot access"))
  | LVDeref deref ->
    let stms, lv = trans_lvalue (Mark.data deref.ptr) stms env in
    (match lv with
    | Stack var ->
      (match var.dtype with
      | Pointer ptr ->
        let base = Tree.Temp var.temp in
        let offset = Tree.Const { v = Int64.zero; size = `QWORD } in
        let size = (var.temp.size :> Size.t) in
        stms, Heap { loc = { base; offset; size }; dtype = ptr }
      | _ -> failwith "expect dereference a pointer")
    | Heap _ -> failwith "cannot dereference array/struct in C0")
  | LVNth nth ->
    let stms, lv = trans_lvalue (Mark.data nth.arr) stms env in
    (match lv with
    | Stack _ -> failwith "array access expect to work on heap"
    | Heap mem ->
      let stms', index = trans_mexp' nth.index env in
      let base = mem.loc.base in
      let etype =
        match mem.dtype with
        | Array etype -> etype
        | _ -> failwith "expect array type"
      in
      let size = sizeof_dtype etype env in
      let offset =
        Tree.Binop
          { lhs = index
          ; op = Times
          ; rhs = Tree.Const { v = Size.type_size_byte size; size = `QWORD }
          }
      in
      stms @ stms', Heap { loc = { base; offset; size }; dtype = etype })
;;

let trans_asnop (lhs : ldest) (op : AST.asnop) (rhs : Tree.exp) : Tree.stm list * Tree.exp
  =
  let stm, lhs =
    match lhs with
    | Stack var -> [], Tree.Temp var.temp
    | Heap mem ->
      let t = Temp.create (sizeof_edest' (Impure { loc = mem.loc; dtype = mem.dtype })) in
      let stm = [ Tree.Load { src = mem.loc; dest = t } ] in
      stm, Tree.Temp t
  in
  match op with
  | Asn -> stm, rhs
  | Plus_asn -> stm, Tree.Binop { lhs; rhs; op = Plus }
  | Minus_asn -> stm, Tree.Binop { lhs; rhs; op = Minus }
  | Times_asn -> stm, Tree.Binop { lhs; rhs; op = Times }
  | Div_asn -> stm, Tree.Binop { lhs; rhs; op = Divided_by }
  | Mod_asn -> stm, Tree.Binop { lhs; rhs; op = Modulo }
  | And_asn -> stm, Tree.Binop { lhs; rhs; op = And }
  | Hat_asn -> stm, Tree.Binop { lhs; rhs; op = Xor }
  | Or_asn -> stm, Tree.Binop { lhs; rhs; op = Or }
  | Left_shift_asn -> stm, Tree.Binop { lhs; rhs; op = Left_shift }
  | Right_shift_asn -> stm, Tree.Binop { lhs; rhs; op = Right_shift }
;;

(* env.vars keep trakcs from variable name to temporary. Two things keep in mind
 * 1) variable name can be the same in different scope (scope has no intersection).
 * So env.vars will update in different context. 
 * 2) env.vars is only a map from variable name to temporary, it doesn't care the 
 * content of temporary. So we only add this linkage in declaration. *)
let rec trans_stm_rev (ast : AST.mstm) (acc : Tree.stm list) (env : env)
    : Tree.stm list * env
  =
  match Mark.data ast with
  | AST.Assign asn_ast ->
    let dest_stms, dest = trans_lvalue (Mark.data asn_ast.name) [] env in
    let v_stms, v_exp = trans_mexp' asn_ast.value env in
    let elab_stm, exp = trans_asnop dest asn_ast.op v_exp in
    (match dest with
    | Stack var ->
      (Tree.Move { dest = var.temp; src = exp } :: List.rev v_stms) @ acc, env
    | Heap mem ->
      ( ((Tree.Store { dest = mem.loc; src = exp } :: elab_stm) @ List.rev v_stms)
        @ List.rev dest_stms
        @ acc
      , env ))
  | AST.If if_ast ->
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
    let cond_stms, cond_exp = trans_mexp' if_ast.cond env in
    let label_false = Label.label (Some "if_false") in
    let label_true = Label.label (Some "if_true") in
    let label_conv = Label.label (Some "if_conv") in
    let false_stm, _ = trans_stm_rev if_ast.false_stm [] env in
    let true_stm, _ = trans_stm_rev if_ast.true_stm [] env in
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
  | AST.While while_ast ->
    (* 
     * Jump label_loop_stop
     * label_loop_start
     * body
     * label_loop_stop
     * cond_side_effect(optional)
     * CJump cond target_true
     * target_false
     * rest blah blah *)
    let cond_stms, cond_exp = trans_mexp' while_ast.cond env in
    let body, _ = trans_stm_rev while_ast.body [] env in
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
  | AST.Return ret_ast ->
    (match ret_ast with
    | None -> Tree.Return None :: acc, env
    | Some ret_ast ->
      let ret_stms, ret_exp = trans_mexp' ret_ast env in
      let ret = Tree.Return (Some ret_exp) in
      (ret :: List.rev ret_stms) @ acc, env)
  | AST.Nop -> acc, env
  | AST.Seq seq_ast ->
    let head, _ = trans_stm_rev seq_ast.head [] env in
    let tail, _ = trans_stm_rev seq_ast.tail [] env in
    tail @ head @ acc, env
  | AST.Declare decl_ast ->
    let temp = Temp.create (sizeof_dtype' decl_ast.t) in
    let var = { temp; dtype = decl_ast.t } in
    let vars' = Map.add_exn env.vars ~key:decl_ast.name ~data:var in
    let env' = { env with vars = vars' } in
    let tail, _ = trans_stm_rev decl_ast.tail [] env' in
    let mov =
      match decl_ast.value with
      | None -> []
      | Some value ->
        let v_stms, v_exp = trans_mexp' value env in
        [ Tree.Move { dest = temp; src = v_exp } ] @ List.rev v_stms
    in
    tail @ mov @ acc, env
  | AST.Sexp sexp_ast ->
    let sexp_stms, _ = trans_mexp' sexp_ast env in
    List.rev sexp_stms @ acc, env
  | AST.Assert asrt ->
    let asrt_stms, asrt_exp = trans_mexp' asrt env in
    let ret = Tree.Assert asrt_exp in
    (ret :: List.rev asrt_stms) @ acc, env
;;

(* return pad for dtype based on current offset.
 * pad + offset is next closest address for aligned dtype *)
let padding (dtype : AST.dtype) (offset : Int64.t) (env : env) : Int64.t =
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

let trans_struct (s : TC.struct') (env : env) : struct' =
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

let trans_fdefn func_name (pars : AST.param list) blk (env : env) : Tree.fdefn =
  let vars =
    List.fold pars ~init:Map.empty ~f:(fun acc par ->
        let temp = Temp.create (sizeof_dtype' par.t) in
        let var = { temp; dtype = par.t } in
        Map.add_exn acc ~key:par.i ~data:var)
  in
  let env = { env with vars } in
  let blk_rev, env = trans_stm_rev blk [] env in
  let body = List.rev blk_rev in
  let temps =
    List.map pars ~f:(fun par ->
        let var = Map.find_exn env.vars par.i in
        var.temp)
  in
  { func_name; temps; body }
;;

let rec trans_prog (program : AST.program) (acc : Tree.program) (env : env) : Tree.program
  =
  match program with
  | [] -> List.rev acc
  | h :: t ->
    (match h with
    | AST.Fdefn fdefn ->
      let fdefn_tree = trans_fdefn fdefn.func_name fdefn.pars fdefn.blk env in
      trans_prog t (fdefn_tree :: acc) env
    | AST.Typedef _ | AST.Fdecl _ | AST.Sdecl _ | AST.Sdefn _ -> trans_prog t acc env)
;;

let translate (program : AST.program) (env : TC.env) : Tree.program =
  let env = trans_structs env in
  trans_prog program [] env
;;
