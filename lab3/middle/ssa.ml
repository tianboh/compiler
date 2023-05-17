(* 
 * SSA will read an IR tree and generate a SSA formed IR tree
 * Here, I use minimal SSA through dominance frontier to make
 * sure that phi function is inserted in a minimal time.
 *
 * Author: Tianbo Hao<tianboh@alumni.cmu.edu>
 *)
open Core
module T = Tree
module D = Dominator
module Temp = Var.Temp

(* dest = phi(src1, ..., srcn) 
 * src is a hashmap from predecessor k to its subscript.
 * key: predecessor block number k, value: current subscript for k *)
type phi =
  { dest : Temp.t
  ; src : Temp.t option Int.Map.t
  }

(* SSA block extends phi list based on dominator block *)
type ssa_block =
  { phis : phi list
  ; body : T.stm list
  ; no : int
  ; succ : Int.Set.t
  }

(* environment for rename.
 * For each temporary, track its most recent index.
 * Also, store the stack of temporaries during parsing the D-tree. *)
type env =
  { index : Temp.t Temp.Map.t
  ; stack : Temp.t List.t Temp.Map.t
  }

(* Store generated temp -> original temp *)
let backtracker = ref Temp.Map.empty

let build_ssa_block (blk_map : D.block Int.Map.t) : ssa_block Int.Map.t =
  Int.Map.map blk_map ~f:(fun blk ->
      { phis = []; body = blk.body; no = blk.no; succ = blk.succ })
;;

let rec get_blk_defsite blk_no (stms : T.stm list) defsites =
  match stms with
  | [] -> defsites
  | stm :: t ->
    (match stm with
    | T.Move move ->
      let dest = move.dest in
      let sites =
        match Temp.Map.find defsites dest with
        | None -> Int.Set.empty
        | Some s -> s
      in
      let sites = Int.Set.add sites blk_no in
      let defsites = Temp.Map.set defsites ~key:dest ~data:sites in
      get_blk_defsite blk_no t defsites
    | T.Return _ | T.Jump _ | T.CJump _ | T.Label _ | T.Nop | T.NExp _ ->
      get_blk_defsite blk_no t defsites)
;;

let rec _get_defsites blks defsites =
  match blks with
  | [] -> defsites
  | blk :: t ->
    let defsites = get_blk_defsite blk.no blk.body defsites in
    _get_defsites t defsites
;;

(* hashmap from Temp -> Int.Set
 * key: temp, value: blk number set that defines this temp *)
let get_defsites blk_map =
  let blks = Int.Map.data blk_map in
  let defsites = Temp.Map.empty in
  _get_defsites blks defsites
;;

(* insert phi(temp) at dominance frontier df_list of a blk
 * return updated acc_blk_map after insertion.
 * Also return updated def_list if this node didn't
 * define temp before. *)
let rec insert_df (temp : Temp.t) df_map df_list acc_blk_map acc_new_def_site pred_map blk
    : ssa_block Int.Map.t * int list
  =
  match df_list with
  | [] -> acc_blk_map, acc_new_def_site
  | h :: t ->
    let blk_df = Int.Map.find_exn acc_blk_map h in
    let phis_dest = List.map blk_df.phis ~f:(fun phi -> phi.dest) in
    if List.mem phis_dest temp ~equal:phys_equal
    then insert_df temp df_map t acc_blk_map acc_new_def_site pred_map blk
    else (
      let dest = temp in
      let preds = Int.Map.find_exn pred_map blk_df.no in
      let src =
        Int.Set.fold preds ~init:Int.Map.empty ~f:(fun acc pred ->
            Int.Map.set acc ~key:pred ~data:None)
      in
      let new_phi = { src; dest } in
      let blk_df = { blk_df with phis = new_phi :: blk_df.phis } in
      let acc_blk_map = Int.Map.set acc_blk_map ~key:blk_df.no ~data:blk_df in
      let acc_new_def_site = blk_df.no :: acc_new_def_site in
      insert_df temp df_map t acc_blk_map acc_new_def_site pred_map blk)
;;

(* insert phi for temp whose defsites is def_list *)
let rec insert_temp (temp : Temp.t) (def_list : int list) df_map acc_blk_map pred_map
    : ssa_block Int.Map.t
  =
  match def_list with
  | [] -> acc_blk_map
  | h :: t ->
    let blk = Int.Map.find_exn acc_blk_map h in
    let df_list = Int.Set.to_list (Int.Map.find_exn df_map blk.no) in
    let acc_blk_map, new_def_list_of_blk =
      insert_df temp df_map df_list acc_blk_map [] pred_map blk
    in
    let new_t = t @ new_def_list_of_blk in
    insert_temp temp new_t df_map acc_blk_map pred_map
;;

(* insert phi function to each dominance frontier *)
let insert blk_map defsites df pred_map =
  Temp.Map.fold defsites ~init:blk_map ~f:(fun ~key:temp ~data:defs acc_blk_map ->
      let defs_l = Int.Set.to_list defs in
      insert_temp temp defs_l df acc_blk_map pred_map)
;;

let rec rename_exp (exp : T.exp) (env : env) : T.exp =
  match exp with
  | Const c -> Const c
  | Temp temp ->
    Temp
      (match Temp.Map.find env.index temp with
      | None -> temp
      | Some s -> s)
  | Binop binop ->
    let lhs_new = rename_exp binop.lhs env in
    let rhs_new = rename_exp binop.rhs env in
    Binop { binop with lhs = lhs_new; rhs = rhs_new }
  (* Sexp generated when transing AST.Terop. *)
  | Sexp sexp ->
    let stm_new_rev =
      List.fold sexp.stm ~init:[] ~f:(fun acc_rec stm ->
          let stm_new = rename_use stm env in
          stm_new :: acc_rec)
    in
    let stm_new = List.rev stm_new_rev in
    let exp_new = rename_exp sexp.exp env in
    Sexp { stm = stm_new; exp = exp_new }

and rename_use (stm : T.stm) env : T.stm =
  match stm with
  | Move move ->
    let src_new = rename_exp move.src env in
    Move { move with src = src_new }
  | Return ret ->
    let ret_new = rename_exp ret env in
    Return ret_new
  | Jump jp -> Jump jp
  | CJump cjp ->
    let lhs_new = rename_exp cjp.lhs env in
    let rhs_new = rename_exp cjp.rhs env in
    CJump { cjp with lhs = lhs_new; rhs = rhs_new }
  | Label l -> Label l
  | Nop -> Nop
  | NExp nexp ->
    let nexp_new = rename_exp nexp env in
    NExp nexp_new

and rename_def (stm : T.stm) (env : env) : T.stm * env =
  match stm with
  | Move move ->
    let dest_new = Temp.create () in
    backtracker := Temp.Map.set !backtracker ~key:dest_new ~data:move.dest;
    let index = Temp.Map.set env.index ~key:move.dest ~data:dest_new in
    let stack_temp = Temp.Map.find_exn env.stack move.dest in
    let stack_temp = dest_new :: stack_temp in
    let stack = Temp.Map.set env.stack ~key:move.dest ~data:stack_temp in
    let env = { index; stack } in
    let move = T.Move { move with dest = dest_new } in
    move, env
  | Return ret -> Return ret, env
  | Jump jp -> Jump jp, env
  | CJump cjp -> CJump cjp, env
  | Label l -> Label l, env
  | Nop -> Nop, env
  | NExp nexp -> NExp nexp, env

(* rename stm includes replace temp in use and def *)
and rename_stm stm env : T.stm * env =
  let stm = rename_use stm env in
  rename_def stm env
;;

(* rename basic block at the begining of _rename *)
let rec rename_bb (body : T.stm list) (new_body : T.stm list) (env : env)
    : T.stm list * env
  =
  match body with
  | [] -> List.rev new_body, env
  | h :: t ->
    let new_stm, new_env = rename_stm h env in
    rename_bb t (new_stm :: new_body) new_env
;;

(* pop variables defined in this block at the end of _rename *)
let rec cleanup_bb (body : T.stm list) env : env =
  match body with
  | [] -> env
  | h :: t ->
    (match h with
    | Move move ->
      let temp =
        match Temp.Map.find !backtracker move.dest with
        | None -> move.dest
        | Some s -> s
      in
      let stack_temp = Temp.Map.find_exn env.stack temp in
      let stack_temp =
        match stack_temp with
        | [] -> []
        | _ :: t -> t
      in
      { env with stack = Temp.Map.set env.stack ~key:temp ~data:stack_temp }
    | Return _ | Jump _ | CJump _ | Label _ | Nop | NExp _ -> cleanup_bb t env)
;;

let rec init_env_stms (env : env) (stms : T.stm list) =
  match stms with
  | [] -> env
  | h :: t ->
    (match h with
    | Move move ->
      let index, stack = env.index, env.stack in
      let index = Temp.Map.set index ~key:move.dest ~data:move.dest in
      let stack = Temp.Map.set stack ~key:move.dest ~data:[ move.dest ] in
      let env = { index; stack } in
      init_env_stms env t
    | _ -> init_env_stms env t)
;;

let rec init_env env blks =
  match blks with
  | [] -> env
  | blk :: t ->
    let env = init_env_stms env blk.body in
    init_env env t
;;

let _rename_phi_operand (pred_branch : int) phi env : phi =
  let dest, src = phi.dest, phi.src in
  let temp = dest in
  let operand = List.hd_exn (Temp.Map.find_exn env.stack temp) in
  let src = Int.Map.set src ~key:pred_branch ~data:(Some operand) in
  { dest; src }
;;

(* rename phi function operand in successors of a parent *)
let rec _rename_succ parent children env blk_map =
  match children with
  | [] -> blk_map
  | h :: t ->
    let blk_child = Int.Map.find_exn blk_map h in
    let phis = blk_child.phis in
    let phis = List.map phis ~f:(fun phi -> _rename_phi_operand parent phi env) in
    let blk_child = { blk_child with phis } in
    let blk_map = Int.Map.set blk_map ~key:h ~data:blk_child in
    _rename_succ parent t env blk_map
;;

(* rename block blk, and update phi function in its successors.
 * then rename its children in D-Tree recursively. *)
let rec _rename blk blk_map env dt =
  match blk.no with
  | -1 -> blk_map, env
  | _ ->
    let body_new, env_new = rename_bb blk.body [] env in
    let blk_new = { blk with body = body_new } in
    let succs = Int.Set.to_list blk_new.succ in
    let blk_map = _rename_succ blk_new.no succs env_new blk_map in
    let children = Int.Map.find_exn dt blk_new.no in
    let blk_map, env_new =
      Int.Set.fold children ~init:(blk_map, env_new) ~f:(fun acc child ->
          let blk_map_acc, env_acc = acc in
          let child_blk = Int.Map.find_exn blk_map child in
          _rename child_blk blk_map_acc env_acc dt)
    in
    let env_end = cleanup_bb body_new env_new in
    blk_map, env_end
;;

let rename blk_map dt =
  let env = { index = Temp.Map.empty; stack = Temp.Map.empty } in
  let env = init_env env (Int.Map.data blk_map) in
  let entry = Int.Map.find_exn blk_map (-2) in
  _rename entry blk_map env dt
;;

let rec _decompose_blk phis (tail_map : T.stm list Int.Map.t) =
  match phis with
  | [] -> tail_map
  | phi :: t ->
    let dest = phi.dest in
    let tail_map =
      Int.Map.fold phi.src ~init:tail_map ~f:(fun ~key:pred ~data:operand acc ->
          let old_tail =
            match Int.Map.find acc pred with
            | None -> []
            | Some s -> s
          in
          match operand with
          | None -> failwith "not found corresponding ssa source"
          | Some src ->
            let new_tail = T.Move { dest; src = T.Temp src } :: old_tail in
            Int.Map.set acc ~key:pred ~data:new_tail)
    in
    _decompose_blk t tail_map
;;

(* Remove phi function by adding tail_map statements to block*)
let to_dblock ssa_blk_map tail_map =
  let dblk_map = Int.Map.empty in
  Int.Map.fold tail_map ~init:dblk_map ~f:(fun ~key:blk_no ~data:move_stms acc ->
      let ssa_blk = Int.Map.find_exn ssa_blk_map blk_no in
      let body = ssa_blk.body @ move_stms in
      let dblk = ({ body; no = ssa_blk.no; succ = ssa_blk.succ } : D.block) in
      Int.Map.set acc ~key:blk_no ~data:dblk)
;;

(* Handle phi function at each block blk.
 * We store the added move statement to tail_map
 * because insert move statement at the end of 
 * statements is expensive. We will handle it once
 * we have stored all added move statements. *)
let rec _decompose blks pred_map tail_map =
  match blks with
  | [] -> tail_map
  | blk :: t ->
    let tail_map = _decompose_blk blk.phis tail_map in
    _decompose t pred_map tail_map
;;

(* Transform ssa_block to Tree.block by removing
 * phi function in ssa_block. Add move statement 
 * at the end of each block's predecessor. *)
let decompose ssa_blk_map pred_map =
  let tail_map = Int.Map.empty in
  let blks = Int.Map.data ssa_blk_map in
  let tail_map = _decompose blks pred_map tail_map in
  let blk_map = to_dblock ssa_blk_map tail_map in
  blk_map
;;

(* df: dominance frontier.
 * dt: dominance tree. Map for parent block_number -> children block_number set.
 * pred_map: predecesor map, block_number -> block_number set
 * blk_map: block number -> block *)
let run df dt pred_map (blk_map : D.block Int.Map.t) : T.stm list =
  let ssa_blk_map = build_ssa_block blk_map in
  let defsites = get_defsites ssa_blk_map in
  let ssa_blk_map = insert ssa_blk_map defsites df pred_map in
  let ssa_blk_map, _ = rename ssa_blk_map dt in
  let blk_map = decompose ssa_blk_map pred_map in
  let blks = Int.Map.to_alist ~key_order:`Increasing blk_map in
  List.fold blks ~init:[] ~f:(fun acc blk_tuple ->
      let _, blk = blk_tuple in
      acc @ blk.body)
;;
