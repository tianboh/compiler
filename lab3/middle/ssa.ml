(* 
 * SSA will read an IR tree and generate a SSA formed IR tree
 * Here, I use minimal SSA through dominance frontier to make
 * sure that phi function is inserted in a minimal time.
 *
 * Check https://www.cs.rice.edu/~keith/EMBED/dom.pdf for 
 * algorithm details.
 *
 * Author: Tianbo Hao<tianboh@alumni.cmu.edu>
 *)
open Core
module T = Tree
module D = Dominator
module Temp = Var.Temp

(* dest = phi(src1, ..., srcn). Since dest and src may change
 * during rename procedure, we keep track of the original dest
 * name for each phi.
 * src is a hashmap from predecessor k to its subscript.
 * key: predecessor block number k, value: current subscript for k *)
type phi =
  { name : Temp.t
  ; dest : Temp.t
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
 * Store the stack of temporaries during parsing the D-tree. 
 * Some temporaries may be renamed during process, so we need
 * to track its original name in root map.
 * key in index and stack are original temporary name. 
 * root keeps track of each temporary's original name *)
type env =
  { stack : Temp.t List.t Temp.Map.t
  ; root : Temp.t Temp.Map.t
  }

module type PRINT = sig
  val pp_phi : phi -> unit
  val pp_phis : phi list -> unit
  val pp_blk : ssa_block Int.Map.t -> unit
  val pp_env : env -> unit
end

module Print : PRINT = struct
  let pp_phi phi =
    let src_l =
      Int.Map.fold phi.src ~init:[] ~f:(fun ~key:k ~data:d acc ->
          match d with
          | None -> sprintf "operand from parent %d not assigned yet" k :: acc
          | Some s -> Temp.name s :: acc)
    in
    printf
      "%s = phi(%s), orig name %s\n"
      (Temp.name phi.dest)
      (String.concat src_l ~sep:", ")
      (Temp.name phi.name)
  ;;

  let pp_phis phis = List.iter phis ~f:(fun phi -> pp_phi phi)

  let pp_blk (blk_map : ssa_block Int.Map.t) =
    let keys = Int.Map.keys blk_map in
    let sorted_key = List.sort keys ~compare:Int.compare in
    List.iter sorted_key ~f:(fun blk_no ->
        let blk = Int.Map.find_exn blk_map blk_no in
        printf "block %d\n" blk_no;
        pp_phis blk.phis;
        printf "%s\n" (T.Print.pp_program blk.body))
  ;;

  let pp_env env =
    printf "print env\n";
    Temp.Map.iteri env.stack ~f:(fun ~key:k ~data:d ->
        let stack = List.map d ~f:(fun x -> Temp.name x) |> String.concat ~sep:", " in
        printf "  temporary %s, stack %s\n" (Temp.name k) stack);
    Temp.Map.iteri env.root ~f:(fun ~key:k ~data:d ->
        printf "  root: %s, child: %s\n" (Temp.name d) (Temp.name k))
  ;;
end

(* Update new_temp's root to old_temp's root. because move: old_temp -> new_temp happend *)
let update_root env old_temp new_temp =
  let original_root =
    match Temp.Map.find env.root old_temp with
    | Some s -> s
    | None -> old_temp
  in
  { env with root = Temp.Map.set env.root ~key:new_temp ~data:original_root }
;;

let build_ssa_block (blk_map : D.block Int.Map.t) : ssa_block Int.Map.t =
  Int.Map.map blk_map ~f:(fun blk ->
      { phis = []; body = blk.body; no = blk.no; succ = blk.succ })
;;

let get_blk_defsite_helper defsites dest blk_no =
  let sites =
    match Temp.Map.find defsites dest with
    | None -> Int.Set.empty
    | Some s -> s
  in
  let sites = Int.Set.add sites blk_no in
  let defsites = Temp.Map.set defsites ~key:dest ~data:sites in
  defsites
;;

let rec get_blk_defsite blk_no (stms : T.stm list) defsites =
  match stms with
  | [] -> defsites
  | stm :: t ->
    (match stm with
    | T.Move move ->
      let defsites = get_blk_defsite_helper defsites move.dest blk_no in
      get_blk_defsite blk_no t defsites
    | T.Effect eft ->
      let defsites = get_blk_defsite_helper defsites eft.dest blk_no in
      get_blk_defsite blk_no t defsites
    | T.Return _ | T.Jump _ | T.CJump _ | T.Label _ | T.Nop ->
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
      let new_phi = { name = dest; src; dest } in
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
    (* In some special cases, exp may be used when there is such temp stack
     * For example, in ternary op, statements are executed for side effect, 
     * and there is not blocks explicitly. So the end exp may not be denoted
     * but not defined in previous statements besides this sexp.stm *)
    let temp_stack =
      match Temp.Map.find env.stack temp with
      | None -> [ temp ]
      | Some s -> s
    in
    Temp (List.hd_exn temp_stack)
  | Binop binop ->
    let lhs_new = rename_exp binop.lhs env in
    let rhs_new = rename_exp binop.rhs env in
    Binop { binop with lhs = lhs_new; rhs = rhs_new }

and rename_use (stm : T.stm) env : T.stm =
  match stm with
  | Move move ->
    let src_new = rename_exp move.src env in
    Move { move with src = src_new }
  | Effect eft ->
    let lhs_new = rename_exp eft.lhs env in
    let rhs_new = rename_exp eft.rhs env in
    Effect { eft with lhs = lhs_new; rhs = rhs_new }
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

and rename_def_helper (dest : Temp.t) (env : env) =
  let dest_new = Temp.create () in
  let env = update_root env dest dest_new in
  let dest_new_root = Temp.Map.find_exn env.root dest_new in
  let stack_temp =
    match Temp.Map.find env.stack dest_new_root with
    | None -> [ dest_new ]
    | Some s -> dest_new :: s
  in
  let stack = Temp.Map.set env.stack ~key:dest_new_root ~data:stack_temp in
  let env = { env with stack } in
  dest_new, env

and rename_def (stm : T.stm) (env : env) : T.stm * env =
  match stm with
  | Move move ->
    let dest_new, env = rename_def_helper move.dest env in
    (* printf "rename_move def from %s to %s\n" (Temp.name move.dest) (Temp.name dest_new); *)
    let move = T.Move { move with dest = dest_new } in
    move, env
  | Effect eft ->
    let dest_new, env = rename_def_helper eft.dest env in
    (* printf "rename_eft def from %s to %s\n" (Temp.name eft.dest) (Temp.name dest_new); *)
    let eft = T.Effect { eft with dest = dest_new } in
    eft, env
  | Return ret -> Return ret, env
  | Jump jp -> Jump jp, env
  | CJump cjp -> CJump cjp, env
  | Label l -> Label l, env
  | Nop -> Nop, env

(* rename stm includes replace temp in use and def *)
and rename_stm stm env : T.stm * env =
  let stm = rename_use stm env in
  rename_def stm env
;;

let rec rename_phis (phis : phi list) (env : env) (phis_new : phi list) : phi list * env =
  match phis with
  | [] -> phis_new, env
  | h :: t ->
    let dest_new = Temp.create () in
    let env = update_root env h.name dest_new in
    let stack_temp =
      match Temp.Map.find env.stack h.name with
      | None -> [ dest_new ]
      | Some s -> dest_new :: s
    in
    let stack = Temp.Map.set env.stack ~key:h.name ~data:stack_temp in
    let env = { env with stack } in
    (* printf "rename_phi def from %s to %s\n" (Temp.name h.dest) (Temp.name dest_new); *)
    let phi_new = { h with dest = dest_new } in
    (* Print.pp_phi phi_new; *)
    rename_phis t env (phi_new :: phis_new)
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

(* Remove the temporary from stack top. *)
let cleanup_temp ori_name new_name env : env =
  let stack_temp = Temp.Map.find_exn env.stack ori_name in
  let stack_temp =
    match stack_temp with
    | [] -> []
    | _ :: t -> t
  in
  { stack = Temp.Map.set env.stack ~key:ori_name ~data:stack_temp
  ; root = Temp.Map.remove env.root new_name
  }
;;

(* pop variables defined in this block at the end of _rename *)
let cleanup_bb (blk : ssa_block) (env : env) : env =
  let rec cleanup_body (body : T.stm list) env =
    match body with
    | [] ->
      (* printf "cleanup\n";
      Print.pp_env env; *)
      env
    | h :: t ->
      (match h with
      | Move move ->
        let name = Temp.Map.find_exn env.root move.dest in
        let env = cleanup_temp name move.dest env in
        cleanup_body t env
      | Effect eft ->
        let name = Temp.Map.find_exn env.root eft.dest in
        let env = cleanup_temp name eft.dest env in
        cleanup_body t env
      | Return _ | Jump _ | CJump _ | Label _ | Nop -> cleanup_body t env)
  in
  let rec cleanup_phi (phis : phi list) (env : env) : env =
    match phis with
    | [] -> env
    | h :: t ->
      let env = cleanup_temp h.name h.dest env in
      cleanup_phi t env
  in
  let env = cleanup_phi blk.phis env in
  cleanup_body blk.body env
;;

let _rename_phi_operand (pred_branch : int) phi env : phi =
  let temp, src = phi.name, phi.src in
  if Temp.Map.mem env.stack temp
  then (
    let operand =
      match List.hd (Temp.Map.find_exn env.stack temp) with
      | None -> None
      | Some s -> Some s
    in
    let src = Int.Map.set src ~key:pred_branch ~data:operand in
    { phi with src })
  else phi
;;

(* rename phi function operand in successors of a parent *)
let rec _rename_succ parent children env blk_map =
  match children with
  | [] -> blk_map
  | h :: t ->
    (* printf "=rename succ %d of par %d\n" h parent; *)
    let blk_child = Int.Map.find_exn blk_map h in
    let phis = blk_child.phis in
    let phis = List.map phis ~f:(fun phi -> _rename_phi_operand parent phi env) in
    let blk_child = { blk_child with phis } in
    let blk_map = Int.Map.set blk_map ~key:h ~data:blk_child in
    (* Print.pp_phis phis; *)
    _rename_succ parent t env blk_map
;;

(* rename block blk, and update phi function in its successors.
 * then rename its children in D-Tree recursively. *)
let rec _rename blk blk_map env dt =
  match blk.no with
  | -1 -> blk_map, env
  | _ ->
    (* printf "==rename block %d\n" blk.no; *)
    let phis_new, env_new = rename_phis blk.phis env [] in
    let body_new, env_new = rename_bb blk.body [] env_new in
    let blk_new = { blk with body = body_new; phis = phis_new } in
    let blk_map = Int.Map.set blk_map ~key:blk_new.no ~data:blk_new in
    let succs = Int.Set.to_list blk_new.succ in
    let blk_map = _rename_succ blk_new.no succs env_new blk_map in
    let children =
      match Int.Map.find dt blk_new.no with
      | Some s -> s
      | None -> Int.Set.empty
    in
    let blk_map, env_new =
      Int.Set.fold children ~init:(blk_map, env_new) ~f:(fun acc child ->
          let blk_map_acc, env_acc = acc in
          let child_blk = Int.Map.find_exn blk_map_acc child in
          _rename child_blk blk_map_acc env_acc dt)
    in
    (* printf "start clenaup for block %d\n" blk.no; *)
    let env_end = cleanup_bb blk_new env_new in
    (* printf "--rename block %d finished\n" blk.no; *)
    blk_map, env_end
;;

(* rename phi operand and dest in the dominance frontier *)
let rename blk_map dt =
  let env = { stack = Temp.Map.empty; root = Temp.Map.empty } in
  (* let env = init_env env (Int.Map.data blk_map) in *)
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
          | None -> acc
          | Some src ->
            let new_tail = T.Move { dest; src = T.Temp src } :: old_tail in
            Int.Map.set acc ~key:pred ~data:new_tail)
    in
    _decompose_blk t tail_map
;;

(* Transform phi function of blk to its predecessors
 * Add move instruction at the end of its predecessors 
 * except jump and cjump. 
 * Make sure those move are executed before jump/cjump *)
let rec concat_tail_move (body : T.stm list) (moves : T.stm list) (res : T.stm list) =
  match body with
  | [] -> List.rev res @ moves
  | h :: t ->
    (match h with
    | Jump _ | CJump _ -> List.rev res @ moves @ body
    | _ -> concat_tail_move t moves (h :: res))
;;

(* Remove phi function by adding tail_map statements to block*)
let to_dblock ssa_blk_map tail_map =
  let dblk_map = Int.Map.empty in
  let ret =
    Int.Map.fold ssa_blk_map ~init:dblk_map ~f:(fun ~key:blk_no ~data:ssa_blk acc ->
        let body =
          match Int.Map.find tail_map blk_no with
          | None -> ssa_blk.body
          | Some s -> concat_tail_move ssa_blk.body s []
        in
        let dblk = ({ body; no = ssa_blk.no; succ = ssa_blk.succ } : D.block) in
        Int.Map.set acc ~key:blk_no ~data:dblk)
  in
  (* Dominator.Print.pp_blk ret; *)
  ret
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
let run (program : T.stm list) : T.stm list =
  let df, dt, pred_map, blk_map = Dominator.run program in
  let ssa_blk_map = build_ssa_block blk_map in
  (* printf "build_ssa_block\n";
  Print.pp_blk ssa_blk_map; *)
  let defsites = get_defsites ssa_blk_map in
  (* printf "get_defsites\n";
  Print.pp_blk ssa_blk_map; *)
  let ssa_blk_map = insert ssa_blk_map defsites df pred_map in
  (* printf "insert\n";
  Print.pp_blk ssa_blk_map; *)
  let ssa_blk_map, _ = rename ssa_blk_map dt in
  (* printf "rename\n";
  Print.pp_blk ssa_blk_map; *)
  let blk_map = decompose ssa_blk_map pred_map in
  (* Dominator.Print.pp_blk blk_map; *)
  let blks = Int.Map.to_alist ~key_order:`Increasing blk_map in
  List.fold blks ~init:[] ~f:(fun acc blk_tuple ->
      let _, blk = blk_tuple in
      acc @ blk.body)
;;
