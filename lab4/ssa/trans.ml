(* 
 * SSA will read an IR fdefn and generate a SSA formed IR fdefn
 * I use minimal SSA through dominance frontier to make
 * sure that phi function is inserted in a minimal time.
 *
 * Function parameters are assigned zero in parameter
 * block for declare/assign consistency in the following SSA
 * This module does not calculate so it will not lead to error.
 * Parameter block will be removed once SSA is done, also, the 
 * new temp name will be updated to function parameter.
 *
 * Check https://www.cs.rice.edu/~keith/EMBED/dom.pdf for 
 * algorithm details.
 *
 * Author: Tianbo Hao<tianboh@alumni.cmu.edu>
 *)
open Core
module Tree = Ir_tree.Inst
module D = Dominator
module Temp = Var.Temp
module Label = Util.Label
module Symbol = Util.Symbol

(* dest = phi(src1, ..., srcn). Since dest and src may change
 * during rename procedure, we keep track of the original dest
 * name for each phi.
 * src is a hashmap from predecessor k to its label.
 * key: predecessor block number k, value: current subscript for k *)
type phi =
  { name : Temp.t
  ; dest : Temp.t
  ; src : Temp.t option Label.Map.t
  }

(* SSA block extends phi list based on dominator block *)
type ssa_block =
  { phis : phi list
  ; body : Tree.stm list
  ; label : Label.t
  ; succ : Label.Set.t
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

let exit = Dominator.exit
let entry = Dominator.entry

module type PRINT = sig
  val pp_phi : phi -> unit
  val pp_phis : phi list -> unit
  val pp_blk : ssa_block Int.Map.t -> unit
  val pp_env : env -> unit
end

module Print : PRINT = struct
  let pp_phi phi =
    let src_l =
      Label.Map.fold phi.src ~init:[] ~f:(fun ~key:k ~data:d acc ->
          match d with
          | None ->
            sprintf "operand from parent %s not assigned yet" (Label.name k) :: acc
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
    List.iter sorted_key ~f:(fun blk_label ->
        let blk = Int.Map.find_exn blk_map blk_label in
        printf "block %d\n" blk_label;
        pp_phis blk.phis;
        printf "%s\n" (Tree.Print.pp_stms blk.body))
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

let build_ssa_block (blk_map : D.block Label.Map.t) : ssa_block Label.Map.t =
  Label.Map.map blk_map ~f:(fun blk ->
      { phis = []; body = blk.body; label = blk.label; succ = blk.succ })
;;

let get_blk_defsite_helper defsites dest blk_label =
  let sites =
    match Temp.Map.find defsites dest with
    | None -> Label.Set.empty
    | Some s -> s
  in
  let sites = Label.Set.add sites blk_label in
  let defsites = Temp.Map.set defsites ~key:dest ~data:sites in
  defsites
;;

let rec get_blk_defsite blk_label (stms : Tree.stm list) defsites =
  match stms with
  | [] -> defsites
  | stm :: t ->
    (match stm with
    | Move move ->
      let defsites = get_blk_defsite_helper defsites move.dest blk_label in
      get_blk_defsite blk_label t defsites
    | Effect eft ->
      let defsites = get_blk_defsite_helper defsites eft.dest blk_label in
      get_blk_defsite blk_label t defsites
    | Fcall fcall ->
      (match fcall.dest with
      | None -> get_blk_defsite blk_label t defsites
      | Some dest ->
        let defsites = get_blk_defsite_helper defsites dest blk_label in
        get_blk_defsite blk_label t defsites)
    | Return _ | Jump _ | CJump _ | Label _ | Nop | Assert _ | Load _ | Store _ ->
      get_blk_defsite blk_label t defsites)
;;

let rec _get_defsites blks defsites =
  match blks with
  | [] -> defsites
  | blk :: t ->
    let defsites = get_blk_defsite blk.label blk.body defsites in
    _get_defsites t defsites
;;

(* hashmap from Temp -> Label.Set
 * key: temp, value: blk number set that defines this temp *)
let get_defsites blk_map =
  let blks = Label.Map.data blk_map in
  let defsites = Temp.Map.empty in
  _get_defsites blks defsites
;;

(* insert phi(temp) at dominance frontier df_list of a blk
 * return updated acc_blk_map after insertion.
 * Also return updated def_list if this node didn't
 * define temp before. *)
let rec insert_df
    (temp : Temp.t)
    df_map
    df_list
    acc_blk_map
    (acc_new_def_site : Label.t list)
    pred_map
    blk
    : ssa_block Label.Map.t * Label.t list
  =
  match df_list with
  | [] -> acc_blk_map, acc_new_def_site
  | h :: t ->
    let blk_df = Label.Map.find_exn acc_blk_map h in
    let phis_dest = List.map blk_df.phis ~f:(fun phi -> phi.dest) in
    if List.mem phis_dest temp ~equal:phys_equal
    then insert_df temp df_map t acc_blk_map acc_new_def_site pred_map blk
    else (
      let dest = temp in
      let preds = Label.Map.find_exn pred_map blk_df.label in
      let src =
        Label.Set.fold preds ~init:Label.Map.empty ~f:(fun acc pred ->
            Label.Map.set acc ~key:pred ~data:None)
      in
      let new_phi = { name = dest; src; dest } in
      let blk_df = { blk_df with phis = new_phi :: blk_df.phis } in
      let acc_blk_map = Label.Map.set acc_blk_map ~key:blk_df.label ~data:blk_df in
      let acc_new_def_site = blk_df.label :: acc_new_def_site in
      insert_df temp df_map t acc_blk_map acc_new_def_site pred_map blk)
;;

(* insert phi for temp whose defsites is def_list *)
let rec insert_temp
    (temp : Temp.t)
    (def_list : Label.t list)
    df_map
    (acc_blk_map : ssa_block Label.Map.t)
    (pred_map : Label.Set.t Label.Map.t)
    : ssa_block Label.Map.t
  =
  match def_list with
  | [] -> acc_blk_map
  | h :: t ->
    let blk = Label.Map.find_exn acc_blk_map h in
    let df_list = Label.Set.to_list (Label.Map.find_exn df_map blk.label) in
    let acc_blk_map, new_def_list_of_blk =
      insert_df temp df_map df_list acc_blk_map [] pred_map blk
    in
    let new_t = t @ new_def_list_of_blk in
    insert_temp temp new_t df_map acc_blk_map pred_map
;;

(* insert phi function to each dominance frontier *)
let insert blk_map defsites df pred_map =
  Temp.Map.fold defsites ~init:blk_map ~f:(fun ~key:temp ~data:defs acc_blk_map ->
      let defs_l = Label.Set.to_list defs in
      insert_temp temp defs_l df acc_blk_map pred_map)
;;

let rec rename_exp (exp : Tree.exp) (env : env) : Tree.exp =
  match exp with
  | Void -> Void
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

and rename_use (stm : Tree.stm) env : Tree.stm =
  match stm with
  | Move move ->
    let src_new = rename_exp move.src env in
    Move { move with src = src_new }
  | Effect eft ->
    let lhs_new = rename_exp eft.lhs env in
    let rhs_new = rename_exp eft.rhs env in
    Effect { eft with lhs = lhs_new; rhs = rhs_new }
  | Fcall fcall ->
    let args = List.map fcall.args ~f:(fun arg -> rename_exp arg env) in
    Fcall { fcall with args }
  | Assert asrt ->
    let asrt = rename_exp asrt env in
    Assert asrt
  | Return ret ->
    (match ret with
    | None -> Return None
    | Some ret ->
      let ret_new = rename_exp ret env in
      Return (Some ret_new))
  | Jump jp -> Jump jp
  | CJump cjp ->
    let lhs_new = rename_exp cjp.lhs env in
    let rhs_new = rename_exp cjp.rhs env in
    CJump { cjp with lhs = lhs_new; rhs = rhs_new }
  | Label l -> Label l
  | Nop -> Nop
  | Load load -> Load load
  | Store store ->
    let src = rename_exp store.src env in
    Store { store with src }

and rename_def_helper (dest : Temp.t) (env : env) =
  let dest_new = Temp.create dest.size in
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

and rename_def (stm : Tree.stm) (env : env) : Tree.stm * env =
  match stm with
  | Move move ->
    let dest_new, env = rename_def_helper move.dest env in
    (* printf "rename_move def from %s to %s\n" (Temp.name move.dest) (Temp.name dest_new); *)
    let move = Tree.Move { move with dest = dest_new } in
    move, env
  | Effect eft ->
    let dest_new, env = rename_def_helper eft.dest env in
    (* printf "rename_eft def from %s to %s\n" (Temp.name eft.dest) (Temp.name dest_new); *)
    let eft = Tree.Effect { eft with dest = dest_new } in
    eft, env
  | Fcall fcall ->
    (match fcall.dest with
    | None -> Tree.Fcall fcall, env
    | Some dest ->
      let dest_new, env = rename_def_helper dest env in
      let eft = Tree.Fcall { fcall with dest = Some dest_new } in
      eft, env)
  | Assert asrt -> Assert asrt, env
  | Return ret -> Return ret, env
  | Jump jp -> Jump jp, env
  | CJump cjp -> CJump cjp, env
  | Label l -> Label l, env
  | Nop -> Nop, env
  | Load load ->
    let dest_new, env = rename_def_helper load.dest env in
    Load { load with dest = dest_new }, env
  | Store store -> Store store, env

(* rename stm includes replace temp in use and def *)
and rename_stm stm env : Tree.stm * env =
  let stm = rename_use stm env in
  rename_def stm env
;;

let rec rename_phis (phis : phi list) (env : env) (phis_new : phi list) : phi list * env =
  match phis with
  | [] -> phis_new, env
  | h :: t ->
    let dest_new = Temp.create h.dest.size in
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
let rec rename_bb (body : Tree.stm list) (new_body : Tree.stm list) (env : env)
    : Tree.stm list * env
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
  let rec cleanup_body (body : Tree.stm list) env =
    match body with
    | [] -> env
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
      | Fcall fcall ->
        (match fcall.dest with
        | None -> cleanup_body t env
        | Some dest ->
          let name = Temp.Map.find_exn env.root dest in
          let env = cleanup_temp name dest env in
          cleanup_body t env)
      | Load load ->
        let name = Temp.Map.find_exn env.root load.dest in
        let env = cleanup_temp name load.dest env in
        cleanup_body t env
      | Return _ | Jump _ | CJump _ | Label _ | Nop | Assert _ | Store _ ->
        cleanup_body t env)
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

let _rename_phi_operand (pred_branch : Label.t) phi env : phi =
  let temp, src = phi.name, phi.src in
  if Temp.Map.mem env.stack temp
  then (
    let operand =
      match List.hd (Temp.Map.find_exn env.stack temp) with
      | None -> None
      | Some s -> Some s
    in
    let src = Label.Map.set src ~key:pred_branch ~data:operand in
    { phi with src })
  else phi
;;

(* rename phi function operand in successors of a parent *)
let rec _rename_succ (parent : Label.t) children env blk_map =
  match children with
  | [] -> blk_map
  | h :: t ->
    (* printf "=rename succ %d of par %d\n" h parent; *)
    let blk_child = Label.Map.find_exn blk_map h in
    let phis = blk_child.phis in
    let phis = List.map phis ~f:(fun phi -> _rename_phi_operand parent phi env) in
    let blk_child = { blk_child with phis } in
    let blk_map = Label.Map.set blk_map ~key:h ~data:blk_child in
    (* Print.pp_phis phis; *)
    _rename_succ parent t env blk_map
;;

(* rename block blk, and update phi function in its successors.
 * then rename its children in D-Tree recursively. *)
let[@warning "-27-11"] rec _rename (blk : ssa_block) blk_map env dt =
  match blk.label with
  | exit -> blk_map, env
  | _ ->
    (* printf "==rename block %d\n" blk.no; *)
    let phis_new, env_new = rename_phis blk.phis env [] in
    let body_new, env_new = rename_bb blk.body [] env_new in
    let blk_new = { blk with body = body_new; phis = phis_new } in
    let blk_map = Label.Map.set blk_map ~key:blk_new.label ~data:blk_new in
    let succs = Label.Set.to_list blk_new.succ in
    let blk_map = _rename_succ blk_new.label succs env_new blk_map in
    let children =
      match Label.Map.find dt blk_new.label with
      | Some s -> s
      | None -> Label.Set.empty
    in
    let blk_map, env_new =
      Label.Set.fold children ~init:(blk_map, env_new) ~f:(fun acc child ->
          let blk_map_acc, env_acc = acc in
          let child_blk = Label.Map.find_exn blk_map_acc child in
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
  let entry = Label.Map.find_exn blk_map entry in
  _rename entry blk_map env dt
;;

let rec _decompose_blk phis (tail_map : Tree.stm list Label.Map.t) =
  match phis with
  | [] -> tail_map
  | phi :: t ->
    let dest = phi.dest in
    let tail_map =
      Label.Map.fold phi.src ~init:tail_map ~f:(fun ~key:pred ~data:operand acc ->
          let old_tail =
            match Label.Map.find acc pred with
            | None -> []
            | Some s -> s
          in
          match operand with
          | None -> acc
          | Some src ->
            let new_tail = Tree.Move { dest; src = Tree.Temp src } :: old_tail in
            Label.Map.set acc ~key:pred ~data:new_tail)
    in
    _decompose_blk t tail_map
;;

(* Transform phi function of blk to its predecessors
 * Add move instruction at the end of its predecessors 
 * except jump and cjump. 
 * Make sure those move are executed before jump/cjump *)
let rec concat_tail_move
    (body : Tree.stm list)
    (moves : Tree.stm list)
    (res : Tree.stm list)
  =
  match body with
  | [] -> List.rev res @ moves
  | h :: t ->
    (match h with
    | Jump _ | CJump _ -> List.rev res @ moves @ body
    | _ -> concat_tail_move t moves (h :: res))
;;

(* Remove phi function by adding tail_map statements to block*)
let to_dblock ssa_blk_map tail_map =
  let dblk_map = Label.Map.empty in
  let ret =
    Label.Map.fold ssa_blk_map ~init:dblk_map ~f:(fun ~key:blk_label ~data:ssa_blk acc ->
        let body =
          match Label.Map.find tail_map blk_label with
          | None -> ssa_blk.body
          | Some s -> concat_tail_move ssa_blk.body s []
        in
        let dblk = ({ body; label = ssa_blk.label; succ = ssa_blk.succ } : D.block) in
        Label.Map.set acc ~key:blk_label ~data:dblk)
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
  let tail_map = Label.Map.empty in
  let blks = Label.Map.data ssa_blk_map in
  let tail_map = _decompose blks pred_map tail_map in
  let blk_map = to_dblock ssa_blk_map tail_map in
  blk_map
;;

(* Build a block for function parameter assignment.
 * This is used to declare and define function parameters
 * and this block will be removed after ssa done.
 * Return block and its label *)
let pre_process (fdefn : Tree.fdefn) : Tree.stm list * Label.t =
  let param_label = Label.label (Some (Symbol.name fdefn.func_name)) in
  let movs =
    List.map fdefn.temps ~f:(fun temp ->
        Tree.Move { dest = temp; src = Tree.Const { v = Int64.zero; size = `DWORD } })
  in
  Tree.Label param_label :: movs, param_label
;;

(* Once SSA finished, skip the parameter block and update fdefn arg temps.
 * Return SSA Tree.fdefn *)
let post_process
    (fdefn : Tree.fdefn)
    (blk_map : D.block Label.Map.t)
    (par_label : Label.t)
    (order : Label.t list)
    : Tree.fdefn
  =
  (* get updated function parameters *)
  let par_blk_ssa = Label.Map.find_exn blk_map par_label in
  let args =
    List.filter_map par_blk_ssa.body ~f:(fun stm ->
        match stm with
        | Tree.Move m -> Some (Tree.Move m)
        | Tree.Label _ -> None
        | _ -> failwith "parameter ssa should not contain this type")
  in
  let[@warning "-8"] (temps : Temp.t list) =
    List.map args ~f:(fun (Tree.Move mov) -> mov.dest)
  in
  (* skip parameter, entry and exit block, and gen fdefn body *)
  let body =
    List.map order ~f:(fun l ->
        let blk = Label.Map.find_exn blk_map l in
        blk.body)
    |> List.concat
  in
  { func_name = fdefn.func_name; temps; body }
;;

(* df: dominance frontier.
 * dt: dominance tree. Map for parent block_number -> children block_number set.
 * pred_map: predecesor map, block_number -> block_number set
 * blk_map: block number -> block *)
let run (fdefn : Tree.fdefn) : Tree.fdefn =
  (* printf "ssa run\n"; *)
  let par_blk_stms, par_label = pre_process fdefn in
  let body =
    Tree.Label (Label.label (Some (Symbol.name fdefn.func_name))) :: fdefn.body
  in
  let (valid_blk_label : Label.t list) =
    List.filter_map body ~f:(fun stm ->
        match stm with
        | Tree.Label l -> Some l
        | _ -> None)
  in
  let program = par_blk_stms @ body in
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
  post_process fdefn blk_map par_label valid_blk_label
;;
