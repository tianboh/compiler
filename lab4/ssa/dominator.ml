(* This module provide function to calculate dominators.
 * D[n] indicates blocks that dominate block n, in other 
 * words, every path from entry point to block n must
 * pass block D[n]. It is calculated as below:
 *
 * D[n] = {n} Union {Inter_{p belongs to pred(n) D[p]}}
 *
 * D[n] will be calculated iteratedly, complexity O(n^2e)
 * if intersection and unions are calculated in vector bit, 
 * which is O(1). n is number of blocks and e is edges in graph.
 *
 * strict dominator is dominator except it self, calculated as 
 *
 * sD[n] = D[n] - {n}
 *
 * Immediate dominator is the first dominator that dominate n.
 *
 * iD[n] = iD[n] - U_{d belongs to iD[n]} (sD[n])
 *
 * For more details and explanations, check 
 * https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/lec/05-ssa.pdf
 * 
 * Author: Tianbo Hao<tianboh@alumni.cmu.edu>
 *)
module Tree = Ir_tree.Inst
module Label = Util.Label
open Core

type block =
  { body : Tree.stm list
  ; label : Label.t
  ; succ : Label.Set.t
  }

let entry = Label.label (Some "entry")
let exit = Label.label (Some "exit")

module Print = struct
  let pp_idom idom =
    Label.Map.iteri idom ~f:(fun ~key:k ~data:d ->
        printf "block %s idom is %s\n" (Label.name k) (Label.name d))
  ;;

  let pp_df df =
    Label.Map.iteri df ~f:(fun ~key:k ~data:d ->
        let df_k =
          Label.Set.to_list d
          |> List.map ~f:(fun x -> Label.name x)
          |> String.concat ~sep:", "
        in
        printf "block %s dominance frontier is %s\n" (Label.name k) df_k)
  ;;

  let pp_dt dt =
    Label.Map.iteri dt ~f:(fun ~key:k ~data:d ->
        let df_k =
          Label.Set.to_list d
          |> List.map ~f:(fun x -> Label.name x)
          |> String.concat ~sep:", "
        in
        printf "block %s dominance tree is %s\n" (Label.name k) df_k)
  ;;

  let pp_int_set s =
    let l = Int.Set.fold s ~init:[] ~f:(fun acc t -> Int.to_string t :: acc) in
    String.concat l ~sep:", "
  ;;

  let pp_label_set s =
    let l = Label.Set.fold s ~init:[] ~f:(fun acc t -> Label.name t :: acc) in
    String.concat l ~sep:", "
  ;;

  let pp_label_list l = List.map l ~f:(fun x -> Label.name x) |> String.concat ~sep:", "

  let pp_blk blk_map =
    let keys = Label.Map.keys blk_map in
    let sorted_key = List.sort keys ~compare:Label.compare in
    List.iter sorted_key ~f:(fun blk_no ->
        let blk = Label.Map.find_exn blk_map blk_no in
        printf "block %s\n%s%!\n" (Label.name blk_no) (Tree.Print.pp_stms blk.body);
        printf "block %s succ %s%!\n" (Label.name blk_no) (pp_label_set blk.succ))
  ;;
end

let rec group_stm
    (stms : Tree.stm list)
    (acc_stms_rev : Tree.stm list)
    (acc_blks_rev : (Tree.stm list * Label.t) list)
    (acc_label : Label.t)
    : (Tree.stm list * Label.t) list
  =
  match stms with
  | [] ->
    let last_blk = List.rev acc_stms_rev, acc_label in
    let blks_rev =
      if List.is_empty acc_stms_rev then acc_blks_rev else last_blk :: acc_blks_rev
    in
    let blks = List.rev blks_rev in
    blks
  | h :: t ->
    (match h with
    | Label label ->
      let blk = List.rev acc_stms_rev, acc_label in
      let acc_blks_rev =
        if List.is_empty acc_stms_rev then acc_blks_rev else blk :: acc_blks_rev
      in
      group_stm t [ Tree.Label label ] acc_blks_rev label
    | Move move -> group_stm t (Tree.Move move :: acc_stms_rev) acc_blks_rev acc_label
    | Return ret -> group_stm t (Tree.Return ret :: acc_stms_rev) acc_blks_rev acc_label
    | Jump jp -> group_stm t (Tree.Jump jp :: acc_stms_rev) acc_blks_rev acc_label
    | CJump cjp -> group_stm t (Tree.CJump cjp :: acc_stms_rev) acc_blks_rev acc_label
    | Effect eft -> group_stm t (Tree.Effect eft :: acc_stms_rev) acc_blks_rev acc_label
    | Nop -> group_stm t acc_stms_rev acc_blks_rev acc_label
    | Fcall fcall -> group_stm t (Tree.Fcall fcall :: acc_stms_rev) acc_blks_rev acc_label
    | Assert asrt -> group_stm t (Tree.Assert asrt :: acc_stms_rev) acc_blks_rev acc_label)
;;

(* entry block(empty) is entry. exit block(empty) is exit
 * return a hash table from label to block *)
let rec _build_block blks res : block Label.Map.t =
  match blks with
  | [] -> res
  | h :: t ->
    let body, label = h in
    let succ_label =
      match List.hd t with
      | None -> exit
      | Some s ->
        let _, s_label = s in
        s_label
    in
    let succ_init =
      match List.last_exn body with
      | Tree.Label _ | Tree.Move _ | Tree.Effect _ | Tree.Fcall _ | Tree.Nop ->
        [ succ_label ]
      | Tree.Return _ | Tree.Assert _ -> [ exit; succ_label ]
      | Tree.Jump jp -> [ jp ]
      | Tree.CJump cjp -> [ cjp.target_true; cjp.target_false; succ_label ]
    in
    let body_wo_tail = List.sub body ~pos:0 ~len:(List.length body - 1) in
    let succ_l =
      List.fold body_wo_tail ~init:succ_init ~f:(fun acc stm ->
          match stm with
          | Tree.Label _ | Tree.Move _ | Tree.Effect _ | Tree.Nop | Tree.Fcall _ -> acc
          | Tree.Return _ | Tree.Assert _ -> exit :: acc
          | Tree.Jump jp -> jp :: acc
          | Tree.CJump cjp -> [ cjp.target_true; cjp.target_false ] @ acc)
    in
    let succ = Label.Set.of_list succ_l in
    let block = { body; label; succ } in
    let res = Label.Map.add_exn res ~key:label ~data:block in
    _build_block t res
;;

(* For edge e from block a -> block b.
 * If block a has >= 2 successors and block b has >= 2 predecessors,
 * then edge e is a critical edge. We will add a block c to eliminate 
 * this critical edge.
 * New graph would be : block a -> block c -> block b. 
 * Now neither a nor b has critical edges.name
 * Other blocks topological remains unchanged. *)
let remove_criticl_edge blk_map pred_map =
  let labels = Label.Map.keys blk_map in
  let edges =
    List.fold labels ~init:[] ~f:(fun acc label_start ->
        let blk = Label.Map.find_exn blk_map label_start in
        let succ_l = Label.Set.to_list blk.succ in
        let tuples =
          List.fold succ_l ~init:[] ~f:(fun acc label_end ->
              (label_start, label_end) :: acc)
        in
        tuples @ acc)
  in
  List.fold edges ~init:(blk_map, pred_map) ~f:(fun acc x ->
      let acc_blk_map, acc_pred_map = acc in
      let src_l, dest_l = x in
      let src_blk = Label.Map.find_exn acc_blk_map src_l in
      if Label.Set.length src_blk.succ > 1
         && Label.Set.length (Label.Map.find_exn acc_pred_map dest_l) > 1
      then (
        (* find critical edge *)
        let label' = Label.label (Some "critical") in
        let blk' =
          { body = [ Tree.Label label'; Tree.Jump dest_l ]
          ; label = label'
          ; succ = Label.Set.of_list [ dest_l ]
          }
        in
        let acc_blk_map = Label.Map.set acc_blk_map ~key:label' ~data:blk' in
        let src_blk_succ = Label.Set.remove src_blk.succ dest_l in
        let src_blk_succ = Label.Set.add src_blk_succ label' in
        let src_blk = { src_blk with succ = src_blk_succ } in
        let acc_blk_map = Label.Map.set acc_blk_map ~key:src_blk.label ~data:src_blk in
        let dest_blk_pred = Label.Map.find_exn acc_pred_map dest_l in
        let dest_blk_pred = Label.Set.remove dest_blk_pred src_l in
        let dest_blk_pred = Label.Set.add dest_blk_pred label' in
        let acc_pred_map = Label.Map.set acc_pred_map ~key:dest_l ~data:dest_blk_pred in
        let acc_pred_map =
          Label.Map.set acc_pred_map ~key:label' ~data:(Label.Set.of_list [ src_l ])
        in
        acc_blk_map, acc_pred_map)
      else acc)
;;

let build_block (f_body : Tree.stm list) =
  let blks = group_stm f_body [] [] entry in
  let blk_map = _build_block blks Label.Map.empty in
  let blk_map =
    Label.Map.set
      blk_map
      ~key:exit
      ~data:{ body = [ Tree.Label exit ]; label = exit; succ = Label.Set.empty }
  in
  blk_map
;;

let rec _build_pred blks res =
  match blks with
  | [] -> res
  | h :: t ->
    let res =
      Label.Set.fold h.succ ~init:res ~f:(fun acc v ->
          let pred_v =
            match Label.Map.find res v with
            | None -> Label.Set.empty
            | Some s -> s
          in
          let pred = Label.Set.add pred_v h.label in
          Label.Map.set acc ~key:v ~data:pred)
    in
    _build_pred t res
;;

(* Return a predecessor map from label to label set. *)
let build_pred (blk_map : block Label.Map.t) : Label.Set.t Label.Map.t =
  let blks = Label.Map.data blk_map in
  let res = Label.Map.empty in
  _build_pred blks res
;;

(* Use dfs to calculate postorder
 * return postorder, visited_set, and dfs_map
 * dfs_map: label -> dfs leave no. *)
let rec postorder
    visited
    blk_label
    blk_map
    (order : Label.t list)
    (dfs_map : int Label.Map.t)
    : Label.t list * Label.Set.t * int Label.Map.t
  =
  (* printf "visiting %s%!\n" (Label.name blk_label); *)
  let visited = Label.Set.add visited blk_label in
  let blk = Label.Map.find_exn blk_map blk_label in
  let ret =
    let order, visited, dfs_map =
      Label.Set.fold blk.succ ~init:(order, visited, dfs_map) ~f:(fun acc succ ->
          let acc_order, acc_visited, acc_dfs_map = acc in
          if Label.Set.mem acc_visited succ
          then acc
          else postorder acc_visited succ blk_map acc_order acc_dfs_map)
    in
    let order = order @ [ blk.label ] in
    let dfs_map = Label.Map.set dfs_map ~key:blk.label ~data:(List.length order) in
    order, visited, dfs_map
  in
  ret
;;

(* Find nearest common root for both b1 and b2. *)
let rec intersect
    (b1 : Label.t)
    (b2 : Label.t)
    (idom_map : Label.t Label.Map.t)
    (dfs_map : int Label.Map.t)
  =
  (* printf "intersect %s %s, %!" (Label.name b1) (Label.name b2); *)
  if phys_equal b1 entry || phys_equal b2 entry
  then entry
  else if phys_equal b1 b2
  then b1
  else (
    let b1_dfs_no, b2_dfs_no =
      Label.Map.find_exn dfs_map b1, Label.Map.find_exn dfs_map b2
    in
    if b1_dfs_no < b2_dfs_no
    then (
      let b1 =
        match Label.Map.find idom_map b1 with
        | Some s -> s
        | None -> failwith (sprintf "intersect b1 %s fail%!" (Label.name b1))
      in
      intersect b1 b2 idom_map dfs_map)
    else (
      let b2 =
        match Label.Map.find idom_map b2 with
        | Some s -> s
        | None -> failwith (sprintf "intersect b2 %s fail%!" (Label.name b2))
      in
      intersect b1 b2 idom_map dfs_map))
;;

(* idom is the immediate dominator of pred_list. it is a integer *)
let rec _idom_trav_par pred_list idom (idom_map : Label.t Label.Map.t) dfs_map =
  match pred_list with
  | [] -> idom
  | h :: t ->
    (match Label.Map.find idom_map h with
    | None -> _idom_trav_par t idom idom_map dfs_map
    | Some _ ->
      let new_idom = intersect h idom idom_map dfs_map in
      (* printf ", new idom %s\n%!" (Label.name new_idom); *)
      _idom_trav_par t new_idom idom_map dfs_map)
;;

(* idom_map is the immediate dominators across all blocks. it is a map *)
let rec _idom
    (idom_map : Label.t Label.Map.t)
    (changed : bool)
    (pred_map : Label.Set.t Label.Map.t)
    (order : Label.t list)
    (dfs_map : int Label.Map.t)
  =
  match changed with
  | true ->
    let changed = false in
    let changed, idom_map =
      List.fold order ~init:(changed, idom_map) ~f:(fun acc node ->
          (* printf "finding idom of node %s, " (Label.name node); *)
          let acc_changed, acc_idom_map = acc in
          let pred_s =
            match Label.Map.find pred_map node with
            | None -> Label.Set.empty
            | Some s -> s
          in
          let new_idom =
            Label.Set.find_exn pred_s ~f:(fun x -> Label.Map.mem acc_idom_map x)
          in
          let pred_s' = Label.Set.remove pred_s new_idom in
          let pred' = Label.Set.to_list pred_s' in
          (* printf
            "check least common root between %s and list: %s\n"
            (Label.name new_idom)
            (Print.pp_label_list pred'); *)
          let new_idom = _idom_trav_par pred' new_idom acc_idom_map dfs_map in
          (* printf "find new_idom for %s is %s\n" (Label.name node) (Label.name new_idom); *)
          match Label.Map.find acc_idom_map node with
          | None ->
            let acc_idom_map = Label.Map.set acc_idom_map ~key:node ~data:new_idom in
            let acc_changed = true in
            acc_changed, acc_idom_map
          | Some s ->
            if phys_equal s new_idom
            then acc_changed, acc_idom_map
            else (
              let acc_idom_map = Label.Map.set acc_idom_map ~key:node ~data:new_idom in
              let acc_changed = true in
              acc_changed, acc_idom_map))
    in
    _idom idom_map changed pred_map order dfs_map
  | false -> idom_map
;;

let pp_dfs_map dfs_map =
  Label.Map.iteri dfs_map ~f:(fun ~key:k ~data:d ->
      printf "dfs_order %s %d\n%!" (Label.name k) d)
;;

(* Calculate immediate dominator id[n] for each block
 * Algorithm: https://www.cs.rice.edu/~keith/EMBED/dom.pdf Figure 3
 *)
let idom blk_map pred_map =
  (* printf "idom%!\n"; *)
  let idom_map = Label.Map.empty in
  let idom_map = Label.Map.set idom_map ~key:entry ~data:entry in
  let changed = true in
  let post_order, _, dfs_map =
    postorder Label.Set.empty entry blk_map [] Label.Map.empty
  in
  (* pp_dfs_map dfs_map; *)
  let rev_post_order = List.rev post_order in
  (* remove entry block(empty) in reverse postorder *)
  let order =
    match rev_post_order with
    | [] -> []
    | _ :: t -> t
  in
  (* printf "order: %!";
  List.iter order ~f:(fun x -> printf "%s %!" (Label.name x));
  printf "\n"; *)
  _idom idom_map changed pred_map order dfs_map
;;

(* traverse dominate tree from bottom to up till found idom_node. *)
let rec _build_DF_while node runner idom_node idom_map df : Label.Set.t Label.Map.t =
  if phys_equal runner idom_node
  then df
  else (
    let df_runner =
      match Label.Map.find df runner with
      | None -> Label.Set.empty
      | Some s -> s
    in
    let df_runner = Label.Set.add df_runner node in
    let df = Label.Map.set df ~key:runner ~data:df_runner in
    let runner = Label.Map.find_exn idom_map runner in
    _build_DF_while node runner idom_node idom_map df)
;;

(* update dominance frontier for walk start from
 * node to its immediate dominator *)
let _build_DF node preds idom_map df : Label.Set.t Label.Map.t =
  Label.Set.fold preds ~init:df ~f:(fun df_acc pred ->
      let idom_node = Label.Map.find_exn idom_map node in
      let runner = pred in
      _build_DF_while node runner idom_node idom_map df_acc)
;;

(* build dominance frontier based on idom *)
let build_DF
    (blk_map : block Label.Map.t)
    (pred_map : Label.Set.t Label.Map.t)
    (idom : Label.t Label.Map.t)
  =
  let nodes = Label.Map.keys blk_map in
  let df = Label.Map.empty in
  let df =
    List.fold nodes ~init:df ~f:(fun df_acc node ->
        (* For entry and exit block, they doesn't have dominance frontier
         * For unreachable block like .afterlife, it doesn't either. *)
        if phys_equal node entry
           || phys_equal node exit
           || not (Label.Map.mem pred_map node)
        then Label.Map.set df_acc ~key:node ~data:Label.Set.empty
        else (
          let preds = Label.Map.find_exn pred_map node in
          if Label.Set.length preds >= 2 then _build_DF node preds idom df_acc else df_acc))
  in
  (* Fill up blocks that are not frontier of any blocks *)
  Label.Map.mapi blk_map ~f:(fun ~key:k ~data:_ ->
      if Label.Map.mem df k then Label.Map.find_exn df k else Label.Set.empty)
;;

(* build dominance tree, which is reverse of idom *)
let build_DT (idom : Label.t Label.Map.t) =
  Label.Map.fold idom ~init:Label.Map.empty ~f:(fun ~key:child ~data:parent acc ->
      let children =
        match Label.Map.find acc parent with
        | None -> Label.Set.empty
        | Some s -> s
      in
      let children = Label.Set.add children child in
      Label.Map.set acc ~key:parent ~data:children)
;;

(* Return dominance frontier, dominate tree, pred_map and blk_map *)
let run (f_body : Tree.stm list) =
  let f_body = (Tree.Label entry :: f_body) @ [ Tree.Label exit ] in
  let blk_map = build_block f_body in
  let pred_map = build_pred blk_map in
  let blk_map, pred_map = remove_criticl_edge blk_map pred_map in
  (* Print.pp_blk blk_map;
  printf "pred_map done%!\n"; *)
  let idom = idom blk_map pred_map in
  (* Print.pp_blk blk_map;
  Print.pp_idom idom; *)
  let df = build_DF blk_map pred_map idom in
  (* Print.pp_df df; *)
  let dt = build_DT idom in
  (* Print.pp_dt dt; *)
  df, dt, pred_map, blk_map
;;
