(* Implementation for CFG wrapper
 * Provide a instruction module following
 * Sig.InstrInterface, return a module with
 * CFG helper functions.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu> 
 *)

module Label = Util.Label
open Core

module Wrapper (I : Sig.InstrInterface) : Sig.CFGInterface with type i = I.i = struct
  type set = Label.Set.t
  type map = set Label.Map.t
  type i = I.i

  type bb =
    { label : Label.t
    ; instrs : i list
    }

  type bbmap = bb Label.Map.t

  let entry = ref (Label.label None)
  let exits = ref []
  let get_entry () : Label.t = !entry
  let get_exits () : Label.t list = !exits

  (* Eliminate fall through between block and block. 
   * Only use jump/cjump to go through blocks.
   * This helps to build control flow graph, and these 
   * redundant jumps will be eliminated in optimization pass.
   * 
   * A basic block should end up with one of following possibilities
   * 1) Jump or conditional jump
   * 2) Return 
   *)
  let eliminate_fall_through (instrs : i list) : i list =
    let rec helper (instrs : i list) (acc : i list) : i list =
      match instrs with
      | [] ->
        (match List.hd acc with
        | None -> acc
        | Some tail ->
          if I.is_return tail || I.is_raise tail
          then List.rev acc
          else List.rev (I.ret () :: acc))
      | h :: t ->
        if I.is_label h
        then (
          let pre_opt = List.hd acc in
          match pre_opt with
          | None ->
            if List.length t > 0 then helper t (h :: acc) else I.ret () :: h :: acc
          | Some pre ->
            if I.is_jump pre || I.is_cjump pre || I.is_return pre || I.is_raise pre
            then helper t (h :: acc)
            else (
              let l = I.get_label h in
              let jp = I.jump l in
              helper t (h :: jp :: acc)))
        else helper t (h :: acc)
    in
    helper instrs []
  ;;

  let print_bbs (bbs : bbmap) =
    printf "print bbs\n";
    Label.Map.iter bbs ~f:(fun bb -> printf "%s\n" (I.pp_insts bb.instrs))
  ;;

  let print_graph (g : map) =
    printf "print graph\n";
    Label.Map.iteri g ~f:(fun ~key:u ~data:vs ->
        printf "%s\n" (Label.name u);
        Label.Set.iter vs ~f:(fun v -> printf "  ->%s\n" (Label.name v)))
  ;;

  let rec _build_bb
      (instrs : i list)
      (bb_instrs : i list)
      (bb_label : Label.t option)
      (bbs : bbmap)
      : bbmap
    =
    match instrs with
    | [] ->
      (match bb_label with
      | None -> bbs
      | Some l ->
        let bb = { label = l; instrs = List.rev bb_instrs } in
        let bbs = Label.Map.set bbs ~key:l ~data:bb in
        bbs)
    | h :: t ->
      if I.is_label h
      then (
        match bb_label with
        | None ->
          entry := I.get_label h;
          _build_bb t [ h ] (Some (I.get_label h)) bbs
        | Some l ->
          let bb = { label = l; instrs = List.rev bb_instrs } in
          let bbs = Label.Map.set bbs ~key:l ~data:bb in
          _build_bb t [ h ] (Some (I.get_label h)) bbs)
      else _build_bb t (h :: bb_instrs) bb_label bbs
  ;;

  (* Build basic blocks. Update entry block label *)
  let build_bb (instrs : i list) : bbmap =
    let instrs = eliminate_fall_through instrs in
    let bb_instrs = [] in
    let bb_label = None in
    let bbs = Label.Map.empty in
    let bbs = _build_bb instrs bb_instrs bb_label bbs in
    (* print_bbs bbs; *)
    bbs
  ;;

  (* Given edges between u and vs, update ins and outs adjacent graph *)
  let update_u_vs (u : Label.t) (vs : Label.t list) (ins : map) (outs : map) : map * map =
    let vs_old =
      match Label.Map.find outs u with
      | None -> Label.Set.empty
      | Some s -> s
    in
    let vs_new = Label.Set.union (Label.Set.of_list vs) vs_old in
    let outs' = Label.Map.set outs ~key:u ~data:vs_new in
    let ins' =
      List.fold vs ~init:ins ~f:(fun acc v ->
          let v_in_old =
            match Label.Map.find acc v with
            | None -> Label.Set.empty
            | Some s -> s
          in
          let v_in_new = Label.Set.add v_in_old u in
          Label.Map.set acc ~key:v ~data:v_in_new)
    in
    ins', outs'
  ;;

  (* Build up ins and outs graph for each label. 
   * Update exits labels. *)
  let build_ino (bbs : bbmap) : map * map =
    let rec helper u instrs ins outs =
      match instrs with
      | [] -> update_u_vs u [] ins outs
      | h :: t ->
        if I.is_jump h || I.is_cjump h
        then (
          let vs = I.next h in
          let ins', outs' = update_u_vs u vs ins outs in
          helper u t ins' outs')
        else if I.is_return h || I.is_assert h || I.is_raise h
        then (
          exits := u :: !exits;
          let ins', outs' = update_u_vs u [] ins outs in
          helper u t ins' outs')
        else helper u t ins outs
    in
    let ins = Label.Map.map bbs ~f:(fun _ -> Label.Set.empty) in
    let outs = Label.Map.map bbs ~f:(fun _ -> Label.Set.empty) in
    let ins, outs =
      Label.Map.fold bbs ~init:(ins, outs) ~f:(fun ~key:_ ~data:bb acc_map ->
          let ins', outs' = acc_map in
          let u, instrs = bb.label, bb.instrs in
          helper u instrs ins' outs')
    in
    (* print_graph ins; *)
    (* print_graph outs; *)
    ins, outs
  ;;

  let is_edge (u : Label.t) (v : Label.t) (outs : map) : bool =
    let s = Label.Map.find_exn outs u in
    Label.Set.mem s v
  ;;

  (* For edge e from block u -> block v.
   * If block u has >= 2 successors and block v has >= 2 predecessors,
   * then edge e is a critical edge. 
   * We need to add a block w to eliminate this critical edge.
   * New graph would be : block u -> block w -> block v. 
   * Now neither u nor v has critical edges.
   * Other blocks topological remains unchanged. *)
  let is_critical_edge (u : Label.t) (v : Label.t) (ins : map) (outs : map) : bool =
    assert (is_edge u v outs);
    (* outs[u] >= 2 *)
    let cond1 = Label.Set.length (Label.Map.find_exn outs u) >= 2 in
    (* ins[v] >= 2 *)
    let cond2 = Label.Set.length (Label.Map.find_exn ins v) >= 2 in
    if cond1 && cond2 then true else false
  ;;

  (* Split edge from u -> v
   * New topology: u -> w -> v. Block w only has one instruction: jump to v.
   * Return updated basic block map, ins, and outs.
   *)
  let split_edge (u : Label.t) (v : Label.t) (bbs : bbmap) (ins : map) (outs : map)
      : bbmap * map * map
    =
    (* Replace label l with l' *)
    (* printf "split edge %s -> %s\n" (Label.name u) (Label.name v); *)
    let rec helper (l : Label.t) (l' : Label.t) (instrs : i list) (ret : i list) : i list =
      match instrs with
      | [] -> List.rev ret
      | h :: t ->
        if I.is_jump h && List.mem (I.next h) l ~equal:Label.equal
        then (
          let h' = I.replace_target h l' in
          helper l l' t (h' :: ret))
        else if I.is_cjump h && List.mem (I.next h) l ~equal:Label.equal
        then (
          let h' = I.replace_ctarget h l l' in
          helper l l' t (h' :: ret))
        else helper l l' t (h :: ret)
    in
    assert (is_edge u v outs);
    let w = Label.label (Some "w") in
    let bb_w = { label = w; instrs = [ I.label w; I.jump v ] } in
    (* update block w *)
    let bbs = Label.Map.set bbs ~key:w ~data:bb_w in
    let ins = Label.Map.set ins ~key:w ~data:(Label.Set.of_list [ u ]) in
    let outs = Label.Map.set outs ~key:w ~data:(Label.Set.of_list [ v ]) in
    (* update block u *)
    let u_out = Label.Set.remove (Label.Map.find_exn outs u) v in
    let u_out = Label.Set.add u_out w in
    let outs = Label.Map.set outs ~key:u ~data:u_out in
    let bb_u = Label.Map.find_exn bbs u in
    let instrs = helper v w bb_u.instrs [] in
    let bb_u' = { bb_u with instrs } in
    let bbs = Label.Map.set bbs ~key:u ~data:bb_u' in
    (* update block v *)
    let v_in = Label.Set.remove (Label.Map.find_exn ins v) u in
    let ins = Label.Map.set ins ~key:v ~data:v_in in
    bbs, ins, outs
  ;;

  let remove_criticl_edges (bbs : bbmap) (ins : map) (outs : map) : bbmap * map * map =
    Label.Map.fold outs ~init:(bbs, ins, outs) ~f:(fun ~key:u ~data:vs acc ->
        Label.Set.fold vs ~init:acc ~f:(fun acc v ->
            let bbs', ins', outs' = acc in
            if is_critical_edge u v ins' outs'
            then split_edge u v bbs' ins' outs'
            else acc))
  ;;

  let postorder (outs : map) : Label.t list =
    let rec helper
        (visited : set)
        (cur_label : Label.t)
        (outs : map)
        (order : Label.t list)
        : set * Label.t list
      =
      let visited = Label.Set.add visited cur_label in
      let succ =
        match Label.Map.find outs cur_label with
        | None -> Label.Set.empty
        | Some s -> s
      in
      let visited, order =
        Label.Set.fold succ ~init:(visited, order) ~f:(fun acc child ->
            let visited_acc, order_acc = acc in
            if Label.Set.mem visited_acc child
            then acc
            else helper visited_acc child outs order_acc)
      in
      visited, order @ [ cur_label ]
    in
    let _, order = helper Label.Set.empty !entry outs [] in
    order
  ;;

  let print_idom (doms : Label.t option Label.Map.t) : unit =
    printf "print idom\n";
    Label.Map.iteri doms ~f:(fun ~key:child ~data:parent ->
        match parent with
        | Some s -> printf "%s -> %s\n" (Label.name s) (Label.name child)
        | None -> printf "root: %s" (Label.name child))
  ;;

  (* The higher the order, the closer to the root of the tree. 
   * Needs info from label to integer order and reverse. *)
  let intersect (b1 : Label.t) (b2 : Label.t) doms order_map : Label.t =
    let rec helper finger1 finger2 =
      let i1 = Label.Map.find_exn order_map finger1 in
      let i2 = Label.Map.find_exn order_map finger2 in
      if i1 = i2
      then finger1
      else if i1 < i2
      then (
        let finger1_pred = Label.Map.find_exn doms finger1 in
        let finger1_pred =
          match finger1_pred with
          | None -> failwith "intersect expect predecessor processed"
          | Some s -> s
        in
        helper finger1_pred finger2)
      else (
        let finger2_pred = Label.Map.find_exn doms finger2 in
        let finger2_pred =
          match finger2_pred with
          | None -> failwith "intersect expect predecessor processed"
          | Some s -> s
        in
        helper finger1 finger2_pred)
    in
    let finger1 = b1 in
    let finger2 = b2 in
    helper finger1 finger2
  ;;

  let rec _idom' doms (rev_porder : Label.t list) (preds : map) order_map =
    let changed = false in
    let doms, changed =
      List.fold rev_porder ~init:(doms, changed) ~f:(fun acc b ->
          let doms, _ = acc in
          let preds_b = Label.Map.find_exn preds b |> Label.Set.to_list in
          let new_idom =
            List.find preds_b ~f:(fun pred_b ->
                match Label.Map.find_exn doms pred_b with
                | None -> false
                | Some _ -> true)
          in
          let new_idom =
            match new_idom with
            | None ->
              failwith
                (sprintf
                   "by rev_porder, %s has at least one processed predecessor"
                   (Label.name b))
            | Some s -> s
          in
          let new_idom =
            List.fold preds_b ~init:new_idom ~f:(fun new_idom p ->
                match Label.Map.find_exn doms p with
                | None -> new_idom
                | Some _ -> intersect p new_idom doms order_map)
          in
          let changed =
            match Label.Map.find_exn doms b with
            | None -> true
            | Some s -> if phys_equal s new_idom then false || changed else true
          in
          let doms = Label.Map.set doms ~key:b ~data:(Some new_idom) in
          doms, changed)
    in
    _idom changed doms rev_porder preds order_map

  and _idom
      (changed : bool)
      (doms : (Label.t, Label.t option, Label.comparator_witness) Map_intf.Map.t)
      (rev_porder : Label.t list)
      (preds : map)
      order_map
    =
    if not changed then doms else _idom' doms rev_porder preds order_map
  ;;

  (* Check http://www.hipersoft.rice.edu/grads/publications/dom14.pdf figure 3 for details.
   * For simplity, I use same notation as original algorithms.
   * Though variable doms may be misleading, it is in fact immediate dominator map. *)
  let idom (porder : Label.t list) (preds : map) : Label.t option Label.Map.t =
    let doms =
      List.fold porder ~init:Label.Map.empty ~f:(fun acc l ->
          Label.Map.set acc ~key:l ~data:None)
    in
    let start_node, tails =
      match List.rev porder with
      | [] -> failwith "empty porder"
      | h :: t -> h, t
    in
    let doms = Label.Map.set doms ~key:start_node ~data:(Some start_node) in
    let rev_porder = tails in
    let order_map =
      List.foldi porder ~init:Label.Map.empty ~f:(fun i acc label ->
          Label.Map.set acc ~key:label ~data:i)
    in
    let doms_raw = _idom true doms rev_porder preds order_map in
    let ret =
      Label.Map.map doms_raw ~f:(fun idom ->
          match idom with
          | Some s -> Some s
          | None -> failwith "dom not processed")
    in
    Label.Map.set ret ~key:(get_entry ()) ~data:None
  ;;

  (* Pseudo code check http://www.hipersoft.rice.edu/grads/publications/dom14.pdf Figure 5 *)
  let build_DF (doms : Label.t option Label.Map.t) (preds : map) : map =
    let rec helper runner (b : Label.t) (dom_b : Label.t) df : map =
      if phys_equal b dom_b
      then df
      else (
        let df_runner =
          match Label.Map.find df runner with
          | None -> Label.Set.empty
          | Some s -> s
        in
        let df_runner' = Label.Set.add df_runner b in
        let df = Label.Map.set df ~key:runner ~data:df_runner' in
        let runner = Label.Map.find_exn doms runner in
        match runner with
        | Some runner ->
          if phys_equal runner (get_entry ()) then df else helper runner b dom_b df
        | None -> failwith "should not happen")
    in
    let df = Label.Map.map doms ~f:(fun _ -> Label.Set.empty) in
    let nodes = Label.Map.keys doms in
    List.fold nodes ~init:df ~f:(fun acc b ->
        let preds_b =
          match Label.Map.find preds b with
          | Some s -> s
          | None -> Label.Set.empty
        in
        if Label.Set.length preds_b >= 2
        then
          Label.Set.fold preds_b ~init:acc ~f:(fun acc pred ->
              let runner = pred in
              let dom_b = Label.Map.find_exn doms b in
              match dom_b with
              | Some dom_b -> helper runner b dom_b acc
              | None -> failwith "should not happen")
        else acc)
  ;;

  let build_DT (doms : Label.t option Label.Map.t) : map =
    let dt = Label.Map.empty in
    Label.Map.fold doms ~init:dt ~f:(fun ~key:child ~data:par acc ->
        match par with
        | Some par ->
          let children =
            match Label.Map.find acc par with
            | None -> Label.Set.empty
            | Some s -> s
          in
          let children' = Label.Set.add children child in
          Label.Map.set acc ~key:par ~data:children'
        | None -> acc)
  ;;

  let print_DT (dt : map) order : unit =
    printf "print DT order:\n%!";
    List.iter order ~f:(fun l -> printf "%s %!" (Label.name l));
    printf "\n%!";
    List.iter order ~f:(fun par ->
        printf "%s\n" (Label.name par);
        match Label.Map.find dt par with
        | None -> ()
        | Some children ->
          Label.Set.iter children ~f:(fun child -> printf "  -> %s\n" (Label.name child)))
  ;;

  let to_instrs (bbs : bbmap) (order : Label.t list) =
    List.map order ~f:(fun l ->
        let bb = Label.Map.find_exn bbs l in
        bb.instrs)
    |> List.concat
  ;;
end
