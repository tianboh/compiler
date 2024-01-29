(* Implementation for CFG wrapper
 * Provide a instruction module following
 * Sig.InstrInterface, return a module with
 * CFG helper functions.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu> 
 *)

module Label = Util.Label
open Core

module Wrapper (I : Sig.InstrInterface) : Sig.CFGInterface with type i = I.t = struct
  type set = Label.Set.t
  type map = set Label.Map.t
  type i = I.t

  type bb =
    { label : Label.t
    ; instrs : i list
    }

  type bbmap = bb Label.Map.t

  let entry_label = Label.label (Some "entry")
  let exit_label = Label.label (Some "exit")
  let entry_bb = { label = entry_label; instrs = [ I.label entry_label ] }
  let exit_bb = { label = exit_label; instrs = [ I.label exit_label ] }
  let get_entry () : bb = entry_bb
  let get_exit () : bb = exit_bb
  let add_entry_exit (instrs : i list) = entry_bb.instrs @ instrs @ exit_bb.instrs

  (* A basic block should end up with one of following possibilities
   * 1) Jump or conditional jump
   * 2) Return 
   *)
  let has_fall_through (instrs : i list) (pre_opt : i option) : bool =
    let rec helper (instrs : i list) (pre_opt : i option) (res : bool) : bool =
      match instrs with
      | [] -> res
      | h :: t ->
        if I.is_label h
        then (
          match pre_opt with
          | None -> if List.length t > 0 then helper t (Some h) res else false
          | Some pre ->
            if I.is_jump pre || I.is_cjump pre || I.is_return pre
            then helper t (Some h) res
            else helper t (Some h) true)
        else helper t (Some h) res
    in
    helper instrs pre_opt false
  ;;

  (* Eliminate fall through between block and block. 
   * Only use jump/cjump to go through blocks.
   * This helps to build control flow graph, and these 
   * redundant jumps will be eliminated in optimization pass. *)
  let rec eliminate_fall_through (instrs : i list) (acc : i list) : i list =
    match instrs with
    | [] -> List.rev acc
    | h :: t ->
      if I.is_label h
      then (
        let pre_opt = List.hd acc in
        match pre_opt with
        | None ->
          if List.length t > 0
          then eliminate_fall_through t (h :: acc)
          else I.ret () :: h :: acc
        | Some pre ->
          if I.is_jump pre || I.is_cjump pre || I.is_return pre
          then eliminate_fall_through t (h :: acc)
          else (
            let l = I.get_label h in
            let jp = I.jump l in
            eliminate_fall_through t (h :: jp :: acc)))
      else eliminate_fall_through t (h :: acc)
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
        | None -> _build_bb t [ h ] (Some (I.get_label h)) bbs
        | Some l ->
          let bb = { label = l; instrs = List.rev bb_instrs } in
          let bbs = Label.Map.set bbs ~key:l ~data:bb in
          _build_bb t [ h ] (Some l) bbs)
      else _build_bb t (h :: bb_instrs) bb_label bbs
  ;;

  (* Build basic blocks with entry and exit block *)
  let build_bb (instrs : i list) : bbmap =
    if has_fall_through instrs None
    then failwith "build_bb need to eliminate fall through edge first.";
    let instrs = add_entry_exit instrs in
    let bb_instrs = [] in
    let bb_label = None in
    let bbs = Label.Map.empty in
    _build_bb instrs bb_instrs bb_label bbs
  ;;

  (* Given edges between u and vs, update ins and outs adjacent graph *)
  let update_u_vs (u : Label.t) (vs : Label.t list) (ins : map) (outs : map) : map * map =
    let vs_old = Label.Map.find_exn outs u in
    let vs_new = Label.Set.union (Label.Set.of_list vs) vs_old in
    let outs' = Label.Map.set outs ~key:u ~data:vs_new in
    let ins' =
      List.fold vs ~init:ins ~f:(fun acc v ->
          let v_in_old = Label.Map.find_exn acc v in
          let v_in_new = Label.Set.union v_in_old (Label.Set.of_list [ u ]) in
          Label.Map.set acc ~key:v ~data:v_in_new)
    in
    ins', outs'
  ;;

  (* Build up ins and outs graph for each label. *)
  let build_ino (bbs : bbmap) : map * map =
    let ins = Label.Map.empty in
    let outs = Label.Map.empty in
    Label.Map.fold bbs ~init:(ins, outs) ~f:(fun ~key:_ ~data:bb acc_map ->
        let ins', outs' = acc_map in
        let u, instrs = bb.label, bb.instrs in
        List.fold instrs ~init:(ins', outs') ~f:(fun acc_list instr ->
            let ins'', outs'' = acc_list in
            if I.is_jump instr || I.is_cjump instr
            then (
              let vs = I.next instr in
              update_u_vs u vs ins'' outs'')
            else if I.is_return instr || I.is_assert instr
            then (
              let vs = [ exit_label ] in
              update_u_vs u vs ins'' outs'')
            else ins'', outs''))
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
    let bb_w = { label = w; instrs = [ I.jump v ] } in
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

  let postorder (outs : map) : Label.t list =
    let rec helper
        (visited : set)
        (cur_label : Label.t)
        (outs : map)
        (order : Label.t list)
        : set * Label.t list
      =
      let visited = Label.Set.add visited cur_label in
      let succ = Label.Map.find_exn outs cur_label in
      let visited, order =
        Label.Set.fold succ ~init:(visited, order) ~f:(fun acc child ->
            let visited_acc, order_acc = acc in
            if Label.Set.mem visited_acc child
            then acc
            else helper visited_acc child outs order_acc)
      in
      visited, order @ [ cur_label ]
    in
    let _, order = helper Label.Set.empty entry_label outs [] in
    order
  ;;

  let to_instrs (bbs : bbmap) (order : Label.t list) =
    List.map order ~f:(fun l ->
        let bb = Label.Map.find_exn bbs l in
        bb.instrs)
    |> List.concat
  ;;
end
