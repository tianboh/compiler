module Label = Util.Label
open Core

module Make (C : Analysis_cfg.Sig.CFGInterface) :
  Sig.DominatorInterface with type bbmap = C.bbmap = struct
  type bbmap = C.bbmap

  (* Given u and v, return their first subcommon parent. *)
  let rec intersect (u : Label.t) (v : Label.t) (order : int Label.Map.t)
      (idom_tree : Label.t Label.Map.t) : Label.t =
    let o1 = Label.Map.find_exn order u in
    let o2 = Label.Map.find_exn order v in
    if o1 = o2 then u
    else if o1 < o2 then
      let p2 = Label.Map.find_exn idom_tree v in
      intersect u p2 order idom_tree
    else
      let p1 = Label.Map.find_exn idom_tree u in
      intersect p1 v order idom_tree

  (* Given a node u, find its processed preds *)
  let find_processed_preds (u : Label.t) (bbmap : bbmap)
      (idom_tree : Label.t Label.Map.t) : Label.t list =
    let u_bb = Label.Map.find_exn bbmap u in
    let preds = u_bb.preds in
    List.fold_left preds ~init:[] ~f:(fun acc pred ->
        if Label.Map.mem idom_tree pred then pred :: acc else acc)

  let idom (u : Label.t) (bbmap : bbmap) (order : int Label.Map.t)
      (idom_tree : Label.t Label.Map.t) : Label.t =
    let processed_preds = find_processed_preds u bbmap idom_tree in
    match processed_preds with
    | [] ->
        failwith
          "idom expect at least one processed pred as it is traversed by rpo"
    | h :: t ->
        List.fold_left t ~init:h ~f:(fun acc processed_pred ->
            intersect acc processed_pred order idom_tree)

  let build_dt (bbmap : bbmap) : Label.t Label.Map.t =
    (* Keep track of each block in reverse post order number. Key: bbmap label, value: index in rpo *)
    let order = ref Label.Map.empty in
    (* reverse post order for bbmap *)
    let rpo = ref [] in
    (* Trackes immediate dominator of each block *)
    let idom_tree = ref Label.Map.empty in
    (* Each bbmap corresponds to a function, init idom_tree and order for it *)
    let init (bbmap : bbmap) : unit =
      idom_tree := Label.Map.empty;
      order := Label.Map.empty;
      rpo := C.get_rpo bbmap;
      order :=
        List.foldi !rpo ~init:Label.Map.empty ~f:(fun index acc_map element ->
            Label.Map.set acc_map ~key:element ~data:index);
      let entry = List.hd_exn !rpo in
      idom_tree := Label.Map.set !idom_tree ~key:entry ~data:entry
    in
    init bbmap;
    let changed = ref true in
    let rpo_wo_entry = List.tl_exn !rpo in
    while !changed do
      changed := false;
      List.iter rpo_wo_entry ~f:(fun u ->
          let u_idom_new = idom u bbmap !order !idom_tree in
          match Label.Map.find !idom_tree u with
          | None ->
              idom_tree := Label.Map.set !idom_tree ~key:u ~data:u_idom_new;
              changed := true
          | Some u_idom_old ->
              if Label.equal u_idom_new u_idom_old then ()
              else (
                idom_tree := Label.Map.set !idom_tree ~key:u ~data:u_idom_new;
                changed := true))
    done;
    !idom_tree

  let build_df (bbmap : bbmap) (dt : Label.t Label.Map.t) :
      Label.Set.t Label.Map.t =
    (* C.pp_bbmap bbmap; *)
    let rpo = ref [] in
    let df = ref Label.Map.empty in
    (* Initialize df for every node *)
    Label.Map.iter_keys bbmap ~f:(fun node ->
        df := Label.Map.set !df ~key:node ~data:Label.Set.empty);
    rpo := C.get_rpo bbmap;
    (* Propagate dominace frontier using node *)
    let process_node (node : Label.t) : unit =
      let bb = Label.Map.find_exn bbmap node in
      let preds = bb.preds in
      if List.length preds >= 2 then
        let dom_node = Label.Map.find_exn dt node in
        List.iter preds ~f:(fun pred ->
            let runner = ref pred in
            while not (Label.equal !runner dom_node) do
              (let current_set = Label.Map.find_exn !df !runner in
               let new_set = Label.Set.add current_set node in
               df := Label.Map.set !df ~key:!runner ~data:new_set);
              runner := Label.Map.find_exn dt !runner
            done)
    in
    List.iter !rpo ~f:(fun node -> process_node node);
    !df
end
