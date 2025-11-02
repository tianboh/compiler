module Label = Util.Label
open Core

module Make (C : Analysis_cfg.Sig.CFGInterface) :
  Sig.DominatorInterface with type bbmap = C.bbmap = struct
  type bbmap = C.bbmap
  type tree = Label.t Label.Map.t

  (* Trackes immediate dominator of each block *)
  let idom_tree = ref Label.Map.empty

  (* Keep track of each block in reverse post order number. Key: bbmap label, value: index in rpo *)
  let order = ref Label.Map.empty

  (* reverse post order for bbmap *)
  let rpo = ref []

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

  (* Given u and v, return their first subcommon parent. *)
  let rec intersect (u : Label.t) (v : Label.t) : Label.t =
    let o1 = Label.Map.find_exn !order u in
    let o2 = Label.Map.find_exn !order v in
    if o1 = o2 then u
    else if o1 < o2 then
      let p2 = Label.Map.find_exn !idom_tree v in
      intersect u p2
    else
      let p1 = Label.Map.find_exn !idom_tree u in
      intersect p1 v

  (* Given a node u, find its processed preds *)
  let find_processed_preds (u : Label.t) (bbmap : bbmap) : Label.t list =
    let u_bb = Label.Map.find_exn bbmap u in
    let preds = u_bb.preds in
    List.fold_left preds ~init:[] ~f:(fun acc pred ->
        if Label.Map.mem !idom_tree pred then pred :: acc else acc)

  let idom (u : Label.t) (bbmap : bbmap) : Label.t =
    let processed_preds = find_processed_preds u bbmap in
    match processed_preds with
    | [] ->
        failwith
          "idom expect at least one processed pred as it is traversed by rpo"
    | h :: t ->
        List.fold_left t ~init:h ~f:(fun acc processed_pred ->
            intersect acc processed_pred)

  let build_idom (bbmap : bbmap) : tree =
    init bbmap;
    let changed = ref true in
    let rpo_wo_entry = List.tl_exn !rpo in
    while !changed do
      changed := false;
      List.iter rpo_wo_entry ~f:(fun u ->
          let u_idom_new = idom u bbmap in
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
end
