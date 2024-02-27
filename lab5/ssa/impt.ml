open Core
module Label = Util.Label

module Wrapper =
functor
  (Instr : Sig.InstrInterface)
  (CFG : Cfg.Sig.CFGInterface with type i = Instr.i)
  ->
  struct
    type pair = Instr.t * Label.t
    type bb = CFG.bb

    type ssa_bb =
      { phis : pair list
      ; block : bb
      }

    module StMap = Map.Make (Instr)

    type st = Instr.t
    type ssa_bbmap = ssa_bb Label.Map.t (* Hash table: label -> ssa basic block *)

    let param_label = Label.label (Some "params")

    let insert_param_block (params : Instr.t list) : Instr.i list =
      let label = Instr.label param_label in
      label :: List.map params ~f:(fun param -> Instr.assign param 0L)
    ;;

    let delete_param_block (bbs : CFG.bbmap) : CFG.bbmap =
      Label.Map.remove bbs param_label
    ;;

    (* Insert phi and generate ssa basic block map. *)
    let construct (bbs : CFG.bbmap) (df : CFG.map) : ssa_bbmap =
      (* orig records block defined sized temporary. block -> st list
       * defsites records locations each sized temporary is defined *)
      let init_bb (bb : bb) (orig : st list Label.Map.t) (defsites : Label.t list StMap.t)
          : st list Label.Map.t * Label.t list StMap.t
        =
        List.fold bb.instrs ~init:(orig, defsites) ~f:(fun acc inst ->
            let orig, defsites = acc in
            let inst_defs = Instr.get_def inst in
            let bb_defs =
              match Label.Map.find orig bb.label with
              | None -> []
              | Some s -> s
            in
            let orig = Label.Map.set orig ~key:bb.label ~data:(inst_defs @ bb_defs) in
            let defsites =
              List.fold inst_defs ~init:defsites ~f:(fun acc def ->
                  let old_list =
                    match StMap.find acc def with
                    | None -> []
                    | Some s -> s
                  in
                  StMap.set acc ~key:def ~data:(bb.label :: old_list))
            in
            orig, defsites)
      in
      (* phis records location(s) for each sized temporary to insert phi *)
      let rec helper
          (var : st)
          (q : Label.t list)
          (df : CFG.map)
          (orig : st list Label.Map.t)
          (phis : Label.Set.t StMap.t)
          : Label.Set.t StMap.t
        =
        match q with
        | [] -> phis
        | u :: t ->
          let df_u = Label.Map.find_exn df u in
          let phis, q' =
            Label.Set.fold df_u ~init:(phis, t) ~f:(fun acc v ->
                let phis, t = acc in
                (* v is dominator frontier of u *)
                let phi_v =
                  match StMap.find phis var with
                  | None -> Label.Set.empty
                  | Some s -> s
                in
                if Label.Set.mem phi_v v
                then phis, t
                else (
                  let phi_v = Label.Set.add phi_v v in
                  let phis = StMap.set phis ~key:var ~data:phi_v in
                  let orig_v = Label.Map.find_exn orig v in
                  if List.mem orig_v var ~equal:phys_equal then phis, t else phis, v :: t))
          in
          helper var q' df orig phis
      in
      let orig, defsites =
        Label.Map.fold
          bbs
          ~init:(Label.Map.empty, StMap.empty)
          ~f:(fun ~key:_ ~data:bb acc ->
            let orig, defsites = acc in
            init_bb bb orig defsites)
      in
      let vs = StMap.keys defsites in
      let phis =
        List.fold vs ~init:StMap.empty ~f:(fun acc v ->
            let defs_v = StMap.find_exn defsites v in
            helper v defs_v df orig acc)
      in
      failwith ""
    ;;

    let decompose (ssa_bbs : ssa_bbmap) : CFG.bbmap = failwith ""
    let rename = failwith ""
    let renameBB = failwith ""

    let run (params : Instr.t list) (instrs_body : Instr.i list) : CFG.bbmap =
      let instrs_head = insert_param_block params in
      let instrs = instrs_head @ instrs_body in
      let bbs = CFG.build_bb instrs in
      let succs, preds = CFG.build_ino bbs in
      let bbs', succs, preds = CFG.remove_criticl_edges bbs succs preds in
      let porder = CFG.postorder succs in
      let idom = CFG.idom porder preds in
      let df = CFG.build_DF idom preds in
      let dt = CFG.build_DT idom in
      let ssa_bbs = construct bbs' df in
      delete_param_block bbs'
    ;;
  end
