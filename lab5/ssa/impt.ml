open Core
module Label = Util.Label

module Wrapper =
functor
  (Instr : Sig.InstrInterface)
  (CFG : Cfg.Sig.CFGInterface with type i = Instr.i)
  ->
  struct
    (* dest temp, src temp *)
    type pair =
      { dest : Instr.t
      ; src : Instr.t
      }

    type bb = CFG.bb

    module K = struct
      type t =
        { st : Instr.t
        ; src : Label.t
        }
      [@@deriving sexp, compare, hash]

      let construct st src = { st; src }
      let decompose t = t.st, t.src
    end

    module PhiKey = Map.Make (K)

    type ssa_bb =
      { phis : Instr.t option PhiKey.t
      ; phi_asns : pair list
      ; block : bb
      }

    module StMap = Map.Make (Instr)

    type st = Instr.t
    type ssa_bbmap = ssa_bb Label.Map.t (* Hash table: label -> ssa basic block *)

    (* Track variable name during renaming. *)
    type stack = st list StMap.t

    let param_label = Label.label (Some "params")

    let insert_param_block (params : Instr.t list) : Instr.i list =
      let label = Instr.label param_label in
      label :: List.map params ~f:(fun param -> Instr.assign param 0L)
    ;;

    let delete_param_block (ssa_bbmap : ssa_bbmap) : CFG.bbmap =
      let ssa_bbmap = Label.Map.remove ssa_bbmap param_label in
      Label.Map.map ssa_bbmap ~f:(fun ssa_bb -> ssa_bb.block)
    ;;

    (* Insert phi and generate ssa basic block map. *)
    let construct (bbs : CFG.bbmap) (df : CFG.map) (preds : CFG.map) : ssa_bbmap * stack =
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
          let df_u =
            match Label.Map.find df u with
            | None -> Label.Set.empty (* root or leaf does not have dominator frontier *)
            | Some s -> s
          in
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
      let ssa_bbmap : ssa_bbmap =
        Label.Map.map bbs ~f:(fun bb ->
            { block = bb; phis = PhiKey.empty; phi_asns = [] })
      in
      let ssa_bbmap =
        StMap.fold phis ~init:ssa_bbmap ~f:(fun ~key:st ~data:locs (acc : ssa_bbmap) ->
            Label.Set.fold
              locs
              ~init:(acc : ssa_bbmap)
              ~f:(fun acc loc ->
                let loc_ssa_bb = Label.Map.find_exn acc loc in
                let preds_loc = Label.Map.find_exn preds loc in
                let loc_phi =
                  Label.Set.fold preds_loc ~init:loc_ssa_bb.phis ~f:(fun acc pred ->
                      let key = K.construct st pred in
                      PhiKey.set acc ~key ~data:None)
                in
                Label.Map.set acc ~key:loc ~data:{ loc_ssa_bb with phis = loc_phi }))
      in
      let stack =
        List.fold vs ~init:StMap.empty ~f:(fun acc v -> StMap.set acc ~key:v ~data:[ v ])
      in
      ssa_bbmap, stack
    ;;

    (* Add move in predecessors to remove phi function at dominator frontier *)
    let[@warning "-27"] decompose (ssa_bbs : ssa_bbmap) : CFG.bbmap = failwith ""

    (* Rename basic block and its successors *)
    let rec rename_BB
        (bb_name : Label.t)
        (ssa_bbmap : ssa_bbmap)
        (stack : stack)
        (dt : CFG.map)
        (succs : CFG.map)
        : ssa_bbmap * stack
      =
      (* Rename def use within block *)
      let bb = Label.Map.find_exn ssa_bbmap bb_name in
      let ssa_bb, stack, defs = rename_BB_inside bb stack in
      let ssa_bbmap = Label.Map.set ssa_bbmap ~key:bb_name ~data:ssa_bb in
      (* Rename block successors phi function *)
      let children = Label.Map.find_exn succs bb_name in
      let ssa_bbmap =
        Label.Set.fold children ~init:ssa_bbmap ~f:(fun ssa_bbmap_acc child ->
            rename_BB_succs ssa_bbmap_acc stack bb_name child)
      in
      (* Rename block dominator frontier *)
      let frontier =
        match Label.Map.find dt bb_name with
        | None -> Label.Set.empty
        | Some s -> s
      in
      let ssa_bbmap, stack =
        Label.Set.fold frontier ~init:(ssa_bbmap, stack) ~f:(fun acc child ->
            let ssa_bbmap_acc, stack_acc = acc in
            rename_BB child ssa_bbmap_acc stack_acc dt succs)
      in
      (* Pop block defined variable *)
      let stack =
        List.fold defs ~init:stack ~f:(fun stack_acc def ->
            let def_stack = StMap.find_exn stack_acc def in
            let def_stack' =
              match def_stack with
              | [] -> failwith "def stack empty"
              | _ :: t -> t
            in
            StMap.set stack_acc ~key:def ~data:def_stack')
      in
      ssa_bbmap, stack

    and (* Rename def and use in instructions. *)
        rename_BB_inside
        (bb : ssa_bb)
        (stack : stack)
        : ssa_bb * stack * st list
      =
      (* Rename phi dest *)
      let ts =
        PhiKey.keys bb.phis
        |> List.map ~f:(fun tuple ->
               let st, _ = K.decompose tuple in
               st)
      in
      let stack, phi_asns =
        List.fold ts ~init:(stack, []) ~f:(fun acc t ->
            let stack_acc, phi_asns_acc = acc in
            let stack_t = StMap.find_exn stack_acc t in
            let t_ssa = Instr.new_t t in
            let stack_t_new = t_ssa :: stack_t in
            let phi_asn = { dest = t_ssa; src = t } in
            let stack_acc_new = StMap.set stack_acc ~key:t ~data:stack_t_new in
            let phi_asn_acc_new = phi_asn :: phi_asns_acc in
            stack_acc_new, phi_asn_acc_new)
      in
      (* Rename instr def and use in body *)
      let instrs = bb.block.instrs in
      let ssa_instrs_rev, stack, defs =
        List.fold instrs ~init:([], stack, []) ~f:(fun acc instr ->
            let ssa_instrs_acc_rev, stack_instrs_acc, defs_acc = acc in
            printf "%s\n%!" (Instr.pp_inst instr);
            let uses = Instr.get_uses instr in
            let uses_ssa =
              List.map uses ~f:(fun v ->
                  let v_stack = StMap.find_exn stack_instrs_acc v in
                  let v_top = List.hd_exn v_stack in
                  v_top)
            in
            let map_uses = List.zip_exn uses uses_ssa in
            let instr_ssa_uses = Instr.replace_uses instr map_uses in
            let defs = Instr.get_def instr in
            let defs_acc = defs @ defs_acc in
            let defs_ssa, stack_def =
              List.fold defs ~init:([], stack_instrs_acc) ~f:(fun acc v ->
                  let defs_ssa_acc, stack_def_acc = acc in
                  let v_new = Instr.new_t v in
                  let v_stack = StMap.find_exn stack_def_acc v in
                  let stack_def_acc =
                    StMap.set stack_def_acc ~key:v ~data:(v_new :: v_stack)
                  in
                  defs_ssa_acc @ [ v_new ], stack_def_acc)
            in
            let map_defs = List.zip_exn defs defs_ssa in
            let instr_ssa = Instr.replace_def instr_ssa_uses map_defs in
            instr_ssa :: ssa_instrs_acc_rev, stack_def, defs_acc)
      in
      let block = { bb.block with instrs = List.rev ssa_instrs_rev } in
      let ssa_bb = { bb with block; phi_asns } in
      ssa_bb, stack, defs

    (* Rename phi function operands *)
    and rename_BB_succs
        (ssa_bbmap : ssa_bbmap)
        (stack : stack)
        (par : Label.t)
        (child : Label.t)
        : ssa_bbmap
      =
      let child_ssa_bb = Label.Map.find_exn ssa_bbmap child in
      let phi_key =
        PhiKey.keys child_ssa_bb.phis
        |> List.filter ~f:(fun tuple ->
               let _, pred = K.decompose tuple in
               Label.equal pred par)
      in
      let phis =
        List.fold phi_key ~init:child_ssa_bb.phis ~f:(fun phis_acc key ->
            let t, _ = K.decompose key in
            let t_stack = StMap.find_exn stack t in
            let t_top = List.hd_exn t_stack in
            PhiKey.set phis_acc ~key ~data:(Some t_top))
      in
      let child_ssa_bb' = { child_ssa_bb with phis } in
      Label.Map.set ssa_bbmap ~key:child ~data:child_ssa_bb'
    ;;

    let run (params : Instr.t list) (instrs_body : Instr.i list) : Instr.i list =
      let instrs_head = insert_param_block params in
      let instrs = instrs_head @ instrs_body in
      let bbs = CFG.build_bb instrs in
      let preds, succs = CFG.build_ino bbs in
      let bbs', preds, succs = CFG.remove_criticl_edges bbs preds succs in
      let porder = CFG.postorder succs in
      let idom = CFG.idom porder preds in
      let df = CFG.build_DF idom preds in
      let dt = CFG.build_DT idom in
      (* CFG.print_bbs bbs'; *)
      let ssa_bbs, stack = construct bbs' df preds in
      let entry = param_label in
      let[@warning "-26"] ssa_bbs, _ = rename_BB entry ssa_bbs stack dt succs in
      let ssa_bbs = delete_param_block ssa_bbs in
      let topoorder = List.rev porder in
      let valid_order =
        (* remove param label *)
        match topoorder with
        | [] -> failwith "empty"
        | _ :: t -> t
      in
      CFG.to_instrs ssa_bbs valid_order
    ;;
  end
