open Core
module Label = Util.Label

module DFWrapper : Sig.Dataflow =
functor
  (CFG : Cfg.Sig.CFGInterface)
  (Info : Sig.Info)
  (Instr : sig
             type instr

             val get_gen : instr -> Info.Set.t
             val get_kill : instr -> Info.Set.t
           end
           with type instr = CFG.i)
  (DFType : Sig.DFType)
  ->
  struct
    type info = {
      gen_ : Info.Set.t;
      kill_ : Info.Set.t;
      in_ : Info.Set.t;
      out_ : Info.Set.t;
    }

    type instr = { instr : CFG.i; info : info }

    type bb = {
      label : Label.t;
      instrs : instr list;
      preds : Label.t list;
      succs : Label.t list;
      info : info;
    }

    type bbmap = bb Label.Map.t

    let pp_info (info : info) : string =
      let gen_str = info.gen_ |> Info.Set.sexp_of_t |> Sexp.to_string_hum in
      let kill_str = info.kill_ |> Info.Set.sexp_of_t |> Sexp.to_string_hum in
      let in_str = info.in_ |> Info.Set.sexp_of_t |> Sexp.to_string_hum in
      let out_str = info.out_ |> Info.Set.sexp_of_t |> Sexp.to_string_hum in
      sprintf "gen: %s, kill: %s, in: %s, out: %s" gen_str kill_str in_str
        out_str

    let pp_inst (instr : instr) : string =
      let instr_info = pp_info instr.info in
      let instr_code = CFG.pp_inst instr.instr in
      sprintf "instr: %s \t info: %s\n" instr_code instr_info

    let meet (i1 : Info.Set.t) (i2 : Info.Set.t) : Info.Set.t =
      match DFType.meet_type with
      | Sig.May -> Info.Set.union i1 i2
      | Sig.Must -> Info.Set.inter i1 i2

    let transfer (i : info) : Info.Set.t =
      match DFType.direction with
      | Sig.Forward -> Info.Set.union i.gen_ (Info.Set.inter i.in_ i.kill_)
      | Sig.Backward -> Info.Set.union i.gen_ (Info.Set.inter i.out_ i.kill_)

    let find_next_bb (cur_lab : Label.t) (bbmap : bbmap) : Label.t list =
      let bb = Label.Map.find_exn bbmap cur_lab in
      match DFType.direction with
      | Sig.Forward -> bb.succs
      | Sig.Backward -> bb.preds

    let get_empty_info () : info =
      {
        gen_ = Info.Set.empty;
        kill_ = Info.Set.empty;
        in_ = Info.Set.empty;
        out_ = Info.Set.empty;
      }

    let initBB (cfgbb : CFG.bb) : bb =
      let label = cfgbb.label in
      let preds = cfgbb.preds in
      let succs = cfgbb.succs in
      let info = get_empty_info () in
      let instrs =
        List.fold_left cfgbb.instrs ~init:[] ~f:(fun acc instr ->
            let instr_info = get_empty_info () in
            let gen = Instr.get_gen instr in
            let kill = Instr.get_kill instr in
            let instr_info = { instr_info with gen_ = gen; kill_ = kill } in
            let dfinstr = { instr; info = instr_info } in
            dfinstr :: acc)
        |> List.rev
      in
      { label; instrs; preds; succs; info }

    let initBBs (cfg_bbmap : CFG.bbmap) : bbmap =
      Label.Map.fold cfg_bbmap ~init:Label.Map.empty
        ~f:(fun ~key:label ~data:cfgbb acc ->
          let bb = initBB cfgbb in
          Label.Map.set acc ~key:label ~data:bb)

    let process_bb (bb : bb) : bb =
      let instrs = bb.instrs in
      let instrs_order =
        match DFType.direction with
        | Sig.Forward -> instrs
        | Sig.Backward -> List.rev instrs
      in
      (* Initialize first instruction in field. For backward, out field. 
       * Remember, first instruction in is the same as bb in.
       * Last instruction out is the same as block out *)
      let instrs_init =
        match instrs_order with
        | [] -> []
        | h :: t ->
            let info =
              match DFType.direction with
              | Sig.Forward -> { h.info with in_ = bb.info.in_ }
              | Sig.Backward -> { h.info with out_ = bb.info.out_ }
            in
            let instr = { h with info } in
            instr :: t
      in
      let rec helper (instrs : instr list) (prev_info : info option)
          (acc : instr list) : instr list =
        match instrs with
        | [] -> List.rev acc
        | h :: t ->
            let info =
              match DFType.direction with
              | Sig.Forward ->
                  let in_ =
                    match prev_info with
                    | None -> bb.info.in_
                    | Some prev_info -> prev_info.out_
                  in
                  let out_ = transfer { h.info with in_ } in
                  { h.info with in_; out_ }
              | Sig.Backward ->
                  let out_ =
                    match prev_info with
                    | None -> bb.info.out_
                    | Some prev_info -> prev_info.in_
                  in
                  let in_ = transfer { h.info with out_ } in
                  { h.info with in_; out_ }
            in
            let instr = { h with info } in
            helper t (Some info) (instr :: acc)
      in
      let instrs_refined = helper instrs_init None [] in
      let bb_info =
        match DFType.direction with
        | Sig.Forward ->
            let last = List.last_exn instrs_refined in
            { bb.info with out_ = last.info.out_ }
        | Sig.Backward ->
            let last = List.last_exn instrs_refined in
            { bb.info with in_ = last.info.in_ }
      in
      { bb with info = bb_info; instrs = instrs_refined }

    let rec process_bbs (bbmap : bbmap) (worklist : Label.t list) : bbmap =
      match worklist with
      | [] -> bbmap
      | h :: t -> (
          let bb_old = Label.Map.find_exn bbmap h in
          let bb_new = process_bb bb_old in
          let bbmap = Label.Map.set bbmap ~key:bb_old.label ~data:bb_new in
          match DFType.direction with
          | Sig.Forward ->
              if Info.Set.equal bb_old.info.out_ bb_new.info.out_ then
                process_bbs bbmap t
              else process_bbs bbmap (t @ bb_new.succs)
          | Sig.Backward ->
              if Info.Set.equal bb_old.info.in_ bb_new.info.in_ then
                process_bbs bbmap t
              else process_bbs bbmap (t @ bb_new.preds))

    let run (cfg_bbmap : CFG.bbmap) : bbmap =
      let start_block =
        match DFType.direction with
        | Sig.Forward -> CFG.get_entry cfg_bbmap
        | Sig.Backward -> CFG.get_exit cfg_bbmap
      in
      let bbmap = initBBs cfg_bbmap in
      process_bbs bbmap [ start_block.label ]

    let to_instrs (bbmap : bbmap) (label_order : Label.t list) : instr list =
      List.fold_left label_order ~init:[] ~f:(fun acc label ->
          let bb = Label.Map.find_exn bbmap label in
          let bb_instrs = bb.instrs in
          List.rev bb_instrs @ acc)
      |> List.rev
  end
