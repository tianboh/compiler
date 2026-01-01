open Core
module Label = Util.Label
module Temp = Var.Temp

module Make
    (Instr : Sig.ADCEInstrInterface)
    (Ssa : Ssa.Sig.S with type instr = Instr.instr) =
struct
  type ssa_bbmap = Ssa.ssa_bbmap

  let has_side_effect (instr : Ssa.ssa_instr) : bool =
    match instr with
    | Ssa.Phi _ -> false
    | Ssa.Instr i -> Instr.has_side_effect i

  let init_worklist (ssa_bbmap : Ssa.ssa_bbmap) : Temp.t list =
    Label.Map.fold ssa_bbmap ~init:[] ~f:(fun ~key:_ ~data:ssa_bb acc_bbs ->
        List.fold ssa_bb.instrs ~init:acc_bbs ~f:(fun acc instr ->
            if has_side_effect instr then
              List.rev_append (Ssa.get_uses instr) acc
            else acc))

  (* defmap tracks temp -> instr that defines it
   * Since ADCE is based on SSA, this defmap is a one-to-one mapping.
   *)
  let init_defmap (ssa_bbmap : Ssa.ssa_bbmap) : Ssa.ssa_instr Temp.Map.t =
    let (defmap : Ssa.ssa_instr Temp.Map.t ref) = ref Temp.Map.empty in
    Label.Map.iter ssa_bbmap ~f:(fun ssa_bb ->
        List.iter ssa_bb.instrs ~f:(fun instr ->
            List.iter (Ssa.get_defs instr) ~f:(fun def ->
                defmap := Temp.Map.set !defmap ~key:def ~data:instr)));
    !defmap

  let run (ssa_bbmap : Ssa.ssa_bbmap) : Ssa.ssa_bbmap =
    let (worklist : Temp.t list ref) = ref [] in
    let (live_set : Temp.Set.t ref) = ref Temp.Set.empty in
    let (defmap : Ssa.ssa_instr Temp.Map.t ref) = ref Temp.Map.empty in
    worklist := init_worklist ssa_bbmap;
    live_set := Temp.Set.of_list !worklist;
    defmap := init_defmap ssa_bbmap;
    while not (List.is_empty !worklist) do
      let live_temp = List.hd_exn !worklist in
      worklist := List.tl_exn !worklist;
      match Temp.Map.find !defmap live_temp with
      | Some instr ->
          List.iter (Ssa.get_uses instr) ~f:(fun use ->
              if not (Temp.Set.mem !live_set use) then (
                worklist := use :: !worklist;
                live_set := Temp.Set.add !live_set use))
      | None -> ()
    done;
    let (ret : Ssa.ssa_bbmap ref) = ref Label.Map.empty in
    Label.Map.iter ssa_bbmap ~f:(fun ssa_bb ->
        let instrs =
          List.filter ssa_bb.instrs ~f:(fun instr ->
              let temp_set = Temp.Set.of_list (Ssa.get_defs instr) in
              let inter_set = Temp.Set.inter temp_set !live_set in
              (not (Temp.Set.is_empty inter_set)) || has_side_effect instr)
        in
        let adce_ssa_bb = { ssa_bb with instrs } in
        ret := Label.Map.set !ret ~key:adce_ssa_bb.label ~data:adce_ssa_bb);
    !ret
end
