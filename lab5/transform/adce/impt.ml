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
              Ssa.get_defs instr @ Ssa.get_uses instr @ acc
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
    ssa_bbmap
end
