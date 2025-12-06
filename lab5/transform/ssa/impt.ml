(*
 * Minimal SSA
 *
 * We use dominance frontier to construct minimal SSA. We only insert phi function 
 * for variables at dominance frontier.
 *
 * Alg paper: An Efficient Method of Computing Static Single Assignment Form  
 * Check https://dl.acm.org/doi/pdf/10.1145/75277.75280 for details
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

module Label = Util.Label
module Temp = Var.Temp
open Core

module Make
    (Instr : Sig.SSAInstrInterface)
    (Cfg : Analysis_cfg.Sig.CFGInterface with type i = Instr.instr)
    (Dom : Analysis_dominator.Sig.DominatorInterface with type bbmap = Cfg.bbmap) =
struct
  type phi = { dst : Temp.t; srcs : Temp.t Label.Map.t }
  type ssa_instr = Phi of phi | Instr of Instr.instr

  type ssa_bb = {
    label : Label.t;
    instrs : ssa_instr list;
    preds : Label.t list;
    succs : Label.t list;
  }

  type ssa_bbmap = ssa_bb Label.Map.t

  (* Collect every definition of temp. Key is temp, value is definition set. *)
  let collect_tmap (bbmap : Cfg.bbmap) : Label.Set.t Temp.Map.t =
    let tmap = ref Temp.Map.empty in
    Label.Map.iteri bbmap ~f:(fun ~key:label ~data:bb ->
        List.iter bb.instrs ~f:(fun instr ->
            List.iter (Instr.get_defs instr) ~f:(fun temp ->
                tmap :=
                  Temp.Map.update !tmap temp ~f:(function
                    | None -> Label.Set.singleton label
                    | Some set -> Label.Set.add set label))));
    !tmap

  (* This function only insert phi function for temporary. It does not rename
   * any other temporary name in neither LHS nor RHS. This is minimal SSA, 
   * so phi func is only inserted at dominance frontier.*)
  let insert_phi (temp : Temp.t) (defs : Label.Set.t) (bbmap : ssa_bbmap)
      (frontier : Label.Set.t Label.Map.t) : ssa_bbmap =
    let worklist = ref [] in
    let phi_guard = ref Label.Set.empty in
    let worklist_guard = ref Label.Set.empty in
    let ssa_bbmap = ref bbmap in
    Label.Set.iter defs ~f:(fun def ->
        worklist := def :: !worklist;
        worklist_guard := Label.Set.add !worklist_guard def);
    while not (List.is_empty !worklist) do
      let head = List.hd_exn !worklist in
      worklist := List.tl_exn !worklist;
      let head_frontier =
        match Label.Map.find frontier head with
        | Some s -> s
        | None -> Label.Set.empty
      in
      Label.Set.iter head_frontier ~f:(fun node ->
          if not (Label.Set.mem !phi_guard node) then (
            let phi_instr = Phi { dst = temp; srcs = Label.Map.empty } in
            let ssa_bb = Label.Map.find_exn !ssa_bbmap node in
            ssa_bbmap :=
              Label.Map.set !ssa_bbmap ~key:node
                ~data:{ ssa_bb with instrs = phi_instr :: ssa_bb.instrs };
            phi_guard := Label.Set.add !phi_guard node;
            if not (Label.Set.mem !worklist_guard node) then (
              worklist := node :: !worklist;
              worklist_guard := Label.Set.add !worklist_guard node)))
    done;
    !ssa_bbmap

  let to_ssa (bbmap : Cfg.bbmap) : ssa_bb Label.Map.t =
    let dom_tree = Dom.build_dt bbmap in
    let frontier = Dom.build_df bbmap dom_tree in
    let tmap = collect_tmap bbmap in
    let ssa_bbmap : ssa_bbmap =
      Label.Map.map bbmap ~f:(fun bb ->
          let ssa_instrs = List.map bb.instrs ~f:(fun instr -> Instr instr) in
          {
            label = bb.label;
            instrs = ssa_instrs;
            preds = bb.preds;
            succs = bb.succs;
          })
    in
    Temp.Map.fold tmap ~init:ssa_bbmap ~f:(fun ~key:temp ~data:defs acc ->
        insert_phi temp defs acc frontier)
end
