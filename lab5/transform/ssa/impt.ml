(*
 * Minimal SSA
 *
 * We use dominance frontier to construct minimal SSA. We only insert phi function for variables at dominance frontier.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

module Label = Util.Label
module Temp = Var.Temp

module Make
    (Instr : Sig.SSAInstrInterface)
    (Cfg : Analysis_cfg.Sig.CFGInterface)
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
end
