(*
 * Minimal SSA
 *
 * We use dominance frontier to construct minimal SSA. We only insert phi function for variables at dominance frontier.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module Label = Util.Label
module Temp = Var.Temp

module type SSAInstrInterface = sig
  type instr

  val get_defs : instr -> Temp.t list
  val get_uses : instr -> Temp.t list

  (* Given a instruction instr, replace temporary and return a new instruction
   * Notice that both source and destination are checked and replaced.
   * This function will be used in temporary renaming. *)
  val replace_temp : instr -> Temp.t -> Temp.t -> instr

  (* gen_mov is used when deconstructing phi node. *)
  val gen_mov : Temp.t -> Temp.t -> instr
  val pp_inst : instr -> string
end

module type S = sig
  type phi = { dst : Temp.t; srcs : Temp.t Label.Map.t }
  type instr
  type ssa_instr = Phi of phi | Instr of instr
  type cfg_bbmap
  type cfg_set

  type ssa_bb = {
    label : Label.t;
    instrs : ssa_instr list;
    preds : Label.t list;
    succs : Label.t list;
  }

  type ssa_bbmap = ssa_bb Label.Map.t

  val get_defs : ssa_instr -> Temp.t list
  val get_uses : ssa_instr -> Temp.t list
  val collect_tmap : cfg_bbmap -> cfg_set Temp.Map.t

  val insert_phi :
    Temp.t -> cfg_set -> ssa_bbmap -> cfg_set Label.Map.t -> ssa_bbmap

  val rename : ssa_bbmap -> Label.t -> cfg_set Label.Map.t -> ssa_bbmap
  val to_ssa : cfg_bbmap -> ssa_bbmap
  val from_ssa : ssa_bbmap -> cfg_bbmap
  val print_ssa_bbmap : ssa_bbmap -> unit
end

module type Make = functor
  (Instr : SSAInstrInterface)
  (Cfg : Analysis_cfg.Sig.CFGInterface with type i = Instr.instr)
  (Dom : Analysis_dominator.Sig.DominatorInterface with type bbmap = Cfg.bbmap)
  ->
  S
    with type instr = Instr.instr
     and type cfg_bbmap = Cfg.bbmap
     and type cfg_set = Cfg.set
