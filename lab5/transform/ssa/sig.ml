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
end

module type SSAInterface = sig
  type phi = Label.t
  type ssa_bbmap
end
