(*
 * Aggresive Dead Code Elimination(ADCE)
 *
 * ADCE assumes every instruction is dead unless provide otherwise.
 * It relies on a worklist to mark instruction liveness. Instructions with
 * side effect(memwrite, return, function call) is marked lives initially.
 * Then their operands is marked and propagate.
 *
 * Once done, each instruction is flaged live or not. Then remove all dead
 * instructions.
 * 
 * Notice, ADCE is worked on SSA because it provides trivial def-use chain.
 * Without SSA, a temporary may have multiple definition, and it's hard to
 * figure out whether it has side effect, and where to propagate.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module Label = Util.Label
module Temp = Var.Temp

module type ADCEInstrInterface = sig
  type instr

  (* Instructions with following cases are considered side-effect in ADCE
   * 1) Mem write
   * 2) Return
   * 3) Function call
   * 4) Push/Pop, it modifies %rsp
   * 5) Jump/Cjump, change CFG
   * 6) Div/Mod
   * 7) Label, similar to Jump/Cjump logic
   *)
  val has_side_effect : instr -> bool

  (* Need to know what variables an instruction defines and uses.
   * This information is used to propagate temporaries.
   *)
  val get_defs : instr -> Temp.t list
  val get_uses : instr -> Temp.t list
end

module type S = sig
  type ssa_bbmap

  val run : ssa_bbmap -> ssa_bbmap
end

module type Make = functor
  (Instr : ADCEInstrInterface)
  (Ssa : Ssa.Sig.S with type instr = Instr.instr)
  -> S with type ssa_bbmap = Ssa.ssa_bbmap
