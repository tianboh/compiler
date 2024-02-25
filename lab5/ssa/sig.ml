(* SSA is constructed on top of CFG.
 * 
 * SSA will add a entry block based on CFG because
 * fdefn has parameter passing process, which is not
 * shown in the function body. This entry block will
 * just assign 0 to parameters, and will be deleted 
 * after SSA is constructed. Since SSA is not run 
 * at this stage, this extra block will not influence
 * the expected result.
 *
 * SSA will only work on temporaries. SSA will not
 * modify memory related variables. 
 *
 * For example, consider instruction load mem to temp. 
 * SSA will modify temp, but leave mem the same as before.
 * Same logic applies for store instruction as well.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module Label = Util.Label
module Temp = Var.Temp

module type InstrInterface = sig
  type t (* Instruction *)

  type st (* Sized temporary *)

  val get_def : t -> st list
  val get_uses : t -> st list

  (* Tuple stands for (old_temp, ssa_temp) *)
  val replace_def : t -> (st * st) list -> t
  val replace_uses : t -> (st * st) list -> t
  val label : Label.t -> t
  val assign : st -> Int64.t -> t
  val pp_insts : t list -> string
  val pp_inst : t -> string
end

module type SSAInterface = functor
  (Instr : InstrInterface)
  (CFG : Cfg.Sig.CFGInterface with type i = Instr.t)
  -> sig
  val run : CFG.bbmap -> CFG.bbmap
end
