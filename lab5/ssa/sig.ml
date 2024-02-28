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
open Core
module Label = Util.Label
module Temp = Var.Temp

module type InstrInterface = sig
  type i (* Instruction *)

  type t [@@deriving sexp, compare, hash] (* Sized temporary *)

  val get_def : i -> t list
  val get_uses : i -> t list

  (* Tuple stands for (old_temp, ssa_temp) *)
  val replace_def : i -> (t * t) list -> i
  val replace_uses : i -> (t * t) list -> i

  (* Given t, generate a new t with same size *)
  val new_t : t -> t
  val label : Label.t -> i
  val assign : t -> Int64.t -> i
  val pp_insts : i list -> string
  val pp_inst : i -> string
end

module type SSAInterface = functor
  (Instr : InstrInterface)
  (CFG : Cfg.Sig.CFGInterface with type i = Instr.t)
  -> sig
  val run : CFG.bbmap -> CFG.bbmap
end
