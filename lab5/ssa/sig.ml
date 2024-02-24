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

module type SSAInterface = sig
  type phi
  type t

  val construct : t -> t
  val decompose : t -> t
  val insert_param_block : t -> t
  val delete_param_block : t -> t
  val place_phi : t -> t
  val rename : t -> t
  val renameBB : t -> t
end

module type InstrInterface = sig
  type t

  val get_def : t -> Temp.t list
  val get_uses : t -> Temp.t list

  (* Tuple stands for (old_temp, ssa_temp) *)
  val replace_def : t -> (Temp.t * Temp.t) list -> t
  val replace_uses : t -> (Temp.t * Temp.t) list -> t
  val pp_insts : t list -> string
  val pp_inst : t -> string
end
