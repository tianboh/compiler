(* Signatures to follow
 * 
 * Any level of instructions can generate control flow graph(CFG)
 * as long as they obey InstrInterface signature. 
 * 
 * Given instructions following InstrInterface, functor will
 * construct control flow graph, and it follows CFInterface.
 *
 * CFG has one entry and one exit block, each block is linked through
 * either jump or cjump. No fall through edge is allowed between blocks.
 * Jump instruction is inserted if fallthrough is detected from original code.
 * Each block is guaranteed to terminated with a terminator.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module Label = Util.Label

module type InstrInterface = sig
  type t

  val is_label : t -> bool
  val is_jump : t -> bool
  val is_cjump : t -> bool
  val is_return : t -> bool
  val is_assert : t -> bool
  val label : Label.t -> t
  val jump : Label.t -> t
  val ret : unit -> t

  (* Given label instr, get its label. Used to transform type *)
  val get_label : t -> Label.t

  (* Given jump/conditional jump, return target label list. *)
  val get_targets : t -> Label.t list

  (* Replace target of Jump *)
  val replace_target : t -> Label.t -> t

  (* Replace old target to new target for CJump *)
  val replace_ctarget : t -> Label.t -> Label.t -> t
end

module type CFGInterface = sig
  type i (* instruction *)

  (* Basic block, node in CFG *)
  type bb = {
    label : Label.t;
    instrs : i list;
    preds : Label.t list;
    succs : Label.t list;
  }

  type bbmap = bb Label.Map.t (* Hash table: label -> basic block *)
  type set = Label.Set.t
  type map = set Label.Map.t (* Graph: key: label, value: label set *)

  val get_entry : bbmap -> bb
  val get_exit : bbmap -> bb

  (* Return basic blocks. Add entry and exit block automatically. *)
  val build_bb : i list -> bbmap * Label.t list
  val to_instrs : bbmap -> Label.t list -> i list
end
