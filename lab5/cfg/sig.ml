(* Signatures to follow
 * 
 * Any level of instructions can generate control flow graph(CFG)
 * as long as they obey InstrInterface signature. 
 * 
 * Given instructions following InstrInterface, functor will
 * construct control flow graph, and it follows CFInterface.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module Label = Util.Label

module type InstrInterface = sig
  type t

  val is_label : t -> bool
  val is_jump : t -> bool
  val is_return : t -> bool
  val is_assert : t -> bool
  val label : Label.t -> t
  val jump : Label.t -> t
  val ret : unit -> t
  val get_label : t -> Label.t

  (* Given current instruction, current block label, and next instruction
   * return label(s) of next instruction. *)
  val next : t -> Label.t -> t -> Label.t list

  (* Replace target of Jump *)
  val replace_target : t -> Label.t -> t

  (* Replace target_true or target_false for CJump *)
  val replace_ctarget : t -> bool -> Label.t -> t
end

module type CFGInterface = sig
  type i (* instruction *)

  (* Basic block, node in CFG *)
  type bb =
    { label : Label.t
    ; instrs : i list
    }

  type bbmap = bb Label.Map.t (* Hash table: label -> basic block *)

  type set = Label.Set.t
  type map = set Label.Map.t (* Graph: key: label, value: label set *)

  val get_entry : unit -> bb
  val get_exit : unit -> bb

  (* Return basic blocks. Add entry and exit block automatically. *)
  val build_bb : i list -> bbmap

  (* Get in and out edge for each label *)
  val build_ino : bbmap -> map * map
  val split_critical_edge : bbmap -> map -> map -> bbmap * map * map
  val postorder : set -> Label.t -> map -> Label.t list -> Label.t list
  val to_instrs : bbmap -> i list
end
