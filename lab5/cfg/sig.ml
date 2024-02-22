(* Signatures to follow
 * 
 * Any level of instructions can generate control flow graph(CFG)
 * as long as they obey InstrInterface signature. 
 * 
 * Given instructions following InstrInterface, functor will
 * construct control flow graph, and it follows CFInterface.
 *
 * CFG has one entry and one or more exit block(s), each block is linked through
 * either jump or cjump. No fall through edge is allowed between blocks.
 * Entry block has no predecessor and one or multiple successor(s), exit block has at
 * least one predecessor and no successor. 
 *
 * CFG constructor will not add new blocks to the original graph.
 * Though it will modify each block to end up with jump, cjump, raise or return.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module Label = Util.Label

module type InstrInterface = sig
  type t

  val is_label : t -> bool
  val is_jump : t -> bool

  (* Cond jump means it will jump to one of the targets.
   * Je is not cond jump because it only jump when equal meet. *)
  val is_cjump : t -> bool
  val is_return : t -> bool
  val is_assert : t -> bool
  val is_raise : t -> bool
  val label : Label.t -> t
  val jump : Label.t -> t
  val ret : unit -> t
  val get_label : t -> Label.t

  (* Given jump/conditional jump, return target label list. *)
  val next : t -> Label.t list

  (* Replace target of Jump *)
  val replace_target : t -> Label.t -> t

  (* Replace old target to new target for CJump *)
  val replace_ctarget : t -> Label.t -> Label.t -> t
  val pp_insts : t list -> string
  val pp_inst : t -> string
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

  val get_entry : unit -> Label.t
  val get_exits : unit -> Label.t list

  (* Return basic blocks. Add entry and exit block automatically. *)
  val build_bb : i list -> bbmap
  val eliminate_fall_through : i list -> i list

  (* Get in and out edge for each label *)
  val build_ino : bbmap -> map * map
  val is_critical_edge : Label.t -> Label.t -> map -> map -> bool
  val split_edge : Label.t -> Label.t -> bbmap -> map -> map -> bbmap * map * map
  val postorder : map -> Label.t list
  val print_bbs : bbmap -> unit
  val print_graph : map -> unit
  val to_instrs : bbmap -> Label.t list -> i list
end
