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
 * CFG provides dominator functions. Algorithm details check:
 * http://www.hipersoft.rice.edu/grads/publications/dom14.pdf
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
module Label = Util.Label

module type InstrInterface = sig
  type i

  val is_label : i -> bool
  val is_jump : i -> bool

  (* Cond jump means it will jump to one of the targets.
   * Je is not cond jump because it only jump when equal meet. *)
  val is_cjump : i -> bool
  val is_return : i -> bool
  val is_assert : i -> bool
  val is_raise : i -> bool
  val label : Label.t -> i
  val jump : Label.t -> i
  val ret : unit -> i
  val get_label : i -> Label.t

  (* Given jump/conditional jump, return target label list. *)
  val next : i -> Label.t list

  (* Replace target of Jump *)
  val replace_target : i -> Label.t -> i

  (* Replace old target to new target for CJump *)
  val replace_ctarget : i -> Label.t -> Label.t -> i
  val pp_insts : i list -> string
  val pp_inst : i -> string
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

  (* Return basic blocks. *)
  val build_bb : i list -> bbmap

  (* Get in and out edge for each label *)
  val build_ino : bbmap -> map * map
  val remove_criticl_edges : bbmap -> map -> map -> bbmap * map * map
  val postorder : map -> Label.t list

  (* Calculate immediate dominator. 
   * node idom[b] immediate dominate node b.
   * entry node does not have immediate dominator. 
   * idom[entry] is None. All other nodes have immediate dominator. *)
  val idom : Label.t list -> map -> Label.t option Label.Map.t

  (* Calculate dominator frontier.
   * df[b] is dominator frontier of node b. *)
  val build_DF : Label.t option Label.Map.t -> map -> map

  (* Calculate dominator tree.
   * dt[b] are children of node b in dominator tree *)
  val build_DT : Label.t option Label.Map.t -> map
  val print_idom : Label.t option Label.Map.t -> unit
  val print_DT : map -> Label.t list -> unit
  val print_bbs : bbmap -> unit
  val print_graph : map -> unit
  val to_instrs : bbmap -> Label.t list -> i list
end
