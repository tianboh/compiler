(*
 * This is data flow analysis. It is based on CFG. We use gen and kill instead of def use
 * because former term has more meaning while the latter one is used in liveness.
 * This framework can handle both forward/backward, must/may analysis.
 *
 * We define a module T as information module. As long as one module has sexp and compare
 * function, we can treat it as information. In liveness analysis, T is Temp module.
 * Gen, kill, in, out are both expressed with information set because df analysis mainly 
 * rely on set operations to process.
 * 
 * Remember gen and kill needs more concrete syntax, so you need to provide Info to functor.
 * Check liveness module for example.
 *
 * Author: Tianbo Hao<tianboh@alumni.cmu.edu>
 *)

module Label = Util.Label
open Core

(*
 * Gen, kill, in, out is expressed by Info.t.
 * Each analysis may have different type of Info.t. For example, liveness analysis 
 * uses Temp.t as t.
 *)
module type Info = sig
  type t [@@deriving sexp, compare]

  module Set : Set.S with type Elt.t = t
end

type direction = Forward | Backward
type meet_op = Must | May

module type DFType = sig
  val meet_type : meet_op
  val direction : direction
end

module type Dataflow = functor
  (CFG : Analysis_cfg.Sig.CFGInterface)
  (Info : Info)
  (Instr : sig
             type instr

             val get_gen : instr -> Info.Set.t
             val get_kill : instr -> Info.Set.t
           end
           with type instr = CFG.i)
  (DFType : DFType)
  -> sig
  (* In liveness analysis, Info is temporary module *)
  type info = {
    gen_ : Info.Set.t;
    kill_ : Info.Set.t;
    in_ : Info.Set.t;
    out_ : Info.Set.t;
  }

  type instr = { instr : CFG.i; info : info }

  type bb = {
    label : Label.t;
    instrs : instr list;
    preds : Label.t list;
    succs : Label.t list;
    info : info;
  }

  type bbmap = bb Label.Map.t

  val meet : Info.Set.t -> Info.Set.t -> Info.Set.t
  val transfer : info -> Info.Set.t
  val get_empty_info : unit -> info

  (* convert from CFGBB to Dataflow BB. info of bb is empty. Gen and kill of each instr is filled. *)
  val initBB : CFG.bb -> bb
  val initBBs : CFG.bbmap -> bbmap
  val find_next_bb : Label.t -> bbmap -> Label.t list
  val process_bb : bb -> bb
  val process_bbs : bbmap -> Label.t -> bbmap
  val run : CFG.bbmap -> bbmap
  val to_instrs : bbmap -> Label.t list -> instr list
  val pp_info : info -> string
  val pp_inst : instr -> string
end
