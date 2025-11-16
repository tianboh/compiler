(*
 * Dominator tree signature
 * Dominator tree is constructed by CFG, and provide more functions
 * Algorithm reference https://www.cs.tufts.edu/~nr/cs257/archive/keith-cooper/dom14.pdf
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

module Label = Util.Label
(* open Core *)

module type DominatorInterface = sig
  type bbmap

  (* Build dominator tree from control flow bbmap.
   * Return a dominator tree map dtmap. 
   * Given a node u, Label.Map.find_exn dtmap u returns u's immediate dominator *)
  val build_dt : bbmap -> Label.t Label.Map.t

  (* Build dominance frontier using cfg and dominator tree. 
   * Dominance frontier is expressed as Label.Set.t Label.Map.t
   * Given a node u for df, return u's dominance frontier *)
  val build_df : bbmap -> Label.t Label.Map.t -> Label.Set.t Label.Map.t
end
