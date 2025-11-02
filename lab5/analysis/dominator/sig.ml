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

  (* Given a node u, Label.Map.find_exn u returns u's immediate dominator *)
  type tree = Label.t Label.Map.t

  (* Build immediate dominator map from control flow bbmap *)
  val build_idom : bbmap -> tree
end
