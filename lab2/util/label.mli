(* C0 Compiler
 *
 * Label is used as target of Jump and CJump.
 * 
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

open Core

(* Suppose v1 and v2 are two values of type t.
 * Suppose that v1 was created from a call to "label s1",
 * and that v2 was created from a call to "label s2",
 * and that the call "label s1" was executed before "label s2".
 *
 * v1 will test as equal to v2 if s1 = s2.
 * v1 will test as less than v2 otherwise (since v1 was created
 * before v2).
 *)
type t [@@deriving compare, hash, sexp]

include Comparable.S with type t := t

val label : string option -> t (* generates a new label with given name *)

val name : t -> string (* returns a name associated with label *)

val content : t -> string