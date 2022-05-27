(* C0 Compiler
 *
 * The front-end uses strings for variable names, but it's
 * expensive and wasteful to repeatedly compare strings.
 * Symbol is an abstract type that maintains the string information
 * but allows for cheaper comparisons.
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 *)

open Core

(* Suppose v1 and v2 are two values of type t.
 * Suppose that v1 was created from a call to "symbol s1",
 * and that v2 was created from a call to "symbol s2",
 * and that the call "symbol s1" was executed before "symbol s2".
 *
 * v1 will test as equal to v2 if s1 = s2.
 * v1 will test as less than v2 otherwise (since v1 was created
 * before v2).
 *)
type t [@@deriving compare, hash, sexp]

include Comparable.S with type t := t

val symbol : string -> t (* generates a new symbol with given name *)

val name : t -> string (* returns a name associated with symbol *)
