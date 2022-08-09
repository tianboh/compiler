(* L1 Compiler
 * Temporaries
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 *)

open Core

type t = int [@@deriving sexp, compare, hash]

let counter = ref 1
let reset () = counter := 1

let create () =
  let t = !counter in
  incr counter;
  t
;;

let name t = "%t" ^ string_of_int t

include Comparable.Make (Int)
