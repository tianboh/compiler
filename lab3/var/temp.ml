(* L1 Compiler
 * Temporaries
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 *)

open Core

module T = struct
  type t = int [@@deriving sexp, compare, hash]
end

include T

let counter = ref 1
let reset () = counter := 1

let create () =
  let t = !counter in
  incr counter;
  t
;;

let create_no (n : int) : t =
  let t = n in
  t
;;

let count () = !counter
let name t = "%t" ^ string_of_int t
let value t = t

include Comparable.Make (T)
