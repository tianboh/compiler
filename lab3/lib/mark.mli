(* L1 Compiler
 *
 * Library for associating asts with positions in the source file.
 * This is not necessary for a working compiler, but can lead to
 * better error messages. To create a marked ast without a position
 * in the source file, you can use "Mark.naked".
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Annotations / bugfixes: Alex Vaynberg <alv@andrew.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified by Nick Roberts <nroberts@alumni.cmu.edu>
 *)

(* Location in the source file. *)
type src_loc =
  { line : int
  ; col : int
  }

(* Span of locations in the source file. *)
type src_span =
  { start_loc : src_loc
  ; end_loc : src_loc
  ; file : string
  }

val of_position : Lexing.position -> src_loc
val of_positions : Lexing.position -> Lexing.position -> src_span
val show : src_span -> string (* converts the data into human readable form *)

type 'a t (* value paired with a src_span *)

(* INTRODUCTION FUNCTIONS for type 'a marked *)

(* put together a value and positional information *)
val mark : 'a -> src_span -> 'a t

(* put together a value and an option of positional information *)
val mark' : 'a -> src_span option -> 'a t

(* mark the value with no positional information *)
val naked : 'a -> 'a t

(* ELIMINATION FUNCTIONS for type a' marked *)

(* data: remove the markings *)
val data : 'a t -> 'a

(* ext: retrieve src_span information from marked value *)
val src_span : 'a t -> src_span option

(* USEFUL TOOLS *)

(* wrap:
 * Merges the src_spans in the list, returning None if the merge
 * isn't possible (i.e., the src_spans belong to different files).
 *)
val wrap : src_span option list -> src_span option

(* map: make your function keep positional information *)
val map : f:('a -> 'b) -> 'a t -> 'b t

(* map': similar to map, but f can now use positional information
 * and preserve it at the same time
 *)
val map' : f:('a t -> 'b) -> 'a t -> 'b t
