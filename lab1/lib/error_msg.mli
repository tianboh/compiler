(* L1 Compiler
 * Mutable data structure for recording errors.
 *
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Annotations: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *)

type t

val create : unit -> t
val has_any_errors : t -> bool

(* Prints an error message, and records an error as having happened at a source
 * location in the file.
 *)
val error : t -> Mark.src_span option -> msg:string -> unit

(* Prints a warning message, but does not record an error as having happened. *)
val warn : t -> Mark.src_span option -> msg:string -> unit

(* Raise this error to halt execution of the compiler.
 * (The top-level should be the only piece of code that handles this exception.)
 *)
exception Error
