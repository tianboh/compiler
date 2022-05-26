(* L1 Compiler
 * Error messages
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Annotations: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *)

open Core

type t = { mutable error_count : int }

let create () : t = { error_count = 0 }
let has_any_errors : t -> bool = fun t -> t.error_count > 0

let print_msg (variety : string) (span : Mark.src_span option) ~(msg : string) =
  Option.iter span ~f:(fun x -> Out_channel.output_string stderr (Mark.show x));
  Out_channel.fprintf stderr ":%s:%s\n" variety msg
;;

let error (t : t) (span : Mark.src_span option) ~(msg : string) : unit =
  t.error_count <- t.error_count + 1;
  print_msg "error" span ~msg
;;

(* Prints a warning message, but does not record an error as having happened. *)
let warn (_ : t) (span : Mark.src_span option) ~(msg : string) : unit =
  print_msg "warning" span ~msg
;;

exception Error
