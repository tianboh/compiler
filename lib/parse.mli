(* L1 Compiler
 * Parsing
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Gluing together the pieces produced by ocamllex and menhir.
 *)

(* parse filename = ast
 * will raise Error_msg.Error in case of lexing or parsing error
 *)
val parse : string -> Ast.program
