(* L2 Compiler
 * AST -> IR Translator
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 * Created: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified by: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)

(* translate abstract syntax tree to IR tree *)
val translate : Ast.program -> Tree.program
