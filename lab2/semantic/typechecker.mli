(* L2 Compiler
 * TypeChecker
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 * Created: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * This type checker is part of the semantic analysis
 * It checkes whether each statement and expression is valid
 * 
 * Check https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab2.pdf
 * Section 4.1 for more details.
 *
 * Statement level check
 * 1) Check the expression of statement is of the correct type. 
 * For example, whether the expression of If.cond is Bool type.
 * 2) Check sub-statement is valid of a statement.
 * For example, whether Seq.head and Seq.tail is valid for Seq.
 * 3) Check variable re-declaration error, and assign without declare error.
 *
 * Expression level check
 * 1) Check whether the operand and operator consistent with each other.
 * 
 * We can summarize above checks to two cases
 * 1) Type check in statement and expression
 * 2) Variable declaration check, including re-decl and non-decl.
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Now distinguishes between declarations and initialization
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Should be more up-to-date with modern spec.
 * Modified: Matt Bryant <mbryant@andrew.cmu.edu> Fall 2015
 * Handles undefined variables in unreachable code, significant simplifications
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu> Fall 2018
 * Use records, redo marks.
 *)

(* prints error message and raises ErrorMsg.error if error found *)
val typecheck : Parser.Ast.program -> unit
