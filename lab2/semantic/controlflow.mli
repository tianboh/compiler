(* 
 * Controlflow analysis
 *
 * Control flow check is part of semantic analysis.
 * It will check
 * 1) Whether each AST element has return
 * 2) Whether a variable is used before initialization.
 * 
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)

val cf_ret : Parser.Ast.program -> unit
val cf_init : Parser.Ast.program -> unit
