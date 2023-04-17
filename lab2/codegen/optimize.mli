(* L1 optimizer
 * Optimizer for pseudo assembly code
 * 1) Const propagation
 * 2) temp propagation
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu> 
 *)

module AS = Inst.Pseudo

val optimize : AS.instr list -> AS.instr list 