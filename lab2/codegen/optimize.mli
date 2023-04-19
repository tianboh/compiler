(* L2 pseudo code optimizer
 *
 * Optimization contains 
 * 1) Const propagation
 * 2) temp propagation
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu> 
 *)

module AS = Inst.Pseudo

val optimize : AS.instr list -> AS.instr list 
val copy_propagation : AS.instr list -> AS.instr list
val const_propagation : AS.instr list -> AS.instr list