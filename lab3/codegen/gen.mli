(* L1 Compiler
 * Assembly Code Generator for FAKE assembly
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Implements a "convenient munch" algorithm
 *)
 module AS = Inst.Pseudo
 module Temp = Temp.Temp
 module Register = Register.X86_reg.Register
 module AS_x86 = Inst.X86

 module Pseudo : sig 
     val gen : Parser.Tree.stm list -> AS.instr list
 end

 (* module Pseudo_x86 : sig
    val gen : Parser.Tree.stm list -> AS.instr list
 end *)

 module X86 : sig
     val gen : AS.instr list -> (Temp.t * Register.t) option list -> AS_x86.instr list
 end