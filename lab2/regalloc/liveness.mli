(* L2 liveness analysis
 * Given a pseudo assembly code, liveness analysis
 * uses dataflow analysis to generate live-out set
 * for each instruction. This information will be 
 * used for reg_alloc_info.
 *
 * Notice that in liveness analysis, gen set of a 
 * statement is its rhs, and kill set is its defination.
 * Also, if a variable appears in both lhs and rhs,
 * then it is only stay in gen set and not in kill set.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
open Core
module Dfana_info = Json_reader.Lab2_checkpoint
module AS = Inst.Pseudo
module Temp = Var.Temp
module Register = Var.X86_reg
module Dfana = Flow.Dfana

val gen_liveness : 
    AS.instr list ->
    (int, (Temp.t, Temp.comparator_witness) Set_intf.Set.t,
     Core.Int.comparator_witness)
    Map_intf.Map.t
val print_line : Dfana_info.line -> unit
val print_df_info : Dfana_info.line list -> unit
val print_liveout : (int list * int list * int) list -> unit