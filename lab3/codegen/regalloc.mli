module Temp = Temp.Temp
module Register = Register.X86_reg.Register
module Reg_info = Program

type reg = Register.t
type temp = Temp.t
type allocations = (temp * temp) option list

val build_graph : Reg_info.temps_info -> Temp.Set.t Temp.Map.t

val gen_reg_table : Reg_info.line list -> Temp.Set.t Temp.Map.t -> int Temp.Map.t

val print_adj : Temp.Set.t Temp.Map.t -> unit

val seo : Temp.Set.t Temp.Map.t -> Reg_info.line list -> temp list

val greedy : temp list -> Temp.Set.t Temp.Map.t -> reg Temp.Map.t -> reg Temp.Map.t

val regalloc : Reg_info.temps_info -> (temp * reg) option list

val print_tmp_to_reg : reg Temp.Map.t -> unit