open Lab1_checkpoint

val build_ori_adj_hash : program ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t

val build_mut_adj_hash : program ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t

val gen_line_to_tmp : line list -> (int, reg) Base.Hashtbl.t

val gen_reg_table : program -> (reg, int) Base.Hashtbl.t

val print_adj : (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t -> unit

val pre_color : line list -> (reg, Assem.reg) Base.Hashtbl.t

val seo : (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t -> program -> reg list

val greedy : reg list ->
  (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t ->
  (reg, Assem.reg) Base.Hashtbl.t -> (reg, Assem.reg) Base.Hashtbl.t

val regalloc : program -> allocations
