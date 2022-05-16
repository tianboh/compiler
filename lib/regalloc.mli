open Lab1_checkpoint

val build_ori_adj_hash : program ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t

val build_mut_adj_hash : program ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t

val gen_line_to_tmp : line list -> (int, reg) Base.Hashtbl.t

val gen_reg_table : program -> (reg, int) Base.Hashtbl.t

val seo : (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t -> (reg, int) Base.Hashtbl.t -> reg list

val regalloc : program -> allocations
