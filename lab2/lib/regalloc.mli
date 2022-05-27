open Lab1_checkpoint

val build_graph : program ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t

val gen_reg_table : line list -> (reg, int) Base.Hashtbl.t

val print_adj : (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t -> unit

val seo : (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t -> line list -> reg list

val greedy : reg list ->
  (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t ->
  (reg, reg) Base.Hashtbl.t -> (reg, reg) Base.Hashtbl.t

val regalloc : program -> allocations

val print_tmp_to_reg : (reg, reg) Base.Hashtbl.t -> unit