open Lab1_checkpoint

val build_graph : program ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t

val gen_line_to_tmp : line list -> (int, reg) Base.Hashtbl.t

val gen_reg_table : line list -> (reg, 'a) Base.Hashtbl.t -> (reg, int) Base.Hashtbl.t

val print_adj : (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t -> unit

val pre_fix : line list -> (reg, reg) Base.Hashtbl.t

val seo : (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t ->
  line list -> (reg, 'b) Base.Hashtbl.t -> reg list

val greedy : reg list ->
  (reg, (reg, 'a) Base.Set.t) Base.Hashtbl.t ->
  (reg, reg) Base.Hashtbl.t -> (reg, reg) Base.Hashtbl.t

val regalloc : program -> allocations

val print_tmp_to_reg : (reg, reg) Base.Hashtbl.t -> unit