open Lab1_checkpoint
type node = 
  { reg : reg
  ; mutable order : int (* order for SEO *)
  ; mutable is_alloc : bool (* whether is allocated during SEO*)
  }

type interference_graph = (node * node list) list;;

val build_ori_adj_hash : program ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t

val build_mut_adj_hash : program ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t ->
  (reg, (reg, Base.String.comparator_witness) Base.Set.t) Base.Hashtbl.t

val regalloc : program -> allocations
