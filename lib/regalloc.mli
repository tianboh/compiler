open Lab1_checkpoint
type node = 
  { reg : reg
  ; mutable order : int (* order for SEO *)
  ; mutable is_alloc : bool (* whether is allocated during SEO*)
  }

type interference_graph = (node * node list) list;;

val regalloc : program -> allocations
