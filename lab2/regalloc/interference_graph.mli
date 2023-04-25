open Core
module X86_reg = Var.X86_reg
module Temp = Var.Temp

module Vertex : sig
    module T : sig 
        type t = Reg of X86_reg.t | Temp of Temp.t
    end
    type t = T.t
    include Comparable.S with type t := T.t
end
  
module Edge : sig
    module T : sig
        type t = Vertex.T.t * Vertex.T.t [@@deriving compare, hash, sexp]
    end
    type t = T.t
    include Comparable.S with type t := T.t
end

type t = {
    vertices : Vertex.T.t list;
    edges : Edge.T.t list;
}

module Print : sig
    val pp_vertex : Vertex.T.t -> string
    val pp_edge : Edge.T.t -> string
    val pp_graph : t -> string
end
