open Core
module Abs_asm = Abs_asm.Inst
module X86_reg = Var.X86_reg.Logic
module Temp = Var.Temp

module Vertex = struct
  module T = struct
    type t =
      | Reg of X86_reg.t
      | Temp of Temp.t
    [@@deriving compare, hash, sexp]
  end

  include T
  include Comparable.Make (T)

  let of_abs (operand : Abs_asm.Op.t) =
    match operand with
    | Abs_asm.Op.Temp t -> Set.of_list [ Temp t ]
    | Abs_asm.Op.Imm _ | Abs_asm.Op.Above_frame _ -> Set.empty
    | Abs_asm.Op.Reg r -> Set.of_list [ Reg r ]
  ;;
end

module Edge = struct
  module T = struct
    type t = Vertex.t * Vertex.t [@@deriving compare, hash, sexp]
  end

  include T
  include Comparable.Make (T)
end

type t =
  { vertices : Vertex.t list
  ; edges : Edge.t list
  }

module Print = struct
  open Printf

  let pp_vertex = function
    | Vertex.Reg reg -> X86_reg.pp reg
    | Vertex.Temp temp -> Temp.name temp
  ;;

  let pp_edge (u, v) = sprintf "(%s, %s)" (pp_vertex u) (pp_vertex v)

  let rec pp_vertices = function
    | [] -> ""
    | vertex :: vertices -> pp_vertex vertex ^ "\n" ^ pp_vertices vertices
  ;;

  let rec pp_edges = function
    | [] -> ""
    | edge :: edges -> pp_edge edge ^ "\n" ^ pp_edges edges
  ;;

  let pp_graph g =
    sprintf
      "vertices:\n%s\ninterference edges\n%s\n"
      (pp_vertices g.vertices)
      (pp_edges g.edges)
  ;;
end
