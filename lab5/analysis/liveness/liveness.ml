open Core
module QCFG = Cfg.Impt.Wrapper (Quads.Inst)

(* module LivenessInfo = struct
  type t = Var.Temp.t [@@deriving sexp, compare]

  module Set = Set.Make (Var.Temp)
end *)

module LivenessInfo = Regalloc.Interference_graph.Vertex

module LivenessType = struct
  let meet_type = Mydf.Sig.May
  let direction = Mydf.Sig.Backward
end

module LivenessInstr = struct
  include Quads.Inst
  include LivenessInfo

  let sop_to_vertex (sop : Sop.t) : t option =
    match sop.data with Temp t -> Some (Temp t) | Imm _ -> None

  let st_to_vertex (st : St.t) : t = Temp (St.to_t st)

  let to_vertex (sop_list : Sop.t list) (st_list : St.t list) : t list =
    List.fold_left sop_list ~init:[] ~f:(fun acc sop ->
        let vop = sop_to_vertex sop in
        match vop with Some v -> v :: acc | None -> acc)
    @ List.fold_left st_list ~init:[] ~f:(fun acc st -> st_to_vertex st :: acc)

  let get_gen (instr : instr) : Set.t =
    let vertex_list =
      match instr with
      | Binop binop -> to_vertex [ binop.lhs; binop.rhs ] [ binop.dest ]
      | Fcall fcall -> to_vertex fcall.args []
      | Cast cast -> to_vertex [] [ cast.src ]
      | Mov mov -> to_vertex [ mov.src ] []
      | CJump cjmp -> to_vertex [ cjmp.lhs; cjmp.rhs ] []
      | Ret ret -> (
          match ret.var with Some var -> to_vertex [ var ] [] | None -> [])
      | Store store -> to_vertex [ store.src ] []
      | Jump _ | Load _ | Label _ | Directive _ | Comment _ -> []
    in
    Set.of_list vertex_list

  let get_kill (instr : instr) : Set.t =
    let vertex_list =
      match instr with
      | Binop binop -> to_vertex [] [ binop.dest ]
      | Fcall fcall -> (
          match fcall.dest with
          | Some dest -> to_vertex [] [ dest ]
          | None -> [])
      | Cast cast -> to_vertex [] [ cast.dest ]
      | Mov mov -> to_vertex [] [ mov.dest ]
      | Load load -> to_vertex [] [ load.dest ]
      | Jump _ | CJump _ | Store _ | Label _ | Ret _ | Directive _ | Comment _
        ->
          []
    in
    Set.of_list vertex_list
end

module LANA =
  Mydf.Impt.DFWrapper (QCFG) (LivenessInfo) (LivenessInstr) (LivenessType)
