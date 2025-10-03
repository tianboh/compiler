open Core
module AbsCFG = Cfg.Impt.Wrapper (Abs_asm.Inst)

(* module LivenessInfo = struct
  type t = Var.Temp.t [@@deriving sexp, compare]

  module Set = Set.Make (Var.Temp)
end *)

module LivenessInfo = Interference_graph.Vertex

module LivenessType = struct
  let meet_type = Mydf.Sig.May
  let direction = Mydf.Sig.Backward
end

module LivenessInstr = struct
  include Abs_asm.Inst
  include LivenessInfo

  let sop_to_vertex (sop : Sop.t) : t option =
    match sop.data with
    | Temp t -> Some (Temp t)
    | Reg r -> Some (Reg r)
    | Imm _ | Above_frame _ -> None

  let st_to_vertex (st : St.t) : t = Temp st.data

  let to_vertex (sop_list : Sop.t list) (st_list : St.t list) : t list =
    List.fold_left sop_list ~init:[] ~f:(fun acc sop ->
        let vop = sop_to_vertex sop in
        match vop with Some v -> v :: acc | None -> acc)
    @ List.fold_left st_list ~init:[] ~f:(fun acc st -> st_to_vertex st :: acc)

  let get_gen (instr : instr) : Set.t =
    let vertex_list =
      match instr with
      | Binop binop -> to_vertex [ binop.lhs; binop.rhs ] []
      | Fcall fcall -> to_vertex fcall.args []
      | Cast cast -> to_vertex [] [ cast.src ]
      | Mov mov -> to_vertex [ mov.src ] []
      | CJump cjmp -> to_vertex [ cjmp.lhs; cjmp.rhs ] []
      | Push push -> to_vertex [ push.var ] []
      | Store store -> to_vertex [ store.src ] []
      | Jump _ | Load _ | Label _ | Ret _ | Pop _ | Directive _ | Comment _ ->
          []
    in
    Set.of_list vertex_list

  let get_kill (instr : instr) : Set.t =
    let vertex_list =
      match instr with
      | Binop binop -> (
          match binop.op with
          | Times -> Reg Register.RAX :: to_vertex [ binop.dest ] []
          | Divided_by | Modulo ->
              [ Reg Register.RAX; Reg Register.RDX ]
              @ to_vertex [ binop.dest ] []
          | Right_shift | Left_shift ->
              Reg Register.RCX :: to_vertex [ binop.dest ] []
          | Plus | Minus | And | Or | Xor | Equal_eq | Greater | Greater_eq
          | Less | Less_eq | Not_eq ->
              to_vertex [ binop.dest ] [])
      | Fcall _ -> [ Reg Register.RAX ]
      | Cast cast -> to_vertex [] [ cast.dest ]
      | Mov mov -> to_vertex [ mov.dest ] []
      | Pop pop -> to_vertex [ pop.var ] []
      | Load load -> to_vertex [] [ load.dest ]
      | Jump _ | CJump _ | Store _ | Label _ | Ret _ | Push _ | Directive _
      | Comment _ ->
          []
    in
    Set.of_list vertex_list
end

module LANA =
  Mydf.Impt.DFWrapper (AbsCFG) (LivenessInfo) (LivenessInstr) (LivenessType)
