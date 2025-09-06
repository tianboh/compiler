open Core
module QCFG = Cfg.Impt.Wrapper (Quads.Inst)

module LivenessInfo = struct
  type t = Var.Temp.t [@@deriving sexp, compare]

  module Set = Set.Make (Var.Temp)
end

module LivenessType = struct
  let meet_type = Mydf.Sig.May
  let direction = Mydf.Sig.Backward
end

module LivenessInstr = struct
  include Quads.Inst
  include LivenessInfo

  let get_gen (instr : instr) =
    match instr with
    | Binop binop -> Set.of_list [ Sop.to_t binop.rhs ]
    | _ -> failwith ""

  let get_kill (instr : instr) =
    match instr with
    | Binop binop -> Set.of_list [ Sop.to_t binop.rhs ]
    | _ -> failwith ""
end

module LANA =
  Mydf.Impt.DFWrapper (QCFG) (LivenessInfo) (LivenessInstr) (LivenessType)
