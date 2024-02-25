open Core
module Label = Util.Label

module Wrapper =
functor
  (Instr : Sig.InstrInterface)
  (CFG : Cfg.Sig.CFGInterface with type i = Instr.t)
  ->
  struct
    type pair = Label.t * Instr.st

    type phi =
      { target : Instr.st
      ; src : pair list
      }

    type ssa_bb =
      { phis : phi list
      ; block : CFG.bb
      }

    type ssa_bbmap = ssa_bb Label.Map.t (* Hash table: label -> ssa basic block *)

    let param_label = Label.label (Some "params")

    let insert_param_block (params : Instr.st list) : Instr.t list =
      let label = Instr.label param_label in
      label :: List.map params ~f:(fun param -> Instr.assign param 0L)
    ;;

    let delete_param_block (bbs : CFG.bbmap) : CFG.bbmap =
      Label.Map.remove bbs param_label
    ;;

    let run (params : Instr.st list) (instrs_body : Instr.t list) : CFG.bbmap =
      let instrs_head = insert_param_block params in
      let instrs = instrs_head @ instrs_body in
      let bbs = CFG.build_bb instrs in
      let succs, preds = CFG.build_ino bbs in
      let bbs', succs, preds = CFG.remove_criticl_edges bbs succs preds in
      let porder = CFG.postorder succs in
      let idom = CFG.idom porder preds in
      let df = CFG.build_DF idom preds in
      let dt = CFG.build_DT idom in
      delete_param_block bbs'
    ;;

    let insert_phi (bbs : CFG.bbmap) (df : CFG.map) = failwith ""

    let construct (bbs : CFG.bbmap) (df : CFG.map) : ssa_bbmap =
      insert_phi bbs df failwith ""
    ;;

    let decompose (ssa_bbs : ssa_bbmap) = failwith ""
    let rename = failwith ""
    let renameBB = failwith ""
  end
