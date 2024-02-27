open Core
module Label = Util.Label

module Wrapper =
functor
  (Instr : Sig.InstrInterface)
  (CFG : Cfg.Sig.CFGInterface with type i = Instr.i)
  ->
  struct
    type pair = Instr.t * Label.t
    type bb = CFG.bb
    type ssa_bb =
      { phis : pair list
      ; block : bb
      }
    module StMap = Map.Make(Instr)
    type ssa_bbmap = ssa_bb Label.Map.t (* Hash table: label -> ssa basic block *)

    let param_label = Label.label (Some "params")

    let insert_param_block (params : Instr.t list) : Instr.i list =
      let label = Instr.label param_label in
      label :: List.map params ~f:(fun param -> Instr.assign param 0L)
    ;;

    let delete_param_block (bbs : CFG.bbmap) : CFG.bbmap =
      Label.Map.remove bbs param_label
    ;;

    (* Insert phi to dominator frontier of bb, update ssa_bmap, orig and defsites *)
    let rec insert_phi (bb : bb) (ssa_bbmap : ssa_bbmap) (orig : Instr.t list Label.Map.t) (defsites : Label.t list StMap.t) : ssa_bbmap  =

    ;;

    (* Insert phi and generate ssa basic block map. 
     * Check https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/lec/05-ssa.pdf P84 
     * for pseudo code details. *)
    let construct (bbs : CFG.bbmap) (df : CFG.map) : ssa_bbmap = 
      
    ;;

    let decompose (ssa_bbs : ssa_bbmap) : CFG.bbmap = failwith ""
    let rename = failwith ""
    let renameBB = failwith ""

    let run (params : Instr.t list) (instrs_body : Instr.i list) : CFG.bbmap =
      let instrs_head = insert_param_block params in
      let instrs = instrs_head @ instrs_body in
      let bbs = CFG.build_bb instrs in
      let succs, preds = CFG.build_ino bbs in
      let bbs', succs, preds = CFG.remove_criticl_edges bbs succs preds in
      let porder = CFG.postorder succs in
      let idom = CFG.idom porder preds in
      let df = CFG.build_DF idom preds in
      let dt = CFG.build_DT idom in
      let ssa_bbs = construct bbs' df in
      delete_param_block bbs'
    ;;
  end
