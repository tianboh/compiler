module Label = Util.Label

module Wraper
    (Instr : Sig.InstrInterface)
    (CFG : Cfg.Sig.CFGInterface with type i = Instr.t) : Sig.SSAInterface = struct
  type phi
  type t = CFG.bb

  let construct = failwith ""
  let decompose = failwith ""
  let insert_param_block = failwith ""
  let delete_param_block = failwith ""
  let place_phi = failwith ""
  let rename = failwith ""
  let renameBB = failwith ""
end
