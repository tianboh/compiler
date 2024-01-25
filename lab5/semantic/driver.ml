module AST = Front.Ast
module TST = Inst
module TC = Typechecker
module CC = Cfchecker

let run (ast : AST.program) : TST.program * TC.env =
  let tst, env = TC.typecheck ast in
  CC.cf_ret ast;
  CC.cf_init ast;
  tst, env
;;
