module AST = Front.Ast
module TST = Inst
module TC = Typechecker

let run (ast : AST.program) : TST.program * TC.env =
  let tst, env = TC.typecheck ast in
  Controlflow.cf_ret ast;
  Controlflow.cf_init ast;
  tst, env
;;
