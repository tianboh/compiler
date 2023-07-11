module AST = Front.Ast
module TST = Inst
module TC = Typechecker

let run (ast : AST.gdecl list) : TC.env =
  let tc_env = TC.typecheck ast in
  Controlflow.cf_ret ast;
  Controlflow.cf_init ast;
  tc_env
;;
