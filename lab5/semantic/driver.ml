module AST = Front.Ast
module TST = Inst
module TC = Typechecker
module CC = Cfchecker

let run (ast : AST.program) : TST.program * TC.env =
  let _, _ = TC.typecheck ast in
  let ast_new = CC.cf_ret ast [] in
  CC.cf_init ast_new;
  let tst, env = TC.typecheck ast_new in
  tst, env
;;
