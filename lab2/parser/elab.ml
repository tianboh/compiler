(* Notice the difference between CST and AST
* CST is basically transferred from source code literaly.
* AST add more structure statement unit based on CST, and it looks like a tree.
*
* Statement level benefit:
* To be specific, AST classify statement from CST into below
* 1) Asign(x,e)
* 2) if(e,s,s)
* 3) while(e,s)
* 4) return(e)
* 5) nop
* 6) seq(s,s)
* 7) declare(x,t,s)
* The obvious advantage is that we can handle variable namespace more efficiently.
* We can see if the use of x is in a declare statement. Notice that the use of x 
* may be nested in many seq statement in declare(x,t,s).
* In addition, we will simplify for from CST to while statement in AST. 
* This will reduce the Intermediate Representation.
*
* Expression level benefit: 
* 1) logical operation && || ^ can be denoted in ternary expression, so IR does not 
*    logical operation anymore.
* 2) <binop>= b can be simplified to a = a binop b
* This can simplify our work in IR level
* More details can be checked in 
* https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab2.pdf Page 5 and 6
*
* Author: Tianbo Hao <tianboh@alumni.cmu.edu>
*)

module Mark = Util.Mark

let elab_exp (cst_exp : Cst.exp) : Ast.exp = 
  failwith (Cst.Print.pp_exp cst_exp)
;;

let elab_mexp (cst_mexp : Cst.mexp) = 
  let exp = Mark.data cst_mexp in
  elab_exp exp
;;


(* 
type stm =
  | Simp of simp
  | Control of control
  | Block of block
  
type decl =
  (* int/bool x; *)
  | New_var of { t : dtype; name : Symbol.t }
  (* int/bool x = e; *)
  | Init of { t : dtype; name : Symbol.t; value : mexp}

and simp = 
  | Assign of {name : Symbol.t ; value : mexp}
  | Declare of decl
  | Exp of mexp

and control = 
  | If of {cond : mexp; s_t : stm; s_f : stm option}
  | While of {cond : mexp; body : stm}
  | For of {init : simp option; cond : mexp; iter : simp option; body : stm}
  | Return of mexp   
*)
(* let elab_internal = function
  | Cst.Decl decl -> elab_decl decl 
  | Cst.Stm stm -> elab_stm stm
  | 
;; *)


let elab_type = function
  | Cst.Int -> Ast.Int
  | Cst.Bool -> Ast.Bool

let rec elaborate_internal (cst : Cst.program) (acc : Ast.program) : Ast.program = 
  match cst with 
  | [] -> acc
  | h :: t -> 
    let ast_head, cst_tail = elab_stm h t in
    let acc = Ast.Seq{ head = acc; tail = ast_head} in
    elaborate_internal cst_tail acc

(* Though we are elaborating current statement, the tail is required
 * during process because in some cases, like declare, we need the following 
 * context for AST unit. Also, we need to return the tail after process to 
 * avoid redo elaboration in elaborate_internal function.
 *
 * Return: Elaborated AST statement from CST head and the remaining CST tail.
 *)
and elab_stm (head : Cst.mstm) (tail : Cst.mstms) : ( Ast.program * Cst.program) = 
  match Util.Mark.data head with
  | Cst.Simp simp -> elab_simp simp tail
  | Cst.Control ctl -> elab_control ctl, tail
  | _ -> failwith ""
  (* | Cst.Block blk -> elab_block blk *)

(* Return AST head and remaining CST tails *)
and elab_simp (simp : Cst.simp) (tail : Cst.mstms) : ( Ast.program * Cst.program) = 
  match simp with
  | Cst.Declare decl -> elab_declare decl tail
  | Cst.Assign asn -> Ast.Assign {name = asn.name; value = elab_mexp asn.value}, tail
  | Cst.Exp exp -> Ast.Sexp (elab_mexp exp), tail

and elab_declare (decl : Cst.decl) (tail : Cst.mstms) = 
  match decl with
  | New_var var -> 
    let ast_tail = elaborate_internal tail Ast.Nop in
    Ast.Declare {t = elab_type var.t; name = var.name; tail = ast_tail}, []
  | Init init -> 
    let ast_tail = elaborate_internal tail Ast.Nop in
    let assign = Ast.Assign {name = init.name; value = elab_mexp init.value} in
    let seq = Ast.Seq {head = assign; tail = ast_tail} in
    Ast.Declare {t = elab_type init.t; name = init.name; tail = seq}, []


(* source
  | If if_stm -> 
  (* of {cond : mexp; s_t : stm; s_f : stm option} *)
  | While 
  (* of {cond : mexp; body : stm} *)
  
  | Return 
  (* of mexp *)   
*)
(* destination
| If of {cond : exp; true_stm : stm; false_stm : stm}
  | While of {cond : exp; body : stm}
  | Return of exp
*)
(* Return: AST statement. *)
and elab_control = function
  | If if_stm ->
    let false_stm, _ = match if_stm.false_stm with 
      | None -> Ast.Nop, []
      | Some s -> elab_stm (Mark.naked s) [] in
    let true_stm, _ = elab_stm (Mark.naked if_stm.true_stm) [] in
    Ast.If {cond = elab_mexp if_stm.cond; 
            true_stm = true_stm; 
            false_stm = false_stm}
  | While while_stm -> 
    let body, _ = elab_stm (Mark.naked while_stm.body) [] in
    let cond = elab_mexp while_stm.cond in
    Ast.While {cond = cond; body = body}
  (* We elaborate CST "for" to AST "while" for simplicity *)
  | For for_stm -> 
    let body_cst = match for_stm.iter with
      | None -> Cst.Block ([Mark.naked for_stm.body])
      | Some simp -> Cst.Block [Mark.naked for_stm.body; Mark.naked (Cst.Simp simp)] in
    let while_cst = Cst.While {cond = for_stm.cond; body = body_cst} in
    let seq = match for_stm.init with
      | None -> elab_control while_cst
      | Some init -> 
        let cst_program = [Mark.naked (Cst.Simp init); Mark.naked (Cst.Control while_cst)] in 
        elaborate_internal cst_program Ast.Nop in
    seq
  | Return ret -> Ast.Return (elab_mexp ret)
;;

let elaborate (cst : Cst.program) : Ast.program = 
  elaborate_internal cst Ast.Nop
;;