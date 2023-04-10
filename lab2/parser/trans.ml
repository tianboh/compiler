(* L2 Compiler
 * AST -> IR Translator
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified by: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)
open Core
(* module A = Ast *)
module A = Cst
module S = Util.Symbol.Map
module T = Tree
module Symbol = Util.Symbol
module Mark = Util.Mark
module Temp = Var.Temp

let trans_binop = function
  | A.Plus -> T.Add
  | A.Minus -> T.Sub
  | A.Times -> T.Mul
  | A.Divided_by -> T.Div
  | A.Modulo -> T.Mod
  | A.And_and -> T.Logic_and
  | A.Or_or -> T.Logic_or
  | A.And -> T.Bit_and
  | A.Or -> T.Bit_or
  | A.Hat -> T.Bit_xor
;;

let trans_unop = function
  (* unary to binary!*)
  | A.Negative -> T.Sub
;;

let rec trans_exp env = function
  (* after type-checking, id must be declared; do not guard lookup *)
  | A.Var id -> T.Temp (S.find_exn env id)
  | A.Const_int c -> T.Const_int c
  | A.True -> T.Const_bool true
  | A.False -> T.Const_bool false
  | A.Binop binop ->
    T.Binop
      { op = trans_binop binop.op
      ; lhs = trans_mexp env binop.lhs
      ; rhs = trans_mexp env binop.rhs
      }
  | A.Unop { op = A.Negative; operand = e } ->
    T.Binop
      { op = trans_unop A.Negative; lhs = T.Const_int Int32.zero; rhs = trans_mexp env e }
  | A.Ter _ ->  failwith "not imp yet"

and trans_mexp env mexp = trans_exp env (Mark.data mexp)

(* translate the statement *)
(* let rec trans_stms (env : Temp.t S.t) (ast : A.stm list) : T.stm list =
  match ast with
  | A.Declare d :: stms ->
    (match d with
    | A.New_var _ -> trans_stms env stms
    | A.Init id -> trans_stms env (A.Assign {name = id.name; value = id.value} :: stms))
  | A.Assign {name=id; value=e} :: stms ->
    let t = Temp.create () in
    let env' = S.set env ~key:id ~data:t in
    T.Move { dest = t; src = trans_mexp env e } :: trans_stms env' stms
  | A.Return e :: _ ->
    (* ignore code after return *)
    [ T.Return (trans_mexp env e) ]
  | [] ->
    (* There must be a return. *)
    assert false
;; *)

(* let trans_mstms (env : Temp.t S.t) (ast : A.program) : T.program =
  trans_stms env (List.map ~f:Mark.data ast)
;; *)

let rec trans_block (env : Temp.t S.t) (ast : A.program) : T.program =
  match ast with
  | [] -> []
  | Concat cnt -> 
    match Mark.data cnt.head with
    | A.Declare d ->
      (match d with
      | A.New_var _ -> trans_block env cnt.tail
      | A.Init id -> trans_block env (A.Concat {head = Mark.naked (A.Assign {name = id.name; value = id.value}); tail = cnt.tail}))
    | A.Assign {name=id; value=e} ->
      let t = Temp.create () in
      let env' = S.set env ~key:id ~data:t in
      T.Move { dest = t; src = trans_mexp env e } :: trans_block env' cnt.tail
    | A.Return e ->
      (* ignore code after return *)
      [ T.Return (trans_mexp env e) ]
;;

(* let trans_block (env : Temp.t S.t) (ast : A.program) : T.program = match ast with
  | []
  | Concat of {head : mstm; tail : stms} *)

let translate (stms : A.program) : T.program = trans_block S.empty stms
