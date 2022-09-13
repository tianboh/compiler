(* L1 Compiler
 * Assembly Code Generator for FAKE assembly
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Use a linear, not quadratic, algorithm.
 *
 * Implements a "convenient munch" algorithm
*)

open Core
module T = Parser.Tree
module AS = Assem.Pseudo
module Register = Register.X86_reg
module Reg_info = Json_reader.Lab1_checkpoint

let munch_op = function
  | T.Add -> AS.Add
  | T.Sub -> AS.Sub
  | T.Mul -> AS.Mul
  | T.Div -> AS.Div
  | T.Mod -> AS.Mod
  | T.Logic_and -> AS.And
  | T.Logic_or -> AS.Or
  | T.Bit_and -> AS.Pand
  | T.Bit_or -> AS.Por
  | T.Bit_xor -> AS.Pxor
;;

(* munch_exp dest exp
 *
 * Generates instructions for dest <-- exp.
*)
let munch_exp : AS.operand -> T.exp -> AS.instr list =
  (* munch_exp_acc dest exp rev_acc
   *
   * Suppose we have the statement:
   *   dest <-- exp
   *
   * If the codegened statements for this are:
   *   s1; s2; s3; s4;
   *
   * Then this function returns the result:
   *   s4 :: s3 :: s2 :: s1 :: rev_acc
   *
   * I.e., rev_acc is an accumulator argument where the codegen'ed
   * statements are built in reverse. This allows us to create the
   * statements in linear time rather than quadratic time (for highly
   * nested expressions).
  *)
  let rec munch_exp_acc (dest : AS.operand) (exp : T.exp) (rev_acc : AS.instr list)
    : AS.instr list
    =
    match exp with
    | T.Const_int i -> AS.Mov { dest; src = AS.Imm i } :: rev_acc
    | T.Const_bool b -> (match b with
        | true -> AS.Mov { dest; src = AS.Imm Int32.one } :: rev_acc
        | false -> AS.Mov { dest; src = AS.Imm Int32.zero } :: rev_acc)
    | T.Temp t -> AS.Mov { dest; src = AS.Temp t } :: rev_acc
    | T.Binop binop -> munch_binop_acc dest (binop.op, binop.lhs, binop.rhs) rev_acc
  (* munch_binop_acc dest (binop, e1, e2) rev_acc
   *
   * generates instructions to achieve dest <- e1 binop e2
   *
   * Much like munch_exp, this returns the result of appending the
   * instructions in reverse to the accumulator argument, rev_acc.
  *)
  and munch_binop_acc
      (dest : AS.operand)
      ((binop, e1, e2) : T.binop * T.exp * T.exp)
      (rev_acc : AS.instr list)
    : AS.instr list
    =
    let op = munch_op binop in
    let t1 = AS.Temp (Temp.create ()) in
    let t2 = AS.Temp (Temp.create ()) in
    let rev_acc' = rev_acc |> munch_exp_acc t1 e1 |> munch_exp_acc t2 e2 in
    AS.Binop { op; dest; lhs = t1; rhs = t2 } :: rev_acc'
  in
  fun dest exp ->
    (* Since munch_exp_acc returns the reversed accumulator, we must
     * reverse the list before returning. *)
    List.rev (munch_exp_acc dest exp [])
;;

(* munch_stm : T.stm -> AS.instr list *)
(* munch_stm stm generates code to execute stm *)
let munch_stm = function
  | T.Move mv -> munch_exp (AS.Temp mv.dest) mv.src
  | T.Return e ->
    (* return e is implemented as %eax <- e *)
    let t = Temp.create () in
    munch_exp (AS.Temp t) e
;;

(* To codegen a series of statements, just concatenate the results of
 * codegen-ing each statement. *)
let codegen = List.concat_map ~f:munch_stm


(* let rec _codegen_w_reg res inst_list reg_alloc_info =
  match inst_list with
  | [] -> res
  | h :: t -> 
    match h with
    | AS.Binop bin_op -> 
      let dest = Hashtbl.find_exn reg_alloc_info (AS.format_operand bin_op.dest) in
      let lhs = Hashtbl.find_exn reg_alloc_info bin_op.lhs in
      let rhs = Hashtbl.find_exn reg_alloc_info bin_op.rhs in
      let bin_op = {bin_op with dest=dest; lhs=lhs; rhs=rhs} in
      _codegen_w_reg (bin_op @@ res) t reg_alloc_info
    | AS.Mov mov -> 
      let dest = Hashtbl.find_exn reg_alloc_info mov.dest in
      let src = Hashtbl.find_exn reg_alloc_info mov.dest in
      let mov = {mov with dest=dest; src=src} in
      _codegen_w_reg (mov @@ res) t reg_alloc_info
    | AS.Directive _ | AS.Comment _ -> _codegen_w_reg res t reg_alloc_info
;;
let codegen_w_reg 
          (inst_list : AS.instr list) 
          (reg_alloc_info : Reg_info.allocations) : AS.instr list = 
  let reg_alloc = Hashtbl.create in
  let () = List.iter reg_alloc_info ~f:(fun x -> 
      match x with 
      | None -> ()
      | Some x -> 
          match x with (temp, reg) -> Hashtbl.set reg_alloc ~key:temp ~data:reg
    ) in
  _codegen_w_reg [] inst_list reg_alloc *)

;;