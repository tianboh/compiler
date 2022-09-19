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
 * We provide 3 address pseudo and 2 address pseudo based on x86 architecture.
 * the way to convert from 3 address to 2 address is to use same operand for
 * Destination and first operand for binary operation. This makes sense because
 * Each binary op will copy the operand and then calculate. The copied operand will
 * never be used again after calculation. So we can safely store the result to the
 * operand.
 * Notice that for [a <- b + c, d <- b + c ] will not reuse temporary in b and c 
 * in the second execution. The assembly looks like
 * t1 <- some_value for b
 * t2 <- some_value for c
 * t3 <- t1
 * t4 <- t2
 * t5 <- t3 + t4
 * t6 <- t1
 * t7 <- t2
 * t8 <- t6 + t7
 * Therefore, we can reuse t3 as destination of t3 + t4 for x86 add inplace mechanism.
*)

open Core
module T = Parser.Tree
module AS = Inst.Pseudo
module AS_x86 = Inst.X86
module Register = Register.X86_reg.Register
module Reg_info = Json_reader.Lab1_checkpoint
module Temp = Temp.Temp

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

module Pseudo = struct
  (* munch_exp dest exp
  *
  * Generates instructions for dest <-- exp.
  *)
  let munch_exp : Temp.t -> T.exp -> AS.instr list =
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
    let rec munch_exp_acc (dest : Temp.t) (exp : T.exp) (rev_acc : AS.instr list) 
      : AS.instr list =
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
        (dest : Temp.t)
        ((binop, e1, e2) : T.binop * T.exp * T.exp)
        (rev_acc : AS.instr list)
      : AS.instr list
      =
      let op = munch_op binop in
      (* Notice we fix the left hand side operand and destination the same to meet x86 instruction. *)
      let t1 = Temp.create () in
      let t2 = Temp.create () in
      let rev_acc' = rev_acc |> munch_exp_acc t1 e1 |> munch_exp_acc t2 e2 in
      AS.Binop { op; dest; lhs = AS.Temp t1; rhs = AS.Temp t2 } :: rev_acc'
    in
    fun dest exp  ->
      (* Since munch_exp_acc returns the reversed accumulator, we must
      * reverse the list before returning. *)
      List.rev (munch_exp_acc dest exp [])
  ;;

  (* munch_stm : T.stm -> AS.instr list *)
  (* munch_stm stm generates code to execute stm *)
  let munch_stm stm  = match stm with
    | T.Move mv -> munch_exp mv.dest mv.src 
    | T.Return e ->
      (* return e is implemented as %eax <- e *)
      let t = Temp.create () in
      munch_exp t e 
  ;;

  (* To codegen a series of statements, just concatenate the results of
  * codegen-ing each statement. *)
  let gen = List.concat_map ~f:(fun stm -> munch_stm stm)

end

(* module Pseudo_x86 = struct
  let gen = List.concat_map ~f:(fun stm -> munch_stm stm)
end *)

module X86 = struct
  let oprd_ps_to_x86 (operand : AS.operand) (reg_alloc_info : Register.t Temp.Map.t) : AS_x86.operand =
    match operand with
    | Imm i -> AS_x86.Imm i
    | Temp t -> AS_x86.Reg (Temp.Map.find_exn reg_alloc_info t)
  ;;

  let inst_bin_ps_to_x86 (op : AS.bin_op) : AS_x86.bin_op = 
    match op with
    | Add -> AS_x86.Add
    | Sub -> AS_x86.Sub
    | Mul -> AS_x86.Mul
    | Div -> AS_x86.Div
    | Mod -> AS_x86.Mod
    | And -> AS_x86.And
    | Or -> AS_x86.Or
    | Pand -> AS_x86.Pand
    | Por -> AS_x86.Por
    | Pxor -> AS_x86.Pxor
  ;;

  let rec _codegen_w_reg res inst_list (reg_alloc_info : Register.t Temp.Map.t) =
    match inst_list with
    | [] -> res @ [AS_x86.Ret]
    | h :: t -> 
      match h with
      | AS.Binop bin_op -> 
        let dest = Temp.Map.find_exn reg_alloc_info bin_op.dest in
        let lhs = oprd_ps_to_x86 bin_op.lhs reg_alloc_info in
        let rhs = oprd_ps_to_x86 bin_op.rhs reg_alloc_info in
        let op = inst_bin_ps_to_x86 bin_op.op in
        let bin_op = AS_x86.Binop {op; dest; lhs; rhs} in
        _codegen_w_reg (res @ [bin_op]) t reg_alloc_info
      | AS.Mov mov -> 
        let dest = Temp.Map.find_exn reg_alloc_info mov.dest in
        let src = oprd_ps_to_x86 mov.src reg_alloc_info in
        let mov = AS_x86.Mov {dest; src} in
        _codegen_w_reg (res @ [mov]) t reg_alloc_info
      | AS.Directive _ | AS.Comment _ -> _codegen_w_reg res t reg_alloc_info
  ;;
  let gen (inst_list : AS.instr list) 
              (reg_alloc_info : (Temp.t * Register.t) option list) : AS_x86.instr list = 
    let reg_alloc = List.fold  reg_alloc_info ~init:(Temp.Map.empty) ~f:(fun acc x -> 
        match x with 
        | None -> acc
        | Some x -> match x with (temp, reg) -> Temp.Map.set acc ~key:temp ~data:reg
      ) in
    _codegen_w_reg [] inst_list reg_alloc

end