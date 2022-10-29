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
module Reg_info = Json_reader.Lab1_checkpoint
module Temp = Var.Temp
module Register = Var.X86_reg
module Memory = Var.Memory

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
  let need_precolor (op : AS.bin_op) = match op with
  | AS.Mul | AS.Div | AS.Mod -> true
  | _ -> false

  let precolor op dest t1 t2 rev_acc' = 
    match op with 
      | AS.Mul | AS.Div  -> 
        let eax = Register.create_no 1 in 
        let t_eax = Register.reg_to_tmp eax in
        AS.Mov {src=AS.Temp t_eax; dest=dest} :: 
        AS.Binop { op; dest = AS.Temp t_eax; lhs = AS.Temp t1; rhs = AS.Temp t2 } ::
        rev_acc'
      | AS.Mod -> 
        let edx = Register.create_no 4 in 
        let t_edx = Register.reg_to_tmp edx in
        AS.Mov {src=AS.Temp t_edx; dest=dest} :: 
        AS.Binop { op; dest = AS.Temp t_edx; lhs = AS.Temp t1; rhs = AS.Temp t2 } ::
        rev_acc'
      | _ -> failwith "not need for pre-color."
  
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
        (dest : AS.operand)
        ((binop, e1, e2) : T.binop * T.exp * T.exp)
        (rev_acc : AS.instr list)
      : AS.instr list
      =
      let op = munch_op binop in
      (* Notice we fix the left hand side operand and destination the same to meet x86 instruction. *)
      let t1 = Temp.create () in
      let t2 = Temp.create () in
      let rev_acc' = rev_acc |> munch_exp_acc (AS.Temp t1) e1 |> munch_exp_acc (AS.Temp t2) e2 in
      if need_precolor op 
        then precolor op dest t1 t2 rev_acc'
        else AS.Binop { op; dest; lhs = AS.Temp t1; rhs = AS.Temp t2 } :: rev_acc'
    in
    fun dest exp  ->
      (* Since munch_exp_acc returns the reversed accumulator, we must
      * reverse the list before returning. *)
      List.rev (munch_exp_acc dest exp [])
  ;;

  (* munch_stm : T.stm -> AS.instr list *)
  (* munch_stm stm generates code to execute stm *)
  let munch_stm stm  = match stm with
    | T.Move mv -> munch_exp (AS.Temp mv.dest) mv.src 
    | T.Return e ->
      (* return e is implemented as %eax <- e 
        %t-1 is %eax, which is our returned destination. *)
      let t = Temp.create_no (-1) in
      munch_exp (AS.Temp t) e 
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
    | Temp t -> 
      let reg = (match Temp.Map.find reg_alloc_info t with | Some s -> s | None -> Register.tmp_to_reg t) in
      if Register.need_spill reg then AS_x86.Mem (Memory.from_reg reg) else AS_x86.Reg reg
    | Reg r -> AS_x86.Reg r
    | Imm i -> AS_x86.Imm i
  ;;
  let eax = AS_x86.Reg (Register.create_no 1);;
  let edx = AS_x86.Reg (Register.create_no 4);;

  let same_reg r1 r2 = if Register.compare r1 r2 = 0 then true else false
  ;;

  let gen_x86_inst_bin 
      (op : AS.bin_op) 
      (dest : AS_x86.operand) 
      (lhs : AS_x86.operand) 
      (rhs : AS_x86.operand)
      (reg_swap : Register.t) = 
    match op with
      | Add -> AS_x86.safe_add lhs rhs @ AS_x86.safe_mov dest lhs
      | Sub -> AS_x86.safe_sub lhs rhs @ AS_x86.safe_mov dest lhs
      | Mul -> [AS_x86.Mov {dest=eax; src=lhs};
                AS_x86.Mul {src=rhs};]
      | Div ->
              (* Notice that lhs and rhs may be allocated on edx. 
                 So we use reg_swap to avoid override in the edx <- 0. *)
              [ AS_x86.Mov {dest=eax; src=lhs};
                AS_x86.Mov {dest=AS_x86.Reg reg_swap; src=edx};
                AS_x86.Cdq;] 
              @ if same_reg (match rhs with | Reg r -> r | _ -> failwith "rhs should be reg or tmp") 
                            (match edx with | Reg r -> r | _ -> failwith "edx should be register.") 
              then [AS_x86.Div {src=AS_x86.Reg reg_swap};]
              else [AS_x86.Div {src=rhs};]
              @ [AS_x86.Mov {dest=edx; src=AS_x86.Reg reg_swap};]
      | Mod -> 
              [ AS_x86.Mov {dest=AS_x86.Reg reg_swap; src=eax};
                AS_x86.Mov {dest=eax; src=lhs};
                AS_x86.Cdq;
                AS_x86.Div {src=rhs};
                AS_x86.Mov {dest=eax; src=AS_x86.Reg reg_swap};]
      | _ -> failwith ("not implemented yet " ^ (AS_x86.format_operand (dest:>AS_x86.operand)))
  ;;

  let rec _codegen_w_reg res inst_list (reg_alloc_info : Register.t Temp.Map.t) (reg_swap: Register.t) =
    match inst_list with
    | [] -> res @ [AS_x86.Ret]
    | h :: t -> 
      match h with
      | AS.Binop bin_op -> 
        let dest = oprd_ps_to_x86 bin_op.dest reg_alloc_info in
        let lhs = oprd_ps_to_x86 bin_op.lhs reg_alloc_info in
        let rhs = oprd_ps_to_x86 bin_op.rhs reg_alloc_info in
        (* let op = inst_bin_ps_to_x86 bin_op.op in *)
        let insts = gen_x86_inst_bin bin_op.op dest lhs rhs reg_swap in
        _codegen_w_reg (res @ insts) t reg_alloc_info reg_swap
      | AS.Mov mov -> 
        let dest = oprd_ps_to_x86 mov.dest reg_alloc_info in
        let src = oprd_ps_to_x86 mov.src reg_alloc_info in
        let insts = AS_x86.safe_mov dest src in
        _codegen_w_reg (res @ insts) t reg_alloc_info reg_swap
      | AS.Directive _ | AS.Comment _ -> _codegen_w_reg res t reg_alloc_info reg_swap
  ;;
  let gen (inst_list : AS.instr list) 
              (reg_alloc_info : (Temp.t * Register.t) option list) : AS_x86.instr list = 
    let reg_alloc = List.fold  reg_alloc_info ~init:(Temp.Map.empty) ~f:(fun acc x -> 
        match x with 
        | None -> acc
        | Some x -> match x with (temp, reg) -> Temp.Map.set acc ~key:temp ~data:reg
      ) in
    let reg_swap = Register.swap () in
    _codegen_w_reg [] inst_list reg_alloc reg_swap

end