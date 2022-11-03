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
open Var.Layout

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

  (* Check if key is stored in cache before, if key -> Imm
   * is stored before, then return Imm, else return key. *)
  let const_cache (map : Int32.t Temp.Map.t) (key : AS.operand) : AS.operand = 
    match key with
    | AS.Temp k-> 
      (* let () = printf "check key %s\n" (Temp.name k) in *)
      (match Temp.Map.find map k with
        | Some s -> 
          (* let () = printf "find %d\n" (Int32.to_int_exn s) in  *)
          AS.Imm s
        | None -> AS.Temp k)
    | AS.Imm i -> AS.Imm i
    | AS.Reg r -> AS.Reg r
  ;;

  (* We store the map from Temp.t to Imm when read mov instruction.
   * When seeing operand in binop, we check whether its left/right hand operand
   * has already been stored in map. If so, we replace the temp with Imm.*)
  let const_propagation (pseudo_assembly : AS.instr list) : AS.instr list = 
    let const_map = Temp.Map.empty in
    let rec helper (pseudo_assembly : AS.instr list) (res : AS.instr list) (const_map : Int32.t Temp.Map.t) = 
      match pseudo_assembly with
      | [] -> res
      | h :: t -> 
        match h with
        | AS.Binop bin -> 
          (match bin.op with
          (* | AS.Add | AS.Sub | AS.Mul | AS.Div | AS.Mod ->  *)
          | AS.Add | AS.Sub -> 
            (let new_l = const_cache const_map bin.lhs in
             let new_r = const_cache const_map bin.rhs in
             helper t (res @ [AS.Binop{op=bin.op;lhs=new_l;rhs=new_r;dest=bin.dest}]) const_map)
          | _ -> helper t (res @ [h]) const_map)
        | AS.Mov mov -> 
          (match mov.dest, mov.src with
          | AS.Temp tmp, AS.Imm i -> 
            (* let () = printf "set %s to %d\n" (Temp.name tmp) (Int32.to_int_exn i) in *)
            let const_map = Temp.Map.set const_map ~key:tmp ~data:i in
            helper t (res @ [h]) const_map
          | AS.Temp tmp1, AS.Temp tmp2 -> 
            (if Temp.Map.mem const_map tmp2 
              then 
                let v = Temp.Map.find_exn const_map tmp2 in
                let const_map = Temp.Map.set const_map ~key:tmp1 ~data:v in
                helper t (res @ [AS.Mov {dest=mov.dest; src=AS.Imm v}]) const_map
              else 
                helper t (res @ [h]) const_map
            )
          | _ -> helper t (res @ [h]) const_map)
        | _ -> helper t (res @ [h]) const_map
    in helper pseudo_assembly [] const_map
  ;;

  (* Check whether temporary key is mapped to a value in coalesce map. *)
  let coalesce_cache (map : Temp.t Temp.Map.t) (key : AS.operand) : AS.operand = 
    match key with 
    | AS.Imm i -> AS.Imm i
    | AS.Reg r -> AS.Reg r
    | AS.Temp t -> 
      (match Temp.Map.find map t with
       | Some v -> AS.Temp v
       | None -> AS.Temp t )
  ;;

  (* When read mov t1 t2, we will generate t3 and use t3 to replace t1 and t2 in the following insts. 
   * Then we build a map to store the mapping relation {t1 : t3} and {t2 : t3} where t1 and t2 are key
   * and t3 is the value. *)
  let coalesce (ori_insts : AS.instr list) : AS.instr list = 
    let coalesce_map = Temp.Map.empty in
    let rec helper (ori_insts : AS.instr list) (ret : AS.instr list) (map : Temp.t Temp.Map.t) : AS.instr list = 
      match ori_insts with
      | [] -> ret
      | h :: t -> 
        match h with 
        | AS.Mov mov -> (match mov.dest, mov.src with
          | AS.Temp dest, AS.Temp src -> (
            if Temp.is_reg dest || Temp.is_reg src
              then helper t (ret@[h]) map
              else 
                let coalesced_t = Temp.create () in
                let map = Temp.Map.set map ~key:dest ~data:coalesced_t in
                let map = Temp.Map.set map ~key:src ~data:coalesced_t in
                helper t ret map)
          | _ -> helper t (ret@[h]) map)
        | AS.Binop bin -> 
          (let new_dest = coalesce_cache map bin.dest in
           let new_lhs = coalesce_cache map bin.lhs in
           let new_rhs = coalesce_cache map bin.rhs in
           helper t (ret @ [AS.Binop{op=bin.op;dest=new_dest;lhs=new_lhs;rhs=new_rhs}]) map
          )
        | _ -> helper t (ret@[h]) map
      in
    helper ori_insts [] coalesce_map
  ;;

  (* To codegen a series of statements, just concatenate the results of
  * codegen-ing each statement. *)
  let gen = List.concat_map ~f:(fun stm -> munch_stm stm)

  (* let rec print_insts insts = 
    match insts with
    | [] -> ()
    | h :: t -> 
      let () = printf "%s\n" (AS.format h) in 
      print_insts t
  ;; *)
  let optimize (ori_insts : AS.instr list) : AS.instr list = 
    (* let () = print_insts ori_insts in *)
    let ret = const_propagation ori_insts in
    (* let ret = coalesce ret in *)
    ret
    (* let () = print_insts ret in *)
    (* ori_insts *)
  ;;

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

  let same_reg (r1:AS_x86.operand) (r2:AS_x86.operand) = 
    match r1, r2 with
    | (Reg r1, Reg r2) -> if Register.compare r1 r2 = 0 then true else false
    | _ -> false
  ;;

  let gen_x86_inst_bin 
      (op : AS.bin_op) 
      (dest : AS_x86.operand) 
      (lhs : AS_x86.operand) 
      (rhs : AS_x86.operand)
      (reg_swap : Register.t) = 
    match op with
      | Add -> AS_x86.safe_mov dest lhs DWORD @ AS_x86.safe_add dest rhs DWORD
      | Sub -> AS_x86.safe_mov dest lhs DWORD @ AS_x86.safe_sub dest rhs DWORD
      | Mul -> [AS_x86.Mov {dest=eax; src=lhs; layout=DWORD};
                AS_x86.Mul {src=rhs; dest=dest; layout=DWORD};]
      | Div ->
              (* Notice that lhs and rhs may be allocated on edx. 
                 So we use reg_swap to avoid override in the edx <- 0. *)
              [ AS_x86.Mov {dest=eax; src=lhs; layout=DWORD};
                AS_x86.Mov {dest=lhs; src=rhs; layout=DWORD};
                AS_x86.Mov {dest=AS_x86.Reg reg_swap; src=edx; layout=DWORD};
                AS_x86.Cvt {layout=DWORD};] 
              (* @ if same_reg (match rhs with | Reg r -> r | _ -> failwith "rhs should be reg or mem") 
                            (match edx with | Reg r -> r | _ -> failwith "edx should be register.")  *)
              @ if same_reg rhs edx
              then [AS_x86.Div {src=AS_x86.Reg reg_swap; layout=DWORD};]
              else [AS_x86.Div {src=lhs; layout=DWORD};]
              @ [AS_x86.Mov {dest=edx; src=AS_x86.Reg reg_swap; layout=DWORD};]
      | Mod -> 
              [ AS_x86.Mov {dest=AS_x86.Reg reg_swap; src=eax; layout=DWORD};
                AS_x86.Mov {dest=eax; src=lhs; layout=DWORD};
                AS_x86.Cvt{layout=DWORD};
                AS_x86.Div {src=rhs; layout=DWORD};
                AS_x86.Mov {dest=eax; src=AS_x86.Reg reg_swap; layout=DWORD};]
      | _ -> failwith ("inst not implemented yet " ^ (AS_x86.format_operand (dest:>AS_x86.operand) DWORD))
  ;;

  let rec _codegen_w_reg res inst_list (reg_alloc_info : Register.t Temp.Map.t) (reg_swap: Register.t) =
    match inst_list with
    | [] -> res @ [AS_x86.Ret]
    | h :: t -> 
      (* let () = printf "%s\n" (AS.format h) in *)
      match h with
      | AS.Binop bin_op -> 
        let dest = oprd_ps_to_x86 bin_op.dest reg_alloc_info in
        let lhs = oprd_ps_to_x86 bin_op.lhs reg_alloc_info in
        let rhs = oprd_ps_to_x86 bin_op.rhs reg_alloc_info in
        let insts = gen_x86_inst_bin bin_op.op dest lhs rhs reg_swap in
        _codegen_w_reg (res @ insts) t reg_alloc_info reg_swap
      | AS.Mov mov -> 
        let dest = oprd_ps_to_x86 mov.dest reg_alloc_info in
        let src = oprd_ps_to_x86 mov.src reg_alloc_info in
        let insts = AS_x86.safe_mov dest src DWORD in
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