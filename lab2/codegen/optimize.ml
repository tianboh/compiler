(* L1 optimizer
 * Optimizer for pseudo assembly code
 * 1) Const propagation
 * 2) temp propagation
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu> 
 *)

open Core
module T = Parser.Tree
module AS = Inst.Pseudo
module AS_x86 = Inst.X86
module Reg_info = Json_reader.Lab1_checkpoint
module Temp = Var.Temp
module Register = Var.X86_reg
module Memory = Var.Memory

(* munch_stm : T.stm -> AS.instr list *)
(* munch_stm stm generates code to execute stm *)

(* Check if key is stored in cache before, if key -> Imm
 * is stored before, then return Imm, else return key. *)
let const_cache (map : Int32.t Temp.Map.t) (key : AS.operand) : AS.operand =
  match key with
  | AS.Temp k ->
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
 * We will replace right hand side operand temp in mov and binop 
 * with Imm if the temporary has already been stored.*)
let const_propagation (pseudo_assembly : AS.instr list) : AS.instr list =
  let const_map = Temp.Map.empty in
  let rec helper
      (pseudo_assembly : AS.instr list)
      (res : AS.instr list)
      (const_map : Int32.t Temp.Map.t)
    =
    match pseudo_assembly with
    | [] -> res
    | h :: t ->
      (match h with
      | AS.Binop bin ->
        (match bin.op with
        | AS.Plus | AS.Minus | AS.Times | AS.Divided_by | AS.Modulo ->
          let new_l = const_cache const_map bin.lhs in
          let new_r = const_cache const_map bin.rhs in
          helper
            t
            (res @ [ AS.Binop { op = bin.op; lhs = new_l; rhs = new_r; dest = bin.dest } ])
            const_map
        | _ -> helper t (res @ [ h ]) const_map)
      | AS.Mov mov ->
        (match mov.dest, mov.src with
        | AS.Temp tmp, AS.Imm i ->
          let const_map = Temp.Map.set const_map ~key:tmp ~data:i in
          if Temp.is_reg tmp
          then helper t (res @ [ h ]) const_map
          else helper t res const_map
        | AS.Temp _, AS.Temp src ->
          (match Temp.Map.find const_map src with
          | None -> helper t (res @ [ h ]) const_map
          | Some s ->
            helper t (res @ [ AS.Mov { dest = mov.dest; src = AS.Imm s } ]) const_map)
        | _ -> helper t (res @ [ h ]) const_map)
      | _ -> helper t (res @ [ h ]) const_map)
  in
  helper pseudo_assembly [] const_map
;;

(* Check whether temporary key is mapped to a value in coalesce map. *)
let temp_cache (map : Temp.t Temp.Map.t) (key : AS.operand) : AS.operand =
  match key with
  | AS.Imm i -> AS.Imm i
  | AS.Reg r -> AS.Reg r
  | AS.Temp t ->
    (match Temp.Map.find map t with
    | Some v ->
      (* let () = printf "find %s\n" (Temp.name v) in  *)
      AS.Temp v
    | None ->
      (* let () = printf "find %s\n" (Temp.name t) in  *)
      AS.Temp t)
;;

(* When read mov t1 t2, we will generate t3 and use t3 to replace t1 and t2 in the following insts. 
 * Then we build a map to store the mapping relation {t1 : t3} and {t2 : t3} where t1 and t2 are key
 * and t3 is the value. *)
let temp_propagation (ori_insts : AS.instr list) : AS.instr list =
  let temp_map = Temp.Map.empty in
  let rec helper
      (ori_insts : AS.instr list)
      (ret : AS.instr list)
      (map : Temp.t Temp.Map.t)
      : AS.instr list
    =
    match ori_insts with
    | [] -> ret
    | h :: t ->
      (match h with
      | AS.Mov mov ->
        (match mov.dest, mov.src with
        | AS.Temp dest, AS.Temp src ->
          if Temp.is_reg dest
          then (
            let src =
              match Temp.Map.find map src with
              | None -> src
              | Some s -> s
            in
            helper t (ret @ [ AS.Mov { dest = AS.Temp dest; src = AS.Temp src } ]) map)
          else (
            let root =
              match Temp.Map.find map src with
              | None -> src
              | Some s -> s
            in
            let map = Temp.Map.set map ~key:dest ~data:root in
            helper t ret map)
        | _ -> helper t (ret @ [ h ]) map)
      | AS.Binop bin ->
        let new_dest = temp_cache map bin.dest in
        let new_lhs = temp_cache map bin.lhs in
        let new_rhs = temp_cache map bin.rhs in
        helper
          t
          (ret
          @ [ AS.Binop { op = bin.op; dest = new_dest; lhs = new_lhs; rhs = new_rhs } ])
          map
      | _ -> helper t (ret @ [ h ]) map)
  in
  helper ori_insts [] temp_map
;;

let optimize (ori_insts : AS.instr list) : AS.instr list =
  (* let () = print_insts ori_insts in *)
  let ret = temp_propagation ori_insts in
  let ret = const_propagation ret in
  ret
;;
