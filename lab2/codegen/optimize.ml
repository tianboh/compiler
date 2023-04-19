(* L2 pseudo code optimizer
 *
 * Optimization contains 
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
          let lhs = const_cache const_map bin.lhs in
          let rhs = const_cache const_map bin.rhs in
          let op = bin.op in
          let dest = bin.dest in
          let const_map =
            match dest with
            | AS.Imm _ -> failwith "dest should not be imm"
            | AS.Temp temp ->
              (* update const_map because destination is updated. *)
              Temp.Map.remove const_map temp
          in
          helper t (res @ [ AS.Binop { op; lhs; rhs; dest } ]) const_map
        | _ -> helper t (res @ [ h ]) const_map)
      | AS.Mov mov ->
        (match mov.dest, mov.src with
        | AS.Temp tmp, AS.Imm i ->
          let const_map = Temp.Map.set const_map ~key:tmp ~data:i in
          helper t res const_map
        | AS.Temp dest, AS.Temp src ->
          (match Temp.Map.find const_map src with
          | None ->
            (* Update const map if dest is already in cache key. *)
            let const_map = Temp.Map.remove const_map dest in
            helper t (res @ [ h ]) const_map
          | Some s ->
            let const_map = Temp.Map.set const_map ~key:dest ~data:s in
            helper t res const_map)
        | _ -> helper t (res @ [ h ]) const_map)
      | AS.Ret ret ->
        (match ret.var with
        | AS.Imm _ -> helper t (res @ [ h ]) const_map
        | AS.Temp temp ->
          (match Temp.Map.find const_map temp with
          | Some _ ->
            let v = Temp.Map.find_exn const_map temp in
            helper t (res @ [ AS.Ret { var = AS.Imm v } ]) const_map
          | None -> helper t (res @ [ h ]) const_map))
      | _ -> helper t (res @ [ h ]) const_map)
  in
  helper pseudo_assembly [] const_map
;;

(* Check whether temporary key is mapped to a value in coalesce map. *)
let temp_cache (map : Temp.t Temp.Map.t) (key : AS.operand) : AS.operand =
  match key with
  | AS.Imm i -> AS.Imm i
  | AS.Temp t ->
    (match Temp.Map.find map t with
    | Some v ->
      (* let () = printf "find %s\n" (Temp.name v) in  *)
      AS.Temp v
    | None ->
      (* let () = printf "find %s\n" (Temp.name t) in  *)
      AS.Temp t)
;;

(* Does not work yet because IR is not SSA.
 * Eliminate intermediate movement instruction. 
 * This can simplify adj graph in reg alloc.
 * For example, the original program is
 * y = x
 * z = 3 + y
 * Copy propagation would yield
 * z = 3 + x *)
let copy_propagation (ori_insts : AS.instr list) : AS.instr list =
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
          let root =
            match Temp.Map.find map src with
            | None -> src
            | Some s -> s
          in
          let map = Temp.Map.set map ~key:dest ~data:root in
          helper t ret map
        | _, _ -> helper t (ret @ [ h ]) map)
      | AS.Binop bin ->
        let dest = bin.dest in
        let lhs = temp_cache map bin.lhs in
        let rhs = temp_cache map bin.rhs in
        (* let map =
          match dest with
          | Temp tmp ->
            if Temp.Map.mem map tmp
            then failwith "Pseudo assembly should be SSA, dest should not be decl before"
            else map
          | _ -> map
        in *)
        helper t (ret @ [ AS.Binop { op = bin.op; dest; lhs; rhs } ]) map
      | AS.Ret ret_as ->
        let value = temp_cache map ret_as.var in
        helper t (ret @ [ AS.Ret { var = value } ]) map
      | _ -> helper t (ret @ [ h ]) map)
  in
  helper ori_insts [] temp_map
;;

let optimize (ori_insts : AS.instr list) : AS.instr list =
  (* let () = print_insts ori_insts in *)
  let ret = const_propagation ori_insts in
  (* let ret = copy_propagation ret in *)
  ret
;;
