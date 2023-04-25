(* L2 liveness analysis
 * Given a pseudo assembly code, liveness analysis
 * uses dataflow analysis to generate live-out set
 * for each instruction. This information will be 
 * used for reg_alloc_info.
 *
 * Notice that in liveness analysis, gen set of a 
 * statement is its rhs, and kill set is its defination.
 * Also, if a variable appears in both lhs and rhs,
 * then it is only stay in gen set and not in kill set.
 *
 * Author: Tianbo Hao <tianboh@alumni.cmu.edu>
 *)
open Core
module Dfana_info = Json_reader.Lab2_checkpoint
module AS = Inst.Pseudo
module Temp = Var.Temp
module Register = Var.X86_reg
module Dfana = Flow.Dfana
module Label = Util.Label
module IG = Interference_graph

let print_line (line : Dfana_info.line) =
  let () = printf "\n{gen: " in
  let () = List.iter ~f:(fun x -> printf "%d " x) line.gen in
  let () = printf "\nkill: " in
  let () = List.iter ~f:(fun x -> printf "%d " x) line.kill in
  let () = printf "\nsucc: " in
  let () = List.iter ~f:(fun x -> printf "%d " x) line.succ in
  let () = printf "\nis_label: %b" line.is_label in
  printf "\nline_number: %d}\n" line.line_number
;;

let print_df_info df_info = List.iter df_info ~f:(fun line -> print_line line)

(* tmp is from line_no to temporary *)
let print_liveout (liveout : (int list * int list * int) list) =
  List.iter liveout ~f:(fun line ->
      let _, out_l, lo = line in
      let () = printf "line %d lo: " lo in
      let () = List.iter out_l ~f:(fun x -> printf "%d " x) in
      printf "\n")
;;

(* map is from is a hash table with key : IG.Vertex.t and value Int.Set.t 
 * The value corresponds line number that define this variable.
 * t2l stands for temporary to line number set *)
let rec gen_t2l (inst_list : AS.instr list) (line_no : int) map =
  match inst_list with
  | [] -> map
  | h :: t ->
    (match h with
    | AS.Binop binop ->
      let map = update_map binop.dest line_no map in
      gen_t2l t (line_no + 1) map
    | AS.Mov mov ->
      let map = update_map mov.dest line_no map in
      gen_t2l t (line_no + 1) map
    | AS.Jump _ | AS.CJump _ | AS.Ret _ | AS.Label _ -> gen_t2l t (line_no + 1) map
    | AS.Directive _ | AS.Comment _ -> gen_t2l t line_no map)

and update_map dest line_no map =
  match dest with
  | AS.Imm _ -> map
  | AS.Temp tmp ->
    let cur_line_set =
      if IG.Vertex.Map.mem map (IG.Vertex.T.Temp tmp)
      then IG.Vertex.Map.find_exn map (IG.Vertex.T.Temp tmp)
      else Int.Set.empty
    in
    let new_line_set = Int.Set.add cur_line_set line_no in
    IG.Vertex.Map.set map ~key:(IG.Vertex.T.Temp tmp) ~data:new_line_set
;;

(* map is a hash table from label to line number *)
let rec gen_succ (inst_list : AS.instr list) (line_no : int) map =
  match inst_list with
  | [] -> map
  | h :: t ->
    (match h with
    | AS.Label l ->
      let map = Label.Map.set map ~key:l ~data:line_no in
      gen_succ t (line_no + 1) map
    | AS.Jump _ | AS.CJump _ | AS.Ret _ | AS.Mov _ | AS.Binop _ ->
      gen_succ t (line_no + 1) map
    | AS.Directive _ | AS.Comment _ -> gen_succ t line_no map)
;;

let _gen_df_info_helper (op : AS.operand) t2l =
  match op with
  | AS.Temp t ->
    (match IG.Vertex.Map.find t2l (IG.Vertex.T.Temp t) with
    | None -> Int.Set.empty
    | Some s -> s)
  | AS.Imm _ -> Int.Set.empty
;;

let _gen_df_info_binop (line_no : int) (lhs : AS.operand) (rhs : AS.operand) t2l =
  let lhs_int_set = _gen_df_info_helper lhs t2l in
  let rhs_int_set = _gen_df_info_helper rhs t2l in
  let gen = Int.Set.union lhs_int_set rhs_int_set in
  let kill = Int.Set.diff (Int.Set.of_list [ line_no ]) gen in
  let succ = [ line_no + 1 ] in
  let is_label = false in
  ({ gen = Int.Set.to_list gen
   ; kill = Int.Set.to_list kill
   ; succ
   ; is_label
   ; line_number = line_no
   }
    : Dfana_info.line)
;;

let _gen_df_info_mov (line_no : int) (src : AS.operand) t2l =
  let gen = _gen_df_info_helper src t2l in
  let kill = Int.Set.diff (Int.Set.of_list [ line_no ]) gen in
  let succ = [ line_no + 1 ] in
  let is_label = false in
  ({ gen = Int.Set.to_list gen
   ; kill = Int.Set.to_list kill
   ; succ
   ; is_label
   ; line_number = line_no
   }
    : Dfana_info.line)
;;

let _gen_df_info_cjump line_no (lhs : AS.operand) (rhs : AS.operand) t2l label_map target =
  let lhs_int_set = _gen_df_info_helper lhs t2l in
  let rhs_int_set = _gen_df_info_helper rhs t2l in
  let gen = Int.Set.union lhs_int_set rhs_int_set in
  let cond_target_line_no = Label.Map.find_exn label_map target in
  ({ gen = Int.Set.to_list gen
   ; kill = []
   ; succ = [ line_no + 1; cond_target_line_no ]
   ; is_label = false
   ; line_number = line_no
   }
    : Dfana_info.line)
;;

let rec _gen_df_info_rev (inst_list : AS.instr list) line_no t2l label_map res =
  match inst_list with
  | [] -> res
  | h :: t ->
    let line =
      match h with
      | AS.Binop binop -> Some (_gen_df_info_binop line_no binop.lhs binop.rhs t2l)
      | AS.Mov mov -> Some (_gen_df_info_mov line_no mov.src t2l)
      | Jump jp ->
        let target_line_no = Label.Map.find_exn label_map jp.target in
        Some
          ({ gen = []
           ; kill = []
           ; succ = [ target_line_no ]
           ; is_label = false
           ; line_number = line_no
           }
            : Dfana_info.line)
      | CJump cjp ->
        Some (_gen_df_info_cjump line_no cjp.lhs cjp.rhs t2l label_map cjp.target)
      | Ret ret ->
        let gen_int_set = _gen_df_info_helper ret.var t2l in
        Some
          ({ gen = Int.Set.to_list gen_int_set
           ; kill = []
           ; succ = []
           ; is_label = false
           ; line_number = line_no
           }
            : Dfana_info.line)
      | Label _ ->
        Some
          ({ gen = []
           ; kill = []
           ; succ = [ line_no + 1 ]
           ; is_label = true
           ; line_number = line_no
           }
            : Dfana_info.line)
      | Directive _ | Comment _ -> None
    in
    (match line with
    | None -> _gen_df_info_rev t line_no t2l label_map res
    | Some line_s -> _gen_df_info_rev t (line_no + 1) t2l label_map (line_s :: res))
;;

let gen_df_info (inst_list : AS.instr list) : Dfana_info.line list =
  let t2l = IG.Vertex.Map.empty in
  let t2l = gen_t2l inst_list 0 t2l in
  let label_map = Label.Map.empty in
  let label_map = gen_succ inst_list 0 label_map in
  let res_rev = _gen_df_info_rev inst_list 0 t2l label_map [] in
  List.rev res_rev
;;

let rec gen_temp (inst_list : AS.instr list) line_no map =
  match inst_list with
  | [] -> map
  | h :: t ->
    (match h with
    | AS.Binop binop ->
      let map = Int.Map.set map ~key:line_no ~data:binop.dest in
      gen_temp t (line_no + 1) map
    | AS.Mov mov ->
      let map = Int.Map.set map ~key:line_no ~data:mov.dest in
      gen_temp t (line_no + 1) map
    | AS.Jump _ | AS.CJump _ | AS.Ret _ | AS.Label _ -> gen_temp t (line_no + 1) map
    | AS.Directive _ | AS.Comment _ -> gen_temp t line_no map)
;;

(* Transform liveness information from int to temp. 
 * lo_int is the dataflow analysis result.
 * tmp_map is map from line_number to temporary *)
let rec trans_liveness lo_int tmp_map res =
  match lo_int with
  | [] -> res
  | h :: t ->
    let _, out_int_list, line_no = h in
    let liveout =
      List.fold out_int_list ~init:IG.Vertex.Set.empty ~f:(fun acc x ->
          match Int.Map.find tmp_map x with
          | None ->
            let err_msg = sprintf "cannot find temporary def at line %d" x in
            failwith err_msg
          | Some s ->
            (match s with
            | AS.Imm _ -> failwith "liveout should not be immediate"
            | AS.Temp t -> IG.Vertex.Set.add acc (IG.Vertex.T.Temp t)))
    in
    let res = Int.Map.set res ~key:line_no ~data:liveout in
    trans_liveness t tmp_map res
;;

let gen_liveness (inst_list : AS.instr list) =
  let df_info = gen_df_info inst_list in
  (* let () = print_df_info df_info in *)
  let lo_int = Dfana.dfana df_info Args.Df_analysis.Backward_may in
  let tmp_map = gen_temp inst_list 0 Int.Map.empty in
  (* let () = print_liveout lo_int in *)
  trans_liveness lo_int tmp_map Int.Map.empty
;;
