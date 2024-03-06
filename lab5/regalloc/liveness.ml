(* L3 liveness analysis
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
module Abs_asm = Abs_asm.Inst
module Temp = Var.Temp
module Register = Var.X86_reg.Logic
module Dfana = Flow.Dfana
module Label = Util.Label
module IG = Interference_graph

let print_line (line : Dfana_info.line) =
  printf "\n{gen: ";
  List.iter ~f:(fun x -> printf "%d " x) line.gen;
  printf "\nkill: ";
  List.iter ~f:(fun x -> printf "%d " x) line.kill;
  printf "\nsucc: ";
  List.iter ~f:(fun x -> printf "%d " x) line.succ;
  printf "\nis_label: %b" line.is_label;
  printf "\nline_number: %d}\n" line.line_number
;;

let print_df_info df_info = List.iter df_info ~f:(fun line -> print_line line)

(* tmp is from line_no to temporary *)
let print_liveout (liveout : (int list * int list * int) list) =
  List.iter liveout ~f:(fun line ->
      let _, out_l, lo = line in
      printf "line %d lo: " lo;
      List.iter out_l ~f:(fun x -> printf "%d " x);
      printf "\n")
;;

(* map is a hash table from label to line number *)
let rec gen_succ (inst_list : Abs_asm.instr list) (line_no : int) map =
  match inst_list with
  | [] -> map
  | h :: t ->
    if Abs_asm.is_dummy h
    then gen_succ t line_no map
    else if Abs_asm.is_label h
    then (
      let l = Abs_asm.get_label h in
      let map = Label.Map.set map ~key:l ~data:line_no in
      gen_succ t (line_no + 1) map)
    else gen_succ t (line_no + 1) map
;;

let[@warning "-8"] _gen_df_info_helper (line_number : int) (line : Abs_asm.line) =
  let uses = line.uses in
  let defs = line.defines in
  let gen = Int.Set.of_list (Abs_asm.to_int_list uses) in
  let kill = Int.Set.of_list (Abs_asm.to_int_list defs) in
  let kill = Int.Set.diff kill gen in
  let succ = [ line_number + 1 ] in
  let is_label = false in
  ({ gen = Int.Set.to_list gen; kill = Int.Set.to_list kill; succ; is_label; line_number }
    : Dfana_info.line)
;;

let[@warning "-8"] _gen_df_info_cjump
    line_number
    (line : Abs_asm.line)
    target_true
    target_false
    label_map
    : Dfana_info.line
  =
  let uses = line.uses in
  let gen = Int.Set.of_list (Abs_asm.to_int_list uses) in
  let target_true_no = Label.Map.find_exn label_map target_true in
  let target_false_no = Label.Map.find_exn label_map target_false in
  let gen = Int.Set.to_list gen in
  let succ = [ target_true_no; target_false_no ] in
  { gen; kill = []; succ; is_label = false; line_number }
;;

let rec _gen_df_info_rev (inst_list : Abs_asm.instr list) line_number label_map res =
  match inst_list with
  | [] -> res
  | h :: t ->
    let line = h.line in
    let line' : Dfana_info.line option =
      if Abs_asm.is_dummy h
      then None
      else if Abs_asm.is_label h
      then (
        let succ = [ line_number + 1 ] in
        Some { gen = []; kill = []; succ; is_label = true; line_number })
      else if Abs_asm.is_return h
      then (
        let gen, kill = Abs_asm.to_int_list line.uses, Abs_asm.to_int_list line.defines in
        Some { gen; kill; succ = []; is_label = false; line_number })
      else if Abs_asm.is_cjump h
      then (
        let target_true, target_false = Abs_asm.get_cjump_targets_exn h in
        Some (_gen_df_info_cjump line_number line target_true target_false label_map))
      else if Abs_asm.is_jump h
      then (
        let target = Abs_asm.get_jump_target_exn h in
        let succ = [ Label.Map.find_exn label_map target ] in
        Some { gen = []; kill = []; succ; is_label = false; line_number })
      else Some (_gen_df_info_helper line_number line)
    in
    (match line' with
    | None -> _gen_df_info_rev t line_number label_map res
    | Some line_s -> _gen_df_info_rev t (line_number + 1) label_map (line_s :: res))
;;

(* Generate information for each instruction. Info includes
 * gen, kill, succ, is_label, line_number *)
let gen_df_info (inst_list : Abs_asm.instr list) : Dfana_info.line list =
  let label_map = Label.Map.empty in
  let label_map = gen_succ inst_list 0 label_map in
  let res_rev = _gen_df_info_rev inst_list 0 label_map [] in
  List.rev res_rev
;;

(* Transform liveness information from int to temp. 
 * lo_int is the dataflow analysis result. *)
let rec trans_liveness (lo_int : (int list * int list * int) list) res =
  match lo_int with
  | [] -> res
  | h :: t ->
    let _, out_int_list, line_no = h in
    let liveout =
      List.fold out_int_list ~init:IG.Vertex.Set.empty ~f:(fun acc x ->
          if x >= Register.num_reg
          then IG.Vertex.Set.add acc (IG.Vertex.T.Temp (Temp.of_int x))
          else IG.Vertex.Set.add acc (IG.Vertex.T.Reg (Register.idx_reg x)))
    in
    let res = Int.Map.set res ~key:line_no ~data:liveout in
    trans_liveness t res
;;

let gen_liveness (inst_list : Abs_asm.instr list) =
  let df_info = gen_df_info inst_list in
  (* print_df_info df_info; *)
  let lo_int = Dfana.dfana df_info Args.Df_analysis.Backward_may in
  (* print_liveout lo_int; *)
  trans_liveness lo_int Int.Map.empty
;;
