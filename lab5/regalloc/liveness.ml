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
module Temp = Var.Temp
module Register = Var.X86_reg.Logic
module Dfana = Flow.Dfana
module Label = Util.Label
module IG = Regalloc_util.Interference_graph
module VSet = IG.Vertex.Set

(* module Op = Abs_asm.Op *)
(* module Inst = Abs_asm.Inst *)
(* module Line = Abs_asm.Trans.Line *)

module type OpSig = sig
  include Regalloc_util.Line.Op

  val to_int_list : t list -> int list
  val of_temp : Temp.t -> t
  val of_reg : Register.t -> t
  val to_temp_exn : t -> Temp.t
  val to_reg_exn : t -> Register.t
end

module type InstrInterface = sig
  type instr

  val is_label : instr -> bool
  val is_return : instr -> bool
  val is_cjump : instr -> bool
  val is_jump : instr -> bool
  val get_label : instr -> Label.t
  val get_cjump_targets_exn : instr -> Label.t * Label.t
  val get_jump_target_exn : instr -> Label.t
end

module type Line = sig
  type op

  type move =
    | Phi
    | Copy
    | Not

  type t =
    { uses : op list
    ; defines : op list
    ; live_out : op list
    ; move : move
    }
end

module Wrapper (Op : OpSig) (Inst : InstrInterface) (Line : Line with type op = Op.t) =
struct
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
  let rec gen_succ (instrs : (Inst.instr * Line.t) list) (line_no : int) map =
    match instrs with
    | [] -> map
    | h :: t ->
      let instr, _ = h in
      if Inst.is_label instr
      then (
        let l = Inst.get_label instr in
        let map = Label.Map.set map ~key:l ~data:line_no in
        gen_succ t (line_no + 1) map)
      else gen_succ t (line_no + 1) map
  ;;

  let[@warning "-8"] _gen_df_info_helper (line_number : int) (line : Line.t) =
    let uses = line.uses in
    let defs = line.defines in
    let gen = Int.Set.of_list (Op.to_int_list uses) in
    let kill = Int.Set.of_list (Op.to_int_list defs) in
    let kill = Int.Set.diff kill gen in
    let succ = [ line_number + 1 ] in
    let is_label = false in
    ({ gen = Int.Set.to_list gen
     ; kill = Int.Set.to_list kill
     ; succ
     ; is_label
     ; line_number
     }
      : Dfana_info.line)
  ;;

  let[@warning "-8"] _gen_df_info_cjump
      line_number
      (line : Line.t)
      target_true
      target_false
      label_map
      : Dfana_info.line
    =
    let uses = line.uses in
    let gen = Int.Set.of_list (Op.to_int_list uses) in
    let target_true_no = Label.Map.find_exn label_map target_true in
    let target_false_no = Label.Map.find_exn label_map target_false in
    let gen = Int.Set.to_list gen in
    let succ = [ target_true_no; target_false_no ] in
    { gen; kill = []; succ; is_label = false; line_number }
  ;;

  let rec _gen_df_info_rev (instrs : (Inst.instr * Line.t) list) line_number label_map res
    =
    match instrs with
    | [] -> res
    | h :: t ->
      let instr, line = h in
      let line' : Dfana_info.line option =
        if Inst.is_label instr
        then (
          let succ = [ line_number + 1 ] in
          Some { gen = []; kill = []; succ; is_label = true; line_number })
        else if Inst.is_return instr
        then (
          let gen, kill = Op.to_int_list line.uses, Op.to_int_list line.defines in
          Some { gen; kill; succ = []; is_label = false; line_number })
        else if Inst.is_cjump instr
        then (
          let target_true, target_false = Inst.get_cjump_targets_exn instr in
          Some (_gen_df_info_cjump line_number line target_true target_false label_map))
        else if Inst.is_jump instr
        then (
          let target = Inst.get_jump_target_exn instr in
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
  let gen_df_info (instrs : (Inst.instr * Line.t) list) : Dfana_info.line list =
    let label_map = Label.Map.empty in
    let label_map = gen_succ instrs 0 label_map in
    let res_rev = _gen_df_info_rev instrs 0 label_map [] in
    List.rev res_rev
  ;;

  (* Transform liveness information from int to temp. 
   * lo_int is the dataflow analysis result. *)
  let rec trans_liveness (lo_int : (int list * int list * int) list) res =
    match lo_int with
    | [] -> List.rev res
    | h :: t ->
      let _, out_int_list, _ = h in
      let liveout =
        List.fold out_int_list ~init:[] ~f:(fun acc x ->
            if x >= Register.num_reg
            then Op.of_temp (Temp.of_int x) :: acc
            else Op.of_reg (Register.idx_reg x) :: acc)
      in
      let res = liveout :: res in
      trans_liveness t res
  ;;

  let of_abs (op : Op.t) : VSet.t =
    if Op.is_temp op
    then VSet.of_list [ Temp (Op.to_temp_exn op) ]
    else if Op.is_reg op
    then VSet.of_list [ Reg (Op.to_reg_exn op) ]
    else VSet.empty
  ;;

  let rec is_lazy (lines : Line.t list) res =
    match lines with
    | [] -> IG.Vertex.Set.length res > 2000
    | line :: t ->
      let res =
        List.fold (line.defines @ line.uses) ~init:res ~f:(fun acc u ->
            IG.Vertex.Set.union acc (of_abs u))
      in
      is_lazy t res
  ;;

  let gen_liveness (instr_line_list : (Inst.instr * Line.t) list) : Line.t list * bool =
    let _, lines = List.unzip instr_line_list in
    let is_lazy = is_lazy lines IG.Vertex.Set.empty in
    if is_lazy
    then lines, is_lazy
    else (
      let df_info = gen_df_info instr_line_list in
      (* print_df_info df_info; *)
      let lo_int = Dfana.dfana df_info Args.Df_analysis.Backward_may in
      (* print_liveout lo_int; *)
      let live_outs = trans_liveness lo_int [] in
      ( List.map2_exn lines live_outs ~f:(fun line lo ->
            let live_out =
              match line.move with
              | Copy | Phi -> lo
              | Not -> line.uses @ lo
            in
            { line with live_out })
      , is_lazy ))
  ;;
end
