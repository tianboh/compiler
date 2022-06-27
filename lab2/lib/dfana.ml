(*
  This file is used to achieve data flow analysis.
  We use 0 and -1 to denote entry and exit point respectively
  So there is only one entry point and one exit point in the whole program
*)
open Core
open Json_reader.Lab2_checkpoint
open Args
(* open Printf *)

module IntSet = Set.Make(Int)

type block = {
  pred : IntSet.t
; succ : IntSet.t
; gen : IntSet.t
; kill : IntSet.t
; in_ : IntSet.t
; out_ : IntSet.t
; no : int
} 

let empty_blk blk_no = 
  {
    pred = IntSet.empty
  ; succ = IntSet.empty
  ; gen = IntSet.empty
  ; kill = IntSet.empty
  ; in_ = IntSet.empty
  ; out_ = IntSet.empty
  ; no = blk_no
  }
;;

let get_l2b prog block_no = 
  let l2b = Hashtbl.create (module Int) in  (* line to block *)
  let rec _get_l2b prog block_no = match prog with
    | [] -> l2b
    | h :: t -> 
      if h.is_label
      then 
        let new_block_no = block_no + 1 in
        let () = Hashtbl.set l2b ~key:h.line_number ~data:new_block_no in
        _get_l2b t new_block_no
      else 
        let () = Hashtbl.set l2b ~key:h.line_number ~data:block_no in
        _get_l2b t block_no in
  _get_l2b prog block_no
;;

(* 
  Each block gets a interval [a, b] indicates its line number range. Both sides are inclusivE.
*)
let get_b2l l2b = 
  let l = Hashtbl.to_alist l2b in
  let b2l = Hashtbl.create (module Int) in
  let b2l_s = Hashtbl.create (module Int) in
  let () = List.iter l ~f:(fun (l,b) -> 
      if Hashtbl.mem b2l_s b 
      then
        Hashtbl.set b2l_s ~key:b ~data:(IntSet.union (Hashtbl.find_exn b2l_s b) (IntSet.of_list [l]))
      else
        Hashtbl.set b2l_s ~key:b ~data:(IntSet.of_list [l])
    ) in
  let () = Hashtbl.iter_keys b2l_s ~f:(fun b -> 
      let s = Hashtbl.find_exn b2l_s b in
      Hashtbl.set b2l ~key:b ~data:(IntSet.min_elt_exn s, IntSet.max_elt_exn s)
    ) in
  b2l
;;

let print_b2l b2l = 
  let keys = Hashtbl.keys b2l in
  let sorted_keys = List.sort keys ~compare:Int.compare in
  List.iter sorted_keys ~f:(fun x -> 
      let (s, e) = Hashtbl.find_exn b2l x in
      printf "block %d [%d, %d]\n" x s e)

let print_l2b l2b = 
  Hashtbl.iteri l2b ~f:(fun ~key:k ~data:v -> printf "line %d block %d\n" k v)
;;

(* group lines from is_label to is_label, first is_lable is inclusive and the second is exclusive *)
let group_lines prog = 
  let l = [] in
  let acc = [] in
  let rec helper prog inclusive l acc = match prog with
    | [] -> if List.is_empty acc then l else l @ [acc]
    | h :: t -> 
      if h.is_label && (not inclusive) then helper ([h]@t) true ([acc] @ l) []
      else if h.is_label then helper t false l [h]
      else if inclusive then failwith "fail at group lines"
      else helper t inclusive l (acc @ [h])
  in helper prog true l acc
;;

let rec _group_lines_logical lss acc = match lss with
  | [] -> acc
  | h :: t -> 
    let new_h = List.rev h in
    _group_lines_logical t (acc @ [new_h])
;;

let group_lines_logical prog (df_type : Df_analysis.t) = 
  let lss = group_lines prog in
  let lss_logical = match df_type with 
    | Forward_must | Forward_may -> lss
    | Backward_must | Backward_may -> _group_lines_logical lss []
    | _ -> failwith "failed at group_lines_logical" in
  lss_logical
;;

let get_block_succ (ls : line list) l2b = 
  let blk_lines_l = List.map ls ~f:(fun line -> line.line_number) in
  let blk_lines_s = IntSet.of_list blk_lines_l in
  let blk_succ_lines_l = List.fold_left ls ~init:[] ~f:(fun acc line -> line.succ @ acc) in
  let blk_succ_lines_s = IntSet.of_list blk_succ_lines_l in
  let succ = IntSet.diff blk_succ_lines_s blk_lines_s in
  if IntSet.is_empty succ
  then IntSet.of_list [-1]
  else IntSet.map succ ~f:(fun s -> Hashtbl.find_exn l2b s)
;;

let get_block_gen_kill (ls : line list) =
  let gen = IntSet.empty in
  let kill = IntSet.empty in
  let rec helper (ls : line list) gen kill = match ls with
    | [] -> (gen, kill)
    | h :: t -> 
      (* gen[BB] <- gen[BB] U gen[s] - kill[s] *)
      let gen' = IntSet.diff (IntSet.union gen (IntSet.of_list h.gen)) (IntSet.of_list h.kill) in
      (* kill[BB] <- kill[BB] U kill[s] - gen[s] *)
      let kill' = IntSet.diff (IntSet.union kill (IntSet.of_list h.kill)) (IntSet.of_list h.gen) in
      helper t gen' kill'
  in helper ls gen kill
;;

(* 
  build a block based on lines within the same block
  ls: lines within a block, guaranteed to be non-empty 
*)
let build_one_block ls l2b = 
  let first_line = List.nth_exn ls 0 in
  let blk_no = Hashtbl.find_exn l2b first_line.line_number in
  let succ = get_block_succ ls l2b in
  (* let () = printf "---build block %d\n" blk_no in *)
  let gen, kill = get_block_gen_kill ls in
  let blk = empty_blk blk_no in
  {blk with succ = succ; gen = gen; kill=kill}
;;

(* Set up successors, gen, kill field *)
let rec build_blocks_step1 lss l2b blocks = match lss with
  | [] -> blocks
  | h :: t -> 
    let blk = build_one_block h l2b in
    let () = Hashtbl.set blocks ~key:blk.no ~data:blk in
    build_blocks_step1 t l2b blocks
;;

(* Set up pred field *)
let build_blocks_step2 blocks = 
  let blk_no_l = Hashtbl.keys blocks in
  let () = List.iter blk_no_l 
      ~f:(fun blk_no -> 
          let blk = Hashtbl.find_exn blocks blk_no in
          let u_succ_int_l = IntSet.to_list blk.succ in
          let u_succ_blk_l = List.map u_succ_int_l ~f:(fun blk_no -> Hashtbl.find_exn blocks blk_no) in
          List.iter u_succ_blk_l ~f:(fun v -> 
              let v'={v with pred = IntSet.union v.pred (IntSet.of_list [blk_no])} in
              Hashtbl.set blocks ~key:v.no ~data:v')
        ) in 
  blocks

(* Get full set for generator line. *)
let get_full_set blocks = 
  Hashtbl.fold blocks ~init:IntSet.empty ~f:(fun ~key:_ ~data:blk acc -> IntSet.union acc blk.gen)
;;

(* 
  Set up default output/input field in blocks based on forward/backward must/may analysis.
 *)
let build_blocks_step3 blocks (df_type : Df_analysis.t) = 
  let blk_no_l = Hashtbl.keys blocks in
  let logical_init = match df_type with 
    | Forward_must | Backward_must -> get_full_set blocks
    | Forward_may | Backward_may -> IntSet.empty
    | _ -> failwith "invalid input for build_blocks_step3" in
  let () = List.iter blk_no_l ~f:(
      fun blk_no -> 
        let blk = Hashtbl.find_exn blocks blk_no in
        let blk_new = match df_type with
          | Forward_must | Forward_may -> {blk with out_ = logical_init}
          | Backward_must | Backward_may -> {blk with in_ = logical_init}
          | _ -> failwith "invalid input for build_blocks_step3 iter" in
        Hashtbl.set blocks ~key:blk_no ~data:blk_new
    ) in
  blocks
;;

let build_blocks lss l2b df_type =
  let blocks = Hashtbl.create (module Int) in
  let () = Hashtbl.set blocks ~key:(-1) ~data:(empty_blk (-1)) in
  let blocks = build_blocks_step1 lss l2b blocks in
  let blocks = build_blocks_step2 blocks in
  let blocks = build_blocks_step3 blocks df_type in
  blocks
;;

let print_blocks blocks = 
  let blk_no_l = Hashtbl.keys blocks in
  let blk_no_l_sort = List.sort blk_no_l ~compare:Int.compare in
  List.iter blk_no_l_sort ~f:(fun blk_no -> 
      let blk = Hashtbl.find_exn blocks blk_no in
      let () = printf "===blk_no %d===" blk_no in
      let gen = IntSet.to_list blk.gen in
      let () = printf "\ngen " in
      let () = List.iter ~f:(printf "%d ") gen in
      let kill = IntSet.to_list blk.kill in
      let () = printf "\nkill " in
      let () = List.iter ~f:(printf "%d ") kill in
      let pred = IntSet.to_list blk.pred in
      let () = printf "\npred " in
      let () = List.iter ~f:(printf "%d ") pred in
      let succ = IntSet.to_list blk.succ in
      let () = printf "\nsucc " in
      let () = List.iter ~f:(printf "%d ") succ in
      let in_ = IntSet.to_list blk.in_ in
      let () = printf "\nin " in
      let () = List.iter ~f:(printf "%d ") in_ in
      let out_ = IntSet.to_list blk.out_ in
      let () = printf "\nout " in
      let () = List.iter ~f:(printf "%d ") out_ in
      printf "\n"
    )
;;

let rec unfold_right f init =
  match f init with
  | None -> []
  | Some (x, next) -> x :: unfold_right f next
;;

(* 
  [init, init + n)
 *)
let range init n =
  let irange x = if x >= init + n then None else Some (x, x + 1) in
  unfold_right irange init
;;

(*  
    Swap predecessors and successors if dataflow analysis is backward.
    This can make DFS life easier in backward analysis.
*)
let swap_pred_succ blocks = 
  let blk_no_list = Hashtbl.keys blocks in
  let () = List.iter blk_no_list 
      ~f:(fun blk_no -> 
          let blk = Hashtbl.find_exn blocks blk_no in
          let blk_swap = {blk with pred = blk.succ; succ = blk.pred} in
          Hashtbl.set blocks ~key:blk_no ~data:blk_swap
        ) in
  blocks
;;

(* 
  Swap in and out set for blocks. This is used when backward analysis is finished.
 *)
let swap_in_out blocks = 
  let blk_no_list = Hashtbl.keys blocks in
  let () = List.iter blk_no_list 
      ~f:(fun blk_no -> 
          let blk = Hashtbl.find_exn blocks blk_no in
          let blk_swap = {blk with out_ = blk.in_; in_ = blk.out_} in
          Hashtbl.set blocks ~key:blk_no ~data:blk_swap
        ) in
  blocks
;;

(* 
  Calculate out set of predecessors of v. That is u -> v
  The output of predecessors will be combined using union or intersection decided by df_type
  This is also the in set for block v.
*)
let get_preds_out v blocks df_type = 
  let us_l = IntSet.to_list v.pred in
  let us_blk = List.map us_l ~f:(fun blk_no -> Hashtbl.find_exn blocks blk_no) in
  let preds_out = List.map us_blk ~f:(fun blk -> blk.out_) in
  match df_type with
  | Df_analysis.Forward_may| Df_analysis.Backward_may ->
    List.fold_left preds_out ~init:IntSet.empty ~f:(fun acc out -> IntSet.union acc out)
  | Df_analysis.Forward_must| Df_analysis.Backward_must -> 
    let init_set = match List.nth preds_out 0 with
      | Some s -> s
      | None -> IntSet.empty
    in
    (* let () = printf "  init_set is " in
       let () = IntSet.iter init_set ~f:(fun x -> printf "%d " x) in
       let () = printf "\n" in *)
    List.fold_left preds_out ~init:init_set ~f:(fun acc out -> IntSet.inter acc out)
  | Df_analysis.No_analysis -> failwith "error for input type no_analysis in get_preds_out"
;;

let process_out block in_  = 
  IntSet.union (block.gen) (IntSet.diff (in_) (block.kill))
;;

let rec _dfs blocks df_type queue = 
  match queue with
  | [] -> blocks
  | blk_no :: t -> 
    let v = Hashtbl.find_exn blocks blk_no in
    (* let () = printf "_dfs block %d\n" blk_no in *)
    let in_ = get_preds_out v blocks df_type in
    let out_ = process_out v in_ in
    let v' = {v with out_ = out_; in_ = in_} in
    let () = Hashtbl.set blocks ~key:blk_no ~data:v' in
    if IntSet.equal v'.out_ v.out_ 
    then 
      _dfs blocks df_type t
    else 
      let l = t @ (IntSet.to_list v'.succ) in
      _dfs blocks df_type l
;;

(* 
  There are 4 types of dataflow analysis. We treat backward or forward the same
  by swapping block predecessors and successors in backward analysis.
  Once finished DFS, we need to swap in and out field for backward analysis.
 *)
let dfs blocks (df_type : Df_analysis.t) = 
  let order = range 0 ((Hashtbl.length blocks) -1) in
  let blocks_logical = match df_type with
    | Df_analysis.Forward_may| Df_analysis.Forward_must  -> 
      _dfs blocks df_type (order @ [-1])
    | Df_analysis.Backward_may| Df_analysis.Backward_must ->
      let blocks = swap_pred_succ blocks in
      let blocks = swap_in_out blocks in
      let blocks = _dfs blocks df_type ([-1] @ (List.rev order)) in
      let blocks = swap_in_out blocks in
      swap_pred_succ blocks
    | Df_analysis.No_analysis -> failwith "error for input type no_analysis in dfs" in 
  let () = Hashtbl.remove blocks_logical (-1) in
  blocks_logical
;;

let store_info prog = 
  let lines = Hashtbl.create (module Int) in 
  let rec helper prog  = match prog with
    | [] -> lines
    | h :: t -> 
      let () = Hashtbl.set lines ~key:h.line_number ~data:h in
      helper t
  in helper prog
;;

(* 
  Notice in_logical is not necessary to be the real in set for line, this in_logical is a logical concept.
  If we pass out field in backward analysis as in_logical, this function still works.
  And this is what we have done in backward analysis.
*)
let process_line (line_info : line) (in_logical : IntSet.t) =
  let gen = IntSet.of_list line_info.gen in
  let kill = IntSet.of_list line_info.kill in
  let out_logical = IntSet.union gen (IntSet.diff in_logical kill) in
  out_logical
;;

let one_block_to_lines lines_info block res df_type line_l = 
  let in_logical = match df_type with
    | Df_analysis.Forward_may| Df_analysis.Forward_must -> block.in_
    | Df_analysis.Backward_may| Df_analysis.Backward_must -> block.out_
    | Df_analysis.No_analysis -> failwith "error for input type no_analysis in one_block_to_lines" in
  let line_l = match df_type with
    | Df_analysis.Forward_may| Df_analysis.Forward_must -> line_l
    | Df_analysis.Backward_may| Df_analysis.Backward_must -> List.rev line_l
    | _ -> failwith "error for input type no_analysis in one_block_to_lines" in
  let rec helper ls in_logical lines_info res = match ls with
    | [] ->  res
    | h :: t ->
      let line_info = Hashtbl.find_exn lines_info h in
      let out_logical = process_line line_info in_logical in
      let () = match df_type with
        | Df_analysis.Forward_may| Df_analysis.Forward_must -> Hashtbl.set res ~key:h ~data:(in_logical, out_logical)
        | Df_analysis.Backward_may| Df_analysis.Backward_must -> Hashtbl.set res ~key:h ~data:(out_logical, in_logical)
        |_ -> failwith "error for input type no_analysis in one_block_to_lines helper"
      in 
      helper t out_logical lines_info res
  in helper line_l in_logical lines_info res
;;

(* 
  Given blocks that finished dataflow analysis. Convert the blocks to line format with in and out field.
*)
let blocks_to_lines blocks lines_info b2l df_type = 
  let res = Hashtbl.create (module Int) in
  let blks_no = Hashtbl.keys blocks in
  let rec helper blks_no res = match blks_no with
    | [] -> res
    | h :: t -> 
      let block = Hashtbl.find_exn blocks h in
      let s, e = Hashtbl.find_exn b2l block.no in
      let line_l = range s (e - s + 1) in
      let res = one_block_to_lines lines_info block res df_type line_l in
      helper t res
  in helper blks_no res
;;

let gen_res res = 
  let keys = Hashtbl.keys res in
  let keys_ordered = List.sort keys ~compare:Int.compare in
  let accu = [] in 
  let rec helper lines accu = match lines with
    | [] -> accu
    | h :: t -> 
      let line_in_set, line_out_set = Hashtbl.find_exn res h in
      let line_in = IntSet.to_list line_in_set in
      let line_out = IntSet.to_list line_out_set in
      let accu = accu @ [(line_in, line_out, h)] in
      helper t accu
  in helper keys_ordered accu
;;

let dfana (prog : program) (df_type : Df_analysis.t) = 
  let l2b = get_l2b prog (-1) in
  let b2l = get_b2l l2b in
  let line_info = store_info prog in
  let lss = group_lines_logical prog df_type in
  let blocks = build_blocks lss l2b df_type in
  let blocks = dfs blocks df_type in
  let res = blocks_to_lines blocks line_info b2l df_type in
  gen_res res
;;