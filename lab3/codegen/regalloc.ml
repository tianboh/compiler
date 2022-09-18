open Core
open Printf
(* 
    This file contains necessary functions to allocate registers 
    based on input file described as type program in Lab1_checkpoint. 

    I used Hash table from register to register Set 
    as adjacency list to denote interference graph.

    The basic allocation procedure follows:
      1) Build interference graph. We build edge from line.define to line.live_out. 
         We do not build clique based on live_out because this may ignore dependency
         between define and live_out. For example, if the defined temporary is not used
         in the future, so it may not in live_out set, then scheduler may allocate a register
         which is already allocated for the live_out for the current register
         (because there is no edge between define and live_out). 
         PS:If we can eliminate redundant defination in SSA, which means every defination 
         will be in the live_out set, then we can build clique purely based on live_out set.
         Build interference graph time complexity: O(v + e)
      2) Use maximum cardinality search to build SEO
         Theoratically, We initialize every vertex with weight 0. Then, each time 
         we start from a vertex u with maximum weight and update its neighbors weight by one.
         Then we record vertex u and delete from graph, and keep doing so until no vertex left on graph.
         There are lines where %eax or %edx is in the define field. We isolate these nodes in the interferance graph
         because interferance graph is used to describe the relationship between temporaries during register alloc
         To keep the consistance, we do not use %eax nor %edx for temporary register allcation as well.
         In addition, for line whose define field is %eax or %edx, we do not allocate other register as well,
         which means these lines will use %eax or %edx to execute. This avoid superfluous allocation.
         Notice temporaries in interference graph is pure SSA. So we can apply maximum cardinality to find
         optimal register allocation policy.
         Time complexity for SEO: O(v + e)
      3) Greedy coloring based on SEO
         Greedy assign registers in SEO order. We generate register name based on %rxx. where xx is index number
         The rule is generate register with minimum index which is greater than its allocated neighbors.
         Time complexity for coloring: O(v + e)
 *)
module Temp = Temp.Temp
module Register = Register.X86_reg.Register
module Reg_info = Program
type reg = Register.t
type temp = Temp.t
type allocations = (temp * temp) option list
 
(* let (<?>) c (cmp, x, y) = 
  if c = 0
  then cmp x y
  else c;; *)

(* let reg_cmp_pretty (t1 : string) (t2 : string) = 
  Int.compare (String.length t1) (String.length t2)
  <?> (String.compare, t1, t2)
;; *)

(* module TempSet = Set.Make(Temp) *)
(* type t = TempSet.t *)
(* let is_tmp par = 
  String.compare (String.sub par ~pos:1 ~len:1) "t" = 0
;;

let is_reg par = 
  (String.compare (String.sub par ~pos:1 ~len:1) "r" = 0)
  || (String.compare (String.sub par ~pos:1 ~len:1) "e" = 0)
;; *)

(* print adjacency list (interference graph) *)
let print_adj adj = 
  printf "\nprint adj\n";
  let keys = Temp.Map.keys adj in
  let sorted_keys = List.sort keys ~compare:Temp.compare in
  let () = List.iter sorted_keys 
      ~f:(fun key -> 
          let s = Temp.Map.find_exn adj key in
          let l = List.sort (Temp.Set.to_list s) ~compare:Temp.compare in
          printf "From %s to\t" (Temp.name key);
          List.iter l ~f:(fun x -> printf "%s " (Temp.name x));
          printf "\n";
        ) in
  printf "\n\n";
;;

(* Build edge between def and live_out *)
let build_def_lo adj def s_lo =
  let s_def = Temp.Set.of_list [def] in
  Temp.Set.fold_right s_lo ~init:adj ~f:(fun v adj ->
    let s_v = match Temp.Map.find adj v with
      | None -> Temp.Set.empty
      | Some s -> s in
    let s_res = Temp.Set.union s_v s_def in
    Temp.Map.set adj ~key:v ~data:s_res
    )
;;

(* Build interference graph
   1. Build clique based on live_out 
   2. Build based on def and live_out. 
        The insight here is we cannot allocate/assign register for def with the same register as 
        registers allocated for live_out temps
   For lines whose define field is %eax or %edx, we build a isolated node for them and do not
   build edge from them to any temporaries.
*)
let rec _build_graph (prog : Program.temps_info) adj = match prog with 
  | [] -> adj
  | h :: t -> 
    (* let () = print_adj adj in *)
    match Program.get_def h with
      | None -> _build_graph t adj
      | Some def ->
        let s_def_nbr = match Temp.Map.find adj def with 
          | Some s -> s
          | None -> Temp.Set.empty in
        let s_lo = h.live_out in
        let s_u = Temp.Set.union s_def_nbr s_lo in
        let adj = Temp.Map.set adj ~key:def ~data:s_u in
        let adj = build_def_lo adj def s_lo in
        _build_graph t adj
;;

(* Build double(mutually) linked adjacency list based on .in file.*)
let build_graph (prog : Program.temps_info) = 
  let adj = Temp.Map.empty in
  _build_graph prog adj
;;

(* Table store info from temp to register index. *)
let gen_reg_table prog = 
  let hash_init = Temp.Map.empty in
  let rec helper prog hash = match prog with
    | [] -> hash
    | h :: t -> 
      match Program.get_def h with
      | None -> helper t hash
      | Some def_ ->
        let hash = Temp.Map.set hash ~key:def_ ~data:0 in
        helper t hash in 
  helper prog hash_init
;;

let rec _seo adj reg_table seq = 
  match Temp.Map.is_empty reg_table with
  | true -> seq
  | false -> 
    let (u, _) = match Temp.Map.fold reg_table ~init:None 
                         ~f:(fun ~key ~data accu -> 
                             match accu with
                             | None -> 
                               Some (key, data)
                             | Some (_, data') -> 
                               if data' > data 
                               then accu
                               else Some (key, data)
                           ) with
    | None -> failwith "empty reg_table"
    | Some s -> s in 
    let seq_new = seq@[u] in
    let nbr = Temp.Map.find_exn adj u in
    let nbr = Temp.Set.remove nbr u in
    let reg_table = Temp.Set.fold_right nbr ~init:reg_table ~f:(fun x acc -> 
        match Temp.Map.find reg_table x with
        | None -> acc
        | Some v -> 
          let order = v + 1 in
          Temp.Map.set reg_table ~key:x ~data:order;
      ) in
      let reg_table = Temp.Map.remove reg_table u in
      _seo adj reg_table seq_new;
;;

(* We need to consider the influence of pre-coloring, which is stored in tmp_to_reg *)
let seo adj prog = 
  let seq = [] in
  let reg_table = gen_reg_table prog in
  _seo adj reg_table seq
;;

(* Find register name with minimum free order that is greater than any register in its neighbor. 
   If nbr[u] is [1,5,0,2], then find_reg will return 3.
*)
let rec find_reg nbr_reg idx = 
  if Register.Set.mem nbr_reg idx
  then find_reg nbr_reg (Register.create_pp idx)
  else idx
;;

(* Allocate register for tmp. 
   tmp_to_reg is a hashtable from temporary to registers.
   nbr is the neighbor of tmp
*)
let alloc (nbr : Temp.Set.t) (tmp_to_reg : reg Temp.Map.t) : reg = 
  (* let nbr_reg_allocated =  *)
  let nbr_reg_l = Temp.Set.fold nbr ~init:[] ~f:(fun acc u -> 
    match Temp.Map.find tmp_to_reg u with
    | None -> acc
    | Some u' -> [u']@acc) in
  let nbr_reg_s = Register.Set.of_list nbr_reg_l in
  find_reg nbr_reg_s (Register.create_no 1)
;;

(* Infinite registers to allocate during greedy coloring. *)
let rec greedy seq adj tmp_to_reg  = match seq with
  | [] -> tmp_to_reg
  | h :: t -> 
    let nbr = Temp.Map.find_exn adj h in
    let reg = alloc nbr tmp_to_reg in
    let tmp_to_reg = Temp.Map.set tmp_to_reg ~key:h ~data:reg in
    greedy t adj tmp_to_reg 
;;

let rec gen_result (color : reg Temp.Map.t) prog  = match prog with
  | [] -> []
  | h :: t ->
    match Program.get_def h with
    | None -> None :: (gen_result color t)
    | Some tmp ->
      let reg = Temp.Map.find color tmp in
      let tk = match reg with
        | None -> None
        | Some reg' -> Some (tmp, reg') 
      in tk :: (gen_result color t)
;;

let print_tmp_to_reg (color : reg Temp.Map.t) = 
  let () = printf "\n\n==========\nTemporary to register\n" in
  let sorted_keys = List.sort (Temp.Map.keys color) ~compare:Temp.compare in
  List.iter sorted_keys ~f:(fun k -> 
    let t = Temp.name k in
    let r = Register.reg_to_str (Temp.Map.find_exn color k) in
    printf "%s -> %s\n" t r
    );
  let l = List.map (Temp.Map.data color) ~f:(fun x -> x) in
  let s = Register.Set.of_list l in
  printf "Used %d register\n" (Register.Set.length s);
;;

let regalloc (prog : Reg_info.temps_info) : (Temp.t * Register.t) option list =
  let adj = build_graph prog in
  let seq = seo adj prog in
  let tmp_to_reg = Temp.Map.empty in
  let color = greedy seq adj tmp_to_reg in
  (* let () = print_adj adj in
  let () = printf "SEO order\n" in
  let seq_l = List.map seq ~f:(fun x -> Temp.name x) in
  let () = List.iter ~f:(printf "%s ") seq_l in
  let () = print_tmp_to_reg color in
  let () = printf "\n" in *)
  gen_result color prog;