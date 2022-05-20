open Core
open Lab1_checkpoint
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
         In this assignment, since it is not a pure SSA, we pre-fix the register where define is %eax and %edx
         as hard ware register %eax and %edx respectively. So we assign the weight for them as one and the rest
         temporarys as zero. This makes sure %eax is first colored in the future. However, the second potential
         allocated register is not necessary %edx, so it is sub-optimal compared with scenarios in pure SSA.
         Time complexity for SEO: O(v + e)
      3) Greedy coloring based on SEO
         Greedy assign registers in SEO order. We generate register name based on %rxx. where xx is index number
         The rule is generate register with minimum index which is greater than its allocated neighbors.
         Time complexity for coloring: O(v + e)

    Subtle issues(s)
      1) The input file is not pure SSA because it contains register %eax and %edx.
         So we need to fix register allocation for line where defination is %eax or %edx.
         Therefore, the number of register we allocate is up to # elements in maximum clique + 1.
 *)


let (<?>) c (cmp, x, y) = 
  if c = 0
  then cmp x y
  else c;;

let reg_str_cmp (t1 : string) (t2 : string) = 
  String.compare (String.sub t1 ~pos:1 ~len:1) (String.sub t2 ~pos:1 ~len:1)
  <?> (Int.compare, (String.length t1), (String.length t2))
  <?> (String.compare, t1, t2)
;;

let reg_cmp_pretty (t1 : string) (t2 : string) = 
  Int.compare (String.length t1) (String.length t2)
  <?> (String.compare, t1, t2)
;;

let is_tmp par = 
  String.compare (String.sub par ~pos:1 ~len:1) "t" = 0
;;

let is_reg par = 
  (String.compare (String.sub par ~pos:1 ~len:1) "r" = 0)
  || (String.compare (String.sub par ~pos:1 ~len:1) "e" = 0)
;;

let print_adj adj = 
  printf "\nprint adj\n";
  let keys = Hashtbl.keys adj in
  let sorted_keys = List.sort keys ~compare:reg_cmp_pretty in
  let () = List.iter sorted_keys 
      ~f:(fun key -> 
          let s = Hashtbl.find_exn adj key in
          let l = List.sort (Set.to_list s) ~compare:reg_cmp_pretty in
          printf "From %s to\t" key;
          List.iter l ~f:(fun x -> printf "%s " x);
          printf "\n";
        ) in
  printf "\n\n";
;;

(* Build edge between def and live_out *)
let build_def_lo adj u vs =
  let s_u = match Hashtbl.find adj u with
    | None -> Set.empty (module String)
    | Some s -> s in
  Set.iter vs ~f:(fun v -> 
      let s_v = match Hashtbl.find adj v with
        | None -> Set.empty (module String)
        | Some s -> s in
      Hashtbl.set adj ~key:u ~data:(Set.union s_u (Set.of_list (module String) [v]));
      Hashtbl.set adj ~key:v ~data:(Set.union s_v (Set.of_list (module String) [u]))
    )
;;

(* Build interference graph
   1. Build clique based on live_out 
   2. Build based on def and live_out. 
        The insight here is we cannot allocate/assign register for def with the same register as 
        registers allocated for live_out temps
*)
let rec _build_graph prog adj = match prog with 
  | [] -> adj
  | h :: t -> 
    let s1 = match Hashtbl.find adj h.define with 
      | Some s -> s
      | None -> Set.empty (module String) in
    let s2 = Set.of_list (module String) h.live_out in
    let s_u = Set.union s1 s2 in
    match h.define with
    | "" -> adj
    | _ -> 
      Hashtbl.set adj ~key: h.define ~data: s_u;
      build_def_lo adj h.define s2;
      _build_graph t adj
;;

(* Build double(mutually) linked adjacency list based on .in file.*)
let build_graph (prog : program) = 
  let adj = Hashtbl.create (module String) in
  _build_graph prog adj
;;

let gen_line_to_tmp prog = 
  let hash = Hashtbl.create (module Int) in
  let rec helper prog hash = match prog with
    | [] -> hash
    | h :: t -> 
      Hashtbl.set hash ~key:h.line_number ~data:h.define;
      helper t hash;
  in helper prog hash
;;

let gen_reg_table prog tmp_to_reg = 
  let hash_init = Hashtbl.create (module String) in
  let rec helper prog hash = match prog with
    | [] -> hash
    | h::t -> 
      match h.define with
      |"" -> helper t hash;
      | _ ->
        Hashtbl.set hash ~key:h.define ~data:0;
        helper t hash in 
  let hash_seo = helper prog hash_init in
  let () = Hashtbl.iter_keys tmp_to_reg 
      ~f:(fun tmp -> 
          if is_reg tmp
          then Hashtbl.set hash_seo ~key:tmp ~data:1
          else ()
        ) in
  hash_seo;
;;

let rec _seo adj reg_table seq = 
  match Hashtbl.is_empty reg_table with
  | true -> seq
  | false -> 
    let (u, _) = match Hashtbl.fold reg_table ~init:None 
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
    if is_reg u
    then 
      let () = Hashtbl.remove reg_table u in
      _seo adj reg_table seq_new;
    else
      let nbr = Hashtbl.find_exn adj u in
      let nbr = Set.remove nbr u in
      Set.iter nbr ~f:(fun x -> 
          match Hashtbl.find reg_table x with
          | None -> ()
          | Some v -> 
            let order = v + 1 in
            Hashtbl.set reg_table ~key:x ~data:order;
        );
      Hashtbl.remove reg_table u;
      _seo adj reg_table seq_new;
;;

(* We need to consider the influence of pre-coloring, which is stored in tmp_to_reg *)
let seo adj prog tmp_to_reg = 
  let seq = [] in
  let reg_table = gen_reg_table prog tmp_to_reg in
  _seo adj reg_table seq
;;

(* Check whether register reg is already assigned to some temporary in adj *)
let reg_is_assigned reg tmp_to_reg adj = 
  Set.fold ~init:false adj ~f:(fun acc tmp -> 
      match Hashtbl.find tmp_to_reg tmp with
      | None -> false || acc
      | Some reg' -> 
        if reg_str_cmp reg reg' = 0
        then  true || acc
        else  false || acc
    )
;;

let rec find_reg_w_min_ord_idx nbr_reg idx = 
  let cur_reg = "%r" ^ (string_of_int idx) in
  if Set.mem nbr_reg cur_reg
  then find_reg_w_min_ord_idx nbr_reg (idx + 1)
  else cur_reg
;;

let find_reg_w_min_ord nbr_reg = 
  if Set.mem nbr_reg "%eax"
  then
    if Set.mem nbr_reg "%edx"
    then find_reg_w_min_ord_idx nbr_reg 0
    else "%edx"
  else "%eax"
;;

let alloc_reg_by_nbr nbr tmp_to_reg = 
  (* printf "alloc_reg_by_nbr nbrs:\n"; *)
  let nbr_reg = Set.filter_map (module String) nbr ~f:(fun u -> Hashtbl.find tmp_to_reg u ) in
  find_reg_w_min_ord nbr_reg
;;

(* Allocate register for tmp. 
   reg_list is registers appeared in the input files, like "%eax", "%edx" etc.
   tmp is temporary to assign registers
   tmp_to_reg is a hashtable from temporary to registers.
   nbr is the neighbor of tmp
*)
let rec alloc reg_list tmp tmp_to_reg nbr = 
  match reg_list with
  | [] ->
    alloc_reg_by_nbr nbr tmp_to_reg
  | reg :: t -> 
    if reg_is_assigned reg tmp_to_reg nbr
    then alloc t tmp tmp_to_reg nbr
    else reg
;;

let rec _greedy seq adj reg_list tmp_to_reg  = match seq with
  | [] -> tmp_to_reg
  | h :: t -> 
    let nbr = Hashtbl.find_exn adj h in
    let reg = alloc reg_list h tmp_to_reg nbr in
    if is_tmp h
    then Hashtbl.set tmp_to_reg ~key:h ~data:reg
    else ();
    _greedy t adj reg_list tmp_to_reg 
;;

(* Infinite registers to allocate during greedy coloring. *)
let greedy seq adj tmp_to_reg = 
  let reg_list = ["%eax"; "%edx"] in
  _greedy seq adj reg_list tmp_to_reg
;;

let pre_fix prog = 
  let hash = Hashtbl.create (module String) in
  List.iter prog ~f:(fun line -> 
      match line.define with
      | "" -> ()
      | s -> 
        if is_tmp s
        then ()
        else Hashtbl.set hash ~key:line.define ~data:line.define;
    );
  hash;
;;

let rec gen_result color prog  = match prog with
  | [] -> []
  | h :: t ->
    let tmp = h.define in
    let reg = Hashtbl.find color tmp in
    let tk = match reg with
      | None -> None
      | Some reg' -> 
        if String.compare tmp reg' = 0
        then None
        else Some (tmp, reg') 
    in tk :: (gen_result color t)
;;

let print_tmp_to_reg color = 
  let () = printf "\n\n==========\nTemporary to register\n" in
  let sorted_keys = List.sort (Hashtbl.keys color) ~compare:reg_cmp_pretty in
  List.iter sorted_keys ~f:(fun k -> printf "%s -> %s\n" k (Hashtbl.find_exn color k));
  let l = List.map (Hashtbl.data color) ~f:(fun x -> x) in
  let s = Set.of_list (module String) l in
  printf "Used %d register\n" (Set.length s);
;;

let regalloc (prog : program) : allocations =
  let adj = build_graph prog in
  let tmp_to_reg = pre_fix prog in
  (* let tmp_to_reg = Hashtbl.create (module String) in *)
  let seq = seo adj prog tmp_to_reg in
  let color = greedy seq adj tmp_to_reg in
  (* let () = print_adj adj in
     let () = printf "SEO order\n" in
     let () = List.iter ~f:(printf "%s ") seq in
     let () = print_tmp_to_reg color in
     let () = printf "\n" in *)
  gen_result color prog;