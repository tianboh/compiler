open Core
open Json_reader.Lab1_checkpoint
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

let (<?>) c (cmp, x, y) = 
  if c = 0
  then cmp x y
  else c;;

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

(* print adjacency list (interference graph) *)
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
   For lines whose define field is %eax or %edx, we build a isolated node for them and do not
   build edge from them to any temporaries.
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
      if is_tmp h.define
      then
        let () = Hashtbl.set adj ~key: h.define ~data: s_u in
        build_def_lo adj h.define s2
      else 
        Hashtbl.set adj ~key:h.define ~data: (Set.of_list (module String)[h.define]);
      _build_graph t adj
;;

(* Build double(mutually) linked adjacency list based on .in file.*)
let build_graph (prog : program) = 
  let adj = Hashtbl.create (module String) in
  _build_graph prog adj
;;

let gen_reg_table prog = 
  let hash_init = Hashtbl.create (module String) in
  let rec helper prog hash = match prog with
    | [] -> hash
    | h::t -> 
      match h.define with
      |"" -> helper t hash;
      | _ ->
        Hashtbl.set hash ~key:h.define ~data:0;
        helper t hash in 
  helper prog hash_init
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
let seo adj prog = 
  let seq = [] in
  let reg_table = gen_reg_table prog in
  _seo adj reg_table seq
;;

(* Find register name with minimum free order that is greater than any register in its neighbor. 
   If nbr[u] is [1,5,0,2], then find_reg will return 3.
*)
let rec find_reg nbr_reg idx = 
  let cur_reg = "%r" ^ (string_of_int idx) in
  if Set.mem nbr_reg cur_reg
  then find_reg nbr_reg (idx + 1)
  else cur_reg
;;

(* Allocate register for tmp. 
   tmp_to_reg is a hashtable from temporary to registers.
   nbr is the neighbor of tmp
*)
let alloc nbr tmp_to_reg = 
  let nbr_reg = Set.filter_map (module String) nbr ~f:(fun u -> Hashtbl.find tmp_to_reg u ) in
  find_reg nbr_reg 0
;;

(* Infinite registers to allocate during greedy coloring. *)
let rec greedy seq adj tmp_to_reg  = match seq with
  | [] -> tmp_to_reg
  | h :: t -> 
    let nbr = Hashtbl.find_exn adj h in
    let reg = alloc nbr tmp_to_reg in
    if is_tmp h
    then Hashtbl.set tmp_to_reg ~key:h ~data:reg
    else Hashtbl.set tmp_to_reg ~key:h ~data:h;
    greedy t adj tmp_to_reg 
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
  let tmp_to_reg = Hashtbl.create (module String) in
  let seq = seo adj prog in
  let color = greedy seq adj tmp_to_reg in
  (* let () = print_adj adj in
     let () = printf "SEO order\n" in
     let () = List.iter ~f:(printf "%s ") seq in
     let () = print_tmp_to_reg color in
     let () = printf "\n" in *)
  gen_result color prog;