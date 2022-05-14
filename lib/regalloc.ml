open Core
open Lab1_checkpoint
open Printf

type node = 
  { reg : reg
  ; mutable order : int (* order for SEO *)
  ; mutable is_alloc : bool (* whether is allocated during SEO*)
  }

type interference_graph = (node * node list) list;;

let (<?>) c (cmp, x, y) = 
  if c = 0
  then cmp x y
  else c;;

let reg_cmp (t1 : string) (t2 : string) = 
  Int.compare (String.length t1) (String.length t2)
  <?> (String.compare, t1, t2)

(* Build single linked adjacency list based on original .in file. *)
let rec build_ori_adj_hash (prog : program) hash = match prog with 
  | [] -> hash
  | h :: t -> 
    let s1 = match Hashtbl.find hash h.define with 
      | Some s -> s
      | None -> Set.empty (module String) in
    let s2 = Set.of_list (module String) h.live_out in
    let s_u = Set.union s1 s2 in
    match h.define with
    |"" -> hash
    |_ -> Hashtbl.set hash ~key: h.define ~data: s_u;
      build_ori_adj_hash t hash;
;;

(* Build double(mutually) linked adjacency list based on .in file.*)
let rec build_mut_adj_hash (prog : program) hash = match prog with 
  | [] -> hash
  | h :: t -> 
    let s1 = match Hashtbl.find hash h.define with 
      | Some s -> s
      | None -> Set.empty (module String) in
    let s2 = Set.of_list (module String) h.live_out in
    let s_u = Set.union s1 s2 in
    match h.define with
    |"" -> hash
    |_ -> 
      Hashtbl.set hash ~key: h.define ~data: s_u;
      Set.iter s2 ~f:(fun key -> 
          let s_h = Set.of_list (module String) [h.define] in
          let s_old =  
            match Hashtbl.find hash key with
            |None -> Set.empty (module String)
            |Some s-> s in
          let s_new = Set.union s_old s_h in
          Hashtbl.set hash ~key: key ~data: s_new);
      build_mut_adj_hash t hash;
;;

let print_adj adj = 
  let keys = Hashtbl.keys adj in
  let sorted_keys = List.sort keys ~compare:reg_cmp in
  let () = List.iter sorted_keys 
      ~f:(fun key -> 
          let s = Hashtbl.find adj key in
          let s_ = match s with
            |None -> failwith "empty adjacency list"
            |Some s -> s in
          let l = List.sort (Set.to_list s_) ~compare:reg_cmp in
          printf "\nFrom %s to\t" key;
          List.iter l ~f:(fun x -> printf "%s " x)
        ) in
  printf "\n\n";
;;

let regalloc (_program : program) : allocations =
  let hash = Hashtbl.create (module String) in
  let adj = build_mut_adj_hash _program hash in
  let () = print_adj adj in
  failwith "Implement regalloc here";;
