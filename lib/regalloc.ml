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
  let s1 = String.sub t1 ~pos:2 ~len:((String.length t1) -2) in
  let s2 = String.sub t2 ~pos:2 ~len:((String.length t2) -2) in
  String.compare (String.sub t1 ~pos:1 ~len:1) (String.sub t2 ~pos:1 ~len:1)
  <?> (Int.compare, int_of_string s1, int_of_string s2)

let rec build_adj_hash (prog : program) hash = match prog with 
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
      build_adj_hash t hash;
;;

let print_adj adj = Hashtbl.iteri adj ~f:(fun ~key ~data -> 
    let l = List.sort (Set.to_list data) ~compare:reg_cmp in
    let () = printf "\nfrom %s to\t" key in 
    List.iter l ~f:(fun x -> printf "%s " x));
  printf "\n\n";
;;

let regalloc (_program : program) : allocations =
  let hash = Hashtbl.create (module String) in
  let adj = build_adj_hash _program hash in
  let () = print_adj adj in
  failwith "Implement regalloc here";;
