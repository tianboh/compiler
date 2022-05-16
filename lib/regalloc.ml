open Core
open Lab1_checkpoint
open Printf

let (<?>) c (cmp, x, y) = 
  if c = 0
  then cmp x y
  else c;;

let reg_cmp (t1 : string) (t2 : string) = 
  Int.compare (String.length t1) (String.length t2)
  <?> (String.compare, t1, t2)

(* Build single linked adjacency list based on original .in file. *)
let build_ori_adj_hash (prog : program) =
  let hash = Hashtbl.create (module String) in 
  let rec helper prog hash = match prog with 
    | [] -> hash
    | h :: t -> 
      let s1 = match Hashtbl.find hash h.define with 
        | Some s -> s
        | None -> Set.empty (module String) in
      let s2 = Set.of_list (module String) h.live_out in
      let s_u = Set.union s1 s2 in
      match h.define with
      | "" -> hash
      | _ -> 
        Hashtbl.set hash ~key: h.define ~data: s_u;
        helper t hash;
  in helper prog hash
;;

(* Build double(mutually) linked adjacency list based on .in file.*)
let build_mut_adj_hash (prog : program) = 
  let hash = Hashtbl.create (module String) in
  let rec helper prog hash = match prog with 
    | [] -> hash
    | h :: t -> 
      let s1 = match Hashtbl.find hash h.define with 
        | Some s -> s
        | None -> Set.empty (module String) in
      let s2 = Set.of_list (module String) h.live_out in
      let s_u = Set.union s1 s2 in
      match h.define with
      | "" -> hash
      | _ -> 
        Hashtbl.set hash ~key: h.define ~data: s_u;
        Set.iter s2 ~f:(fun key -> 
            match key with
            | "" -> () (* Avoid empty key match to a list of nodes. *)
            | _ -> 
              let s_h = Set.of_list (module String) [h.define] in
              let s_old =  
                match Hashtbl.find hash key with
                |None -> Set.empty (module String)
                |Some s-> s in
              let s_new = Set.union s_old s_h in
              Hashtbl.set hash ~key: key ~data: s_new);
        helper t hash;
  in helper prog hash
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

let gen_reg_table (prog : program) = 
  let hash = Hashtbl.create (module String) in
  let rec helper prog hash = match prog with
    | [] -> hash
    | h::t -> 
      match h.define with
      |"" -> helper t hash;
      | _ ->
        Hashtbl.set hash ~key:h.define ~data:0;
        helper t hash;
  in helper prog hash
;;

let print_adj adj = 
  let keys = Hashtbl.keys adj in
  let sorted_keys = List.sort keys ~compare:reg_cmp in
  let () = List.iter sorted_keys 
      ~f:(fun key -> 
          let s = Hashtbl.find_exn adj key in
          let l = List.sort (Set.to_list s) ~compare:reg_cmp in
          printf "\nFrom %s to\t" key;
          List.iter l ~f:(fun x -> printf "%s " x)
        ) in
  printf "\n\n";
;;

let seo adj reg_table = 
  let seq = [] in
  let rec helper adj reg_table seq = 
    let () = printf "\nhelper seq\n" in
    let () = List.iter ~f:(printf "%s ") seq in 
    let () = printf "\ncurrent graph order\n" in
    let () = Hashtbl.iteri reg_table ~f:(fun ~key ~data -> printf "%s %d\n" key data) in
    match Hashtbl.is_empty reg_table with
    | true -> seq
    | false -> 
      let (u, ord_) = match Hashtbl.fold reg_table ~init:None 
                              ~f:(fun ~key ~data accu -> 
                                  let () = printf "  iterate reg_table %s %d\n" key data in
                                  match accu with
                                  | None -> 
                                    let () = printf "  accu initialize with %s %d\n" key data in
                                    Some (key, data)
                                  | Some (key', data') -> 
                                    let () = printf "  current accu %s %d\n" key' data' in
                                    if data' < data 
                                    then 
                                      let () = printf "  accu not change\n" in
                                      accu
                                    else 
                                      let () = printf "  find smaller value with %s %d\n" key data in
                                      Some (key, data)
                                ) with
      | None -> failwith "empty reg_table"
      | Some s -> s in 
      let seq_new = seq@[u] in
      let nbr = Hashtbl.find_exn adj u in
      let nbr = Set.remove nbr u in
      printf "find node %s with order %d\n" u ord_;
      Set.iter nbr ~f:(fun x -> 
          match Hashtbl.find reg_table x with
          | None -> ()
          | Some v -> 
            let order = v + 1 in
            Hashtbl.set reg_table ~key:x ~data:order;
            printf "---> %s update node %s's order to %d\n" u x order);
      Hashtbl.remove reg_table u;
      helper adj reg_table seq_new;
  in helper adj reg_table seq
;;

let regalloc (prog : program) : allocations =
  let adj = build_mut_adj_hash prog in
  let () = print_adj adj in
  let reg_table = gen_reg_table prog in
  let seq = seo adj reg_table in
  let () = List.iter ~f:(printf "%s ") seq in
  let () = printf "\n" in
  (* let line_to_tmp = gen_line_to_tmp prog in *)
  failwith "Implement regalloc here";;
