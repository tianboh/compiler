open Core
open Lab1_checkpoint
open Printf
open Assem

let (<?>) c (cmp, x, y) = 
  if c = 0
  then cmp x y
  else c;;

let reg_str_cmp (t1 : string) (t2 : string) = 
  Int.compare (String.length t1) (String.length t2)
  <?> (String.compare, t1, t2)
;;

(* let reg_cmp (t1 : Assem.reg) (t2 : Assem.reg) = 
   let t1_str = reg_to_str t1 in
   let t2_str = reg_to_str t2 in
   reg_str_cmp t1_str t2_str
   ;; *)

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

let build_clique adj live_out = 
  Set.iter live_out ~f:(fun u -> 
      Set.iter live_out ~f:(fun v -> 
          if String.compare u v <> 0 then
            let s1 = match Hashtbl.find adj u with
              | None -> Set.empty (module String)
              | Some s -> s in
            let s2 = Set.of_list (module String) [v] in
            let s = Set.union s1 s2 in
            Hashtbl.set adj ~key:u ~data:s;
          else
            ()
        ));
;;

(* Build double(mutually) linked adjacency list based on .in file.*)
let build_mut_adj_hash (prog : program) = 
  let adj = Hashtbl.create (module String) in
  let rec helper prog adj = match prog with 
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
        build_clique adj s2;
        helper t adj;
  in helper prog adj
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
  printf "\nprint adj\n";
  let keys = Hashtbl.keys adj in
  let sorted_keys = List.sort keys ~compare:reg_str_cmp in
  let () = List.iter sorted_keys 
      ~f:(fun key -> 
          let s = Hashtbl.find_exn adj key in
          let l = List.sort (Set.to_list s) ~compare:reg_str_cmp in
          printf "From %s to\t" key;
          List.iter l ~f:(fun x -> printf "%s " x);
          printf "\n";
        ) in
  printf "\n\n";
;;

let rec _seo adj reg_table seq = 
  (* let () = printf "\nhelper seq\n" in
     let () = List.iter ~f:(printf "%s ") seq in 
     let () = printf "\ncurrent graph order\n" in *)
  (* let () = Hashtbl.iteri reg_table ~f:(fun ~key ~data -> printf "%s %d\n" key data) in *)
  match Hashtbl.is_empty reg_table with
  | true -> seq
  | false -> 
    let (u, _) = match Hashtbl.fold reg_table ~init:None 
                         ~f:(fun ~key ~data accu -> 
                             (* let () = printf "  iterate reg_table %s %d\n" key data in *)
                             match accu with
                             | None -> 
                               (* let () = printf "  accu initialize with %s %d\n" key data in *)
                               Some (key, data)
                             | Some (_, data') -> 
                               (* let () = printf "  current accu %s %d\n" key' data' in *)
                               if data' < data 
                               then 
                                 (* let () = printf "  accu not change\n" in *)
                                 accu
                               else 
                                 (* let () = printf "  find smaller value with %s %d\n" key data in *)
                                 Some (key, data)
                           ) with
    | None -> failwith "empty reg_table"
    | Some s -> s in 
    let seq_new = seq@[u] in
    let nbr = Hashtbl.find_exn adj u in
    let nbr = Set.remove nbr u in
    (* printf "find node %s with order %d\n" u ord_; *)
    Set.iter nbr ~f:(fun x -> 
        match Hashtbl.find reg_table x with
        | None -> ()
        | Some v -> 
          let order = v + 1 in
          Hashtbl.set reg_table ~key:x ~data:order;
          printf "---> %s update node %s's order to %d\n" u x order);
    Hashtbl.remove reg_table u;
    _seo adj reg_table seq_new;
;;

let seo adj prog = 
  let seq = [] in
  let reg_table = gen_reg_table prog in
  _seo adj reg_table seq
;;

(* Check whether register reg is already assigned to some temporary in adj *)
let reg_is_assigned reg tmp_to_reg adj = 
  let () = printf "check whether reg %s is assigned\n" (reg_to_str reg) in
  Set.fold ~init:false adj ~f:(fun acc tmp -> 
      match Hashtbl.find tmp_to_reg tmp with
      | None -> false || acc
      | Some reg' -> 
        if reg_str_cmp (reg_to_str reg) (reg_to_str reg') = 0
        then 
          let () = printf "register %s is already allocated\n" (reg_to_str reg) in
          true || acc;
        else 
          let () = printf "register %s is not allocated\n" (reg_to_str reg) in
          false || acc;
    )
;;

let rec _alloc reg_list tmp tmp_to_reg adj = 
  let () = printf "_alloc for tmp %s\n" tmp in
  match reg_list with
  | [] -> failwith "No available register."
  | h :: t -> 
    if reg_is_assigned h tmp_to_reg adj
    then
      _alloc t tmp tmp_to_reg adj
    else
      h
;;

(* Allocate register for tmp. *)
let alloc reg_list tmp tmp_to_reg adj = 
  let () = printf "\nallocate register for tmp %s\n" tmp in
  _alloc reg_list tmp tmp_to_reg adj;
;;

let rec _greedy (seq : string list) adj reg_list tmp_to_reg = match seq with
  | [] -> tmp_to_reg
  | h :: t -> 
    let nbr = Hashtbl.find_exn adj h in
    let reg = alloc reg_list h tmp_to_reg nbr in
    let () = Hashtbl.set tmp_to_reg ~key:h ~data:reg in
    let () = printf "assign reg %s to tmp %s\n" (reg_to_str reg) h in
    _greedy t adj reg_list tmp_to_reg
;;

let greedy seq adj tmp_to_reg = 
  let () = printf "greedy coloring\n" in 
  (* let seq_for_greedy = List.rev seq in
     let () = List.iter  ~f:(printf "%s ") seq_for_greedy in
     let () = printf "\n" in *)
  let reg_list = [EAX; EBX; ECX; EDX; ESI; EDI; EBP; ESP; E8D; E9D; E10D; E11D; E12D; E13D; E14D; E15D] in
  _greedy seq adj reg_list tmp_to_reg
;;

let pre_color prog = 
  let hash = Hashtbl.create (module String) in
  List.iter prog ~f:(fun line -> 
      match line.define with
      | "" -> ()
      | s -> 
        if String.compare (String.sub s ~pos:1 ~len:1) "t" = 0
        then ()
        else
          Hashtbl.set hash ~key:line.define ~data:(str_to_reg line.define);
    );
  hash;
;;

let print_tmp_to_reg color = 
  let () = printf "\n\n==========\nTemporary to register\n" in
  Hashtbl.iteri color ~f:(fun ~key ~data -> printf "%s -> %s\n" key (reg_to_str data));
  let l = List.map (Hashtbl.data color) ~f:(fun x -> reg_to_str x) in
  (* let s = Set.empty (module String)in
     let () = List.iter l ~f:(fun x -> Set.add s x) in *)
  let s = Set.of_list (module String) l in
  printf "Used %d register\n" (Set.length s);
;;

let regalloc (prog : program) : allocations =
  let adj = build_mut_adj_hash prog in
  let tmp_to_reg = pre_color prog in
  let seq = seo adj prog in
  let color = greedy seq adj tmp_to_reg in
  let () = print_adj adj in
  let () = printf "SEO order\n" in
  let () = List.iter ~f:(printf "%s ") seq in
  let () = print_tmp_to_reg color in
  let () = printf "\n" in
  (* let line_to_tmp = gen_line_to_tmp prog in *)
  failwith "Implement regalloc here";;
