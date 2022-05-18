open Core
open Lab1_checkpoint
open Printf
(* open Assem *)

let (<?>) c (cmp, x, y) = 
  if c = 0
  then cmp x y
  else c;;

let reg_str_cmp (t1 : string) (t2 : string) = 
  Int.compare (String.length t1) (String.length t2)
  <?> (String.compare, t1, t2)
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
          else ()
        ));
;;

(* Build edge between def and live_out *)
let build_def_lo adj u vs =
  Set.iter vs ~f:(fun v -> 
      let s_u = match Hashtbl.find adj u with
        | None -> Set.empty (module String)
        | Some s -> s in
      let s_v = match Hashtbl.find adj v with
        | None -> Set.empty (module String)
        | Some s -> s in
      Hashtbl.set adj ~key:u ~data:(Set.union s_u (Set.of_list (module String) [v]));
      Hashtbl.set adj ~key:v ~data:(Set.union s_v (Set.of_list (module String) [u])))
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
      build_clique adj s2;
      if Set.mem s2 h.define
      then ()
      else build_def_lo adj h.define s2;
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
                               then accu
                               else Some (key, data)
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
          (* printf "---> %s update node %s's order to %d\n" u x order *)
      );
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
  (* let () = printf "check whether reg %s is assigned\n" (reg_to_str reg) in *)
  Set.fold ~init:false adj ~f:(fun acc tmp -> 
      match Hashtbl.find tmp_to_reg tmp with
      | None -> false || acc
      | Some reg' -> 
        if reg_str_cmp reg reg' = 0
        then 
          (* let () = printf "register %s is already allocated\n" (reg_to_str reg) in *)
          true || acc
        else 
          (* let () = printf "register %s is not allocated\n" (reg_to_str reg) in *)
          false || acc
    )
;;

(* Allocate register for tmp. *)
let rec alloc reg_list tmp tmp_to_reg adj = 
  (* let () = printf "_alloc for tmp %s\n" tmp in *)
  match reg_list with
  | [] -> failwith "No available register."
  | h :: t -> 
    if reg_is_assigned h tmp_to_reg adj
    then alloc t tmp tmp_to_reg adj
    else h
;;

let is_tmp par = 
  String.compare (String.sub par ~pos:1 ~len:1) "t" = 0
;;

let is_reg par = 
  String.compare (String.sub par ~pos:1 ~len:1) "r" = 0
;;

let rec _greedy seq adj reg_list tmp_to_reg  = match seq with
  | [] -> tmp_to_reg
  | h :: t -> 
    let nbr = Hashtbl.find_exn adj h in
    let reg = alloc reg_list h tmp_to_reg nbr in
    if is_tmp h
    then Hashtbl.set tmp_to_reg ~key:h ~data:reg
    else ();
    (* let () = printf "assign reg %s to tmp %s\n" (reg_to_str reg) h in *)
    _greedy t adj reg_list tmp_to_reg 
;;

(* Infinite registers to allocate during greedy coloring. *)
let greedy seq adj tmp_to_reg = 
  let () = printf "\n" in
  let keys = Hashtbl.keys adj in
  let reg_list = List.filter keys ~f:(fun x -> is_reg x) in
  let reg_list = reg_list @ ["%e1d";"%e2d";"%e3d";"%e4d";"%e5d";"%e6d";"%e7d";"%e8d";"%e9d"; "%e10d"; "%e11d"; "%e12d"; "%e13d"; "%e14d"; "%e15d"] in
  _greedy seq adj reg_list tmp_to_reg
;;

let pre_color prog = 
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
  Hashtbl.iteri color ~f:(fun ~key ~data -> printf "%s -> %s\n" key  data);
  let l = List.map (Hashtbl.data color) ~f:(fun x -> x) in
  let s = Set.of_list (module String) l in
  printf "Used %d register\n" (Set.length s);
;;

let regalloc (prog : program) : allocations =
  let adj = build_graph prog in
  let tmp_to_reg = pre_color prog in
  let seq = seo adj prog in
  let color = greedy seq adj tmp_to_reg in
  (* let () = print_adj adj in *)
  (* let () = printf "SEO order\n" in *)
  (* let () = List.iter ~f:(printf "%s ") seq in *)
  (* let () = print_tmp_to_reg color in *)
  (* let () = printf "\n" in *)
  gen_result color prog;
  (* failwith "Implement regalloc here";; *)
