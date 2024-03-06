open Core

(*
 * This file contains necessary functions to allocate registers
 * based on input file described as type program in Lab1_checkpoint.
 *
 * We considered x86 conventions during register allocation. 
 * They are of register type in as vertex.
 * See https://www.cs.cmu.edu/~janh/courses/411/17/lec/03-regalloc.pdf Section 7 for details.
 * This is automatically done during Convention.X86.gen because it provide def use info.
 *
 * The basic allocation procedure follows:
 *   1) Build interference graph. We build edge between line.defines and line.live_out.
 *     Edges are also created between defines in the same instruction.
 *     For special instructions like mul, div, mod, shift, we follow the same scheme because
 *     special registers are already in defines during Convention.X86.gen.
 *     Time complexity: O(v + e)
 *   2) Use maximum cardinality search to build SEO
 *     Theoratically, We initialize every vertex with weight 0. Then, each time
 *     we start from a vertex u with maximum weight and update its neighbors weight by one.
 *     Then we record vertex u and delete from graph, and keep doing so until no vertex left on graph.
 *     Notice temporaries in interference graph is pure SSA.
 *     So we can apply maximum cardinality to find optimal register allocation policy.
 *     Time complexity for SEO: O(v + e)
 *   3) Greedy coloring based on SEO
 *     Greedy assign registers in SEO order. The rule is generate register with minimum index which
 *     is greater than its allocated neighbors.
 *     Time complexity for coloring: O(v + e)
 *)
module Temp = Var.Temp
module Size = Var.Size
module Register = Var.X86_reg.Logic
module Spill = Var.X86_reg.Spill
module Reg_info = Program
module Abs_asm = Abs_asm.Inst
module IG = Interference_graph
module VMap = IG.Vertex.Map
module VSet = IG.Vertex.Set

type t = IG.Vertex.t

type dest =
  | Reg of Register.t
  | Spill of Spill.t

let threshold = 2000
let eax = Register.RAX
let ecx = Register.RCX
let edx = Register.RDX

module Print = struct
  open Printf

  (* print adjacency list (interference graph) *)
  let print_adj adj =
    printf "\nprint adj\n";
    let keys = VMap.keys adj in
    let sorted_keys = List.sort keys ~compare:IG.Vertex.compare in
    let () =
      List.iter sorted_keys ~f:(fun key ->
          let s = VMap.find_exn adj key in
          let l = List.sort (VSet.to_list s) ~compare:IG.Vertex.compare in
          printf "From %s to\t" (IG.Print.pp_vertex key);
          List.iter l ~f:(fun x -> printf "%s " (IG.Print.pp_vertex x));
          printf "\n")
    in
    printf "\n\n"
  ;;

  let dest_str dest : string =
    match dest with
    | Reg r -> Register.pp r
    | Spill s -> Spill.pp s
  ;;

  let print_vertex_to_dest (color : dest VMap.t) =
    let () = printf "\n\n==========\nVertex to register\n" in
    let sorted_keys = List.sort (VMap.keys color) ~compare:IG.Vertex.compare in
    List.iter sorted_keys ~f:(fun k ->
        let t = IG.Print.pp_vertex k in
        let r = VMap.find_exn color k |> dest_str in
        printf "%s -> %s\n%!" t r)
  ;;

  let print_result (results : (t * dest) option list) : unit =
    printf "print result\n";
    List.iter results ~f:(fun tuple ->
        match tuple with
        | None -> ()
        | Some s ->
          let src, dest = s in
          let src_string, dest_string = IG.Print.pp_vertex src, dest_str dest in
          printf "%s -> %s\n%!" src_string dest_string);
    printf "result done\n%!"
  ;;
end

module Helper = struct
  let link (u : t) (v : t) (adj : VSet.t VMap.t) : VSet.t VMap.t =
    let u_nbr =
      match VMap.find adj u with
      | None -> VSet.empty
      | Some s -> s
    in
    let u_nbr' = VSet.add u_nbr v in
    let adj = VMap.set adj ~key:u ~data:u_nbr' in
    let v_nbr =
      match VMap.find adj v with
      | None -> VSet.empty
      | Some s -> s
    in
    let v_nbr' = VSet.add v_nbr u in
    VMap.set adj ~key:v ~data:v_nbr'
  ;;

  (* Build edge between vertices and vertex *)
  let connect adj vertex vertices =
    let s_vertex = VSet.of_list [ vertex ] in
    let s_vertex_nbr =
      match VMap.find adj vertex with
      | None -> VSet.empty
      | Some s -> s
    in
    let s_vertex_nbr_union = VSet.union s_vertex_nbr vertices in
    let adj = VMap.set adj ~key:vertex ~data:s_vertex_nbr_union in
    VSet.fold_right vertices ~init:adj ~f:(fun v adj ->
        let s_vertices =
          match VMap.find adj v with
          | None -> VSet.empty
          | Some s -> s
        in
        let s_res = VSet.union s_vertices s_vertex in
        VMap.set adj ~key:v ~data:s_res)
  ;;

  (* Build interference graph based on def and (live_out Union uses).
   * The insight here is we cannot allocate/assign register for def with the same register as
   * registers allocated for live_out temps.
   * Theoretically, we don't need to build edge between def and uses. But In order to 
   * make x86 assembly code generation easier, we don't allow uses and def to be assigned
   * to the same register. This can be more flexible for x86 assembly code generation.
   *)
  let build_graph reginfo_instr =
    let rec helper reginfo_instr adj =
      match reginfo_instr with
      | [] ->
        let vs = VMap.keys adj in
        let roots =
          List.fold vs ~init:VMap.empty ~f:(fun acc v -> VMap.set acc ~key:v ~data:v)
        in
        adj, roots
      | h :: t ->
        let reginfo, _ = h in
        (* Reg_info.print_line reginfo; *)
        let defs = Reg_info.get_defs reginfo in
        let adj =
          VSet.fold defs ~init:adj ~f:(fun adj_acc def ->
              (* build edges between defs *)
              let defs' = VSet.diff defs (VSet.of_list [ def ]) in
              let s_def_nbr =
                match VMap.find adj def with
                | Some s -> VSet.union s defs'
                | None -> defs'
              in
              let s_lo = reginfo.live_out in
              let s_u = VSet.union s_def_nbr s_lo in
              connect adj_acc def s_u)
        in
        helper t adj
    in
    helper reginfo_instr VMap.empty
  ;;

  (* Build coalesce graph. 
   * Connect def use when both requirements are meet.
   * 1) instruction move is true.
   * 2) edge (def, use) does not exist in interference graph. *)
  let build_coalesce reginfo_instr adj_ig =
    let rec _build_coalesce reginfo_instr adj =
      match reginfo_instr with
      | [] ->
        let edges =
          VMap.fold adj ~init:[] ~f:(fun ~key:u ~data:vs acc ->
              VSet.fold vs ~init:acc ~f:(fun acc v -> (u, v) :: acc))
        in
        adj, edges
      | h :: t ->
        let reginfo, _ = h in
        if Reg_info.get_move reginfo
        then (
          let defs = Reg_info.get_defs reginfo in
          let uses = Reg_info.get_uses reginfo in
          let adj =
            VSet.fold defs ~init:adj ~f:(fun adj_acc def ->
                let def_nbr = VMap.find_exn adj_ig def in
                VSet.fold uses ~init:adj_acc ~f:(fun adj_acc use ->
                    if VSet.mem def_nbr use then adj_acc else link def use adj_acc))
          in
          _build_coalesce t adj)
        else _build_coalesce t adj
    in
    let vs = VMap.keys adj_ig in
    let adj_init =
      List.fold vs ~init:VMap.empty ~f:(fun acc v -> VMap.set acc ~key:v ~data:VSet.empty)
    in
    _build_coalesce reginfo_instr adj_init
  ;;

  let rec dfs (node : t) (visited : bool VMap.t) (adj : VSet.t VMap.t) (roots : t VMap.t)
      : bool VMap.t * t VMap.t
    =
    let visited = VMap.set visited ~key:node ~data:true in
    let succs = VMap.find_exn adj node in
    let node_root = VMap.find_exn roots node in
    VSet.fold succs ~init:(visited, roots) ~f:(fun acc succ ->
        let visited_acc, roots_acc = acc in
        let has_visited = VMap.find_exn visited_acc succ in
        if has_visited
        then acc
        else (
          let roots_acc = VMap.set roots_acc ~key:succ ~data:node_root in
          dfs succ visited_acc adj roots_acc))
  ;;

  let get_nbr u adj =
    let u_nbr =
      match VMap.find adj u with
      | None -> VSet.empty
      | Some s -> s
    in
    VSet.remove u_nbr u
  ;;

  (* Given a interference graph, coalesce edges, eliminate redundant edges to make
   * each components is a fully connected(any two nodes in it does not interfere). 
   * This algorithm does not return the optimal maximum clique because it is NP-hard.
   * Here we only provide a greedy algorithm to find all cliques. *)
  let cliques (edges : (t * t) list) (ig_adj : VSet.t VMap.t) : VSet.t VMap.t =
    let cliques = VMap.mapi ig_adj ~f:(fun ~key:u ~data:_ -> VSet.of_list [ u ]) in
    List.fold edges ~init:cliques ~f:(fun cliques_acc edge ->
        let u, v = edge in
        let u_coa_nbr = get_nbr u cliques_acc in
        let u_ig_nbr = get_nbr v cliques_acc in
        let v_coa_nbr = get_nbr v cliques_acc in
        let v_ig_nbr = get_nbr v ig_adj in
        let intersect1 = VSet.inter u_coa_nbr v_ig_nbr in
        let intersect2 = VSet.inter v_coa_nbr u_ig_nbr in
        if VSet.is_empty intersect1
           && VSet.is_empty intersect2
           && VSet.length (VSet.union u_ig_nbr v_ig_nbr) < 4
        then (
          let acc1 = connect cliques_acc v (VSet.add u_coa_nbr u) in
          let v_coa_nbr = get_nbr v acc1 in
          connect acc1 u (VSet.add v_coa_nbr v))
        else cliques_acc)
  ;;

  (* Given coalesce graph, generate connected component graph.
   * Each node records its component root. So roots can compose a new graph *)
  let ccg (adj : VSet.t VMap.t) : t VMap.t =
    let roots = VMap.mapi adj ~f:(fun ~key:u ~data:_ -> u) in
    let visited = VMap.mapi adj ~f:(fun ~key:_ ~data:_ -> false) in
    let nodes = VMap.keys adj in
    let _, ccg =
      List.fold nodes ~init:(visited, roots) ~f:(fun acc node ->
          let visited_acc, roots_acc = acc in
          let has_visited = VMap.find_exn visited_acc node in
          if has_visited then acc else dfs node visited_acc adj roots_acc)
    in
    ccg
  ;;

  (* Build graph using coalesce information. 
   * adj: original connected graph built on def-live out info
   * ccg: records node -> its root.
   * return: adj graph after treating all connected components 
   *         in coalesce graph as a single node.*)
  let build_graph' reginfo_instr =
    let ig_adj, _ = build_graph reginfo_instr in
    let _, coa_edges = build_coalesce reginfo_instr ig_adj in
    let cliques = cliques coa_edges ig_adj in
    (* Print.print_adj cliques; *)
    let roots = ccg cliques in
    let graph_init =
      VMap.data roots
      |> VSet.of_list
      |> VSet.to_list
      |> List.fold ~init:VMap.empty ~f:(fun graph_acc root ->
             VMap.set graph_acc ~key:root ~data:VSet.empty)
    in
    (* List.iter (VMap.data ccg) ~f:(fun n -> printf "%s\n" (IG.Print.pp_vertex n)); *)
    let adj_ccg =
      VMap.fold ig_adj ~init:graph_init ~f:(fun ~key:u ~data:vs graph_acc ->
          let u' = VMap.find_exn roots u in
          let vs' = VSet.map vs ~f:(fun v -> VMap.find_exn roots v) in
          connect graph_acc u' vs')
    in
    adj_ccg, roots
  ;;
end

module Lazy = struct
  type reg = Register.t

  let threshold = 2000
  let eax = Register.RAX
  let ecx = Register.RCX
  let edx = Register.RDX

  let rec collect_vertex (lines : Abs_asm.line list) res =
    match lines with
    | [] -> res
    | line :: t ->
      let res =
        List.fold (line.defines @ line.uses) ~init:res ~f:(fun acc u ->
            VSet.union acc (IG.Vertex.of_abs u))
      in
      collect_vertex t res
  ;;

  let gen_result_dummy vertex_set =
    let cnt = ref 16 in
    let cache = ref Int.Map.empty in
    let vertex_list = VSet.to_list vertex_set in
    List.map vertex_list ~f:(fun vtx ->
        let dest =
          match vtx with
          | IG.Vertex.Reg r -> Reg r
          | IG.Vertex.Temp t ->
            if Int.Map.mem !cache t.id
            then (
              let id = Int.Map.find_exn !cache t.id in
              Spill (Spill.of_int id))
            else (
              let id = !cnt in
              cache := Int.Map.set !cache ~key:t.id ~data:!cnt;
              cnt := !cnt + 1;
              Spill (Spill.of_int id))
        in
        match dest with
        | Spill _ -> Some (vtx, dest)
        | Reg _ -> None)
  ;;
end

let rec _seo_rev adj vertex_table seq =
  match VMap.is_empty vertex_table with
  | true -> seq
  | false ->
    let u, _ =
      match
        VMap.fold vertex_table ~init:None ~f:(fun ~key ~data accu ->
            match accu with
            | None -> Some (key, data)
            | Some (_, data') -> if data' > data then accu else Some (key, data))
      with
      | None -> failwith "empty vertex_table"
      | Some s -> s
    in
    let seq_new = u :: seq in
    let nbr = VMap.find_exn adj u in
    let nbr = VSet.remove nbr u in
    let vertex_table =
      VSet.fold_right nbr ~init:vertex_table ~f:(fun x acc ->
          match VMap.find vertex_table x with
          | None -> acc
          | Some v ->
            let order = v + 1 in
            VMap.set vertex_table ~key:x ~data:order)
    in
    let vertex_table = VMap.remove vertex_table u in
    _seo_rev adj vertex_table seq_new
;;

let seo adj =
  let vertex_table = VMap.map adj ~f:(fun _ -> 0) in
  let seo_rev = _seo_rev adj vertex_table [] in
  List.rev seo_rev
;;

(* find minimum available register with neighbor nbr *)
let find_min_available (nbr : Int.Set.t) (black_set : Int.Set.t) : int =
  let rec helper (idx : int) =
    if Register.special_use' idx || Set.mem black_set idx
    then helper (idx + 1)
    else if Set.mem nbr idx
    then helper (idx + 1)
    else idx
  in
  helper 0
;;

(* Allocate register for vertex. Neighbors may be of register or 
 * temporary. If neighbor is register, put this register to blacklist
 * so we will not assign this register to the current vertex.
 * vertex_to_dest is a hashtable from vertex to registers.
 * nbr is the neighbor of vertex
 * 
 * In a word, the chosen register whould satisfy below requirement
 * 1) Not the same as hard registers of its neighbor. For example,
 * if t is connected to rax, it will not be assigned as rax.
 * 2) Minimum available registers among its temporary neighbors.
 *)
let alloc (nbr : VSet.t) (vertex_to_dest : dest VMap.t) : dest =
  (* If a temporary is connected to a register, 
   * we cannot assign this register to it. *)
  let nbr_black_list =
    VSet.fold nbr ~init:[] ~f:(fun acc u ->
        match u with
        | IG.Vertex.Reg r -> Register.get_idx r :: acc
        | IG.Vertex.Temp _ -> acc)
  in
  (* Keep track of assigned registers for neighbor temporaries *)
  let nbr_int_l =
    VSet.fold nbr ~init:[] ~f:(fun acc u ->
        match VMap.find vertex_to_dest u with
        | None -> acc
        | Some u' ->
          (match u' with
          | Reg r -> Register.get_idx r :: acc
          | Spill m -> Spill.get_idx16 m :: acc))
  in
  let nbr_int_s = Int.Set.of_list nbr_int_l in
  let black_set = Int.Set.of_list nbr_black_list in
  let r = find_min_available nbr_int_s black_set in
  if r < Register.num_reg then Reg (Register.idx_reg r) else Spill (Spill.of_int r)
;;

(* Infinite registers to allocate during greedy coloring. *)
let rec greedy seq adj vertex_to_dest =
  match seq with
  | [] -> vertex_to_dest
  | h :: t ->
    (match h with
    | IG.Vertex.Reg reg ->
      let vertex_to_dest =
        VMap.set vertex_to_dest ~key:(IG.Vertex.Reg reg) ~data:(Reg reg)
      in
      greedy t adj vertex_to_dest
    | IG.Vertex.Temp temp ->
      let nbr = VMap.find_exn adj h in
      let dest = alloc nbr vertex_to_dest in
      (* let () =
        match dest with
        | Reg r ->
          printf "alloc %s for %s\n" (Var.X86_reg.Logic.ppr) (Temp.name temp)
        | Spill s -> printf "alloc %s for %s\n" (Spill.pp s) (Temp.name temp)
      in *)
      let vertex_to_dest =
        VMap.set vertex_to_dest ~key:(IG.Vertex.Temp temp) ~data:dest
      in
      greedy t adj vertex_to_dest)
;;

let gen_result (roots : t VMap.t) color : (t * dest) option list =
  let vs = VMap.keys roots in
  List.map vs ~f:(fun v ->
      match v with
      | IG.Vertex.Temp _ ->
        let v_root = VMap.find_exn roots v in
        let dest = VMap.find color v_root in
        (match dest with
        | None -> None
        | Some dest' -> Some (v, dest'))
      | IG.Vertex.Reg _ -> None)
;;

let regalloc (fdefn : Abs_asm.fdefn) : (t * dest) option list =
  let lines = List.map fdefn.body ~f:(fun instr -> instr.line) in
  let vertex_set = Lazy.collect_vertex lines VSet.empty in
  if VSet.length vertex_set > threshold
  then Lazy.gen_result_dummy vertex_set
  else (
    let reginfo_instrs = Program.gen_regalloc_info fdefn.body in
    (* let adj, roots = Helper.build_graph reginfo_instrs in *)
    let adj, roots = Helper.build_graph' reginfo_instrs in
    let seq = seo adj in
    let color = greedy seq adj VMap.empty in
    (* Print.print_adj adj;
    printf "SEO order\n";
    let seq_l = List.map seq ~f:(fun x -> IG.Print.pp_vertex x) in
    List.iter ~f:(printf "%s ") seq_l;
    Print.print_vertex_to_dest color;
    printf "\n%!";
    VMap.iteri roots ~f:(fun ~key:u ~data:root ->
        printf "root %s -> %s\n" (IG.Print.pp_vertex root) (IG.Print.pp_vertex u)); *)
    let results = gen_result roots color in
    (* Print.print_result results; *)
    results)
;;
