open Core
open Printf

(*
 * This file contains necessary functions to allocate registers
 * based on input file described as type program in Lab1_checkpoint.
 *
 * I used Hash table from vertex, which can be temporary of register,
 * to register Set as adjacency list to denote interference graph.
 *
 * We considered x86 conventions during register allocation. 
 * They are of register type in as vertex.
 * See https://www.cs.cmu.edu/~janh/courses/411/17/lec/03-regalloc.pdf Section 7 for details.
 *
 * The basic allocation procedure follows:
 *   1) Build interference graph. We build edge from line.define to line.live_out.
 *     We do not build clique based on live_out because this may ignore dependency
 *     between define and live_out. For example, if the defined temporary is not used
 *     in the future, so it may not in live_out set, then scheduler may allocate a register
 *     which is already allocated for the live_out for the current register
 *     (because there is no edge between define and live_out).
 *     PS:If we can eliminate redundant defination in SSA, which means every defination
 *     will be in the live_out set, then we can build clique purely based on live_out set.
 *     Time complexity: O(v + e)
 *   2) Use maximum cardinality search to build SEO
 *     Theoratically, We initialize every vertex with weight 0. Then, each time
 *     we start from a vertex u with maximum weight and update its neighbors weight by one.
 *     Then we record vertex u and delete from graph, and keep doing so until no vertex left on graph.
 *     Notice temporaries(not consider pre-colored register) in interference graph is pure SSA.
 *     So we can apply maximum cardinality to find optimal register allocation policy.
 *     Time complexity for SEO: O(v + e)
 *   3) Greedy coloring based on SEO
 *     Greedy assign registers in SEO order. The rule is generate register with minimum index which
 *     is greater than its allocated neighbors.
 *     Time complexity for coloring: O(v + e)
 *)
module Temp = Var.Temp
module Register = Var.X86_reg
module Reg_info = Program
module AS = Inst.Pseudo
module IG = Interference_graph

type reg = Register.t
type temp = Temp.t

let threshold = 3000

(* print adjacency list (interference graph) *)
let print_adj adj =
  printf "\nprint adj\n";
  let keys = IG.Vertex.Map.keys adj in
  let sorted_keys = List.sort keys ~compare:IG.Vertex.compare in
  let () =
    List.iter sorted_keys ~f:(fun key ->
        let s = IG.Vertex.Map.find_exn adj key in
        let l = List.sort (IG.Vertex.Set.to_list s) ~compare:IG.Vertex.compare in
        printf "From %s to\t" (IG.Print.pp_vertex key);
        List.iter l ~f:(fun x -> printf "%s " (IG.Print.pp_vertex x));
        printf "\n")
  in
  printf "\n\n"
;;

(* Build edge between def and live_out *)
let build_def_lo adj def s_lo =
  let s_def = IG.Vertex.Set.of_list [ def ] in
  IG.Vertex.Set.fold_right s_lo ~init:adj ~f:(fun v adj ->
      let s_v =
        match IG.Vertex.Map.find adj v with
        | None -> IG.Vertex.Set.empty
        | Some s -> s
      in
      let s_res = IG.Vertex.Set.union s_v s_def in
      IG.Vertex.Map.set adj ~key:v ~data:s_res)
;;

(* Build interference graph based on def and (live_out Union uses).
 * The insight here is we cannot allocate/assign register for def with the same register as
 * registers allocated for live_out temps.
 * Theoretically, we don't need to build edge between def and uses. But In order to 
 * make x86 assembly code generation easier, we don't allow uses and def to be assigned
 * to the same register. This can be more flexible for x86 assembly code generation.
 *)
let rec build_graph (prog : Reg_info.temps_info) adj =
  match prog with
  | [] -> adj
  | h :: t ->
    let adj =
      match Reg_info.get_def h with
      | None -> adj
      | Some def ->
        let s_def_nbr =
          match IG.Vertex.Map.find adj def with
          | Some s -> s
          | None -> IG.Vertex.Set.empty
        in
        let s_lo = h.live_out in
        let s_u = IG.Vertex.Set.union s_def_nbr s_lo in
        let adj = IG.Vertex.Map.set adj ~key:def ~data:s_u in
        build_def_lo adj def s_lo
    in
    build_graph t adj
;;

(* Table store info from vertex to number which will be used in seo. *)
let gen_vertex_table prog =
  let rec helper prog hash =
    match prog with
    | [] -> hash
    | h :: t ->
      (match Reg_info.get_def h with
      | None -> helper t hash
      | Some def_ ->
        let hash = IG.Vertex.Map.set hash ~key:def_ ~data:0 in
        helper t hash)
  in
  helper prog IG.Vertex.Map.empty
;;

let rec _seo_rev adj vertex_table seq =
  match IG.Vertex.Map.is_empty vertex_table with
  | true -> seq
  | false ->
    let u, _ =
      match
        IG.Vertex.Map.fold vertex_table ~init:None ~f:(fun ~key ~data accu ->
            match accu with
            | None -> Some (key, data)
            | Some (_, data') -> if data' > data then accu else Some (key, data))
      with
      | None -> failwith "empty vertex_table"
      | Some s -> s
    in
    let seq_new = u :: seq in
    let nbr = IG.Vertex.Map.find_exn adj u in
    let nbr = IG.Vertex.Set.remove nbr u in
    let vertex_table =
      IG.Vertex.Set.fold_right nbr ~init:vertex_table ~f:(fun x acc ->
          match IG.Vertex.Map.find vertex_table x with
          | None -> acc
          | Some v ->
            let order = v + 1 in
            IG.Vertex.Map.set vertex_table ~key:x ~data:order)
    in
    let vertex_table = IG.Vertex.Map.remove vertex_table u in
    _seo_rev adj vertex_table seq_new
;;

let seo adj prog =
  let vertex_table = gen_vertex_table prog in
  let seo_rev = _seo_rev adj vertex_table [] in
  List.rev seo_rev
;;

(* Allocate register for vertex.
 * vertex_to_reg is a hashtable from vertex to registers.
 * nbr is the neighbor of vertex
 *)
let alloc (nbr : IG.Vertex.Set.t) (vertex_to_reg : reg IG.Vertex.Map.t) : reg =
  let nbr_reg_l =
    IG.Vertex.Set.fold nbr ~init:[] ~f:(fun acc u ->
        match IG.Vertex.Map.find vertex_to_reg u with
        | None -> acc
        | Some u' -> u' :: acc)
  in
  let nbr_reg_s = Register.Set.of_list nbr_reg_l in
  let r = Register.find_min_available nbr_reg_s in
  Register.create_no r
;;

(* Infinite registers to allocate during greedy coloring. *)
let rec greedy seq adj vertex_to_reg =
  match seq with
  | [] -> vertex_to_reg
  | h :: t ->
    (match h with
    | IG.Vertex.T.Reg reg ->
      let vertex_to_reg =
        IG.Vertex.Map.set vertex_to_reg ~key:(IG.Vertex.T.Reg reg) ~data:reg
      in
      greedy t adj vertex_to_reg
    | IG.Vertex.T.Temp temp ->
      let nbr = IG.Vertex.Map.find_exn adj h in
      let reg = alloc nbr vertex_to_reg in
      let vertex_to_reg =
        IG.Vertex.Map.set vertex_to_reg ~key:(IG.Vertex.T.Temp temp) ~data:reg
      in
      greedy t adj vertex_to_reg)
;;

let rec gen_result (color : reg IG.Vertex.Map.t) prog =
  match prog with
  | [] -> []
  | h :: t ->
    (match Reg_info.get_def h with
    | None -> None :: gen_result color t
    | Some tmp ->
      (match tmp with
      | IG.Vertex.T.Temp _ ->
        let reg = IG.Vertex.Map.find color tmp in
        let tk =
          match reg with
          | None -> None
          | Some reg' -> Some (tmp, reg')
        in
        tk :: gen_result color t
      | IG.Vertex.T.Reg _ -> None :: gen_result color t))
;;

let print_vertex_to_reg (color : reg IG.Vertex.Map.t) =
  let () = printf "\n\n==========\nVertex to register\n" in
  let sorted_keys = List.sort (IG.Vertex.Map.keys color) ~compare:IG.Vertex.compare in
  List.iter sorted_keys ~f:(fun k ->
      let t = IG.Print.pp_vertex k in
      let r = Register.reg_idx (IG.Vertex.Map.find_exn color k) in
      printf "%s -> %d\n" t r);
  let l = List.map (IG.Vertex.Map.data color) ~f:(fun x -> x) in
  let s = Register.Set.of_list l in
  printf "Used %d register\n" (Register.Set.length s)
;;

let trans_operand (operand : AS.operand) =
  match operand with
  | AS.Temp t -> IG.Vertex.Set.of_list [ IG.Vertex.T.Temp t ]
  | AS.Imm _ -> IG.Vertex.Set.empty
;;

(* When there are too much temporaries, we spill them all to stacks. *)
let rec collect_vertex prog res =
  match prog with
  | [] -> res
  | h :: t ->
    (match h with
    | AS.Binop binop ->
      let res = IG.Vertex.Set.union res (trans_operand binop.dest) in
      let res = IG.Vertex.Set.union res (trans_operand binop.lhs) in
      let res = IG.Vertex.Set.union res (trans_operand binop.rhs) in
      collect_vertex t res
    | AS.Mov mov ->
      let res = IG.Vertex.Set.union res (trans_operand mov.dest) in
      let res = IG.Vertex.Set.union res (trans_operand mov.src) in
      collect_vertex t res
    | AS.CJump cjp ->
      let res = IG.Vertex.Set.union res (trans_operand cjp.lhs) in
      let res = IG.Vertex.Set.union res (trans_operand cjp.rhs) in
      collect_vertex t res
    | AS.Ret ret ->
      let res = IG.Vertex.Set.union res (trans_operand ret.var) in
      collect_vertex t res
    | AS.Jump _ | AS.Label _ | AS.Directive _ | AS.Comment _ -> collect_vertex t res)
;;

let gen_result_dummy vertex_set =
  let base = Register.num_gen_reg in
  let vertex_list = IG.Vertex.Set.to_list vertex_set in
  List.map vertex_list ~f:(fun vtx ->
      let reg =
        match vtx with
        | IG.Vertex.T.Reg r -> r
        | IG.Vertex.T.Temp t -> Register.create_no (base + Temp.value t)
      in
      Some (vtx, reg))
;;

let regalloc (assem_ps : AS.instr list) : (IG.Vertex.t * Register.t) option list =
  if Temp.count () > threshold
  then (
    let vertex_set = collect_vertex assem_ps IG.Vertex.Set.empty in
    gen_result_dummy vertex_set)
  else (
    let prog = Program.gen_regalloc_info assem_ps in
    let adj = build_graph prog IG.Vertex.Map.empty in
    let seq = seo adj prog in
    (* let vertex_to_reg = IG.Vertex.Map.empty in *)
    let vertex_to_reg = IG.Vertex.Map.empty in
    let color = greedy seq adj vertex_to_reg in
    (* let () = print_adj adj in
     let () = printf "SEO order\n" in
     let seq_l = List.map seq ~f:(fun x -> IG.Vertex.name x) in
     let () = List.iter ~f:(printf "%s ") seq_l in
     let () = print_vertex_to_reg color in
     let () = printf "\n" in *)
    gen_result color prog)
;;

(* This is used for l1 checkpoint to match the API. *)
let regalloc_ckpt (prog : Program.line list) : (IG.Vertex.t * Register.t) option list =
  let adj = build_graph prog IG.Vertex.Map.empty in
  let seq = seo adj prog in
  let vertex_to_reg = IG.Vertex.Map.empty in
  let color = greedy seq adj vertex_to_reg in
  gen_result color prog
;;
