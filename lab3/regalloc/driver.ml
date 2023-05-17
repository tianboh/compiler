open Core

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
 *     Also, for special instructions like mul, div, mod, shift, we build edge between
 *     those special registers,like eax and edx for div and mod, and live out temporaries.
 *     This ensures that when these instructions are executed, we can use eax, edx for free.
 *     In other words, we don't need to store their value before use them.
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
 *     is greater than its allocated neighbors. Also, we will avoid assign register to temporary if
 *     that register is a neighbor of the temporary.
 *     Time complexity for coloring: O(v + e)
 *)
module Temp = Var.Temp
module Memory = Var.Memory
module Register = Var.X86_reg
module Reg_info = Program
module AS = Middle.Inst
module IG = Interference_graph

type reg = Register.t

type dest =
  | Reg of Register.t
  | Mem of Memory.t

let threshold = 2000
let eax = Register.RAX
let ecx = Register.RCX
let edx = Register.RDX

module Lazy = struct
  (* When there are too many temporaries, we will not spend time on
   * register allocation algorithm. Instead, we spill them all to memory.
   * This will greatly reduce the time for reg alloc algorithm. *)
  let trans_operand (operand : AS.operand) =
    match operand with
    | AS.Temp t -> IG.Vertex.Set.of_list [ IG.Vertex.T.Temp t ]
    | AS.Imm _ -> IG.Vertex.Set.empty
  ;;

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
    let base = Register.num_reg in
    let vertex_list = IG.Vertex.Set.to_list vertex_set in
    List.map vertex_list ~f:(fun vtx ->
        let dest =
          match vtx with
          | IG.Vertex.T.Reg r -> Reg r
          | IG.Vertex.T.Temp t ->
            let idx = base + Temp.value t in
            Mem (Memory.create idx Register.RSP idx 8)
        in
        Some (vtx, dest))
  ;;
end

module Print = struct
  open Printf

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

  let print_vertex_to_dest (color : dest IG.Vertex.Map.t) =
    let () = printf "\n\n==========\nVertex to register\n" in
    let sorted_keys = List.sort (IG.Vertex.Map.keys color) ~compare:IG.Vertex.compare in
    List.iter sorted_keys ~f:(fun k ->
        let t = IG.Print.pp_vertex k in
        let r =
          match IG.Vertex.Map.find_exn color k with
          | Reg r -> Register.reg_idx r
          | Mem m -> Memory.mem_idx m
        in
        printf "%s -> %d\n" t r);
    let l = List.map (IG.Vertex.Map.data color) ~f:(fun x -> x) in
    printf "Used %d register\n" (List.length l)
  ;;
end

module Helper = struct
  (* Build edge between vertices and vertex *)
  let build_vtx_vtxs adj vertex vertices =
    let s_vertex = IG.Vertex.Set.of_list [ vertex ] in
    let s_vertex_nbr =
      match IG.Vertex.Map.find adj vertex with
      | None -> IG.Vertex.Set.empty
      | Some s -> s
    in
    let s_vertex_nbr_union = IG.Vertex.Set.union s_vertex_nbr vertices in
    let adj = IG.Vertex.Map.set adj ~key:vertex ~data:s_vertex_nbr_union in
    IG.Vertex.Set.fold_right vertices ~init:adj ~f:(fun v adj ->
        let s_vertices =
          match IG.Vertex.Map.find adj v with
          | None -> IG.Vertex.Set.empty
          | Some s -> s
        in
        let s_res = IG.Vertex.Set.union s_vertices s_vertex in
        IG.Vertex.Map.set adj ~key:v ~data:s_res)
  ;;

  (* This is how we reuse eax, edx, ecx and other special registers. 
   * These registers(vertices) are connected to all live-out vertices.
   * so when the instruction is executed, eax, edx and ecx will be
   * available and do not need to use swap to store the info in eax, 
   * edx and ecx. For example, for div instruction, we connect eax and
   * edx to all current live out temporaries. For sal, sar instruction,
   * we connect ecx to all current temporaries.
   *)
  let precolor adj def s_lo uses instr =
    match instr with
    | AS.Binop binop ->
      (match binop.op with
      | AS.Times ->
        let def = IG.Vertex.Set.of_list [ def ] in
        let s_l = IG.Vertex.Set.union s_lo def in
        let s_l = IG.Vertex.Set.union s_l uses in
        build_vtx_vtxs adj (IG.Vertex.T.Reg eax) s_l
      | AS.Divided_by | AS.Modulo ->
        let def = IG.Vertex.Set.of_list [ def ] in
        let s_l = IG.Vertex.Set.union s_lo def in
        let s_l = IG.Vertex.Set.union s_l uses in
        let adj = build_vtx_vtxs adj (IG.Vertex.T.Reg eax) s_l in
        build_vtx_vtxs adj (IG.Vertex.T.Reg edx) s_l
      | AS.Right_shift | AS.Left_shift ->
        let def = IG.Vertex.Set.of_list [ def ] in
        let s_l = IG.Vertex.Set.union s_lo def in
        let s_l = IG.Vertex.Set.union s_l uses in
        build_vtx_vtxs adj (IG.Vertex.T.Reg ecx) s_l
      | AS.Equal_eq | AS.Greater | AS.Greater_eq | AS.Less | AS.Less_eq | AS.Not_eq ->
        let def = IG.Vertex.Set.of_list [ def ] in
        let s_l = IG.Vertex.Set.union s_lo def in
        let s_l = IG.Vertex.Set.union s_l uses in
        build_vtx_vtxs adj (IG.Vertex.T.Reg eax) s_l
      | AS.Plus | AS.Minus | AS.And | AS.Or | AS.Xor -> adj)
    | AS.Ret _
    | AS.Mov _
    | AS.Jump _
    | AS.CJump _
    | AS.Label _
    | AS.Directive _
    | AS.Comment _ -> adj
  ;;

  (* Build interference graph based on def and (live_out Union uses).
   * The insight here is we cannot allocate/assign register for def with the same register as
   * registers allocated for live_out temps.
   * Theoretically, we don't need to build edge between def and uses. But In order to 
   * make x86 assembly code generation easier, we don't allow uses and def to be assigned
   * to the same register. This can be more flexible for x86 assembly code generation.
   *)
  let rec build_graph reginfo_instr adj =
    match reginfo_instr with
    | [] -> adj
    | h :: t ->
      let reginfo, instr = h in
      let adj =
        match Reg_info.get_def reginfo with
        | None -> adj
        | Some def ->
          let s_def_nbr =
            match IG.Vertex.Map.find adj def with
            | Some s -> s
            | None -> IG.Vertex.Set.empty
          in
          let s_lo = reginfo.live_out in
          let s_u = IG.Vertex.Set.union s_def_nbr s_lo in
          let adj = precolor adj def s_lo reginfo.uses instr in
          build_vtx_vtxs adj def s_u
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
end

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
  let vertex_table = Helper.gen_vertex_table prog in
  let seo_rev = _seo_rev adj vertex_table [] in
  List.rev seo_rev
;;

(* 
 * ESP(6) and EBP(7) are used to store stack pointer and base pointer respectively, 
 * we should not assign these two registers for general purpose use like register allocation. 
 * We also preserver r15(15) as a swap register, and do not assign it for register allocation.
 *)
let special_use = function
  | 6 | 7 | 15 -> true
  | _ -> false
;;

(* find minimum available register with neighbor nbr *)
let find_min_available (nbr : Int.Set.t) (black_set : Int.Set.t) : int =
  let rec helper (idx : int) (nbr : Int.Set.t) =
    if special_use idx || Set.mem black_set idx
    then helper (idx + 1) nbr
    else if Set.mem nbr idx
    then helper (idx + 1) nbr
    else idx
  in
  helper 0 nbr
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
let alloc (nbr : IG.Vertex.Set.t) (vertex_to_dest : dest IG.Vertex.Map.t) : dest =
  (* If a temporary is connected to a register, 
   * we cannot assign this register to it. *)
  let nbr_black_list =
    IG.Vertex.Set.fold nbr ~init:[] ~f:(fun acc u ->
        match u with
        | IG.Vertex.T.Reg r -> Register.reg_idx r :: acc
        | IG.Vertex.T.Temp _ -> acc)
  in
  (* Keep track of assigned registers for neighbor temporaries *)
  let nbr_int_l =
    IG.Vertex.Set.fold nbr ~init:[] ~f:(fun acc u ->
        match IG.Vertex.Map.find vertex_to_dest u with
        | None -> acc
        | Some u' ->
          (match u' with
          | Reg r -> Register.reg_idx r :: acc
          | Mem m -> Memory.mem_idx m :: acc))
  in
  let nbr_int_s = Int.Set.of_list nbr_int_l in
  let black_set = Int.Set.of_list nbr_black_list in
  let r = find_min_available nbr_int_s black_set in
  if r < Register.num_reg
  then Reg (Register.idx_reg r)
  else Mem (Memory.create r Register.RBP r 8)
;;

(* Infinite registers to allocate during greedy coloring. *)
let rec greedy seq adj vertex_to_dest =
  match seq with
  | [] -> vertex_to_dest
  | h :: t ->
    (match h with
    | IG.Vertex.T.Reg reg ->
      let vertex_to_dest =
        IG.Vertex.Map.set vertex_to_dest ~key:(IG.Vertex.T.Reg reg) ~data:(Reg reg)
      in
      greedy t adj vertex_to_dest
    | IG.Vertex.T.Temp temp ->
      let nbr = IG.Vertex.Map.find_exn adj h in
      let dest = alloc nbr vertex_to_dest in
      let vertex_to_dest =
        IG.Vertex.Map.set vertex_to_dest ~key:(IG.Vertex.T.Temp temp) ~data:dest
      in
      greedy t adj vertex_to_dest)
;;

let rec gen_result (color : dest IG.Vertex.Map.t) prog =
  match prog with
  | [] -> []
  | h :: t ->
    (match Reg_info.get_def h with
    | None -> None :: gen_result color t
    | Some tmp ->
      (match tmp with
      | IG.Vertex.T.Temp _ ->
        let dest = IG.Vertex.Map.find color tmp in
        let tk =
          match dest with
          | None -> None
          | Some dest' -> Some (tmp, dest')
        in
        tk :: gen_result color t
      | IG.Vertex.T.Reg _ -> None :: gen_result color t))
;;

let regalloc (assem_ps : AS.instr list) : (IG.Vertex.t * dest) option list =
  if Temp.count () > threshold
  then (
    let vertex_set = Lazy.collect_vertex assem_ps IG.Vertex.Set.empty in
    Lazy.gen_result_dummy vertex_set)
  else (
    let reginfo_instrs = Program.gen_regalloc_info assem_ps in
    let adj = Helper.build_graph reginfo_instrs IG.Vertex.Map.empty in
    let prog =
      List.fold_left reginfo_instrs ~init:[] ~f:(fun acc line ->
          let reginfo, _ = line in
          reginfo :: acc)
    in
    let seq = seo adj prog in
    (* let vertex_to_dest = IG.Vertex.Map.empty in *)
    let vertex_to_dest = IG.Vertex.Map.empty in
    let color = greedy seq adj vertex_to_dest in
    (* Print.print_adj adj;
    printf "SEO order\n";
    let seq_l = List.map seq ~f:(fun x -> IG.Print.pp_vertex x) in
    List.iter ~f:(printf "%s ") seq_l;
    Print.print_vertex_to_dest color;
    printf "\n"; *)
    gen_result color prog)
;;
