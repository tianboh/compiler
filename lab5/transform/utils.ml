(* Make sure no fallthrough between basic blocks. 
 * Add unconditional jump instr if fallthrough is detected. *)

module Label = Util.Label
module Ana_CFG = Analysis_cfg.Sig
open Core

module type InstrInterface = sig
  include Ana_CFG.InstrInterface

  (* Replace target of Jump *)
  val replace_target : t -> Label.t -> t

  (* Replace old target to new target for CJump *)
  val replace_ctarget : t -> Label.t -> Label.t -> t
  val gen_label : Label.t -> t
  val gen_jump : Label.t -> t
  val gen_ret : unit -> t
end

module Make
    (I : InstrInterface)
    (CFG : Analysis_cfg.Sig.CFGInterface with type i = I.t) : sig
  val eliminate_fall_through : I.t list -> I.t list
  val add_synthetic_label : int -> I.t list -> I.t list -> I.t list

  (* split_critical_edges input I.t list should already be a CFG, which means
   * eliminate_fall_trhough and add_synthetic_label should already be called before. *)
  val split_critical_edges : I.t list -> I.t list
end = struct
  let split_id = ref 0

  let rec helper (acc_instrs : I.t list) (instrs : I.t list) : I.t list =
    match instrs with
    | [] -> List.rev acc_instrs
    | h :: t ->
        if I.is_label h then
          match acc_instrs with
          (* h is entry label *)
          | [] -> helper (h :: acc_instrs) t
          | prev_instr :: _ ->
              if
                I.is_jump prev_instr || I.is_cjump prev_instr
                || I.is_return prev_instr
              then helper (h :: acc_instrs) t
              else
                let jump_instr = I.gen_jump (I.get_label h) in
                helper (h :: jump_instr :: acc_instrs) t
        else helper (h :: acc_instrs) t

  let eliminate_fall_through (instrs : I.t list) : I.t list = helper [] instrs

  (* Make sure each terminator is followed by a label. If not, add a synthetic label after it 
   * This function ensures even unreachable instructions have a label, therefore they are
   * in their own block. *)
  let rec add_synthetic_label (next_synth_id : int) (acc_instrs : I.t list)
      (instrs : I.t list) : I.t list =
    match instrs with
    | [] -> List.rev acc_instrs
    | h :: t ->
        if I.is_terminator h then
          match t with
          | [] -> List.rev (h :: acc_instrs)
          | next :: _ ->
              if I.is_label next then
                add_synthetic_label next_synth_id (h :: acc_instrs) t
              else
                let synth_label =
                  Label.label (Some ("synth" ^ string_of_int next_synth_id))
                in
                let synth_label_instr = I.gen_label synth_label in
                add_synthetic_label (next_synth_id + 1) (h :: acc_instrs)
                  (synth_label_instr :: t)
        else add_synthetic_label next_synth_id (h :: acc_instrs) t

  let has_edge (u_label : Label.t) (v_label : Label.t) (bbmap : CFG.bbmap) :
      bool =
    let u_bb = Label.Map.find_exn bbmap u_label in
    List.mem u_bb.succs v_label ~equal:Label.equal

  let is_critical_edge (u_label : Label.t) (v_label : Label.t)
      (bbmap : CFG.bbmap) : bool =
    let u_bb = Label.Map.find_exn bbmap u_label in
    let v_bb = Label.Map.find_exn bbmap v_label in
    let edge_uv_exist = has_edge u_label v_label bbmap in
    let src_has_multi_dests =
      if List.length u_bb.succs > 1 then true else false
    in
    let dest_has_multi_srcs =
      if List.length v_bb.preds > 1 then true else false
    in
    edge_uv_exist && src_has_multi_dests && dest_has_multi_srcs

  let split_edge (u_label : Label.t) (v_label : Label.t) (bbmap : CFG.bbmap) :
      CFG.bbmap * Label.t =
    let u_bb_old = Label.Map.find_exn bbmap u_label in
    let v_bb_old = Label.Map.find_exn bbmap v_label in
    assert (has_edge u_label v_label bbmap);
    let label_name = sprintf "split_%d" !split_id in
    split_id := !split_id + 1;
    let new_label = Label.label' label_name in
    let new_bb : CFG.bb =
      {
        label = new_label;
        instrs = [ I.gen_label new_label; I.gen_jump v_label ];
        preds = [ u_label ];
        succs = [ v_label ];
      }
    in
    let u_bb_instrs =
      List.fold_left u_bb_old.instrs ~init:[] ~f:(fun acc instr ->
          let new_instr =
            if
              I.is_jump instr
              && List.mem (I.get_targets instr) v_label ~equal:Label.equal
            then I.replace_target instr new_label
            else if
              I.is_cjump instr
              && List.mem (I.get_targets instr) v_label ~equal:Label.equal
            then I.replace_ctarget instr v_label new_label
            else instr
          in
          new_instr :: acc)
      |> List.rev
    in
    let u_bb_new_succs =
      new_label
      :: List.filter u_bb_old.succs ~f:(fun x -> not (Label.equal x v_label))
    in
    let u_bb_new =
      { u_bb_old with instrs = u_bb_instrs; succs = u_bb_new_succs }
    in
    let v_bb_new_preds =
      new_label
      :: List.filter v_bb_old.preds ~f:(fun x -> not (Label.equal x u_label))
    in
    let v_bb_new = { v_bb_old with preds = v_bb_new_preds } in
    let bbmap = Label.Map.set bbmap ~key:u_label ~data:u_bb_new in
    let bbmap = Label.Map.set bbmap ~key:v_label ~data:v_bb_new in
    let bbmap = Label.Map.set bbmap ~key:new_label ~data:new_bb in
    (bbmap, new_label)

  let split_critical_edges (instrs : I.t list) : I.t list =
    let initial_bbmap, initial_orders = CFG.build_bb instrs in
    let critical_edges : (Label.t * Label.t) list =
      List.fold_right initial_orders ~init:[] ~f:(fun u_label acc ->
          let u_bb = Label.Map.find_exn initial_bbmap u_label in
          List.fold_right u_bb.succs ~init:acc ~f:(fun v_label acc_inner ->
              if is_critical_edge u_label v_label initial_bbmap then
                (u_label, v_label) :: acc_inner
              else acc_inner))
    in
    let finale_bbmap, final_labels =
      List.fold_left critical_edges ~init:(initial_bbmap, initial_orders)
        ~f:(fun (current_bbmap, current_orders) edge ->
          let u_label, v_label = edge in
          let new_bbmap, new_label = split_edge u_label v_label current_bbmap in
          let new_orders =
            List.fold_right current_orders ~init:[] ~f:(fun l acc ->
                if Label.equal l u_label then l :: new_label :: acc
                else l :: acc)
          in

          (new_bbmap, new_orders))
    in
    CFG.to_instrs finale_bbmap final_labels
end
