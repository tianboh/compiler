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
end

module Make (I : InstrInterface) : sig
  val eliminate_fall_through : I.t list -> I.t list
  val add_synthetic_label : int -> I.t list -> I.t list -> I.t list
end = struct
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
                let jump_instr = I.jump (I.get_label h) in
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
                let synth_label_instr = I.label synth_label in
                add_synthetic_label (next_synth_id + 1) (h :: acc_instrs)
                  (synth_label_instr :: t)
        else add_synthetic_label next_synth_id (h :: acc_instrs) t
end
