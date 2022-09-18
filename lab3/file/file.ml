open Core
module Asm_ps = Inst.Pseudo
module Asm_x86 = Inst.X86

let c0_main = 
  match Sys.getenv "UNAME" with
  | Some("Darwin") -> "__c0_main"
  | _ -> "_c0_main"

let dump_asm_ps file_name ps_asm = 
  Out_channel.with_file file_name ~f:(fun out ->
    let output_instr instr = Out_channel.fprintf out "\t%s\n" (Asm_ps.format instr) in
    output_instr (Asm_ps.Directive (".file\t\"" ^ file_name ^ "\""));
    output_instr (Asm_ps.Directive ".function\tmain()");
    List.iter ~f:output_instr ps_asm;
    output_instr (Asm_ps.Directive ".ident\t\"15-411 L1 reference compiler\""))

let dump_asm_x86 file_name x86_asm = 
  (* header *)
  let () = Out_channel.with_file file_name ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (Asm_x86.format instr) in
      output_instr (Asm_x86.Directive (".file\t\"" ^ file_name ^ "\""));
      output_instr (Asm_x86.Directive ".text");
      output_instr (Asm_x86.Directive (".globl " ^ c0_main));
      (* output_instr (Asm_x86.Directive ".type	main, @function"); *)
      ) in
  (* Main header*)
  let () = Out_channel.with_file file_name ~f:(fun out ->
    let output_instr instr = Out_channel.fprintf out "%s\n" (Asm_x86.format instr) in
    output_instr (Asm_x86.Directive (c0_main ^ ":"))) ~append:true in
  (* Main body *)
  Out_channel.with_file file_name ~f:(fun out ->
    let output_instr instr = Out_channel.fprintf out "\t%s\n" (Asm_x86.format instr) in
      List.iter ~f:output_instr x86_asm;
      (* output_instr (Asm_x86.Directive "ret") *)
      ) ~append:true
      (* output_instr (Asm_x86.Directive ".ident\t\"15-411 L1 reference compiler\"")) ~append:true  *)