open Core
module Ast = Front.Ast
module Asm_ps = Middle.Inst
module Asm_x86 = Inst.X86
module Register = Var.X86_reg
module Memory = Var.Memory

let c0_main =
  match Sys.getenv "UNAME" with
  | Some "Darwin" -> "__c0_main"
  | _ -> "_c0_main"
;;

let dump_asm_ps file_name ps_asm =
  Out_channel.with_file file_name ~f:(fun out ->
      let output_instr instr =
        match instr with
        | Asm_ps.Label _ | Asm_ps.Directive _ ->
          Out_channel.fprintf out "%s\n" (Asm_ps.pp_instr instr)
        | _ -> Out_channel.fprintf out "\t%s\n" (Asm_ps.pp_instr instr)
      in
      output_instr (Asm_ps.Directive (".file\t\"" ^ file_name ^ "\""));
      output_instr (Asm_ps.Directive ".function\tmain()");
      List.iter ~f:output_instr ps_asm;
      output_instr (Asm_ps.Directive ".ident\t\"15-411 L1 reference compiler\""))
;;

let dump_asm_x86 file_name x86_asm =
  (* header *)
  let () =
    Out_channel.with_file file_name ~f:(fun out ->
        let output_instr instr =
          Out_channel.fprintf out "\t%s\n" (Asm_x86.format instr)
        in
        output_instr (Asm_x86.Directive (".file\t\"" ^ file_name ^ "\""));
        output_instr (Asm_x86.Directive ".text");
        output_instr (Asm_x86.Directive (".globl " ^ c0_main)))
  in
  (* Main header*)
  let () =
    Out_channel.with_file
      file_name
      ~f:(fun out ->
        let output_instr instr = Out_channel.fprintf out "%s\n" (Asm_x86.format instr) in
        output_instr (Asm_x86.Directive (c0_main ^ ":")))
      ~append:true
  in
  (* Main prologue *)
  let () =
    Out_channel.with_file
      file_name
      ~f:(fun out ->
        let output_instr content = Out_channel.fprintf out "%s\n" content in
        output_instr (Asm_x86.format_prologue Memory.get_allocated_count))
      ~append:true
  in
  (* Main body *)
  Out_channel.with_file
    file_name
    ~f:(fun out ->
      let output_instr instr =
        match instr with
        | Asm_x86.Label _ | Asm_x86.GDB _ ->
          Out_channel.fprintf out "%s\n" (Asm_x86.format instr)
        | _ -> Out_channel.fprintf out "\t%s\n" (Asm_x86.format instr)
      in
      List.iter ~f:output_instr x86_asm)
    ~append:true
;;
