open Core
module Ast = Front.Ast
module Asm_ps = Quads.Inst
module Asm_x86 = X86_asm.Inst
module Register = Var.X86_reg.Logic
module Memory = Var.Memory
module Symbol = Util.Symbol
module Temp = Var.Temp

let c0_main =
  match Sys.getenv "UNAME" with
  | Some "Darwin" -> "__c0_main"
  | _ -> "_c0_main"
;;

let dump_ps file_name (program : Asm_ps.program) =
  Out_channel.with_file file_name ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (Asm_ps.pp_inst instr) in
      output_instr (Asm_ps.Directive (".file\t\"" ^ file_name ^ "\"")));
  List.iter program ~f:(fun fdefn ->
      let insts = fdefn.body in
      Out_channel.with_file
        file_name
        ~f:(fun out ->
          let output_instr instr =
            match instr with
            | Asm_ps.Label _ | Asm_ps.Directive _ ->
              Out_channel.fprintf out "%s\n" (Asm_ps.pp_inst instr)
            | _ -> Out_channel.fprintf out "\t%s\n" (Asm_ps.pp_inst instr)
          in
          let func_name = Symbol.name fdefn.func_name in
          let pars =
            List.map fdefn.pars ~f:(fun par -> Temp.name par) |> String.concat ~sep:", "
          in
          output_instr (Asm_ps.Directive (sprintf ".function\t%s(%s)" func_name pars));
          List.iter ~f:output_instr insts)
        ~append:true);
  Out_channel.with_file
    file_name
    ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (Asm_ps.pp_inst instr) in
      output_instr (Asm_ps.Directive ".ident\t\"15-411 L1 reference compiler\""))
    ~append:true
;;

let dump_asm_x86 file_name fnames instrs =
  (* header *)
  Out_channel.with_file file_name ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (Asm_x86.format instr) in
      output_instr (Asm_x86.Directive (".file\t\"" ^ file_name ^ "\""));
      output_instr (Asm_x86.Directive ".text");
      output_instr (Asm_x86.Directive (".globl " ^ String.concat fnames ~sep:", ")));
  Out_channel.with_file
    file_name
    ~f:(fun out ->
      let output_instr instr =
        match instr with
        | Asm_x86.Label _ | Asm_x86.GDB _ | Asm_x86.Fname _ ->
          Out_channel.fprintf out "%s\n" (Asm_x86.format instr)
        | _ -> Out_channel.fprintf out "\t%s\n" (Asm_x86.format instr)
      in
      List.iter ~f:output_instr instrs)
    ~append:true
;;
