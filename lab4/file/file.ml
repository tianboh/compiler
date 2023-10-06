open Core
module Ast = Front.Ast
module Quad = Quads.Inst
module Abs = Abs_asm.Inst
module X86 = X86_asm.Inst
module Register = Var.X86_reg.Logic
module Memory = Var.Memory
module Symbol = Util.Symbol
module Temp = Var.Temp

let dump_quad file_name (program : Quad.program) =
  Out_channel.with_file file_name ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (Quad.pp_inst instr) in
      output_instr (Quad.Directive (".file\t\"" ^ file_name ^ "\"")));
  List.iter program ~f:(fun fdefn ->
      let insts = fdefn.body in
      Out_channel.with_file
        file_name
        ~f:(fun out ->
          let output_instr instr =
            match instr with
            | Quad.Label _ | Quad.Directive _ ->
              Out_channel.fprintf out "%s\n" (Quad.pp_inst instr)
            | _ -> Out_channel.fprintf out "\t%s\n" (Quad.pp_inst instr)
          in
          let func_name = Symbol.name fdefn.func_name in
          let pars =
            List.map fdefn.pars ~f:(fun par -> Temp.name par) |> String.concat ~sep:", "
          in
          output_instr (Quad.Directive (sprintf ".function\t%s(%s)" func_name pars));
          List.iter ~f:output_instr insts)
        ~append:true);
  Out_channel.with_file
    file_name
    ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (Quad.pp_inst instr) in
      output_instr (Quad.Directive ".ident\t\"15-411 reference compiler\""))
    ~append:true
;;

let dump_abs file_name (program : Abs.program) =
  let program = Abs.pp_program program "" in
  Out_channel.with_file file_name ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (Abs.pp_inst instr) in
      output_instr (Abs.Directive (".file\t\"" ^ file_name ^ "\""));
      output_instr (Abs.Directive ".text"));
  Out_channel.with_file
    file_name
    ~f:(fun out -> Out_channel.fprintf out "%s\n" program)
    ~append:true
;;

let dump_x86 file_name fnames instrs =
  let fnames =
    List.filter_map fnames ~f:(fun t ->
        let name, scope = t in
        match scope with
        | `C0 -> Some (Symbol.pp_scope scope ^ name)
        | _ -> None)
  in
  (* header *)
  Out_channel.with_file file_name ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (X86.format instr) in
      output_instr (X86.Directive (".file\t\"" ^ file_name ^ "\""));
      output_instr (X86.Directive ".text");
      output_instr (X86.Directive (".globl " ^ String.concat fnames ~sep:", ")));
  Out_channel.with_file
    file_name
    ~f:(fun out ->
      let output_instr instr =
        match instr with
        | X86.Label _ | X86.GDB _ | X86.Fname _ ->
          Out_channel.fprintf out "%s\n" (X86.format instr)
        | _ -> Out_channel.fprintf out "\t%s\n" (X86.format instr)
      in
      List.iter ~f:output_instr instrs)
    ~append:true
;;
