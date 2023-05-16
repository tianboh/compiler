open Core
open Args
module AS_psu = Inst.Pseudo
module AS_x86 = Inst.X86
module Parse = Parser.Parse
module Elab = Parser.Elab
module Ast = Parser.Ast
module Cst = Parser.Cst
module Typechecker = Semantic.Typechecker
module Controlflow = Semantic.Controlflow
module Dfana = Flow.Dfana
module Tree = Parser.Tree
module Trans = Parser.Trans

let process_checkpoint
    (filename : string)
    (regalloc_only : bool)
    (df_type : Df_analysis.t)
  =
  match String.chop_suffix filename ~suffix:".in" with
  | None ->
    prerr_endline "Invalid input filename";
    exit 1
  | Some base_filename ->
    let input_json = Yojson.Basic.from_file filename in
    if regalloc_only
    then (
      let input = Json_reader.Lab1_checkpoint.program_of_json input_json in
      let input_temp = Regalloc.Program.transform_json_to_temp input in
      (* let () = Regalloc.Program.print_lines input_temp in *)
      let output = Regalloc.Ckpt.regalloc_ckpt input_temp in
      let output' = Regalloc.Ckpt.transform_vertices_to_json output in
      let filename = base_filename ^ ".out" in
      Out_channel.with_file filename ~f:(fun out ->
          Out_channel.output_string
            out
            (output'
            |> Json_reader.Lab1_checkpoint.json_of_allocations
            |> Yojson.Basic.to_string)))
    else (
      let input = Json_reader.Lab2_checkpoint.program_of_json input_json in
      let output = Dfana.dfana input df_type in
      let filename = base_filename ^ ".out" in
      Out_channel.with_file filename ~f:(fun out ->
          Out_channel.output_string
            out
            (output |> Json_reader.Lab2_checkpoint.json_of_dflines)))
;;
