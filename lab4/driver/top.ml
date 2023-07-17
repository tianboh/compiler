(* L3 Compiler
 * Top Level Environment
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Use Cmdliner instead of Getopt for command-line parsing.
 * Modified: Henry Nelson <hcnelson99@gmail.com>
 *   - Switch from ocamlbuild to dune 2.7
 *   - TODO: Add support for expect tests
 *   - Update to Core v0.14
 *)

open Core
open Args
module Parse = Front.Parse
module Elab = Front.Elab
module AST = Front.Ast
module CST = Front.Cst
module Typechecker = Semantic.Typechecker
module Controlflow = Semantic.Controlflow
module Dfana = Flow.Dfana
module Memory = Var.Memory
module Symbol = Util.Symbol

(* Command line arguments *)
type cmd_line_args =
  { verbose : bool
  ; dump_parsing : bool
  ; dump_cst : bool
  ; dump_ast : bool
  ; dump_ir : bool
  ; dump_assem : bool
  ; dump_conv : bool
  ; semcheck_only : bool
  ; regalloc_only : bool
  ; emit : Emit.t
  ; opt_level : Opt_level.t
  ; df_type : Df_analysis.t
  ; header_file : string option
  ; filename : string
  }

(* A term (using the vocabulary of the Cmdliner library) that can be used to
 * parse command-line arguments. *)
(* cheetsheet: https://github.com/mjambon/cmdliner-cheatsheet *)
let cmd_line_term : cmd_line_args Cmdliner.Term.t =
  let open Cmdliner in
  (* See https://github.com/janestreet/ppx_let *)
  (* This allows a more convenient syntax for using the Cmdliner
   * library: If we use let%map instead of normal "let", and we
   * have a declaration of the form:
   *
   * let%map x = e1 in e2
   *
   * even if e1 is of type 'a Term.t, we can use x as having type 'a
   * in the body of e2.
   *)
  let module Let_syntax = struct
    let return = Term.pure
    let map ~f a = Term.(return f $ a)
    let both a b = Term.(pure Tuple2.create $ a $ b)
  end
  in
  let flag info = Arg.value (Arg.flag info) in
  let opt conv ~default info = Arg.value (Arg.opt conv default info) in
  let%map verbose =
    let doc = "If present, print verbose debug information." in
    flag (Arg.info [ "v"; "verbose" ] ~doc)
  and dump_parsing =
    let doc = "If present, print debug informaton from parsing." in
    flag (Arg.info [ "dump-parsing" ] ~doc)
  and dump_cst =
    let doc = "If present, print the parsed cst." in
    flag (Arg.info [ "dump-cst" ] ~doc)
  and dump_ast =
    let doc = "If present, print the parsed ast." in
    flag (Arg.info [ "dump-ast" ] ~doc)
  and dump_ir =
    let doc = "If present, print the translated ir ast." in
    flag (Arg.info [ "dump-ir" ] ~doc)
  and dump_assem =
    let doc = "If present, print the final assembly." in
    flag (Arg.info [ "dump-assem" ] ~doc)
  and dump_conv =
    let doc = "If present, print the x86 conventional assembly." in
    flag (Arg.info [ "dump-conv" ] ~doc)
  and semcheck_only =
    let doc = "If present, exit after semantic analysis." in
    flag (Arg.info [ "t"; "semcheck-only" ] ~doc)
  and regalloc_only =
    let doc = "Regalloc only for l1 checkpoint" in
    flag (Arg.info [ "r"; "regalloc-only" ] ~doc)
  and emit =
    let doc = "[abs|x86-64] The type of assembly $(docv) to emit." in
    opt
      Emit.conv
      ~default:Emit.Abstract_assem
      (Arg.info [ "e"; "emit" ] ~doc ~docv:"TARGET")
  and opt_level =
    let doc = "[0|1|2] The optimization level $(docv)." in
    opt
      Opt_level.conv
      ~default:Opt_level.Opt_none
      (Arg.info [ "O"; "opt" ] ~doc ~docv:"OPT")
  and df_type =
    let doc =
      "[forward-may|forward-must|backward-may|backward-must|no-analysis] The type of \
       dataflow analysis"
    in
    opt
      Df_analysis.conv
      ~default:Df_analysis.No_analysis
      (Arg.info [ "r2"; "lab2 checkpoint" ] ~doc ~docv:"DF-ANALYSIS")
  and filename =
    let doc = "The source file $(docv) to compile." in
    Arg.(required (pos 0 (some non_dir_file) None (info [] ~doc ~docv:"FILE")))
  and header_file =
    let info =
      Arg.info [ "l"; "link" ] ~docv:"NUM" ~doc:"The header file $(docv) to compile."
    in
    Arg.value (Arg.opt (Arg.some Arg.string) None info)
  in
  { verbose
  ; dump_parsing
  ; dump_cst
  ; dump_ast
  ; dump_ir
  ; dump_assem
  ; dump_conv
  ; semcheck_only
  ; regalloc_only
  ; emit
  ; opt_level
  ; df_type
  ; filename
  ; header_file
  }
;;

let say_if (v : bool) (f : unit -> string) = if v then prerr_endline (f ())

(* The main driver for the compiler: runs each phase. *)
let compile (cmd : cmd_line_args) : unit =
  let cst =
    match cmd.header_file with
    | Some header -> Parse.parse header true @ Parse.parse cmd.filename false
    | None -> Parse.parse cmd.filename false
  in
  say_if cmd.verbose (fun () -> "Parsing... " ^ cmd.filename);
  if cmd.dump_parsing then ignore (Parsing.set_trace true : bool);
  say_if cmd.dump_cst (fun () -> CST.Print.pp_program cst);
  let ast = Elab.elaborate cst in
  let func_name, ret_type = Symbol.symbol "main", `Int in
  let ast = AST.Fdecl { ret_type; func_name; pars = []; scope = `C0 } :: ast in
  say_if cmd.dump_ast (fun () -> AST.Print.pp_program ast);
  say_if cmd.verbose (fun () -> "Semantic analysis...");
  let tst, tc_env = Semantic.Driver.run ast in
  if cmd.semcheck_only then exit 0;
  (* Translate *)
  say_if cmd.verbose (fun () -> "Translating...");
  let ir = Ir_tree.Trans.translate tst tc_env false in
  (* let ir_ssa = List.map ir ~f:(fun ir -> Ssa.Trans.run ir) in *)
  say_if cmd.dump_ir (fun () ->
      List.map ir ~f:Ir_tree.Inst.Print.pp_fdefn |> String.concat ~sep:"\n");
  (* Codegen *)
  say_if cmd.verbose (fun () -> "Codegen...");
  (* let start = Unix.gettimeofday () in *)
  let assem_ps_ssa = Quads.Trans.gen ir in
  (* let assem_ps_ssa = Codegen.Optimize.optimize assem_ps_ssa in *)
  (* let () = Codegen.Gen.Pseudo.print_insts assem_ps_ssa in *)
  (* let stop = Unix.gettimeofday () in *)
  (* let () = Printf.printf "Execution time assem_ps_ssa: %fs\n%!" (stop -. start) in *)
  say_if cmd.dump_assem (fun () -> Quads.Inst.pp_program assem_ps_ssa "");
  match cmd.emit with
  (* Output: abstract 3-address assem *)
  | Abstract_assem ->
    let file = cmd.filename ^ ".abs" in
    say_if cmd.verbose (fun () -> sprintf "Writing abstract assem to %s..." file);
    File.dump_ps file assem_ps_ssa
  | X86_64 ->
    let file = cmd.filename ^ ".s" in
    say_if cmd.verbose (fun () -> sprintf "Writing x86 assem to %s..." file);
    (* let start = Unix.gettimeofday () in *)
    (* let stop = Unix.gettimeofday () in *)
    (* let () = Printf.printf "Execution time gen_regalloc_info: %fs\n%!" (stop -. start) in *)
    (* let start = Unix.gettimeofday () in *)
    let assem_x86_conv = Abs_asm.Trans.gen assem_ps_ssa [] in
    say_if cmd.dump_conv (fun () -> Abs_asm.Inst.pp_program assem_x86_conv "");
    let progs =
      List.map assem_x86_conv ~f:(fun fdefn ->
          let reg_alloc_info = Regalloc.Driver.regalloc fdefn in
          let instrs = X86_asm.Trans.gen fdefn reg_alloc_info in
          fdefn.func_name, instrs)
    in
    let _, instrs = List.unzip progs in
    let fnames =
      List.filter assem_x86_conv ~f:(fun fdefn -> phys_equal fdefn.scope `C0)
      |> List.map ~f:(fun f -> f.func_name, f.scope)
    in
    let instrs =
      List.concat instrs @ X86_asm.Trans.fpe_handler @ X86_asm.Trans.abort_handler
    in
    File.dump_asm_x86 file fnames instrs
;;

let run (cmd : cmd_line_args) : unit =
  let f = cmd.filename in
  match cmd.regalloc_only, cmd.df_type with
  | true, No_analysis
  | false, Forward_may
  | false, Forward_must
  | false, Backward_may
  | false, Backward_must -> Ckpt.process_checkpoint f cmd.regalloc_only cmd.df_type
  | _, _ ->
    (try compile cmd with
    | Util.Error_msg.Error ->
      prerr_endline "Compilation failed.";
      exit 1)
;;

(* Compiler entry point
 * Use the cmd_line_term to parse the command line arguments, and pass the
 * parsed args to the run function.
 *)
let main () =
  let open Cmdliner in
  let cmd_line_info = Term.info "c0c" ~doc:"Compile a c0c source file." in
  match Term.eval (cmd_line_term, cmd_line_info) with
  | `Ok cmd_line -> run cmd_line
  | result -> Term.exit result
;;
