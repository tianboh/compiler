(* L2 Compiler
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

(* open Json_reader *)
open Args
module AS_psu = Middle.Inst
module AS_x86 = Inst.X86
module Parse = Front.Parse
module Elab = Front.Elab
module Ast = Front.Ast
module Cst = Front.Cst
module Typechecker = Semantic.Typechecker
module Controlflow = Semantic.Controlflow
module Dfana = Flow.Dfana
module Tree = Middle.Tree
module Trans = Middle.Trans

(* Command line arguments *)

type cmd_line_args =
  { verbose : bool
  ; dump_parsing : bool
  ; dump_cst : bool
  ; dump_ast : bool
  ; dump_ir : bool
  ; dump_assem : bool
  ; semcheck_only : bool
  ; regalloc_only : bool
  ; emit : Emit.t
  ; opt_level : Opt_level.t
  ; df_type : Df_analysis.t
  ; filename : string
  }

(* A term (using the vocabulary of the Cmdliner library) that can be used to
 * parse command-line arguments. *)
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
  in
  { verbose
  ; dump_parsing
  ; dump_cst
  ; dump_ast
  ; dump_ir
  ; dump_assem
  ; semcheck_only
  ; regalloc_only
  ; emit
  ; opt_level
  ; df_type
  ; filename
  }
;;

let say_if (v : bool) (f : unit -> string) = if v then prerr_endline (f ())

(* The main driver for the compiler: runs each phase. *)
let compile (cmd : cmd_line_args) : unit =
  say_if cmd.verbose (fun () -> "Parsing... " ^ cmd.filename);
  if cmd.dump_parsing then ignore (Parsing.set_trace true : bool);
  (* Parse *)
  let cst = Parse.parse cmd.filename in
  say_if cmd.dump_cst (fun () -> Cst.Print.pp_program cst);
  (* Elaborate *)
  let ast = Elab.elaborate cst in
  say_if cmd.dump_ast (fun () -> Ast.Print.pp_program ast);
  (* Semantic analysis *)
  say_if cmd.verbose (fun () -> "Checking...");
  Typechecker.typecheck ast;
  Controlflow.cf_ret ast;
  Controlflow.cf_init ast;
  if cmd.semcheck_only then exit 0;
  (* Translate *)
  say_if cmd.verbose (fun () -> "Translating...");
  let ir = Trans.translate ast in
  let ir_ssa = Middle.Ssa.run ir in
  (* Okay, this is a hack, we will provide more comprehensive handling in lab3. 
   * TODO: fix it! *)
  say_if cmd.dump_ir (fun () -> Tree.Print.pp_stms ir_ssa);
  (* Codegen *)
  say_if cmd.verbose (fun () -> "Codegen...");
  (* let start = Unix.gettimeofday () in *)
  let assem_ps_ssa = Middle.Gen.gen ir in
  (* let assem_ps_ssa = Codegen.Optimize.optimize assem_ps_ssa in *)
  (* let () = Codegen.Gen.Pseudo.print_insts assem_ps_ssa in *)
  (* let stop = Unix.gettimeofday () in *)
  (* let () = Printf.printf "Execution time assem_ps_ssa: %fs\n%!" (stop -. start) in *)
  say_if cmd.dump_assem (fun () -> AS_psu.pp_program assem_ps_ssa "");
  match cmd.emit with
  (* Output: abstract 3-address assem *)
  | Abstract_assem ->
    let file = cmd.filename ^ ".abs" in
    say_if cmd.verbose (fun () -> sprintf "Writing abstract assem to %s..." file);
    File.dump_asm_ps file assem_ps_ssa
  | X86_64 ->
    let file = cmd.filename ^ ".s" in
    say_if cmd.verbose (fun () -> sprintf "Writing x86 assem to %s..." file);
    (* let start = Unix.gettimeofday () in *)
    (* let stop = Unix.gettimeofday () in *)
    (* let () = Printf.printf "Execution time gen_regalloc_info: %fs\n%!" (stop -. start) in *)
    (* let start = Unix.gettimeofday () in *)
    let assem_x86_conv = Convention.X86.gen assem_ps_ssa [] in
    let reg_alloc_info = Regalloc.Driver.regalloc assem_x86_conv in
    (* let stop = Unix.gettimeofday () in *)
    (* let () = Printf.printf "Execution time reg_alloc_info: %fs\n%!" (stop -. start) in *)
    let assem_x86 = Codegen.Gen.X86.gen assem_ps_ssa reg_alloc_info in
    File.dump_asm_x86 file assem_x86
;;

(* failwith "error" *)

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
