(* L1 Compiler
 * Parsing
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Gluing together the pieces produced by ocamllex and ocamlyacc
 *)

(* parse filename = ast
 * will raise ErrorMsg.Error in case of lexing or parsing error
 *)

open Core

(* In order for the lexbuf to correctly track source locations
 * we have to initialize the filename in the positions tracked by
 * the lexbuf.
 *)
let initialize_lexbuf (filename : string) : Lexing.lexbuf -> unit =
  let open Lexing in
  let pos = { pos_fname = filename; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 } in
  fun lexbuf ->
    lexbuf.lex_start_p <- pos;
    lexbuf.lex_curr_p <- pos
;;

let parse (filename : string) : Ast.program =
  try
    let ast =
      In_channel.with_file filename ~f:(fun chan ->
          let lexbuf = Lexing.from_channel chan in
          initialize_lexbuf filename lexbuf;
          try C0_parser.program C0_lexer.initial lexbuf with
          | _ ->
            (* Parse error; attempt to print a helpful error message. *)
            let src_span =
              Mark.of_positions Lexing.(lexbuf.lex_start_p) Lexing.(lexbuf.lex_curr_p)
            in
            Error_msg.error C0_lexer.errors (Some src_span) ~msg:"Parse error.";
            raise Error_msg.Error)
    in
    if Error_msg.has_any_errors C0_lexer.errors
    then (
      Out_channel.prerr_endline "Lex error.";
      raise Error_msg.Error)
    else ast
  with
  | Sys_error s ->
    (* Probably file not found or permissions errors. *)
    Out_channel.prerr_endline ("System error: " ^ s);
    raise Error_msg.Error
;;

(* Example expect test -- see README *)
let%expect_test "Test parsing of an empty program" =
  let lexbuf =
    Lexing.from_string "int main() {int x = 3; int y = -x + 4; return x + y * x / 3; }"
  in
  let program = C0_parser.program C0_lexer.initial lexbuf in
  print_endline (Ast.Print.pp_program program);
  [%expect
    {|
    {
    int x = 3;
    int y = (-(x) + 4);
    return (x + ((y * x) / 3));
    }
  |}]
;;
