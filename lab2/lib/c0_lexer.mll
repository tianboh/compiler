{
(* L1 Compiler
 * Lexer
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Lexes forward compatible fragment of C0
 *
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Updated to match 2014 spec
 *
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 * Updated to use Core instead of Core.Std and ppx
 *
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Simplify calculation of source location for marking asts.
 *   - Fix eof-in-comment error.
 *   - Keep track of comment nesting level directly in lexer instead of in
 *     mutable state.
 *
 * Update this file to lex the necessary keywords and other tokens
 * in order to make the grammar forward compatible with C0.
 *)

open Core

module T = C0_parser (* Stands for "Token" *)

(* A record of all errors that happened. *)
let errors = Error_msg.create ()

let text = Lexing.lexeme

let from_lexbuf : Lexing.lexbuf -> Mark.src_span option =
  fun lexbuf ->
    Mark.of_positions
      (Lexing.lexeme_start_p lexbuf)
      (Lexing.lexeme_end_p lexbuf)
    |> Option.some

let error lexbuf ~msg : unit =
  let src_span = from_lexbuf lexbuf in
  Error_msg.error errors src_span ~msg

let dec_constant s lexbuf =
  let handle_int_min str =
    if String.equal str "2147483648"
      then "0x80000000"
      else str
  in
  let i32 =
    try Int32.of_string (handle_int_min s)
    with Failure _ ->
      let src_span = from_lexbuf lexbuf in
      Error_msg.error errors src_span
        ~msg:(sprintf "Cannot parse decimal constant `%s`" (text lexbuf));
      Int32.zero
  in
  T.Dec_const i32

let hex_constant s lexbuf =
  let i32 =
    try Int32.of_string s
    with Failure _ ->
      let src_span = from_lexbuf lexbuf in
      Error_msg.error errors src_span
        ~msg:(sprintf "Cannot parse hex constant `%s`" (text lexbuf));
      Int32.zero
  in
  T.Hex_const i32

}

let ident = ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*
let dec_num = ("0" | ['1'-'9'](['0'-'9']*))
let hex_num = "0"['x' 'X']['0'-'9' 'a'-'f' 'A'-'F']+

let ws = [' ' '\t' '\r' '\011' '\012']

rule initial = parse
  | ws+  { initial lexbuf }
  | '\n' { Lexing.new_line lexbuf;
           initial lexbuf
         }

  | '{' { T.L_brace }
  | '}' { T.R_brace }
  | '(' { T.L_paren }
  | ')' { T.R_paren }

  | ';' { T.Semicolon }

  | '='  { T.Assign }
  | "+=" { T.Plus_eq }
  | "-=" { T.Minus_eq }
  | "*=" { T.Star_eq }
  | "/=" { T.Slash_eq }
  | "%=" { T.Percent_eq }

  | '+' { T.Plus }
  | '-' { T.Minus }
  | '*' { T.Star }
  | '/' { T.Slash }
  | '%' { T.Percent }

  | "--" { T.Minus_minus } (* Illegal *)

  | "assert" { assert false }
  | "main"   { T.Main }
  | "return" { T.Return }

  | "bool"    { assert false }
  | "char"    { assert false }
  | "int"     { T.Int }
  | "void"    { assert false }
  | "struct"  { assert false }
  | "typedef" { assert false }

  | "if"    { assert false }
  | "else"  { assert false }
  | "while" { assert false }
  | "for"   { assert false }

  | "true"  { assert false }
  | "false" { assert false }

  | "NULL"        { assert false }
  | "alloc"       { assert false }
  | "alloc_array" { assert false }

  | "string"   { assert false }
  | "continue" { assert false }
  | "break"    { assert false }

  | dec_num as n { dec_constant n lexbuf }
  | hex_num as n { hex_constant n lexbuf }

  | ident as name { T.Ident (Symbol.symbol name) }

  | "/*" { comment 1 lexbuf }
  | "*/" { error lexbuf ~msg:"Unbalanced comments.";
           initial lexbuf
         }
  | "//" { comment_line lexbuf }

  | eof { T.Eof }

  | _  { error lexbuf
           ~msg:(sprintf "Illegal character '%s'" (text lexbuf));
         initial lexbuf
       }

and comment nesting = parse
  | "/*" { comment (nesting + 1) lexbuf }
  | "*/" { match nesting - 1 with
           | 0 -> initial lexbuf
           | nesting' -> comment nesting' lexbuf
         }
  | eof  { error lexbuf ~msg:"Reached EOF in comment.";
           T.Eof
         }
  | '\n' { Lexing.new_line lexbuf;
           comment nesting lexbuf
         }
  | _    { comment nesting lexbuf }

and comment_line = parse
  | '\n' { Lexing.new_line lexbuf;
           initial lexbuf
         }
  | eof  { error lexbuf ~msg:"Reached EOF in comment.";
           T.Eof
         }
  | _    { comment_line lexbuf }

{}
