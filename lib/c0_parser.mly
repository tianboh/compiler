%{
(* L1 Compiler
 * L1 grammar
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Now conforms to the L1 fragment of C0
 *
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Should be more up-to-date with 2014 spec
 *
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 *   - Update to use Core instead of Core.Std and ppx
 *
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Update to use menhir instead of ocamlyacc.
 *   - Improve presentation of marked asts.
 *
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)

let mark
  (data : 'a)
  (start_pos : Lexing.position)
  (end_pos : Lexing.position) : 'a Mark.t =
  let src_span = Mark.of_positions start_pos end_pos in
  Mark.mark data src_span

(* expand_asnop (id, "op=", exp) region = "id = id op exps"
 * or = "id = exp" if asnop is "="
 * syntactically expands a compound assignment operator
 *)
let expand_asnop ~lhs ~op ~rhs
  (start_pos : Lexing.position)
  (end_pos : Lexing.position) =
    match lhs, op, rhs with
    | id, None, exp -> Ast.Assign (Mark.data id, exp)
    | id, Some op, exp ->
      let binop = Ast.Binop {
        op;
        lhs = Mark.map lhs ~f:(fun id -> Ast.Var id);
        rhs = exp;
      } in
      Ast.Assign (Mark.data id, mark binop start_pos end_pos)

%}

%token Eof
%token Semicolon
%token <Int32.t> Dec_const
%token <Int32.t> Hex_const
%token <Symbol.t> Ident
%token Return
%token Int
%token Main
%token Plus Minus Star Slash Percent
%token Assign Plus_eq Minus_eq Star_eq Slash_eq Percent_eq
%token L_brace R_brace
%token L_paren R_paren
%token Unary
%token Minus_minus 

(* Unary is a dummy terminal.
 * We need dummy terminals if we wish to assign a precedence
 * to a production that does not correspond to the precedence of
 * the rightmost terminal in that production.
 * Implicit in this is that precedence can only be inferred for
 * terminals. Therefore, don't try to assign precedence to "rules"
 * or "productions".
 *
 * Minus_minus is a dummy terminal to parse-fail on.
 *)

%left Plus Minus
%left Star Slash Percent
%right Unary

%start program

(* It's only necessary to provide the type of the start rule,
 * but it can improve the quality of parser type errors to annotate
 * the types of other rules.
 *)
%type <Ast.mstm list> program
%type <Ast.mstm list> stms
%type <Ast.stm> stm
%type <Ast.mstm> m(stm)
%type <Ast.decl> decl
%type <Ast.stm> simp
%type <Symbol.t> lvalue
%type <Symbol.t Mark.t> m(lvalue)
%type <Ast.exp> exp
%type <Ast.mexp> m(exp)
%type <Core.Int32.t> int_const
%type <Ast.binop> binop
%type <Ast.binop option> asnop

%%

program :
  | Int;
    Main;
    L_paren R_paren;
    L_brace;
    body = stms;
    R_brace;
    Eof;
      { body }
  ;

(* This higher-order rule produces a marked result of whatever the
 * rule passed as argument will produce.
 *)
m(x) :
  | x = x;
      (* $startpos(s) and $endpos(s) are menhir's replacements for
       * Parsing.symbol_start_pos and Parsing.symbol_end_pos, but,
       * unfortunately, they can only be called from productions. *)
      { mark x $startpos(x) $endpos(x) }
  ;

stms :
  | (* empty *)
      { [] }
  | hd = m(stm); tl = stms;
      { hd :: tl }
  | L_brace; body = stms; R_brace;
      { body }
  ;

stm :
  | d = decl; Semicolon;
      { Ast.Declare d }
  | s = simp; Semicolon;
      { s }
  | Return; e = m(exp); Semicolon;
      { Ast.Return e }
  ;

decl :
  | Int; ident = Ident;
      { Ast.New_var ident }
  | Int; ident = Ident; Assign; e = m(exp);
      { Ast.Init (ident, e) }
  | Int; Main;
      { Ast.New_var (Symbol.symbol "main") }
  | Int; Main; Assign; e = m(exp);
      { Ast.Init (Symbol.symbol "main", e) }
  ;

simp :
  | lhs = m(lvalue);
    op = asnop;
    rhs = m(exp);
      { expand_asnop ~lhs ~op ~rhs $startpos(lhs) $endpos(rhs) }
  ;

lvalue :
  | ident = Ident;
      { ident }
  | Main;
      { Symbol.symbol "main" }
  | L_paren; lhs = lvalue; R_paren;
      { lhs }
  ;

exp :
  | L_paren; e = exp; R_paren;
      { e }
  | c = int_const;
      { Ast.Const c }
  | Main;
      { Ast.Var (Symbol.symbol "main") }
  | ident = Ident;
      { Ast.Var ident }
  | lhs = m(exp);
    op = binop;
    rhs = m(exp);
      { Ast.Binop { op; lhs; rhs; } }
  | Minus; e = m(exp); %prec Unary
      { Ast.Unop { op = Ast.Negative; operand = e; } }
  ;

int_const :
  | c = Dec_const;
      { c }
  | c = Hex_const;
      { c }
  ;

(* See the menhir documentation for %inline.
 * This allows us to factor out binary operators while still
 * having the correct precedence for binary operator expressions.
 *)
%inline
binop :
  | Plus;
      { Ast.Plus }
  | Minus;
      { Ast.Minus }
  | Star;
      { Ast.Times }
  | Slash;
      { Ast.Divided_by }
  | Percent;
      { Ast.Modulo }
  ;

asnop :
  | Assign
      { None }
  | Plus_eq
      { Some Ast.Plus }
  | Minus_eq
      { Some Ast.Minus }
  | Star_eq
      { Some Ast.Times }
  | Slash_eq
      { Some Ast.Divided_by }
  | Percent_eq
      { Some Ast.Modulo }
  ;

%%
