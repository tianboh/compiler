%{
(* L2 Compiler
 * L2 grammar
 * Author: Tianbo Hao, Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
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
 *   - Improve presentation of marked Csts.
 *
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)
module Mark = Util.Mark
module Symbol = Util.Symbol

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
    | id, None, exp -> Cst.Assign {name = Mark.data id; value = exp}
    | id, Some op, exp ->
      let binop = Cst.Binop {
        op;
        lhs = Mark.map lhs ~f:(fun id -> Cst.Var id);
        rhs = exp;
      } in
      Cst.Assign {name = Mark.data id; value = mark binop start_pos end_pos}

%}

(* Variable name *)
%token <Util.Symbol.t> Ident
(* Data type  *) 
%token Int
%token Bool
(* Data type values *)
%token <Int32.t> Dec_const
%token <Int32.t> Hex_const
%token <Bool.t> Bool_const
(* Keywords *)
%token Main
%token Return
(* Special characters *)
%token L_brace R_brace
%token L_paren R_paren
%token Eof
%token Semicolon
%token Unary
(* Below are binary operators *) 
%token Plus Minus Star Slash Percent
%token Assign Plus_eq Minus_eq Star_eq Slash_eq Percent_eq
// %token Minus_minus Plus_plus
%token Logic_and Logic_or           (* Logic op: && || *)
%token Bit_and Bit_or Bit_xor       (* Bitwise op: & | ^ *)
(* Others *)
// %token <Int32.t> Dbg_line
// %token <Int32.t> Dbg_col

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
 *
 * The way we organize below types is based on the grammer
 * Check https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab2.pdf
 * Page 3 for more details.
 *
 *)
%type <Cst.block> program
%type <Cst.block> block
%type <Cst.dtype> dtype
%type <Cst.stms> stms
%type <Cst.stm> stm
%type <Cst.decl> decl
%type <Cst.stm> simp
%type <Symbol.t> lvalue
%type <Cst.exp> exp
%type <Core.Int32.t> int_const
%type <Core.Bool.t> bool_const
%type <Cst.binop option> asnop
%type <Cst.binop> binop
// %type <Cst.postop> postop

%%

program :
  | Int;
    Main;
    L_paren R_paren;
    block = block
    Eof;
      { block }
  ;

block : 
   | L_brace;
     body = stms;
     R_brace;
      { body }

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
  | block = block;
      { block }
  | hd = m(stm); tl = stms;
      { Cst.Concat{head = hd; tail = tl} }
  ;

stm :
  | d = decl; Semicolon;
      { Cst.Declare d }
  | s = simp; Semicolon;
      { s }
  | Return; e = m(exp); Semicolon;
      { Cst.Return e }
  ;

dtype : 
  | Int;
      { Cst.Int }
  | Bool;
      {Cst.Bool}

decl :
  | t = dtype; ident = Ident;
      { Cst.New_var { t = t; name = ident } }
  | t = dtype; ident = Ident; Assign; e = m(exp);
      { Cst.Init { t = t; name = ident; value = e } }
  | Int; Main;
      { Cst.New_var {t = Int; name = Symbol.symbol "main"} }
  | Int; Main; Assign; e = m(exp);
      { Cst.Init {t = Int; name = Symbol.symbol "main"; value = e} }
  ;

simp :
  | lhs = m(lvalue);
    op = asnop;
    rhs = m(exp);
      { expand_asnop ~lhs ~op ~rhs $startpos(lhs) $endpos(rhs) }
  // | lhs = m(lvalue)
  //   op = postop;
  //   { expand_}
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
      { Cst.Const_int c }
  | Main;
      { Cst.Var (Symbol.symbol "main") }
  | b = bool_const;
      { Cst.Const_bool b }
  | ident = Ident;
      { Cst.Var ident }
  | lhs = m(exp);
    op = binop;
    rhs = m(exp);
      { Cst.Binop { op; lhs; rhs; } }
  | Minus; e = m(exp); %prec Unary
      { Cst.Unop { op = Cst.Negative; operand = e; } }
  ;

int_const :
  | c = Dec_const;
      { c }
  | c = Hex_const;
      { c }
  ;

bool_const : 
  | b = Bool_const;
    { b }
  ;

(* See the menhir documentation for %inline.
 * This allows us to factor out binary operators while still
 * having the correct precedence for binary operator expressions.
 *)
%inline
binop :
  | Plus;
      { Cst.Plus }
  | Minus;
      { Cst.Minus }
  | Star;
      { Cst.Times }
  | Slash;
      { Cst.Divided_by }
  | Percent;
      { Cst.Modulo }
  | Logic_and;
      { Cst.Logic_and }
  | Logic_or;
      { Cst.Logic_or }
  | Bit_and;
      { Cst.Bit_and }
  | Bit_or;
      { Cst.Bit_or }
  | Bit_xor;
      { Cst.Bit_xor }
  ;

asnop :
  | Assign
      { None }
  | Plus_eq
      { Some Cst.Plus }
  | Minus_eq
      { Some Cst.Minus }
  | Star_eq
      { Some Cst.Times }
  | Slash_eq
      { Some Cst.Divided_by }
  | Percent_eq
      { Some Cst.Modulo }
  ;

%%
