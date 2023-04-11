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

(* expand_postop (id, "postop") region = "id = id postop 1"
 * syntactically expands a compound post operator
 *)
let expand_postop lhs op 
  (start_pos : Lexing.position) =
    let op = match op with | Cst.Plus_plus -> Cst.Plus | Cst.Minus_minus -> Cst.Minus in
    match lhs, op with
    | id, op ->
      let binop = Cst.Binop {
        op;
        lhs = Mark.map lhs ~f:(fun id -> Cst.Var id);
        rhs = Mark.naked (Cst.Const_int Int32.one);
      } in
      Cst.Assign {name = Mark.data id; value = mark binop start_pos start_pos}


%}

(* Variable name *)
%token <Util.Symbol.t> Ident
(* Data type  *) 
%token Int
%token Bool
(* Data type values *)
%token <Int32.t> Dec_const
%token <Int32.t> Hex_const
%token True
%token False
(* Keywords *)
%token Main
%token If
%token Else
%token While
%token For
%token Return
(* Special characters *)
%token L_brace R_brace
%token L_paren R_paren
%token Eof
%token Semicolon
%token Unary
(* Binary operators *) 
%token Plus Minus Star Slash Percent Less Less_eq Greater Greater_eq Equal_eq Not_eq
        And_and Or_or And Or Left_shift Right_shift
(* postop *)
%token Minus_minus Plus_plus
(* unop *)
%token Excalmation_mark Dash_mark Hat
(* assign op *)
%token Assign Plus_eq Minus_eq Star_eq Slash_eq Percent_eq And_eq Or_eq Hat_eq Left_shift_eq Right_shift_eq
(* Ternary op *)
%token Question_mark Colon
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
%type <Cst.decl> decl
// %type <Cst.stms> stms
%type <Cst.stm> stm
%type <Cst.mstms> mstms
%type <Cst.simp> simp
%type <Symbol.t> lvalue
%type <Cst.control> control
%type <Cst.exp> exp
%type <Core.Int32.t> int_const
%type <Cst.binop option> asnop
%type <Cst.binop> binop
%type <Cst.unop> unop
%type <Cst.postop> postop

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
     body = mstms;
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
  | Bool; Main;
      { Cst.New_var {t = Bool; name = Symbol.symbol "main"} }
  | Bool; Main; Assign; e = m(exp);
      { Cst.Init {t = Bool; name = Symbol.symbol "main"; value = e} }
  ;

mstms :
  | (* empty *)
      { [] }
  | hd = m(stm); tl = mstms;
      { hd :: tl }
  ;

stm :
  | s = simp; Semicolon;
      { Cst.Simp s }
  | c = control;
      { Cst.Control c }
  | b = block;
      { Cst.Block b }

  ;

simp :
  | lhs = m(lvalue); op = asnop; rhs = m(exp);
      { expand_asnop ~lhs ~op ~rhs $startpos(lhs) $endpos(rhs) }
  | lhs = m(lvalue); op = postop;
      { expand_postop lhs op $startpos(lhs)}
  | d = decl; Semicolon;
      { Cst.Declare d }
  | e = m(exp);
      { Cst.Exp e }
  ;

lvalue :
  | ident = Ident;
      { ident }
  | Main;
      { Symbol.symbol "main" }
  | L_paren; lhs = lvalue; R_paren;
      { lhs }
  ;

control : 
  | If; L_paren; e = m(exp); R_paren; s = stm;
      { Cst.If {cond = e; s_t = s; s_f = None} }
  | If; L_paren; e = m(exp); R_paren; s_t = stm; Else; s_f = stm;
      { Cst.If {cond = e; s_t = s_t; s_f = Some s_f} }
  | While; L_paren; e = m(exp); R_paren; s = stm;
      { Cst.While {cond = e; body = s} }
  | For; L_paren; e = m(exp); s = stm;
      { Cst.For {init = None; cond = e; iter = None; body = s} }
  | For; L_paren; init = simp; e = m(exp); s = stm;
      { Cst.For {init = Some init; cond = e; iter = None; body = s} }
  | For; L_paren; e = m(exp); iter = simp; s = stm;
      { Cst.For {init = None; cond = e; iter = Some iter; body = s} }
  | For; L_paren; init = simp; e = m(exp); iter = simp; s = stm;
      { Cst.For {init = Some init; cond = e; iter = Some iter; body = s} }
  | Return; e = m(exp); Semicolon;
      { Cst.Return e }

exp :
  | L_paren; e = exp; R_paren;
      { e }
  | c = int_const;
      { Cst.Const_int c }
  | Main;
      { Cst.Var (Symbol.symbol "main") }
  | True;
      { Cst.True }
  | False;
      { Cst.False }
  | ident = Ident;
      { Cst.Var ident }
  | unop = unop; e = m(exp);
      { Cst.Unop {op = unop; operand = e} }
  | lhs = m(exp);
    op = binop;
    rhs = m(exp);
      { Cst.Binop { op; lhs; rhs; } }
  | Minus; e = m(exp); %prec Unary
      { Cst.Unop { op = Cst.Negative; operand = e; } }
  | cond = m(exp); Question_mark; true_exp = m(exp); Colon; false_exp = m(exp);
     { Cst.Ter {cond = cond; true_exp = true_exp; false_exp = false_exp} }
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
      { Cst.Plus }
  | Minus;
      { Cst.Minus }
  | Star;
      { Cst.Times }
  | Slash;
      { Cst.Divided_by }
  | Percent;
      { Cst.Modulo }
  | And_and;
      { Cst.And_and }
  | Or_or;
      { Cst.Or_or }
  | And;
      { Cst.And }
  | Or;
      { Cst.Or }
  | Hat;
      { Cst.Hat }
  ;

unop : 
  | Excalmation_mark
    { Cst.Excalmation_mark }
  | Dash_mark
    { Cst.Dash_mark }
  ;

postop : 
  | Plus_plus
    { Cst.Plus_plus }
  | Minus_minus
    { Cst.Minus_minus }
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
  | And_eq
      { Some Cst.And }
  | Hat_eq
      { Some Cst.Hat }
  | Or_eq
      { Some Cst.Or }
  | Left_shift_eq
      { Some Cst.Left_shift }
  | Right_shift_eq
      { Some Cst.Right_shift }
  ;

%%
