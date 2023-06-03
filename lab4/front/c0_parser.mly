%{
(* L3 Compiler
 * L3 grammar
 *
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
 *   - Improve presentation of marked Csts.
 *
 * Modified: Tianbo Hao  May 2023 
 *   - Provide L3 grammar.
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
    let op = match op with | Cst.Plus_plus -> Cst.Plus  | Cst.Minus_minus -> Cst.Minus in
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
%token Void
(* Data type values *)
%token <Int32.t> Dec_const
%token <Int32.t> Hex_const
%token True
%token False
(* Keywords *)
%token If
%token Else
%token While
%token For
%token Return
%token Typedef
%token Assert
(* Special characters *)
%token L_brace R_brace
%token L_paren R_paren
%token Eof
%token Semicolon
%token Comma
(* Binary operators *) 
%token Plus Minus Star Slash Percent Less Less_eq Greater Greater_eq Equal_eq Not_eq
        And_and Or_or And Or Left_shift Right_shift Hat (* bitwise exclusive or *)
(* postop *)
%token Minus_minus Plus_plus
(* unop *)
%token Excalmation_mark (* logical not *) Dash_mark (* bitwise not *) Negative (* This is a placeholder for minus *)
(* assign op *)
%token Assign Plus_eq Minus_eq Star_eq Slash_eq Percent_eq And_eq Or_eq Hat_eq Left_shift_eq Right_shift_eq
(* Ternary op *)
%token Question_mark Colon
(* Others *)
// %token <Int32.t> Dbg_line
// %token <Int32.t> Dbg_col

(* Negative is a dummy terminal.
 * We need dummy terminals if we wish to assign a precedence
 * to a production that does not correspond to the precedence of
 * the rightmost terminal in that production.
 * Implicit in this is that precedence can only be inferred for
 * terminals. Therefore, don't try to assign precedence to "rules"
 * or "productions".
 *
 * Minus_minus is a dummy terminal to parse-fail on.
 *)

(*
 * Operation declared before has lower precedence. Check 
 * https://www.cs.cmu.edu/afs/cs/academic/class/15411-f20/www/hw/lab3.pdf
 * for detailed operation precedence in L3 grammar.
 *)
%right Assign Plus_eq Minus_eq Star_eq Slash_eq Percent_eq And_eq Or_eq Hat_eq Left_shift_eq Right_shift_eq
%right Question_mark Colon
%left Or_or
%left And_and
%left Or
%left Hat
%left And
%left Equal_eq Not_eq
%left Less Less_eq Greater Greater_eq
%left Left_shift Right_shift
%left Plus Minus
%left Star Slash Percent
%right Negative Excalmation_mark Dash_mark Plus_plus Minus_minus

%start program

%type <Cst.program> program

%%

program :
  | Eof;
      { [] }
  | gdecl = gdecl; prog = program;
      { gdecl :: prog }
  ;

gdecl :
  | ret_type = dtype; fun_name = Ident; pars = param_list; Semicolon;
      { Cst.Fdecl {ret_type = ret_type; func_name = fun_name; par_type = pars} }
  | ret_type = dtype; fun_name = Ident; pars = param_list; blk = block;
      { Cst.Fdefn {ret_type = ret_type; func_name = fun_name; par_type = pars; blk = blk} }
  | Typedef; t = dtype; var = Ident; Semicolon
      { Cst.Typedef {t = t; t_var = var} }
  ;

param : 
  | t = dtype; var = Ident;
      { {t = t; i = var} : Cst.param }
  ;

param_list_follow:
  | 
      { [] }
  | Comma; par = param; pars = param_list_follow;
      { par :: pars }
  ;

param_list : 
  | L_paren; R_paren;
      { [] }
  | L_paren; par = param; pars = param_list_follow ; R_paren;
      { par :: pars }
  ;

block : 
   | L_brace;
     body = mstms;
     R_brace;
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

dtype : 
  | Int;
      { Cst.Int }
  | Bool;
      { Cst.Bool }
  | Void;
      { Cst.Void }
  | ident = Ident;
      { Cst.Ctype ident }

decl :
  | t = dtype; ident = Ident;
      { Cst.New_var { t = t; name = ident } }
  | t = dtype; ident = Ident; Assign; e = m(exp);
      { Cst.Init { t = t; name = ident; value = e } }
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
  | d = decl;
      { Cst.Declare d }
  | e = m(exp);
      { Cst.Sexp e }
  ;

lvalue :
  | ident = Ident;
      { ident }
  | L_paren; lhs = lvalue; R_paren;
      { lhs }
  ;

simpopt : 
  |
      { None }
  | simp_ = m(simp);
      { Some simp_ }

elseopt : 
  | 
      { None }
  | Else; else_ = m(stm);
      { Some else_ }

control : 
  | If; L_paren; e = m(exp); R_paren; true_stm = m(stm); false_stm = elseopt;
      { Cst.If {cond = e; true_stm = true_stm; false_stm = false_stm} }
  | While; L_paren; e = m(exp); R_paren; s = m(stm);
      { Cst.While {cond = e; body = s} }
  | For; L_paren; init = simpopt; Semicolon; e = m(exp); Semicolon; iter = simpopt; R_paren; s = m(stm);
         { Cst.For {init = init; cond = e; iter = iter; body = s} }
  | Return; e = expopt; Semicolon;
      { Cst.Return e }
  | Assert; L_paren; e = m(exp); R_paren; Semicolon;
      { Cst.Assert e }

exp :
  | L_paren; e = exp; R_paren;
    { e }
  | c = int_const;
    { Cst.Const_int c }
  | True;
    { Cst.True }
  | False;
    { Cst.False }
  | ident = lvalue; 
    { Cst.Var ident }
  | unop = unop; e = m(exp);
    { Cst.Unop {op = unop; operand = e} }
  | lhs = m(exp);
    op = binop;
    rhs = m(exp);
    { Cst.Binop { op; lhs; rhs; } }
  | Minus; e = m(exp); %prec Negative
    { Cst.Unop { op = Cst.Negative; operand = e; } }
  | Excalmation_mark; e = m(exp); %prec Excalmation_mark
    { Cst.Unop {op = Cst.Excalmation_mark; operand = e; } }
  | Dash_mark; e = m(exp); %prec Dash_mark
    { Cst.Unop {op = Cst.Dash_mark; operand = e; } }
  | cond = m(exp); Question_mark; true_exp = m(exp); Colon; false_exp = m(exp);
    { Cst.Terop {cond = cond; true_exp = true_exp; false_exp = false_exp} }
  | fname = Ident; arg_list = arg_list;
    { Cst.Fcall {func_name = fname; args = arg_list} }
  ;

arg_list : 
  | L_paren; R_paren;
    { [] }
  | L_paren; e = m(exp); arg_list_follow = arg_list_follow ; R_paren;
    { e :: arg_list_follow }

arg_list_follow : 
  |
      { [] }
  | Comma; e = m(exp); arg_list_follow = arg_list_follow;
      { e :: arg_list_follow }
  
expopt :
  | 
    { None }
  | e = m(exp)
    { Some e }

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
  | Less
    { Cst.Less }
  | Less_eq
    { Cst.Less_eq }
  | Greater
    { Cst.Greater }
  | Greater_eq
    { Cst.Greater_eq }
  | Equal_eq
    { Cst.Equal_eq }
  | Not_eq
    { Cst.Not_eq }
  | Left_shift
    { Cst.Left_shift }
  | Right_shift
    { Cst.Right_shift }
  | Hat
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