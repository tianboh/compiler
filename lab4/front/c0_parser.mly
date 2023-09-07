%{
(* L4 Compiler
 * L4 grammar
 *
 * Reference: http://gallium.inria.fr/~fpottier/menhir/manual.pdf
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
 * Modified: Tianbo Hao  June 2023 
 *   - Provide L4 grammar.
 *   - Provide context dependent parser based on a smart lexer
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

%}

(* Variable name *)
%token <Util.Symbol.t> VIdent
%token <Util.Symbol.t> TIdent
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
%token Struct
%token Alloc
%token Alloc_array
(* Special characters *)
%token L_brace R_brace
%token L_paren R_paren
%token L_bracket R_bracket
%token Eof
%token Semicolon
%token Comma
%token Dot
%token Arrow
%token NULL
(* Binary operators *) 
%token Plus Minus Star Slash Percent Less Less_eq Greater Greater_eq Equal_eq Not_eq
        And_and Or_or And Or Left_shift Right_shift Hat (* bitwise exclusive or *)
(* postop *)
%token Minus_minus Plus_plus
(* unop *)
%token Excalmation_mark (* logical not *) Dash_mark (* bitwise not *) 
(* assign op *)
%token Assign Plus_eq Minus_eq Star_eq Slash_eq Percent_eq And_eq Or_eq Hat_eq Left_shift_eq Right_shift_eq
(* Ternary op *)
%token Question_mark Colon
(* Dummy token *)
%token Deref Explicit_parenthesis Arr_sub Negative

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
%right Negative Deref Excalmation_mark Dash_mark Plus_plus Minus_minus
%nonassoc Explicit_parenthesis Arr_sub L_bracket R_bracket Arrow Dot 
(* Else shift-reduce conflict solution reference
 * https://stackoverflow.com/questions/12731922/reforming-the-grammar-to-remove-shift-reduce-conflict-in-if-then-else*)
%right Else None 
%nonassoc Side_eff
%nonassoc LHS
%start program

%type <Cst.program> program

%%

id_or_type : 
  | vid = VIdent;
      { vid }
  | tid = TIdent;
      { tid }

program :
  | Eof;
      { [] }
  | gdecl = gdecl; prog = program;
      { gdecl :: prog }

gdecl :
  | ret_type = dtype; func_name = VIdent; pars = param_list; Semicolon;
      { if !Env.is_header 
        then Cst.Fdecl {ret_type = ret_type; func_name; par_type = pars; scope=`External}
        else Cst.Fdecl {ret_type = ret_type; func_name; par_type = pars; scope=`C0} }
  | ret_type = dtype; func_name = VIdent; pars = param_list; blk = block;
      { if !Env.is_header 
        then Cst.Fdefn {ret_type = ret_type; func_name; par_type = pars; blk = blk; scope=`External} 
        else Cst.Fdefn {ret_type = ret_type; func_name; par_type = pars; blk = blk; scope=`C0} }
  | Typedef; t = dtype; var = midrule(var = VIdent {Env.add_type var; var}); Semicolon
      { Cst.Typedef {t = t; t_var = var} }
  | Struct; var = VIdent; Semicolon
      { Cst.Sdecl { struct_name = var } }
  | Struct; var = VIdent; L_brace; fields = field_list; R_brace;  Semicolon
      { Cst.Sdefn { struct_name = var; fields = fields; } }

field : 
  | t = dtype; var = id_or_type; Semicolon
      { {t = t; i = var} : Cst.field }

field_list :
  | 
      { [] }
  |  field = field; fields = field_list
      { field :: fields }

param : 
  | t = dtype; var = VIdent;
      { {t = t; i = var} : Cst.param }

param_list_follow:
  | 
      { [] }
  | Comma; par = param; pars = param_list_follow;
      { par :: pars }

param_list : 
  | L_paren; R_paren;
      { [] }
  | L_paren; par = param; pars = param_list_follow ; R_paren;
      { par :: pars }

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

dtype : 
  | Int;
      { `Int }
  | Bool;
      { `Bool }
  | Void;
      { `Void }
  | ident = TIdent;
      { `Ctype ident }
  | t = dtype; Star;
      { `Pointer t }
  | t = dtype; L_bracket; R_bracket
      { `Array t }
  | Struct; var = id_or_type;
      { `Struct var }
      

decl :
  | t = dtype; ident = VIdent;
      { Cst.New_var { t = t; name = ident } }
  | t = dtype; ident = VIdent; Assign; e = m(exp);
      { Cst.Init { t = t; name = ident; value = e } }

mstms :
  | (* empty *)
      { [] }
  | hd = m(stm); tl = mstms;
      { hd :: tl }

stm :
  | s = simp; Semicolon;
      { Cst.Simp s }
  | c = control;
      { Cst.Control c }
  | b = block;
      { Cst.Block b }

simp :
  | lhs = m(exp); op = asnop; rhs = m(exp); 
      { Cst.Assign { name = lhs; value = rhs; op = op } }
  | lhs = m(exp); op = postop;
      { let rhs = Mark.naked (Cst.Const_int Int32.one) in
        match op with 
        | Cst.Plus_plus -> Cst.Assign { name = lhs; op = Cst.Plus_asn; value = rhs}
        | Cst.Minus_minus -> Cst.Assign { name = lhs; op = Cst.Minus_asn; value = rhs } }
  | d = decl;
      { Cst.Declare d }
  | e = m(exp); 
      { Cst.Sexp e }

simpopt : 
  |
      { None }
  | simp_ = m(simp);
      { Some simp_ }

elseopt : 
  | %prec None
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
  | ident = VIdent; 
    { Cst.Var ident }
  | NULL;
    { Cst.NULL }
  | Minus; e = m(exp); %prec Negative
    { Cst.Unop {op = Cst.Negative; operand = e} }
  | Excalmation_mark; e = m(exp); %prec Excalmation_mark
    { Cst.Unop {op = Cst.Excalmation_mark; operand = e} }
  | Dash_mark; e = m(exp); %prec Dash_mark
    { Cst.Unop {op = Cst.Dash_mark; operand = e} }
  | lhs = m(exp); op = binop; rhs = m(exp);
    { Cst.Binop { op; lhs; rhs; } }
  | cond = m(exp); Question_mark; true_exp = m(exp); Colon; false_exp = m(exp);
    { Cst.Terop {cond = cond; true_exp = true_exp; false_exp = false_exp} }
  | fname = VIdent; arg_list = arg_list;
    { Cst.Fcall {func_name = fname; args = arg_list} }
  | struct_obj = m(exp); Dot; ident = VIdent; 
      { Cst.Dot { struct_obj = struct_obj; field = ident } }
  | ptr = m(exp); Arrow; ident = id_or_type; 
      { Cst.Arrow { struct_ptr = ptr; field = ident } }
  | Alloc; L_paren; t = dtype; R_paren;
      { Cst.Alloc {t = t} }
  | Star; lv = m(exp); 
      { Cst.Deref {ptr = lv} }
  | Alloc_array; L_paren; t = dtype; Comma; e = m(exp); R_paren;
      { Cst.Alloc_arr {t = t; e = e} }
  | arr = m(exp); L_bracket; e = m(exp); R_bracket; 
      { Cst.Nth { arr = arr; index = e } }

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

postop : 
  | Plus_plus
    { Cst.Plus_plus }
  | Minus_minus
    { Cst.Minus_minus }
  ;

asnop :
  | Assign
      { Cst.Asn }
  | Plus_eq
      { Cst.Plus_asn }
  | Minus_eq
      { Cst.Minus_asn }
  | Star_eq
      { Cst.Times_asn }
  | Slash_eq
      { Cst.Div_asn }
  | Percent_eq
      { Cst.Mod_asn }
  | And_eq
      { Cst.And_asn }
  | Hat_eq
      { Cst.Hat_asn }
  | Or_eq
      { Cst.Or_asn }
  | Left_shift_eq
      { Cst.Left_shift_asn }
  | Right_shift_eq
      { Cst.Right_shift_asn }
  ;

%%