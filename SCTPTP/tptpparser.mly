
%{
  open Tptpast
%}

(* EOF *)
%token EOF
  
(* delimiters *) 
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE COMMA DOT COLON
  
(* operators *) 
%token PLUS TIMES DIVIDE MINUS
  
(* operators: logical *)
%token AND OR NOT BANG QUESTION HASH IFF IMPLIES IMPLIEDBY NIFF NOR NAND GENTZEN_ARROW

(* equality *)
%token EQUAL NOTEQUAL

(* keywords *)
%token FOF INFERENCE INTRODUCED FILE THEORY CREATOR UNKNOWN
%token DOLLAR_FOF DOLLAR_FOT

(* numerics *)
%token <int> NAT
%token <float> FLOAT

(* identifiers *)
%token <string> DOLLAR_DOLLAR_WORD DOLLAR_WORD SINGLE_QUOTED DOUBLE_QUOTED LOWER_WORD UPPER_WORD

%start tptp_file
%type <annotated_formula list> tptp_file

%%

tptp_file:
  | fs = annotated_formula* EOF { fs }

annotated_formula:
  | f = fof_annotated_formula { f }

fof_annotated_formula:
  | FOF LPAREN name = name COMMA role = role COMMA formula = fof_sequent annotations = annotations RPAREN DOT {
    Fof { name = name; role = role; formula = formula; annotations = annotations }
  }

name: (* TODO: allow integer names *)
  | s = atomic_word { s }

role:
  | s = atomic_word { s }

(* annotation crap *)

annotations:
  | a = annotation? { a }

annotation:
  | COMMA s = source info = optional_info { (s, info) }

(* SOURCES *)

source:
  | UNKNOWN { Unknown }
  | s = dag_source { s }
  | s = internal_source { s }
  | s = external_source { s }
  (* \[ source [, source]* \] *)
  | ss = comma_nonempty_blist(source) { Sourcelist ss }

dag_source:
  | n = name { Named n }
  | i = inference_record { i }

internal_source:
  | INTRODUCED LPAREN itype = atomic_word COMMA info = useful_info COMMA parents = parents RPAREN {
    Introduced (itype, info, parents)
  }

external_source:
  | s = file_source     { s }
  | s = theory          { s }
  | s = creator_source  { s }

inference_record:
  | INFERENCE LPAREN rule = atomic_word COMMA info = useful_info COMMA parents = parents RPAREN {
    Inference (rule, info, parents)
  }

file_source:
  | FILE LPAREN file_name = atomic_word name = option(preceded(COMMA, name)) RPAREN {
    File (file_name, name)
  }

theory:
  | THEORY LPAREN name = atomic_word info = optional_info RPAREN {
    Theory (name, info)
  }

creator_source:
  | CREATOR LPAREN cname = atomic_word COMMA info = useful_info COMMA parents = parents RPAREN {
    Creator (cname, info, parents)
  }

(* ANNOTATED INFO *)

optional_info:
  | is = loption(preceded(COMMA, useful_info)) { is }

useful_info:
  | l = general_list { l }
  | t = general_term { [t] } (* TODO: non-standard. complain? *)

general_list:
  | ls = delimited(LBRACKET, general_terms, RBRACKET) { ls }

general_terms:
  | ls = separated_list(COMMA, general_term) { ls }

general_term:
  | d = general_data t = option(preceded(COLON, general_term)) { Data (d, t) }
  | ls = general_list { Listterm ls }

general_data:
  | s = atomic_word { String s }
  | f = general_function { f }
  | v = variable { Var v }
  | n = number { Num n }
  | d = distinct_object { Distinctobject d }
  | f = formula_data { f }

general_function:
  | func = atomic_word args = delimited(LPAREN, general_terms, RPAREN) {
    Metafunction (func, args)
  }

formula_data:
  | DOLLAR_FOF f = delimited(LPAREN, fof_formula, RPAREN) { Fof f }
  | DOLLAR_FOT t = delimited(LPAREN, fof_term, RPAREN)    { Fot t }

(* PARENTS / REFERENCES *)

parents:
  | ps = comma_blist(parent_info) { ps }

parent_info:
  | s = source ls = loption(preceded(COLON, general_list)) { Parent (s, ls) }

(* LOGICAL FORMULAS *)

fof_formula:
  (* the cases are shifted to fof_sequent for convenience *)
  | sq = fof_sequent { sq }

fof_sequent:
  | LPAREN sq = fof_sequent RPAREN { sq } 
  | LBRACKET ans = fof_formula_list RBRACKET 
      GENTZEN_ARROW 
    LBRACKET cqs = fof_formula_list RBRACKET {
    Sequent(ans, cqs)
  }
  | f = fof_logic_formula { Sequent([], [f]) }

fof_formula_list:
  | fs = separated_list (COMMA, fof_logic_formula) { fs }

(* all fo formulas *)
fof_logic_formula:
  | f = fof_unary_formula   { f }
  | f = fof_unitary_formula { f }
  | f = fof_binary_formula  { f }

fof_unit_formula:
  | f = fof_unitary_formula { f }
  | f = fof_unary_formula  { f }

fof_binary_formula:
  | f = fof_binary_assoc    { f }
  | f = fof_binary_nonassoc { f }

fof_binary_assoc:
  (* f1 & f2 [ & fn]* *)
  | f = fof_and_formula { f }
  (* f1 | f2 [ | fn]* *)
  | f = fof_or_formula { f }

fof_and_formula:
  | l = fof_unit_formula AND r = fof_unit_formula { And (l, r) }
  | ls = fof_and_formula AND r = fof_unit_formula { And (ls, r) }

fof_or_formula:
  | l = fof_unit_formula OR r = fof_unit_formula { Or (l, r) }
  | ls = fof_or_formula  OR r = fof_unit_formula { Or (ls, r) }

fof_binary_nonassoc:
  | l = fof_unit_formula c = nonassoc_connective r = fof_unit_formula {
    c l r
  }

nonassoc_connective:
  | IFF { fun l r -> Iff (l, r) }
  | IMPLIES { fun l r -> Implies (l, r) }
  | IMPLIEDBY { fun l r -> Implies (r, l) }
  | NIFF { fun l r -> Not (Iff (l, r)) }
  | NOR { fun l r -> Not (Or (l, r)) }
  | NAND { fun l r -> Not (And (l, r)) }

fof_unary_formula:
  | NOT f = fof_unit_formula { Not f }
  | f = fof_infix_unary {f}

(* why is this defined in a completely different path from real equality? sigh *)
fof_infix_unary:
  | l = fof_term NOTEQUAL r = fof_term { Not (Equal (l, r)) }

fof_unitary_formula:
  | LPAREN f = fof_logic_formula RPAREN { f }
  | f = fof_quantified_formula { f }
  | f = fof_atomic_formula { f }
  | v = UPPER_WORD { Fvar v }

fof_quantified_formula:
  | q = quantifier 
    vs = comma_nonempty_blist(variable)
    COLON body = fof_unit_formula {
      q vs body
    }

quantifier:
  | BANG { fun vs body -> Forall (vs, body) }
  | QUESTION { fun vs body -> Exist (vs, body) }

fof_atomic_formula:
  | f = fof_plain_atomic_formula    { f }
  | f = fof_defined_atomic_formula  { f }
  | f = fof_system_atomic_formula   { f }

fof_plain_atomic_formula:
  | t = fof_plain_term { t }

fof_defined_atomic_formula:
  | f = fof_defined_plain_formula { f }
  | f = fof_defined_infix_formula { f }

fof_defined_plain_formula:
  | t = fof_defined_plain_term { t }

fof_defined_infix_formula:
  | l = fof_term EQUAL r = fof_term { Equal (l, r) }

fof_system_atomic_formula:
  | t = fof_system_term { t }

(* TERMS *)

fof_term:
  | t = fof_function_term { t }
  | v = variable { v }
  | e = sc_epsilon_term { e }

sc_epsilon_term:
  | HASH vs = comma_nonempty_blist(variable) COLON LPAREN body = fof_unit_formula RPAREN { Epsilon (vs, body) }

fof_function_term:
  | t = fof_plain_term    { t }
  | t = fof_defined_term  { t }
  | t = fof_system_term   { t }

fof_plain_term:
  | c = constant { c }
  | f = ffunctor LPAREN args = fof_arguments RPAREN {
    Functorapplication (f, args)
  }

constant:
  | s = atomic_word { Constant s }

ffunctor:
  | s = atomic_word { Functor s }
  | v = UPPER_WORD { Vfunctor v }

fof_defined_term:
  | t = defined_term { t }
  | t = fof_defined_atomic_term { t }

defined_term:
  | n = number  { n }
  | o = distinct_object { o }

fof_defined_atomic_term:
  | t = fof_defined_plain_term { t }

fof_defined_plain_term:
  | c = defined_constant { c }
  | f = defined_ffunctor LPAREN args = fof_arguments RPAREN {
    Functorapplication (f, args)
  }

defined_constant:
  | s = atomic_defined_word { Definedconstant s }

defined_ffunctor:
  | s = atomic_defined_word { Definedfunctor s }

fof_system_term:
  | c = system_constant { c }
  | f = system_ffunctor LPAREN args = fof_arguments RPAREN {
    Functorapplication (f, args)
  }

system_constant:
  | s = atomic_system_word { Systemconstant s }

system_ffunctor:
  | s = atomic_system_word { Systemfunctor s }

fof_arguments:
  | ts = separated_nonempty_list(COMMA, fof_term) { ts }

variable:
  | name = UPPER_WORD { Var name }

distinct_object:
  | s = DOUBLE_QUOTED { Distinctobject s }

number: (* TODO: improve, check for signs *)
  | i = NAT { Integer i }
  | f = FLOAT { Float f }

atomic_word:
  | s = LOWER_WORD { s }
  | s = SINGLE_QUOTED { s }

atomic_defined_word:
  | s = DOLLAR_WORD { s }

atomic_system_word:
  | s = DOLLAR_DOLLAR_WORD { s }

(* helpers *)
%inline
blist(X):
  | xs = delimited(LBRACKET, X, RBRACKET) { xs }

%inline
comma_blist(X):
  | xs = blist(separated_list(COMMA, X)) { xs }

%inline
comma_nonempty_blist(X):
  | xs = blist(separated_nonempty_list(COMMA, X)) { xs }