%{
(* The 'intermediate' type expression. *)
type ityp =
  | ITyFun of { arg: ityp; argname: string option; optional: bool; retty: ityp }
  | ITyApp of { args: ityp list; destty: ityp } (* string list, or (int, int) func *)
  | ITyTuple of ityp list
  | ITyConst of string
  | ITyParen of ityp

let rec postprocess (ity:ityp): OcamlTypes.typ =
  match ity with
  | ITyFun x -> OcamlTypes.TyFun {
      arg = postprocess x.arg;
      argname = x.argname;
      optional = x.optional;
      retty = postprocess x.retty
    }
  | ITyApp x -> OcamlTypes.TyApp {
      args = List.map postprocess x.args;
      destty = postprocess x.destty
    }
  | ITyTuple tys -> OcamlTypes.TyTuple (List.map postprocess tys)
  | ITyConst s -> OcamlTypes.TyConst s
  | ITyParen t -> postprocess t
%}

%token <string> TYPEVAR IDENT
%token ARROW LPAREN RPAREN STAR COMMA COLON QUESTION_MARK EOF

%start typ_expr
%type <OcamlTypes.typ> typ_expr

%right ARROW
%left STAR
%left COMMA
%%

typ_expr:
  | typ EOF { postprocess $1 }

(* a -> b -> ... *)
typ:
  | typ_tuple { $1 }
  | typ ARROW typ { ITyFun { arg = $1 ; argname = None; optional = false; retty = $3 } }
  | IDENT COLON typ ARROW typ {
    ITyFun { arg = $3; argname = Some $1; optional = false; retty = $5 }
  }
  | QUESTION_MARK IDENT COLON typ ARROW typ {
    ITyFun { arg = $4; argname = Some $2; optional = true; retty = $6 }
  }

(* a * b * ... *)
typ_tuple:
  | typ_app STAR typ_tuple {
    match $3 with
    | ITyTuple ls -> ITyTuple ($1::ls)
    | _ -> ITyTuple [$1;$3]
  }
  | typ_app { $1 }

(* a b ... *)
typ_app:
  | typ_atom typ_app { ITyApp { args = [$1]; destty = $2 } }
  | LPAREN typ_args RPAREN typ_app { ITyApp { args = $2; destty = $4 } }
  | typ_atom { $1 }

(* a, b, ... *)
typ_args:
  | typ COMMA typ_args { $1 :: $3 }
  | typ { [$1] }

typ_atom:
  | TYPEVAR { ITyConst $1 }
  | IDENT { ITyConst $1 }
  | LPAREN typ RPAREN { ITyParen $2 }

%%
