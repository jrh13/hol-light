type general_term =
  | Data of general_data * (general_term option)
  | Listterm of general_term list

and general_data =
  | String of string
  | Var of tptp_term
  | Num of tptp_term
  | Metafunction of string * (general_term list)
  | Distinctobject of tptp_term
  (* formula data *)
  | Fof of sequent (* can be formula or sequent, so generalize *)
  | Fot of tptp_term

and parent =
  | Parent of source * (general_term list)

and source =
  | Unknown
  | Named of string
  | Inference of string * (general_term list) * (parent list)
  | Introduced of string * (general_term list) * (parent list)
  | File of string * (string option)
  | Theory of string * (general_term list)
  | Creator of string * (general_term list) * (parent list)
  | Sourcelist of (source list)

and func =
  | Definedfunctor of string
  | Systemfunctor of string
  | Functor of string
  | Vfunctor of string

and tptp_term =
  | Var of string
  | Const of string
  | Fun of string * tptp_term list
  | Integer of int
  | Float of float
  | Constant of string
  | Definedconstant of string
  | Systemconstant of string
  | Distinctobject of string
  | Functorapplication of func * (tptp_term list)
  | Fvar of string
  | Not of tptp_term
  | And of tptp_term * tptp_term
  | Or of tptp_term * tptp_term
  | Implies of tptp_term * tptp_term
  | Iff of tptp_term * tptp_term
  | Forall of (tptp_term list) * tptp_term
  | Exist of (tptp_term list) * tptp_term
  | Epsilon of (tptp_term list) * tptp_term
  | Equal of tptp_term * tptp_term

(* A sequent is a pair of lists of formulas:
   the antecedents and the succedents. *)
and sequent =
  | Sequent of tptp_term list * tptp_term list

(* The top-level step (FOF) has a name, a role, a sequent as formula,
   and a (possibly empty) list of parent annotations. *)
and annotated_formula =
  | Fof of {
      name: string;
      role: string;
      formula: sequent;
      annotations: (source * (general_term list)) option;
    };;
