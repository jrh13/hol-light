(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* Examples showing error messages displayed by readable.ml when raising the *)
(* exception Readable_fail, with some working examples interspersed.         *)

needs "RichterHilbertAxiomGeometry/readable.ml";;

let s = "abc]edf" in Str.string_before s (FindMatch "\[" "\]" s);;

let s = "123456[abc]lmn[op[abc]pq]rs!!!!!!!!!!]xyz" in Str.string_before s
  (FindMatch "\[" "\]" s);;

let s = "123456[abc]lmn[op[abc]pq]rs!!!!!!!!!![]xyz" in Str.string_before s
  (FindMatch "\[" "\]" s);;

let s = "123456[abc]lmn[op[a; b; c]pq]rs[];xyz" in Str.string_before s
  (FindSemicolon s);;

let s = "123456[abc]lmn[op[a; b; c]pq]rs![]xyz" in Str.string_before s
  (FindSemicolon s);;

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    mp_TAC_specl [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    mp_TAC_specl [m; n; 1] mod_mod;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    mp_TAC_specl [m; n; 1] MOD _MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    mp_tac_specl [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  prooof
    intro_TAC !m n, H1;
    mp_TAC_specl [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

(* Output follows:

                  val it : string = "abc]"
#     val it : string = "123456[abc]lmn[op[abc]pq]rs!!!!!!!!!!]"
#     Exception:
No matching right bracket operator \] to left bracket operator \[ in xyz.
#     val it : string = "123456[abc]lmn[op[a; b; c]pq]rs[]"
#     Exception: No final semicolon in 123456[abc]lmn[op[a; b; c]pq]rs![]xyz.
#                   0..0..3..6..solved at 21
0..0..3..6..31..114..731..5973..solved at 6087
val MOD_MOD_REFL : thm = |- !m n. ~(n = 0) ==> m MOD n MOD n = m MOD n
#                   Exception:
This is not an mp_TAC_specl expression:
    mp_TAC_specl [m;  n;  1]  mod_mod.
#                   Exception:

    mp_TAC_specl [m; n; 1] MOD _MOD is not an mp_TAC_specl expression.
#                   Exception: can't parse
    mp_tac_specl [m; n; 1] MOD_MOD.
#                   Exception:
Missing initial "proof" or final "qed;" in

  !m n. ~(n = 0)  ==>  ((m MOD n) MOD n = m MOD n)

  prooof
    intro_TAC !m n, H1;
    mp_TAC_specl [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
.

Two examples from the ocaml reference manual sec 1.4 to show the handling of
exceptions other than Readable_fail.                                         *)

exception Empty_list;;
let head l =
  match l with
     [] -> raise Empty_list
  | hd :: tl -> hd;;
head [1;2];;
head [];;

exception Unbound_variable of string;;

type expression =
     Const of float
   | Var of string
   | Sum of expression * expression
   | Diff of expression * expression
   | Prod of expression * expression
   | Quot of expression * expression;;

let rec eval env exp =
    match exp with
       Const c -> c
    | Var v ->
         (try List.assoc v env with Not_found -> raise(Unbound_variable v))
    | Sum(f, g) -> eval env f +. eval env g
    | Diff(f, g) -> eval env f -. eval env g
    | Prod(f, g) -> eval env f *. eval env g
    | Quot(f, g) -> eval env f /. eval env g;;

eval [("x", 1.0); ("y", 3.14)] (Prod(Sum(Var "x", Const 2.0), Var "y"));;

eval [("x", 1.0); ("y", 3.14)] (Prod(Sum(Var "z", Const 2.0), Var "y"));;
