(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* Examples showing error messages displayed by readable.ml when raising the *)
(* exception Readable_fail, with some working examples interspersed.         *)

needs "RichterHilbertAxiomGeometry/readable.ml";;

let s = "abc]edf" in Str.string_before s (FindMatch "\[" "\]" s);;

let s = "123456[abc]lmn[op[abc]pq]rs!!!!!!!!!!]xyz" in
  Str.string_before s (FindMatch "\[" "\]" s);;

(* val it : string = "abc]"
   val it : string = "123456[abc]lmn[op[abc]pq]rs!!!!!!!!!!]"                   *)

let s = "123456[abc]lmn[op[abc]pq]rs!!!!!!!!!![]xyz" in Str.string_before s
  (FindMatch "\[" "\]" s);;

(*     Exception:
No matching right bracket operator \] to left bracket operator \[ in xyz.    *)

let s = "123456[abc]lmn[op[a; b; c]pq]rs[];xyz" in
  Str.string_before s (FindSemicolon s);;

let s = "123456[abc]lmn[op[a; b; c]pq]rs![]xyz" in
  Str.string_before s (FindSemicolon s);;

(*   Exception: No final semicolon in 123456[abc]lmn[op[a; b; c]pq]rs![]xyz. *)

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    MP_TAC ISPECL [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

(*                   0..0..3..6..solved at 21
0..0..3..6..31..114..731..5973..solved at 6087
val MOD_MOD_REFL : thm = |- !m n. ~(n = 0) ==> m MOD n MOD n = m MOD n       *)

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    INTRO_TAC !m n, H1;
    MP_TAC ISPECL [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

(*                  Exception: Can't parse as a Proof:

    INTRO_TAC !m n, H1.							     *)

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    MP_TAC ISPECL [m; n; 1] mod_mod;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

(*                Exception: Not a theorem:
 ISPECL [m; n; 1] mod_mod.                                      *)


let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    MP_TAC ISPECL  MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

(*                        Exception: termlist->thm->thm ISPECL
 not followed by term list in
  MOD_MOD.                                                                   *)

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    MP_TAC ISPECL m n 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

(*                        Exception:
termlist->thm->thm ISPECL
 not followed by term list in
 m n 1] MOD_MOD.                                                             *)

interactive_goal `;∀p q. p * p = 2 * q * q  ⇒  q = 0
`;;
interactive_proof `;
    MATCH_MP_TAC     ;
    intro_TAC ∀p, A, ∀q, B;
    EVEN(p * p) ⇔ EVEN(2 * q * q)     [] proof  qed;
`;;

(*         Exception: Empty theorem:
 .                                                                           *)


interactive_goal `;∀p q. p * p = 2 * q * q  ⇒  q = 0
`;;
interactive_proof `;
    MATCH_MP_TAC num_WF num_WF ;
    intro_TAC ∀p, A, ∀q, B;
    EVEN(p * p) ⇔ EVEN(2 * q * q)     [] proof  qed;
`;;

(*          Exception:
thm_tactic MATCH_MP_TAC not followed by a theorem, but instead
 num_WF num_WF .                                                             *)

let EXP_2_read = theorem `;
  ∀n:num. n EXP 2 = n * n
  by REWRITE BIT0_THM BIT1_THM EXP EXP_ADD MULT_CLAUSES ADD_CLAUSES`;;

(*      Exception:
Not a proof:
 REWRITE BIT0_THM BIT1_THM EXP EXP_ADD MULT_CLAUSES ADD_CLAUSES.             

The problem is that REWRITE should be rewrite.*)

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  prooof
    intro_TAC !m n, H1;
    MP_TAC ISPECL [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
`;;

(*                            Exception:
Missing initial "proof", "by", or final "qed;" in

  !m n. ~(n = 0)  ==>  ((m MOD n) MOD n = m MOD n)

  prooof
    intro_TAC !m n, H1;
    MP_TAC ISPECL [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
.                                                                            *)

let MOD_MOD_REFL = theorem `;
  ∀m n. ¬(n = 0)  ⇒  ((m MOD n) MOD n = m MOD n)

  proof
    intro_TAC !m n, H1;
    MP_TAC ISPECL [m; n; 1] MOD_MOD;
    fol H1 MULT_CLAUSES MULT_EQ_0 ONE NOT_SUC;
  qed;
What me worry?
`;;

(*                  Exception: Trailing garbage after the proof...qed:
What me worry?
.

   Two examples from the ocaml reference manual sec 1.4 to show the
   handling of exceptions other than Readable_fail.                          *)

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


(* The only difference caused by printReadExn is that
    Exception: Unbound_variable "z".
    is now
    Exception: Unbound_variable("z").                                        *)


let binom = define
 `(!n. binom(n,0) = 1) /\
  (!k. binom(0,SUC(k)) = 0) /\
  (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))`;;

let BINOM_LT_read = theorem `;
  ∀n k. n < k  ⇒  binom(n,k) = 0

  proof
    INDUCT_TAC; INDUCT_TAC;
    rewrite binom ARITH LT_SUC LT;
    ASM_SIMP_TAC ARITH_RULE [n < k ==> n < SUC(k)] ARITH;
  qed;
`;;

let BINOM_REFL_read = theorem `;
  ∀n. binom(n,n) = 1

  proof
    INDUCT_TAC;
    ASM_SIMP_TAC binom BINOM_LT_read LT ARITH;
  qed;
`;;

let BINOMIAL_THEOREM_read = theorem `;
  ∀n. (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))

  proof
    ∀f n. nsum (0.. SUC n) f = f(0) + nsum (0..n) (λi. f (SUC i))     [Nsum0SUC] by simplify LE_0 ADD1 NSUM_CLAUSES_LEFT NSUM_OFFSET;
    MATCH_MP_TAC num_INDUCTION;
    simplify EXP NSUM_SING_NUMSEG binom SUB_0 MULT_CLAUSES;
    intro_TAC ∀n, nThm;
    rewrite Nsum0SUC binom RIGHT_ADD_DISTRIB NSUM_ADD_NUMSEG GSYM NSUM_LMUL ADD_ASSOC;
    rewriteR ADD_SYM;
    rewriteRLDepth SUB_SUC EXP;
    rewrite MULT_AC EQ_ADD_LCANCEL MESON [binom] [1 = binom(n, 0)] GSYM Nsum0SUC;
    simplify NSUM_CLAUSES_RIGHT ARITH_RULE [0 < SUC n  ∧  0 <= SUC n] LT BINOM_LT_read MULT_CLAUSES ADD_CLAUSES SUC_SUB1;
    simplify ARITH_RULE [k <= n  ⇒  SUC n - k = SUC(n - k)] EXP MULT_AC;
  qed;
`;;

(* val binom : thm =
  |- (!n. binom (n,0) = 1) /\
     (!k. binom (0,SUC k) = 0) /\
     (!n k. binom (SUC n,SUC k) = binom (n,SUC k) + binom (n,k))
                val BINOM_LT_read : thm = |- !n k. n < k ==> binom (n,k) = 0
                val BINOM_REFL_read : thm = |- !n. binom (n,n) = 1
                              0..0..1..2..solved at 6
val BINOMIAL_THEOREM_read : thm =
  |- !n. (x + y) EXP n =
         nsum (0..n) (\k. binom (n,k) * x EXP k * y EXP (n - k))             *)


let BINOM_LT_read = theorem `;
  ∀n k. n < k  ⇒  binom(n,k) = 0

  proof
    INDUCT_TAC; INDUCT_TAC;
    rewrite binom ARITH LT_SUC LT;
    ASM_SIMP_TAC ARITH_RULE n < k ==> n < SUC(k)] ARITH;
  qed;
`;;

(*                   Exception:
term->thm ARITH_RULE not followed by term list, but instead
n < k ==> n < SUC(k)] ARITH.                                                 *)


let BINOM_LT_read = theorem `;
  ∀n k. n < k  ⇒  binom(n,k) = 0

  proof
    INDUCT_TAC; INDUCT_TAC;
    rewrite binom ARITH LT_SUC LT;
    ASM_SIMP_TAC ARITH_RULE [n < k; n < SUC(k)] ARITH;
  qed;
`;;

(*                   Exception:
term->thm ARITH_RULE not followed by length 1 term list, but instead the list
[n < k; n < SUC(k)].                                                         *)


let BINOM_LT_read = theorem `;
  ∀n k. n < k  ⇒  binom(n,k) = 0

  proof
    INDUCT_TAC; INDUCT_TAC;
    rewrite binom ARITH LT_SUC LT;
    ASM_SIMP_TAC ARITH_RULE [ ] ARITH;
  qed;
`;;

(*                   Exception:
term->thm ARITH_RULE not followed by length 1 term list, but instead
 [].                                                                         *)


let BINOMIAL_THEOREM_read = theorem `;
  ∀n. (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))

  proof
    ∀f n. nsum (0.. SUC n) f = f(0) + nsum (0..n) (λi. f (SUC i))     [Nsum0SUC] by simplify LE_0 ADD1 NSUM_CLAUSES_LEFT NSUM_OFFSET;
    MATCH_MP_TAC num_INDUCTION;
    simplify EXP NSUM_SING_NUMSEG binom SUB_0 MULT_CLAUSES;
    intro_TAC ∀n, nThm;
    rewrite Nsum0SUC binom RIGHT_ADD_DISTRIB NSUM_ADD_NUMSEG GSYM NSUM_LMUL ADD_ASSOC;
    rewriteR ADD_SYM;
    rewriteRLDepth SUB_SUC EXP;
    rewrite MULT_AC EQ_ADD_LCANCEL MESON binom] [1 = binom(n, 0)] GSYM Nsum0SUC;
    simplify NSUM_CLAUSES_RIGHT ARITH_RULE [0 < SUC n  ∧  0 <= SUC n] LT BINOM_LT_read MULT_CLAUSES ADD_CLAUSES SUC_SUB1;
    simplify ARITH_RULE [k <= n  ⇒  SUC n - k = SUC(n - k)] EXP MULT_AC;
  qed;
`;;

(*                                  Exception:
thmlist->term->thm MESON not followed by thm list in
 binom] [1 = binom(n, 0)] GSYM Nsum0SUC.                                     *)


let BINOMIAL_THEOREM_read = theorem `;
  ∀n. (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))

  proof
    ∀f n. nsum (0.. SUC n) f = f(0) + nsum (0..n) (λi. f (SUC i))     [Nsum0SUC] by simplify LE_0 ADD1 NSUM_CLAUSES_LEFT NSUM_OFFSET;
    MATCH_MP_TAC num_INDUCTION;
    simplify EXP NSUM_SING_NUMSEG binom SUB_0 MULT_CLAUSES;
    intro_TAC ∀n, nThm;
    rewrite Nsum0SUC binom RIGHT_ADD_DISTRIB NSUM_ADD_NUMSEG GSYM NSUM_LMUL ADD_ASSOC;
    rewriteR ADD_SYM;
    rewriteRLDepth SUB_SUC EXP;
    rewrite MULT_AC EQ_ADD_LCANCEL MESON [binom] 1 = binom(n, 0)] GSYM Nsum0SUC;
    simplify NSUM_CLAUSES_RIGHT ARITH_RULE [0 < SUC n  ∧  0 <= SUC n] LT BINOM_LT_read MULT_CLAUSES ADD_CLAUSES SUC_SUB1;
    simplify ARITH_RULE [k <= n  ⇒  SUC n - k = SUC(n - k)] EXP MULT_AC;
  qed;
`;;

(*                                Exception:
thmlist->term->thm MESON followed by list of theorems [binom]
      not followed by term in
 1 = binom(n, 0)] GSYM Nsum0SUC.                                             *)

