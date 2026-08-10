(* ========================================================================= *)
(* Incomplete or unsupported examples for the HOL Light WZ implementation.   *)
(* ========================================================================= *)

(* These are possible future extensions, not executable regression tests.    *)
(* The reasons they are not handled are recorded with each candidate.        *)

(* ------------------------------------------------------------------------- *)
(* Nonexample 1. A = B, p. 78.                                               *)
(* ------------------------------------------------------------------------- *)

(* The summand (&4 * &k + &1) * &(FACT k) / &(FACT (2 * k + 1)) does not    *)
(* have finite support, so the original certificate was not passed to the    *)
(* checker.                                                                  *)

(* ------------------------------------------------------------------------- *)
(* Nonexample 2. Nemes et al., Monthly problem example, p. 518.              *)
(* ------------------------------------------------------------------------- *)

(* The original checker run deliberately stops before theorem extraction:    *)
(* The quotient below does not have finite support over UNIV.                *)
(*
let stm =
  `sum UNIV
       (\k. -- &1 spow &k *
            &(binom (4 * n,2 * k)) / &(binom (2 * n,k)))`
and rtm = `(&1 - &2 * &k) / (&4 * &n - &2)`
and ctm = [`&1`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 3. Gould, identity 2.8.                                        *)
(* ------------------------------------------------------------------------- *)

(* The original certificate has a pole at k = 0 and was not submitted to     *)
(* the checker.                                                              *)
(*
let stm =
  `sum (0..n)
       (\k. -- &1 spow &k * &k / &(binom (2 * n,k)) *
            (&n + &1) / &n)`
and rtm =
  `((&2 * &n - &k + &1) *
    ((&2 * &n + &3) -
     &k * (&4 * &n pow 2 + &10 * &n + &6))) /
   ((&4 * &n pow 2 + &10 * &n + &6) *
    (&2 * &n + &3) * &k)`
and ctm = [`&1`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 4. Gould, identity 4.9.                                        *)
(* ------------------------------------------------------------------------- *)

(* The denominator binomial can vanish inside the intended range, so the     *)
(* original side-condition proof was left unfinished.                        *)
(*
let stm =
  `sum (0..n + 1)
       (\k. &(binom (n + 1,k)) / &(binom (2 * n + 1,k)))`
and rtm = `(&k - &2 * &n - &2) / (&n + &1)`
and ctm = [`&1`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 5. Gould, identity 22.2.                                       *)
(* ------------------------------------------------------------------------- *)

(* This very large certificate was used only for initial reduction in the    *)
(* original.  A binomial in the denominator can vanish, and completing the   *)
(* side conditions was both unsupported and prohibitively expensive.         *)
(*
let stm =
  `sum (0..2 * n)
       (\k. (-- &1 spow &k * &(binom (2 * n,k)) pow 4 *
             &(binom (3 * n + k,k)) / &(binom (5 * n,k))) /
            (-- &1 spow &n * &(binom (3 * n,n)) pow 3 *
             (&(FACT (4 * n)) * &(FACT (2 * n))) /
             (&(FACT (5 * n)) * &(FACT n))))`;;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 6. Riordan, p. 42.                                             *)
(* ------------------------------------------------------------------------- *)

(* The original asks how to prove that this sum is zero after obtaining a    *)
(* recurrence; no HOL summand or certificate was recorded.                   *)
(*
  Zeilberger((-1)^k * binomial(2 * n + 1,k)^3,k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 7. Riordan, p. 144.                                            *)
(* ------------------------------------------------------------------------- *)

(* The first formulation has a binomial with a subtractive upper argument.   *)
(* The change of variables below avoids it, but the original checker run was *)
(* still left inside an unfinished experiment.                               *)
(*
let stm =
  `sum (0..n)
       (\k. &(binom (n,k)) pow 2 * &(binom (2 * n + k,2 * n)) /
            &(binom (2 * n,n)) pow 2)`
and rtm =
  `--(&k pow 3 *
      (&30 * &n pow 2 - &21 * &k * &n + &49 * &n -
       &13 * &k + &19)) /
   (&8 * (&n - &k + &1) pow 2 * (&2 * &n + &1) pow 3)`
and ctm = [`-- &1`; `&1`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 8. Generalized Apery recurrence (Strehl).                      *)
(* ------------------------------------------------------------------------- *)

(* Maxima did not find the expected order-six recurrence.                    *)
(*
  Zeilberger(binomial(n,k)^3 * binomial(n + k,k)^3,k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 9. Srivastava, generalization of a Vietoris identity.          *)
(* ------------------------------------------------------------------------- *)

(* The proposed formulation uses rbinom to express a subtractive argument,   *)
(* so it is outside the fragment translated by maxima.ml.                    *)
(*
let stm =
  `sum UNIV
       (\k. &(binom (p + k,k)) *
            rbinom (&m + &n - &p - &k - &1,&n - &k) /
            &(binom (m + n,n)))`
and rtm =
  `(&k * (&p - &n - &m + &k)) /
   ((&n - &k + &1) * (&n + &m + &1))`
and ctm = [`-- &1`; `&1`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 10. Gould, identity 1.59.                                      *)
(* ------------------------------------------------------------------------- *)

(* Initial reduction succeeded for a third-order recurrence, but the side    *)
(* conditions were too slow and no theorem was obtained.                     *)
(*
let stm =
  `sum (0..n) (\k. &(binom (4 * n,4 * k)) / &4 spow &k)`;;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 11. A = B, Quick Start.                                        *)
(* ------------------------------------------------------------------------- *)

(* The proposed identity has unresolved finite-support and subtraction       *)
(* issues; the original contains only the Maxima input.                      *)
(*
  Zeilberger((-1)^k * binomial(x - k + 1,k) *
             binomial(x - 2 * k,n - k),k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 12. A = B, Exercise 2.7(2c).                                   *)
(* ------------------------------------------------------------------------- *)

(* This proposed normalization did not produce the expected identity.        *)
(*
  Zeilberger(binomial(x + 1,2 * k + 1) *
             binomial(x - 2 * k,n - k) /
             binomial(2 * x + 2,2 * n + 1),k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 13. A = B, Example 3.6.2.                                      *)
(* ------------------------------------------------------------------------- *)

(* Maxima can generate a recurrence, but finite support was not established. *)
(*
  Zeilberger((-1)^k * binomial(2 * n,k) * binomial(2 * k,k) *
             binomial(4 * n - 2 * k,2 * n - k) /
             binomial(2 * n,n)^2,k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 14. A = B, Example 6.4.3.                                      *)
(* ------------------------------------------------------------------------- *)

(* Initial reduction succeeds, but the side-condition tactic does not finish *)
(* the proof because of the subtractive rbinom argument.                     *)
(*
let stm =
  `sum (0..n + 1)
       (\k. -- &1 spow &k * &(binom (n + 1,k)) *
            rbinom (&2 * &n + &1 - &2 * &k,&n))`
and rtm =
  `--(&2 * &k * (&n - &k + &1) *
      (&2 * &n - &2 * &k + &3) *
      (&3 * &n - &2 * &k + &6)) /
   ((&n + &1) * (&n - &2 * &k + &2) * (&n - &k + &2))`
and ctm = [`--(&n + &2)`; `&n + &2`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 15. A = B, Exercise 6.6(1e).                                   *)
(* ------------------------------------------------------------------------- *)

(* Only Maxima input was recorded; natural subtraction prevents a direct     *)
(* encoding in the supported fragment.                                       *)
(*
  Zeilberger((-1)^k * binomial(n - k,k) *
             2^(n - 2 * k) / (n + 1),k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 16. A = B, pp. 130-131.                                        *)
(* ------------------------------------------------------------------------- *)

(* This companion identity needs support for a quotient whose summation      *)
(* range is not represented by the current tactic.                           *)
(*
  Zeilberger((binomial(k,n) / binomial(k + a + 1,k)) /
             ((a + 1) / ((n + 1) * binomial(a,n + 1))),k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 17. Non-proper hypergeometric pattern.                         *)
(* ------------------------------------------------------------------------- *)

(* The generic summand, and the concrete specialization tried in the         *)
(* original, are rejected as non-proper hypergeometric terms.                *)
(*
  Zeilberger(binomial(t * k + r,k) *
             binomial(t * (n - k) + s,n - k) *
             (r / (t * k + r)) /
             binomial(t * n + r + s,n),k,n);

  Zeilberger((binomial(3 * k + 1,k) *
              binomial(3 * n - 3 * k,n - k) / (3 * k + 1)) /
             binomial(3 * n + 1,n),k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 18. AMM 103, p. 702, Problem 10332.                            *)
(* ------------------------------------------------------------------------- *)

(* Only the proposed Maxima input was recorded.                              *)
(*
  Zeilberger(2^(n - m - 2 * k) * binomial(n,k) *
             binomial(n - k,k + m) /
             binomial(2 * n,m + n),k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 19. AMM 102, p. 70, Problem 10424.                             *)
(* ------------------------------------------------------------------------- *)

(* Maxima gives a high-order recurrence, but the intended WZ normalization   *)
(* and the subtractive arguments were not resolved.                          *)
(*
  Zeilberger(2^k * (n / (n - k)) *
             binomial(n - k,2 * k),k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 20. Finite Pascal sum.                                         *)
(* ------------------------------------------------------------------------- *)

(* This identity needs explicit summation limits rather than the finite-     *)
(* support argument used by the current implementation.                      *)
(*
  !n. sum (0..n) (\k. &(binom (n + k,k)) / &2 pow (n + k)) = &1
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 21. Generalized finite Pascal sum.                             *)
(* ------------------------------------------------------------------------- *)

(* This generalization of the preceding identity also needs explicit limits. *)
(*
  !n m.
    sum (0..n) (\k. &(binom (m + n,m + k)) / &2 pow (m + n)) =
    sum (0..n)
        (\k. &(binom ((m + k) - 1,m - 1)) / &2 pow (m + k))
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 22. AMM 99, p. 63, Problem E3376.                              *)
(* ------------------------------------------------------------------------- *)

(* This is a double sum requiring a separate adaptation of Zeilberger's      *)
(* method; no single-sum certificate was recorded.                           *)
(*
  !N. nsum (0..N)
       (\i. nsum (0..N)
            (\j. binom (i + j,j) EXP 2 *
                 binom (2 * N - 2 * i - 2 * j,2 * N - 2 * j))) =
      (2 * N + 1) * binom (2 * N,N) pow 2
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 23. Abramov Gosper counterexample.                             *)
(* ------------------------------------------------------------------------- *)

(* This deliberate Gosper counterexample does not have finite support.       *)
(*
let stm =
  `sum (0..n) (\k. &(binom (2 * k - 1,k)) / &4 spow &k)`
and rtm = `&2 * &k`
and ctm = [`&1`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 24. Abel binomial identity; Riordan, p. 18.                    *)
(* ------------------------------------------------------------------------- *)

(* Maxima classifies Abel's binomial generalization as non-proper            *)
(* hypergeometric.                                                           *)
(*
  Zeilberger(binomial(n,k) * (x + k)^(k - 1) *
             (y + n - k)^(n - k) * x / (x + y + n)^n,k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 25. Riordan, p. 41, Exercise 22.                               *)
(* ------------------------------------------------------------------------- *)

(* The original side-condition proof made substantial progress but did not   *)
(* finish.                                                                   *)
(*
let stm =
  `sum (:num)
       (\k. &(binom (p + k,q)) * &(binom (q,k)) *
            &(binom (n,p + k)) /
            (&(binom (n,p)) * &(binom (n,q))))`
and rtm =
  `(&k * (&q - &p - &k)) /
   ((&n + &1) * (&p - &n + &k - &1))`
and ctm = [`&1`; `-- &1`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 26. Gould, identity 1.14.                                      *)
(* ------------------------------------------------------------------------- *)

(* Maxima classifies this summand as non-proper hypergeometric.              *)
(*
  Zeilberger((-1)^k * binomial(n,k) * (x - k)^(n + 1) /
             (factorial(n + 1) * (2 * x - n) / 2),k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 27. Gould, identity 3.30.                                      *)
(* ------------------------------------------------------------------------- *)

(* Both original formulations leave unresolved denominator conditions.       *)
(*
let stm =
  `sum (0..n + 1)
       (\k. &(binom (n + 1,k)) * &(binom (x,k)) * &k /
            ((&n + &1) * &(binom (x + n,n + 1))))`
and rtm =
  `((&k - &1) * &k) /
   ((&n - &k + &2) * (&x + &n + &1))`
and ctm = [`&1`; `-- &1`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 28. Gould, identity 3.118.                                     *)
(* ------------------------------------------------------------------------- *)

(* This normalized binomial theorem also leaves unresolved side conditions.  *)
(*
let stm =
  `sum (0..n)
       (\k. &(binom (n,k)) * &(binom (k,j)) * x pow k /
            (&(binom (n,j)) * x spow &j *
             (&1 + x) spow (&n - &j)))`
and rtm = `(&k - &j) / ((&n - &k + &1) * (x + &1))`
and ctm = [`&1`; `-- &1`];;
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 29. Gould, identity 6.36.                                      *)
(* ------------------------------------------------------------------------- *)

(* Maxima produces an enormous certificate; it was not imported into HOL.    *)
(*
  Zeilberger((-1)^k * binomial(2 * n,k)^2 *
             binomial(n + k,k)^2 / binomial(2 * n,n),k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 30. Gould, p. 66.                                              *)
(* ------------------------------------------------------------------------- *)

(* The original only proposes comparing the two recurrences below.           *)
(*
  Zeilberger(binomial(n,k)^4 * k,k,n);
  Zeilberger(binomial(n,k)^4 * n / 2,k,n);
*)

(* ------------------------------------------------------------------------- *)
(* Nonexample 31. Chaundy-Bullard identity.                                  *)
(* ------------------------------------------------------------------------- *)

(* The Chaundy-Bullard identity is not directly hypergeometric and its WZ    *)
(* proof needs explicit summation limits, which are not supported here.      *)
(* The original notes "New proofs of the Chaundy-Bullard identity" and       *)
(* "A Proof That Zeilberger Missed", arXiv:1112.1359.                        *)
