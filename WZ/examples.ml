(* ========================================================================= *)
(* Examples for the HOL Light implementation of the WZ method.               *)
(* ========================================================================= *)

needs "WZ/maxima.ml";;

(* Each executable example obtains its certificate from Maxima and checks it *)
(* in HOL.  The original explicit certificate is retained in a comment so   *)
(* that the example can instead be run with WZ_PROVE when Maxima is absent.  *)

(* ------------------------------------------------------------------------- *)
(* Example 1. Binomial theorem.                                              *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_1 =
  let ntm = `n:num`
  and stm = `sum (0..n) (\k. &(binom (n,k)) / &2 spow &n)`
  and atm = [] in
  (*
  let rtm = `&k / (&2 * (&n - &k + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 2. Chu-Vandermonde identity.                                      *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_2 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (n,k)) pow 2 / &(binom (2 * n,n)))`
  and atm = [] in
  (*
  let rtm =
    `--(&k pow 2 * (&3 * &n - &2 * &k + &3)) /
     (&2 * (&n - &k + &1) pow 2 * (&2 * &n + &1))`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 3. Shifted Chu-Vandermonde identity.                              *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_3 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (n,k)) * &(binom (m,k + p)) /
              &(binom (n + m,n + p)))`
  and atm = [`&p <= &m`] in
  (*
  let rtm =
    `(&k * (&p + &k)) / ((&n - &k + &1) * (&n + &m + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 4. Gosper example from Nemes et al.                               *)
(* ------------------------------------------------------------------------- *)

(* Shifting k and n avoids the pole at k = 0.                                *)

let WZ_EXAMPLE_4 =
  let ntm = `n:num`
  and stm =
    `sum (0..n + 1)
         (\k. &(binom (n + 1,k + 1)) * (&k + &1) * (&k + &1) *
              &(FACT k) / (&n + &1) spow (&k + &1))`
  and atm = [] in
  (*
  let rtm = `--(&n + &1) / (&k + &1)`
  and ctm = [`&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 5. Central-binomial identity.                                     *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_5 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. (-- &1 spow &k * &(binom (n,k)) *
               &(binom (2 * k,k)) * &4 spow &n / &4 spow &k) /
              &(binom (2 * n,n)))`
  and atm = [] in
  (*
  let rtm =
    `(&2 * &k pow 2) / ((&n - &k + &1) * (&2 * &n + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 6. Alternating binomial sum.                                      *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_6 =
  let ntm = `n:num`
  and stm =
    `sum (0..n + 1) (\k. -- &1 spow &k * &(binom (n + 1,k)))`
  and atm = [] in
  (*
  let rtm = `-- &k / (&n + &1)`
  and ctm = [`&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 7. Apery-number recurrence.                                       *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_7 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (n + k,k)) pow 2 * &(binom (n,k)) pow 2)`
  and atm = [] in
  (*
  let rtm =
    `(&4 * &k pow 4 * (&2 * &n + &3) *
      (&4 * &n pow 2 + &12 * &n - &2 * &k pow 2 + &3 * &k + &8)) /
     ((&n - &k + &1) pow 2 * (&n - &k + &2) pow 2)`
  and ctm =
    [`--((&n + &1) pow 3)`;
     `(&2 * &n + &3) * (&17 * &n pow 2 + &51 * &n + &39)`;
     `--((&n + &2) pow 3)`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 8. Dixon identity; A = B, Example 6.4.4.                          *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_8 =
  let ntm = `n:num`
  and stm =
    `sum (0..2 * n)
         (\k. (-- &1 spow &k * &(binom (2 * n,k)) pow 3) /
              (-- &1 spow &n * &(FACT (3 * n)) / &(FACT n) pow 3))`
  and atm = [] in
  (*
  let rtm =
    `(&k pow 3 *
      (&448 * &n pow 5 - &624 * &k * &n pow 4 + &1760 * &n pow 4 +
       &348 * &k pow 2 * &n pow 3 - &1932 * &k * &n pow 3 +
       &2728 * &n pow 3 - &90 * &k pow 3 * &n pow 2 +
       &792 * &k pow 2 * &n pow 2 - &2214 * &k * &n pow 2 +
       &2084 * &n pow 2 + &9 * &k pow 4 * &n -
       &132 * &k pow 3 * &n + &594 * &k pow 2 * &n -
       &1113 * &k * &n + &784 * &n + &6 * &k pow 4 -
       &48 * &k pow 3 + &147 * &k pow 2 - &207 * &k + &116)) /
     (&3 * (&2 * &n - &k + &1) pow 3 *
      (&2 * &n - &k + &2) pow 3 * (&3 * &n + &1) *
      (&3 * &n + &2) * &2)`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 9. Franel-number recurrence; A = B, p. 20.                        *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_9 =
  let ntm = `n:num`
  and stm = `sum (0..n) (\k. &(binom (n,k)) pow 3)`
  and atm = [] in
  (*
  let rtm =
    `(&k pow 3 * (&n + &1) pow 2 *
      (&14 * &n pow 3 - &27 * &k * &n pow 2 + &74 * &n pow 2 +
       &18 * &k pow 2 * &n - &93 * &k * &n + &128 * &n -
       &4 * &k pow 3 + &30 * &k pow 2 - &78 * &k + &72)) /
     ((&n - &k + &1) pow 3 * (&n - &k + &2) pow 3)`
  and ctm =
    [`&8 * (&n + &1) pow 2`;
     `&7 * &n pow 2 + &21 * &n + &16`;
     `--((&n + &2) pow 2)`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 10. A = B, p. 32.                                                 *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_10 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. (&1 - &2 * &n) *
              (-- &1 spow &k * &(binom (n,k)) * &4 spow &k) /
              &(binom (2 * k,k)))`
  and atm = [] in
  (*
  let rtm = `(&1 - &2 * &k) / (&2 * &n - &1)`
  and ctm = [`&1`] in
  WZ_PROVE ntm stm rtm ctm atm

  The A = B exercise gives the alternative certificate

  let rtm =
    `(&k * (&2 * &k - &1)) /
     ((&2 * &n - &1) * (&k - &n - &1))`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 11. Laguerre-polynomial recurrence.                               *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_11 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. -- &1 spow &k * &(binom (n,k)) / &(FACT k))`
  and atm = [] in
  (*
  let rtm =
    `--(&k pow 2 * (&n + &1)) /
     ((&n - &k + &1) * (&n - &k + &2))`
  and ctm = [`&n + &1`; `-- &2 * (&n + &1)`; `&n + &2`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 12. Dixon variant; A = B, p. 55.                                  *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_12 =
  let ntm = `n:num`
  and stm =
    `sum UNIV
         (\k. -- &1 spow &k *
              (&(binom (a + n,a + k)) * &(binom (a + c,c + k)) *
               &(binom (n + c,n + k))) /
              (&(FACT (a + n + c)) /
               (&(FACT a) * &(FACT n) * &(FACT c))))`
  and atm = [] in
  (*
  let rtm =
    `((&k + &a) * (&k + &c)) /
     ((&n + &c + &a + &1) * (&n - &k + &1))`
  and ctm = [`&2`; `-- &2`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 13. Alternating Chu-Vandermonde; A = B, p. 44.                    *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_13 =
  let ntm = `n:num`
  and stm =
    `sum UNIV
         (\k. (-- &1 spow &k * &(binom (2 * n,k)) pow 2) /
              (-- &1 spow &n * &(binom (2 * n,n))))`
  and atm = [] in
  (*
  let rtm =
    `(--(&k pow 2) *
      (&10 * &n pow 2 - &6 * &k * &n + &17 * &n +
       &k pow 2 - &5 * &k + &7)) /
     ((&2 * &n - &k + &1) pow 2 *
      (&2 * &n - &k + &2) pow 2)`
  and ctm = [`&2`; `-- &2`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 14. First binomial moment; A = B, p. 55.                          *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_14 =
  let ntm = `n:num`
  and stm =
    `sum (0..n + 1)
         (\k. &k * &(binom (n + 1,k)) /
              ((&n + &1) * &2 spow &n))`
  and atm = [] in
  (*
  let rtm = `(&k - &1) / (&2 * (&n - &k + &2))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 15. A = B, p. 115.                                                *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_15 =
  let ntm = `n:num`
  and stm =
    `sum (0..n + 1)
         (\k. &(binom (n + 1 + k,2 * k)) * &(binom (2 * k,k)) *
              -- &1 spow &k / (&k + &1))`
  and atm = [] in
  (*
  let rtm =
    `(-- &k * (&k + &1)) / ((&n + &1) pow 2 + &n + &1)`
  and ctm = [`&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 16. Nemes et al., Monthly problem example, p. 512.                *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_16 =
  let ntm = `n:num`
  and stm =
    `sum UNIV
         (\k. ((&n + &2) / (&2 * &k + &1)) *
              &(binom (n,2 * k)) * &2 spow (&n - &2 * &k - &1) *
              &(binom (2 * k + 1,k)) / &(binom (2 * n + 1,n)))`
  and atm = [] in
  (*
  let rtm =
    `(&4 * &k * (&k + &1)) /
     ((&n - &2 * &k + &1) * (&2 * &n + &3))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 17. Nemes et al., Monthly problem example, p. 518.                *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_17 =
  let ntm = `n:num`
  and stm =
    `sum UNIV
         (\k. &(binom (2 * n + 1,2 * k)) *
              &3 spow &k / &2 spow &n)`
  and atm = [] in
  (*
  let rtm =
    `(-- &k * (&2 * &k - &1) *
      (&2 * &n pow 2 + &4 * &k * &n + &n -
       &4 * &k pow 2 + &14 * &k - &7)) /
     (&4 * (&n - &k + &1) * (&n - &k + &2) *
      (&2 * &n - &2 * &k + &3) *
      (&2 * &n - &2 * &k + &5))`
  and ctm = [`&1`; `-- &4`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 18. Alternative Franel sum; Koepf, p. 58.                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_18 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (n,k)) pow 2 * &(binom (2 * k,n)))`
  and atm = [] in
  (*
  let rtm =
    `(--(&k pow 2) * (&n + &1) * (&n - &2 * &k) *
      (&n - &2 * &k + &1) * (&3 * &n - &2 * &k + &6)) /
     ((&n - &k + &1) pow 2 * (&n - &k + &2) pow 2)`
  and ctm =
    [`-- &8 * (&n + &1) pow 2`;
     `--(&7 * &n pow 2 + &21 * &n + &16)`;
     `(&n + &2) pow 2`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 19. Koepf, Exercise 6.7(g), p. 91.                                *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_19 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. -- &1 spow &k * &(binom (n,k)) *
              &(binom (n + x,n)) * &x / (&k + &x))`
  and atm = [`~(&x = &0)`] in
  (*
  let rtm =
    `(&k * (&x + &k)) / ((&n + &1) * (&n - &k + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 20. Factorial-binomial recurrence.                                *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_20 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (n,k)) * &(FACT k) * &(FACT k))`
  and atm = [] in
  (*
  let rtm =
    `(--(&n + &1) * (&n + &2)) /
     ((&n - &k + &1) * (&n - &k + &2))`
  and ctm =
    [`(&n + &1) * (&n + &2)`;
     `--((&n + &2) pow 2)`;
     `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 21. Generalized binomial theorem.                                 *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_21 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (n,k)) * x spow &k / (x + &1) spow &n)`
  and atm = [`~(x + &1 = &0)`] in
  (*
  let rtm = `&k / ((&n - &k + &1) * (x + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 22. Gould, identity 1.89.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_22 =
  let ntm = `n:num`
  and stm =
    `sum (0..n) (\k. &(binom (n,2 * k)) * &2 / &2 spow &n)`
  and atm = [`~(n = 0)`] in
  (*
  let rtm =
    `(&k * (&2 * &k - &1)) / (&n * (&n - &2 * &k + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 23. Gould, identity 1.91.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_23 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (2 * n + 1,2 * k + 1)) /
              &2 spow (&2 * &n + &1))`
  and atm = [] in
  (*
  let rtm =
    `(-- &k * (&2 * &k + &1) * (&6 * &n - &4 * &k + &5)) /
     (&4 * (&2 * &n + &1) * (&n - &k + &1) *
      (&2 * &n - &2 * &k + &1))`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 24. Gould, identity 3.99.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_24 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. (&(binom (n,2 * k)) * &(binom (2 * k,k)) *
               &2 spow &n) /
              (&4 spow &k * &(binom (2 * n,n))))`
  and atm = [] in
  (*
  let rtm =
    `(&4 * &k pow 2) /
     ((&n - &2 * &k + &1) * (&2 * &n + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 25. Gould, identity 6.30.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_25 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (n,k)) pow 2 * &(binom (p + k,2 * n)) /
              &(binom (p,n)) pow 2)`
  and atm = [`n:num < p`] in
  (*
  let rtm =
    `(--(&k pow 2) * (&p - &2 * &n + &k) *
      (&3 * &n * &p - &2 * &k * &p + &3 * &p -
       &4 * &n pow 2 + &3 * &k * &n - &5 * &n + &k - &1)) /
     (&2 * (&n - &k + &1) pow 2 * (&2 * &n + &1) *
      (&p - &n) pow 2)`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 26. Fourth-order Franel recurrence; Gould X.14.                   *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_26 =
  let ntm = `n:num`
  and stm = `sum (0..n) (\k. &(binom (n,k)) pow 4)`
  and atm = [] in
  (*
  let rtm =
    `--(&k pow 4 * (&n + &1) *
       (&75 * &n pow 6 - &260 * &k * &n pow 5 + &725 * &n pow 5 +
        &374 * &k pow 2 * &n pow 4 - &2056 * &k * &n pow 4 +
        &2885 * &n pow 4 - &276 * &k pow 3 * &n pow 3 +
        &2314 * &k pow 2 * &n pow 3 - &6420 * &k * &n pow 3 +
        &6045 * &n pow 3 + &104 * &k pow 4 * &n pow 2 -
        &1244 * &k pow 3 * &n pow 2 +
        &5298 * &k pow 2 * &n pow 2 - &9892 * &k * &n pow 2 +
        &7030 * &n pow 2 - &16 * &k pow 5 * &n +
        &298 * &k pow 4 * &n - &1844 * &k pow 3 * &n +
        &5322 * &k pow 2 * &n - &7520 * &k * &n + &4300 * &n -
        &20 * &k pow 5 + &210 * &k pow 4 - &900 * &k pow 3 +
        &1980 * &k pow 2 - &2256 * &k + &1080)) /
     ((&n - &k + &1) pow 4 * (&n - &k + &2) pow 4)`
  and ctm =
    [`-- &4 * (&n + &1) * (&4 * &n + &3) * (&4 * &n + &5)`;
     `-- &2 * (&2 * &n + &3) *
      (&3 * &n pow 2 + &9 * &n + &7)`;
     `(&n + &2) pow 3`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 27. Bruckman identity, following Gould.                           *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_27 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. ((&2 * &n + &1) / &4 spow &n) *
              &(binom (2 * n,n)) * -- &1 spow &k *
              &(binom (n,k)) * &2 spow &k / (&2 * &k + &1))`
  and atm = [] in
  (*
  let rtm =
    `(&k * (&2 * &k + &1) * (&2 * &n + &3)) /
     (&2 * (&n - &k + &1) * (&n - &k + &2))`
  and ctm = [`&2 * &n + &3`; `&1`; `-- &2 * (&n + &2)`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 28. Sury, Corollary 2.2.                                          *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_28 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. (&n + &m + &1) * &(binom (n + m,m)) *
              -- &1 spow &k * &(binom (n,k)) / (&m + &k + &1))`
  and atm = [] in
  (*
  let rtm =
    `(&k * (&m + &k + &1)) /
     ((&n - &k + &1) * (&n + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 29. Amdeberhan and De Angelis identity.                           *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_29 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. (&(binom (2 * n + 1,2 * k)) *
               &(binom (2 * k,k)) / &4 spow &k) /
              (&(binom (4 * n + 1,2 * n)) / &4 spow &n))`
  and atm = [] in
  (*
  let rtm =
    `(-- &2 * &k pow 2 *
      (&12 * &n pow 2 - &8 * &k * &n + &30 * &n -
       &10 * &k + &19)) /
     ((&n - &k + &1) * (&2 * &n - &2 * &k + &3) *
      (&4 * &n + &3) * (&4 * &n + &5))`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 30. Binomial convolution.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_30 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (n,k)) * &(binom (k,j)) /
              (&(binom (n,j)) * &2 spow (&n - &j)))`
  and atm = [`j:num <= n`] in
  (*
  let rtm = `(&k - &j) / (&2 * (&n - &k + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 31. Polya-Szego identity; Riordan, p. 5.                          *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_31 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. (-- &1 spow (&n - &k) * &4 spow &k *
               &(binom (n + k + 1,2 * k + 1))) / (&n + &1))`
  and atm = [] in
  (*
  let rtm =
    `(&k * (&2 * &k + &1)) /
     ((&n + &2) * (&n - &k + &1))`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 32. Riordan, p. 10.                                               *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_32 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. -- &1 spow (&k + &d) * &(binom (d,k)) *
              &(binom (n + k,p + k)) / &(binom (n,p + d)))`
  and atm = [`p + d:num <= n`] in
  (*
  let rtm =
    `(-- &k * (&p + &k)) / ((&n + &1) * (&p - &n - &1))`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 33. Riordan, p. 15, identity (10).                                *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_33 =
  let ntm = `n:num`
  and stm =
    `sum UNIV
         (\k. &(binom (p,k)) * &(binom (q,k)) *
              &(binom (n + k,p + q)) /
              (&(binom (n,p)) * &(binom (n,q))))`
  and atm = [`p:num <= n`; `q:num <= n`] in
  (*
  let rtm = `&k pow 2 / (&n + &1) pow 2`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 34. Riordan, p. 36.                                               *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_34 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (2 * n + 1,2 * k)) *
              &(binom (m + k,2 * n)) /
              &(binom (2 * m + 1,2 * n)))`
  and atm = [`n:num < m`] in
  (*
  let rtm =
    `(&k * (&2 * &k - &1) * (&2 * &n - &m - &k) *
      (&8 * &n pow 2 - &6 * &m * &n - &6 * &k * &n +
       &10 * &n + &4 * &k * &m - &7 * &m - &k + &1)) /
     (&2 * (&n - &k + &1) * (&n - &m) *
      (&2 * &n - &2 * &k + &3) * (&2 * &n - &2 * &m - &1) *
      (&2 * &n + &1))`
  and ctm = [`&1`; `-- &1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 35. Gould, identity 1.45.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_35 =
  let ntm = `n:num`
  and stm =
    `sum UNIV
         (\k. -- &1 spow (&k + &1) *
              &(binom (n,k + 1)) / (&k + &1))`
  and atm = [`~(&n = &0)`] in
  (*
  let rtm = `(&k + &1) pow 2 / (&n - &k)`
  and ctm = [`&n + &1`; `--(&n + &1)`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 36. Gould, identity 1.94.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_36 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. -- &1 spow &k * &(binom (2 * n + 1,2 * k)))`
  and atm = [] in
  (*
  let rtm =
    `(-- &k * (&2 * &k - &1) *
      (&10 * &n pow 2 - &12 * &k * &n + &37 * &n +
       &4 * &k pow 2 - &22 * &k + &33)) /
     ((&n - &k + &1) * (&n - &k + &2) *
      (&2 * &n - &2 * &k + &3) *
      (&2 * &n - &2 * &k + &5))`
  and ctm = [`&4`; `&0`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 37. Gould, identity 1.100.                                        *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_37 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. &(binom (2 * n + 1,2 * k + 1)) * &k /
              ((&2 * &n - &1) * &4 spow (&n - &1)))`
  and atm = [] in
  (*
  let rtm =
    `((&k - &1) * (&2 * &k + &1) *
      (&6 * &n pow 2 - &4 * &k * &n + &7 * &n -
       &2 * &k + &1)) /
     (&4 * (&n - &k + &1) * (&2 * &n + &1) *
      (&2 * &n - &2 * &k + &1))`
  and ctm = [`&n`; `-- &n`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 38. Gould, identity 3.34.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_38 =
  let ntm = `n:num`
  and stm =
    `sum (:num)
         (\k. (-- &1 spow &k * &(binom (x,k)) *
               rbinom (&x,&2 * &n - &k)) /
              (-- &1 spow &n * &(binom (x,n))))`
  and atm = [`n:num < x`] in
  (*
  let rtm =
    `(&k * (&x + &1) * (&x - &2 * &n + &k)) /
     ((&2 * &n - &k + &1) * (&2 * &n - &k + &2) *
      (&x - &n))`
  and ctm = [`-- &2`; `&2`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 39. Gould, identity 7.12.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_39 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. (&n * -- &1 spow &k * &(binom (n,k)) *
               &(binom (n + k,k)) * &4 spow &k) /
              (-- &1 spow &n * &(binom (2 * k,k)) *
               (&n + &k)))`
  and atm = [`0 < n`] in
  (*
  let rtm =
    `(&k * (&2 * &k - &1)) / (&n * (&n - &k + &1))`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 40. Gould, identity 3.106.                                        *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_40 =
  let ntm = `n:num`
  and stm =
    `sum (0..2 * n)
         (\k. (-- &1 spow &k * &(binom (2 * n,k)) *
               &(binom (2 * n + 2 * k,n + k)) *
               &2 spow (&2 * &n - &k)) /
              &(binom (2 * n,n)))`
  and atm = [] in
  (*
  let rtm =
    `--(&32 * &k * (&n + &1) pow 2 *
        (&250 * &k * &n pow 4 - &250 * &n pow 4 +
         &270 * &k pow 2 * &n pow 3 + &1015 * &k * &n pow 3 -
         &1275 * &n pow 3 + &15 * &k pow 3 * &n pow 2 +
         &1016 * &k pow 2 * &n pow 2 +
         &1393 * &k * &n pow 2 - &2385 * &n pow 2 -
         &5 * &k pow 4 * &n + &57 * &k pow 3 * &n +
         &1195 * &k pow 2 * &n + &737 * &k * &n - &1940 * &n -
         &9 * &k pow 4 + &54 * &k pow 3 + &431 * &k pow 2 +
         &112 * &k - &576)) /
     ((&n + &k + &1) * (&2 * &n - &k + &1) *
      (&2 * &n - &k + &2) * (&2 * &n - &k + &3) *
      (&2 * &n - &k + &4))`
  and ctm =
    [`&32 * (&n + &1) pow 2 * (&5 * &n + &9)`;
     `--(&4 *
         (&145 * &n pow 3 + &551 * &n pow 2 + &665 * &n + &256))`;
     `&3 * (&3 * &n + &4) * (&3 * &n + &5) * (&5 * &n + &4)`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 41. Gould, identity 3.48.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_41 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. (-- &1 spow &k * &(binom (n,k)) *
               &(binom (x + k,r + k))) /
              (-- &1 spow &n * &(binom (x,n + r))))`
  and atm = [`n + r:num < x`] in
  (*
  let rtm =
    `(&k * (&r + &k)) /
     ((&n - &k + &1) * (&x - &r - &n))`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;

(* ------------------------------------------------------------------------- *)
(* Example 42. Gould, identity 6.37.                                         *)
(* ------------------------------------------------------------------------- *)

let WZ_EXAMPLE_42 =
  let ntm = `n:num`
  and stm =
    `sum (0..n)
         (\k. (&(binom (n,k)) pow 2 *
               &(binom (3 * n + k,2 * n))) /
              &(binom (3 * n,n)) pow 2)`
  and atm = [] in
  (*
  let rtm =
    `--(&k pow 2 *
        (&207 * &n pow 4 + &66 * &k * &n pow 3 +
         &468 * &n pow 3 - &145 * &k pow 2 * &n pow 2 +
         &294 * &k * &n pow 2 + &340 * &n pow 2 -
         &186 * &k pow 2 * &n + &294 * &k * &n + &78 * &n -
         &59 * &k pow 2 + &84 * &k - &1)) /
     (&9 * (&n - &k + &1) pow 2 * (&3 * &n + &1) pow 2 *
      (&3 * &n + &2) pow 2)`
  and ctm = [`-- &1`; `&1`] in
  WZ_PROVE ntm stm rtm ctm atm
  *)
  WZ_MAXIMA_PROVE ntm stm atm;;
