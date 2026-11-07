(* ========================================================================= *)
(* Products of two L-series at s = 1 as lattice sums: the genus identity and *)
(* the total identities of class number two.                                 *)
(*                                                                           *)
(* Purpose: for d = p q (p = 1, q = 3 mod 4 primes) with                     *)
(* form_classno(-d) = 2 and k = k1 k2 (two distinct primes, k = 1 mod 4)     *)
(* coprime to d, the genus identity of Baker, Transcendental Number Theory,  *)
(* Ch. 5, sec. 5 (CN_GENUS_PRODUCT_LIMIT):                                   *)
(*   L(1,chi_k) L(1,chi_kd) + L(1,chi_kp) L(1,chi_kq) = 2 (zeta_k(2) + S),   *)
(* S the slice sum of the principal form f = (1, 1, (d+1)/4) alone, and the  *)
(* total identity (Baker, sec. 2, (1), for the two classes of forms,         *)
(* CN_TOTAL_PRODUCT_LIMIT):                                                  *)
(*   L(1,chi_k) L(1,chi_kd) = zeta_k(2) (1 + chi_k(q)/q) + S1 + S2,          *)
(* S1, S2 the slice sums of f and of f2 = (q, q, (p+q)/4); for the           *)
(* discriminant -4d (d prime = 1 mod 4 or d = 2 p) with                      *)
(* form_classno(-4d) = 2 (CN_TOTAL_PRODUCT_LIMIT_EVEN):                      *)
(*   L(1,chi_k) L(1,chi_k chi_-4d) = zeta_k(2) (1 + chi_k(2)/2) + S1 + S2,   *)
(* S1 for x^2 + d y^2 and S2 for the second form (2, b2, c2),                *)
(* 8 c2 - b2^2 = 4 d. Characters: chi_m = qchar m (Jacobi symbol), so        *)
(* qchar (k p q) is chi_-kd, qchar (k p) is chi_kp (even), qchar (k q) is    *)
(* chi_-kq (odd), and kchar4 d is the Kronecker symbol (-4d / .). The slices *)
(* at s = 1 are qform_slice k a b c (&1).                                    *)
(*                                                                           *)
(* Method: for s > 1 the Dirichlet product (DIRICHLET_SERIES_PRODUCT) and    *)
(* the complete multiplicativity of the characters turn the products into    *)
(* the series of chi_k(l) g(l) / l^s and chi_k(l) g2(l) / l^s, with g(l) the *)
(* sum over m dividing l of chi_d(m) and g2(l) that of chi_p(m) chi_q(l/m);  *)
(* the representation formulas 2 g = r_f + r_f2 and 2 g2 = r_f - r_f2        *)
(* (CN_REP_TOTAL_ODD, CN_REP_GENUS_ODD; CN_REP_TOTAL_EVEN for -4d) and the   *)
(* lattice series of each form (QFORM_DIRICHLET_SERIES: the row y = 0        *)
(* gives 2 chi_k(a) zeta_k(2s) / a^s, the other rows twice the sum of the    *)
(* slices S_y(s)) give the identities for s > 1 (CNP_GENUS_PRODUCT_S,        *)
(* CNP_TOTAL_PRODUCT_S, CNP_EVEN_PRODUCT_S, any k). The limit s -> 1+ is     *)
(* taken as in CLASSNO_PRODUCT_LIMIT (Baker/classno_product.ml) with the     *)
(* tools of Baker/qform_series.ml: the limits of the L-series                *)
(* (QFORM_SERIES_QCHAR_LIMIT, QFORM_SERIES_LSERIES_LIMIT; their characters   *)
(* are non-principal: a quadratic nonresidue modulo one prime factor of the  *)
(* modulus that is 1 modulo the other factors, CNP_QCHAR_NONRESIDUE), of     *)
(* zeta_k(2s) (QFORM_SERIES_ZETA_LIMIT), of a^-s (QFORM_SERIES_RPOW_LIMIT)   *)
(* and of the slice sums (QFORM_SERIES_SLICE_LIMIT), and the uniqueness of   *)
(* the limits (QFORM_SERIES_LIMIT_EQ). For -4d the character n -> chi_k(n)   *)
(* kchar4 d n is a Dirichlet character modulo 4 k d (KCHAR4_DIRICHLET,       *)
(* CN_DIRICHLET_CHARACTER_PRODUCT).                                          *)
(*                                                                           *)
(* Main results: CN_GENUS_PRODUCT_LIMIT, CN_TOTAL_PRODUCT_LIMIT,             *)
(* CN_TOTAL_PRODUCT_LIMIT_EVEN; CNP_EVEN_PRODUCT_LIMIT (the even identity    *)
(* for any second form (2, b2, c2) with the total representation formula),   *)
(* CNP_GENUS_PRODUCT_S, CNP_TOTAL_PRODUCT_S, CNP_EVEN_PRODUCT_S (the         *)
(* identities for s > 1), CNP_QCHAR_NONRESIDUE, CNP_QCHAR_NONPRINCIPAL_MUL;  *)
(* helper names CNP_*.                                                       *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (form_classno, qform_rep),                    *)
(* Baker/classno_chardefs.ml (qchar, zeta_coprime, qform_slice,              *)
(* QCHAR_1), Baker/cn_defs.ml (kchar4), Baker/cn_rep.ml                      *)
(* (CN_REP_TOTAL_ODD, CN_REP_GENUS_ODD), Baker/cn_rep_even.ml                *)
(* (CN_REP_TOTAL_EVEN), Baker/qform_series.ml (QFORM_DIRICHLET_SERIES,       *)
(* QFORM_SERIES_SUMS_COMBINE, QFORM_SERIES_QCHAR_BOUNDED,                    *)
(* QFORM_SERIES_LIMIT_EQ, QFORM_SERIES_LSERIES_LIMIT,                        *)
(* QFORM_SERIES_QCHAR_LIMIT, QFORM_SERIES_ZETA_LIMIT,                        *)
(* QFORM_SERIES_RPOW_LIMIT, QFORM_SERIES_SLICE_LIMIT),                       *)
(* Baker/cn_gauss_even.ml (KCHAR4_DIRICHLET, CN_KCHAR4_1,                    *)
(* CN_DIRICHLET_CHARACTER_PRODUCT), Baker/classno_series_lib.ml              *)
(* (DIRICHLET_SERIES_PRODUCT), Baker/classno_series.ml (QCHAR_DIRICHLET,     *)
(* CLASSNO_SERIES_DIVISOR_CHAR, CLASSNO_SERIES_QCHAR_BOUND, _RMUL, _LMUL),   *)
(* Baker/classno_gauss.ml (CLASSNO_GAUSS_ODD_MOD4); Library/primitive.ml     *)
(* (QUADRATIC_NONRESIDUE_EXISTS), Library/pocklington.ml                     *)
(* (CHINESE_REMAINDER_USUAL), Library/jacobi.ml (JACOBI_PRIME, JACOBI_CONG), *)
(* 100/dirichlet.ml (dirichlet_character, chi_0, Lfunction).                 *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files, 100/dirichlet.ml before *)
(* Multivariate/gamma.ml), so that the file also loads alone.                *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Multivariate/gamma.ml";;
needs "Baker/qform_series.ml";;
needs "Baker/cn_rep.ml";;
needs "Baker/cn_rep_even.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Real characters: values, quadratic nonresidues in prescribed residue      *)
(* classes, non-principal characters, the Kronecker symbol kchar4.           *)
(* ------------------------------------------------------------------------- *)

let CNP_QCHAR_CONG_1 = prove
 (`!m n. (n == 1) (mod m) ==> qchar m n = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[qchar] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP JACOBI_CONG) THEN
  REWRITE_TAC[JACOBI_1; int_of_num_th]);;

(* A quadratic nonresidue modulo the odd prime r which is 1 modulo m         *)
(* (QUADRATIC_NONRESIDUE_EXISTS and the Chinese remainder theorem).          *)
let CNP_QCHAR_NONRESIDUE = prove
 (`!r m. prime r /\ ODD r /\ coprime(r,m)
         ==> ?n. qchar r n = -- &1 /\ (n == 1) (mod m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `3 <= r` MP_TAC THENL
   [MP_TAC(SPEC `r:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `r = 2` THENL
     [UNDISCH_TAC `ODD r` THEN ASM_REWRITE_TAC[ARITH]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM QUADRATIC_NONRESIDUE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`r:num`; `m:num`; `a:num`; `1`] CHINESE_REMAINDER_USUAL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[qchar] THEN
  SUBGOAL_THEN `jacobi(n,r) = jacobi(a,r)` SUBST1_TAC THENL
   [MATCH_MP_TAC JACOBI_CONG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[JACOBI_PRIME] THEN
  SUBGOAL_THEN `~((r:num) divides a)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[PRIME_COPRIME_EQ]; ALL_TAC] THEN
  REWRITE_TAC[int_neg_th; int_of_num_th]);;

let CNP_NONPRINCIPAL_MINUS1 = prove
 (`!d f n. f n = -- &1 ==> ~((\n. Cx(f n)) = chi_0 d)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM `n:num`) THEN
  ASM_REWRITE_TAC[chi_0] THEN COND_CASES_TAC THEN
  REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC);;

let CNP_QCHAR_NONPRINCIPAL_MUL = prove
 (`!m r. prime r /\ ODD r /\ coprime(r,m)
         ==> ~((\n. Cx(qchar (m * r) n)) = chi_0 (m * r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:num`; `m:num`] CNP_QCHAR_NONRESIDUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m * r:num`; `qchar (m * r)`; `n:num`]
    CNP_NONPRINCIPAL_MINUS1) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[CLASSNO_SERIES_QCHAR_RMUL] THEN
  ASM_SIMP_TAC[CNP_QCHAR_CONG_1] THEN REAL_ARITH_TAC);;

let CNP_KCHAR4_BOUND = prove
 (`!d n. abs(kchar4 d n) <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kchar4] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_POS] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NEG; REAL_ABS_NUM;
              REAL_POW_ONE; REAL_MUL_LID] THEN
  MP_TAC(SPECL [`d:num`; `n:num`] JACOBI_BOUND) THEN
  REWRITE_TAC[int_le; int_abs_th; int_of_num_th]);;

let CNP_KCHAR4_QCHAR_BOUNDED = prove
 (`!k d. ?B. !n. abs(qchar k n * kchar4 d n) <= B`,
  REPEAT GEN_TAC THEN EXISTS_TAC `&1` THEN GEN_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; CLASSNO_SERIES_QCHAR_BOUND; CNP_KCHAR4_BOUND];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Dirichlet convolutions of the products of characters.                 *)
(* ------------------------------------------------------------------------- *)

let CNP_DIVISOR_CHAR_GENUS = prove
 (`!k p q l.
     sum {m | m divides l} (\m. qchar (k * p) m * qchar (k * q) (l DIV m)) =
     qchar k l * sum {m | m divides l} (\m. qchar p m * qchar q (l DIV m))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[IN_ELIM_THM; DIVIDES_DIV_MULT] THEN DISCH_TAC THEN
  REWRITE_TAC[CLASSNO_SERIES_QCHAR_RMUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [SYM(ASSUME
    `l DIV m * m = l`)] THEN
  REWRITE_TAC[CLASSNO_SERIES_QCHAR_LMUL] THEN REAL_ARITH_TAC);;

let CNP_DIVISOR_CHAR_EVEN = prove
 (`!k d l.
     sum {m | m divides l} (\m. (qchar k m * kchar4 d m) * qchar k (l DIV m)) =
     qchar k l * sum {m | m divides l} (\m. kchar4 d m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[IN_ELIM_THM; DIVIDES_DIV_MULT] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [SYM(ASSUME
    `l DIV m * m = l`)] THEN
  REWRITE_TAC[CLASSNO_SERIES_QCHAR_LMUL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The discriminants of the forms.                                           *)
(* ------------------------------------------------------------------------- *)

let CNP_DISC_ODD = prove
 (`!p q. p MOD 4 = 1 /\ q MOD 4 = 3
         ==> (&4 * &1 * &((p * q + 1) DIV 4) - &1 pow 2):int = &(p * q) /\
             (&4 * &q * &((p + q) DIV 4) - &q pow 2):int = &(p * q)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p * q + 1) MOD 4 = 0 /\ (p + q) MOD 4 = 0` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    POP_ASSUM(K ALL_TAC)] THEN
  REWRITE_TAC[GSYM DIVIDES_MOD; DIVIDES_DIV_MULT] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
  CONV_TAC INT_RING);;

let CNP_MOD4_EVEN = prove
 (`!d. (prime d /\ d MOD 4 = 1 \/ (?p. prime p /\ ODD p /\ d = 2 * p))
       ==> d MOD 4 = 1 \/ d MOD 4 = 2`,
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC(2 * m) = m * 4 + 2`; MOD_MULT_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CNP_DISC_EVEN = prove
 (`!d. d MOD 4 = 1 \/ d MOD 4 = 2
       ==> &8 * (if d MOD 4 = 1 then &((d + 1) DIV 2) else &(d DIV 2)) -
           (if d MOD 4 = 1 then &2 else &0) pow 2 = (&4 * &d):int`,
  GEN_TAC THEN
  SUBGOAL_THEN `d MOD 2 = (d MOD 4) MOD 2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`d:num`; `2`; `2`] MOD_MOD) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN
    (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN REWRITE_TAC[ARITH_EQ] THENL
   [SUBGOAL_THEN `(d + 1) DIV 2 * 2 = d + 1` MP_TAC THENL
     [REWRITE_TAC[GSYM DIVIDES_DIV_MULT; DIVIDES_MOD] THEN
      ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC];
    SUBGOAL_THEN `d DIV 2 * 2 = d` MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM DIVIDES_DIV_MULT; DIVIDES_MOD]; ALL_TAC]] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] THEN
  INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The identities for s > 1.                                                 *)
(* ------------------------------------------------------------------------- *)

let CNP_GENUS_PRODUCT_S = prove
 (`!k p q s.
     prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
     form_classno (--(&(p * q))) = 2 /\ &1 < s
     ==> real_infsum (from 1) (\n. qchar (k * p * q) n / &n rpow s) *
         real_infsum (from 1) (\n. qchar k n / &n rpow s) +
         real_infsum (from 1) (\n. qchar (k * p) n / &n rpow s) *
         real_infsum (from 1) (\n. qchar (k * q) n / &n rpow s) =
         &2 * real_infsum (from 1)
               (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) +
         &2 * real_infsum (from 1)
               (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (&(p * q):int)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LT; LT_NZ; MULT_EQ_0; DE_MORGAN_THM] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNP_DISC_ODD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`qchar (k * p * q)`; `qchar k`; `s:real`]
    DIRICHLET_SERIES_PRODUCT) THEN
  ASM_REWRITE_TAC[QFORM_SERIES_QCHAR_BOUNDED; CLASSNO_SERIES_DIVISOR_CHAR] THEN
  DISCH_THEN(LABEL_TAC "u") THEN
  MP_TAC(ISPECL [`qchar (k * p)`; `qchar (k * q)`; `s:real`]
    DIRICHLET_SERIES_PRODUCT) THEN
  ASM_REWRITE_TAC[QFORM_SERIES_QCHAR_BOUNDED; CNP_DIVISOR_CHAR_GENUS] THEN
  DISCH_THEN(LABEL_TAC "v") THEN
  MP_TAC(ISPECL [`k:num`; `&1:int`; `&1:int`; `&((p * q + 1) DIV 4):int`;
                 `s:real`] QFORM_DIRICHLET_SERIES) THEN
  ASM_REWRITE_TAC[INT_LT_01] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; int_of_num_th; RPOW_ONE; QCHAR_1;
              REAL_DIV_1; REAL_MUL_LID] THEN
  DISCH_THEN(LABEL_TAC "w") THEN
  USE_THEN "u" (fun u -> USE_THEN "v" (fun v -> USE_THEN "w" (fun w ->
    MP_TAC(SPEC `&1`
      (MATCH_MP (MATCH_MP (MATCH_MP QFORM_SERIES_SUMS_COMBINE u) v) w))))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `l:num`] CN_REP_TOTAL_ODD) THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `l:num`] CN_REP_GENUS_ODD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
      `a - b = &2 * (x:real) ==> x = (a - b) / &2`)) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
      `a + b = &2 * (x:real) ==> x = (a + b) / &2`)) THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let CNP_TOTAL_PRODUCT_S = prove
 (`!k p q s.
     prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
     form_classno (--(&(p * q))) = 2 /\ &1 < s
     ==> real_infsum (from 1) (\n. qchar (k * p * q) n / &n rpow s) *
         real_infsum (from 1) (\n. qchar k n / &n rpow s) =
         real_infsum (from 1)
          (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) *
         (&1 + qchar k q / &q rpow s) +
         real_infsum (from 1)
          (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) s) +
         real_infsum (from 1) (qform_slice k (&q) (&q) (&((p + q) DIV 4)) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (&(p * q):int) /\ &0 < (&q:int)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LT; LT_NZ; MULT_EQ_0; DE_MORGAN_THM] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNP_DISC_ODD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `&1:int`; `&1:int`; `&((p * q + 1) DIV 4):int`;
                 `s:real`] QFORM_DIRICHLET_SERIES) THEN
  ASM_REWRITE_TAC[INT_LT_01] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; int_of_num_th; RPOW_ONE; QCHAR_1;
              REAL_DIV_1; REAL_MUL_LID] THEN
  DISCH_THEN(LABEL_TAC "u") THEN
  MP_TAC(ISPECL [`k:num`; `&q:int`; `&q:int`; `&((p + q) DIV 4):int`;
                 `s:real`] QFORM_DIRICHLET_SERIES) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[NUM_OF_INT_OF_NUM; int_of_num_th] THEN
  DISCH_THEN(LABEL_TAC "v") THEN
  MP_TAC(ISPECL [`qchar (k * p * q)`; `qchar k`; `s:real`]
    DIRICHLET_SERIES_PRODUCT) THEN
  ASM_REWRITE_TAC[QFORM_SERIES_QCHAR_BOUNDED; CLASSNO_SERIES_DIVISOR_CHAR] THEN
  DISCH_THEN(LABEL_TAC "w") THEN
  USE_THEN "u" (fun u -> USE_THEN "v" (fun v -> USE_THEN "w" (fun w ->
    MP_TAC(SPEC `&2`
      (MATCH_MP (MATCH_MP (MATCH_MP QFORM_SERIES_SUMS_COMBINE u) v) w))))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `l:num`] CN_REP_TOTAL_ODD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
      `a + b = &2 * (x:real) ==> x = (a + b) / &2`)) THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let CNP_EVEN_PRODUCT_S = prove
 (`!k d b2 c2 s.
     ~(d = 0) /\ &8 * c2 - b2 pow 2 = &4 * &d /\
     (!l. 1 <= l
          ==> &(qform_rep (&1) (&0) (&d) l) + &(qform_rep (&2) b2 c2 l) =
              &2 * sum {m | m divides l} (\m. kchar4 d m)) /\
     &1 < s
     ==> real_infsum (from 1) (\n. (qchar k n * kchar4 d n) / &n rpow s) *
         real_infsum (from 1) (\n. qchar k n / &n rpow s) =
         real_infsum (from 1)
          (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) *
         (&1 + qchar k 2 / &2 rpow s) +
         real_infsum (from 1) (qform_slice k (&1) (&0) (&d) s) +
         real_infsum (from 1) (qform_slice k (&2) b2 c2 s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&4 * &1 * &d - &0 pow 2 = (&4 * &d):int /\
                &4 * &2 * c2 - b2 pow 2 = (&4 * &d):int /\
                (&0:int) < &4 * &d`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [INT_ARITH_TAC;
      UNDISCH_TAC `&8 * c2 - b2 pow 2 = (&4 * &d):int` THEN INT_ARITH_TAC;
      REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LT] THEN
      UNDISCH_TAC `~(d = 0)` THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `&1:int`; `&0:int`; `&d:int`; `s:real`]
    QFORM_DIRICHLET_SERIES) THEN
  ASM_REWRITE_TAC[INT_LT_01] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; int_of_num_th; RPOW_ONE; QCHAR_1;
              REAL_DIV_1; REAL_MUL_LID] THEN
  DISCH_THEN(LABEL_TAC "u") THEN
  MP_TAC(ISPECL [`k:num`; `&2:int`; `b2:int`; `c2:int`; `s:real`]
    QFORM_DIRICHLET_SERIES) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; int_of_num_th] THEN
  DISCH_THEN(LABEL_TAC "v") THEN
  MP_TAC(ISPECL [`\n. qchar k n * kchar4 d n`; `qchar k`; `s:real`]
    DIRICHLET_SERIES_PRODUCT) THEN
  ASM_REWRITE_TAC[QFORM_SERIES_QCHAR_BOUNDED; CNP_KCHAR4_QCHAR_BOUNDED;
                  CNP_DIVISOR_CHAR_EVEN] THEN
  DISCH_THEN(LABEL_TAC "w") THEN
  USE_THEN "u" (fun u -> USE_THEN "v" (fun v -> USE_THEN "w" (fun w ->
    MP_TAC(SPEC `&2`
      (MATCH_MP (MATCH_MP (MATCH_MP QFORM_SERIES_SUMS_COMBINE u) v) w))))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
      `a + b = &2 * (x:real) ==> x = (a + b) / &2`)) THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The hypotheses on k, p, q and d: oddness, coprimality and the             *)
(* non-principal characters.                                                 *)
(* ------------------------------------------------------------------------- *)

let CNP_ODD_FACTS = prove
 (`!k k1 k2 p q.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\ coprime(k,p * q)
     ==> ODD k /\ ODD(k * p) /\ ODD(k * q) /\ ODD(k * p * q) /\
         ~((\n. Cx(qchar k n)) = chi_0 k) /\
         ~((\n. Cx(qchar (k * p) n)) = chi_0 (k * p)) /\
         ~((\n. Cx(qchar (k * q) n)) = chi_0 (k * q)) /\
         ~((\n. Cx(qchar (k * p * q) n)) = chi_0 (k * p * q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ODD k /\ ODD p /\ ODD q` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((\n. Cx(qchar k n)) = chi_0 k)` ASSUME_TAC THENL
   [UNDISCH_TAC `ODD k` THEN UNDISCH_TAC `k = k1 * k2` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ODD_MULT] THEN STRIP_TAC THEN
    MATCH_MP_TAC CNP_QCHAR_NONPRINCIPAL_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `k = k1 * k2` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `~(p:num = q)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `p MOD 4 = 1` THEN
    ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(p,k) /\ coprime(q,k) /\ coprime(q,k * p)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `coprime(q,p)` MP_TAC THENL
     [MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `coprime(k,p * q)` THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ODD_MULT] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CNP_QCHAR_NONPRINCIPAL_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CNP_QCHAR_NONPRINCIPAL_MUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MULT_ASSOC] THEN
    MATCH_MP_TAC CNP_QCHAR_NONPRINCIPAL_MUL THEN ASM_REWRITE_TAC[]]);;

let CNP_EVEN_FACTS = prove
 (`!k k1 k2 d.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     (d MOD 4 = 1 \/ d MOD 4 = 2) /\ coprime(k,d)
     ==> ODD k /\ ~(d = 0) /\ coprime(k,2) /\ coprime(k,4 * d) /\
         ~((\n. Cx(qchar k n)) = chi_0 k) /\
         dirichlet_character (k * 4 * d) (\n. Cx(qchar k n * kchar4 d n)) /\
         ~((\n. Cx(qchar k n * kchar4 d n)) = chi_0 (k * 4 * d))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `ODD k` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `0 MOD 4 = 1 \/ 0 MOD 4 = 2` THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(k,2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COPRIME_2]; ALL_TAC] THEN
  SUBGOAL_THEN `coprime(k,4 * d)` ASSUME_TAC THENL
   [SUBST1_TAC(ARITH_RULE `4 * d = 2 * 2 * d`) THEN
    ASM_REWRITE_TAC[COPRIME_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((\n. Cx(qchar k n)) = chi_0 k) /\
    ?n0. qchar k n0 = -- &1 /\ (n0 == 1) (mod (4 * d))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ODD k` THEN UNDISCH_TAC `coprime(k,4 * d)` THEN
    UNDISCH_TAC `k = k1 * k2` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ODD_MULT] THEN
    DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `coprime(k2,k1)` ASSUME_TAC THENL
     [MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CNP_QCHAR_NONPRINCIPAL_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`k1:num`; `k2 * 4 * d`] CNP_QCHAR_NONRESIDUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `coprime(k1 * k2,4 * d)` THEN
      UNDISCH_TAC `coprime(k2,k1)` THEN SPEC_TAC(`4 * d`,`e:num`) THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(n0 == 1) (mod k2) /\ (n0 == 1) (mod (4 * d))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(n0 == 1) (mod (k2 * 4 * d))` THEN
      SPEC_TAC(`4 * d`,`e:num`) THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CLASSNO_SERIES_QCHAR_RMUL; CNP_QCHAR_CONG_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `k = k1 * k2` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `kchar4 d n0 = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`4 * d`; `\n. Cx(kchar4 d n)`; `n0:num`; `1`]
      DIRICHLET_CHARACTER_CONG) THEN
    ASM_SIMP_TAC[KCHAR4_DIRICHLET; CX_INJ; CN_KCHAR4_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dirichlet_character (k * 4 * d) (\n. Cx(qchar k n * kchar4 d n))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN
    MATCH_MP_TAC CN_DIRICHLET_CHARACTER_PRODUCT THEN
    ASM_SIMP_TAC[QCHAR_DIRICHLET; KCHAR4_DIRICHLET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k * 4 * d`; `\n. qchar k n * kchar4 d n`; `n0:num`]
    CNP_NONPRINCIPAL_MINUS1) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main results.                                                         *)
(* ------------------------------------------------------------------------- *)

let CN_GENUS_PRODUCT_LIMIT = prove
 (`!k k1 k2 p q.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
     coprime(k,p * q) /\ form_classno (--(&(p * q))) = 2
     ==> ?S. (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) (&1) real_sums S)
             (from 1) /\
             Lfunction (\n. Cx(qchar k n)) *
             Lfunction (\n. Cx(qchar (k * p * q) n)) +
             Lfunction (\n. Cx(qchar (k * p) n)) *
             Lfunction (\n. Cx(qchar (k * q) n)) =
             Cx(&2 * (zeta_coprime k + S))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `p:num`; `q:num`]
    CNP_ODD_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`] QFORM_SERIES_SLICE_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "slice")] THEN
  UNDISCH_TAC `k = k1 * k2` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNP_DISC_ODD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < (&(p * q):int)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LT; LT_NZ; MULT_EQ_0; DE_MORGAN_THM] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  REMOVE_THEN "slice" (MP_TAC o SPECL
    [`&1:int`; `&1:int`; `&((p * q + 1) DIV 4):int`]) THEN
  ASM_REWRITE_TAC[INT_LT_01; NUM_OF_INT_OF_NUM; COPRIME_1] THEN
  STRIP_TAC THEN
  EXISTS_TAC
   `real_infsum (from 1)
     (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) (&1))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `k:num` QFORM_SERIES_QCHAR_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(SPEC `k * p * q:num` QFORM_SERIES_QCHAR_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(SPEC `k * p:num` QFORM_SERIES_QCHAR_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L3:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(SPEC `k * q:num` QFORM_SERIES_QCHAR_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L4:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  MATCH_MP_TAC QFORM_SERIES_LIMIT_EQ THEN
  EXISTS_TAC
   `\s. real_infsum (from 1) (\n. qchar k n / &n rpow s) *
        real_infsum (from 1) (\n. qchar (k * p * q) n / &n rpow s) +
        real_infsum (from 1) (\n. qchar (k * p) n / &n rpow s) *
        real_infsum (from 1) (\n. qchar (k * q) n / &n rpow s)` THEN
  EXISTS_TAC
   `\s. &2 * (real_infsum (from 1)
               (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) +
              real_infsum (from 1)
               (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) s))` THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`k:num`; `p:num`; `q:num`; `s:real`]
      CNP_GENUS_PRODUCT_S) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_MUL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_ADD THEN
    ASM_REWRITE_TAC[QFORM_SERIES_ZETA_LIMIT]]);;

let CN_TOTAL_PRODUCT_LIMIT = prove
 (`!k k1 k2 p q.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
     coprime(k,p * q) /\ form_classno (--(&(p * q))) = 2
     ==> ?S1 S2. (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) (&1)
                  real_sums S1) (from 1) /\
                 (qform_slice k (&q) (&q) (&((p + q) DIV 4)) (&1) real_sums S2)
                 (from 1) /\
                 Lfunction (\n. Cx(qchar k n)) *
                 Lfunction (\n. Cx(qchar (k * p * q) n)) =
                 Cx(zeta_coprime k * (&1 + qchar k q / &q) + S1 + S2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `p:num`; `q:num`]
    CNP_ODD_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`] QFORM_SERIES_SLICE_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "slice")] THEN
  UNDISCH_TAC `k = k1 * k2` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CNP_DISC_ODD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < (&(p * q):int) /\ &0 < (&q:int) /\ &0 < &q /\
                coprime(k,q)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LT; REAL_OF_NUM_LT; LT_NZ; MULT_EQ_0;
                DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    UNDISCH_TAC `coprime(k,p * q)` THEN SIMP_TAC[COPRIME_RMUL];
    ALL_TAC] THEN
  REMOVE_THEN "slice" (fun th ->
    MP_TAC(SPECL [`&q:int`; `&q:int`; `&((p + q) DIV 4):int`] th) THEN
    MP_TAC(SPECL [`&1:int`; `&1:int`; `&((p * q + 1) DIV 4):int`] th)) THEN
  ASM_REWRITE_TAC[INT_LT_01; NUM_OF_INT_OF_NUM; COPRIME_1] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  EXISTS_TAC
   `real_infsum (from 1)
     (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) (&1))` THEN
  EXISTS_TAC
   `real_infsum (from 1) (qform_slice k (&q) (&q) (&((p + q) DIV 4)) (&1))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `k:num` QFORM_SERIES_QCHAR_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(SPEC `k * p * q:num` QFORM_SERIES_QCHAR_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM CX_MUL; CX_INJ] THEN
  MATCH_MP_TAC QFORM_SERIES_LIMIT_EQ THEN
  EXISTS_TAC
   `\s. real_infsum (from 1) (\n. qchar k n / &n rpow s) *
        real_infsum (from 1) (\n. qchar (k * p * q) n / &n rpow s)` THEN
  EXISTS_TAC
   `\s. real_infsum (from 1)
         (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) *
        (&1 + qchar k q / &q rpow s) +
        real_infsum (from 1)
         (qform_slice k (&1) (&1) (&((p * q + 1) DIV 4)) s) +
        real_infsum (from 1) (qform_slice k (&q) (&q) (&((p +
          q) DIV 4)) s)` THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`k:num`; `p:num`; `q:num`; `s:real`]
      CNP_TOTAL_PRODUCT_S) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[QFORM_SERIES_ZETA_LIMIT] THEN
      MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
      MATCH_MP_TAC QFORM_SERIES_RPOW_LIMIT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[]]]);;

(* The even identity for any second form (2, b2, c2) of discriminant -4d     *)
(* with the total representation formula.                                    *)
let CNP_EVEN_PRODUCT_LIMIT = prove
 (`!k k1 k2 d b2 c2.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     (d MOD 4 = 1 \/ d MOD 4 = 2) /\ coprime(k,d) /\
     &8 * c2 - b2 pow 2 = &4 * &d /\
     (!l. 1 <= l
          ==> &(qform_rep (&1) (&0) (&d) l) + &(qform_rep (&2) b2 c2 l) =
              &2 * sum {m | m divides l} (\m. kchar4 d m))
     ==> ?S1 S2. (qform_slice k (&1) (&0) (&d) (&1) real_sums S1) (from 1) /\
                 (qform_slice k (&2) b2 c2 (&1) real_sums S2) (from 1) /\
                 Lfunction (\n. Cx(qchar k n)) *
                 Lfunction (\n. Cx(qchar k n * kchar4 d n)) =
                 Cx(zeta_coprime k * (&1 + qchar k 2 / &2) + S1 + S2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `d:num`] CNP_EVEN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`] QFORM_SERIES_SLICE_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "slice")] THEN
  UNDISCH_TAC `k = k1 * k2` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `&4 * &1 * &d - &0 pow 2 = (&4 * &d):int /\
                &4 * &2 * c2 - b2 pow 2 = (&4 * &d):int /\
                (&0:int) < &4 * &d /\ num_of_int(&4 * &d) = 4 * d`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [INT_ARITH_TAC;
      UNDISCH_TAC `&8 * c2 - b2 pow 2 = (&4 * &d):int` THEN INT_ARITH_TAC;
      REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LT] THEN
      UNDISCH_TAC `~(d = 0)` THEN ARITH_TAC;
      REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM]];
    ALL_TAC] THEN
  REMOVE_THEN "slice" (fun th ->
    MP_TAC(SPECL [`&2:int`; `b2:int`; `c2:int`] th) THEN
    MP_TAC(SPECL [`&1:int`; `&0:int`; `&d:int`] th)) THEN
  ASM_REWRITE_TAC[INT_LT_01; NUM_OF_INT_OF_NUM; COPRIME_1] THEN
  REWRITE_TAC[INT_OF_NUM_LT; ARITH] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `real_infsum (from 1) (qform_slice k (&1) (&0) (&d) (&1))` THEN
  EXISTS_TAC `real_infsum (from 1) (qform_slice k (&2) b2 c2 (&1))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `k:num` QFORM_SERIES_QCHAR_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k * 4 * d`; `\n. qchar k n * kchar4 d n`]
    QFORM_SERIES_LSERIES_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM CX_MUL; CX_INJ] THEN
  MATCH_MP_TAC QFORM_SERIES_LIMIT_EQ THEN
  EXISTS_TAC
   `\s. real_infsum (from 1) (\n. qchar k n / &n rpow s) *
        real_infsum (from 1) (\n. (qchar k n * kchar4 d n) / &n rpow s)` THEN
  EXISTS_TAC
   `\s. real_infsum (from 1)
         (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) *
        (&1 + qchar k 2 / &2 rpow s) +
        real_infsum (from 1) (qform_slice k (&1) (&0) (&d) s) +
        real_infsum (from 1) (qform_slice k (&2) b2 c2 s)` THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`k:num`; `d:num`; `b2:int`; `c2:int`; `s:real`]
      CNP_EVEN_PRODUCT_S) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[QFORM_SERIES_ZETA_LIMIT] THEN
      MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
      MATCH_MP_TAC QFORM_SERIES_RPOW_LIMIT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[]]]);;

let CN_TOTAL_PRODUCT_LIMIT_EVEN = prove
 (`!k k1 k2 d.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     (prime d /\ d MOD 4 = 1 \/ (?p. prime p /\ ODD p /\ d = 2 * p)) /\
     coprime(k,d) /\ form_classno (--(&4 * &d)) = 2
     ==> ?b2 c2 S1 S2.
           &8 * c2 - b2 pow 2 = &4 * &d /\
           (qform_slice k (&1) (&0) (&d) (&1) real_sums S1) (from 1) /\
           (qform_slice k (&2) b2 c2 (&1) real_sums S2) (from 1) /\
           Lfunction (\n. Cx(qchar k n)) *
           Lfunction (\n. Cx(qchar k n * kchar4 d n)) =
           Cx(zeta_coprime k * (&1 + qchar k 2 / &2) + S1 + S2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CNP_MOD4_EVEN) THEN
  MAP_EVERY EXISTS_TAC
   [`if d MOD 4 = 1 then (&2:int) else &0`;
    `if d MOD 4 = 1 then &((d + 1) DIV 2) else (&(d DIV 2):int)`] THEN
  REWRITE_TAC[MATCH_MP CNP_DISC_EVEN
    (ASSUME `d MOD 4 = 1 \/ d MOD 4 = 2`)] THEN
  MATCH_MP_TAC CNP_EVEN_PRODUCT_LIMIT THEN
  MAP_EVERY EXISTS_TAC [`k1:num`; `k2:num`] THEN
  REWRITE_TAC[MATCH_MP CNP_DISC_EVEN
    (ASSUME `d MOD 4 = 1 \/ d MOD 4 = 2`)] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC CN_REP_TOTAL_EVEN THEN ASM_REWRITE_TAC[]);;

prioritize_num();;
