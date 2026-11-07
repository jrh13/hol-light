(* ========================================================================= *)
(* The class number one problem: the product of two L-series at s = 1 as the *)
(* lattice series of the principal form, and the bound for its slices.       *)
(*                                                                           *)
(* Purpose: for k = 21, 33 and a prime d = 3 mod 4, d > k, with              *)
(* form_classno(-d) = 1, L(1, chi_k) L(1, chi_kd) = zeta_k(2) + S, where S   *)
(* is the sum over y >= 1 of the slices S_y(1) =                             *)
(* qform_slice k (&1) (&1) (&((d + 1) DIV 4)) (&1) y of the principal form   *)
(* f0 = (1, 1, (d + 1) DIV 4), the sums over all integers x of               *)
(* chi_k(f0(x,y)) / f0(x,y) (CLASSNO_PRODUCT_LIMIT: the identity (1) of      *)
(* Baker, Transcendental Number Theory, Ch. 5, sec. 2, for one class of      *)
(* forms, at s = 1; Baker and Wustholz, Logarithmic Forms and Diophantine    *)
(* Geometry, sec. 3.1), and abs S <=                                         *)
(* (4 pi / sqrt d) eta (1 + eta) / (1 - eta)^3 with                          *)
(* eta = exp(-pi sqrt(d) / k) for any sum S of the slices and any            *)
(* d = 3 mod 4 coprime to k (CLASSNO_SLICE_BOUND, without any class number   *)
(* hypothesis: the estimate of the terms A_r of the limit formula in Baker,  *)
(* Ch. 5, sec. 3, together with A_0 = 0 for k not a prime power).            *)
(* CLASSNO_SERIES_PRODUCT_S (any k, s > 1):                                  *)
(* L(s, chi_kd) L(s, chi_k) = zeta_k(2s) + T(s), T(s) the sum over y >= 1 of *)
(* the slices S_y(s).                                                        *)
(*                                                                           *)
(* Method: the results for a general positive definite form at the principal *)
(* form (1, 1, c), c = (d + 1) DIV 4, of discriminant -d                     *)
(* (CLASSNO_PRODUCT_DISC). For s > 1: the Dirichlet product                  *)
(* (DIRICHLET_SERIES_PRODUCT), the representation formula                    *)
(* (CLASSNO_REPRESENTATION, with prin_rep the representation numbers of the  *)
(* form: QFORM_REP_PRIN) and the lattice series of the form                  *)
(* (QFORM_DIRICHLET_SERIES). The limit s -> 1+: the sums of the slices       *)
(* (QFORM_SERIES_SLICE_LIMIT), the two L-series of the non-principal         *)
(* characters (QFORM_SERIES_QCHAR_LIMIT; QCHAR_NONPRINCIPAL for the          *)
(* squarefree moduli k, k d), zeta_k(2s) (QFORM_SERIES_ZETA_LIMIT) and the   *)
(* uniqueness of the limits (QFORM_SERIES_LIMIT_EQ). The slice bound is      *)
(* QFORM_SLICE_BOUND for k = 3 * 7, 3 * 11.                                  *)
(*                                                                           *)
(* Main results: CLASSNO_PRODUCT_LIMIT, CLASSNO_SLICE_BOUND,                 *)
(* CLASSNO_SERIES_PRODUCT_S; CLASSNO_PRODUCT_DISC.                           *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (form_classno, QFORM_REP_PRIN),               *)
(* Baker/classno_forms.ml (CLASSNO_PRINCIPAL_REDUCED),                       *)
(* Baker/classno_chardefs.ml (qchar, zeta_coprime, qform_slice,              *)
(* qform_kernel, QCHAR_1), Baker/classno_rep.ml (CLASSNO_REPRESENTATION),    *)
(* Baker/classno_series_lib.ml (DIRICHLET_SERIES_PRODUCT),                   *)
(* Baker/classno_series.ml (CLASSNO_SERIES_DIVISOR_CHAR),                    *)
(* Baker/classno_limit.ml (CLASSNO_LIMIT_C0, CLASSNO_LIMIT_PRIMES,           *)
(* CLASSNO_LIMIT_LE_MULT), Baker/classno_gauss.ml (QCHAR_NONPRINCIPAL),      *)
(* Baker/qform_limit.ml (QFORM_SLICE_BOUND), Baker/qform_series.ml           *)
(* (QFORM_DIRICHLET_SERIES, QFORM_SERIES_SUMS_COMBINE,                       *)
(* QFORM_SERIES_QCHAR_BOUNDED, QFORM_SERIES_SLICE_LIMIT,                     *)
(* QFORM_SERIES_QCHAR_LIMIT, QFORM_SERIES_ZETA_LIMIT,                        *)
(* QFORM_SERIES_LIMIT_EQ); 100/dirichlet.ml (Lfunction),                     *)
(* Library/pocklington.ml (SQUAREFREE_MUL, PRIME_IMP_SQUAREFREE),            *)
(* Library/prime.ml (DISTINCT_PRIME_COPRIME).                                *)
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

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The principal form (1, 1, (d + 1) DIV 4) has discriminant -d.             *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_PRODUCT_DISC = prove
 (`!d. d MOD 4 = 3 ==> (&4 * &1 * &((d + 1) DIV 4) - &1 pow 2):int = &d`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP CLASSNO_PRINCIPAL_REDUCED) THEN
  INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The identity for s > 1: L(s,chi_kd) L(s,chi_k) = zeta_k(2s) + T(s).       *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_PRODUCT_S = prove
 (`!k d s.
     prime d /\ d MOD 4 = 3 /\ 3 < d /\ form_classno (--(&d)) = 1 /\ &1 < s
     ==> real_infsum (from 1) (\n. qchar (k * d) n / &n rpow s) *
         real_infsum (from 1) (\n. qchar k n / &n rpow s) =
         real_infsum (from 1)
          (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) +
         real_infsum (from 1)
          (qform_slice k (&1) (&1) (&((d + 1) DIV 4)) s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLASSNO_PRODUCT_DISC) THEN
  MP_TAC(ISPECL [`k:num`; `&1:int`; `&1:int`; `&((d + 1) DIV 4):int`;
                 `s:real`] QFORM_DIRICHLET_SERIES) THEN
  ASM_REWRITE_TAC[INT_LT_01; INT_OF_NUM_LT] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; int_of_num_th; RPOW_ONE; QCHAR_1;
              REAL_DIV_1; REAL_MUL_LID] THEN
  DISCH_THEN(LABEL_TAC "u") THEN
  MP_TAC(ISPECL [`qchar (k * d)`; `qchar k`; `s:real`]
    DIRICHLET_SERIES_PRODUCT) THEN
  ASM_REWRITE_TAC[QFORM_SERIES_QCHAR_BOUNDED; CLASSNO_SERIES_DIVISOR_CHAR] THEN
  DISCH_THEN(LABEL_TAC "w") THEN
  USE_THEN "u" (fun u -> USE_THEN "w" (fun w ->
    MP_TAC(SPEC `&2`
      (MATCH_MP (MATCH_MP (MATCH_MP QFORM_SERIES_SUMS_COMBINE u)
         (ISPEC `from 1` REAL_SERIES_0)) w)))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_FROM] THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`d:num`; `l:num`] CLASSNO_REPRESENTATION) THEN
    ASM_REWRITE_TAC[QFORM_REP_PRIN] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div; REAL_ADD_RID] THEN REWRITE_TAC[REAL_MUL_AC];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The limit s -> 1+ for k = 21, 33.                                         *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_PRODUCT_LIMIT = prove
 (`!k d. (k = 21 \/ k = 33) /\ prime d /\ d MOD 4 = 3 /\ k < d /\
        form_classno (--(&d)) = 1
        ==> ?S. (qform_slice k (&1) (&1) (&((d + 1) DIV 4)) (&1) real_sums S)
                (from 1) /\
                Lfunction (\n. Cx(qchar k n)) *
                Lfunction (\n. Cx(qchar (k * d) n)) =
                Cx(zeta_coprime k + S)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLASSNO_PRODUCT_DISC) THEN
  SUBGOAL_THEN `?k1 k2. k1 * k2 = k /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\
                        ODD k /\ ODD(k * d) /\ 3 < d /\ coprime(k,d)`
  (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC)) THENL
   [SUBGOAL_THEN `ODD d /\ coprime(k,d)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN
        ASM_REWRITE_TAC[ARITH_EQ] THEN
        DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
        REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH];
        ONCE_REWRITE_TAC[COPRIME_SYM] THEN
        ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
        UNDISCH_TAC `k < d:num` THEN
        FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl))
        THEN ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ODD_MULT] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl))
    THENL
     [MAP_EVERY EXISTS_TAC [`3`; `7`]; MAP_EVERY EXISTS_TAC [`3`; `11`]] THEN
    REWRITE_TAC[CLASSNO_LIMIT_PRIMES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `squarefree k /\ squarefree(k * d)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SQUAREFREE_MUL] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> concl th = `k1 * k2 = k`)) THEN
    ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE; DISTINCT_PRIME_COPRIME];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`] QFORM_SERIES_SLICE_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`&1:int`; `&1:int`; `&((d + 1) DIV 4):int`]) THEN
  ASM_REWRITE_TAC[INT_LT_01; NUM_OF_INT_OF_NUM; COPRIME_1; INT_OF_NUM_LT] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  EXISTS_TAC
   `real_infsum (from 1)
     (qform_slice k (&1) (&1) (&((d + 1) DIV 4)) (&1))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `k:num` QFORM_SERIES_QCHAR_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC QCHAR_NONPRINCIPAL THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(SPEC `k * d:num` QFORM_SERIES_QCHAR_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC QCHAR_NONPRINCIPAL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `d:num` THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CLASSNO_LIMIT_LE_MULT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:real`
    (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  MATCH_MP_TAC QFORM_SERIES_LIMIT_EQ THEN
  EXISTS_TAC
   `\s. real_infsum (from 1) (\n. qchar (k * d) n / &n rpow s) *
        real_infsum (from 1) (\n. qchar k n / &n rpow s)` THEN
  EXISTS_TAC
   `\s. real_infsum (from 1)
          (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) +
        real_infsum (from 1)
          (qform_slice k (&1) (&1) (&((d + 1) DIV 4)) s)` THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC CLASSNO_SERIES_PRODUCT_S THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REALLIM_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_ADD THEN ASM_REWRITE_TAC[QFORM_SERIES_ZETA_LIMIT]]);;

(* ------------------------------------------------------------------------- *)
(* The bound for the sum of the slices (k = 3 * 7, 3 * 11).                  *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SLICE_BOUND = prove
 (`!k d S. (k = 21 \/ k = 33) /\ d MOD 4 = 3 /\ coprime(k,d) /\
          (qform_slice k (&1) (&1) (&((d + 1) DIV 4)) (&1) real_sums S) (from 1)
          ==> abs S <= &4 * pi / sqrt(&d) * exp(--(pi * sqrt(&d) / &k)) *
                       (&1 + exp(--(pi * sqrt(&d) / &k))) /
                       (&1 - exp(--(pi * sqrt(&d) / &k))) pow 3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM qform_kernel] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CLASSNO_PRODUCT_DISC) THEN
  SUBGOAL_THEN `?k1 k2. k1 * k2 = k /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\
                        ODD k`
  (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC)) THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THENL
     [MAP_EVERY EXISTS_TAC [`3`; `7`]; MAP_EVERY EXISTS_TAC [`3`; `11`]] THEN
    REWRITE_TAC[CLASSNO_LIMIT_PRIMES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `&1:int`; `&1:int`;
                `&((d + 1) DIV 4):int`; `S:real`] QFORM_SLICE_BOUND) THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; COPRIME_1; INT_LT_01;
                  int_of_num_th; REAL_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[INT_OF_NUM_LT] THEN
  MP_TAC(SPEC `d:num` CLASSNO_LIMIT_C0) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;
