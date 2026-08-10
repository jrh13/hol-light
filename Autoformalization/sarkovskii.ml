(* ========================================================================= *)
(* Sarkovskii's theorem for continuous maps of the real line.                *)
(*                                                                           *)
(* The interval-covering proof is based on Section 1.10 of:                  *)
(* R. L. Devaney, "An Introduction to Chaotic Dynamical Systems", 2nd ed.    *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Periodic points and their least periods.                                  *)
(* ------------------------------------------------------------------------- *)

let periodic_point = new_definition
 `periodic_point (f:A->A) n x <=> ITER n f x = x`;;

let minimal_period = new_definition
 `minimal_period (f:A->A) n x <=>
        0 < n /\
        periodic_point f n x /\
        !m. 0 < m /\ m < n ==> ~periodic_point f m x`;;

let has_period = new_definition
 `has_period (f:A->A) n <=> ?x. minimal_period f n x`;;

let PERIODIC_POINT_0 = prove
 (`!f:A->A x. periodic_point f 0 x`,
  REWRITE_TAC[periodic_point; ITER]);;

let PERIODIC_POINT_MULTIPLE = prove
 (`!f:A->A n x m.
        periodic_point f n x ==> periodic_point f (m * n) x`,
  REWRITE_TAC[periodic_point] THEN
  MESON_TAC[ITER_FIXPOINT; ITER_MUL]);;

let PERIODIC_POINT_ITER_ADD = prove
 (`!f:A->A n x m.
        periodic_point f n x ==> ITER (n + m) f x = ITER m f x`,
  REWRITE_TAC[periodic_point] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(n:num) + m = m + n` SUBST1_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[GSYM ITER_ADD] THEN ASM_REWRITE_TAC[]]);;

let PERIODIC_POINT_ITERATE = prove
 (`!f:A->A n x i.
        periodic_point f n x
        ==> periodic_point f n (ITER i f x)`,
  REWRITE_TAC[periodic_point; ITER_ADD] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PERIODIC_POINT_ITER_ADD THEN
  ASM_REWRITE_TAC[periodic_point]);;

let PERIODIC_POINTS_IMAGE_INJ = prove
 (`!f:A->A n x y.
        0 < n /\
        periodic_point f n x /\
        periodic_point f n y
        ==> (f x = f y <=> x = y)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "positive periodx periody" THEN
  EQ_TAC THENL
   [DISCH_THEN(LABEL_TAC "sameimage") THEN
    SUBGOAL_THEN `(n:num) - 1 + 1 = n` (LABEL_TAC "sum") THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ITER (n - 1) (f:A->A) (f x) = x`
    (LABEL_TAC "backx") THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ITER_1] THEN
      REWRITE_TAC[ITER_ADD] THEN
      USE_THEN "sum" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "periodx"
       (ACCEPT_TAC o REWRITE_RULE[periodic_point]);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ITER (n - 1) (f:A->A) (f y) = y`
    (LABEL_TAC "backy") THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ITER_1] THEN
      REWRITE_TAC[ITER_ADD] THEN
      USE_THEN "sum" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "periody"
       (ACCEPT_TAC o REWRITE_RULE[periodic_point]);
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    SIMP_TAC[]]);;

let PERIODIC_POINTS_ITER_INJ = prove
 (`!f:A->A n k x y.
        0 < (n:num) /\
        periodic_point (f:A->A) n (x:A) /\
        periodic_point f n (y:A)
        ==> (ITER (k:num) f x = ITER k f y <=> x = y)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[ITER];
    POP_ASSUM(LABEL_TAC "IH") THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    INTRO_TAC "positive periodx periody" THEN
    REWRITE_TAC[ITER] THEN
    MP_TAC(ISPECL
     [`f:A->A`; `n:num`; `ITER (k:num) (f:A->A) (x:A)`;
      `ITER (k:num) (f:A->A) (y:A)`]
     PERIODIC_POINTS_IMAGE_INJ) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "positive" ACCEPT_TAC;
        MATCH_MP_TAC PERIODIC_POINT_ITERATE THEN
        USE_THEN "periodx" ACCEPT_TAC;
        MATCH_MP_TAC PERIODIC_POINT_ITERATE THEN
        USE_THEN "periody" ACCEPT_TAC];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    USE_THEN "IH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let PERIODIC_POINT_ITER = prove
 (`!f:A->A k m x.
        periodic_point (ITER k f) m x <=>
        periodic_point f (m * k) x`,
  REWRITE_TAC[periodic_point; ITER_MUL]);;

let PERIODIC_POINT_ITER_MOD = prove
 (`!f:A->A n x m.
        0 < n /\ periodic_point f n x
        ==> ITER m f x = ITER (m MOD n) f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `n:num`] DIVISION) THEN
  ANTS_TAC THENL
   [ASM_ARITH_TAC;
    INTRO_TAC "division remainder"] THEN
  SUBGOAL_THEN
   `periodic_point (f:A->A) (m DIV n * n) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PERIODIC_POINT_MULTIPLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ITER (m DIV n * n + m MOD n) (f:A->A) x` THEN
  CONJ_TAC THENL
   [USE_THEN "division" (fun th ->
      ACCEPT_TAC(BETA_RULE
       (AP_TERM `\k:num. ITER k (f:A->A) x` th)));
    MATCH_MP_TAC PERIODIC_POINT_ITER_ADD THEN ASM_REWRITE_TAC[]]);;

let PERIODIC_POINT_ITER_EQ = prove
 (`!f:A->A n x i j.
        periodic_point f n x /\
        i <= j /\
        j <= n /\
        ITER i f x = ITER j f x
        ==> periodic_point f (j - i) x`,
  REWRITE_TAC[periodic_point] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ITER ((n:num) - i) (f:A->A) (ITER i f x) =
    ITER (n - i) f (ITER j f x)`
  MP_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[ITER_ADD]] THEN
  SUBGOAL_THEN
   `((n:num) - i) + i = n /\
    (n - i) + j = n + (j - i)`
  STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `ITER (n + (j - i)) (f:A->A) x = ITER (j - i) f x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PERIODIC_POINT_ITER_ADD THEN
    ASM_REWRITE_TAC[periodic_point];
    ASM_MESON_TAC[]]);;

let MINIMAL_PERIOD_DIVISIBILITY = prove
 (`!f:A->A n x.
        minimal_period f n x <=>
        0 < n /\ !m. periodic_point f m x <=> n divides m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[minimal_period] THEN EQ_TAC THENL
   [INTRO_TAC "positive period least" THEN
    CONJ_TAC THENL
     [USE_THEN "positive" ACCEPT_TAC;
      X_GEN_TAC `m:num` THEN EQ_TAC THENL
       [DISCH_THEN(LABEL_TAC "mperiod") THEN
        SUBGOAL_THEN
         `periodic_point (f:A->A) (m MOD n) x`
        (LABEL_TAC "remainder") THENL
         [MP_TAC(ISPECL [`f:A->A`; `n:num`; `x:A`; `m:num`]
           PERIODIC_POINT_ITER_MOD) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[];
            DISCH_THEN(LABEL_TAC "iterate")] THEN
          REWRITE_TAC[periodic_point] THEN
          USE_THEN "iterate" (fun th -> REWRITE_TAC[GSYM th]) THEN
          USE_THEN "mperiod"
           (ACCEPT_TAC o REWRITE_RULE[periodic_point]);
          ALL_TAC] THEN
        REWRITE_TAC[DIVIDES_MOD] THEN
        ASM_CASES_TAC `m MOD n = 0` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `0 < m MOD n /\ m MOD n < n`
        (LABEL_TAC "remainderbound") THENL
         [CONJ_TAC THENL
           [ASM_ARITH_TAC;
            ASM_REWRITE_TAC[MOD_LT_EQ_LT]];
          USE_THEN "least" (MP_TAC o SPEC `m MOD n`) THEN
          ASM_MESON_TAC[]];
        DISCH_THEN(LABEL_TAC "divides") THEN
        USE_THEN "divides" MP_TAC THEN REWRITE_TAC[divides] THEN
        DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
        ONCE_REWRITE_TAC[MULT_SYM] THEN
        MATCH_MP_TAC PERIODIC_POINT_MULTIPLE THEN
        USE_THEN "period" ACCEPT_TAC]];
    INTRO_TAC "positive periods" THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "positive" ACCEPT_TAC;
      USE_THEN "periods" (MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[DIVIDES_REFL];
      X_GEN_TAC `m:num` THEN
      INTRO_TAC "mpositive mlt" THEN
      DISCH_THEN(LABEL_TAC "mperiod") THEN
      USE_THEN "periods" (MP_TAC o SPEC `m:num`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_ARITH_TAC]]);;

let MINIMAL_PERIOD_POS = prove
 (`!f:A->A n x. minimal_period f n x ==> 0 < n`,
  SIMP_TAC[minimal_period]);;

let HAS_PERIOD_POS = prove
 (`!f:A->A n. has_period f n ==> 0 < n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_period] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A`
   (ACCEPT_TAC o MATCH_MP MINIMAL_PERIOD_POS)));;

let MINIMAL_PERIOD_PERIODIC = prove
 (`!f:A->A n x. minimal_period f n x ==> periodic_point f n x`,
  SIMP_TAC[minimal_period]);;

let MINIMAL_PERIOD_DIVIDES = prove
 (`!f:A->A n x m.
        minimal_period f n x
        ==> (periodic_point f m x <=> n divides m)`,
  SIMP_TAC[MINIMAL_PERIOD_DIVISIBILITY]);;

let MINIMAL_PERIOD_ITERATE = prove
 (`!f:A->A n x k.
        minimal_period f n x
        ==> minimal_period f n (ITER k f x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "minimal") THEN
  REWRITE_TAC[MINIMAL_PERIOD_DIVISIBILITY] THEN CONJ_TAC THENL
   [USE_THEN "minimal" (MP_TAC o MATCH_MP MINIMAL_PERIOD_POS) THEN
    ARITH_TAC;
    X_GEN_TAC `m:num` THEN EQ_TAC THENL
     [DISCH_THEN(LABEL_TAC "perioditerate") THEN
      SUBGOAL_THEN
       `ITER k (f:A->A) (ITER m f x) =
        ITER m f (ITER k f x)`
      (LABEL_TAC "commute") THENL
       [REWRITE_TAC[ITER_ADD] THEN
        SUBGOAL_THEN `(k:num) + m = m + k` SUBST1_TAC THENL
         [ARITH_TAC;
          REFL_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `ITER k (f:A->A) (ITER m f x) = ITER k f x`
      (LABEL_TAC "sameiterate") THENL
       [USE_THEN "commute" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "perioditerate"
         (ACCEPT_TAC o REWRITE_RULE[periodic_point]);
        ALL_TAC] THEN
      SUBGOAL_THEN `periodic_point (f:A->A) m x`
      (LABEL_TAC "period") THENL
       [REWRITE_TAC[periodic_point] THEN
        MP_TAC(ISPECL
         [`f:A->A`; `n:num`; `k:num`; `ITER m (f:A->A) (x:A)`; `x:A`]
         PERIODIC_POINTS_ITER_INJ) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [USE_THEN "minimal" (MP_TAC o MATCH_MP MINIMAL_PERIOD_POS) THEN
            ARITH_TAC;
            MATCH_MP_TAC PERIODIC_POINT_ITERATE THEN
            MATCH_MP_TAC MINIMAL_PERIOD_PERIODIC THEN
            USE_THEN "minimal" ACCEPT_TAC;
            MATCH_MP_TAC MINIMAL_PERIOD_PERIODIC THEN
            USE_THEN "minimal" ACCEPT_TAC];
          DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
          DISCH_THEN MATCH_MP_TAC THEN
          USE_THEN "sameiterate" ACCEPT_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:A->A`; `n:num`; `x:A`; `m:num`]
       MINIMAL_PERIOD_DIVIDES) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(LABEL_TAC "divides") THEN
      MATCH_MP_TAC PERIODIC_POINT_ITERATE THEN
      MP_TAC(ISPECL [`f:A->A`; `n:num`; `x:A`; `m:num`]
       MINIMAL_PERIOD_DIVIDES) THEN
      ASM_REWRITE_TAC[]]]);;

let MINIMAL_PERIOD_ITER_INJ_LE = prove
 (`!f:A->A n x i j.
        minimal_period f n x /\
        i <= j /\
        j < n /\
        ITER i f x = ITER j f x
        ==> i = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `periodic_point (f:A->A) (j - i) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL
     [`f:A->A`; `n:num`; `x:A`; `i:num`; `j:num`]
     PERIODIC_POINT_ITER_EQ) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MINIMAL_PERIOD_PERIODIC THEN ASM_REWRITE_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n:num) divides (j - i)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:A->A`; `n:num`; `x:A`; `j - i:num`]
      MINIMAL_PERIOD_DIVIDES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP DIVIDES_LE
    (ASSUME `(n:num) divides (j - i)`)) THEN
  ASM_ARITH_TAC);;

let MINIMAL_PERIOD_ITER_INJ = prove
 (`!f:A->A n x i j.
        minimal_period f n x /\
        i < n /\
        j < n
        ==> (ITER i f x = ITER j f x <=> i = j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `(i:num) <= j` THENL
     [MATCH_MP_TAC(ISPECL
       [`f:A->A`; `n:num`; `x:A`; `i:num`; `j:num`]
       MINIMAL_PERIOD_ITER_INJ_LE) THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(j:num) = i` MP_TAC THENL
       [MATCH_MP_TAC(ISPECL
         [`f:A->A`; `n:num`; `x:A`; `j:num`; `i:num`]
         MINIMAL_PERIOD_ITER_INJ_LE) THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        SIMP_TAC[]]];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let MINIMAL_PERIOD_UNIQUE = prove
 (`!f:A->A m n x.
        minimal_period f m x /\ minimal_period f n x
        ==> m = n`,
  REWRITE_TAC[MINIMAL_PERIOD_DIVISIBILITY] THEN
  MESON_TAC[DIVIDES_ANTISYM]);;

let PERIODIC_POINT_IMP_MINIMAL_PERIOD = prove
 (`!f:A->A x m.
        0 < m /\ periodic_point f m x
        ==> ?n. n divides m /\ minimal_period f n x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(=):A->A->bool`; `f:A->A`; `x:A`]
        ORDER_EXISTENCE_ITER) THEN
  ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[MINIMAL_PERIOD_DIVISIBILITY; periodic_point] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ASM_REWRITE_TAC[GSYM periodic_point];
    ASM_CASES_TAC `n = 0` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
      ASM_REWRITE_TAC[GSYM periodic_point; DIVIDES_ZERO] THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

let MINIMAL_PERIOD_ITER = prove
 (`!f:A->A n x k.
        minimal_period f n x
        ==> minimal_period (ITER k f) (n DIV gcd(n,k)) x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MINIMAL_PERIOD_DIVISIBILITY; PERIODIC_POINT_ITER] THEN
  FIRST_X_ASSUM
   (STRIP_ASSUME_TAC o REWRITE_RULE[MINIMAL_PERIOD_DIVISIBILITY]) THEN
  SUBGOAL_THEN `gcd(n,k) divides n` ASSUME_TAC THENL
   [MESON_TAC[DIVIDES_GCD; DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `n DIV gcd(n,k) * gcd(n,k) = n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM DIVIDES_DIV_MULT];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n DIV gcd(n,k) = 0` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `n DIV gcd(n,k) * gcd(n,k) = n` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
    X_GEN_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`n:num`; `gcd(n,k)`; `m:num`]
      DIVIDES_DIV_DIVIDES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th])] THEN
    REWRITE_TAC[DIVIDES_LMUL_GCD; MULT_SYM]]);;

let HAS_PERIOD_ITER = prove
 (`!f:A->A n k.
        has_period f n
        ==> has_period (ITER k f) (n DIV gcd(n,k))`,
  REWRITE_TAC[has_period] THEN MESON_TAC[MINIMAL_PERIOD_ITER]);;

let DIVIDES_NOT_SUB = prove
 (`!d m r.
        d divides m /\ 0 < r /\ r < d /\ r <= m
        ==> ~(d divides (m - r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(LABEL_TAC "subdivides") THEN
  SUBGOAL_THEN `(d:num) divides (m - (m - r))`
  (LABEL_TAC "difference") THENL
   [MATCH_MP_TAC DIVIDES_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:num) - (m - r) = r`
  (LABEL_TAC "subtract") THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "subtract" (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  USE_THEN "difference" (MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_ARITH_TAC);;

let SUB_NOT_DIVIDES = prove
 (`!m r.
        0 < r /\ 2 * r < m
        ==> ~((m - r) divides m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(LABEL_TAC "divides") THEN
  MP_TAC(ISPECL [`m - r:num`; `m:num`; `r:num`]
   DIVIDES_NOT_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[DIVIDES_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Ordered finite orbits.                                                    *)
(* ------------------------------------------------------------------------- *)

let MINIMAL_PERIOD_ORBIT_CARD = prove
 (`!f:A->A n x.
        minimal_period f n x
        ==> CARD (IMAGE (\i. ITER i f x) {i | i < n}) = n`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `CARD {i:num | i < n}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`f:A->A`; `n:num`; `x:A`; `i:num`; `j:num`]
        MINIMAL_PERIOD_ITER_INJ) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FINITE_NUMSEG_LT]];
    REWRITE_TAC[CARD_NUMSEG_LT]]);;

let MINIMAL_PERIOD_ORBIT_IMAGE = prove
 (`!f:A->A n x y.
        minimal_period f n x /\
        y IN IMAGE (\i. ITER i f x) {i | i < n}
        ==> f y IN IMAGE (\i. ITER i f x) {i | i < n}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "minimal") MP_TAC) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `0 < (n:num)` ASSUME_TAC THENL
   [USE_THEN "minimal" (MP_TAC o MATCH_MP MINIMAL_PERIOD_POS) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `periodic_point (f:A->A) n x` ASSUME_TAC THENL
   [MATCH_MP_TAC MINIMAL_PERIOD_PERIODIC THEN
    USE_THEN "minimal" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ITER (SUC i) (f:A->A) x = ITER ((SUC i) MOD n) f x`
  (LABEL_TAC "reduce") THENL
   [MATCH_MP_TAC PERIODIC_POINT_ITER_MOD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(SUC i) MOD n < n` (LABEL_TAC "index") THENL
   [REWRITE_TAC[MOD_LT_EQ_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f(ITER i (f:A->A) x) = ITER ((SUC i) MOD n) f x`
  (LABEL_TAC "step") THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT2 ITER)] THEN
    USE_THEN "reduce" ACCEPT_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(SUC i) MOD n` THEN CONJ_TAC THENL
   [USE_THEN "step" ACCEPT_TAC;
    USE_THEN "index" ACCEPT_TAC]);;

let MINIMAL_PERIOD_ORBIT_MINIMAL = prove
 (`!f:A->A n x y.
        minimal_period f n x /\
        y IN IMAGE (\i. ITER i f x) {i | i < n}
        ==> minimal_period f n y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "minimal") MP_TAC) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC MINIMAL_PERIOD_ITERATE THEN
  USE_THEN "minimal" ACCEPT_TAC);;

let MINIMAL_PERIOD_ORDERED_ORBIT = prove
 (`!f:real->real n x.
        minimal_period f n x
        ==> ?z.
              (!i j. i < j /\ j < n ==> z i < z j) /\
              IMAGE z {i | i < n} =
              IMAGE (\i. ITER i f x) {i | i < n}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC
   `s:real->bool = IMAGE (\i. ITER i (f:real->real) x) {i | i < n}` THEN
  SUBGOAL_THEN `(s:real->bool) HAS_SIZE n` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LT];
      MATCH_MP_TAC MINIMAL_PERIOD_ORBIT_CARD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(<=):real->real->bool` TOPOLOGICAL_SORT) THEN
  ANTS_TAC THENL [MESON_TAC[REAL_LE_TRANS; REAL_LE_ANTISYM]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`n:num`; `s:real->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\i. (g:num->real)(i + 1)` THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i + 1` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `k - 1` THEN
      SUBGOAL_THEN `k - 1 + 1 = k` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]]);;

let FINITE_STRICTLY_INCREASING_INJ = prove
 (`!z:num->real n i j.
        (!r s. r < s /\ s < n ==> z r < z s) /\
        i < n /\
        j < n
        ==> (z i = z j <=> i = j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `(i:num) = j` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(i:num) < j` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`]) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let MINIMAL_PERIOD_ORDERED_ORBIT_TRANSITION = prove
 (`!f:real->real n x z.
        minimal_period f n x /\
        IMAGE z {i | i < n} = IMAGE (\i. ITER i f x) {i | i < n}
        ==> ?p:num->num.
              !i. i < n ==> p i < n /\ f(z i) = z(p i)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "minimal enum" THEN
  ABBREV_TAC
   `p:num->num =
    \i. @j:num. j < n /\ (f:real->real)((z:num->real) i) = z j` THEN
  EXISTS_TAC `p:num->num` THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  EXPAND_TAC "p" THEN BETA_TAC THEN
  SUBGOAL_THEN
   `?j:num. j < n /\ (f:real->real)((z:num->real) i) = z j`
  MP_TAC THENL
   [SUBGOAL_THEN
     `(z:num->real) i IN
      IMAGE (\k. ITER k (f:real->real) x) {k | k < n}`
    (LABEL_TAC "zi") THENL
     [USE_THEN "enum" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:real->real)((z:num->real) i) IN
      IMAGE (\k. ITER k f x) {k | k < n}`
    (LABEL_TAC "fzi") THENL
     [MATCH_MP_TAC MINIMAL_PERIOD_ORBIT_IMAGE THEN CONJ_TAC THENL
       [USE_THEN "minimal" ACCEPT_TAC;
        USE_THEN "zi" ACCEPT_TAC];
      ALL_TAC] THEN
    USE_THEN "enum" (fun th ->
      USE_THEN "fzi" (MP_TAC o REWRITE_RULE[GSYM th])) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN BETA_TAC THEN SIMP_TAC[]]);;

let FINITE_ORBIT_TRANSITION_ITER = prove
 (`!f:A->A z p n.
        (!i:num.
             i < n
             ==> (p:num->num) i < n /\
                 f((z:num->A) i) = z(p i))
        ==> !k i:num.
              i < n
              ==> ITER k p i < n /\
                  ITER k f (z i) = z(ITER k p i)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "transition") THEN
  INDUCT_TAC THENL
   [SIMP_TAC[ITER; I_THM];
    X_GEN_TAC `i:num` THEN DISCH_THEN(LABEL_TAC "ibound") THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL
     [USE_THEN "ibound" ACCEPT_TAC;
      ALL_TAC] THEN
    INTRO_TAC "iterbound iterate" THEN
    USE_THEN "transition" (MP_TAC o SPEC `ITER k (p:num->num) i`) THEN
    ANTS_TAC THENL
     [USE_THEN "iterbound" ACCEPT_TAC;
      ALL_TAC] THEN
    INTRO_TAC "nextbound step" THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[ITER; o_THM];
      REWRITE_TAC[ITER; o_THM] THEN
      ASM_REWRITE_TAC[]]]);;

let MINIMAL_PERIOD_ORDERED_ORBIT_TRANSITION_MINIMAL = prove
 (`!f:real->real n x z p.
        minimal_period f n x /\
        (!i j. i < j /\ j < n ==> z i < z j) /\
        IMAGE z {i | i < n} =
        IMAGE (\i. ITER i f x) {i | i < n} /\
        (!i. i < n ==> p i < n /\ f(z i) = z(p i))
        ==> !i. i < n ==> minimal_period p n i`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "minimal ordered enum transition" THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN(LABEL_TAC "ibound") THEN
  SUBGOAL_THEN
   `(z:num->real) i IN
    IMAGE (\k. ITER k (f:real->real) x) {k | k < n}`
  (LABEL_TAC "zi") THENL
   [USE_THEN "enum" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `minimal_period (f:real->real) n ((z:num->real) i)`
  (LABEL_TAC "pointminimal") THENL
   [MATCH_MP_TAC(ISPECL
     [`f:real->real`; `n:num`; `x:real`; `(z:num->real) i`]
     MINIMAL_PERIOD_ORBIT_MINIMAL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MINIMAL_PERIOD_DIVISIBILITY] THEN CONJ_TAC THENL
   [USE_THEN "minimal" (MP_TAC o MATCH_MP MINIMAL_PERIOD_POS) THEN
    ARITH_TAC;
    X_GEN_TAC `m:num` THEN REWRITE_TAC[periodic_point] THEN
    MP_TAC(ISPECL
     [`f:real->real`; `z:num->real`; `p:num->num`; `n:num`]
     FINITE_ORBIT_TRANSITION_ITER) THEN
    ANTS_TAC THENL
     [USE_THEN "transition" ACCEPT_TAC;
      DISCH_THEN(MP_TAC o SPECL [`m:num`; `i:num`])] THEN
    ANTS_TAC THENL
     [USE_THEN "ibound" ACCEPT_TAC;
      INTRO_TAC "iterbound iterate"] THEN
    MP_TAC(ISPECL
     [`z:num->real`; `n:num`; `ITER m (p:num->num) i`; `i:num`]
     FINITE_STRICTLY_INCREASING_INJ) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "ordered" ACCEPT_TAC;
        USE_THEN "iterbound" ACCEPT_TAC;
        USE_THEN "ibound" ACCEPT_TAC];
      DISCH_THEN(LABEL_TAC "zinj")] THEN
    MP_TAC(ISPECL
     [`f:real->real`; `n:num`; `(z:num->real) i`; `m:num`]
     MINIMAL_PERIOD_DIVIDES) THEN
    ASM_REWRITE_TAC[periodic_point] THEN
    ASM_MESON_TAC[]]);;

let adjacent_interval_cover = new_definition
 `adjacent_interval_cover p i j <=>
        (p i <= j /\ j + 1 <= p(i + 1)) \/
        (p(i + 1) <= j /\ j + 1 <= p i)`;;

let ADJACENT_INTERVAL_COVER_BOUND = prove
 (`!p n i j.
        p i < n /\
        p(i + 1) < n /\
        adjacent_interval_cover p i j
        ==> j + 1 < n`,
  REWRITE_TAC[adjacent_interval_cover] THEN ARITH_TAC);;

let ADJACENT_INTERVAL_COVER_MINMAX = prove
 (`!p i j.
        adjacent_interval_cover p i j <=>
        MIN (p i) (p(i + 1)) <= j /\
        j < MAX (p i) (p(i + 1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[adjacent_interval_cover; MIN; MAX] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let ADJACENT_INTERVAL_COVER_CONVEX = prove
 (`!p i j k l.
        adjacent_interval_cover p i j /\
        adjacent_interval_cover p i k /\
        j <= l /\
        l <= k
        ==> adjacent_interval_cover p i l`,
  REWRITE_TAC[ADJACENT_INTERVAL_COVER_MINMAX] THEN ARITH_TAC);;

let ADJACENT_INTERVAL_COVER_BETWEEN = prove
 (`!p a b j.
        a < b /\
        ((p a <= j /\ j < p b) \/ (p b <= j /\ j < p a))
        ==> ?i.
              a <= i /\
              i < b /\
              adjacent_interval_cover p i j`,
  SUBGOAL_THEN
   `!d p a j.
        ((p a <= j /\ j < p(a + SUC d)) \/
         (p(a + SUC d) <= j /\ j < p a))
        ==> ?i.
              a <= i /\
              i < a + SUC d /\
              adjacent_interval_cover p i j`
  (LABEL_TAC "induction") THENL
   [INDUCT_TAC THENL
     [MAP_EVERY X_GEN_TAC [`p:num->num`; `a:num`; `j:num`] THEN
      DISCH_TAC THEN EXISTS_TAC `a:num` THEN
      REWRITE_TAC[adjacent_interval_cover; ADD_CLAUSES] THEN
      ASM_ARITH_TAC;
      POP_ASSUM(LABEL_TAC "IH") THEN
      MAP_EVERY X_GEN_TAC [`p:num->num`; `a:num`; `j:num`] THEN
      DISCH_THEN DISJ_CASES_TAC THENL
       [ASM_CASES_TAC `(p:num->num) (a + SUC d) <= j` THENL
         [EXISTS_TAC `a + SUC d` THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
          REWRITE_TAC[adjacent_interval_cover; ADD_CLAUSES;
            ARITH_RULE
             `(a + SUC d) + 1 = a + SUC(SUC d)`] THEN
          ASM_ARITH_TAC;
          USE_THEN "IH"
           (MP_TAC o SPECL [`p:num->num`; `a:num`; `j:num`]) THEN
          ANTS_TAC THENL
           [ASM_ARITH_TAC;
            DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
            EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
            ASM_ARITH_TAC]];
        ASM_CASES_TAC `(p:num->num) (a + SUC d) <= j` THENL
         [USE_THEN "IH"
           (MP_TAC o SPECL [`p:num->num`; `a:num`; `j:num`]) THEN
          ANTS_TAC THENL
           [ASM_ARITH_TAC;
            DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
            EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
            ASM_ARITH_TAC];
          EXISTS_TAC `a + SUC d` THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
          REWRITE_TAC[adjacent_interval_cover; ADD_CLAUSES;
            ARITH_RULE
             `(a + SUC d) + 1 = a + SUC(SUC d)`] THEN
          ASM_ARITH_TAC]]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[LT_EXISTS] (ASSUME `(a:num) < b`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  USE_THEN "induction"
   (MATCH_MP_TAC o SPECL
     [`d:num`; `p:num->num`; `a:num`; `j:num`]) THEN
  ASM_REWRITE_TAC[]);;

let ADJACENT_INTERVAL_COVER_RANGE = prove
 (`!p a b j k l.
        a <= b /\
        adjacent_interval_cover p a j /\
        adjacent_interval_cover p b k /\
        j <= l /\
        l <= k
        ==> ?h.
              a <= h /\
              h <= b /\
              adjacent_interval_cover p h l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `adjacent_interval_cover (p:num->num) a l` THENL
   [EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `adjacent_interval_cover (p:num->num) b l` THENL
   [EXISTS_TAC `b:num` THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:num->num) a <= l /\ p(a + 1) <= l`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `adjacent_interval_cover (p:num->num) a j`) THEN
    MP_TAC(ASSUME `~adjacent_interval_cover (p:num->num) a l`) THEN
    REWRITE_TAC[ADJACENT_INTERVAL_COVER_MINMAX; MIN; MAX] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `l < (p:num->num) b /\ l < p(b + 1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `adjacent_interval_cover (p:num->num) b k`) THEN
    MP_TAC(ASSUME `~adjacent_interval_cover (p:num->num) b l`) THEN
    REWRITE_TAC[ADJACENT_INTERVAL_COVER_MINMAX; MIN; MAX] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) + 1 < b` ASSUME_TAC THENL
   [ASM_CASES_TAC `(b:num) = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `(b:num) = a + 1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p:num->num`; `a + 1`; `b:num`; `l:num`]
   ADJACENT_INTERVAL_COVER_BETWEEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `h:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let ADJACENT_INTERVAL_COVER_RANGE_REVERSE = prove
 (`!p a b j k l.
        a <= b /\
        adjacent_interval_cover p a j /\
        adjacent_interval_cover p b k /\
        k <= l /\
        l <= j
        ==> ?h.
              a <= h /\
              h <= b /\
              adjacent_interval_cover p h l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `adjacent_interval_cover (p:num->num) a l` THENL
   [EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `adjacent_interval_cover (p:num->num) b l` THENL
   [EXISTS_TAC `b:num` THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `l < (p:num->num) a /\ l < p(a + 1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `adjacent_interval_cover (p:num->num) a j`) THEN
    MP_TAC(ASSUME `~adjacent_interval_cover (p:num->num) a l`) THEN
    REWRITE_TAC[ADJACENT_INTERVAL_COVER_MINMAX; MIN; MAX] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:num->num) b <= l /\ p(b + 1) <= l`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `adjacent_interval_cover (p:num->num) b k`) THEN
    MP_TAC(ASSUME `~adjacent_interval_cover (p:num->num) b l`) THEN
    REWRITE_TAC[ADJACENT_INTERVAL_COVER_MINMAX; MIN; MAX] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) + 1 < b` ASSUME_TAC THENL
   [ASM_CASES_TAC `(b:num) = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `(b:num) = a + 1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p:num->num`; `a + 1`; `b:num`; `l:num`]
   ADJACENT_INTERVAL_COVER_BETWEEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `h:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let adjacent_interval_reachable =
  new_recursive_definition num_RECURSION
   `(adjacent_interval_reachable p 0 i j <=> j = i) /\
    (!k. adjacent_interval_reachable p (SUC k) i j <=>
         ?h. adjacent_interval_reachable p k i h /\
             adjacent_interval_cover p h j)`;;

let ADJACENT_INTERVAL_REACHABLE_1 = prove
 (`!p i j.
        adjacent_interval_reachable p 1 i j <=>
        adjacent_interval_cover p i j`,
  REWRITE_TAC[ONE; adjacent_interval_reachable] THEN MESON_TAC[]);;

let ADJACENT_INTERVAL_REACHABLE_BOUND = prove
 (`!p n k i j.
        (!r. r < n ==> p r < n) /\
        i + 1 < n /\
        adjacent_interval_reachable p k i j
        ==> j + 1 < n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    REWRITE_TAC[adjacent_interval_reachable] THEN ARITH_TAC;
    POP_ASSUM(LABEL_TAC "IH") THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    REWRITE_TAC[adjacent_interval_reachable] THEN
    INTRO_TAC "transition ibound @h. path cover" THEN
    SUBGOAL_THEN `(h:num) + 1 < n` ASSUME_TAC THENL
     [USE_THEN "IH" (MATCH_MP_TAC o SPECL [`i:num`; `h:num`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL
     [`p:num->num`; `n:num`; `h:num`; `j:num`]
     ADJACENT_INTERVAL_COVER_BOUND) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "transition" (MATCH_MP_TAC o SPEC `h:num`) THEN
      ASM_ARITH_TAC;
      USE_THEN "transition" (MATCH_MP_TAC o SPEC `h + 1`) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "cover" ACCEPT_TAC]]);;

let ADJACENT_INTERVAL_REACHABLE_PREPEND = prove
 (`!p k i h j.
        adjacent_interval_cover p i h /\
        adjacent_interval_reachable p k h j
        ==> adjacent_interval_reachable p (SUC k) i j`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[adjacent_interval_reachable] THEN MESON_TAC[];
    POP_ASSUM(LABEL_TAC "IH") THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `h:num`; `j:num`] THEN
    INTRO_TAC "first path" THEN
    USE_THEN "path"
     (MP_TAC o REWRITE_RULE[adjacent_interval_reachable]) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `adjacent_interval_reachable p (SUC k) i l`
    ASSUME_TAC THENL
     [USE_THEN "IH"
       (MATCH_MP_TAC o SPECL [`i:num`; `h:num`; `l:num`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[adjacent_interval_reachable] THEN
    EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[]]);;

let ADJACENT_INTERVAL_REACHABLE_TRANS = prove
 (`!p k l i j h.
        adjacent_interval_reachable p k i j /\
        adjacent_interval_reachable p l j h
        ==> adjacent_interval_reachable p (k + l) i h`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; adjacent_interval_reachable] THEN
    MESON_TAC[];
    POP_ASSUM(LABEL_TAC "IH") THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `h:num`] THEN
    INTRO_TAC "first path" THEN
    USE_THEN "path"
     (MP_TAC o REWRITE_RULE[adjacent_interval_reachable]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `adjacent_interval_reachable p (k + l) i m`
    ASSUME_TAC THENL
     [USE_THEN "IH"
       (MATCH_MP_TAC o SPECL [`i:num`; `j:num`; `m:num`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[adjacent_interval_reachable] THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]]);;

let ADJACENT_INTERVAL_REACHABLE_SELF = prove
 (`!p k i j.
        adjacent_interval_cover p i i /\
        adjacent_interval_reachable p k i j
        ==> adjacent_interval_reachable p (SUC k) i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL
   [`p:num->num`; `k:num`; `i:num`; `i:num`; `j:num`]
   ADJACENT_INTERVAL_REACHABLE_PREPEND) THEN
  ASM_REWRITE_TAC[]);;

let ADJACENT_INTERVAL_REACHABLE_CONVEX = prove
 (`!p k i j l m.
        adjacent_interval_reachable p k i j /\
        adjacent_interval_reachable p k i l /\
        j <= m /\
        m <= l
        ==> adjacent_interval_reachable p k i m`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[adjacent_interval_reachable] THEN ARITH_TAC;
    POP_ASSUM(LABEL_TAC "IH") THEN
    MAP_EVERY X_GEN_TAC
     [`i:num`; `j:num`; `l:num`; `m:num`] THEN
    INTRO_TAC "pathj pathl jm ml" THEN
    USE_THEN "pathj"
     (MP_TAC o REWRITE_RULE[adjacent_interval_reachable]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "pathl"
     (MP_TAC o REWRITE_RULE[adjacent_interval_reachable]) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?h. adjacent_interval_reachable p k i h /\
          adjacent_interval_cover p h m`
    MP_TAC THENL
     [ASM_CASES_TAC `(a:num) <= b` THENL
       [MP_TAC(ISPECL
         [`p:num->num`; `a:num`; `b:num`; `j:num`; `l:num`; `m:num`]
         ADJACENT_INTERVAL_COVER_RANGE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[];
          DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
        EXISTS_TAC `h:num` THEN CONJ_TAC THENL
         [USE_THEN "IH"
           (MATCH_MP_TAC o
            SPECL [`i:num`; `a:num`; `b:num`; `h:num`]) THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        MP_TAC(ISPECL
         [`p:num->num`; `b:num`; `a:num`; `l:num`; `j:num`; `m:num`]
         ADJACENT_INTERVAL_COVER_RANGE_REVERSE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
        EXISTS_TAC `h:num` THEN CONJ_TAC THENL
         [USE_THEN "IH"
           (MATCH_MP_TAC o
            SPECL [`i:num`; `b:num`; `a:num`; `h:num`]) THEN
          ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          ASM_REWRITE_TAC[]]];
      DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
    ONCE_REWRITE_TAC[adjacent_interval_reachable] THEN
    EXISTS_TAC `h:num` THEN ASM_REWRITE_TAC[]]);;

let ADJACENT_INTERVAL_REACHABLE_PATH = prove
 (`!p k i j.
        adjacent_interval_reachable p k i j <=>
        ?q. q 0 = i /\
            q k = j /\
            !r. r < k
                ==> adjacent_interval_cover p (q r) (q(SUC r))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[adjacent_interval_reachable] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC `\r:num. (i:num)` THEN REWRITE_TAC[] THEN ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `q:num->num` STRIP_ASSUME_TAC) THEN
      TRANS_TAC EQ_TRANS `(q:num->num) 0` THEN CONJ_TAC THENL
       [ACCEPT_TAC(SYM(ASSUME `(q:num->num) 0 = j`));
        ACCEPT_TAC(ASSUME `(q:num->num) 0 = i`)]];
    POP_ASSUM(LABEL_TAC "IH") THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    ONCE_REWRITE_TAC[adjacent_interval_reachable] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "IH" (MP_TAC o SPECL [`i:num`; `h:num`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:num->num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC
       `\r. if r < SUC k then (q:num->num) r else j` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[ARITH_RULE `0 < SUC k`];
        REWRITE_TAC[LT_REFL];
        X_GEN_TAC `r:num` THEN DISCH_TAC THEN
        ASM_CASES_TAC `(r:num) < k` THENL
         [SUBGOAL_THEN `SUC(r:num) < SUC k` ASSUME_TAC THENL
           [ASM_ARITH_TAC;
            ASM_REWRITE_TAC[] THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
          SUBGOAL_THEN `(r:num) = k` SUBST_ALL_TAC THENL
           [ASM_ARITH_TAC;
            ASM_REWRITE_TAC[LT_REFL; GSYM ADD1]]]];
      DISCH_THEN(X_CHOOSE_THEN `q:num->num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(q:num->num) k` THEN CONJ_TAC THENL
       [USE_THEN "IH"
         (MATCH_MP_TAC o snd o EQ_IMP_RULE o
          SPECL [`i:num`; `(q:num->num) k`]) THEN
        EXISTS_TAC `q:num->num` THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `r:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
        ANTS_TAC THENL
         [ARITH_TAC;
          ASM_REWRITE_TAC[]]]]]);;

let ADJACENT_INTERVAL_PATH_BOUND = prove
 (`!p n k i (q:num->num).
        (!r. r < n ==> p r < n) /\
        i + 1 < n /\
        q 0 = i /\
        (!r. r < k
             ==> adjacent_interval_cover p (q r) (q(SUC r)))
        ==> !r. r <= k ==> q r + 1 < n`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "transition ibound initial path" THEN
  INDUCT_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `(q:num->num) r + 1 < n` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `r <= k ==> (q:num->num) r + 1 < n`) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL
     [`p:num->num`; `n:num`; `(q:num->num) r`;
      `(q:num->num)(SUC r)`]
     ADJACENT_INTERVAL_COVER_BOUND) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "transition" (MATCH_MP_TAC o SPEC `(q:num->num) r`) THEN
      ASM_ARITH_TAC;
      USE_THEN "transition"
       (MATCH_MP_TAC o SPEC `(q:num->num) r + 1`) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "path" MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let FINITE_ASCENDING_CHAIN_STABILIZES = prove
 (`!s:num->A->bool u.
        FINITE u /\
        (!k. s k SUBSET u) /\
        (!k. s k SUBSET s(SUC k))
        ==> ?k. s(SUC k) = s k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE
   (SPEC `\m. ?k. m = CARD((s:num->A->bool) k)` num_MAX)))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `CARD((s:num->A->bool) 0)` THEN
      EXISTS_TAC `0` THEN REFL_TAC;
      EXISTS_TAC `CARD(u:A->bool)` THEN
      X_GEN_TAC `m:num` THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]];
    INTRO_TAC "@m. (@k. card) maximal"] THEN
  USE_THEN "card" SUBST_ALL_TAC THEN
  EXISTS_TAC `k:num` THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  MATCH_MP_TAC CARD_SUBSET_LE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "maximal" MATCH_MP_TAC THEN
    EXISTS_TAC `SUC k` THEN REFL_TAC]);;

let FINITE_CYCLIC_CLOSED_INTERVAL = prove
 (`!p n a b.
        a < b /\
        b < n /\
        (!i. i < n ==> p i < n /\ minimal_period p n i) /\
        (!i j.
             a <= i /\
             i < b /\
             adjacent_interval_cover p i j
             ==> a <= j /\ j < b)
        ==> a = 0 /\ b + 1 = n`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "nontrivial bound cycle closed" THEN
  SUBGOAL_THEN
   `!h. a <= h /\ h < b
        ==> a <= (p:num->num) h /\
            p h <= b /\
            a <= p(h + 1) /\
            p(h + 1) <= b`
  (LABEL_TAC "edge_invariant") THENL
   [X_GEN_TAC `h:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~((p:num->num) h = p(h + 1))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`p:num->num`; `n:num`; `h:num`; `h + 1`]
       PERIODIC_POINTS_IMAGE_INJ) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC;
          MATCH_MP_TAC MINIMAL_PERIOD_PERIODIC THEN
          USE_THEN "cycle" (MP_TAC o SPEC `h:num`) THEN
          ANTS_TAC THENL
           [ASM_ARITH_TAC;
            SIMP_TAC[]];
          MATCH_MP_TAC MINIMAL_PERIOD_PERIODIC THEN
          USE_THEN "cycle" (MP_TAC o SPEC `h + 1`) THEN
          ANTS_TAC THENL
           [ASM_ARITH_TAC;
            SIMP_TAC[]]];
        ASM_REWRITE_TAC[] THEN ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `(p:num->num) h < p(h + 1)` THENL
     [SUBGOAL_THEN
       `a <= (p:num->num) h /\ p h < b`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "closed"
         (MATCH_MP_TAC o SPECL [`h:num`; `(p:num->num) h`]) THEN
        ASM_REWRITE_TAC[adjacent_interval_cover] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `a <= (p:num->num) (h + 1) - 1 /\
        p(h + 1) - 1 < b`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "closed"
         (MATCH_MP_TAC o
          SPECL [`h:num`; `(p:num->num) (h + 1) - 1`]) THEN
        ASM_REWRITE_TAC[adjacent_interval_cover] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      SUBGOAL_THEN
       `(p:num->num) (h + 1) < p h`
      ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `a <= (p:num->num) (h + 1) /\ p(h + 1) < b`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "closed"
         (MATCH_MP_TAC o
          SPECL [`h:num`; `(p:num->num) (h + 1)`]) THEN
        ASM_REWRITE_TAC[adjacent_interval_cover] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `a <= (p:num->num) h - 1 /\ p h - 1 < b`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "closed"
         (MATCH_MP_TAC o
          SPECL [`h:num`; `(p:num->num) h - 1`]) THEN
        ASM_REWRITE_TAC[adjacent_interval_cover] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. a <= r /\ r <= b
        ==> a <= (p:num->num) r /\ p r <= b`
  (LABEL_TAC "invariant") THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(r:num) = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "edge_invariant" (MP_TAC o SPEC `b - 1`) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        SUBGOAL_THEN `(b:num) - 1 + 1 = b` ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          DISCH_THEN STRIP_ASSUME_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE
           [ASSUME `(b:num) - 1 + 1 = b`]) THEN
          ASM_REWRITE_TAC[]]];
      USE_THEN "edge_invariant" (MP_TAC o SPEC `r:num`) THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ITER m (p:num->num) a IN (a..b)`
  (LABEL_TAC "orbit_in_interval") THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[ITER; IN_NUMSEG] THEN ASM_ARITH_TAC;
      REWRITE_TAC[ITER; IN_NUMSEG] THEN
      MATCH_MP_TAC(SPEC `ITER m (p:num->num) a`
       (ASSUME
        `!r. a <= r /\ r <= b
             ==> a <= (p:num->num) r /\ p r <= b`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\m. ITER m (p:num->num) a) {m | m < n}
    SUBSET (a..b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(IMAGE (\m. ITER m (p:num->num) a) {m | m < n}) = n`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MINIMAL_PERIOD_ORBIT_CARD THEN
    USE_THEN "cycle" (MP_TAC o SPEC `a:num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(IMAGE (\m. ITER m (p:num->num) a) {m | m < n}) <=
    CARD(a..b)`
  MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ASM_REWRITE_TAC[CARD_NUMSEG] THEN ASM_ARITH_TAC]);;

let FINITE_CYCLIC_REACHABLE_ALL = prove
 (`!p n i j.
        (!r. r < n ==> p r < n /\ minimal_period p n r) /\
        i + 1 < n /\
        j + 1 < n /\
        ~(j = i) /\
        adjacent_interval_cover p i i /\
        adjacent_interval_cover p i j
        ==> ?k.
              !h. h + 1 < n
                  ==> adjacent_interval_reachable p k i h`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "cycle ibound jbound distinct self exit" THEN
  SUBGOAL_THEN
   `!m. adjacent_interval_reachable (p:num->num) m i i`
  (LABEL_TAC "loop") THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[adjacent_interval_reachable];
      MATCH_MP_TAC ADJACENT_INTERVAL_REACHABLE_SELF THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\k. {h | h + 1 < n /\
              adjacent_interval_reachable (p:num->num) k i h}`;
    `0..n`]
   FINITE_ASCENDING_CHAIN_STABILIZES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG];
      X_GEN_TAC `m:num` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      X_GEN_TAC `m:num` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `h:num` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ADJACENT_INTERVAL_REACHABLE_SELF THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `k:num`
     (LABEL_TAC "stable" o BETA_RULE))] THEN
  SUBGOAL_THEN
   `!h l.
        h + 1 < n /\
        adjacent_interval_reachable (p:num->num) k i h /\
        adjacent_interval_cover p h l
        ==> l + 1 < n /\
            adjacent_interval_reachable p k i l`
  (LABEL_TAC "reachclosed") THENL
   [MAP_EVERY X_GEN_TAC [`h:num`; `l:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(l:num) + 1 < n` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL
       [`p:num->num`; `n:num`; `h:num`; `l:num`]
       ADJACENT_INTERVAL_COVER_BOUND) THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "cycle" (MP_TAC o SPEC `h:num`) THEN
        ANTS_TAC THENL
         [ASM_ARITH_TAC;
          SIMP_TAC[]];
        USE_THEN "cycle" (MP_TAC o SPEC `h + 1`) THEN
        ANTS_TAC THENL
         [ASM_ARITH_TAC;
          SIMP_TAC[]];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `l IN {q | q + 1 < n /\
                  adjacent_interval_reachable
                   (p:num->num) k i q}`
      MP_TAC THENL
       [USE_THEN "stable" (SUBST1_TAC o SYM) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          ONCE_REWRITE_TAC[adjacent_interval_reachable] THEN
          EXISTS_TAC `h:num` THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `j + 1 < n /\
    adjacent_interval_reachable (p:num->num) k i j`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "reachclosed"
     (MATCH_MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE
   (SPEC
    `\h. h + 1 < n /\
         adjacent_interval_reachable (p:num->num) k i h`
    num_WOP)))) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    INTRO_TAC "@a. amin minimal"] THEN
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE
   (SPEC
    `\h. h + 1 < n /\
         adjacent_interval_reachable (p:num->num) k i h`
    num_MAX)))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `n:num` THEN
      X_GEN_TAC `h:num` THEN STRIP_TAC THEN ASM_ARITH_TAC];
    INTRO_TAC "@b. bmax maximal"] THEN
  SUBGOAL_THEN
   `!h.
        (h + 1 < n /\
         adjacent_interval_reachable (p:num->num) k i h <=>
         a <= h /\ h <= b)`
  (LABEL_TAC "range") THENL
   [X_GEN_TAC `h:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [ASM_CASES_TAC `(a:num) <= h` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(h:num) < a` ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          ALL_TAC] THEN
        USE_THEN "minimal" (MP_TAC o SPEC `h:num`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[];
          DISCH_TAC THEN
          UNDISCH_TAC
           `h + 1 < n /\
            adjacent_interval_reachable (p:num->num) k i h` THEN
          ASM_REWRITE_TAC[]];
        USE_THEN "maximal" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC(CONJUNCT1(ASSUME
         `b + 1 < n /\
          adjacent_interval_reachable (p:num->num) k i b`)) THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC(ISPECL
         [`p:num->num`; `k:num`; `i:num`;
          `a:num`; `b:num`; `h:num`]
         ADJACENT_INTERVAL_REACHABLE_CONVEX) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) < b` ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:num) <= i /\ i <= b`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "range"
       (MATCH_MP_TAC o fst o EQ_IMP_RULE o SPEC `i:num`) THEN
      CONJ_TAC THENL
       [USE_THEN "ibound" ACCEPT_TAC;
        USE_THEN "loop" (ACCEPT_TAC o SPEC `k:num`)];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:num) <= j /\ j <= b`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "range"
       (MATCH_MP_TAC o fst o EQ_IMP_RULE o SPEC `j:num`) THEN
      CONJ_TAC THENL
       [USE_THEN "jbound" ACCEPT_TAC;
        ACCEPT_TAC(ASSUME
         `adjacent_interval_reachable (p:num->num) k i j`)];
      ASM_CASES_TAC `(a:num) < b` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(i:num) = j` ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        UNDISCH_TAC `~((j:num) = i)` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p:num->num`; `n:num`; `a:num`; `b + 1`]
   FINITE_CYCLIC_CLOSED_INTERVAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ACCEPT_TAC(CONJUNCT1(ASSUME
       `b + 1 < n /\
        adjacent_interval_reachable (p:num->num) k i b`));
      USE_THEN "cycle" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`h:num`; `l:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `h + 1 < n /\
        adjacent_interval_reachable (p:num->num) k i h`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "range"
         (MATCH_MP_TAC o snd o EQ_IMP_RULE o SPEC `h:num`) THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `l + 1 < n /\
        adjacent_interval_reachable (p:num->num) k i l`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "reachclosed"
         (MATCH_MP_TAC o SPECL [`h:num`; `l:num`]) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(a:num) <= l /\ l <= b`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "range"
         (MATCH_MP_TAC o fst o EQ_IMP_RULE o SPEC `l:num`) THEN
        CONJ_TAC THENL
         [ACCEPT_TAC(ASSUME `(l:num) + 1 < n`);
          ACCEPT_TAC(ASSUME
           `adjacent_interval_reachable (p:num->num) k i l`)];
        ASM_ARITH_TAC]];
    STRIP_TAC] THEN
  EXISTS_TAC `k:num` THEN
  X_GEN_TAC `h:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `h + 1 < n /\
    adjacent_interval_reachable (p:num->num) k i h`
  MP_TAC THENL
   [USE_THEN "range" (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    SIMP_TAC[]]);;

let FINITE_CYCLIC_SELFCOVER_EXIT = prove
 (`!p n i.
        2 < n /\
        (!r. r < n ==> p r < n /\ minimal_period p n r) /\
        i + 1 < n /\
        adjacent_interval_cover p i i
        ==> ?j.
              j + 1 < n /\
              ~(j = i) /\
              adjacent_interval_cover p i j`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "nontrivial cycle ibound self" THEN
  SUBGOAL_THEN
   `(p:num->num) i < n /\
    minimal_period p n i /\
    p(i + 1) < n`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "cycle" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        SIMP_TAC[]];
      USE_THEN "cycle" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        SIMP_TAC[]];
      USE_THEN "cycle" (MP_TAC o SPEC `i + 1`) THEN
      ANTS_TAC THENL
       [USE_THEN "ibound" ACCEPT_TAC;
        SIMP_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "self"
   (DISJ_CASES_TAC o REWRITE_RULE[adjacent_interval_cover]) THENL
   [SUBGOAL_THEN
     `(p:num->num) i < i \/ i + 1 < p(i + 1)`
    MP_TAC THENL
     [ASM_CASES_TAC `(p:num->num) i < i` THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i + 1 < (p:num->num) (i + 1)` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(p:num->num) i = i` ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        MP_TAC(ISPECL
         [`p:num->num`; `n:num`; `i:num`; `0`; `1`]
         MINIMAL_PERIOD_ITER_INJ) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            ASM_ARITH_TAC;
            ASM_ARITH_TAC];
          REWRITE_TAC[ITER; ITER_1] THEN ASM_REWRITE_TAC[] THEN
          ARITH_TAC]];
      DISCH_THEN DISJ_CASES_TAC THENL
       [EXISTS_TAC `i - 1` THEN
        ASM_REWRITE_TAC[adjacent_interval_cover] THEN ASM_ARITH_TAC;
        EXISTS_TAC `i + 1` THEN
        ASM_REWRITE_TAC[adjacent_interval_cover] THEN ASM_ARITH_TAC]];
    SUBGOAL_THEN
     `(p:num->num) (i + 1) < i \/ i + 1 < p i`
    MP_TAC THENL
     [ASM_CASES_TAC `(p:num->num) (i + 1) < i` THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i + 1 < (p:num->num) i` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(p:num->num) (i + 1) = i /\ p i = i + 1`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN ASM_ARITH_TAC;
        MP_TAC(ISPECL
         [`p:num->num`; `n:num`; `i:num`; `0`; `2`]
         MINIMAL_PERIOD_ITER_INJ) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            ASM_ARITH_TAC;
            ASM_ARITH_TAC];
          REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; ITER; o_THM] THEN
          ASM_REWRITE_TAC[] THEN ARITH_TAC]];
      DISCH_THEN DISJ_CASES_TAC THENL
       [EXISTS_TAC `i - 1` THEN
        ASM_REWRITE_TAC[adjacent_interval_cover] THEN ASM_ARITH_TAC;
        EXISTS_TAC `i + 1` THEN
        ASM_REWRITE_TAC[adjacent_interval_cover] THEN
        ASM_ARITH_TAC]]]);;

let FINITE_CYCLIC_CROSSING = prove
 (`!p n.
        1 < n /\
        (!i. i < n ==> p i < n /\ minimal_period p n i)
        ==> ?i.
              i + 1 < n /\
              p(i + 1) <= i /\
              i + 1 <= p i`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "nontrivial cycle" THEN
  SUBGOAL_THEN
   `(p:num->num) 0 < n /\ minimal_period p n 0`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cycle" (MATCH_MP_TAC o SPEC `0`) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i:num.
        (i < n /\ i < (p:num->num) i) /\
        !j. j < n /\ j < p j ==> j <= i`
  MP_TAC THENL
   [MP_TAC(SPEC `\j:num. j < n /\ j < (p:num->num) j` num_MAX) THEN
    DISCH_THEN(MP_TAC o BETA_RULE o fst o EQ_IMP_RULE) THEN
    DISCH_THEN MATCH_MP_TAC THEN BETA_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `0` THEN CONJ_TAC THENL
       [ASM_ARITH_TAC;
        REWRITE_TAC[LT_NZ] THEN
        MP_TAC(ISPECL
         [`p:num->num`; `n:num`; `0`; `0`; `1`]
         MINIMAL_PERIOD_ITER_INJ) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            CONJ_TAC THENL
             [USE_THEN "nontrivial" MP_TAC THEN ARITH_TAC;
              USE_THEN "nontrivial" ACCEPT_TAC]];
          DISCH_THEN(fun ith ->
            DISCH_THEN(fun fth ->
              MP_TAC(REWRITE_RULE[ITER; ITER_1; fth] ith))) THEN
          ARITH_TAC]];
      EXISTS_TAC `n:num` THEN BETA_TAC THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(i:num) + 1 < n` ASSUME_TAC THENL
   [USE_THEN "cycle" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL
     [ACCEPT_TAC(ASSUME `(i:num) < n`);
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)] THEN
    MP_TAC(ASSUME `(i:num) < (p:num->num) i`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:num->num) (i + 1) < n /\
    minimal_period p n (i + 1)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cycle" (MATCH_MP_TAC o SPEC `i + 1`) THEN
    ACCEPT_TAC(ASSUME `(i:num) + 1 < n`);
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) (i + 1) <= i`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `(p:num->num) (i + 1) <= i` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((p:num->num) (i + 1) = i + 1)` ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`p:num->num`; `n:num`; `i + 1`; `0`; `1`]
       MINIMAL_PERIOD_ITER_INJ) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          CONJ_TAC THENL
           [USE_THEN "nontrivial" MP_TAC THEN ARITH_TAC;
            USE_THEN "nontrivial" ACCEPT_TAC]];
        DISCH_THEN(fun ith ->
          DISCH_THEN(fun fth ->
            MP_TAC(REWRITE_RULE[ITER; ITER_1; fth] ith))) THEN
        ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPEC `i + 1`
     (ASSUME `!j. j < n /\ j < (p:num->num) j ==> j <= i`)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ACCEPT_TAC(ASSUME `(i:num) + 1 < n`);
        UNDISCH_TAC `~((p:num->num) (i + 1) <= i)` THEN
        UNDISCH_TAC `~((p:num->num) (i + 1) = i + 1)` THEN
        ARITH_TAC];
      ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `i:num` THEN CONJ_TAC THENL
   [ACCEPT_TAC(ASSUME `(i:num) + 1 < n`);
    CONJ_TAC THENL
     [ACCEPT_TAC(ASSUME `(p:num->num) (i + 1) <= i`);
      MP_TAC(ASSUME `(i:num) < (p:num->num) i`) THEN ARITH_TAC]]);;

let FINITE_ODD_CYCLIC_RETURN = prove
 (`!p n.
        ODD n /\
        2 < n /\
        (!i. i < n ==> p i < n /\ minimal_period p n i)
        ==> ?i j.
              i + 1 < n /\
              j + 1 < n /\
              ~(j = i) /\
              p(i + 1) <= i /\
              i + 1 <= p i /\
              adjacent_interval_cover p i i /\
              adjacent_interval_cover p j i`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "odd nontrivial cycle" THEN
  MP_TAC(ISPECL [`p:num->num`; `n:num`] FINITE_CYCLIC_CROSSING) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "nontrivial" MP_TAC THEN ARITH_TAC;
      USE_THEN "cycle" ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(p:num->num) i < n` ASSUME_TAC THENL
   [USE_THEN "cycle" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL
     [MP_TAC(ASSUME `(i:num) + 1 < n`) THEN ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) (i + 1) < n` ASSUME_TAC THENL
   [USE_THEN "cycle" (MP_TAC o SPEC `i + 1`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?j. j + 1 < n /\ ~(j = i) /\ adjacent_interval_cover p j i`
  THENL
   [POP_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN
    ASM_REWRITE_TAC[adjacent_interval_cover] THEN ASM_ARITH_TAC;
    POP_ASSUM(LABEL_TAC "noreturn")] THEN
  SUBGOAL_THEN
   `!r. r <= i ==> i < (p:num->num) r`
  (LABEL_TAC "left") THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(r:num) = i` THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `i < (p:num->num) r` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`p:num->num`; `r:num`; `i:num`; `i:num`]
     ADJACENT_INTERVAL_COVER_BETWEEN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_ARITH_TAC;
        DISJ1_TAC THEN ASM_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN
     `?j. j + 1 < n /\
          ~(j = i) /\
          adjacent_interval_cover (p:num->num) j i`
    MP_TAC THENL
     [EXISTS_TAC `h:num` THEN CONJ_TAC THENL
       [ASM_ARITH_TAC;
        CONJ_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[]]];
      DISCH_THEN ASSUME_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. i + 1 <= r /\ r < n ==> (p:num->num) r <= i`
  (LABEL_TAC "right") THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(p:num->num) r <= i` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`p:num->num`; `i + 1`; `r:num`; `i:num`]
     ADJACENT_INTERVAL_COVER_BETWEEN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_CASES_TAC `(r:num) = i + 1` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[];
          ASM_ARITH_TAC];
        DISJ1_TAC THEN ASM_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN
     `?j. j + 1 < n /\
          ~(j = i) /\
          adjacent_interval_cover (p:num->num) j i`
    MP_TAC THENL
     [EXISTS_TAC `h:num` THEN CONJ_TAC THENL
       [ASM_ARITH_TAC;
        CONJ_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[]]];
      DISCH_THEN ASSUME_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r s.
        r < n /\ s < n /\ (p:num->num) r = p s
        ==> r = s`
  (LABEL_TAC "injective") THENL
   [MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p:num->num`; `n:num`; `r:num`; `s:num`]
     PERIODIC_POINTS_IMAGE_INJ) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "nontrivial" MP_TAC THEN ARITH_TAC;
        MATCH_MP_TAC MINIMAL_PERIOD_PERIODIC THEN
        USE_THEN "cycle" (MP_TAC o SPEC `r:num`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[];
          DISCH_THEN(fun th -> ACCEPT_TAC(CONJUNCT2 th))];
        MATCH_MP_TAC MINIMAL_PERIOD_PERIODIC THEN
        USE_THEN "cycle" (MP_TAC o SPEC `s:num`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[];
          DISCH_THEN(fun th -> ACCEPT_TAC(CONJUNCT2 th))]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:num->num) (0..i) SUBSET ((i + 1)..(n - 1))`
  (LABEL_TAC "leftimage") THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "left" (MP_TAC o SPEC `r:num`) THEN ASM_ARITH_TAC;
      USE_THEN "cycle" (MP_TAC o SPEC `r:num`) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        SIMP_TAC[] THEN ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:num->num) ((i + 1)..(n - 1)) SUBSET (0..i)`
  (LABEL_TAC "rightimage") THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    USE_THEN "right" (MP_TAC o SPEC `r:num`) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(IMAGE (p:num->num) (0..i)) = CARD(0..i)`
  (LABEL_TAC "leftcard") THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    USE_THEN "injective" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(IMAGE (p:num->num) ((i + 1)..(n - 1))) =
    CARD((i + 1)..(n - 1))`
  (LABEL_TAC "rightcard") THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    USE_THEN "injective" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(0..i) <= CARD((i + 1)..(n - 1))`
  ASSUME_TAC THENL
   [USE_THEN "leftcard" (fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD((i + 1)..(n - 1)) <= CARD(0..i)`
  ASSUME_TAC THENL
   [USE_THEN "rightcard" (fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n:num) = 2 * (i + 1)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[CARD_NUMSEG]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `EVEN n` ASSUME_TAC THENL
   [REWRITE_TAC[EVEN_EXISTS] THEN EXISTS_TAC `i + 1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "odd" MP_TAC THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN ASM_REWRITE_TAC[]);;

let FINITE_ODD_CYCLIC_RETURN_CYCLE = prove
 (`!p n.
        ODD n /\
        2 < n /\
        (!i. i < n ==> p i < n /\ minimal_period p n i)
        ==> ?k q.
              1 < k /\
              (!r. r <= k ==> q r + 1 < n) /\
              q 0 = q k /\
              p(q 0 + 1) <= q 0 /\
              q 0 + 1 <= p(q 0) /\
              adjacent_interval_cover p (q 0) (q 0) /\
              ~(q(k - 1) = q 0) /\
              (!r. r < k
                   ==> adjacent_interval_cover p (q r) (q(SUC r)))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "odd nontrivial cycle" THEN
  MP_TAC(ISPECL [`p:num->num`; `n:num`]
   FINITE_ODD_CYCLIC_RETURN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `i:num`
     (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL
   [`p:num->num`; `n:num`; `i:num`]
   FINITE_CYCLIC_SELFCOVER_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL
   [`p:num->num`; `n:num`; `i:num`; `h:num`]
   FINITE_CYCLIC_REACHABLE_ALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    INTRO_TAC "@m. reachable"] THEN
  SUBGOAL_THEN
   `adjacent_interval_reachable (p:num->num) m i j`
  ASSUME_TAC THENL
   [USE_THEN "reachable" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p:num->num`; `m:num`; `i:num`; `j:num`]
   ADJACENT_INTERVAL_REACHABLE_PATH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `0 < (m:num)` ASSUME_TAC THENL
   [ASM_CASES_TAC `(m:num) = 0` THENL
     [SUBGOAL_THEN `(j:num) = i` ASSUME_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE
         [ASSUME `(m:num) = 0`]) THEN
        TRANS_TAC EQ_TRANS `(q:num->num) 0` THEN CONJ_TAC THENL
         [ACCEPT_TAC(SYM(ASSUME `(q:num->num) 0 = j`));
          ACCEPT_TAC(ASSUME `(q:num->num) 0 = i`)];
        ASM_MESON_TAC[]];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p:num->num`; `n:num`; `m:num`; `i:num`; `q:num->num`]
   ADJACENT_INTERVAL_PATH_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      USE_THEN "cycle" (MP_TAC o SPEC `r:num`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_THEN(LABEL_TAC "qbound")] THEN
  EXISTS_TAC `SUC m` THEN
  EXISTS_TAC `\r. if r < SUC m then (q:num->num) r else i` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(r:num) < SUC m` THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "qbound" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `(r:num) = SUC m` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[LT_REFL]]];
    ASM_REWRITE_TAC[ARITH_RULE `0 < SUC m`; LT_REFL];
    ASM_REWRITE_TAC[ARITH_RULE `0 < SUC m`];
    ASM_REWRITE_TAC[ARITH_RULE `0 < SUC m`];
    ASM_REWRITE_TAC[ARITH_RULE `0 < SUC m`];
    REWRITE_TAC[ARITH_RULE `SUC m - 1 = m`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `m < SUC m`;
      ARITH_RULE `0 < SUC m`];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(r:num) < m` THENL
     [SUBGOAL_THEN `SUC(r:num) < SUC m` ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(r:num) = m` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[LT_REFL]]]]);;

let PATH_FIRST_RETURN_CYCLE = prove
 (`!v e w.
        (?k (q:num->A).
              1 < k /\
              (!r. r <= k ==> v(q r)) /\
              q 0 = q k /\
              w(q 0) /\
              ~(q(k - 1) = q 0) /\
              (!r. r < k ==> e (q r) (q(SUC r))))
        ==> ?k q.
              1 < k /\
              (!r. r <= k ==> v(q r)) /\
              q 0 = q k /\
              w(q 0) /\
              (!r. 0 < r /\ r < k ==> ~(q r = q 0)) /\
              (!r. r < k ==> e (q r) (q(SUC r)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "exists") THEN
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE
   (SPEC
    `\k. ?q:num->A.
              1 < k /\
              (!r. r <= k ==> v(q r)) /\
              q 0 = q k /\
              w(q 0) /\
              ~(q(k - 1) = q 0) /\
              (!r. r < k ==> e (q r) (q(SUC r)))`
    num_WOP)))) THEN
  ANTS_TAC THENL
   [REMOVE_THEN "exists" MP_TAC THEN REWRITE_TAC[];
    INTRO_TAC
     "@k. (@q. length bound closed base last path) minimal"] THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `q:num->A`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN
  INTRO_TAC "rpos rlt" THEN
  DISCH_THEN(LABEL_TAC "return") THEN
  USE_THEN "rlt" (MP_TAC o REWRITE_RULE[LT_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ADD_CLAUSES; ARITH_RULE `(r + SUC 0) - 1 = r`]) THEN
    USE_THEN "last" MP_TAC THEN
    REWRITE_TAC[TAUT `(~p ==> F) <=> p`] THEN
    TRANS_TAC EQ_TRANS `(q:num->A)(SUC r)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 < (r + SUC d) - r` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ADD_SUB2;
      ARITH_RULE `1 < SUC d <=> ~(d = 0)`];
    ALL_TAC] THEN
  USE_THEN "minimal"
   (MP_TAC o SPEC `((r + SUC d) - r)`) THEN
  REWRITE_TAC[ADD_SUB2; LT_ADDR] THEN
  USE_THEN "rpos" (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC `\s. (q:num->A)(r + s)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ADD_SUB2;
      ARITH_RULE `1 < SUC d <=> ~(d = 0)`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:num` THEN DISCH_THEN(LABEL_TAC "sbound") THEN
    BETA_TAC THEN
    USE_THEN "bound" MATCH_MP_TAC THEN
    USE_THEN "sbound" MP_TAC THEN
    REWRITE_TAC[ADD_SUB2; LE_ADD_LCANCEL];
    BETA_TAC THEN REWRITE_TAC[ADD_0; ADD_SUB2] THEN
    USE_THEN "return" ACCEPT_TAC;
    BETA_TAC THEN REWRITE_TAC[ADD_0] THEN
    ASM_MESON_TAC[];
    BETA_TAC THEN
    REWRITE_TAC[ADD_SUB2; ARITH_RULE `SUC d - 1 = d`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ADD_CLAUSES; ARITH_RULE `(r + SUC d) - 1 = r + d`]) THEN
    DISCH_THEN(LABEL_TAC "repeat") THEN
    USE_THEN "last" MP_TAC THEN
    REWRITE_TAC[TAUT `(~p ==> F) <=> p`] THEN
    TRANS_TAC EQ_TRANS `(q:num->A) r` THEN
    ASM_REWRITE_TAC[ADD_0];
    X_GEN_TAC `s:num` THEN DISCH_THEN(LABEL_TAC "slt") THEN
    BETA_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    USE_THEN "path" MATCH_MP_TAC THEN
    USE_THEN "slt" MP_TAC THEN
    REWRITE_TAC[ADD_SUB2; LT_ADD_LCANCEL]]);;

let PATH_SIMPLE_CYCLE = prove
 (`!v e w.
        (?k (q:num->A).
              1 < k /\
              (!r. r <= k ==> v(q r)) /\
              q 0 = q k /\
              w(q 0) /\
              ~(q(k - 1) = q 0) /\
              (!r. r < k ==> e (q r) (q(SUC r))))
        ==> ?k q.
              1 < k /\
              (!r. r <= k ==> v(q r)) /\
              q 0 = q k /\
              w(q 0) /\
              (!r s. r < s /\ s < k ==> ~(q r = q s)) /\
              (!r. r < k ==> e (q r) (q(SUC r)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "exists") THEN
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE
   (SPEC
    `\k. ?q:num->A.
              1 < k /\
              (!r. r <= k ==> v(q r)) /\
              q 0 = q k /\
              w(q 0) /\
              (!r. 0 < r /\ r < k ==> ~(q r = q 0)) /\
              (!r. r < k ==> e (q r) (q(SUC r)))`
    num_WOP)))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PATH_FIRST_RETURN_CYCLE THEN
    REMOVE_THEN "exists" MP_TAC THEN REWRITE_TAC[];
    INTRO_TAC
     "@k. (@q. length bound closed base first path) minimal"] THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `q:num->A`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN
  INTRO_TAC "rs sk" THEN
  DISCH_THEN(LABEL_TAC "repeat") THEN
  SUBGOAL_THEN `0 < r` (LABEL_TAC "rpos") THENL
   [ASM_CASES_TAC `(r:num) = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `r < k - (s - r) /\
    1 < k - (s - r) /\
    k - (s - r) < k`
  (DESTRUCT_TAC "after newlength shorter") THENL
   [MAP_EVERY (fun s -> USE_THEN s MP_TAC) ["rs"; "sk"; "rpos"] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "minimal"
   (MP_TAC o SPEC `(k:num) - (s - r)`) THEN
  USE_THEN "shorter" (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC
   `\i. if i <= r then (q:num->A) i else q(i + (s - r))` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "newlength" ACCEPT_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL
     [USE_THEN "bound" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "bound" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    BETA_TAC THEN REWRITE_TAC[LE_0] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN
    USE_THEN "rs" (fun rth ->
     USE_THEN "sk" (fun sth ->
      let eth = MATCH_MP
       (SPECL [`k:num`; `(s:num) - r`] SUB_ADD)
       (MATCH_MP
        (SPECL [`r:num`; `s:num`; `k:num`]
         (ARITH_RULE
          `!r s k:num.
               r < s /\ s < k ==> s - r <= k`))
        (CONJ rth sth)) in
      REWRITE_TAC[eth])) THEN
    USE_THEN "closed" ACCEPT_TAC;
    BETA_TAC THEN REWRITE_TAC[LE_0] THEN
    USE_THEN "base" ACCEPT_TAC;
    X_GEN_TAC `i:num` THEN
    INTRO_TAC "ipos ilt" THEN
    BETA_TAC THEN REWRITE_TAC[LE_0] THEN
    COND_CASES_TAC THENL
     [USE_THEN "first" (MATCH_MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      USE_THEN "first"
       (MATCH_MP_TAC o SPEC `(i:num) + (s - r)`) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `(i:num) < r` THENL
     [SUBGOAL_THEN
       `(i:num) <= r /\ SUC i <= r`
      STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        USE_THEN "path" MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ASM_CASES_TAC `(i:num) = r` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[LE_REFL;
          ARITH_RULE `~(SUC r <= r)`] THEN
        SUBGOAL_THEN
         `SUC r + (s - r) = SUC s`
        SUBST1_TAC THENL
         [ASM_ARITH_TAC;
          USE_THEN "path" (MATCH_MP_TAC o SPEC `s:num`) THEN
          ASM_REWRITE_TAC[]];
        SUBGOAL_THEN
         `~((i:num) <= r) /\ ~(SUC i <= r)`
        STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[ADD_CLAUSES] THEN
          USE_THEN "path" MATCH_MP_TAC THEN
          ASM_ARITH_TAC]]]]);;

let PATH_SHORTEST_SIMPLE_CYCLE = prove
 (`!v e w.
        (?k (q:num->A).
              1 < k /\
              (!r. r <= k ==> v(q r)) /\
              q 0 = q k /\
              w(q 0) /\
              ~(q(k - 1) = q 0) /\
              (!r. r < k ==> e (q r) (q(SUC r))))
        ==> ?k q.
              1 < k /\
              (!r. r <= k ==> v(q r)) /\
              q 0 = q k /\
              w(q 0) /\
              (!r s. r < s /\ s < k ==> ~(q r = q s)) /\
              (!r s. r + 1 < s /\ s < k ==> ~e (q r) (q s)) /\
              (!r. 0 < r /\ r + 1 < k ==> ~e (q r) (q 0)) /\
              (!r. r < k ==> e (q r) (q(SUC r)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "exists") THEN
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE
   (SPEC
    `\k. ?q:num->A.
              1 < k /\
              (!r. r <= k ==> v(q r)) /\
              q 0 = q k /\
              w(q 0) /\
              (!r s. r < s /\ s < k ==> ~(q r = q s)) /\
              (!r. r < k ==> e (q r) (q(SUC r)))`
    num_WOP)))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PATH_SIMPLE_CYCLE THEN
    REMOVE_THEN "exists" MP_TAC THEN REWRITE_TAC[];
    INTRO_TAC
     "@k. (@q. length bound closed base distinct path) minimal"] THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `q:num->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN STRIP_TAC THEN
    DISCH_THEN(LABEL_TAC "chord") THEN
    ABBREV_TAC `d = (s:num) - SUC r` THEN
    ABBREV_TAC `l = (k:num) - d` THEN
    SUBGOAL_THEN
     `0 < (d:num) /\ d <= k /\ 1 < l /\ l < k /\ l + d = k`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `SUC r + d = s` (LABEL_TAC "jump") THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
     `h = \i:num. if i <= r then (q:num->A) i else q(i + d)` THEN
    SUBGOAL_THEN
     `(!i. i <= l ==> v((h:num->A) i)) /\
      (!i. i < l
           ==> (if i <= r then i else i + d) < k) /\
      (!i j. i < j /\ j < l
             ==> (if i <= r then i else i + d) <
                 (if j <= r then j else j + d))`
    (DESTRUCT_TAC "hbound indexbound indexorder") THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
        BETA_TAC THEN COND_CASES_TAC THEN
        USE_THEN "bound" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        COND_CASES_TAC THEN ASM_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
        ASM_CASES_TAC `(i:num) <= r` THEN
        ASM_CASES_TAC `(j:num) <= r` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "minimal" (fun mth ->
      MP_TAC(MATCH_MP (SPEC `l:num` mth)
       (ASSUME `(l:num) < k`))) THEN
    REWRITE_TAC[TAUT `(~p ==> F) <=> p`] THEN
    EXISTS_TAC `h:num->A` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "hbound" ACCEPT_TAC;
      EXPAND_TAC "h" THEN BETA_TAC THEN
      SUBGOAL_THEN `0 <= (r:num) /\ ~(l <= r)`
      STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        USE_THEN "closed" ACCEPT_TAC];
      EXPAND_TAC "h" THEN BETA_TAC THEN
      REWRITE_TAC[LE_0] THEN USE_THEN "base" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      EXPAND_TAC "h" THEN BETA_TAC THEN
      REWRITE_TAC[GSYM COND_RAND] THEN
      USE_THEN "distinct" MATCH_MP_TAC THEN CONJ_TAC THENL
       [USE_THEN "indexorder"
         (MATCH_MP_TAC o SPECL [`i:num`; `j:num`]) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "indexbound" (MATCH_MP_TAC o SPEC `j:num`) THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
      BETA_TAC THEN ASM_CASES_TAC `(i:num) < r` THENL
       [SUBGOAL_THEN `(i:num) <= r /\ SUC i <= r`
        STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[] THEN
          USE_THEN "path" MATCH_MP_TAC THEN ASM_ARITH_TAC];
        ASM_CASES_TAC `(i:num) = r` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN
          ASM_REWRITE_TAC[LE_REFL;
            ARITH_RULE `~(SUC r <= r)`] THEN
          USE_THEN "jump" (fun th -> REWRITE_TAC[th]) THEN
          USE_THEN "chord" ACCEPT_TAC;
          SUBGOAL_THEN
           `~((i:num) <= r) /\ ~(SUC i <= r)`
          STRIP_ASSUME_TAC THENL
           [ASM_ARITH_TAC;
            ASM_REWRITE_TAC[ADD_CLAUSES] THEN
            USE_THEN "path" MATCH_MP_TAC THEN
            USE_THEN "indexbound" (fun ith ->
             ACCEPT_TAC(REWRITE_RULE[ASSUME `~((i:num) <= r)`]
              (MATCH_MP (SPEC `i:num` ith)
               (ASSUME `(i:num) < l`))))]]]];
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    DISCH_THEN(LABEL_TAC "return") THEN
    USE_THEN "minimal" (fun mth ->
      MP_TAC(MATCH_MP (SPEC `SUC r` mth)
       (MATCH_MP
        (ARITH_RULE
         `0 < r /\ r + 1 < k ==> SUC r < k`)
        (CONJ (ASSUME `0 < (r:num)`)
         (ASSUME `(r:num) + 1 < k`))))) THEN
    REWRITE_TAC[TAUT `(~p ==> F) <=> p`] THEN
    EXISTS_TAC
     `\i. if i < SUC r then (q:num->A) i else q 0` THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
      COND_CASES_TAC THEN USE_THEN "bound" MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      BETA_TAC THEN
      REWRITE_TAC[ARITH_RULE `0 < SUC r`;
                  ARITH_RULE `~(SUC r < SUC r)`];
      BETA_TAC THEN REWRITE_TAC[ARITH_RULE `0 < SUC r`] THEN
      USE_THEN "base" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(i:num) < SUC r` ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        BETA_TAC THEN ASM_REWRITE_TAC[]] THEN
      USE_THEN "distinct" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
      ASM_CASES_TAC `(i:num) < r` THENL
       [SUBGOAL_THEN
         `(i:num) < SUC r /\ SUC i < SUC r`
        STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[] THEN
          USE_THEN "path" MATCH_MP_TAC THEN ASM_ARITH_TAC];
        SUBGOAL_THEN `(i:num) = r` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[ARITH_RULE `r < SUC r`;
                          ARITH_RULE `~(SUC r < SUC r)`] THEN
          USE_THEN "return" ACCEPT_TAC]]]]);;

let PATH_SIMPLE_CYCLE_WAIT = prove
 (`!v e k (q:num->A).
        1 < k /\
        (!i. i <= k ==> v(q i)) /\
        q 0 = q k /\
        e (q 0) (q 0) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        (!i. i < k ==> e (q i) (q(SUC i)))
        ==> ?r.
              (!i. i <= k + 1 ==> v(r i)) /\
              r 0 = r(k + 1) /\
              (!i. 0 < i /\ i < k + 1 ==> ~(r i = r 0)) /\
              (!i. i < k + 1 ==> e (r i) (r(SUC i)))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "length bound closed base distinct path" THEN
  SUBGOAL_THEN `~((q:num->A) 0 = q 1)`
  (LABEL_TAC "different") THENL
   [USE_THEN "distinct" (MATCH_MP_TAC o SPECL [`0`; `1`]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 < j /\ j <= k ==> ~((q:num->A) j = q 1)`
  (LABEL_TAC "taildistinct") THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(j:num) = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "closed" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "different" ACCEPT_TAC;
      DISCH_THEN(LABEL_TAC "same") THEN
      ASM_MESON_TAC[LT_LE]];
    ALL_TAC] THEN
  EXISTS_TAC
   `\i. if i < k then (q:num->A)(SUC i)
        else if i = k then q 0 else q 1` THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `(i:num) < k` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "bound" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      COND_CASES_TAC THEN
      USE_THEN "bound" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    BETA_TAC THEN
    SUBGOAL_THEN `0 < (k:num)` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `~(k + 1 < k)`;
                      ARITH_RULE `~(k + 1 = k)`] THEN
      REWRITE_TAC[GSYM ONE]];
    X_GEN_TAC `i:num` THEN
    INTRO_TAC "ipos ilt" THEN
    BETA_TAC THEN
    SUBGOAL_THEN `0 < (k:num)` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(i:num) < k` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "taildistinct" (MP_TAC o SPEC `SUC i`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ONE]];
      SUBGOAL_THEN `(i:num) = k` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        USE_THEN "taildistinct" (MP_TAC o SPEC `k:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ONE]]]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `SUC(i:num) < k` THENL
     [SUBGOAL_THEN `(i:num) < k` ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        USE_THEN "path" MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ASM_CASES_TAC `(i:num) < k` THENL
       [SUBGOAL_THEN `SUC(i:num) = k` ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[LT_REFL] THEN
          USE_THEN "closed" (fun th -> REWRITE_TAC[GSYM th]) THEN
          USE_THEN "base" ACCEPT_TAC];
        SUBGOAL_THEN `(i:num) = k` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[LT_REFL;
            ARITH_RULE `~(SUC k < k)`;
            ARITH_RULE `~(SUC k = k)`] THEN
          USE_THEN "path" (MP_TAC o SPEC `0`) THEN
          ANTS_TAC THENL
           [USE_THEN "length" MP_TAC THEN ARITH_TAC;
            USE_THEN "closed" (fun th ->
             REWRITE_TAC[th; GSYM ONE])]]]]]);;

let PATH_SIMPLE_CYCLE_WAITS = prove
 (`!v e k (q:num->A) t.
        1 < k /\
        0 < t /\
        (!i. i <= k ==> v(q i)) /\
        q 0 = q k /\
        e (q 0) (q 0) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        (!i. i < k ==> e (q i) (q(SUC i)))
        ==> ?r.
              (!i. i <= k + t ==> v(r i)) /\
              r 0 = r(k + t) /\
              (!i. 0 < i /\ i < k + t ==> ~(r i = r 0)) /\
              (!i. i < k + t ==> e (r i) (r(SUC i)))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "length wait bound closed base distinct path" THEN
  SUBGOAL_THEN `~((q:num->A) 0 = q 1)`
  (LABEL_TAC "different") THENL
   [USE_THEN "distinct" (MATCH_MP_TAC o SPECL [`0`; `1`]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 < j /\ j <= k ==> ~((q:num->A) j = q 1)`
  (LABEL_TAC "taildistinct") THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(j:num) = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "closed" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "different" ACCEPT_TAC;
      DISCH_THEN(LABEL_TAC "same") THEN
      ASM_MESON_TAC[LT_LE]];
    ALL_TAC] THEN
  EXISTS_TAC
   `\i. if i < k then (q:num->A)(SUC i)
        else if i < k + t then q 0 else q 1` THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `(i:num) < k` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "bound" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      COND_CASES_TAC THEN
      USE_THEN "bound" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    BETA_TAC THEN
    SUBGOAL_THEN `0 < (k:num)` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[LT_REFL; GSYM ONE] THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:num` THEN
    INTRO_TAC "ipos ilt" THEN
    BETA_TAC THEN
    SUBGOAL_THEN `0 < (k:num)` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(i:num) < k` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "taildistinct" (MP_TAC o SPEC `SUC i`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ONE]];
      USE_THEN "closed" (fun th ->
       REWRITE_TAC[GSYM th; ARITH_RULE `SUC 0 = 1`]) THEN
      USE_THEN "different" ACCEPT_TAC];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_CASES_TAC `SUC(i:num) < k` THENL
     [SUBGOAL_THEN `(i:num) < k` ASSUME_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        USE_THEN "path" MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ASM_CASES_TAC `(i:num) < k` THENL
       [SUBGOAL_THEN `SUC(i:num) = k` ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          SUBGOAL_THEN `(k:num) < k + t` ASSUME_TAC THENL
           [ASM_ARITH_TAC;
            ASM_REWRITE_TAC[LT_REFL] THEN
            USE_THEN "closed" (fun th -> REWRITE_TAC[GSYM th]) THEN
            USE_THEN "base" ACCEPT_TAC]];
        SUBGOAL_THEN
         `i < k + t /\ ~(i < k) /\ ~(SUC i < k)`
        STRIP_ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          ASM_REWRITE_TAC[] THEN
          ASM_CASES_TAC `SUC(i:num) < k + t` THEN
          ASM_REWRITE_TAC[] THENL
           [USE_THEN "closed" (fun th -> REWRITE_TAC[GSYM th]) THEN
            USE_THEN "base" ACCEPT_TAC;
            USE_THEN "closed" (fun th ->
             REWRITE_TAC[GSYM th; ONE]) THEN
            USE_THEN "path" (MATCH_MP_TAC o SPEC `0`) THEN
            ASM_ARITH_TAC]]]]]);;

let FINITE_INDEX_ENUMERATION = prove
 (`!q (k:num).
        (!i. i < k ==> q i < k) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j))
        ==> !x. x < k ==> ?i. i < k /\ q i = x`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "bound distinct" THEN
  MP_TAC(ISPECL [`{i:num | i < k}`; `q:num->num`]
   SURJECTIVE_IFF_INJECTIVE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET;
                FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
     ONCE_REWRITE_TAC[REWRITE_RULE[IN_ELIM_THM] th])] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_MESON_TAC[LT_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Chordless zigzag paths in the adjacent-interval graph.                    *)
(* ------------------------------------------------------------------------- *)

let FINITE_PATH_NEXT_COVER = prove
 (`!p q k r x.
        (!i. i < k ==> q i < k) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        (!i j. i + 1 < j /\ j < k
               ==> ~adjacent_interval_cover p (q i) (q j)) /\
        r + 1 < k /\
        x < k /\
        adjacent_interval_cover p (q r) x /\
        (!s. s <= r ==> ~(q s = x))
        ==> x = q(r + 1)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "bound distinct chordless next xbound cover unseen" THEN
  MP_TAC(ISPECL [`q:num->num`; `k:num`]
   FINITE_INDEX_ENUMERATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    ASM_REWRITE_TAC[] THEN
    INTRO_TAC "@s. sbound same"] THEN
  ASM_MESON_TAC
   [NOT_LE;
    ARITH_RULE `!r s:num. r < s ==> s = r + 1 \/ r + 1 < s`]);;

let FINITE_PATH_NEXT_OUTSIDE = prove
 (`!(q:num->num) k r a b.
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        r + 1 < k /\
        (!s. s <= r ==> a <= q s /\ q s <= b) /\
        (!x. a <= x /\ x <= b ==> ?s. s <= r /\ q s = x)
        ==> q(r + 1) < a \/ b < q(r + 1)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "distinct next range full" THEN
  ASM_CASES_TAC `(q:num->num) (r + 1) < a` THENL
   [ASM_REWRITE_TAC[];
    ASM_CASES_TAC `b < (q:num->num) (r + 1)` THENL
     [ASM_REWRITE_TAC[];
      MP_TAC(SPEC `(q:num->num) (r + 1)`
      (ASSUME
        `!x. a <= x /\ x <= b
             ==> ?s. s <= r /\ (q:num->num) s = x`)) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        INTRO_TAC "@s. sle same"] THEN
      ASM_MESON_TAC
       [ARITH_RULE `!s r:num. s <= r ==> s < r + 1`]]]);;

let FINITE_PATH_ZIGZAG_DOWN = prove
 (`!p q k r a lo hi.
        (!i. i < k ==> q i < k) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        (!i j. i + 1 < j /\ j < k
               ==> ~adjacent_interval_cover p (q i) (q j)) /\
        r + 1 < k /\
        ~adjacent_interval_cover p (q r) a /\
        adjacent_interval_cover p (q r) (q(r + 1)) /\
        q r = hi /\
        p hi = lo /\
        lo <= a /\ a <= hi /\
        (!s. s <= r ==> lo <= q s /\ q s <= hi) /\
        (!x. lo <= x /\ x <= hi ==> ?s. s <= r /\ q s = x)
        ==> 0 < lo /\
            q(r + 1) = lo - 1 /\
            p(hi + 1) = lo - 1 /\
            (!s. s <= r + 1 ==> lo - 1 <= q s /\ q s <= hi) /\
            (!x. lo - 1 <= x /\ x <= hi
                 ==> ?s. s <= r + 1 /\ q s = x)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("bound distinct chordless next nobase cover last endpoint " ^
    "alower aupper range full") THEN
  SUBGOAL_THEN `(hi:num) < k` (LABEL_TAC "hibound") THENL
   [USE_THEN "bound" (MP_TAC o SPEC `r:num`) THEN
    USE_THEN "last" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "next" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(q:num->num) (r + 1) < lo \/ hi < q(r + 1)`
  (LABEL_TAC "outside") THENL
   [MATCH_MP_TAC(ISPECL
     [`q:num->num`; `k:num`; `r:num`; `lo:num`; `hi:num`]
     FINITE_PATH_NEXT_OUTSIDE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) (hi + 1) <= a`
  (LABEL_TAC "otherbelow") THENL
   [MP_TAC(ASSUME
     `~adjacent_interval_cover (p:num->num)
        ((q:num->num) (r:num)) a`) THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:num->num) (r + 1) < lo`
  (LABEL_TAC "nextbelow") THENL
   [USE_THEN "outside" DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME
     `adjacent_interval_cover (p:num->num)
        ((q:num->num) (r:num)) (q(r + 1))`) THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:num->num) (hi + 1) <= q(r + 1) /\
    q(r + 1) + 1 <= lo`
  (LABEL_TAC "orientation") THENL
   [MP_TAC(ASSUME
     `adjacent_interval_cover (p:num->num)
        ((q:num->num) (r:num)) (q(r + 1))`) THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < (lo:num)` (LABEL_TAC "lopos") THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `adjacent_interval_cover (p:num->num)
      ((q:num->num) (r:num)) (lo - 1)`
  (LABEL_TAC "coverspredecessor") THENL
   [REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(lo:num) - 1 = q(r + 1)`
  (LABEL_TAC "nextvalue") THENL
   [MATCH_MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `r:num`; `lo - 1`]
     FINITE_PATH_NEXT_COVER) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `s:num` THEN DISCH_TAC THEN
      USE_THEN "range" (MP_TAC o SPEC `s:num`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN STRIP_ASSUME_TAC] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `adjacent_interval_cover (p:num->num)
      ((q:num->num) (r:num)) (p(hi + 1))`
  (LABEL_TAC "coversendpoint") THENL
   [REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) (hi + 1) = q(r + 1)`
  (LABEL_TAC "endpointvalue") THENL
   [MATCH_MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `r:num`;
      `(p:num->num) (hi + 1)`]
     FINITE_PATH_NEXT_COVER) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `s:num` THEN DISCH_TAC THEN
      USE_THEN "range" (MP_TAC o SPEC `s:num`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN STRIP_ASSUME_TAC] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(s:num) <= r` THENL
     [USE_THEN "range" (MP_TAC o SPEC `s:num`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN STRIP_ASSUME_TAC] THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `(s:num) = r + 1` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:num) = lo - 1` THENL
     [EXISTS_TAC `r + 1` THEN ASM_REWRITE_TAC[LE_REFL];
      USE_THEN "full" (MP_TAC o SPEC `x:num`) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `s:num` STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let FINITE_PATH_ZIGZAG_UP = prove
 (`!p q k r a lo hi.
        (!i. i <= k ==> p i <= k) /\
        (!i. i < k ==> q i < k) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        (!i j. i + 1 < j /\ j < k
               ==> ~adjacent_interval_cover p (q i) (q j)) /\
        r + 1 < k /\
        ~adjacent_interval_cover p (q r) a /\
        adjacent_interval_cover p (q r) (q(r + 1)) /\
        q r = lo /\
        p(lo + 1) = hi + 1 /\
        lo <= a /\ a <= hi /\
        (!s. s <= r ==> lo <= q s /\ q s <= hi) /\
        (!x. lo <= x /\ x <= hi ==> ?s. s <= r /\ q s = x)
        ==> q(r + 1) = hi + 1 /\
            p lo = hi + 2 /\
            (!s. s <= r + 1 ==> lo <= q s /\ q s <= hi + 1) /\
            (!x. lo <= x /\ x <= hi + 1
                 ==> ?s. s <= r + 1 /\ q s = x)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("pbound bound distinct chordless next nobase cover last " ^
    "endpoint alower aupper range full") THEN
  SUBGOAL_THEN `(lo:num) < k` (LABEL_TAC "lobound") THENL
   [USE_THEN "bound" (MP_TAC o SPEC `r:num`) THEN
    USE_THEN "last" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "next" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:num->num) (r + 1) < k`
  (LABEL_TAC "nextbound") THENL
   [USE_THEN "bound" (MP_TAC o SPEC `r + 1`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(q:num->num) (r + 1) < lo \/ hi < q(r + 1)`
  (LABEL_TAC "outside") THENL
   [MATCH_MP_TAC(ISPECL
     [`q:num->num`; `k:num`; `r:num`; `lo:num`; `hi:num`]
     FINITE_PATH_NEXT_OUTSIDE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < (p:num->num) lo`
  (LABEL_TAC "otherabove") THENL
   [MP_TAC(ASSUME
     `~adjacent_interval_cover (p:num->num)
        ((q:num->num) (r:num)) a`) THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hi < (q:num->num) (r + 1)`
  (LABEL_TAC "nextabove") THENL
   [USE_THEN "outside" DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME
     `adjacent_interval_cover (p:num->num)
        ((q:num->num) (r:num)) (q(r + 1))`) THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hi + 1 <= (q:num->num) (r + 1) /\
    q(r + 1) + 1 <= (p:num->num) lo`
  (LABEL_TAC "orientation") THENL
   [MP_TAC(ASSUME
     `adjacent_interval_cover (p:num->num)
        ((q:num->num) (r:num)) (q(r + 1))`) THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `adjacent_interval_cover (p:num->num)
      ((q:num->num) (r:num)) (hi + 1)`
  (LABEL_TAC "coverssuccessor") THENL
   [REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(hi:num) + 1 = q(r + 1)`
  (LABEL_TAC "nextvalue") THENL
   [MATCH_MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `r:num`; `hi + 1`]
     FINITE_PATH_NEXT_COVER) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `s:num` THEN DISCH_TAC THEN
      USE_THEN "range" (MP_TAC o SPEC `s:num`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN STRIP_ASSUME_TAC] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) lo <= k`
  (LABEL_TAC "otherbound") THENL
   [USE_THEN "pbound" (MP_TAC o SPEC `lo:num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) lo = hi + 2`
  (LABEL_TAC "endpointvalue") THENL
   [ASM_CASES_TAC `(p:num->num) lo = hi + 2` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hi + 2 < (p:num->num) lo`
    (LABEL_TAC "gap") THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `adjacent_interval_cover (p:num->num)
        ((q:num->num) (r:num)) (hi + 2)`
    (LABEL_TAC "coversgap") THENL
     [REWRITE_TAC[adjacent_interval_cover] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(hi:num) + 2 = q(r + 1)`
    (LABEL_TAC "gapvalue") THENL
     [MATCH_MP_TAC(ISPECL
       [`p:num->num`; `q:num->num`; `k:num`; `r:num`; `hi + 2`]
       FINITE_PATH_NEXT_COVER) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        X_GEN_TAC `s:num` THEN DISCH_TAC THEN
        USE_THEN "range" (MP_TAC o SPEC `s:num`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[];
          DISCH_THEN STRIP_ASSUME_TAC] THEN
        ASM_ARITH_TAC];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(s:num) <= r` THENL
     [USE_THEN "range" (MP_TAC o SPEC `s:num`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN STRIP_ASSUME_TAC] THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `(s:num) = r + 1` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:num) = hi + 1` THENL
     [EXISTS_TAC `r + 1` THEN ASM_REWRITE_TAC[LE_REFL];
      USE_THEN "full" (MP_TAC o SPEC `x:num`) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `s:num` STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC `s:num` THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC]]);;

let FINITE_PATH_ZIGZAG_LEFT_START = prove
 (`!p q k a.
        (!i. i <= k ==> p i <= k) /\
        (!i. i < k ==> q i < k) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        (!i j. i + 1 < j /\ j < k
               ==> ~adjacent_interval_cover p (q i) (q j)) /\
        1 < k /\
        q 0 = a /\
        p(a + 1) <= a /\
        a + 1 <= p a /\
        q 1 < a /\
        adjacent_interval_cover p (q 0) (q 1)
        ==> 0 < a /\
            q 1 = a - 1 /\
            p(a + 1) = a - 1 /\
            p a = a + 1 /\
            (!s. s <= 1 ==> a - 1 <= q s /\ q s <= a) /\
            (!x. a - 1 <= x /\ x <= a
                 ==> ?s. s <= 1 /\ q s = x)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("pbound bound distinct chordless nontrivial base lower " ^
    "upper left cover") THEN
  SUBGOAL_THEN `(a:num) < k` (LABEL_TAC "abound") THENL
   [USE_THEN "bound" (MP_TAC o SPEC `0`) THEN
    USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "nontrivial" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:num->num) 1 < k`
  (LABEL_TAC "q1bound") THENL
   [USE_THEN "bound" (MP_TAC o SPEC `1`) THEN
    USE_THEN "nontrivial" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP
   (ISPECL
     [`(p:num->num) a`; `(p:num->num) (a + 1)`;
      `(q:num->num) 1`; `a:num`]
     (ARITH_RULE
      `!pa pa1 q a:num.
          q < a /\ a + 1 <= pa
          ==> ~(pa <= q /\ q + 1 <= pa1)`))
   (CONJ (ASSUME `(q:num->num) 1 < a`)
    (ASSUME `(a:num) + 1 <= (p:num->num) a`))) THEN
  SUBGOAL_THEN
   `(p:num->num) (a + 1) <= q 1 /\ q 1 + 1 <= p a`
  (LABEL_TAC "orientation") THENL
   [MP_TAC(ASSUME
     `adjacent_interval_cover (p:num->num) (q 0) (q 1)`) THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < (a:num)` (LABEL_TAC "apos") THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `adjacent_interval_cover (p:num->num) (q 0) (a - 1)`
  (LABEL_TAC "coverspredecessor") THENL
   [REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) - 1 = q 1`
  (LABEL_TAC "nextvalue") THENL
   [(MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `0`; `a - 1`]
     FINITE_PATH_NEXT_COVER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "bound" ACCEPT_TAC;
        USE_THEN "distinct" ACCEPT_TAC;
        USE_THEN "chordless" ACCEPT_TAC;
        ASM_ARITH_TAC;
        ASM_ARITH_TAC;
        USE_THEN "coverspredecessor" ACCEPT_TAC;
        X_GEN_TAC `s:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(s:num) = 0` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC;
          USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
          ASM_ARITH_TAC]];
      DISCH_THEN(fun th ->
       ACCEPT_TAC(REWRITE_RULE[ADD_CLAUSES] th))]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `adjacent_interval_cover (p:num->num) (q 0) (p(a + 1))`
  (LABEL_TAC "coverslower") THENL
   [REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) (a + 1) = q 1`
  (LABEL_TAC "lowervalue") THENL
   [(MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `0`;
      `(p:num->num) (a + 1)`]
     FINITE_PATH_NEXT_COVER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "bound" ACCEPT_TAC;
        USE_THEN "distinct" ACCEPT_TAC;
        USE_THEN "chordless" ACCEPT_TAC;
        ASM_ARITH_TAC;
        ASM_ARITH_TAC;
        USE_THEN "coverslower" ACCEPT_TAC;
        X_GEN_TAC `s:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(s:num) = 0` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC;
          USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
          ASM_ARITH_TAC]];
      DISCH_THEN(fun th ->
       ACCEPT_TAC(REWRITE_RULE[ADD_CLAUSES] th))]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) a <= k`
  (LABEL_TAC "pabound") THENL
   [USE_THEN "pbound" (MP_TAC o SPEC `a:num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) a = a + 1`
  (LABEL_TAC "uppervalue") THENL
   [ASM_CASES_TAC `(p:num->num) a = a + 1` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:num) + 1 < p a`
    (LABEL_TAC "gap") THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `adjacent_interval_cover (p:num->num) (q 0) (a + 1)`
    (LABEL_TAC "coversgap") THENL
     [REWRITE_TAC[adjacent_interval_cover] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:num) + 1 = q 1`
    (LABEL_TAC "gapvalue") THENL
     [(MP_TAC(ISPECL
       [`p:num->num`; `q:num->num`; `k:num`; `0`; `a + 1`]
       FINITE_PATH_NEXT_COVER) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "bound" ACCEPT_TAC;
          USE_THEN "distinct" ACCEPT_TAC;
          USE_THEN "chordless" ACCEPT_TAC;
          ASM_ARITH_TAC;
          ASM_ARITH_TAC;
          USE_THEN "coversgap" ACCEPT_TAC;
          X_GEN_TAC `s:num` THEN DISCH_TAC THEN
          SUBGOAL_THEN `(s:num) = 0` SUBST_ALL_TAC THENL
           [ASM_ARITH_TAC;
            USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
            ASM_ARITH_TAC]];
        DISCH_THEN(fun th ->
         ACCEPT_TAC(REWRITE_RULE[ADD_CLAUSES] th))]);
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(s:num) = 0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `(s:num) = 1` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:num) = a - 1` THENL
     [EXISTS_TAC `1` THEN ASM_REWRITE_TAC[LE_REFL];
      EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let FINITE_PATH_ZIGZAG_RIGHT_START = prove
 (`!p q k a.
        (!i. i <= k ==> p i <= k) /\
        (!i. i < k ==> q i < k) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        (!i j. i + 1 < j /\ j < k
               ==> ~adjacent_interval_cover p (q i) (q j)) /\
        1 < k /\
        q 0 = a /\
        p(a + 1) <= a /\
        a + 1 <= p a /\
        a < q 1 /\
        adjacent_interval_cover p (q 0) (q 1)
        ==> q 1 = a + 1 /\
            p(a + 1) = a /\
            p a = a + 2 /\
            (!s. s <= 1 ==> a <= q s /\ q s <= a + 1) /\
            (!x. a <= x /\ x <= a + 1
                 ==> ?s. s <= 1 /\ q s = x)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("pbound bound distinct chordless nontrivial base lower " ^
    "upper right cover") THEN
  SUBGOAL_THEN `(a:num) < k` (LABEL_TAC "abound") THENL
   [USE_THEN "bound" (MP_TAC o SPEC `0`) THEN
    USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "nontrivial" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:num->num) 1 < k`
  (LABEL_TAC "q1bound") THENL
   [USE_THEN "bound" (MP_TAC o SPEC `1`) THEN
    USE_THEN "nontrivial" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP
   (ISPECL
     [`(p:num->num) a`; `(p:num->num) (a + 1)`;
      `(q:num->num) 1`; `a:num`]
     (ARITH_RULE
      `!pa pa1 q a:num.
          pa1 <= a /\ a < q
          ==> ~(pa <= q /\ q + 1 <= pa1)`))
   (CONJ (ASSUME `(p:num->num) (a + 1) <= a`)
    (ASSUME `(a:num) < (q:num->num) 1`))) THEN
  SUBGOAL_THEN
   `(p:num->num) (a + 1) <= q 1 /\ q 1 + 1 <= p a`
  (LABEL_TAC "orientation") THENL
   [MP_TAC(ASSUME
     `adjacent_interval_cover (p:num->num) (q 0) (q 1)`) THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `adjacent_interval_cover (p:num->num) (q 0) (a + 1)`
  (LABEL_TAC "coverssuccessor") THENL
   [REWRITE_TAC[adjacent_interval_cover] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) + 1 = q 1`
  (LABEL_TAC "nextvalue") THENL
   [(MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `0`; `a + 1`]
     FINITE_PATH_NEXT_COVER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "bound" ACCEPT_TAC;
        USE_THEN "distinct" ACCEPT_TAC;
        USE_THEN "chordless" ACCEPT_TAC;
        ASM_ARITH_TAC;
        ASM_ARITH_TAC;
        USE_THEN "coverssuccessor" ACCEPT_TAC;
        X_GEN_TAC `s:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(s:num) = 0` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC;
          USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
          ASM_ARITH_TAC]];
      DISCH_THEN(fun th ->
       ACCEPT_TAC(REWRITE_RULE[ADD_CLAUSES] th))]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) (a + 1) = a`
  (LABEL_TAC "lowervalue") THENL
   [ASM_CASES_TAC `(p:num->num) (a + 1) = a` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p:num->num) (a + 1) < a`
    (LABEL_TAC "gap") THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `adjacent_interval_cover (p:num->num) (q 0) (p(a + 1))`
    (LABEL_TAC "coversgap") THENL
     [REWRITE_TAC[adjacent_interval_cover] THEN
      USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
      DISJ2_TAC THEN REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:num->num) (a + 1) = q 1`
    (LABEL_TAC "gapvalue") THENL
     [(MP_TAC(ISPECL
       [`p:num->num`; `q:num->num`; `k:num`; `0`;
        `(p:num->num) (a + 1)`]
       FINITE_PATH_NEXT_COVER) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "bound" ACCEPT_TAC;
          USE_THEN "distinct" ACCEPT_TAC;
          USE_THEN "chordless" ACCEPT_TAC;
          ASM_ARITH_TAC;
          ASM_ARITH_TAC;
          USE_THEN "coversgap" ACCEPT_TAC;
          X_GEN_TAC `s:num` THEN DISCH_TAC THEN
          SUBGOAL_THEN `(s:num) = 0` SUBST_ALL_TAC THENL
           [ASM_ARITH_TAC;
            USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
            ASM_ARITH_TAC]];
        DISCH_THEN(fun th ->
         ACCEPT_TAC(REWRITE_RULE[ADD_CLAUSES] th))]);
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) a <= k`
  (LABEL_TAC "pabound") THENL
   [USE_THEN "pbound" (MP_TAC o SPEC `a:num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) a = a + 2`
  (LABEL_TAC "uppervalue") THENL
   [ASM_CASES_TAC `(p:num->num) a = a + 2` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:num) + 2 < p a`
    (LABEL_TAC "gap") THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `adjacent_interval_cover (p:num->num) (q 0) (a + 2)`
    (LABEL_TAC "coversgap") THENL
     [REWRITE_TAC[adjacent_interval_cover] THEN
      USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
      DISJ2_TAC THEN
      USE_THEN "lowervalue" (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:num) + 2 = q 1`
    (LABEL_TAC "gapvalue") THENL
     [(MP_TAC(ISPECL
       [`p:num->num`; `q:num->num`; `k:num`; `0`; `a + 2`]
       FINITE_PATH_NEXT_COVER) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "bound" ACCEPT_TAC;
          USE_THEN "distinct" ACCEPT_TAC;
          USE_THEN "chordless" ACCEPT_TAC;
          ASM_ARITH_TAC;
          ASM_ARITH_TAC;
          USE_THEN "coversgap" ACCEPT_TAC;
          X_GEN_TAC `s:num` THEN DISCH_TAC THEN
          SUBGOAL_THEN `(s:num) = 0` SUBST_ALL_TAC THENL
           [ASM_ARITH_TAC;
            USE_THEN "base" (fun th -> REWRITE_TAC[th]) THEN
            ASM_ARITH_TAC]];
        DISCH_THEN(fun th ->
         ACCEPT_TAC(REWRITE_RULE[ADD_CLAUSES] th))]);
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(s:num) = 0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `(s:num) = 1` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:num) = a + 1` THENL
     [EXISTS_TAC `1` THEN ASM_REWRITE_TAC[LE_REFL];
      EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let FINITE_PATH_ZIGZAG_LEFT = prove
 (`!p q k a.
        (!i. i <= k ==> p i <= k) /\
        (!i. i < k ==> q i < k) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        (!i j. i + 1 < j /\ j < k
               ==> ~adjacent_interval_cover p (q i) (q j)) /\
        (!r. 0 < r /\ r + 1 < k
             ==> ~adjacent_interval_cover p (q r) (q 0)) /\
        (!r. r < k
             ==> adjacent_interval_cover p (q r) (q(r + 1))) /\
        1 < k /\
        q 0 = a /\
        p(a + 1) <= a /\
        a + 1 <= p a /\
        q 1 < a
        ==> !t. 2 * t + 1 < k
                ==> t < a /\
                    q(2 * t) = a + t /\
                    q(2 * t + 1) = a - t - 1 /\
                    p(a - t) = a + t + 1 /\
                    p(a + t + 1) = a - t - 1 /\
                    (!s. s <= 2 * t + 1
                         ==> a - t - 1 <= q s /\ q s <= a + t) /\
                    (!x. a - t - 1 <= x /\ x <= a + t
                         ==> ?s. s <= 2 * t + 1 /\ q s = x)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("pbound bound distinct chordless nobase path nontrivial " ^
    "base lower upper left") THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `a:num`]
     FINITE_PATH_ZIGZAG_LEFT_START) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "path" (MP_TAC o SPEC `0`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 < k ==> 0 < k`) THEN
        USE_THEN "nontrivial" ACCEPT_TAC;
        DISCH_THEN(fun th ->
         USE_THEN "base" (fun eth ->
          ACCEPT_TAC(REWRITE_RULE[eth; ADD_CLAUSES] th)))];
      STRIP_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0]];
    POP_ASSUM(LABEL_TAC "induction") THEN
    DISCH_THEN(LABEL_TAC "target") THEN
    USE_THEN "induction" MP_TAC THEN
    ANTS_TAC THENL
     [USE_THEN "target" MP_TAC THEN ARITH_TAC;
      INTRO_TAC "tlt qeven qodd plow phigh range full"] THEN
    MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `2 * (t:num) + 1`;
      `a:num`; `(a:num) - t - 1`; `(a:num) + t`]
     FINITE_PATH_ZIGZAG_UP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "pbound" ACCEPT_TAC;
        USE_THEN "bound" ACCEPT_TAC;
        USE_THEN "distinct" ACCEPT_TAC;
        USE_THEN "chordless" ACCEPT_TAC;
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "base" (fun th -> REWRITE_TAC[GSYM th]) THEN
        USE_THEN "nobase" MATCH_MP_TAC THEN
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "path" MATCH_MP_TAC THEN
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "qodd" ACCEPT_TAC;
        SUBGOAL_THEN `(a - t - 1) + 1 = a - t`
        SUBST1_TAC THENL
         [USE_THEN "tlt" MP_TAC THEN ARITH_TAC;
          USE_THEN "plow" (fun th -> REWRITE_TAC[th]) THEN
          ARITH_TAC];
        ACCEPT_TAC(ARITH_RULE `(a:num) - t - 1 <= a`);
        ACCEPT_TAC(ARITH_RULE `(a:num) <= a + t`);
        USE_THEN "range" ACCEPT_TAC;
        USE_THEN "full" ACCEPT_TAC];
      INTRO_TAC "qnext pnext nextrange nextfull"] THEN
    MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `2 * (t:num) + 2`;
      `a:num`; `(a:num) - t - 1`; `(a:num) + t + 1`]
     FINITE_PATH_ZIGZAG_DOWN) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "bound" ACCEPT_TAC;
        USE_THEN "distinct" ACCEPT_TAC;
        USE_THEN "chordless" ACCEPT_TAC;
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "base" (fun th -> REWRITE_TAC[GSYM th]) THEN
        USE_THEN "nobase" MATCH_MP_TAC THEN
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "path" MATCH_MP_TAC THEN
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        TRANS_TAC EQ_TRANS `(q:num->num)((2 * t + 1) + 1)` THEN
        CONJ_TAC THENL
         [AP_TERM_TAC THEN ARITH_TAC;
          USE_THEN "qnext" (fun th -> REWRITE_TAC[th]) THEN
          ARITH_TAC];
        USE_THEN "phigh" ACCEPT_TAC;
        ACCEPT_TAC(ARITH_RULE `(a:num) - t - 1 <= a`);
        ACCEPT_TAC(ARITH_RULE `(a:num) <= a + t + 1`);
        X_GEN_TAC `s:num` THEN DISCH_THEN(LABEL_TAC "sle") THEN
        USE_THEN "nextrange" (MP_TAC o SPEC `s:num`) THEN
        ANTS_TAC THENL
         [USE_THEN "sle" MP_TAC THEN ARITH_TAC;
          INTRO_TAC "slow shigh"] THEN
        CONJ_TAC THENL
         [USE_THEN "slow" ACCEPT_TAC;
          MATCH_MP_TAC(ARITH_RULE
           `x <= (a + t) + 1 ==> x <= a + t + 1`) THEN
          USE_THEN "shigh" ACCEPT_TAC];
        X_GEN_TAC `x:num` THEN
        INTRO_TAC "xlow xhigh" THEN
        USE_THEN "nextfull" (MP_TAC o SPEC `x:num`) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [USE_THEN "xlow" ACCEPT_TAC;
            MATCH_MP_TAC(ARITH_RULE
             `x <= a + t + 1 ==> x <= (a + t) + 1`) THEN
            USE_THEN "xhigh" ACCEPT_TAC];
          INTRO_TAC "@s. sle qs"] THEN
        EXISTS_TAC `s:num` THEN CONJ_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE
           `s <= (2 * t + 1) + 1 ==> s <= 2 * t + 2`) THEN
          USE_THEN "sle" ACCEPT_TAC;
          USE_THEN "qs" ACCEPT_TAC]];
      INTRO_TAC "lopos qoddnext phighnext finalrange finalfull"] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `0 < a - t - 1 ==> SUC t < a`) THEN
      USE_THEN "lopos" ACCEPT_TAC;
      TRANS_TAC EQ_TRANS
       `(q:num->num)((2 * t + 1) + 1)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN
        ACCEPT_TAC(ARITH_RULE
         `2 * SUC t = (2 * t + 1) + 1`);
        USE_THEN "qnext" (fun th -> REWRITE_TAC[th]) THEN
        ACCEPT_TAC(ARITH_RULE
         `(a + t) + 1 = a + SUC t`)];
      TRANS_TAC EQ_TRANS
       `(q:num->num)((2 * t + 2) + 1)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN
        ACCEPT_TAC(ARITH_RULE
         `2 * SUC t + 1 = (2 * t + 2) + 1`);
        USE_THEN "qoddnext" (fun th -> REWRITE_TAC[th]) THEN
        ACCEPT_TAC(ARITH_RULE
         `(a - t - 1) - 1 = a - SUC t - 1`)];
      TRANS_TAC EQ_TRANS `(p:num->num)(a - t - 1)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN
        ACCEPT_TAC(ARITH_RULE
         `a - SUC t = a - t - 1`);
        USE_THEN "pnext" (fun th -> REWRITE_TAC[th]) THEN
        ACCEPT_TAC(ARITH_RULE
         `(a + t) + 2 = a + SUC t + 1`)];
      TRANS_TAC EQ_TRANS `(p:num->num)((a + t + 1) + 1)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN
        ACCEPT_TAC(ARITH_RULE
         `a + SUC t + 1 = (a + t + 1) + 1`);
        USE_THEN "phighnext" (fun th -> REWRITE_TAC[th]) THEN
        ACCEPT_TAC(ARITH_RULE
         `(a - t - 1) - 1 = a - SUC t - 1`)];
      X_GEN_TAC `s:num` THEN DISCH_THEN(LABEL_TAC "sle") THEN
      USE_THEN "finalrange" (MP_TAC o SPEC `s:num`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `s <= 2 * SUC t + 1 ==> s <= (2 * t + 2) + 1`) THEN
        USE_THEN "sle" ACCEPT_TAC;
        INTRO_TAC "slow shigh"] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `(a - t - 1) - 1 <= x ==> a - SUC t - 1 <= x`) THEN
        USE_THEN "slow" ACCEPT_TAC;
        MATCH_MP_TAC(ARITH_RULE
         `x <= a + t + 1 ==> x <= a + SUC t`) THEN
        USE_THEN "shigh" ACCEPT_TAC];
      X_GEN_TAC `x:num` THEN
      INTRO_TAC "xlow xhigh" THEN
      USE_THEN "finalfull" (MP_TAC o SPEC `x:num`) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE
           `a - SUC t - 1 <= x ==> (a - t - 1) - 1 <= x`) THEN
          USE_THEN "xlow" ACCEPT_TAC;
          MATCH_MP_TAC(ARITH_RULE
           `x <= a + SUC t ==> x <= a + t + 1`) THEN
          USE_THEN "xhigh" ACCEPT_TAC];
        INTRO_TAC "@s. sle qs"] THEN
      EXISTS_TAC `s:num` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `s <= (2 * t + 2) + 1 ==> s <= 2 * SUC t + 1`) THEN
        USE_THEN "sle" ACCEPT_TAC;
        USE_THEN "qs" ACCEPT_TAC]]]);;

let FINITE_PATH_ZIGZAG_RIGHT = prove
 (`!p q k a.
        (!i. i <= k ==> p i <= k) /\
        (!i. i < k ==> q i < k) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        (!i j. i + 1 < j /\ j < k
               ==> ~adjacent_interval_cover p (q i) (q j)) /\
        (!r. 0 < r /\ r + 1 < k
             ==> ~adjacent_interval_cover p (q r) (q 0)) /\
        (!r. r < k
             ==> adjacent_interval_cover p (q r) (q(r + 1))) /\
        1 < k /\
        q 0 = a /\
        p(a + 1) <= a /\
        a + 1 <= p a /\
        a < q 1
        ==> !t. 2 * t + 1 < k
                ==> t <= a /\
                    q(2 * t) = a - t /\
                    q(2 * t + 1) = a + t + 1 /\
                    p(a - t) = a + t + 2 /\
                    p(a + t + 1) = a - t /\
                    (!s. s <= 2 * t + 1
                         ==> a - t <= q s /\ q s <= a + t + 1) /\
                    (!x. a - t <= x /\ x <= a + t + 1
                         ==> ?s. s <= 2 * t + 1 /\ q s = x)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("pbound bound distinct chordless nobase path nontrivial " ^
    "base lower upper right") THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `a:num`]
     FINITE_PATH_ZIGZAG_RIGHT_START) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "path" (MP_TAC o SPEC `0`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `1 < k ==> 0 < k`) THEN
        USE_THEN "nontrivial" ACCEPT_TAC;
        DISCH_THEN(fun th ->
         USE_THEN "base" (fun eth ->
          ACCEPT_TAC(REWRITE_RULE[eth; ADD_CLAUSES] th)))];
      STRIP_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; LE_0]];
    POP_ASSUM(LABEL_TAC "induction") THEN
    DISCH_THEN(LABEL_TAC "target") THEN
    USE_THEN "induction" MP_TAC THEN
    ANTS_TAC THENL
     [USE_THEN "target" MP_TAC THEN ARITH_TAC;
      INTRO_TAC "tle qeven qodd plow phigh range full"] THEN
    MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `2 * (t:num) + 1`;
      `a:num`; `(a:num) - t`; `(a:num) + t + 1`]
     FINITE_PATH_ZIGZAG_DOWN) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "bound" ACCEPT_TAC;
        USE_THEN "distinct" ACCEPT_TAC;
        USE_THEN "chordless" ACCEPT_TAC;
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "base" (fun th -> REWRITE_TAC[GSYM th]) THEN
        USE_THEN "nobase" MATCH_MP_TAC THEN
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "path" MATCH_MP_TAC THEN
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "qodd" ACCEPT_TAC;
        USE_THEN "phigh" ACCEPT_TAC;
        ACCEPT_TAC(ARITH_RULE `(a:num) - t <= a`);
        ACCEPT_TAC(ARITH_RULE `(a:num) <= a + t + 1`);
        USE_THEN "range" ACCEPT_TAC;
        USE_THEN "full" ACCEPT_TAC];
      INTRO_TAC "lopos qnext phighnext nextrange nextfull"] THEN
    MP_TAC(ISPECL
     [`p:num->num`; `q:num->num`; `k:num`; `2 * (t:num) + 2`;
      `a:num`; `(a:num) - t - 1`; `(a:num) + t + 1`]
     FINITE_PATH_ZIGZAG_UP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "pbound" ACCEPT_TAC;
        USE_THEN "bound" ACCEPT_TAC;
        USE_THEN "distinct" ACCEPT_TAC;
        USE_THEN "chordless" ACCEPT_TAC;
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "base" (fun th -> REWRITE_TAC[GSYM th]) THEN
        USE_THEN "nobase" MATCH_MP_TAC THEN
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        USE_THEN "path" MATCH_MP_TAC THEN
        USE_THEN "target" MP_TAC THEN ARITH_TAC;
        TRANS_TAC EQ_TRANS
         `(q:num->num)((2 * t + 1) + 1)` THEN
        CONJ_TAC THENL
         [AP_TERM_TAC THEN ARITH_TAC;
          USE_THEN "qnext" (fun th -> REWRITE_TAC[th]) THEN
          ARITH_TAC];
        SUBGOAL_THEN `(a - t - 1) + 1 = a - t`
        SUBST1_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE
           `0 < a - t ==> (a - t - 1) + 1 = a - t`) THEN
          USE_THEN "lopos" ACCEPT_TAC;
          USE_THEN "plow" (fun th -> REWRITE_TAC[th]) THEN
          ARITH_TAC];
        ACCEPT_TAC(ARITH_RULE `(a:num) - t - 1 <= a`);
        ACCEPT_TAC(ARITH_RULE `(a:num) <= a + t + 1`);
        X_GEN_TAC `s:num` THEN DISCH_THEN(LABEL_TAC "sle") THEN
        USE_THEN "nextrange" (MP_TAC o SPEC `s:num`) THEN
        ANTS_TAC THENL
         [USE_THEN "sle" MP_TAC THEN ARITH_TAC;
          INTRO_TAC "slow shigh"] THEN
        CONJ_TAC THENL
         [USE_THEN "slow" ACCEPT_TAC;
          USE_THEN "shigh" ACCEPT_TAC];
        X_GEN_TAC `x:num` THEN STRIP_TAC THEN
        USE_THEN "nextfull" (MP_TAC o SPEC `x:num`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN ARITH_TAC;
          INTRO_TAC "@s. sle qs"] THEN
        EXISTS_TAC `s:num` THEN CONJ_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE
           `s <= (2 * t + 1) + 1 ==> s <= 2 * t + 2`) THEN
          USE_THEN "sle" ACCEPT_TAC;
          USE_THEN "qs" ACCEPT_TAC]];
      INTRO_TAC "qoddnext plownext finalrange finalfull"] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `0 < a - t ==> SUC t <= a`) THEN
      USE_THEN "lopos" ACCEPT_TAC;
      TRANS_TAC EQ_TRANS
       `(q:num->num)((2 * t + 1) + 1)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN
        ACCEPT_TAC(ARITH_RULE
         `2 * SUC t = (2 * t + 1) + 1`);
        USE_THEN "qnext" (fun th -> REWRITE_TAC[th]) THEN
        ACCEPT_TAC(ARITH_RULE
         `(a - t) - 1 = a - SUC t`)];
      TRANS_TAC EQ_TRANS
       `(q:num->num)((2 * t + 2) + 1)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN
        ACCEPT_TAC(ARITH_RULE
         `2 * SUC t + 1 = (2 * t + 2) + 1`);
        USE_THEN "qoddnext" (fun th -> REWRITE_TAC[th]) THEN
        ACCEPT_TAC(ARITH_RULE
         `(a + t + 1) + 1 = a + SUC t + 1`)];
      TRANS_TAC EQ_TRANS `(p:num->num)(a - t - 1)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN
        ACCEPT_TAC(ARITH_RULE
         `a - SUC t = a - t - 1`);
        USE_THEN "plownext" (fun th -> REWRITE_TAC[th]) THEN
        ACCEPT_TAC(ARITH_RULE
         `(a + t + 1) + 2 = a + SUC t + 2`)];
      TRANS_TAC EQ_TRANS `(p:num->num)((a + t + 1) + 1)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN
        ACCEPT_TAC(ARITH_RULE
         `a + SUC t + 1 = (a + t + 1) + 1`);
        USE_THEN "phighnext" (fun th -> REWRITE_TAC[th]) THEN
        ACCEPT_TAC(ARITH_RULE
         `(a - t) - 1 = a - SUC t`)];
      X_GEN_TAC `s:num` THEN DISCH_THEN(LABEL_TAC "sle") THEN
      USE_THEN "finalrange" (MP_TAC o SPEC `s:num`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `s <= 2 * SUC t + 1 ==> s <= (2 * t + 2) + 1`) THEN
        USE_THEN "sle" ACCEPT_TAC;
        INTRO_TAC "slow shigh"] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `a - t - 1 <= x ==> a - SUC t <= x`) THEN
        USE_THEN "slow" ACCEPT_TAC;
        MATCH_MP_TAC(ARITH_RULE
         `x <= (a + t + 1) + 1 ==> x <= a + SUC t + 1`) THEN
        USE_THEN "shigh" ACCEPT_TAC];
      X_GEN_TAC `x:num` THEN
      INTRO_TAC "xlow xhigh" THEN
      USE_THEN "finalfull" (MP_TAC o SPEC `x:num`) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE
           `a - SUC t <= x ==> a - t - 1 <= x`) THEN
          USE_THEN "xlow" ACCEPT_TAC;
          MATCH_MP_TAC(ARITH_RULE
           `x <= a + SUC t + 1 ==> x <= (a + t + 1) + 1`) THEN
          USE_THEN "xhigh" ACCEPT_TAC];
        INTRO_TAC "@s. sle qs"] THEN
      EXISTS_TAC `s:num` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE
         `s <= (2 * t + 2) + 1 ==> s <= 2 * SUC t + 1`) THEN
        USE_THEN "sle" ACCEPT_TAC;
        USE_THEN "qs" ACCEPT_TAC]]]);;

let FINITE_PATH_ZIGZAG_LEFT_TERMINAL = prove
 (`!p q m a.
        (!i. i <= 2 * m ==> p i <= 2 * m) /\
        (!i. i < 2 * m ==> q i < 2 * m) /\
        (!i j. i < j /\ j < 2 * m ==> ~(q i = q j)) /\
        (!i j. i + 1 < j /\ j < 2 * m
               ==> ~adjacent_interval_cover p (q i) (q j)) /\
        (!r. 0 < r /\ r + 1 < 2 * m
             ==> ~adjacent_interval_cover p (q r) (q 0)) /\
        (!r. r < 2 * m
             ==> adjacent_interval_cover p (q r) (q(r + 1))) /\
        0 < m /\
        q 0 = a /\
        q(2 * m) = q 0 /\
        p(a + 1) <= a /\
        a + 1 <= p a /\
        q 1 < a
        ==> a = m /\
            q(2 * m - 1) = 0 /\
            p 1 = 2 * m /\
            (!r. r < m
                 ==> adjacent_interval_cover p
                      (q(2 * m - 1)) (q(2 * r)))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("pbound bound distinct chordless nobase path positive base " ^
    "closed lower upper left") THEN
  MP_TAC(ISPECL
   [`p:num->num`; `q:num->num`; `2 * (m:num)`; `a:num`]
   FINITE_PATH_ZIGZAG_LEFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `0 < m ==> 1 < 2 * m`) THEN
    USE_THEN "positive" ACCEPT_TAC;
    DISCH_THEN(LABEL_TAC "zigzag")] THEN
  USE_THEN "zigzag" (MP_TAC o SPEC `m - 1`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `0 < m ==> 2 * (m - 1) + 1 < 2 * m`) THEN
    USE_THEN "positive" ACCEPT_TAC;
    INTRO_TAC "leftbound qeven qodd plow phigh range full"] THEN
  SUBGOAL_THEN
   `(q:num->num)(2 * (m - 1)) < 2 * m`
  (LABEL_TAC "qevenbound") THENL
   [USE_THEN "bound" MATCH_MP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE
     `0 < m ==> 2 * (m - 1) < 2 * m`) THEN
    USE_THEN "positive" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) + (m - 1) < 2 * m`
  (LABEL_TAC "abound") THENL
   [USE_THEN "qevenbound" MP_TAC THEN
    USE_THEN "qeven" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) = m` (LABEL_TAC "center") THENL
   [MATCH_MP_TAC(ARITH_RULE
     `m - 1 < a /\ a + (m - 1) < 2 * m ==> a = m`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:num->num)(2 * m - 1) = 0`
  (LABEL_TAC "terminal") THENL
   [SUBGOAL_THEN `2 * m - 1 = 2 * (m - 1) + 1`
    (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC(ARITH_RULE
       `0 < m ==> 2 * m - 1 = 2 * (m - 1) + 1`) THEN
      USE_THEN "positive" ACCEPT_TAC;
      USE_THEN "qodd" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "center" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC(ARITH_RULE
       `0 < m ==> m - (m - 1) - 1 = 0`) THEN
      USE_THEN "positive" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) 1 = 2 * m`
  (LABEL_TAC "pone") THENL
   [SUBGOAL_THEN
     `(p:num->num) 1 = p(a - (m - 1))`
    (LABEL_TAC "parg") THENL
     [AP_TERM_TAC THEN
      USE_THEN "center" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC(ARITH_RULE `0 < m ==> 1 = m - (m - 1)`) THEN
      USE_THEN "positive" ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:num) + m - 1 + 1 = 2 * m`
    (LABEL_TAC "prhs") THENL
     [USE_THEN "center" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC(ARITH_RULE
       `0 < m ==> m + m - 1 + 1 = 2 * m`) THEN
      USE_THEN "positive" ACCEPT_TAC;
      USE_THEN "parg" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "plow" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "prhs" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 * m - 1) + 1 = 2 * m`
  (LABEL_TAC "lastindex") THENL
   [USE_THEN "positive" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `adjacent_interval_cover (p:num->num) 0 m`
  (LABEL_TAC "lastedge") THENL
   [SUBGOAL_THEN
     `adjacent_interval_cover (p:num->num)
        (q(2 * m - 1)) (q((2 * m - 1) + 1))`
    (LABEL_TAC "rawedge") THENL
     [USE_THEN "path" MATCH_MP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `0 < m ==> 2 * m - 1 < 2 * m`) THEN
      USE_THEN "positive" ACCEPT_TAC;
      USE_THEN "rawedge" (fun th ->
       USE_THEN "lastindex" (fun ith ->
        USE_THEN "terminal" (fun qth ->
         USE_THEN "closed" (fun cth ->
          USE_THEN "base" (fun bth ->
           USE_THEN "center" (fun ath ->
            ACCEPT_TAC
             (REWRITE_RULE[ith; qth; cth; bth; ath] th)))))))];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) 0 <= m`
  (LABEL_TAC "pzero") THENL
   [USE_THEN "lastedge" MP_TAC THEN
    REWRITE_TAC[adjacent_interval_cover; ADD_CLAUSES] THEN
    USE_THEN "pone" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(LABEL_TAC "orientation") THEN
    USE_THEN "positive" MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "center" ACCEPT_TAC;
    USE_THEN "terminal" ACCEPT_TAC;
    USE_THEN "pone" ACCEPT_TAC;
    X_GEN_TAC `r:num` THEN DISCH_THEN(LABEL_TAC "rlt") THEN
    USE_THEN "zigzag" (MP_TAC o SPEC `r:num`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `r < m ==> 2 * r + 1 < 2 * m`) THEN
      USE_THEN "rlt" ACCEPT_TAC;
      INTRO_TAC "_ qreven _ _ _ _ _"] THEN
    USE_THEN "terminal" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "qreven" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "center" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[adjacent_interval_cover; ADD_CLAUSES] THEN
    DISJ1_TAC THEN
    CONJ_TAC THENL
     [USE_THEN "pzero" MP_TAC THEN ARITH_TAC;
      USE_THEN "pone" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "rlt" MP_TAC THEN ARITH_TAC]]);;

let FINITE_PATH_ZIGZAG_RIGHT_TERMINAL = prove
 (`!p q m a.
        (!i. i <= 2 * m ==> p i <= 2 * m) /\
        (!i. i < 2 * m ==> q i < 2 * m) /\
        (!i j. i < j /\ j < 2 * m ==> ~(q i = q j)) /\
        (!i j. i + 1 < j /\ j < 2 * m
               ==> ~adjacent_interval_cover p (q i) (q j)) /\
        (!r. 0 < r /\ r + 1 < 2 * m
             ==> ~adjacent_interval_cover p (q r) (q 0)) /\
        (!r. r < 2 * m
             ==> adjacent_interval_cover p (q r) (q(r + 1))) /\
        0 < m /\
        q 0 = a /\
        q(2 * m) = q 0 /\
        p(a + 1) <= a /\
        a + 1 <= p a /\
        a < q 1
        ==> a = m - 1 /\
            q(2 * m - 1) = 2 * m - 1 /\
            p(2 * m - 1) = 0 /\
            (!r. r < m
                 ==> adjacent_interval_cover p
                      (q(2 * m - 1)) (q(2 * r)))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("pbound bound distinct chordless nobase path positive base " ^
    "closed lower upper right") THEN
  MP_TAC(ISPECL
   [`p:num->num`; `q:num->num`; `2 * (m:num)`; `a:num`]
   FINITE_PATH_ZIGZAG_RIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `0 < m ==> 1 < 2 * m`) THEN
    USE_THEN "positive" ACCEPT_TAC;
    DISCH_THEN(LABEL_TAC "zigzag")] THEN
  USE_THEN "zigzag" (MP_TAC o SPEC `m - 1`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE
     `0 < m ==> 2 * (m - 1) + 1 < 2 * m`) THEN
    USE_THEN "positive" ACCEPT_TAC;
    INTRO_TAC "leftbound qeven qodd plow phigh range full"] THEN
  SUBGOAL_THEN
   `(q:num->num)(2 * (m - 1) + 1) < 2 * m`
  (LABEL_TAC "qoddbound") THENL
   [USE_THEN "bound" MATCH_MP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE
     `0 < m ==> 2 * (m - 1) + 1 < 2 * m`) THEN
    USE_THEN "positive" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) + (m - 1) + 1 < 2 * m`
  (LABEL_TAC "abound") THENL
   [USE_THEN "qoddbound" MP_TAC THEN
    USE_THEN "qodd" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) = m - 1` (LABEL_TAC "center") THENL
   [MATCH_MP_TAC(ARITH_RULE
     `m - 1 <= a /\ a + (m - 1) + 1 < 2 * m
      ==> a = m - 1`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(q:num->num)(2 * m - 1) = 2 * m - 1`
  (LABEL_TAC "terminal") THENL
   [SUBGOAL_THEN
     `(q:num->num)(2 * m - 1) =
      q(2 * (m - 1) + 1)`
    (LABEL_TAC "qarg") THENL
     [AP_TERM_TAC THEN
      MATCH_MP_TAC(ARITH_RULE
       `0 < m ==> 2 * m - 1 = 2 * (m - 1) + 1`) THEN
      USE_THEN "positive" ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:num) + (m - 1) + 1 = 2 * m - 1`
    (LABEL_TAC "qrhs") THENL
     [USE_THEN "center" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "positive" MP_TAC THEN ARITH_TAC;
      USE_THEN "qarg" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "qodd" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "qrhs" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num)(2 * m - 1) = 0`
  (LABEL_TAC "pterminal") THENL
   [SUBGOAL_THEN
    `(p:num->num)(2 * m - 1) =
      p(a + (m - 1) + 1)`
    (LABEL_TAC "parg") THENL
     [AP_TERM_TAC THEN
      MAP_EVERY (fun s -> USE_THEN s MP_TAC) ["center"; "positive"] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:num) - (m - 1) = 0`
    (LABEL_TAC "prhs") THENL
     [USE_THEN "center" MP_TAC THEN ARITH_TAC;
      USE_THEN "parg" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "phigh" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "prhs" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 * m - 1) + 1 = 2 * m`
  (LABEL_TAC "lastindex") THENL
   [USE_THEN "positive" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `adjacent_interval_cover (p:num->num) (2 * m - 1) (m - 1)`
  (LABEL_TAC "lastedge") THENL
   [SUBGOAL_THEN
     `adjacent_interval_cover (p:num->num)
        (q(2 * m - 1)) (q((2 * m - 1) + 1))`
    (LABEL_TAC "rawedge") THENL
     [USE_THEN "path" MATCH_MP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `0 < m ==> 2 * m - 1 < 2 * m`) THEN
      USE_THEN "positive" ACCEPT_TAC;
      USE_THEN "rawedge" (fun th ->
       USE_THEN "lastindex" (fun ith ->
        USE_THEN "terminal" (fun qth ->
         USE_THEN "closed" (fun cth ->
          USE_THEN "base" (fun bth ->
           USE_THEN "center" (fun ath ->
            ACCEPT_TAC
             (REWRITE_RULE[ith; qth; cth; bth; ath] th)))))))];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:num) <= p(2 * m)`
  (LABEL_TAC "ptop") THENL
   [USE_THEN "lastedge" MP_TAC THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    USE_THEN "lastindex" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "pterminal" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(LABEL_TAC "orientation") THEN
    USE_THEN "positive" MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "center" ACCEPT_TAC;
    USE_THEN "terminal" ACCEPT_TAC;
    USE_THEN "pterminal" ACCEPT_TAC;
    X_GEN_TAC `r:num` THEN DISCH_THEN(LABEL_TAC "rlt") THEN
    USE_THEN "zigzag" (MP_TAC o SPEC `r:num`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `r < m ==> 2 * r + 1 < 2 * m`) THEN
      USE_THEN "rlt" ACCEPT_TAC;
      INTRO_TAC "_ qreven _ _ _ _ _"] THEN
    USE_THEN "terminal" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "qreven" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "center" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[adjacent_interval_cover] THEN
    USE_THEN "lastindex" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "pterminal" (fun th -> REWRITE_TAC[th]) THEN
    DISJ1_TAC THEN CONJ_TAC THENL
     [ARITH_TAC;
      USE_THEN "ptop" MP_TAC THEN
      USE_THEN "positive" MP_TAC THEN ARITH_TAC]]);;

let PATH_TERMINAL_TAIL_CYCLE = prove
 (`!v e (q:num->A) k r.
        0 < k /\
        r < k /\
        (!i. i < k ==> v(q i)) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j)) /\
        e (q(k - 1)) (q r) /\
        (!i. i < k ==> e (q i) (q(i + 1)))
        ==> ?u.
              (!i. i <= k - r ==> v(u i)) /\
              u 0 = u(k - r) /\
              (!i. 0 < i /\ i < k - r ==> ~(u i = u 0)) /\
              (!i. i < k - r ==> e (u i) (u(i + 1)))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "positive rlt bound distinct terminal path" THEN
  EXISTS_TAC
   `\i. if i = 0 then (q:num->A)(k - 1)
        else q(r + i - 1)` THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_THEN(LABEL_TAC "ile") THEN
    BETA_TAC THEN COND_CASES_TAC THENL
     [USE_THEN "bound" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "bound" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    BETA_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((k:num) - r = 0)` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:num` THEN
    INTRO_TAC "ipos ilt" THEN
    SUBGOAL_THEN `~((i:num) = 0)` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      BETA_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "distinct" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:num` THEN DISCH_THEN(LABEL_TAC "ilt") THEN
    BETA_TAC THEN ASM_CASES_TAC `(i:num) = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(1 = 0)`;
                      ARITH_RULE `r + 1 - 1 = r`] THEN
      USE_THEN "terminal" ACCEPT_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `~(i + 1 = 0)`] THEN
      SUBGOAL_THEN
       `r + (i + 1) - 1 = (r + i - 1) + 1`
      SUBST1_TAC THENL
       [ASM_ARITH_TAC;
        USE_THEN "path" MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

let FINITE_PATH_TERMINAL_EVEN_CYCLES = prove
 (`!v e (q:num->A) m.
        0 < m /\
        (!i. i < 2 * m ==> v(q i)) /\
        (!i j. i < j /\ j < 2 * m ==> ~(q i = q j)) /\
        (!i. i < 2 * m ==> e (q i) (q(i + 1))) /\
        (!r. r < m ==> e (q(2 * m - 1)) (q(2 * r)))
        ==> !s. 0 < s /\ s <= m
                ==> ?u.
                      (!i. i <= 2 * s ==> v(u i)) /\
                      u 0 = u(2 * s) /\
                      (!i. 0 < i /\ i < 2 * s
                           ==> ~(u i = u 0)) /\
                      (!i. i < 2 * s ==> e (u i) (u(i + 1)))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "positive bound distinct path terminal" THEN
  X_GEN_TAC `s:num` THEN
  INTRO_TAC "spos sle" THEN
  MP_TAC(BETA_RULE(ISPECL
   [`v:A->bool`; `e:A->A->bool`; `q:num->A`; `2 * (m:num)`;
    `2 * (m - s)`]
   PATH_TERMINAL_TAIL_CYCLE)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `0 < m ==> 0 < 2 * m`) THEN
      USE_THEN "positive" ACCEPT_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `0 < s /\ s <= m ==> 2 * (m - s) < 2 * m`) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "bound" ACCEPT_TAC;
      USE_THEN "distinct" ACCEPT_TAC;
      USE_THEN "terminal" MATCH_MP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE
       `0 < s /\ s <= m ==> m - s < m`) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "path" ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_THEN `u:num->A` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `2 * m - 2 * (m - s) = 2 * s`
  (LABEL_TAC "length") THENL
   [MATCH_MP_TAC(ARITH_RULE
     `s <= m ==> 2 * m - 2 * (m - s) = 2 * s`) THEN
    USE_THEN "sle" ACCEPT_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `u:num->A` THEN
  USE_THEN "length" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ASM_REWRITE_TAC[]);;

let FINITE_INJECTIVE_INDEX_BOUND = prove
 (`!q (k:num) (n:num).
        (!i. i < k ==> q i < n) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j))
        ==> k <= n`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "bound distinct" THEN
  SUBGOAL_THEN
   `CARD(IMAGE (q:num->num) {i | i < k}) = k`
  (LABEL_TAC "imagecard") THENL
   [TRANS_TAC EQ_TRANS `CARD {i:num | i < k}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
        INTRO_TAC "ibound jbound same" THEN
        ASM_CASES_TAC `(i:num) = j` THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `(i:num) < j` THENL
         [USE_THEN "distinct" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
          ASM_MESON_TAC[];
          SUBGOAL_THEN `(j:num) < i` (LABEL_TAC "ji") THENL
           [ASM_ARITH_TAC;
            USE_THEN "distinct" (MP_TAC o SPECL [`j:num`; `i:num`]) THEN
            ASM_MESON_TAC[]]];
        REWRITE_TAC[FINITE_NUMSEG_LT]];
      REWRITE_TAC[CARD_NUMSEG_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (q:num->num) {i | i < k} SUBSET {j | j < n}`
  (LABEL_TAC "subset") THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    USE_THEN "bound" ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (q:num->num) {i | i < k}`; `{j:num | j < n}`]
   CARD_SUBSET) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT]);;

let FINITE_SIMPLE_CYCLE_LENGTH = prove
 (`!q (k:num) (n:num).
        0 < k /\
        (!i. i < k ==> q i + 1 < n) /\
        (!i j. i < j /\ j < k ==> ~(q i = q j))
        ==> k < n`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "positive bound distinct" THEN
  MP_TAC(ISPECL
   [`q:num->num`; `k:num`; `n - 1`]
   FINITE_INJECTIVE_INDEX_BOUND) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
      ASM_ARITH_TAC;
      USE_THEN "distinct" ACCEPT_TAC];
    ASM_ARITH_TAC]);;

let FINITE_ODD_CYCLIC_SHORTEST_CYCLE = prove
 (`!p n.
        ODD n /\
        2 < n /\
        (!i. i < n ==> p i < n /\ minimal_period p n i)
        ==> ?k q.
              1 < k /\
              k < n /\
              (!r. r <= k ==> q r + 1 < n) /\
              q 0 = q k /\
              p(q 0 + 1) <= q 0 /\
              q 0 + 1 <= p(q 0) /\
              adjacent_interval_cover p (q 0) (q 0) /\
              (!r s. r < s /\ s < k ==> ~(q r = q s)) /\
              (!r s. r + 1 < s /\ s < k
                     ==> ~adjacent_interval_cover p (q r) (q s)) /\
              (!r. 0 < r /\ r + 1 < k
                   ==> ~adjacent_interval_cover p (q r) (q 0)) /\
              (!r. r < k
                   ==> adjacent_interval_cover p (q r) (q(SUC r)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:num->num`; `n:num`]
   FINITE_ODD_CYCLIC_RETURN_CYCLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `l:num`
     (X_CHOOSE_THEN `u:num->num` STRIP_ASSUME_TAC))] THEN
  ABBREV_TAC `a = (u:num->num) 0` THEN
  SUBGOAL_THEN
   `(p:num->num)(a + 1) <= a /\
    a + 1 <= p a /\
    adjacent_interval_cover p a a`
  (LABEL_TAC "originalbase") THENL
   [ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\i:num. i + 1 < n`;
    `adjacent_interval_cover (p:num->num)`;
    `\i:num. i = a`]
   PATH_SHORTEST_SIMPLE_CYCLE)) THEN
  ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`l:num`; `u:num->num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `k:num`
     (X_CHOOSE_THEN `q:num->num` STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `(k:num) < n` (LABEL_TAC "short") THENL
   [MATCH_MP_TAC(ISPECL
     [`q:num->num`; `k:num`; `n:num`]
     FINITE_SIMPLE_CYCLE_LENGTH) THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:num->num) k = a` (LABEL_TAC "basevalue") THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `q:num->num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Compact level sets and interval covering.                                 *)
(* ------------------------------------------------------------------------- *)

let REAL_COMPACT_LEVELSET = prove
 (`!f s y.
        real_compact s /\ f real_continuous_on s
        ==> real_compact {x | x IN s /\ f x = y}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_BOUNDED_SUBSET THEN
    EXISTS_TAC `s:real->bool` THEN
    ASM_SIMP_TAC[REAL_COMPACT_IMP_BOUNDED] THEN SET_TAC[];
    REWRITE_TAC[REAL_CLOSED] THEN
    SUBGOAL_THEN
     `IMAGE lift {x | x IN s /\ (f:real->real) x = y} =
      {x | x IN IMAGE lift s /\ (lift o f o drop) x = lift y}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; o_THM] THEN
      MESON_TAC[LIFT_DROP];
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN
        ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON];
        REWRITE_TAC[GSYM REAL_CLOSED] THEN
        MATCH_MP_TAC REAL_COMPACT_IMP_CLOSED THEN ASM_REWRITE_TAC[]]]]);;

let REAL_INTERVAL_ENDPOINTS_COVER = prove
 (`!f a b c d.
        a <= b /\
        c <= d /\
        f real_continuous_on real_interval[a,b] /\
        ((f a <= c /\ d <= f b) \/ (f b <= c /\ d <= f a))
        ==> real_interval[c,d] SUBSET IMAGE f (real_interval[a,b])`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "ab cd continuous ends" THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real` THEN
  REWRITE_TAC[IN_REAL_INTERVAL; IN_IMAGE] THEN DISCH_TAC THEN
  USE_THEN "ends" DISJ_CASES_TAC THENL
   [MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `y:real`]
      REAL_IVT_INCREASING) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC];
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `y:real`]
      REAL_IVT_DECREASING) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC]] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  ASM_REWRITE_TAC[]);;

let REAL_INTERVAL_ADJACENT_INTERSECTION = prove
 (`!z n i j x.
        (!r s. r < s /\ s < n ==> z r < z s) /\
        i + 1 < n /\
        j + 1 < n /\
        ~(i = j) /\
        x IN real_interval[z i,z(i + 1)] /\
        x IN real_interval[z j,z(j + 1)]
        ==> (i + 1 = j /\ x = z j) \/
            (j + 1 = i /\ x = z i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  INTRO_TAC "ordered ibound jbound distinct left right" THEN
  ASM_CASES_TAC `(i:num) < j` THENL
   [DISJ1_TAC THEN ASM_CASES_TAC `(i:num) + 1 = j` THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(i:num) + 1 = j`]) THEN
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(z:num->real) (i + 1) < z j` ASSUME_TAC THENL
       [USE_THEN "ordered" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    DISJ2_TAC THEN
    SUBGOAL_THEN `(j:num) < i` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `(j:num) + 1 = i` THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(j:num) + 1 = i`]) THEN
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(z:num->real) (j + 1) < z i` ASSUME_TAC THENL
       [USE_THEN "ordered" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        ASM_REAL_ARITH_TAC]]]);;

let REAL_INTERVAL_ORDERED_COVER = prove
 (`!f z p n i j.
        f real_continuous_on (:real) /\
        (!r s. r < s /\ s < n ==> z r < z s) /\
        i + 1 < n /\
        j + 1 < n /\
        p i < n /\
        p(i + 1) < n /\
        f(z i) = z(p i) /\
        f(z(i + 1)) = z(p(i + 1)) /\
        adjacent_interval_cover p i j
        ==> real_interval[z j,z(j + 1)]
            SUBSET IMAGE f (real_interval[z i,z(i + 1)])`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("continuous ordered ibound jbound pibound psibound " ^
    "fi fsi straddles") THEN
  SUBGOAL_THEN
   `!r s. r <= s /\ s < n ==> (z:num->real) r <= z s`
  (LABEL_TAC "monotone") THENL
   [MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(r:num) = s` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "ordered" (MATCH_MP_TAC o SPECL [`r:num`; `s:num`]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTERVAL_ENDPOINTS_COVER THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "monotone"
     (MATCH_MP_TAC o SPECL [`i:num`; `i + 1`]) THEN
    ASM_ARITH_TAC;
    USE_THEN "monotone"
     (MATCH_MP_TAC o SPECL [`j:num`; `j + 1`]) THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    USE_THEN "straddles"
     (DISJ_CASES_TAC o REWRITE_RULE[adjacent_interval_cover]) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "monotone"
         (MATCH_MP_TAC o SPECL [`(p:num->num) i`; `j:num`]) THEN
        ASM_ARITH_TAC;
        USE_THEN "monotone"
         (MATCH_MP_TAC o
          SPECL [`j + 1`; `(p:num->num) (i + 1)`]) THEN
        ASM_ARITH_TAC];
      DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "monotone"
         (MATCH_MP_TAC o
          SPECL [`(p:num->num) (i + 1)`; `j:num`]) THEN
        ASM_ARITH_TAC;
        USE_THEN "monotone"
         (MATCH_MP_TAC o SPECL [`j + 1`; `(p:num->num) i`]) THEN
        ASM_ARITH_TAC]]]);;

let REAL_INTERVAL_CYCLIC_SELFCOVER = prove
 (`!f z p n.
        f real_continuous_on (:real) /\
        1 < n /\
        (!i j. i < j /\ j < n ==> z i < z j) /\
        (!i. i < n
             ==> p i < n /\
                 minimal_period p n i /\
                 f(z i) = z(p i))
        ==> ?i.
              i + 1 < n /\
              real_interval[z i,z(i + 1)]
              SUBSET IMAGE f (real_interval[z i,z(i + 1)])`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous nontrivial ordered cycle" THEN
  MP_TAC(ISPECL [`p:num->num`; `n:num`] FINITE_CYCLIC_CROSSING) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "nontrivial" ACCEPT_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "cycle" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN(fun th ->
          ACCEPT_TAC(CONJ (CONJUNCT1 th)
            (CONJUNCT1(CONJUNCT2 th))))]];
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `(p:num->num) i < n /\
    minimal_period p n i /\
    (f:real->real)((z:num->real) i) = z(p i)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cycle" (MATCH_MP_TAC o SPEC `i:num`) THEN
    MP_TAC(ASSUME `(i:num) + 1 < n`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:num->num) (i + 1) < n /\
    minimal_period p n (i + 1) /\
    (f:real->real)((z:num->real) (i + 1)) = z(p(i + 1))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cycle" (MATCH_MP_TAC o SPEC `i + 1`) THEN
    ACCEPT_TAC(ASSUME `(i:num) + 1 < n`);
    ALL_TAC] THEN
  EXISTS_TAC `i:num` THEN CONJ_TAC THENL
   [ACCEPT_TAC(ASSUME `(i:num) + 1 < n`);
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `z:num->real`; `p:num->num`;
     `n:num`; `i:num`; `i:num`]
     REAL_INTERVAL_ORDERED_COVER) THEN
    ASM_REWRITE_TAC[adjacent_interval_cover]]);;

let REAL_INTERVAL_ENDPOINTS_SUBINTERVAL = prove
 (`!f x y c d.
        x < y /\
        c < d /\
        f real_continuous_on real_interval[x,y] /\
        f x = c /\
        f y = d
        ==> ?u v.
              x <= u /\ u <= v /\ v <= y /\
              IMAGE f (real_interval[u,v]) = real_interval[c,d]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `real_compact
      {z | z IN real_interval[x,y] /\ (f:real->real) z = c}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_LEVELSET THEN
    ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(SPEC
   `{z | z IN real_interval[x,y] /\ (f:real->real) z = c}`
   REAL_COMPACT_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `x:real` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  INTRO_TAC "@u. ulevel umax" THEN
  SUBGOAL_THEN
   `(f:real->real) real_continuous_on real_interval[u,y]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[x,y]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM; IN_REAL_INTERVAL]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_compact
      {z | z IN real_interval[u,y] /\ (f:real->real) z = d}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_LEVELSET THEN
    ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(SPEC
   `{z | z IN real_interval[u,y] /\ (f:real->real) z = d}`
   REAL_COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `y:real` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM; IN_REAL_INTERVAL]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  INTRO_TAC "@v. vlevel vmin" THEN
  MAP_EVERY EXISTS_TAC [`u:real`; `v:real`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM; IN_REAL_INTERVAL]) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN real_interval[u,v]
        ==> c <= (f:real->real) z /\ f z <= d`
  (LABEL_TAC "bounds") THENL
   [X_GEN_TAC `z:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_CASES_TAC `c <= (f:real->real) z` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`f:real->real`; `z:real`; `v:real`; `c:real`]
        REAL_IVT_INCREASING) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `real_interval[u,y]` THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `(x <= w /\ w <= y) /\ (f:real->real) w = c`
      (LABEL_TAC "wlower") THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "umax" (fun th ->
        USE_THEN "wlower"
         (MP_TAC o MATCH_MP (SPEC `w:real` th))) THEN
      DISCH_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
      SUBGOAL_THEN `z:real = u` SUBST_ALL_TAC THEN
      ASM_REAL_ARITH_TAC;
      ASM_CASES_TAC `(f:real->real) z <= d` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`f:real->real`; `u:real`; `z:real`; `d:real`]
        REAL_IVT_INCREASING) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `real_interval[u,y]` THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `(u <= w /\ w <= y) /\ (f:real->real) w = d`
      (LABEL_TAC "wupper") THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "vmin" (fun th ->
        USE_THEN "wupper"
         (MP_TAC o MATCH_MP (SPEC `w:real` th))) THEN
      DISCH_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
      SUBGOAL_THEN `z:real = v` SUBST_ALL_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `z:real` THEN STRIP_TAC THEN
    USE_THEN "bounds" (MATCH_MP_TAC o SPEC `z:real`) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    MATCH_MP_TAC IS_REALINTERVAL_CONTAINS_INTERVAL THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IS_REALINTERVAL_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[u,y]` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `u:real` THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `v:real` THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]]);;

let REAL_INTERVAL_COVER_SUBINTERVAL = prove
 (`!f a b c d.
        a <= b /\
        c <= d /\
        f real_continuous_on real_interval[a,b] /\
        real_interval[c,d] SUBSET IMAGE f (real_interval[a,b])
        ==> ?u v.
              u <= v /\
              real_interval[u,v] SUBSET real_interval[a,b] /\
              IMAGE f (real_interval[u,v]) = real_interval[c,d]`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "ab cd continuous cover" THEN
  ASM_CASES_TAC `c:real = d` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "cover" (MP_TAC o REWRITE_RULE[SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_IMAGE]] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`x:real`; `x:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_INTERVAL_SING;
                    IMAGE_CLAUSES; SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `c < d` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c IN IMAGE (f:real->real) (real_interval[a,b]) /\
    d IN IMAGE f (real_interval[a,b])`
  MP_TAC THENL
   [CONJ_TAC THEN USE_THEN "cover"
      (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_IMAGE]] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(x:real = y)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x < y` THENL
   [MP_TAC(ISPECL [`f:real->real`; `x:real`; `y:real`;
                   `c:real`; `d:real`]
      REAL_INTERVAL_ENDPOINTS_SUBINTERVAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real`
     (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `v:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `y < x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z:real. --((f:real->real) z)`; `y:real`; `x:real`;
    `--d:real`; `--c:real`]
   REAL_INTERVAL_ENDPOINTS_SUBINTERVAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_NEG2] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  INTRO_TAC "@u v. uv uy vy negimage" THEN
  MAP_EVERY EXISTS_TAC [`u:real`; `v:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\z:real. --z) (real_interval[--d,--c]) =
    real_interval[c,d]`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `z:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN EXISTS_TAC `--(z:real)` THEN
      REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "negimage"
   (MP_TAC o AP_TERM `IMAGE (\z:real. --z)`) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; REAL_NEG_NEG; IMAGE_ID;
                  ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Fixed points obtained from interval covering.                             *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_ON_FIXPOINT = prove
 (`!f s.
        is_realinterval s /\
        f real_continuous_on s /\
        (?x. x IN s /\ f x <= x) /\
        (?y. y IN s /\ y <= f y)
        ==> ?x. x IN s /\ f x = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `is_realinterval (IMAGE (\z. (f:real->real) z - z) s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IS_REALINTERVAL_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 IN real_interval[(f:real->real) x - x,f y - y]`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (\z. (f:real->real) z - z) s`;
    `(f:real->real) x - x`;
    `(f:real->real) y - y`]
   IS_REALINTERVAL_CONTAINS_INTERVAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `&0` (REWRITE_RULE[SUBSET] th))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:real` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let REAL_INTERVAL_COVER_FIXPOINT = prove
 (`!f a b.
        a <= b /\
        f real_continuous_on real_interval[a,b] /\
        real_interval[a,b] SUBSET IMAGE f (real_interval[a,b])
        ==> ?x. x IN real_interval[a,b] /\ f x = x`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "endpoints continuous cover" THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_FIXPOINT THEN
  ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN
  CONJ_TAC THENL
   [USE_THEN "cover" (MP_TAC o REWRITE_RULE[SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_REAL_ARITH_TAC;
    USE_THEN "cover" (MP_TAC o REWRITE_RULE[SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Finite chains of interval coverings.                                      *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_ON_ITER = prove
 (`!f n s.
        f real_continuous_on (:real)
        ==> ITER n f real_continuous_on s`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[ITER_POINTLESS; I_DEF; REAL_CONTINUOUS_ON_ID];
    POP_ASSUM(LABEL_TAC "IH") THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[ITER_ALT_POINTLESS] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      USE_THEN "IH" (MATCH_MP_TAC o SPEC `IMAGE (f:real->real) s`) THEN
      ASM_REWRITE_TAC[]]]);;

let REAL_INTERVAL_COVER_CHAIN = prove
 (`!f n a b.
        f real_continuous_on (:real) /\
        (!i. i <= n ==> a i <= b i) /\
        (!i. i < n
             ==> real_interval[a(SUC i),b(SUC i)]
                 SUBSET IMAGE f (real_interval[a i,b i]))
        ==> ?u v.
              u <= v /\
              real_interval[u,v] SUBSET real_interval[a 0,b 0] /\
              IMAGE (ITER n f) (real_interval[u,v]) =
              real_interval[a n,b n] /\
              !i. i <= n
                  ==> IMAGE (ITER i f) (real_interval[u,v])
                      SUBSET real_interval[a i,b i]`,
  GEN_TAC THEN INDUCT_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:num->real`; `b:num->real`] THEN
    INTRO_TAC "continuous endpoints covers" THEN
    MAP_EVERY EXISTS_TAC [`(a:num->real) 0`; `(b:num->real) 0`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "endpoints" (MATCH_MP_TAC o SPEC `0`) THEN ARITH_TAC;
      REWRITE_TAC[SUBSET_REFL];
      REWRITE_TAC[ITER_POINTLESS; I_DEF; IMAGE_ID];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL
       [ASM_ARITH_TAC;
        REWRITE_TAC[ITER_POINTLESS; I_DEF; IMAGE_ID; SUBSET_REFL]]];
    POP_ASSUM(LABEL_TAC "IH") THEN
    MAP_EVERY X_GEN_TAC [`a:num->real`; `b:num->real`] THEN
    INTRO_TAC "continuous endpoints covers"] THEN
  USE_THEN "IH" (MP_TAC o SPECL
   [`\i. (a:num->real) (SUC i)`; `\i. (b:num->real) (SUC i)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "endpoints" (MATCH_MP_TAC o SPEC `SUC i`) THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "covers" (MATCH_MP_TAC o SPEC `SUC i`) THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o BETA_RULE) THEN
  INTRO_TAC "@u v. uv tailinitial tail_exact tail_itinerary" THEN
  MP_TAC(ISPECL [`f:real->real`; `(a:num->real) 0`; `(b:num->real) 0`;
                 `u:real`; `v:real`]
    REAL_INTERVAL_COVER_SUBINTERVAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "endpoints" (MATCH_MP_TAC o SPEC `0`) THEN ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `real_interval[(a:num->real) 1,(b:num->real) 1]` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[ONE];
        USE_THEN "covers" (MP_TAC o SPEC `0`) THEN
        DISCH_THEN(fun th ->
          MP_TAC(MATCH_MP th (ARITH_RULE `0 < SUC n`))) THEN
        SIMP_TAC[ONE]]];
    ALL_TAC] THEN
  INTRO_TAC "@p q. pq firstinitial first_exact" THEN
  MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ITER_ALT_POINTLESS; IMAGE_o] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = 0` THENL
     [ASM_REWRITE_TAC[ITER_POINTLESS; I_DEF; IMAGE_ID];
      MP_TAC(SPEC `i:num` num_CASES) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN
      REWRITE_TAC[ITER_ALT_POINTLESS; IMAGE_o] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "tail_itinerary" (MATCH_MP_TAC o SPEC `j:num`) THEN
      ASM_ARITH_TAC]]);;

let REAL_INTERVAL_COVER_CYCLE = prove
 (`!f n a b.
        f real_continuous_on (:real) /\
        (!i. i <= n ==> a i <= b i) /\
        (!i. i < n
             ==> real_interval[a(SUC i),b(SUC i)]
                 SUBSET IMAGE f (real_interval[a i,b i])) /\
        a n = a 0 /\
        b n = b 0
        ==> ?x.
              x IN real_interval[a 0,b 0] /\
              ITER n f x = x /\
              !i. i <= n ==> ITER i f x IN real_interval[a i,b i]`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous endpoints covers closeda closedb" THEN
  MP_TAC(ISPECL [`f:real->real`; `n:num`;
                 `a:num->real`; `b:num->real`]
    REAL_INTERVAL_COVER_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  INTRO_TAC "@u v. uv initial exact itinerary" THEN
  SUBGOAL_THEN
   `real_interval[u,v] SUBSET
    IMAGE (ITER n (f:real->real)) (real_interval[u,v])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval[(a:num->real) 0,(b:num->real) 0]` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "exact" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ITER n (f:real->real)`; `u:real`; `v:real`]
    REAL_INTERVAL_COVER_FIXPOINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_ITER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "initial" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `IMAGE (ITER i (f:real->real)) (real_interval[u,v])
      SUBSET real_interval[(a:num->real) i,(b:num->real) i]`
    ASSUME_TAC THENL
     [USE_THEN "itinerary" (MATCH_MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real` THEN
    ASM_REWRITE_TAC[]]);;

let REAL_INTERVAL_COVER_CYCLE_MINIMAL_PERIOD_GEN = prove
 (`!f n a b.
        f real_continuous_on (:real) /\
        0 < n /\
        (!i. i <= n ==> a i <= b i) /\
        (!i. i < n
             ==> real_interval[a(SUC i),b(SUC i)]
                 SUBSET IMAGE f (real_interval[a i,b i])) /\
        a n = a 0 /\
        b n = b 0 /\
        (!i x.
             0 < i /\ i < n /\
             x IN real_interval[a 0,b 0] /\
             x IN real_interval[a i,b i]
             ==> ~(ITER i f x = x))
        ==> ?x.
              minimal_period f n x /\
              !i. i <= n ==> ITER i f x IN real_interval[a i,b i]`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   "continuous positive endpoints covers closeda closedb separated" THEN
  MP_TAC(ISPECL [`f:real->real`; `n:num`;
                 `a:num->real`; `b:num->real`]
    REAL_INTERVAL_COVER_CYCLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  INTRO_TAC "@x. initial periodn itinerary" THEN
  MP_TAC(ISPECL [`f:real->real`; `x:real`; `n:num`]
    PERIODIC_POINT_IMP_MINIMAL_PERIOD) THEN
  ASM_REWRITE_TAC[periodic_point] THEN
  INTRO_TAC "@d. divides minimal" THEN
  SUBGOAL_THEN `(d:num) <= (n:num)` ASSUME_TAC THENL
   [USE_THEN "divides" (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:num) = (n:num)` SUBST_ALL_TAC THENL
   [ASM_CASES_TAC `(d:num) = (n:num)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `0 < (d:num)` ASSUME_TAC THENL
     [USE_THEN "minimal" (MP_TAC o MATCH_MP MINIMAL_PERIOD_POS) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "minimal"
     (MP_TAC o REWRITE_RULE[periodic_point] o
      MATCH_MP MINIMAL_PERIOD_PERIODIC) THEN
    DISCH_THEN(LABEL_TAC "periodd") THEN
    SUBGOAL_THEN
     `ITER d (f:real->real) x IN real_interval[(a:num->real) d,b d]`
    (LABEL_TAC "visit") THENL
     [USE_THEN "itinerary" (MATCH_MP_TAC o SPEC `d:num`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `x IN real_interval[(a:num->real) d,b d]`
    (LABEL_TAC "return") THENL
     [USE_THEN "periodd" (fun th ->
        USE_THEN "visit" (ACCEPT_TAC o REWRITE_RULE[th]));
      ALL_TAC] THEN
    SUBGOAL_THEN
     `0 < (d:num) /\ d < n /\
      x IN real_interval[(a:num->real) 0,b 0] /\
      x IN real_interval[a d,b d]`
    (LABEL_TAC "earlyconditions") THENL
     [REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        ASM_ARITH_TAC;
        USE_THEN "initial" ACCEPT_TAC;
        USE_THEN "return" ACCEPT_TAC];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[]);;

let REAL_INTERVAL_ORDERED_FIRST_RETURN_CYCLE = prove
 (`!f z p n k q.
        f real_continuous_on (:real) /\
        (!i j. i < j /\ j < n ==> z i < z j) /\
        (!i. i < n ==> p i < n /\ f(z i) = z(p i)) /\
        (!i. i < n ==> minimal_period f n (z i)) /\
        0 < k /\
        k < n /\
        (!r. r <= k ==> q r + 1 < n) /\
        q 0 = q k /\
        (!r. 0 < r /\ r < k ==> ~(q r = q 0)) /\
        (!r. r < k
             ==> adjacent_interval_cover p (q r) (q(SUC r)))
        ==> ?x. minimal_period f k x`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("continuous ordered transition oldminimal positive short " ^
    "bound closed first covers") THEN
  MP_TAC(BETA_RULE(ISPECL
   [`f:real->real`; `k:num`;
    `\i:num. (z:num->real)((q:num->num) i)`;
    `\i:num. (z:num->real)((q:num->num) i + 1)`]
   REAL_INTERVAL_COVER_CYCLE_MINIMAL_PERIOD_GEN)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      USE_THEN "positive" ACCEPT_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "ordered" MATCH_MP_TAC THEN CONJ_TAC THENL
       [ARITH_TAC;
        USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
        ASM_ARITH_TAC];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `((p:num->num) ((q:num->num) (i:num)) < n /\
         (f:real->real)(z(q i)) = z(p(q i))) /\
        (p(q i + 1) < n /\ f(z(q i + 1)) = z(p(q i + 1)))`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "transition" MATCH_MP_TAC THEN
          USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
          ASM_ARITH_TAC;
          USE_THEN "transition" MATCH_MP_TAC THEN
          USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
          ASM_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC(ISPECL
       [`f:real->real`; `z:num->real`; `p:num->num`; `n:num`;
        `(q:num->num) i`; `(q:num->num)(SUC i)`]
       REAL_INTERVAL_ORDERED_COVER) THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "continuous" ACCEPT_TAC;
        USE_THEN "ordered" ACCEPT_TAC;
        USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
        ASM_ARITH_TAC;
        USE_THEN "bound" (MP_TAC o SPEC `SUC i`) THEN
        ASM_ARITH_TAC;
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        USE_THEN "covers" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "closed" (fun th -> REWRITE_TAC[th]);
      USE_THEN "closed" (fun th -> REWRITE_TAC[th]);
      MAP_EVERY X_GEN_TAC [`i:num`; `x:real`] THEN
      INTRO_TAC "ipos ik left right" THEN
      SUBGOAL_THEN
       `?h. h < n /\ x = (z:num->real) h`
      (DESTRUCT_TAC "@h. hbound endpoint") THENL
       [MP_TAC(ISPECL
         [`z:num->real`; `n:num`; `(q:num->num) 0`;
          `(q:num->num) i`; `x:real`]
         REAL_INTERVAL_ADJACENT_INTERSECTION) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [USE_THEN "ordered" ACCEPT_TAC;
            USE_THEN "bound" (MP_TAC o SPEC `0`) THEN ASM_ARITH_TAC;
            USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
            ASM_ARITH_TAC;
            DISCH_THEN(LABEL_TAC "same") THEN ASM_MESON_TAC[];
            USE_THEN "left" ACCEPT_TAC;
            USE_THEN "right" ACCEPT_TAC];
          DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
           [EXISTS_TAC `(q:num->num) i` THEN CONJ_TAC THENL
             [USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
              ASM_ARITH_TAC;
              ACCEPT_TAC
               (ASSUME `x = (z:num->real)((q:num->num) i)`)];
            EXISTS_TAC `(q:num->num) 0` THEN CONJ_TAC THENL
             [USE_THEN "bound" (MP_TAC o SPEC `0`) THEN
              ASM_ARITH_TAC;
              ACCEPT_TAC
               (ASSUME `x = (z:num->real)((q:num->num) 0)`)]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `minimal_period (f:real->real) n x`
      (LABEL_TAC "oldperiod") THENL
       [USE_THEN "endpoint" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "oldminimal" MATCH_MP_TAC THEN
        USE_THEN "hbound" ACCEPT_TAC;
        ALL_TAC] THEN
      DISCH_THEN(LABEL_TAC "earlyreturn") THEN
      MP_TAC(ISPECL [`f:real->real`; `n:num`; `x:real`; `i:num`]
       MINIMAL_PERIOD_DIVIDES) THEN
      ASM_REWRITE_TAC[periodic_point] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_ARITH_TAC];
    INTRO_TAC "@x. minimal itinerary" THEN
    EXISTS_TAC `x:real` THEN USE_THEN "minimal" ACCEPT_TAC]);;

let REAL_INTERVAL_ORDERED_FIRST_RETURN_CYCLE_NONMULTIPLE = prove
 (`!f z p n k q.
        f real_continuous_on (:real) /\
        (!i j. i < j /\ j < n ==> z i < z j) /\
        (!i. i < n ==> p i < n /\ f(z i) = z(p i)) /\
        (!i. i < n ==> minimal_period f n (z i)) /\
        0 < k /\
        ~(n divides k) /\
        (!r. r <= k ==> q r + 1 < n) /\
        q 0 = q k /\
        (!r. 0 < r /\ r < k ==> ~(q r = q 0)) /\
        (!r. r < k
             ==> adjacent_interval_cover p (q r) (q(SUC r)))
        ==> ?x. minimal_period f k x`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("continuous ordered transition oldminimal positive " ^
    "nonmultiple bound closed first covers") THEN
  MP_TAC(BETA_RULE(ISPECL
   [`f:real->real`; `k:num`;
    `\i:num. (z:num->real)((q:num->num) i)`;
    `\i:num. (z:num->real)((q:num->num) i + 1)`]
   REAL_INTERVAL_COVER_CYCLE)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "ordered" MATCH_MP_TAC THEN CONJ_TAC THENL
       [ARITH_TAC;
        USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
        ASM_ARITH_TAC];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `((p:num->num) ((q:num->num) (i:num)) < n /\
         (f:real->real)(z(q i)) = z(p(q i))) /\
        (p(q i + 1) < n /\ f(z(q i + 1)) = z(p(q i + 1)))`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "transition" MATCH_MP_TAC THEN
          USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
          ASM_ARITH_TAC;
          USE_THEN "transition" MATCH_MP_TAC THEN
          USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
          ASM_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC(ISPECL
       [`f:real->real`; `z:num->real`; `p:num->num`; `n:num`;
        `(q:num->num) i`; `(q:num->num)(SUC i)`]
       REAL_INTERVAL_ORDERED_COVER) THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "continuous" ACCEPT_TAC;
        USE_THEN "ordered" ACCEPT_TAC;
        USE_THEN "bound" (MP_TAC o SPEC `i:num`) THEN
        ASM_ARITH_TAC;
        USE_THEN "bound" (MP_TAC o SPEC `SUC i`) THEN
        ASM_ARITH_TAC;
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        USE_THEN "covers" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "closed" (fun th -> REWRITE_TAC[th]);
      USE_THEN "closed" (fun th -> REWRITE_TAC[th])];
    INTRO_TAC "@x. initial periodk itinerary"] THEN
  MP_TAC(ISPECL [`f:real->real`; `x:real`; `k:num`]
   PERIODIC_POINT_IMP_MINIMAL_PERIOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[periodic_point];
    INTRO_TAC "@d. divides minimal"] THEN
  SUBGOAL_THEN `(d:num) <= k` ASSUME_TAC THENL
   [USE_THEN "divides" (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:num) = k` SUBST_ALL_TAC THENL
   [ASM_CASES_TAC `(d:num) = k` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `0 < (d:num) /\ d < k`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "minimal" (MP_TAC o MATCH_MP MINIMAL_PERIOD_POS) THEN
        ARITH_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `ITER d (f:real->real) x = x`
    (LABEL_TAC "periodd") THENL
     [USE_THEN "minimal"
       (ACCEPT_TAC o REWRITE_RULE[periodic_point] o
        MATCH_MP MINIMAL_PERIOD_PERIODIC);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ITER d (f:real->real) x IN
      real_interval[(z:num->real)((q:num->num) d),z(q d + 1)]`
    (LABEL_TAC "visit") THENL
     [USE_THEN "itinerary" (MATCH_MP_TAC o SPEC `d:num`) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `x IN
      real_interval[(z:num->real)((q:num->num) d),z(q d + 1)]`
    (LABEL_TAC "return") THENL
     [USE_THEN "periodd" (fun th ->
       USE_THEN "visit" (ACCEPT_TAC o REWRITE_RULE[th]));
      ALL_TAC] THEN
    SUBGOAL_THEN `?h. h < n /\ x = (z:num->real) h`
    (DESTRUCT_TAC "@h. hbound endpoint") THENL
     [MP_TAC(ISPECL
       [`z:num->real`; `n:num`; `(q:num->num) 0`;
        `(q:num->num) d`; `x:real`]
       REAL_INTERVAL_ADJACENT_INTERSECTION) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "ordered" ACCEPT_TAC;
          USE_THEN "bound" (MP_TAC o SPEC `0`) THEN ASM_ARITH_TAC;
          USE_THEN "bound" (MP_TAC o SPEC `d:num`) THEN
          ASM_ARITH_TAC;
          DISCH_THEN(LABEL_TAC "same") THEN ASM_MESON_TAC[];
          ASM_REWRITE_TAC[ADD_CLAUSES];
          ASM_REWRITE_TAC[ADD_CLAUSES]];
        DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
         [EXISTS_TAC `(q:num->num) d` THEN CONJ_TAC THENL
           [USE_THEN "bound" (MP_TAC o SPEC `d:num`) THEN
            ASM_ARITH_TAC;
            ASM_REWRITE_TAC[]];
          EXISTS_TAC `(q:num->num) 0` THEN CONJ_TAC THENL
           [USE_THEN "bound" (MP_TAC o SPEC `0`) THEN
            ASM_ARITH_TAC;
            ASM_REWRITE_TAC[]]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `minimal_period (f:real->real) n x`
    (LABEL_TAC "oldperiod") THENL
     [USE_THEN "endpoint" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "oldminimal" MATCH_MP_TAC THEN
      USE_THEN "hbound" ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(d:num) = n` (LABEL_TAC "deqn") THENL
     [MATCH_MP_TAC(ISPECL
       [`f:real->real`; `d:num`; `n:num`; `x:real`]
       MINIMAL_PERIOD_UNIQUE) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `x:real` THEN
  USE_THEN "minimal" ACCEPT_TAC);;

let REAL_INTERVAL_ORDERED_SIMPLE_CYCLE = prove
 (`!f z p n k q.
        f real_continuous_on (:real) /\
        (!i j. i < j /\ j < n ==> z i < z j) /\
        (!i. i < n ==> p i < n /\ f(z i) = z(p i)) /\
        (!i. i < n ==> minimal_period f n (z i)) /\
        0 < k /\
        k < n /\
        (!r. r <= k ==> q r + 1 < n) /\
        q 0 = q k /\
        (!r s. r < s /\ s < k ==> ~(q r = q s)) /\
        (!r. r < k
             ==> adjacent_interval_cover p (q r) (q(SUC r)))
        ==> ?x. minimal_period f k x`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("continuous ordered transition oldminimal positive short " ^
    "bound closed distinct covers") THEN
  MATCH_MP_TAC(ISPECL
   [`f:real->real`; `z:num->real`; `p:num->num`; `n:num`;
    `k:num`; `q:num->num`]
   REAL_INTERVAL_ORDERED_FIRST_RETURN_CYCLE) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "continuous" ACCEPT_TAC;
    USE_THEN "ordered" ACCEPT_TAC;
    USE_THEN "transition" ACCEPT_TAC;
    USE_THEN "oldminimal" ACCEPT_TAC;
    USE_THEN "positive" ACCEPT_TAC;
    USE_THEN "short" ACCEPT_TAC;
    USE_THEN "bound" ACCEPT_TAC;
    USE_THEN "closed" ACCEPT_TAC;
    X_GEN_TAC `i:num` THEN
    INTRO_TAC "ipos ik" THEN
    DISCH_THEN(LABEL_TAC "same") THEN
    USE_THEN "distinct" (MP_TAC o SPECL [`0`; `i:num`]) THEN
    ASM_MESON_TAC[];
    USE_THEN "covers" ACCEPT_TAC]);;

let REAL_INTERVAL_COVER_CYCLE_MINIMAL_PERIOD = prove
 (`!f n a b.
        f real_continuous_on (:real) /\
        0 < n /\
        (!i. i <= n ==> a i <= b i) /\
        (!i. i < n
             ==> real_interval[a(SUC i),b(SUC i)]
                 SUBSET IMAGE f (real_interval[a i,b i])) /\
        a n = a 0 /\
        b n = b 0 /\
        (!i. 0 < i /\ i < n
             ==> DISJOINT (real_interval[a 0,b 0])
                          (real_interval[a i,b i]))
        ==> ?x.
              minimal_period f n x /\
              !i. i <= n ==> ITER i f x IN real_interval[a i,b i]`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("continuous positive endpoints covers closedleft closedright " ^
    "separated") THEN
  MATCH_MP_TAC REAL_INTERVAL_COVER_CYCLE_MINIMAL_PERIOD_GEN THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `x:real`] THEN
  INTRO_TAC "ipos ilt left right" THEN
  SUBGOAL_THEN
   `DISJOINT (real_interval[(a:num->real) 0,b 0])
             (real_interval[a i,b i])`
  (LABEL_TAC "apart") THENL
   [USE_THEN "separated" (MATCH_MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "apart" (MP_TAC o MATCH_MP
   (SET_RULE
    `DISJOINT (s:real->bool) t
     ==> ~((x:real) IN s /\ x IN t)`)) THEN
  ASM_REWRITE_TAC[]);;

let ODD_PERIOD_ORDERED_SIMPLE_CYCLE = prove
 (`!f n.
        ODD n /\
        2 < n /\
        has_period f n
        ==> ?z p k q.
              (!i j. i < j /\ j < n ==> z i < z j) /\
              (!i. i < n ==> p i < n /\ f(z i) = z(p i)) /\
              (!i. i < n ==> minimal_period f n (z i)) /\
              (!i. i < n
                   ==> p i < n /\ minimal_period p n i) /\
              1 < k /\
              k < n /\
              (!r. r <= k ==> q r + 1 < n) /\
              q 0 = q k /\
              p(q 0 + 1) <= q 0 /\
              q 0 + 1 <= p(q 0) /\
              adjacent_interval_cover p (q 0) (q 0) /\
              (!r s. r < s /\ s < k ==> ~(q r = q s)) /\
              (!r s. r + 1 < s /\ s < k
                     ==> ~adjacent_interval_cover p (q r) (q s)) /\
              (!r. 0 < r /\ r + 1 < k
                   ==> ~adjacent_interval_cover p (q r) (q 0)) /\
              (!r. r < k
                   ==> adjacent_interval_cover p (q r) (q(SUC r)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_period] THEN
  INTRO_TAC "odd nontrivial @x. minimal" THEN
  MP_TAC(MATCH_MP
   (ISPECL [`f:real->real`; `n:num`; `x:real`]
    MINIMAL_PERIOD_ORDERED_ORBIT)
   (ASSUME `minimal_period (f:real->real) n x`)) THEN
  INTRO_TAC "@z. ordered enum" THEN
  MP_TAC(ISPECL
   [`f:real->real`; `n:num`; `x:real`; `z:num->real`]
   MINIMAL_PERIOD_ORDERED_ORBIT_TRANSITION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    INTRO_TAC "@p. transition"] THEN
  SUBGOAL_THEN
   `!i. i < n ==> minimal_period (p:num->num) n i`
  (LABEL_TAC "pminimal") THENL
   [MATCH_MP_TAC(ISPECL
     [`f:real->real`; `n:num`; `x:real`; `z:num->real`;
      `p:num->num`]
     MINIMAL_PERIOD_ORDERED_ORBIT_TRANSITION_MINIMAL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> (p:num->num) i < n /\ minimal_period p n i`
  (LABEL_TAC "cycle") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "transition" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "pminimal" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> minimal_period (f:real->real) n ((z:num->real) i)`
  (LABEL_TAC "oldminimal") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `n:num`; `x:real`; `(z:num->real) i`]
     MINIMAL_PERIOD_ORBIT_MINIMAL) THEN
    CONJ_TAC THENL
     [USE_THEN "minimal" ACCEPT_TAC;
      USE_THEN "enum" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num->num`; `n:num`]
   FINITE_ODD_CYCLIC_SHORTEST_CYCLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    INTRO_TAC
     ("@k q. length short pathbound closed lower upper self " ^
      "distinct chordless nobase path")] THEN
  MAP_EVERY EXISTS_TAC
   [`z:num->real`; `p:num->num`; `k:num`; `q:num->num`] THEN
  ASM_REWRITE_TAC[]);;

let ODD_PERIOD_IMP_LARGER_NONMULTIPLE_PERIOD = prove
 (`!f n m.
        f real_continuous_on (:real) /\
        ODD n /\
        2 < n /\
        has_period f n /\
        n < m /\
        ~(n divides m)
        ==> has_period f m`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous odd nontrivial period larger nonmultiple" THEN
  MP_TAC(ISPECL [`f:real->real`; `n:num`]
   ODD_PERIOD_ORDERED_SIMPLE_CYCLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    INTRO_TAC
     ("@z p k q. ordered transition oldminimal pcycle length short " ^
      "pathbound closed lower upper self distinct chordless nobase path")] THEN
  SUBGOAL_THEN `(k:num) < m` (LABEL_TAC "klt") THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\i:num. i + 1 < n`;
    `adjacent_interval_cover (p:num->num)`;
    `k:num`; `q:num->num`; `m - k:num`]
   PATH_SIMPLE_CYCLE_WAITS)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(k:num) + (m - k) = m`
  (LABEL_TAC "target") THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "target" (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MP_TAC(ISPECL
   [`f:real->real`; `z:num->real`; `p:num->num`; `n:num`;
    `m:num`; `r:num->num`]
   REAL_INTERVAL_ORDERED_FIRST_RETURN_CYCLE_NONMULTIPLE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_ARITH_TAC;
      USE_THEN "nonmultiple" ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    INTRO_TAC "@x. minimal"] THEN
  REWRITE_TAC[has_period] THEN
  EXISTS_TAC `x:real` THEN
  USE_THEN "minimal" ACCEPT_TAC);;

let ODD_PERIOD_IMP_LARGER_PERIOD = prove
 (`!f n m.
        f real_continuous_on (:real) /\
        ODD n /\
        2 < n /\
        has_period f n /\
        n < m
        ==> has_period f m`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous odd nontrivial period larger" THEN
  ASM_CASES_TAC `(n:num) divides m` THENL
   [ALL_TAC;
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `n:num`; `m:num`]
     ODD_PERIOD_IMP_LARGER_NONMULTIPLE_PERIOD) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `2 * (n:num) <= m`
  (LABEL_TAC "double") THENL
   [MP_TAC(ISPECL [`m:num`; `n:num`] DIVIDES_CASES) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `EVEN m` THENL
   [SUBGOAL_THEN `ODD(m - 1)` (LABEL_TAC "nearodd") THENL
     [ASM_REWRITE_TAC[ODD_SUB; GSYM NOT_EVEN; ODD] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((n:num) divides (m - 1))`
    (LABEL_TAC "oldnonmultiple") THENL
     [MATCH_MP_TAC(ISPECL [`n:num`; `m:num`; `1`]
       DIVIDES_NOT_SUB) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((m - 1) divides (m:num))`
    (LABEL_TAC "newnonmultiple") THENL
     [MATCH_MP_TAC(ISPECL [`m:num`; `1`] SUB_NOT_DIVIDES) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `has_period (f:real->real) (m - 1)`
    (LABEL_TAC "nearperiod") THENL
     [MATCH_MP_TAC(ISPECL
       [`f:real->real`; `n:num`; `m - 1:num`]
       ODD_PERIOD_IMP_LARGER_NONMULTIPLE_PERIOD) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `m - 1:num`; `m:num`]
     ODD_PERIOD_IMP_LARGER_NONMULTIPLE_PERIOD) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `ODD m` (LABEL_TAC "modd") THENL
     [ASM_REWRITE_TAC[GSYM NOT_EVEN];
      ALL_TAC] THEN
    SUBGOAL_THEN `ODD(m - 2)` (LABEL_TAC "nearodd") THENL
     [ASM_REWRITE_TAC[ODD_SUB; ODD] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((n:num) divides (m - 2))`
    (LABEL_TAC "oldnonmultiple") THENL
     [MATCH_MP_TAC(ISPECL [`n:num`; `m:num`; `2`]
       DIVIDES_NOT_SUB) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((m - 2) divides (m:num))`
    (LABEL_TAC "newnonmultiple") THENL
     [MATCH_MP_TAC(ISPECL [`m:num`; `2`] SUB_NOT_DIVIDES) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `has_period (f:real->real) (m - 2)`
    (LABEL_TAC "nearperiod") THENL
     [MATCH_MP_TAC(ISPECL
       [`f:real->real`; `n:num`; `m - 2:num`]
       ODD_PERIOD_IMP_LARGER_NONMULTIPLE_PERIOD) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `m - 2:num`; `m:num`]
     ODD_PERIOD_IMP_LARGER_NONMULTIPLE_PERIOD) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let LEAST_ODD_PERIOD_ORDERED_CYCLE = prove
 (`!f n.
        f real_continuous_on (:real) /\
        ODD n /\
        2 < n /\
        has_period f n /\
        (!m. ODD m /\ 1 < m /\ m < n ==> ~has_period f m)
        ==> ?z p q.
              (!i j. i < j /\ j < n ==> z i < z j) /\
              (!i. i < n ==> p i < n /\ f(z i) = z(p i)) /\
              (!i. i < n ==> minimal_period f n (z i)) /\
              (!i. i < n
                   ==> p i < n /\ minimal_period p n i) /\
              (!r. r <= n - 1 ==> q r + 1 < n) /\
              q 0 = q(n - 1) /\
              p(q 0 + 1) <= q 0 /\
              q 0 + 1 <= p(q 0) /\
              adjacent_interval_cover p (q 0) (q 0) /\
              (!r s. r < s /\ s < n - 1 ==> ~(q r = q s)) /\
              (!r s. r + 1 < s /\ s < n - 1
                     ==> ~adjacent_interval_cover p (q r) (q s)) /\
              (!r. 0 < r /\ r + 1 < n - 1
                   ==> ~adjacent_interval_cover p (q r) (q 0)) /\
              (!r. r < n - 1
                   ==> adjacent_interval_cover p (q r) (q(SUC r)))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous odd nontrivial period least" THEN
  MP_TAC(ISPECL [`f:real->real`; `n:num`]
   ODD_PERIOD_ORDERED_SIMPLE_CYCLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    INTRO_TAC
     ("@z p k q. ordered transition oldminimal pcycle length short " ^
      "pathbound closed lower upper self distinct chordless nobase path")] THEN
  MP_TAC(ISPECL
   [`f:real->real`; `z:num->real`; `p:num->num`; `n:num`;
    `k:num`; `q:num->num`]
   REAL_INTERVAL_ORDERED_SIMPLE_CYCLE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    INTRO_TAC "@y. kminimal"] THEN
  SUBGOAL_THEN `has_period (f:real->real) k`
  (LABEL_TAC "kperiod") THENL
   [REWRITE_TAC[has_period] THEN EXISTS_TAC `y:real` THEN
    USE_THEN "kminimal" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:num) = n - 1` (LABEL_TAC "klength") THENL
   [ASM_CASES_TAC `ODD k` THENL
     [USE_THEN "least" (MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN(fun nth ->
         USE_THEN "kperiod" (fun pth ->
          CONTR_TAC(MP (NOT_ELIM nth) pth)))];
      ALL_TAC] THEN
    ASM_CASES_TAC `(k:num) + 1 = n` THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(k:num) + 1 < n`
    (LABEL_TAC "waitshort") THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`\i:num. i + 1 < n`;
      `adjacent_interval_cover (p:num->num)`;
      `k:num`; `q:num->num`]
     PATH_SIMPLE_CYCLE_WAIT)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL
     [`f:real->real`; `z:num->real`; `p:num->num`; `n:num`;
      `(k:num) + 1`; `r:num->num`]
     REAL_INTERVAL_ORDERED_FIRST_RETURN_CYCLE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "continuous" ACCEPT_TAC;
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ARITH_TAC;
        USE_THEN "waitshort" ACCEPT_TAC;
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      INTRO_TAC "@w. waitminimal"] THEN
    SUBGOAL_THEN `has_period (f:real->real) (k + 1)`
    (LABEL_TAC "waitperiod") THENL
     [REWRITE_TAC[has_period] THEN EXISTS_TAC `w:real` THEN
      USE_THEN "waitminimal" ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "least" (MP_TAC o SPEC `(k:num) + 1`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[ODD_ADD; ARITH];
        ASM_ARITH_TAC;
        USE_THEN "waitshort" ACCEPT_TAC];
      DISCH_THEN(fun nth ->
       USE_THEN "waitperiod" (fun pth ->
        CONTR_TAC(MP (NOT_ELIM nth) pth)))];
    ALL_TAC] THEN
  USE_THEN "klength" (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MAP_EVERY EXISTS_TAC
   [`z:num->real`; `p:num->num`; `q:num->num`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Periods one, two and four.                                                *)
(* ------------------------------------------------------------------------- *)

let HAS_PERIOD_ORDERED_CYCLE = prove
 (`!f n.
        has_period (f:real->real) n
        ==> ?z p.
              (!i j. i < j /\ j < n ==> z i < z j) /\
              (!i. i < n ==> p i < n /\ f(z i) = z(p i)) /\
              (!i. i < n ==> minimal_period f n (z i)) /\
              (!i. i < n ==> p i < n /\ minimal_period p n i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_period] THEN
  INTRO_TAC "@x. minimal" THEN
  MP_TAC(ISPECL [`f:real->real`; `n:num`; `x:real`]
   MINIMAL_PERIOD_ORDERED_ORBIT) THEN
  ASM_REWRITE_TAC[] THEN
  INTRO_TAC "@z. ordered orbit" THEN
  MP_TAC(ISPECL
   [`f:real->real`; `n:num`; `x:real`; `z:num->real`]
   MINIMAL_PERIOD_ORDERED_ORBIT_TRANSITION) THEN
  ASM_REWRITE_TAC[] THEN
  INTRO_TAC "@p. transition" THEN
  MP_TAC(ISPECL
   [`f:real->real`; `n:num`; `x:real`; `z:num->real`;
    `p:num->num`]
   MINIMAL_PERIOD_ORDERED_ORBIT_TRANSITION_MINIMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pminimal") THEN
  MAP_EVERY EXISTS_TAC [`z:num->real`; `p:num->num`] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "ordered" ACCEPT_TAC;
    USE_THEN "transition" ACCEPT_TAC;
    X_GEN_TAC `i:num` THEN DISCH_THEN(LABEL_TAC "ibound") THEN
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `n:num`; `x:real`; `(z:num->real) i`]
     MINIMAL_PERIOD_ORBIT_MINIMAL) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "orbit" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_THEN(LABEL_TAC "ibound") THEN
    CONJ_TAC THENL
     [USE_THEN "transition" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL
       [USE_THEN "ibound" ACCEPT_TAC;
        SIMP_TAC[]];
      USE_THEN "pminimal" MATCH_MP_TAC THEN
      USE_THEN "ibound" ACCEPT_TAC]]);;

let FINITE_CYCLIC_4_TWO_CYCLE = prove
 (`!p.
        (!i. i < 4 ==> p i < 4 /\ minimal_period p 4 i)
        ==> (adjacent_interval_cover p 0 1 /\
             adjacent_interval_cover p 1 0) \/
            (adjacent_interval_cover p 0 2 /\
             adjacent_interval_cover p 2 0) \/
            (adjacent_interval_cover p 1 2 /\
             adjacent_interval_cover p 2 1)`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "cycle") THEN
  SUBGOAL_THEN
   `minimal_period (p:num->num) 4 0`
  (LABEL_TAC "minimal") THENL
   [USE_THEN "cycle" (MP_TAC o SPEC `0`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:num->num) (p (p (p 0))) = 0`
  (LABEL_TAC "closed") THENL
   [USE_THEN "minimal"
     (MP_TAC o MATCH_MP MINIMAL_PERIOD_PERIODIC) THEN
    REWRITE_TAC[periodic_point; num_CONV `4`; num_CONV `3`;
                num_CONV `2`; num_CONV `1`; ITER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((p:num->num) 0 = 0)`
  (LABEL_TAC "not1") THENL
   [DISCH_THEN(LABEL_TAC "early") THEN
    SUBGOAL_THEN `periodic_point (p:num->num) 1 0`
    (LABEL_TAC "earlyperiod") THENL
     [REWRITE_TAC[periodic_point; ITER_1] THEN
      USE_THEN "early" ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:num->num`; `4`; `0`; `1`]
     MINIMAL_PERIOD_DIVIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((p:num->num) (p 0) = 0)`
  (LABEL_TAC "not2") THENL
   [DISCH_THEN(LABEL_TAC "early") THEN
    SUBGOAL_THEN `periodic_point (p:num->num) 2 0`
    (LABEL_TAC "earlyperiod") THENL
     [REWRITE_TAC[periodic_point; num_CONV `2`; num_CONV `1`;
                  ITER] THEN
      USE_THEN "early" ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:num->num`; `4`; `0`; `2`]
     MINIMAL_PERIOD_DIVIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((p:num->num) (p (p 0)) = 0)`
  (LABEL_TAC "not3") THENL
   [DISCH_THEN(LABEL_TAC "early") THEN
    SUBGOAL_THEN `periodic_point (p:num->num) 3 0`
    (LABEL_TAC "earlyperiod") THENL
     [REWRITE_TAC[periodic_point; num_CONV `3`; num_CONV `2`;
                  num_CONV `1`; ITER] THEN
      USE_THEN "early" ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:num->num`; `4`; `0`; `3`]
     MINIMAL_PERIOD_DIVIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p 0 = 0 \/ p 0 = 1 \/ p 0 = 2 \/ p 0 = 3`
  (LABEL_TAC "p0cases") THENL
   [USE_THEN "cycle" (MP_TAC o SPEC `0`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p 1 = 0 \/ p 1 = 1 \/ p 1 = 2 \/ p 1 = 3`
  (LABEL_TAC "p1cases") THENL
   [USE_THEN "cycle" (MP_TAC o SPEC `1`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p 2 = 0 \/ p 2 = 1 \/ p 2 = 2 \/ p 2 = 3`
  (LABEL_TAC "p2cases") THENL
   [USE_THEN "cycle" (MP_TAC o SPEC `2`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p 3 = 0 \/ p 3 = 1 \/ p 3 = 2 \/ p 3 = 3`
  (LABEL_TAC "p3cases") THENL
   [USE_THEN "cycle" (MP_TAC o SPEC `3`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "p0cases"
   (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  USE_THEN "p1cases"
   (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  USE_THEN "p2cases"
   (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  USE_THEN "p3cases"
   (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  UNDISCH_TAC `~((p:num->num) (p (p 0)) = 0)` THEN
  UNDISCH_TAC `~((p:num->num) (p 0) = 0)` THEN
  UNDISCH_TAC `~((p:num->num) 0 = 0)` THEN
  UNDISCH_TAC `(p:num->num) (p (p (p 0))) = 0` THEN
  ASM_REWRITE_TAC[adjacent_interval_cover] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

let REAL_INTERVAL_ORDERED_TWO_CYCLE = prove
 (`!f z p n i j.
        f real_continuous_on (:real) /\
        (!r s. r < s /\ s < n ==> z r < z s) /\
        (!r. r < n ==> p r < n /\ f(z r) = z(p r)) /\
        (!r. r < n ==> minimal_period f n (z r)) /\
        i + 1 < n /\
        j + 1 < n /\
        ~(i = j) /\
        adjacent_interval_cover p i j /\
        adjacent_interval_cover p j i
        ==> ?x. minimal_period f 2 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL
   [`f:real->real`; `z:num->real`; `p:num->num`; `n:num`;
    `2`; `\r:num. if r = 1 then (j:num) else (i:num)`]
   REAL_INTERVAL_ORDERED_SIMPLE_CYCLE) THEN
  (REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ARITH_TAC;
    ASM_ARITH_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(r:num) = 1` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ARITH];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(r:num) = 0 /\ s = 1` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[ARITH]];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:num) = 0 \/ r = 1`
    DISJ_CASES_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[ARITH];
      ASM_REWRITE_TAC[ARITH]]]));;

let PERIOD_4_IMP_PERIOD_2 = prove
 (`!f. f real_continuous_on (:real) /\ has_period f 4
       ==> has_period f 2`,
  GEN_TAC THEN
  INTRO_TAC "continuous period" THEN
  MP_TAC(ISPECL [`f:real->real`; `4`] HAS_PERIOD_ORDERED_CYCLE) THEN
  ASM_REWRITE_TAC[] THEN
  INTRO_TAC "@z p. ordered transition oldminimal pcycle" THEN
  MP_TAC(ISPEC `p:num->num` FINITE_CYCLIC_4_TWO_CYCLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
   (DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[has_period] THENL
   [MATCH_MP_TAC(ISPECL
     [`f:real->real`; `z:num->real`; `p:num->num`; `4`; `0`; `1`]
     REAL_INTERVAL_ORDERED_TWO_CYCLE) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `z:num->real`; `p:num->num`; `4`; `0`; `2`]
     REAL_INTERVAL_ORDERED_TWO_CYCLE) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `z:num->real`; `p:num->num`; `4`; `1`; `2`]
     REAL_INTERVAL_ORDERED_TWO_CYCLE) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let FINITE_REAL_CYCLE_DESCENT = prove
 (`!x n.
        0 < n /\ x n = x 0
        ==> ?i. i < n /\ x(SUC i) <= x i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `?i:num. i < n /\ (x:num->real)(SUC i) <= x i` THENL
   [ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n ==> (x:num->real) i < x(SUC i)`
  (LABEL_TAC "increasing") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_MESON_TAC[REAL_NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 0 < k /\ k <= n ==> (x:num->real) 0 < x k`
  (LABEL_TAC "chain") THENL
   [INDUCT_TAC THENL
     [ARITH_TAC;
      INTRO_TAC "positive bound" THEN
      ASM_CASES_TAC `(k:num) = 0` THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "increasing" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_TRANS THEN
        EXISTS_TAC `(x:num->real) k` THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
          USE_THEN "increasing" MATCH_MP_TAC THEN ASM_ARITH_TAC]]];
    USE_THEN "chain" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LT_REFL]]]);;

let HAS_PERIOD_IMP_PERIOD_1 = prove
 (`!f n.
        f real_continuous_on (:real) /\ has_period f n
        ==> has_period f 1`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous period" THEN
  USE_THEN "period" (MP_TAC o REWRITE_RULE[has_period]) THEN
  INTRO_TAC "@x. minimal" THEN
  SUBGOAL_THEN
   `0 < (n:num) /\ periodic_point (f:real->real) n x`
  (DESTRUCT_TAC "positive orbit") THENL
   [ASM_MESON_TAC[MINIMAL_PERIOD_POS; MINIMAL_PERIOD_PERIODIC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i. i < n /\
        (f:real->real)(ITER i f x) <= ITER i f x`
  (LABEL_TAC "below") THENL
   [MP_TAC(ISPECL [`\i:num. ITER i (f:real->real) x`; `n:num`]
     FINITE_REAL_CYCLE_DESCENT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "positive" ACCEPT_TAC;
        USE_THEN "orbit" (fun th ->
         REWRITE_TAC[REWRITE_RULE[periodic_point] th; ITER])];
      REWRITE_TAC[ITER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i. i < n /\
        ITER i (f:real->real) x <= f(ITER i f x)`
  (LABEL_TAC "above") THENL
   [MP_TAC(ISPECL
     [`\i:num. --(ITER i (f:real->real) x)`; `n:num`]
     FINITE_REAL_CYCLE_DESCENT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "positive" ACCEPT_TAC;
        USE_THEN "orbit" (fun th ->
         REWRITE_TAC[REWRITE_RULE[periodic_point] th; ITER])];
      REWRITE_TAC[REAL_LE_NEG2; ITER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `(:real)`]
   REAL_CONTINUOUS_ON_FIXPOINT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_UNIV];
      USE_THEN "continuous" ACCEPT_TAC;
      ASM_MESON_TAC[IN_UNIV];
      ASM_MESON_TAC[IN_UNIV]];
    DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC)] THEN
  REWRITE_TAC[has_period] THEN EXISTS_TAC `z:real` THEN
  REWRITE_TAC[MINIMAL_PERIOD_DIVISIBILITY; ARITH] THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[DIVIDES_1] THEN
  REWRITE_TAC[periodic_point] THEN
  MATCH_MP_TAC ITER_FIXPOINT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Even periods forced by odd periods.                                       *)
(* ------------------------------------------------------------------------- *)

let LEAST_ODD_PERIOD_IMP_EVEN_PERIODS_INDEXED = prove
 (`!f m.
        f real_continuous_on (:real) /\
        0 < m /\
        has_period f (2 * m + 1) /\
        (!d. ODD d /\ 1 < d /\ d < 2 * m + 1
             ==> ~has_period f d)
        ==> !s. 0 < s /\ s <= m ==> has_period f (2 * s)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous positive period least" THEN
  MP_TAC(ISPECL [`f:real->real`; `2 * (m:num) + 1`]
   LEAST_ODD_PERIOD_ORDERED_CYCLE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      REWRITE_TAC[ODD_EXISTS] THEN
      EXISTS_TAC `m:num` THEN ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE `0 < m ==> 2 < 2 * m + 1`) THEN
      USE_THEN "positive" ACCEPT_TAC;
      USE_THEN "period" ACCEPT_TAC;
      USE_THEN "least" ACCEPT_TAC];
    INTRO_TAC
     ("@z p q. ordered transition oldminimal pcycle pathbound closed " ^
      "lower upper self distinct chordless nobase path")] THEN
  SUBGOAL_THEN `(2 * m + 1) - 1 = 2 * m`
  (LABEL_TAC "predecessor") THENL
   [ARITH_TAC;
    USE_THEN "predecessor" (fun th ->
     RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN
   `!i. i <= 2 * m ==> (p:num->num) i <= 2 * m`
  (LABEL_TAC "pbound") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "transition" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      SIMP_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < 2 * m ==> (q:num->num) i < 2 * m`
  (LABEL_TAC "qbound") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "pathbound" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((q:num->num) 0 = q 1)`
  (LABEL_TAC "firstdifferent") THENL
   [USE_THEN "distinct" (MATCH_MP_TAC o SPECL [`0`; `1`]) THEN
    USE_THEN "positive" MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r < m
        ==> adjacent_interval_cover (p:num->num)
             (q(2 * m - 1)) (q(2 * r))`
  (LABEL_TAC "terminalcovers") THENL
   [ASM_CASES_TAC `(q:num->num) 1 < q 0` THENL
     [MP_TAC(ISPECL
       [`p:num->num`; `q:num->num`; `m:num`; `(q:num->num) 0`]
       FINITE_PATH_ZIGZAG_LEFT_TERMINAL) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "pbound" ACCEPT_TAC;
          USE_THEN "qbound" ACCEPT_TAC;
          USE_THEN "distinct" ACCEPT_TAC;
          USE_THEN "chordless" ACCEPT_TAC;
          USE_THEN "nobase" ACCEPT_TAC;
          REWRITE_TAC[GSYM ADD1] THEN USE_THEN "path" ACCEPT_TAC;
          USE_THEN "positive" ACCEPT_TAC;
          REFL_TAC;
          USE_THEN "closed" (ACCEPT_TAC o SYM);
          USE_THEN "lower" ACCEPT_TAC;
          USE_THEN "upper" ACCEPT_TAC;
          ASM_REWRITE_TAC[]];
        INTRO_TAC "_ _ _ terminalcover" THEN
        USE_THEN "terminalcover" ACCEPT_TAC];
      SUBGOAL_THEN `(q:num->num) 0 < q 1`
      (LABEL_TAC "right") THENL
       [USE_THEN "firstdifferent" MP_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`p:num->num`; `q:num->num`; `m:num`; `(q:num->num) 0`]
       FINITE_PATH_ZIGZAG_RIGHT_TERMINAL) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "pbound" ACCEPT_TAC;
          USE_THEN "qbound" ACCEPT_TAC;
          USE_THEN "distinct" ACCEPT_TAC;
          USE_THEN "chordless" ACCEPT_TAC;
          USE_THEN "nobase" ACCEPT_TAC;
          REWRITE_TAC[GSYM ADD1] THEN USE_THEN "path" ACCEPT_TAC;
          USE_THEN "positive" ACCEPT_TAC;
          REFL_TAC;
          USE_THEN "closed" (ACCEPT_TAC o SYM);
          USE_THEN "lower" ACCEPT_TAC;
          USE_THEN "upper" ACCEPT_TAC;
          USE_THEN "right" ACCEPT_TAC];
        INTRO_TAC "_ _ _ terminalcover" THEN
        USE_THEN "terminalcover" ACCEPT_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `s:num` THEN
  INTRO_TAC "spos sle" THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\i:num. i + 1 < 2 * m + 1`;
    `adjacent_interval_cover (p:num->num)`;
   `q:num->num`; `m:num`]
   FINITE_PATH_TERMINAL_EVEN_CYCLES)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "positive" ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_THEN(LABEL_TAC "ilt") THEN
      USE_THEN "pathbound" (fun bth ->
       USE_THEN "ilt" (fun ith ->
        ACCEPT_TAC(MATCH_MP (SPEC `i:num` bth)
         (MATCH_MP
          (ARITH_RULE `i < 2 * m ==> i <= 2 * m`) ith))));
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "distinct" ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM ADD1] THEN USE_THEN "path" ACCEPT_TAC;
      USE_THEN "terminalcovers" ACCEPT_TAC];
    DISCH_THEN(MP_TAC o SPEC `s:num`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:num->num` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL
   [`f:real->real`; `z:num->real`; `p:num->num`;
    `2 * m + 1`; `2 * s`; `u:num->num`]
   REAL_INTERVAL_ORDERED_FIRST_RETURN_CYCLE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      USE_THEN "ordered" ACCEPT_TAC;
      USE_THEN "transition" ACCEPT_TAC;
      USE_THEN "oldminimal" ACCEPT_TAC;
      MATCH_MP_TAC(ARITH_RULE `0 < s ==> 0 < 2 * s`) THEN
      USE_THEN "spos" ACCEPT_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `s <= m ==> 2 * s < 2 * m + 1`) THEN
      USE_THEN "sle" ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ADD1] THEN ASM_REWRITE_TAC[]];
    INTRO_TAC "@x. minimal"] THEN
  REWRITE_TAC[has_period] THEN
  EXISTS_TAC `x:real` THEN USE_THEN "minimal" ACCEPT_TAC);;

let LEAST_ODD_PERIOD_IMP_EVEN_PERIODS = prove
 (`!f n.
        f real_continuous_on (:real) /\
        ODD n /\
        2 < n /\
        has_period f n /\
        (!d. ODD d /\ 1 < d /\ d < n ==> ~has_period f d)
        ==> !s. 0 < s /\ 2 * s < n ==> has_period f (2 * s)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous odd nontrivial period least" THEN
  USE_THEN "odd" (MP_TAC o REWRITE_RULE[ODD_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  MP_TAC(ISPECL [`f:real->real`; `m:num`]
   LEAST_ODD_PERIOD_IMP_EVEN_PERIODS_INDEXED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      MATCH_MP_TAC(ARITH_RULE `2 < SUC(2 * m) ==> 0 < m`) THEN
      USE_THEN "nontrivial" ACCEPT_TAC;
      REWRITE_TAC[GSYM ADD1] THEN USE_THEN "period" ACCEPT_TAC;
      REWRITE_TAC[GSYM ADD1] THEN USE_THEN "least" ACCEPT_TAC];
    DISCH_THEN(LABEL_TAC "even")] THEN
  X_GEN_TAC `s:num` THEN STRIP_TAC THEN
  USE_THEN "even" MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let ODD_PERIOD_IMP_EVEN_PERIOD = prove
 (`!f n m.
        f real_continuous_on (:real) /\
        ODD n /\
        1 < n /\
        has_period f n /\
        EVEN m /\
        0 < m
        ==> has_period f m`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous odd nontrivial period even positive" THEN
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE
   (SPEC `\d:num. ODD d /\ 1 < d /\ has_period (f:real->real) d`
    num_WOP)))) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    INTRO_TAC
     "@d. (dodd dnontrivial dperiod) least"] THEN
  SUBGOAL_THEN `2 < (d:num)` (LABEL_TAC "dlarge") THENL
   [MATCH_MP_TAC(ARITH_RULE `1 < d /\ ~(d = 2) ==> 2 < d`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ODD 2` THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. ODD e /\ 1 < e /\ e < d
        ==> ~has_period (f:real->real) e`
  (LABEL_TAC "leastodd") THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(m:num) < d` THENL
   [USE_THEN "even" (MP_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:num` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`f:real->real`; `d:num`]
     LEAST_ODD_PERIOD_IMP_EVEN_PERIODS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `s:num`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        SIMP_TAC[]]];
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `d:num`; `m:num`]
     ODD_PERIOD_IMP_LARGER_PERIOD) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((m:num) = d)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
     UNDISCH_TAC `EVEN d` THEN
      ASM_REWRITE_TAC[GSYM NOT_ODD];
      ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Transfer of periods between a map and its iterates.                       *)
(* ------------------------------------------------------------------------- *)

let HAS_PERIOD_SQUARE_CASES = prove
 (`!f:A->A m.
        has_period (ITER 2 f) m
        ==> (ODD m /\ has_period f m) \/ has_period f (2 * m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_period] THEN
  INTRO_TAC "@x. square" THEN
  SUBGOAL_THEN `0 < (m:num)` (LABEL_TAC "positive") THENL
   [USE_THEN "square" (MP_TAC o MATCH_MP MINIMAL_PERIOD_POS) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `periodic_point (f:A->A) (m * 2) x`
  (LABEL_TAC "periodic") THENL
   [REWRITE_TAC[GSYM PERIODIC_POINT_ITER] THEN
    MATCH_MP_TAC MINIMAL_PERIOD_PERIODIC THEN
    USE_THEN "square" ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->A`; `x:A`; `m * 2`]
   PERIODIC_POINT_IMP_MINIMAL_PERIOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    INTRO_TAC "@n. divides minimal"] THEN
  SUBGOAL_THEN `m = n DIV gcd(n,2)` (LABEL_TAC "quotient") THENL
   [MATCH_MP_TAC(ISPECL
     [`ITER 2 (f:A->A)`; `m:num`; `n DIV gcd(n,2)`;
      `x:A`] MINIMAL_PERIOD_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MINIMAL_PERIOD_ITER THEN
    USE_THEN "minimal" ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `EVEN n` THENL
   [DISJ2_TAC THEN EXISTS_TAC `x:A` THEN
    SUBGOAL_THEN `(n:num) = 2 * m` SUBST_ALL_TAC THENL
     [USE_THEN "quotient" MP_TAC THEN
      ASM_REWRITE_TAC[GCD_2_CASES] THEN
      SUBGOAL_THEN `n DIV 2 * 2 = n` ASSUME_TAC THENL
       [ASM_SIMP_TAC[DOUBLE_HALF];
        ASM_ARITH_TAC];
      USE_THEN "minimal" ACCEPT_TAC];
    DISJ1_TAC THEN CONJ_TAC THENL
     [USE_THEN "quotient" MP_TAC THEN
      ASM_REWRITE_TAC[GCD_2_CASES; DIV_1; GSYM NOT_EVEN];
      EXISTS_TAC `x:A` THEN
      SUBGOAL_THEN `(n:num) = m` SUBST_ALL_TAC THENL
       [USE_THEN "quotient" MP_TAC THEN
        ASM_REWRITE_TAC[GCD_2_CASES; DIV_1];
        USE_THEN "minimal" ACCEPT_TAC]]]);;

let HAS_PERIOD_SQUARE_IMP_DOUBLE = prove
 (`!f m.
        f real_continuous_on (:real) /\
        1 < m /\
        has_period (ITER 2 f) m
        ==> has_period f (2 * m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `m:num`]
   HAS_PERIOD_SQUARE_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
   (LABEL_TAC "double")) THENL
   [SUBGOAL_THEN `2 < (m:num)` (LABEL_TAC "nontrivial") THENL
     [MATCH_MP_TAC(ARITH_RULE `1 < m /\ ~(m = 2) ==> 2 < m`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `ODD 2` THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `(m:num) < 2 * m` (LABEL_TAC "larger") THENL
     [MATCH_MP_TAC(ARITH_RULE `1 < m ==> m < 2 * m`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `m:num`; `2 * m`]
     ODD_PERIOD_IMP_LARGER_PERIOD) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "double" ACCEPT_TAC]);;

let HAS_PERIOD_POWER2_MULTIPLE_IMP_ITER = prove
 (`!f:A->A a m.
        has_period f ((2 EXP a) * m)
        ==> has_period (ITER (2 EXP a) f) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`f:A->A`; `(2 EXP a) * m`; `2 EXP a`]
   HAS_PERIOD_ITER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `gcd((2 EXP a) * m,2 EXP a) = 2 EXP a`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(2 EXP a) divides (2 EXP a) * m`
    ASSUME_TAC THENL
     [REWRITE_TAC[divides] THEN EXISTS_TAC `m:num` THEN REFL_TAC;
      MP_TAC(SPECL [`(2 EXP a) * m`; `2 EXP a`] GCD) THEN
      INTRO_TAC "(_ gcddivides) greatest" THEN
      REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
      CONJ_TAC THENL
       [USE_THEN "gcddivides" ACCEPT_TAC;
        USE_THEN "greatest" (MP_TAC o SPEC `2 EXP a`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[DIVIDES_REFL];
          SIMP_TAC[]]]];
    SUBGOAL_THEN `~(2 EXP a = 0)` (LABEL_TAC "nonzero") THENL
     [REWRITE_TAC[EXP_EQ_0] THEN ARITH_TAC;
      USE_THEN "nonzero" (fun th ->
       REWRITE_TAC[MATCH_MP
        (SPECL [`2 EXP a`; `m:num`] DIV_MULT) th])]]);;

let HAS_PERIOD_ITER_POWER2_IMP_MULTIPLE = prove
 (`!a f m.
        f real_continuous_on (:real) /\
        1 < m /\
        has_period (ITER (2 EXP a) f) m
        ==> has_period f ((2 EXP a) * m)`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `ITER 1 (f:real->real) = f`
    (fun th -> REWRITE_TAC[EXP; MULT_CLAUSES; th]) THEN
    REWRITE_TAC[FUN_EQ_THM; ITER_1] THEN SIMP_TAC[];
    POP_ASSUM(LABEL_TAC "induction") THEN
    MAP_EVERY X_GEN_TAC [`f:real->real`; `m:num`] THEN
    INTRO_TAC "continuous nontrivial period" THEN
    SUBGOAL_THEN
     `ITER (2 EXP SUC a) (f:real->real) =
     ITER (2 EXP a) (ITER 2 f)`
    (LABEL_TAC "iterate") THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[ITER_MUL; EXP; MULT_SYM];
      ALL_TAC] THEN
    USE_THEN "induction"
     (MP_TAC o SPECL [`ITER 2 (f:real->real)`; `m:num`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_ITER THEN
        USE_THEN "continuous" ACCEPT_TAC;
        USE_THEN "nontrivial" ACCEPT_TAC;
        USE_THEN "iterate" (fun th ->
         USE_THEN "period" (ACCEPT_TAC o REWRITE_RULE[th]))];
      DISCH_THEN(LABEL_TAC "squareperiod")] THEN
    REWRITE_TAC[EXP] THEN REWRITE_TAC[GSYM MULT_ASSOC] THEN
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `(2 EXP a) * m`]
     HAS_PERIOD_SQUARE_IMP_DOUBLE) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `m:num` THEN
      CONJ_TAC THENL
       [USE_THEN "nontrivial" ACCEPT_TAC;
        SUBGOAL_THEN `1 <= 2 EXP a` ASSUME_TAC THENL
         [MATCH_MP_TAC(ARITH_RULE `0 < k ==> 1 <= k`) THEN
          REWRITE_TAC[LT_NZ; EXP_EQ_0] THEN ARITH_TAC;
          MP_TAC(SPECL [`1`; `2 EXP a`; `m:num`; `m:num`]
           LE_MULT2) THEN
          ASM_REWRITE_TAC[MULT_CLAUSES; LE_REFL]]];
      USE_THEN "squareperiod" ACCEPT_TAC]]);;

let HAS_PERIOD_POWER2_SUC_IMP_POWER2 = prove
 (`!f a.
        f real_continuous_on (:real) /\
        has_period f (2 EXP (SUC a))
        ==> has_period f (2 EXP a)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous period" THEN
  ASM_CASES_TAC `(a:num) = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[EXP; MULT_CLAUSES] THEN
    MATCH_MP_TAC(ISPECL [`f:real->real`; `2`]
     HAS_PERIOD_IMP_PERIOD_1) THEN
    CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      USE_THEN "period"
       (ACCEPT_TAC o REWRITE_RULE[EXP; MULT_CLAUSES])];
    MP_TAC(SPEC `a:num` num_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num` SUBST_ALL_TAC)] THEN
  SUBGOAL_THEN
   `(ITER (2 EXP b) f) real_continuous_on (:real)`
  (LABEL_TAC "itercontinuous") THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ITER THEN
    USE_THEN "continuous" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `has_period (ITER (2 EXP b) (f:real->real)) 4`
  (LABEL_TAC "period4") THENL
   [MATCH_MP_TAC(ISPECL
     [`f:real->real`; `b:num`; `4`]
     HAS_PERIOD_POWER2_MULTIPLE_IMP_ITER) THEN
    SUBGOAL_THEN
     `(2 EXP b) * 4 = 2 EXP SUC (SUC b)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXP] THEN ARITH_TAC;
      USE_THEN "period" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `has_period (ITER (2 EXP b) (f:real->real)) 2`
  (LABEL_TAC "period2") THENL
   [MATCH_MP_TAC PERIOD_4_IMP_PERIOD_2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:num`; `f:real->real`; `2`]
   HAS_PERIOD_ITER_POWER2_IMP_MULTIPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_THEN(LABEL_TAC "multiple")] THEN
  SUBGOAL_THEN
   `(2 EXP b) * 2 = 2 EXP SUC b`
  (fun th -> REWRITE_TAC[GSYM th] THEN
             USE_THEN "multiple" ACCEPT_TAC) THEN
  REWRITE_TAC[EXP; MULT_SYM]);;

let HAS_PERIOD_POWER2_MONO = prove
 (`!f a b.
        f real_continuous_on (:real) /\
        b <= a /\
        has_period f (2 EXP a)
        ==> has_period f (2 EXP b)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(b:num) = 0` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    POP_ASSUM(LABEL_TAC "induction") THEN
    X_GEN_TAC `b:num` THEN
    INTRO_TAC "continuous le period" THEN
    ASM_CASES_TAC `(b:num) = SUC a` THENL
     [ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "induction" (MP_TAC o SPEC `b:num`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "continuous" ACCEPT_TAC;
        ASM_ARITH_TAC;
        MATCH_MP_TAC HAS_PERIOD_POWER2_SUC_IMP_POWER2 THEN
        ASM_REWRITE_TAC[]];
      SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Sarkovskii's ordering and the full forcing theorem.                       *)
(* ------------------------------------------------------------------------- *)

let ODD_POS = prove
 (`!n. ODD n ==> 0 < n`,
  REWRITE_TAC[ODD_EXISTS] THEN ARITH_TAC);;

let ODD_GT_1_IMP_GT_2 = prove
 (`!n. ODD n /\ 1 < n ==> 2 < n`,
  GEN_TAC THEN
  INTRO_TAC "odd large" THEN
  MATCH_MP_TAC(ARITH_RULE `1 < n /\ ~(n = 2) ==> 2 < n`) THEN
  CONJ_TAC THENL
   [USE_THEN "large" ACCEPT_TAC;
    DISCH_THEN(LABEL_TAC "eq") THEN
    USE_THEN "odd" MP_TAC THEN
    USE_THEN "eq" (fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let EVEN_POS_IMP_GT_1 = prove
 (`!n. EVEN n /\ 0 < n ==> 1 < n`,
  GEN_TAC THEN
  INTRO_TAC "even positive" THEN
  MATCH_MP_TAC(ARITH_RULE `0 < n /\ ~(n = 1) ==> 1 < n`) THEN
  CONJ_TAC THENL
   [USE_THEN "positive" ACCEPT_TAC;
    DISCH_THEN(LABEL_TAC "eq") THEN
    USE_THEN "even" MP_TAC THEN
    USE_THEN "eq" (fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let POWER2_SPLIT = prove
 (`!a b. a <= b
          ==> 2 EXP a * 2 EXP (b - a) = 2 EXP b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let ODD_FACTOR_PERIOD_IMP_LATER_PERIOD = prove
 (`!f a u b v.
        f real_continuous_on (:real) /\
        ODD u /\
        1 < u /\
        ODD v /\
        has_period f (2 EXP a * u) /\
        (v = 1 \/ a < b \/ a = b /\ u < v)
        ==> has_period f (2 EXP b * v)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous uodd ularge vodd period later" THEN
  SUBGOAL_THEN
   `(ITER (2 EXP a) f) real_continuous_on (:real)`
  (LABEL_TAC "itercontinuous") THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ITER THEN
    USE_THEN "continuous" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `has_period (ITER (2 EXP a) (f:real->real)) u`
  (LABEL_TAC "oddperiod") THENL
   [MATCH_MP_TAC(ISPECL
     [`f:real->real`; `a:num`; `u:num`]
     HAS_PERIOD_POWER2_MULTIPLE_IMP_ITER) THEN
    USE_THEN "period" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 < (u:num)` (LABEL_TAC "ugt2") THENL
   [MATCH_MP_TAC ODD_GT_1_IMP_GT_2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(v:num) = 1` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_CASES_TAC `(a:num) < b` THENL
     [SUBGOAL_THEN
       `has_period (ITER (2 EXP a) (f:real->real))
                   (2 EXP (b - a))`
      (LABEL_TAC "iterpower") THENL
       [MATCH_MP_TAC(ISPECL
         [`ITER (2 EXP a) (f:real->real)`; `u:num`;
          `2 EXP (b - a)`]
         ODD_PERIOD_IMP_EVEN_PERIOD) THEN
        REPEAT CONJ_TAC THENL
         [USE_THEN "itercontinuous" ACCEPT_TAC;
          USE_THEN "uodd" ACCEPT_TAC;
          USE_THEN "ularge" ACCEPT_TAC;
          USE_THEN "oddperiod" ACCEPT_TAC;
          REWRITE_TAC[EVEN_EXP] THEN ASM_ARITH_TAC;
          REWRITE_TAC[LT_NZ; EXP_EQ_0] THEN ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`a:num`; `f:real->real`; `2 EXP (b - a)`]
       HAS_PERIOD_ITER_POWER2_IMP_MULTIPLE) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "continuous" ACCEPT_TAC;
          MATCH_MP_TAC EVEN_POS_IMP_GT_1 THEN
          REWRITE_TAC[EVEN_EXP; LT_NZ; EXP_EQ_0] THEN
          ASM_ARITH_TAC;
          USE_THEN "iterpower" ACCEPT_TAC];
        DISCH_THEN(LABEL_TAC "lifted")] THEN
      MP_TAC(SPECL [`a:num`; `b:num`] POWER2_SPLIT) THEN
      ANTS_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
        USE_THEN "lifted" ACCEPT_TAC];
      SUBGOAL_THEN
       `has_period (ITER (2 EXP a) (f:real->real)) 2`
      (LABEL_TAC "iterperiod2") THENL
       [MATCH_MP_TAC(ISPECL
         [`ITER (2 EXP a) (f:real->real)`; `u:num`; `2`]
         ODD_PERIOD_IMP_EVEN_PERIOD) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`a:num`; `f:real->real`; `2`]
       HAS_PERIOD_ITER_POWER2_IMP_MULTIPLE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN(LABEL_TAC "nextpower")] THEN
      MATCH_MP_TAC(ISPECL
       [`f:real->real`; `SUC a`; `b:num`]
       HAS_PERIOD_POWER2_MONO) THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "continuous" ACCEPT_TAC;
        ASM_ARITH_TAC;
        REWRITE_TAC[EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
        USE_THEN "nextpower" ACCEPT_TAC]];
    POP_ASSUM(LABEL_TAC "vnotone")] THEN
  SUBGOAL_THEN `1 < (v:num)` (LABEL_TAC "vlarge") THENL
   [USE_THEN "vodd" (MP_TAC o REWRITE_RULE[ODD_EXISTS]) THEN
    INTRO_TAC "@c. vform" THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "later" MP_TAC THEN
  USE_THEN "vnotone" (fun th -> REWRITE_TAC[th]) THEN
  (DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "ab")
   (CONJUNCTS_THEN2 (LABEL_TAC "abeq") (LABEL_TAC "uv"))) THENL
   [ABBREV_TAC `k:num = 2 EXP (b - a) * v` THEN
    SUBGOAL_THEN `EVEN k /\ 0 < k`
    (DESTRUCT_TAC "keven kpos") THENL
     [EXPAND_TAC "k" THEN CONJ_TAC THENL
       [REWRITE_TAC[EVEN_MULT; EVEN_EXP] THEN ASM_ARITH_TAC;
        REWRITE_TAC[LT_NZ; MULT_EQ_0; EXP_EQ_0] THEN
        MP_TAC(SPEC `v:num` ODD_POS) THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `has_period (ITER (2 EXP a) (f:real->real)) k`
    (LABEL_TAC "iterperiod") THENL
     [MATCH_MP_TAC(ISPECL
       [`ITER (2 EXP a) (f:real->real)`; `u:num`; `k:num`]
       ODD_PERIOD_IMP_EVEN_PERIOD) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:num`; `f:real->real`; `k:num`]
     HAS_PERIOD_ITER_POWER2_IMP_MULTIPLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EVEN_POS_IMP_GT_1 THEN ASM_REWRITE_TAC[];
      DISCH_THEN(LABEL_TAC "lifted")] THEN
    SUBGOAL_THEN
     `2 EXP a * k = 2 EXP b * v`
    (fun th -> USE_THEN "lifted"
      (ACCEPT_TAC o REWRITE_RULE[th])) THEN
    EXPAND_TAC "k" THEN
    MP_TAC(SPECL [`a:num`; `b:num`] POWER2_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[MULT_ASSOC; th])];
    USE_THEN "abeq" SUBST_ALL_TAC THEN
    SUBGOAL_THEN
     `has_period (ITER (2 EXP b) (f:real->real)) v`
    (LABEL_TAC "iterperiod") THENL
     [MATCH_MP_TAC(ISPECL
       [`ITER (2 EXP b) (f:real->real)`; `u:num`; `v:num`]
       ODD_PERIOD_IMP_LARGER_PERIOD) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL [`b:num`; `f:real->real`; `v:num`]
     HAS_PERIOD_ITER_POWER2_IMP_MULTIPLE) THEN
    ASM_REWRITE_TAC[]]));;

let sarkovskii_precedes = new_definition
 `sarkovskii_precedes m n <=>
    ?a b u v.
        ODD u /\
        ODD v /\
        m = 2 EXP a * u /\
        n = 2 EXP b * v /\
        ((1 < u /\
          (v = 1 \/ a < b \/ a = b /\ u < v)) \/
         (u = 1 /\ v = 1 /\ b < a))`;;

let SARKOVSKII_PRECEDES_POS = prove
 (`!m n.
        sarkovskii_precedes m n
        ==> 0 < m /\ 0 < n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sarkovskii_precedes] THEN
  INTRO_TAC "@a b u v. uodd vodd meq neq _" THEN
  CONJ_TAC THENL
   [USE_THEN "meq" SUBST1_TAC THEN
    REWRITE_TAC[LT_MULT; EXP_LT_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC ODD_POS THEN ASM_REWRITE_TAC[];
    USE_THEN "neq" SUBST1_TAC THEN
    REWRITE_TAC[LT_MULT; EXP_LT_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC ODD_POS THEN ASM_REWRITE_TAC[]]);;

let ODD_POWER2_FACTOR_LE = prove
 (`!a b u v.
        ODD u /\
        2 EXP a * u = 2 EXP b * v /\
        a <= b
        ==> b <= a`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "uodd eq le" THEN
  USE_THEN "le" (MP_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  INTRO_TAC "@c. split" THEN
  SUBGOAL_THEN
   `u = 2 EXP c * v`
  (LABEL_TAC "factors") THENL
   [USE_THEN "eq" MP_TAC THEN
    USE_THEN "split" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC;
                EQ_MULT_LCANCEL; EXP_EQ_0] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:num) = 0` SUBST_ALL_TAC THENL
   [ASM_CASES_TAC `(c:num) = 0` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "uodd" MP_TAC THEN
    USE_THEN "factors" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ODD_MULT; ODD_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL]]);;

let ODD_POWER2_FACTOR_UNIQUE = prove
 (`!a b u v.
        ODD u /\
        ODD v /\
        2 EXP a * u = 2 EXP b * v
        ==> a = b /\ u = v`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "uodd vodd eq" THEN
  SUBGOAL_THEN `(a:num) = b` (LABEL_TAC "exponents") THENL
   [DISJ_CASES_TAC(SPECL [`a:num`; `b:num`] LE_CASES) THENL
     [SUBGOAL_THEN `(b:num) <= a` MP_TAC THENL
       [MATCH_MP_TAC(ISPECL
         [`a:num`; `b:num`; `u:num`; `v:num`]
         ODD_POWER2_FACTOR_LE) THEN
        ASM_REWRITE_TAC[];
        ASM_ARITH_TAC];
      SUBGOAL_THEN `(a:num) <= b` MP_TAC THENL
       [MATCH_MP_TAC(ISPECL
         [`b:num`; `a:num`; `v:num`; `u:num`]
         ODD_POWER2_FACTOR_LE) THEN
        ASM_REWRITE_TAC[];
        ASM_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "exponents" ACCEPT_TAC;
    USE_THEN "eq" MP_TAC THEN
    USE_THEN "exponents" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0] THEN
    ARITH_TAC]);;

let SARKOVSKII_PRECEDES_ODD_FACTORS = prove
 (`!a b u v.
        ODD u /\
        ODD v
        ==> (sarkovskii_precedes (2 EXP a * u) (2 EXP b * v) <=>
             (1 < u /\
              (v = 1 \/ a < b \/ a = b /\ u < v)) \/
             (u = 1 /\ v = 1 /\ b < a))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "uodd vodd" THEN
  REWRITE_TAC[sarkovskii_precedes] THEN EQ_TAC THENL
   [INTRO_TAC "@c d w x. wodd xodd first second order" THEN
    SUBGOAL_THEN `(a:num) = c /\ (u:num) = w`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC ODD_POWER2_FACTOR_UNIQUE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(b:num) = d /\ (v:num) = x`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC ODD_POWER2_FACTOR_UNIQUE THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_THEN(LABEL_TAC "order") THEN
    MAP_EVERY EXISTS_TAC
     [`a:num`; `b:num`; `u:num`; `v:num`] THEN
    ASM_REWRITE_TAC[]]);;

let SARKOVSKII_PRECEDES_IRREFLEXIVE = prove
 (`!n. ~sarkovskii_precedes n n`,
  GEN_TAC THEN REWRITE_TAC[sarkovskii_precedes] THEN
  INTRO_TAC "@a b u v. uodd vodd first second order" THEN
  SUBGOAL_THEN `(a:num) = b /\ (u:num) = v`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ODD_POWER2_FACTOR_UNIQUE THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "first" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "second" (fun th -> REWRITE_TAC[GSYM th]);
    ASM_ARITH_TAC]);;

let SARKOVSKII_PRECEDES_TRANSITIVE = prove
 (`!m n p.
        sarkovskii_precedes m n /\
        sarkovskii_precedes n p
        ==> sarkovskii_precedes m p`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "first second" THEN
  USE_THEN "first" (MP_TAC o REWRITE_RULE[sarkovskii_precedes]) THEN
  INTRO_TAC "@a b u v. uodd vodd meq neq order1" THEN
  USE_THEN "second" (MP_TAC o REWRITE_RULE[sarkovskii_precedes]) THEN
  INTRO_TAC "@c d w x. wodd xodd neqprime peq order2" THEN
  SUBGOAL_THEN `(b:num) = c /\ (v:num) = w`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ODD_POWER2_FACTOR_UNIQUE THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "neq" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "neqprime" (fun th -> REWRITE_TAC[GSYM th]);
    ALL_TAC] THEN
  USE_THEN "meq" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "peq" (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[SARKOVSKII_PRECEDES_ODD_FACTORS] THEN
  ASM_ARITH_TAC);;

let SARKOVSKII_PRECEDES_ASYMMETRIC = prove
 (`!m n.
        sarkovskii_precedes m n
        ==> ~sarkovskii_precedes n m`,
  MESON_TAC[SARKOVSKII_PRECEDES_TRANSITIVE;
            SARKOVSKII_PRECEDES_IRREFLEXIVE]);;

let SARKOVSKII_PRECEDES_TRICHOTOMY = prove
 (`!m n.
        0 < m /\
        0 < n
        ==> m = n \/
            sarkovskii_precedes m n \/
            sarkovskii_precedes n m`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "mpos npos" THEN
  MP_TAC(SPEC `m:num` EVEN_ODD_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[GSYM LT_NZ] THEN
  INTRO_TAC "@a u. uodd meq" THEN
  MP_TAC(SPEC `n:num` EVEN_ODD_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[GSYM LT_NZ] THEN
  INTRO_TAC "@b v. vodd neq" THEN
  SUBGOAL_THEN `0 < u /\ 0 < v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ODD_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "meq" SUBST_ALL_TAC THEN
  USE_THEN "neq" SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[SARKOVSKII_PRECEDES_ODD_FACTORS] THEN
  ASM_CASES_TAC `(u:num) = 1` THEN
  ASM_CASES_TAC `(v:num) = 1` THEN
  ASM_CASES_TAC `(a:num) = b` THEN
  ASM_CASES_TAC `(u:num) = v` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let SARKOVSKII_PRECEDES_3 = prove
 (`!n. ~sarkovskii_precedes n 3`,
  GEN_TAC THEN REWRITE_TAC[sarkovskii_precedes] THEN
  INTRO_TAC "@a b u v. uodd vodd _ three order" THEN
  SUBGOAL_THEN `(b:num) = 0 /\ (v:num) = 3`
  (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(ISPECL
     [`b:num`; `0`; `v:num`; `3`]
     ODD_POWER2_FACTOR_UNIQUE) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "vodd" ACCEPT_TAC;
      CONV_TAC NUM_REDUCE_CONV;
      CONV_TAC NUM_REDUCE_CONV THEN
      USE_THEN "three" (ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  REMOVE_THEN "order" MP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  INTRO_TAC "ularge (aneg | _ usmall)" THENL
   [ASM_ARITH_TAC;
    MP_TAC(SPEC `u:num` ODD_GT_1_IMP_GT_2) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let SARKOVSKII_3_PRECEDES = prove
 (`!n.
        0 < n
        ==> (sarkovskii_precedes 3 n <=> ~(n = 3))`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "npos") THEN EQ_TAC THENL
   [DISCH_THEN(LABEL_TAC "precedes") THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "precedes" MP_TAC THEN
    REWRITE_TAC[SARKOVSKII_PRECEDES_IRREFLEXIVE];
    DISCH_THEN(LABEL_TAC "neq") THEN
    MP_TAC(SPECL [`3`; `n:num`]
     SARKOVSKII_PRECEDES_TRICHOTOMY) THEN
    ASM_REWRITE_TAC[SARKOVSKII_PRECEDES_3] THEN
    ARITH_TAC]);;

let SARKOVSKII_1_PRECEDES = prove
 (`!n. ~sarkovskii_precedes 1 n`,
  GEN_TAC THEN REWRITE_TAC[sarkovskii_precedes] THEN
  INTRO_TAC "@a b u v. uodd _ one _ order" THEN
  SUBGOAL_THEN `(a:num) = 0 /\ (u:num) = 1`
  (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) THENL
   [MATCH_MP_TAC(ISPECL
     [`a:num`; `0`; `u:num`; `1`]
     ODD_POWER2_FACTOR_UNIQUE) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "uodd" ACCEPT_TAC;
      CONV_TAC NUM_REDUCE_CONV;
      CONV_TAC NUM_REDUCE_CONV THEN
      USE_THEN "one" (ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  REMOVE_THEN "order" MP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let SARKOVSKII_PRECEDES_1 = prove
 (`!n.
        0 < n
        ==> (sarkovskii_precedes n 1 <=> ~(n = 1))`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "npos") THEN EQ_TAC THENL
   [DISCH_THEN(LABEL_TAC "precedes") THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "precedes" MP_TAC THEN
    REWRITE_TAC[SARKOVSKII_PRECEDES_IRREFLEXIVE];
    DISCH_THEN(LABEL_TAC "neq") THEN
    MP_TAC(SPECL [`n:num`; `1`]
     SARKOVSKII_PRECEDES_TRICHOTOMY) THEN
    ASM_REWRITE_TAC[SARKOVSKII_1_PRECEDES] THEN
    ARITH_TAC]);;

let SARKOVSKII_PRECEDES_IMP_PERIOD = prove
 (`!f m n.
        f real_continuous_on (:real) /\
        sarkovskii_precedes m n /\
        has_period f m
        ==> has_period f n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sarkovskii_precedes] THEN
  INTRO_TAC
   "continuous (@a b u v. uodd vodd meq neq order) period" THEN
  USE_THEN "neq" SUBST1_TAC THEN
  USE_THEN "order"
   (DISJ_CASES_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "ularge") (LABEL_TAC "later"))
    (CONJUNCTS_THEN2 (LABEL_TAC "uone")
     (CONJUNCTS_THEN2 (LABEL_TAC "vone") (LABEL_TAC "ba"))))
  THENL
   [MATCH_MP_TAC(ISPECL
     [`f:real->real`; `a:num`; `u:num`; `b:num`; `v:num`]
     ODD_FACTOR_PERIOD_IMP_LATER_PERIOD) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      USE_THEN "uodd" ACCEPT_TAC;
      USE_THEN "ularge" ACCEPT_TAC;
      USE_THEN "vodd" ACCEPT_TAC;
      USE_THEN "period"
       (ACCEPT_TAC o REWRITE_RULE[ASSUME
        `m = 2 EXP a * u`]);
      USE_THEN "later" ACCEPT_TAC];
    USE_THEN "uone" SUBST_ALL_TAC THEN
    USE_THEN "vone" SUBST_ALL_TAC THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `a:num`; `b:num`]
     HAS_PERIOD_POWER2_MONO) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      ASM_ARITH_TAC;
      USE_THEN "period"
       (ACCEPT_TAC o REWRITE_RULE
        [ASSUME `m = 2 EXP a * 1`; MULT_CLAUSES])]]);;

let SARKOVSKII_THEOREM = prove
 (`!f m n.
        f real_continuous_on (:real) /\
        (m = n \/ sarkovskii_precedes m n) /\
        has_period f m
        ==> has_period f n`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous (eq | precedes) period" THENL
   [USE_THEN "eq" (fun th ->
     USE_THEN "period" (ACCEPT_TAC o REWRITE_RULE[th]));
    MATCH_MP_TAC(ISPECL
     [`f:real->real`; `m:num`; `n:num`]
     SARKOVSKII_PRECEDES_IMP_PERIOD) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "continuous" ACCEPT_TAC;
      USE_THEN "precedes" ACCEPT_TAC;
      USE_THEN "period" ACCEPT_TAC]]);;

let PERIOD_3_IMP_ALL_PERIODS = prove
 (`!f n.
        f real_continuous_on (:real) /\
        0 < n /\
        has_period f 3
        ==> has_period f n`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "continuous npos period" THEN
  MATCH_MP_TAC(ISPECL [`f:real->real`; `3`; `n:num`]
   SARKOVSKII_THEOREM) THEN
  ASM_SIMP_TAC[SARKOVSKII_3_PRECEDES] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Localized periods and scalar homeomorphisms.                              *)
(* ------------------------------------------------------------------------- *)

let has_period_on = new_definition
 `has_period_on (f:A->A) n s <=>
        ?x. x IN s /\ minimal_period f n x`;;

let REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP = prove
 (`!f s.
        f real_continuous_on s <=>
        continuous_map
         (subtopology euclideanreal s,euclideanreal) f`,
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC;
              GSYM MTOPOLOGY_SUBMETRIC] THEN
  REWRITE_TAC[METRIC_CONTINUOUS_MAP; real_continuous_on] THEN
  REWRITE_TAC[SUBMETRIC; REAL_EUCLIDEAN_METRIC; IN_UNIV; IN_INTER] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_ABS_SUB] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`a:real`; `e:real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[REAL_ABS_SUB];
    DISCH_TAC THEN X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `e:real`]) THEN
    ASM_REWRITE_TAC[REAL_ABS_SUB]]);;

let REAL_HOMEOMORPHISM = prove
 (`!s t h k.
        homeomorphic_maps
         (subtopology euclideanreal s,
          subtopology euclideanreal t) (h,k) <=>
        h real_continuous_on s /\
        IMAGE h s SUBSET t /\
        k real_continuous_on t /\
        IMAGE k t SUBSET s /\
        (!x. x IN s ==> k(h x) = x) /\
        (!y. y IN t ==> h(k y) = y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
              REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP] THEN
  ITAUT_TAC);;

let ITER_CONJUGATE_ON = prove
 (`!f h k s t.
        homeomorphic_maps
         (subtopology euclideanreal s,
          subtopology euclideanreal t) (h,k) /\
        IMAGE f s SUBSET s
        ==> !n x.
              x IN s
              ==> ITER n (h o f o k) (h x) = h(ITER n f x) /\
                  ITER n f x IN s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_HOMEOMORPHISM] THEN
  INTRO_TAC "(_ _ _ _ leftinv _) invariant" THEN
  INDUCT_TAC THENL
   [SIMP_TAC[ITER];
    X_GEN_TAC `x:real` THEN DISCH_THEN(LABEL_TAC "inside") THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    ASM_REWRITE_TAC[] THEN
    INTRO_TAC "iterate iterinside" THEN
    REWRITE_TAC[ITER; o_THM] THEN
    USE_THEN "iterate" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "leftinv" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "invariant"
     (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    USE_THEN "iterinside" ACCEPT_TAC]);;

let MINIMAL_PERIOD_CONJUGATE_ON = prove
 (`!f h k s t n x.
        homeomorphic_maps
         (subtopology euclideanreal s,
          subtopology euclideanreal t) (h,k) /\
        IMAGE f s SUBSET s /\
        x IN s
        ==> (minimal_period (h o f o k) n (h x) <=>
             minimal_period f n x)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "homeomorphism invariant inside" THEN
  SUBGOAL_THEN
   `!m. periodic_point ((h:real->real) o f o k) m (h x) <=>
        periodic_point f m x`
  (LABEL_TAC "periodic") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL
     [`f:real->real`; `h:real->real`; `k:real->real`;
      `s:real->bool`; `t:real->bool`]
     ITER_CONJUGATE_ON) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `x:real`]) THEN
    ASM_REWRITE_TAC[periodic_point] THEN
    INTRO_TAC "iterate iterinside" THEN
    USE_THEN "homeomorphism"
     (MP_TAC o REWRITE_RULE[REAL_HOMEOMORPHISM]) THEN
    INTRO_TAC "_ _ _ _ leftinv _" THEN
    USE_THEN "iterate" (fun th -> REWRITE_TAC[th]) THEN
    EQ_TAC THENL
     [DISCH_THEN(LABEL_TAC "same") THEN
      MP_TAC(BETA_RULE(AP_TERM `k:real->real`
       (ASSUME `(h:real->real) (ITER m f x) = h x`))) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    REWRITE_TAC[minimal_period] THEN
    USE_THEN "periodic" (fun th -> REWRITE_TAC[th])]);;

let HAS_PERIOD_ON_CONJUGATE = prove
 (`!f h k s t n.
        homeomorphic_maps
         (subtopology euclideanreal s,
          subtopology euclideanreal t) (h,k) /\
        IMAGE f s SUBSET s
        ==> (has_period_on f n s <=>
             has_period_on (h o f o k) n t)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "homeomorphism invariant" THEN
  USE_THEN "homeomorphism"
   (MP_TAC o REWRITE_RULE[REAL_HOMEOMORPHISM]) THEN
  INTRO_TAC "_ hinto _ kinto leftinv rightinv" THEN
  REWRITE_TAC[has_period_on] THEN EQ_TAC THENL
   [INTRO_TAC "@x. inside minimal" THEN
    EXISTS_TAC `(h:real->real) x` THEN CONJ_TAC THENL
     [USE_THEN "hinto"
       (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      USE_THEN "inside" ACCEPT_TAC;
      MP_TAC(ISPECL
       [`f:real->real`; `h:real->real`; `k:real->real`;
        `s:real->bool`; `t:real->bool`; `n:num`; `x:real`]
       MINIMAL_PERIOD_CONJUGATE_ON) THEN
      ASM_REWRITE_TAC[]];
    INTRO_TAC "@y. inside minimal" THEN
    EXISTS_TAC `(k:real->real) y` THEN CONJ_TAC THENL
     [USE_THEN "kinto"
       (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      USE_THEN "inside" ACCEPT_TAC;
      MP_TAC(ISPECL
       [`f:real->real`; `h:real->real`; `k:real->real`;
        `s:real->bool`; `t:real->bool`; `n:num`;
        `(k:real->real) y`]
       MINIMAL_PERIOD_CONJUGATE_ON) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "kinto"
         (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
        USE_THEN "inside" ACCEPT_TAC;
        DISCH_THEN(MP_TAC) THEN
        USE_THEN "rightinv" (fun th -> ASM_SIMP_TAC[th])]]]);;

(* ------------------------------------------------------------------------- *)
(* Extension from a closed real interval and transfer of periods.            *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_EXTENSION_INTO_REALINTERVAL = prove
 (`!f s.
        real_closed s /\
        is_realinterval s /\
        ~(s = {}) /\
        f real_continuous_on s /\
        IMAGE f s SUBSET s
        ==> ?g.
              g real_continuous_on (:real) /\
              IMAGE g (:real) SUBSET s /\
              (!x. x IN s ==> g x = f x)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "closed interval nonempty continuous invariant" THEN
  MP_TAC(ISPECL
   [`euclideanreal`; `f:real->real`;
    `s:real->bool`; `s:real->bool`]
   TIETZE_EXTENSION_REALINTERVAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
      REWRITE_TAC[NORMAL_SPACE_MTOPOLOGY];
      ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN];
      USE_THEN "interval" ACCEPT_TAC;
      USE_THEN "nonempty" ACCEPT_TAC;
      REWRITE_TAC[GSYM REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP] THEN
      USE_THEN "continuous" ACCEPT_TAC;
      USE_THEN "invariant"
       (ACCEPT_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE])];
    INTRO_TAC "@g. continuousg intog agrees"] THEN
  EXISTS_TAC `g:real->real` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP] THEN
    REWRITE_TAC[GSYM TOPSPACE_EUCLIDEANREAL;
                SUBTOPOLOGY_TOPSPACE] THEN
    USE_THEN "continuousg" ACCEPT_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `x:real` THEN
    USE_THEN "intog" MATCH_MP_TAC THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; IN_UNIV];
    USE_THEN "agrees" ACCEPT_TAC]);;

let ITER_EQ_ON_EXTENSION = prove
 (`!f g s.
        IMAGE f (:A) SUBSET s /\
        (!x. x IN s ==> f x = g x)
        ==> !n x.
              x IN s
              ==> ITER n f x = ITER n g x /\
                  ITER n f x IN s`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "into agrees" THEN
  INDUCT_TAC THENL
   [SIMP_TAC[ITER];
    X_GEN_TAC `x:A` THEN DISCH_THEN(LABEL_TAC "inside") THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC[] THEN
    INTRO_TAC "iterate iterinside" THEN
    REWRITE_TAC[ITER] THEN
    USE_THEN "iterate" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [USE_THEN "agrees" MATCH_MP_TAC THEN
      USE_THEN "iterate" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "iterinside" ACCEPT_TAC;
      USE_THEN "into"
       (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      REWRITE_TAC[IN_UNIV]]]);;

let MINIMAL_PERIOD_EQ_ON_EXTENSION = prove
 (`!f g s n x.
        IMAGE f (:A) SUBSET s /\
        (!y. y IN s ==> f y = g y) /\
        x IN s
        ==> (minimal_period f n x <=> minimal_period g n x)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "into agrees inside" THEN
  SUBGOAL_THEN
   `!m. periodic_point (f:A->A) m (x:A) <=>
        periodic_point g m x`
  (LABEL_TAC "periodic") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`f:A->A`; `g:A->A`; `s:A->bool`]
     ITER_EQ_ON_EXTENSION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `x:A`]) THEN
    ASM_REWRITE_TAC[periodic_point] THEN MESON_TAC[];
    REWRITE_TAC[minimal_period] THEN
    USE_THEN "periodic" (fun th -> REWRITE_TAC[th])]);;

let PERIODIC_POINT_IN_EXTENSION_RANGE = prove
 (`!f:A->A s n x.
        IMAGE f (:A) SUBSET s /\
        0 < n /\
        periodic_point f n x
        ==> x IN s`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "into positive periodic" THEN
  MP_TAC(SPEC `n:num` num_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)) THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "into"
   (MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  DISCH_THEN(MP_TAC o SPEC `ITER m (f:A->A) x`) THEN
  REWRITE_TAC[IN_UNIV] THEN
  USE_THEN "periodic" MP_TAC THEN
  REWRITE_TAC[periodic_point; ITER] THEN MESON_TAC[]);;

let HAS_PERIOD_EXTENSION_EQ = prove
 (`!f g s n.
        IMAGE f (:A) SUBSET s /\
        (!x. x IN s ==> f x = g x)
        ==> (has_period f n <=> has_period_on g n s)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "into agrees" THEN
  REWRITE_TAC[has_period; has_period_on] THEN EQ_TAC THENL
   [INTRO_TAC "@x. minimal" THEN
    SUBGOAL_THEN `(x:A) IN s` (LABEL_TAC "inside") THENL
     [MATCH_MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `n:num`; `x:A`]
       PERIODIC_POINT_IN_EXTENSION_RANGE) THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "into" ACCEPT_TAC;
        USE_THEN "minimal"
         (ACCEPT_TAC o MATCH_MP MINIMAL_PERIOD_POS);
        USE_THEN "minimal"
         (ACCEPT_TAC o MATCH_MP MINIMAL_PERIOD_PERIODIC)];
      ALL_TAC] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`f:A->A`; `g:A->A`; `s:A->bool`; `n:num`; `x:A`]
     MINIMAL_PERIOD_EQ_ON_EXTENSION) THEN
    ASM_REWRITE_TAC[];
    INTRO_TAC "@x. inside minimal" THEN
    EXISTS_TAC `x:A` THEN
    MP_TAC(ISPECL
     [`f:A->A`; `g:A->A`; `s:A->bool`; `n:num`; `x:A`]
     MINIMAL_PERIOD_EQ_ON_EXTENSION) THEN
    ASM_REWRITE_TAC[]]);;

let SARKOVSKII_THEOREM_CLOSED_REALINTERVAL = prove
 (`!f s m n.
        real_closed s /\
        is_realinterval s /\
        f real_continuous_on s /\
        IMAGE f s SUBSET s /\
        (m = n \/ sarkovskii_precedes m n) /\
        has_period_on f m s
        ==> has_period_on f n s`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "closed interval continuous invariant order period" THEN
  SUBGOAL_THEN `~(s:real->bool = {})`
  (LABEL_TAC "nonempty") THENL
   [USE_THEN "period" MP_TAC THEN
    REWRITE_TAC[has_period_on] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `s:real->bool`]
   REAL_CONTINUOUS_EXTENSION_INTO_REALINTERVAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    INTRO_TAC "@g. continuousg intog agrees"] THEN
  SUBGOAL_THEN `has_period (g:real->real) m`
  (LABEL_TAC "periodg") THENL
   [MP_TAC(ISPECL
     [`g:real->real`; `f:real->real`; `s:real->bool`; `m:num`]
     HAS_PERIOD_EXTENSION_EQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `has_period (g:real->real) n`
  (LABEL_TAC "targetg") THENL
   [MATCH_MP_TAC(ISPECL [`g:real->real`; `m:num`; `n:num`]
     SARKOVSKII_THEOREM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g:real->real`; `f:real->real`; `s:real->bool`; `n:num`]
   HAS_PERIOD_EXTENSION_EQ) THEN
  ASM_REWRITE_TAC[]);;

let SARKOVSKII_THEOREM_HOMEOMORPHIC_CLOSED = prove
 (`!f s t h k m n.
        homeomorphic_maps
         (subtopology euclideanreal s,
          subtopology euclideanreal t) (h,k) /\
        real_closed t /\
        is_realinterval t /\
        f real_continuous_on s /\
        IMAGE f s SUBSET s /\
        (m = n \/ sarkovskii_precedes m n) /\
        has_period_on f m s
        ==> has_period_on f n s`,
  REPEAT GEN_TAC THEN
  INTRO_TAC
   ("homeomorphism closed interval continuous invariant order " ^
    "period") THEN
  USE_THEN "homeomorphism"
   (MP_TAC o REWRITE_RULE[REAL_HOMEOMORPHISM]) THEN
  INTRO_TAC "hcontinuous hinto kcontinuous kinto _ _" THEN
  SUBGOAL_THEN
   `((h:real->real) o (f:real->real) o (k:real->real))
    real_continuous_on (t:real->bool)`
  (LABEL_TAC "conjugatecontinuous") THENL
   [REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [USE_THEN "kcontinuous" ACCEPT_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `s:real->bool` THEN CONJ_TAC THENL
         [USE_THEN "continuous" ACCEPT_TAC;
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `IMAGE (k:real->real) t` THEN
          REWRITE_TAC[SUBSET_REFL] THEN
          USE_THEN "kinto" ACCEPT_TAC];
        MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `s:real->bool` THEN CONJ_TAC THENL
         [USE_THEN "hcontinuous" ACCEPT_TAC;
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `IMAGE (f:real->real) s` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC IMAGE_SUBSET THEN
            MATCH_MP_TAC SUBSET_TRANS THEN
            EXISTS_TAC `IMAGE (k:real->real) t` THEN
            REWRITE_TAC[SUBSET_REFL] THEN
            USE_THEN "kinto" ACCEPT_TAC;
            USE_THEN "invariant" ACCEPT_TAC]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((h:real->real) o (f:real->real) o (k:real->real))
          (t:real->bool) SUBSET t`
  (LABEL_TAC "conjugateinvariant") THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `x:real` THEN DISCH_THEN(LABEL_TAC "inside") THEN
    SUBGOAL_THEN `(k:real->real) x IN s`
    (LABEL_TAC "kinside") THENL
     [USE_THEN "kinto"
       (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      USE_THEN "inside" ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real->real)((k:real->real) x) IN s`
    (LABEL_TAC "finside") THENL
     [USE_THEN "invariant"
       (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      USE_THEN "kinside" ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "hinto"
     (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    USE_THEN "finside" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `has_period_on
     ((h:real->real) o (f:real->real) o (k:real->real))
     m (t:real->bool)`
  (LABEL_TAC "conjugateperiod") THENL
   [MP_TAC(ISPECL
     [`f:real->real`; `h:real->real`; `k:real->real`;
      `s:real->bool`; `t:real->bool`; `m:num`]
     HAS_PERIOD_ON_CONJUGATE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `has_period_on
     ((h:real->real) o (f:real->real) o (k:real->real))
     n (t:real->bool)`
  (LABEL_TAC "conjugatetarget") THENL
   [MATCH_MP_TAC(ISPECL
     [`(h:real->real) o (f:real->real) o (k:real->real)`;
      `t:real->bool`;
      `m:num`; `n:num`]
     SARKOVSKII_THEOREM_CLOSED_REALINTERVAL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real->real`; `h:real->real`; `k:real->real`;
    `s:real->bool`; `t:real->bool`; `n:num`]
   HAS_PERIOD_ON_CONJUGATE) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Canonical homeomorphisms for the interval classification.                 *)
(* ------------------------------------------------------------------------- *)

let REAL_AFFINITY_HOMEOMORPHISM = prove
 (`!s c d.
        ~(c = &0)
        ==> homeomorphic_maps
             (subtopology euclideanreal s,
              subtopology euclideanreal
               (IMAGE (\x. c * x + d) s))
             ((\x. c * x + d),(\y. (y - d) / c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "nonzero") THEN
  REWRITE_TAC[REAL_HOMEOMORPHISM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    REWRITE_TAC[SUBSET_REFL];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_DIV THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real` THEN DISCH_THEN(LABEL_TAC "inside") THEN
    SUBGOAL_THEN
     `(((c:real) * (x:real) + (d:real)) - d) / c = x`
    SUBST1_TAC THENL
     [USE_THEN "nonzero" MP_TAC THEN CONV_TAC REAL_FIELD;
      USE_THEN "inside" ACCEPT_TAC];
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    USE_THEN "nonzero" MP_TAC THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    USE_THEN "nonzero" MP_TAC THEN
    CONV_TAC REAL_FIELD]);;

let REAL_EXP_HOMEOMORPHISM = prove
 (`homeomorphic_maps
    (subtopology euclideanreal (:real),
     subtopology euclideanreal {x | &0 < x})
    (exp,log)`,
  REWRITE_TAC[REAL_HOMEOMORPHISM] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EXP];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_EXP_POS_LT];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LOG THEN
    REWRITE_TAC[IN_ELIM_THM];
    REWRITE_TAC[SUBSET_UNIV];
    REWRITE_TAC[IN_UNIV; LOG_EXP];
    REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[EXP_LOG]]);;

let REAL_SHRINK_NONNEGATIVE_HOMEOMORPHISM = prove
 (`homeomorphic_maps
    (subtopology euclideanreal {x | &0 <= x},
     subtopology euclideanreal {x | &0 <= x /\ x < &1})
    ((\x. x / (&1 + abs x)),
     (\y. y / (&1 - abs y)))`,
  REWRITE_TAC[REAL_HOMEOMORPHISM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_DIV THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MP_TAC(ISPECL
       [`\x:real. x`; `{x:real | &0 <= x}`]
       REAL_CONTINUOUS_ON_ABS) THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX];
      REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN DISCH_THEN(LABEL_TAC "nonnegative") THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`&0`; `x:real`] REAL_SHRINK_LE) THEN
      ASM_REWRITE_TAC[REAL_ABS_NUM; real_div; REAL_MUL_LZERO];
      SUBGOAL_THEN `&0 <= x / (&1 + abs x)`
      (LABEL_TAC "shrinknonnegative") THENL
       [MP_TAC(SPECL [`&0`; `x:real`] REAL_SHRINK_LE) THEN
        ASM_REWRITE_TAC[REAL_ABS_NUM; real_div; REAL_MUL_LZERO];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `abs (x / (&1 + abs x)) = x / (&1 + abs x)`
      (LABEL_TAC "absshrink") THENL
       [REWRITE_TAC[REAL_ABS_REFL] THEN
        USE_THEN "shrinknonnegative" ACCEPT_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `x:real` REAL_SHRINK_RANGE) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_DIV THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MP_TAC(ISPECL
       [`\x:real. x`; `{x:real | &0 <= x /\ x < &1}`]
       REAL_CONTINUOUS_ON_ABS) THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX];
      REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `abs y = y` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs y = y` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[IN_ELIM_THM; REAL_GROW_SHRINK];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_SHRINK_GROW THEN
    SUBGOAL_THEN `abs y = y` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REWRITE_TAC[]]);;

let REAL_UNIT_OPEN_HOMEOMORPHIC_UNIV = prove
 (`?h k.
        homeomorphic_maps
         (subtopology euclideanreal {x | &0 < x /\ x < &1},
          subtopology euclideanreal (:real)) (h,k)`,
  MP_TAC(ISPECL
   [`{x:real | &0 < x /\ x < &1}`; `&2`; `-- &1`]
   REAL_AFFINITY_HOMEOMORPHISM) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `IMAGE (\x:real. &2 * x + -- &1)
          {x | &0 < x /\ x < &1} =
    real_interval(-- &1,&1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM;
                IN_REAL_INTERVAL] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN EXISTS_TAC `(y + &1) / &2` THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "affinity")] THEN
  SUBGOAL_THEN
   `homeomorphic_maps
     (subtopology euclideanreal (real_interval(-- &1,&1)),
      subtopology euclideanreal (:real))
     ((\y. y / (&1 - abs y)),
      (\x. x / (&1 + abs x)))`
  (LABEL_TAC "grow") THENL
   [MP_TAC HOMEOMORPHIC_MAPS_REAL_SHRINK THEN
    REWRITE_TAC[HOMEOMORPHIC_MAPS_SYM; SUBTOPOLOGY_UNIV];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(\y. y / (&1 - abs y)) o
     (\x:real. &2 * x + -- &1)`;
    `(\x. (x - -- &1) / &2) o
     (\y. y / (&1 + abs y))`] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAPS_COMPOSE THEN
  EXISTS_TAC
   `subtopology euclideanreal (real_interval(-- &1,&1))` THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "affinity" MATCH_MP_TAC THEN
  REAL_ARITH_TAC);;

let REAL_UNIT_HALFOPEN_HOMEOMORPHIC_NONNEGATIVE = prove
 (`homeomorphic_maps
    (subtopology euclideanreal {x | &0 <= x /\ x < &1},
     subtopology euclideanreal {x | &0 <= x})
    ((\y. y / (&1 - abs y)),
     (\x. x / (&1 + abs x)))`,
  MP_TAC REAL_SHRINK_NONNEGATIVE_HOMEOMORPHISM THEN
  MESON_TAC[HOMEOMORPHIC_MAPS_SYM]);;

let REAL_NORMALIZE_OPEN_INTERVAL = prove
 (`!a b.
        a < b
        ==> ?h k.
              homeomorphic_maps
               (subtopology euclideanreal
                 {x | a < x /\ x < b},
                subtopology euclideanreal
                 {y | &0 < y /\ y < &1}) (h,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{x:real | a < x /\ x < b}`;
    `inv((b:real) - (a:real))`;
    `--(inv((b:real) - (a:real)) * (a:real))`]
   REAL_AFFINITY_HOMEOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE
     (\x:real. inv(b - a) * x + --(inv(b - a) * a))
     {x | a < x /\ x < b} =
    {y | &0 < y /\ y < &1}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `inv((b:real) - (a:real)) * (x:real) +
        --(inv(b - a) * a) = (x - a) / (b - a)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (x:real) - (a:real)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (b:real) - (a:real)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN
      EXISTS_TAC `(a:real) + ((b:real) - a) * (y:real)` THEN
      CONJ_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
        CONJ_TAC THENL
         [SUBGOAL_THEN
           `&0 < ((b:real) - (a:real)) * (y:real)`
          MP_TAC THENL
           [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
            REAL_ARITH_TAC];
          SUBGOAL_THEN
           `((b:real) - (a:real)) * (y:real) < b - a`
          MP_TAC THENL
           [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
            REAL_ARITH_TAC]]]];
    MESON_TAC[]]);;

let REAL_NORMALIZE_RIGHT_OPEN_INTERVAL = prove
 (`!a b.
        a < b
        ==> ?h k.
              homeomorphic_maps
               (subtopology euclideanreal
                 {x | a <= x /\ x < b},
                subtopology euclideanreal
                 {y | &0 <= y /\ y < &1}) (h,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{x:real | a <= x /\ x < b}`;
    `inv((b:real) - (a:real))`;
    `--(inv((b:real) - (a:real)) * (a:real))`]
   REAL_AFFINITY_HOMEOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE
     (\x:real. inv(b - a) * x + --(inv(b - a) * a))
     {x | a <= x /\ x < b} =
    {y | &0 <= y /\ y < &1}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `inv((b:real) - (a:real)) * (x:real) +
        --(inv(b - a) * a) = (x - a) / (b - a)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (x:real) - (a:real)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (b:real) - (a:real)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (b:real) - (a:real)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN
      EXISTS_TAC `(a:real) + ((b:real) - a) * (y:real)` THEN
      CONJ_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
        CONJ_TAC THENL
         [SUBGOAL_THEN
           `&0 <= ((b:real) - (a:real)) * (y:real)`
          MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
            REAL_ARITH_TAC];
          SUBGOAL_THEN
           `((b:real) - (a:real)) * (y:real) < b - a`
          MP_TAC THENL
           [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
            REAL_ARITH_TAC]]]];
    MESON_TAC[]]);;

let REAL_NORMALIZE_LEFT_OPEN_INTERVAL = prove
 (`!a b.
        a < b
        ==> ?h k.
              homeomorphic_maps
               (subtopology euclideanreal
                 {x | a < x /\ x <= b},
                subtopology euclideanreal
                 {y | &0 <= y /\ y < &1}) (h,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{x:real | a < x /\ x <= b}`;
    `--inv((b:real) - (a:real))`;
    `inv((b:real) - (a:real)) * (b:real)`]
   REAL_AFFINITY_HOMEOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_NEG_EQ_0; REAL_INV_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE
     (\x:real. --inv(b - a) * x + inv(b - a) * b)
     {x | a < x /\ x <= b} =
    {y | &0 <= y /\ y < &1}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `--inv((b:real) - (a:real)) * (x:real) +
        inv(b - a) * b = (b - x) / (b - a)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (b:real) - (x:real)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (b:real) - (a:real)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (b:real) - (a:real)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN
      EXISTS_TAC `(b:real) - ((b:real) - a) * (y:real)` THEN
      CONJ_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
        CONJ_TAC THENL
         [SUBGOAL_THEN
           `((b:real) - (a:real)) * (y:real) < b - a`
          MP_TAC THENL
           [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
            REAL_ARITH_TAC];
          SUBGOAL_THEN
           `&0 <= ((b:real) - (a:real)) * (y:real)`
          MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
            REAL_ARITH_TAC]]]];
    MESON_TAC[]]);;

let REAL_OPEN_INTERVAL_HOMEOMORPHIC_UNIV = prove
 (`!a b.
        a < b
        ==> ?h k.
              homeomorphic_maps
               (subtopology euclideanreal
                 {x | a < x /\ x < b},
                subtopology euclideanreal (:real)) (h,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`]
   REAL_NORMALIZE_OPEN_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN
  INTRO_TAC "@h k. normalize" THEN
  MP_TAC REAL_UNIT_OPEN_HOMEOMORPHIC_UNIV THEN
  INTRO_TAC "@h' k'. canonical" THEN
  MAP_EVERY EXISTS_TAC
   [`(h':real->real) o (h:real->real)`;
    `(k:real->real) o (k':real->real)`] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAPS_COMPOSE THEN
  EXISTS_TAC
   `subtopology euclideanreal {x:real | &0 < x /\ x < &1}` THEN
  ASM_REWRITE_TAC[]);;

let REAL_RIGHT_OPEN_INTERVAL_HOMEOMORPHIC_NONNEGATIVE = prove
 (`!a b.
        a < b
        ==> ?h k.
              homeomorphic_maps
               (subtopology euclideanreal
                 {x | a <= x /\ x < b},
                subtopology euclideanreal {x | &0 <= x}) (h,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`]
   REAL_NORMALIZE_RIGHT_OPEN_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN
  INTRO_TAC "@h k. normalize" THEN
  MAP_EVERY EXISTS_TAC
   [`(\y. y / (&1 - abs y)) o (h:real->real)`;
    `(k:real->real) o (\x. x / (&1 + abs x))`] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAPS_COMPOSE THEN
  EXISTS_TAC
   `subtopology euclideanreal {x:real | &0 <= x /\ x < &1}` THEN
  ASM_REWRITE_TAC[REAL_UNIT_HALFOPEN_HOMEOMORPHIC_NONNEGATIVE]);;

let REAL_LEFT_OPEN_INTERVAL_HOMEOMORPHIC_NONNEGATIVE = prove
 (`!a b.
        a < b
        ==> ?h k.
              homeomorphic_maps
               (subtopology euclideanreal
                 {x | a < x /\ x <= b},
                subtopology euclideanreal {x | &0 <= x}) (h,k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`]
   REAL_NORMALIZE_LEFT_OPEN_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN
  INTRO_TAC "@h k. normalize" THEN
  MAP_EVERY EXISTS_TAC
   [`(\y. y / (&1 - abs y)) o (h:real->real)`;
    `(k:real->real) o (\x. x / (&1 + abs x))`] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAPS_COMPOSE THEN
  EXISTS_TAC
   `subtopology euclideanreal {x:real | &0 <= x /\ x < &1}` THEN
  ASM_REWRITE_TAC[REAL_UNIT_HALFOPEN_HOMEOMORPHIC_NONNEGATIVE]);;

let REAL_OPEN_UPPER_RAY_HOMEOMORPHIC_UNIV = prove
 (`!a.
        ?h k.
          homeomorphic_maps
           (subtopology euclideanreal {x | a < x},
            subtopology euclideanreal (:real)) (h,k)`,
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`{x:real | a < x}`; `&1`; `--(a:real)`]
   REAL_AFFINITY_HOMEOMORPHISM) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `IMAGE (\x:real. &1 * x + --a) {x | a < x} =
    {x | &0 < x}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      EXISTS_TAC `(y:real) + (a:real)` THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "affinity")] THEN
  SUBGOAL_THEN
   `homeomorphic_maps
     (subtopology euclideanreal {x:real | &0 < x},
      subtopology euclideanreal (:real)) (log,exp)`
  (LABEL_TAC "logarithm") THENL
   [MP_TAC REAL_EXP_HOMEOMORPHISM THEN
    MESON_TAC[HOMEOMORPHIC_MAPS_SYM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`log o (\x:real. &1 * x + --a)`;
    `(\y:real. (y - --(a:real)) / &1) o exp`] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAPS_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal {x:real | &0 < x}` THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "affinity" MATCH_MP_TAC THEN
  REAL_ARITH_TAC);;

let REAL_OPEN_LOWER_RAY_HOMEOMORPHIC_UNIV = prove
 (`!b.
        ?h k.
          homeomorphic_maps
           (subtopology euclideanreal {x | x < b},
            subtopology euclideanreal (:real)) (h,k)`,
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`{x:real | x < b}`; `-- &1`; `(b:real)`]
   REAL_AFFINITY_HOMEOMORPHISM) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `IMAGE (\x:real. -- &1 * x + b) {x | x < b} =
    {x | &0 < x}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      EXISTS_TAC `(b:real) - (y:real)` THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "affinity")] THEN
  SUBGOAL_THEN
   `homeomorphic_maps
     (subtopology euclideanreal {x:real | &0 < x},
      subtopology euclideanreal (:real)) (log,exp)`
  (LABEL_TAC "logarithm") THENL
   [MP_TAC REAL_EXP_HOMEOMORPHISM THEN
    MESON_TAC[HOMEOMORPHIC_MAPS_SYM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`log o (\x:real. -- &1 * x + b)`;
    `(\y:real. (y - (b:real)) / -- &1) o exp`] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAPS_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal {x:real | &0 < x}` THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "affinity" MATCH_MP_TAC THEN
  REAL_ARITH_TAC);;

let IS_REALINTERVAL_HOMEOMORPHIC_CLOSED = prove
 (`!s.
        is_realinterval s /\
        ~(s = {})
        ==> ?t h k.
              real_closed t /\
              is_realinterval t /\
              homeomorphic_maps
               (subtopology euclideanreal s,
                subtopology euclideanreal t) (h,k)`,
  GEN_TAC THEN
  INTRO_TAC "interval nonempty" THEN
  MP_TAC(SPEC `s:real->bool` IS_REAL_INTERVAL_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  INTRO_TAC
   ("univ | (@a. upperopen) | (@a. upperclosed) | " ^
    "(@b. lowerclosed) | (@b. loweropen) | (@a b. boundedopen) | " ^
    "(@a b. leftopen) | (@a b. rightopen) | " ^
    "(@a b. boundedclosed)") THENL
   [USE_THEN "univ" SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(:real)`; `I:real->real`; `I:real->real`] THEN
    REWRITE_TAC[REAL_CLOSED_UNIV; IS_REALINTERVAL_CLAUSES;
                HOMEOMORPHIC_MAPS_I];
    USE_THEN "upperopen" SUBST_ALL_TAC THEN
    MP_TAC(SPEC `a:real`
     REAL_OPEN_UPPER_RAY_HOMEOMORPHIC_UNIV) THEN
    INTRO_TAC "@h k. homeomorphism" THEN
    MAP_EVERY EXISTS_TAC
     [`(:real)`; `h:real->real`; `k:real->real`] THEN
    ASM_REWRITE_TAC[REAL_CLOSED_UNIV; IS_REALINTERVAL_CLAUSES];
    USE_THEN "upperclosed" SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`{x:real | a <= x}`; `I:real->real`; `I:real->real`] THEN
    REWRITE_TAC[GSYM real_ge; REAL_CLOSED_HALFSPACE_GE;
                IS_REALINTERVAL_CLAUSES;
                HOMEOMORPHIC_MAPS_I];
    USE_THEN "lowerclosed" SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`{x:real | x <= b}`; `I:real->real`; `I:real->real`] THEN
    REWRITE_TAC[REAL_CLOSED_HALFSPACE_LE; IS_REALINTERVAL_CLAUSES;
                HOMEOMORPHIC_MAPS_I];
    USE_THEN "loweropen" SUBST_ALL_TAC THEN
    MP_TAC(SPEC `b:real`
     REAL_OPEN_LOWER_RAY_HOMEOMORPHIC_UNIV) THEN
    INTRO_TAC "@h k. homeomorphism" THEN
    MAP_EVERY EXISTS_TAC
     [`(:real)`; `h:real->real`; `k:real->real`] THEN
    ASM_REWRITE_TAC[REAL_CLOSED_UNIV; IS_REALINTERVAL_CLAUSES];
    USE_THEN "boundedopen" SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(a:real) < b` (LABEL_TAC "ordered") THENL
     [ASM_CASES_TAC `(a:real) < b` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `{x:real | a < x /\ x < b} = {}`
      (fun th -> USE_THEN "nonempty"
       (fun nth -> CONTR_TAC(MP (NOT_ELIM nth) th))) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `b:real`]
     REAL_OPEN_INTERVAL_HOMEOMORPHIC_UNIV) THEN
    ASM_REWRITE_TAC[] THEN
    INTRO_TAC "@h k. homeomorphism" THEN
    MAP_EVERY EXISTS_TAC
     [`(:real)`; `h:real->real`; `k:real->real`] THEN
    ASM_REWRITE_TAC[REAL_CLOSED_UNIV; IS_REALINTERVAL_CLAUSES];
    USE_THEN "leftopen" SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(a:real) < b` (LABEL_TAC "ordered") THENL
     [ASM_CASES_TAC `(a:real) < b` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `{x:real | a < x /\ x <= b} = {}`
      (fun th -> USE_THEN "nonempty"
       (fun nth -> CONTR_TAC(MP (NOT_ELIM nth) th))) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `b:real`]
     REAL_LEFT_OPEN_INTERVAL_HOMEOMORPHIC_NONNEGATIVE) THEN
    ASM_REWRITE_TAC[] THEN
    INTRO_TAC "@h k. homeomorphism" THEN
    MAP_EVERY EXISTS_TAC
     [`{x:real | &0 <= x}`; `h:real->real`; `k:real->real`] THEN
    ASM_REWRITE_TAC[GSYM real_ge; REAL_CLOSED_HALFSPACE_GE;
                    IS_REALINTERVAL_CLAUSES];
    USE_THEN "rightopen" SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(a:real) < b` (LABEL_TAC "ordered") THENL
     [ASM_CASES_TAC `(a:real) < b` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `{x:real | a <= x /\ x < b} = {}`
      (fun th -> USE_THEN "nonempty"
       (fun nth -> CONTR_TAC(MP (NOT_ELIM nth) th))) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `b:real`]
     REAL_RIGHT_OPEN_INTERVAL_HOMEOMORPHIC_NONNEGATIVE) THEN
    ASM_REWRITE_TAC[] THEN
    INTRO_TAC "@h k. homeomorphism" THEN
    MAP_EVERY EXISTS_TAC
     [`{x:real | &0 <= x}`; `h:real->real`; `k:real->real`] THEN
    ASM_REWRITE_TAC[GSYM real_ge; REAL_CLOSED_HALFSPACE_GE;
                    IS_REALINTERVAL_CLAUSES];
    USE_THEN "boundedclosed" SUBST_ALL_TAC THEN
    SUBGOAL_THEN
     `{x:real | a <= x /\ x <= b} = real_interval[a,b]`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_REAL_INTERVAL];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`real_interval[a,b]`; `I:real->real`; `I:real->real`] THEN
    REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL; IS_REALINTERVAL_CLAUSES;
                HOMEOMORPHIC_MAPS_I; IS_REALINTERVAL_INTERVAL]]);;

let SARKOVSKII_THEOREM_ON_REALINTERVAL = prove
 (`!f s m n.
        is_realinterval s /\
        f real_continuous_on s /\
        IMAGE f s SUBSET s /\
        (m = n \/ sarkovskii_precedes m n) /\
        has_period_on f m s
        ==> has_period_on f n s`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "interval continuous invariant order period" THEN
  SUBGOAL_THEN `~(s:real->bool = {})`
  (LABEL_TAC "nonempty") THENL
   [USE_THEN "period" MP_TAC THEN
    REWRITE_TAC[has_period_on] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `s:real->bool`
   IS_REALINTERVAL_HOMEOMORPHIC_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  INTRO_TAC "@t h k. closed targetinterval homeomorphism" THEN
  MATCH_MP_TAC(ISPECL
   [`f:real->real`; `s:real->bool`; `t:real->bool`;
    `h:real->real`; `k:real->real`; `m:num`; `n:num`]
   SARKOVSKII_THEOREM_HOMEOMORPHIC_CLOSED) THEN
  ASM_REWRITE_TAC[]);;

let PERIOD_3_IMP_ALL_PERIODS_ON_REALINTERVAL = prove
 (`!f s n.
        is_realinterval s /\
        f real_continuous_on s /\
        IMAGE f s SUBSET s /\
        0 < n /\
        has_period_on f 3 s
        ==> has_period_on f n s`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "interval continuous invariant positive period" THEN
  MATCH_MP_TAC(ISPECL
   [`f:real->real`; `s:real->bool`; `3`; `n:num`]
   SARKOVSKII_THEOREM_ON_REALINTERVAL) THEN
  ASM_SIMP_TAC[SARKOVSKII_3_PRECEDES] THEN
  ARITH_TAC);;
