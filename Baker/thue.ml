(* ========================================================================= *)
(* The Thue theorem via BAKER_FELDMAN (Baker, Transcendental Number Theory,  *)
(* Ch. 4; Thue 1909).                                                        *)
(*                                                                           *)
(* Purpose: F(x,y) = sum_i a_i x^(n-i) y^i with integer coefficients,        *)
(* n >= 3, every root of F(t,1) of degree n (F irreducible over Q): F(x,y)   *)
(* = m has only finitely many integer solutions. Route: monic reduction      *)
(* G(X,y) = a_0^(n-1) F(X / a_0, y) = prod_k (X - r_k y) with nf_data for    *)
(* G(X,1); beta_k = X - r_k y in the order Z[theta] with norm                *)
(* a_0^(n-1) m; NF_NORM_EQ_DECOMPOSITION; size estimates of the conjugates;  *)
(* the Siegel identity for three distinct conjugates; the linear form        *)
(* clog(1 + E) in finitely many fixed logarithms; BAKER_FELDMAN bounds |y|.  *)
(*                                                                           *)
(* Main results: THUE, THUE_CUBIC_2 (x^3 - 2 y^3 = m); BAKER_FELDMAN_INTEGER *)
(* (BAKER_FELDMAN with integer coefficients for a family of logarithms       *)
(* indexed by a finite set), BAKER_FELDMAN_INTEGER_FAMILIES (the same        *)
(* uniformly for finitely many families) and BAKER_ONE_PLUS_E (the closing   *)
(* step: a lower bound for |E| when 1 + E is a fixed algebraic number times  *)
(* a product of powers of fixed algebraic numbers; used also by              *)
(* Baker/uniteq.ml, as is NF_ORDER_ALGEBRAIC).                               *)
(*                                                                           *)
(* Uses: Baker/theorem.ml (BAKER_FELDMAN), Baker/lemmas.ml                   *)
(* (VSUM_DEGREE_1_ROOT, POLYLOG_BOUND, CLOG_ONE_PLUS_NZ,                     *)
(* CLOG_ONE_PLUS_SMALL, CLOG_MUL_CPRODUCT_POW and other real lemmas),        *)
(* Baker/bridge.ml (ALGEBRAIC_NUMBER_MUL, ALGEBRAIC_NUMBER_DIV),             *)
(* Baker/algebraic.ml (COMPLEX_POLYFUN_FACTOR), Baker/algint.ml              *)
(* (ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER), Baker/nf_defs.ml (nf_data,      *)
(* nf_unit), Baker/nf_order.ml (NF_CUBE2_DEGREE), Baker/nf_units.ml          *)
(* (NF_NORM_EQ_DECOMPOSITION).                                               *)
(* ========================================================================= *)

needs "Baker/theorem.ml";;
needs "Baker/nf_units.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* BAKER_FELDMAN for integer coefficients: a finite family of logarithms     *)
(* indexed by an arbitrary finite set plus two extra logarithms, and then    *)
(* uniformly for finitely many such families.                                *)
(* ------------------------------------------------------------------------- *)

let THUE_VSUM_NUMSEG_ADD2 = prove
 (`!(g:num->complex) N.
        vsum(1..N + 2) g = vsum(1..N) g + g(N + 1) + g(N + 2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`g:num->complex`; `1`; `N + 2`] VSUM_CLAUSES_RIGHT) THEN
  MP_TAC(ISPECL [`g:num->complex`; `1`; `N + 1`] VSUM_CLAUSES_RIGHT) THEN
  REWRITE_TAC[ARITH_RULE `0 < N + 2 /\ 1 <= N + 2 /\ 0 < N + 1 /\
                          1 <= N + 1 /\ (N + 2) - 1 = N + 1 /\
                          (N + 1) - 1 = N`] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[COMPLEX_ADD_AC]);;

let THUE_VSUM_IMAGE_NUMSEG = prove
 (`!(f:num->A) N.
        (!i j. i IN 1..N /\ j IN 1..N /\ f i = f j ==> i = j)
        ==> !h:A->complex. vsum (IMAGE f (1..N)) h = vsum(1..N) (\r. h(f r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->A`; `h:A->complex`; `1..N`] VSUM_IMAGE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; o_DEF]);;

let BAKER_FELDMAN_INTEGER = prove
 (`!(s:A->bool) (lg:A->complex) L1 L2.
     FINITE s /\
     (!x. x IN s ==> algebraic_number(cexp(lg x))) /\
     algebraic_number(cexp L1) /\ algebraic_number(cexp L2)
     ==> ?C. !B t1 t2 (t:A->real).
           &2 <= B /\ integer t1 /\ abs t1 <= B /\
           integer t2 /\ abs t2 <= B /\
           (!x. x IN s ==> integer(t x) /\ abs(t x) <= B) /\
           ~(Cx t1 * L1 + Cx t2 * L2 + vsum s (\x. Cx(t x) * lg x) = Cx(&0))
           ==> inv(B pow C) <=
               norm(Cx t1 * L1 + Cx t2 * L2 + vsum s (\x. Cx(t x) * lg x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `N = CARD(s:A->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP THUE_VSUM_IMAGE_NUMSEG th]) THEN
  BETA_TAC THEN
  MP_TAC(ISPECL
   [`N + 2`;
    `\r. if r = N + 1 then L1 else if r = N + 2 then L2
         else (lg:A->complex)((f:num->A) r)`;
    `1`] BAKER_FELDMAN) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `r:num` THEN BETA_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
    DISCH_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `C:num`)] THEN
  EXISTS_TAC `C:num` THEN
  MAP_EVERY X_GEN_TAC [`B:real`; `t1:real`; `t2:real`; `t:A->real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `co = \r. if r = 0 then &0 else if r = N + 1 then t1
             else if r = N + 2 then t2 else (t:A->real)((f:num->A) r)` THEN
  SUBGOAL_THEN `!j. j <= N + 2 ==> integer((co:num->real) j) /\ abs(co j) <= B`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "co" THEN
    REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM] THEN
    TRY(ASM_REAL_ARITH_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx((co:num->real) 0) +
    vsum(1..N + 2)
     (\r. Cx(co r) *
          (if r = N + 1 then L1 else if r = N + 2 then L2
           else (lg:A->complex)((f:num->A) r))) =
    Cx t1 * L1 + Cx t2 * L2 + vsum(1..N) (\r. Cx((t:A->real)(f r)) * lg(f r))`
  ASSUME_TAC THENL
   [REWRITE_TAC[THUE_VSUM_NUMSEG_ADD2] THEN BETA_TAC THEN
    EXPAND_TAC "co" THEN
    REWRITE_TAC[ARITH_RULE `~(N + 1 = 0) /\ ~(N + 2 = 0) /\
                            ~(N + 2 = N + 1)`] THEN
    REWRITE_TAC[COMPLEX_ADD_LID] THEN
    SUBGOAL_THEN
     `vsum(1..N)
       (\r. Cx(if r = 0 then &0 else if r = N + 1 then t1
               else if r = N + 2 then t2 else (t:A->real)((f:num->A) r)) *
            (if r = N + 1 then L1 else if r = N + 2 then L2
             else (lg:A->complex)(f r))) =
      vsum(1..N) (\r. Cx(t(f r)) * lg(f r))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN
      STRIP_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `~(r = 0) /\ ~(r = N + 1) /\ ~(r = N + 2)`
       (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[COMPLEX_ADD_AC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`B:real`; `\r. Cx((co:num->real) r)`; `\j:num. 1`;
    `\j i. if i = 0 then --((co:num->real) j)
           else if i = 1 then &1 else &0`]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[LE_REFL; VSUM_DEGREE_1_ROOT; ARITH_EQ; REAL_OF_NUM_EQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
  SUBGOAL_THEN `integer((co:num->real) j) /\ abs(co j) <= B`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NEG; REAL_ABS_NUM] THEN
  ASM_REAL_ARITH_TAC);;

let BAKER_FELDMAN_INTEGER_FAMILIES = prove
 (`!(U:B->bool) (s:A->bool) (lg:B->A->complex) L1 L2.
     FINITE U /\ FINITE s /\
     (!u. u IN U
          ==> algebraic_number(cexp(L1 u)) /\ algebraic_number(cexp(L2 u)) /\
              !x. x IN s ==> algebraic_number(cexp(lg u x)))
     ==> ?C. !u B t1 t2 (t:A->real).
           u IN U /\ &2 <= B /\ integer t1 /\ abs t1 <= B /\
           integer t2 /\ abs t2 <= B /\
           (!x. x IN s ==> integer(t x) /\ abs(t x) <= B) /\
           ~(Cx t1 * L1 u + Cx t2 * L2 u + vsum s (\x. Cx(t x) * lg u x) =
             Cx(&0))
           ==> inv(B pow C) <=
               norm(Cx t1 * L1 u + Cx t2 * L2 u +
                    vsum s (\x. Cx(t x) * lg u x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u:B. ?C. u IN U
              ==> !B t1 t2 (t:A->real).
                    &2 <= B /\ integer t1 /\ abs t1 <= B /\
                    integer t2 /\ abs t2 <= B /\
                    (!x. x IN s ==> integer(t x) /\ abs(t x) <= B) /\
                    ~(Cx t1 * L1 u + Cx t2 * L2 u +
                      vsum s (\x. Cx(t x) * lg u x) = Cx(&0))
                    ==> inv(B pow C) <=
                        norm(Cx t1 * L1 u + Cx t2 * L2 u +
                             vsum s (\x. Cx(t x) * lg u x))`
  MP_TAC THENL
   [X_GEN_TAC `u:B` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC BAKER_FELDMAN_INTEGER THEN ASM_MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `Cf:B->num` (LABEL_TAC "cf"))] THEN
  MP_TAC(ISPECL [`Cf:B->num`; `U:B->bool`] UPPER_BOUND_FINITE_SET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:num` (LABEL_TAC "cb")) THEN
  EXISTS_TAC `C:num` THEN
  MAP_EVERY X_GEN_TAC [`u:B`; `B:real`; `t1:real`; `t2:real`; `t:A->real`] THEN
  STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `inv(B pow ((Cf:B->num) u))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; REMOVE_THEN "cb" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    REMOVE_THEN "cf" (MP_TAC o SPEC `u:B`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The closing step of a Baker application: if 1 + E = alpha u times a       *)
(* product of powers w u s ^ mm s (finitely many non-zero algebraic alpha u  *)
(* and w u s) and 0 < |E| <= 1/2, then 2 |E| >= (2 + sum mm)^-C. The linear  *)
(* form is clog(1 + E) in clog(alpha u), clog(w u s) and 2 pi ii.            *)
(* ------------------------------------------------------------------------- *)

let BAKER_ONE_PLUS_E = prove
 (`!(U:B->bool) (S:A->bool) (w:B->A->complex) (alpha:B->complex).
     FINITE U /\ FINITE S /\
     (!u. u IN U
          ==> algebraic_number(alpha u) /\ ~(alpha u = Cx(&0)) /\
              !s. s IN S ==> algebraic_number(w u s) /\ ~(w u s = Cx(&0)))
     ==> ?C. !u (mm:A->num) E.
               u IN U /\ ~(E = Cx(&0)) /\ norm E <= &1 / &2 /\
               Cx(&1) + E = alpha u * cproduct S (\s. w u s pow mm s)
               ==> inv((&2 + &(nsum S mm)) pow C) <= &2 * norm E`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:B->bool`; `S:A->bool`;
                 `\u s. clog((w:B->A->complex) u s)`;
                 `\u. clog((alpha:B->complex) u)`;
                 `\u:B. Cx(&2 * pi) * ii`] BAKER_FELDMAN_INTEGER_FAMILIES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CEXP_2PI_II; ALGEBRAIC_NUMBER_CX_NUM] THEN
    ASM_SIMP_TAC[CEXP_CLOG];
    DISCH_THEN(X_CHOOSE_THEN `C:num` (LABEL_TAC "baker"))] THEN
  EXISTS_TAC `C:num` THEN
  MAP_EVERY X_GEN_TAC [`u:B`; `mm:A->num`; `E:complex`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:A->bool`; `(w:B->A->complex) u`; `mm:A->num`;
                 `(alpha:B->complex) u`; `Cx(&1) + E`]
    CLOG_MUL_CPRODUCT_POW) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPLEX_ONE_PLUS_NZ]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lam")))) THEN
  REMOVE_THEN "baker" (MP_TAC o SPECL
   [`u:B`; `&2 + &(nsum S (mm:A->num))`; `&1`; `t0:real`;
    `\s:A. &((mm:A->num) s)`]) THEN
  REWRITE_TAC[] THEN
  REMOVE_THEN "lam" (fun th -> REWRITE_TAC[GSYM th]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM] THEN
    ASSUME_TAC(SPEC `nsum S (mm:A->num)` REAL_POS) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(ASM_REAL_ARITH_TAC) THENL
     [X_GEN_TAC `s:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `(x:real) <= y ==> x <= &2 + y`) THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN
      MP_TAC(ISPECL [`mm:A->num`; `nsum S (mm:A->num)`; `S:A->bool`]
        NSUM_POS_BOUND) THEN
      ASM_SIMP_TAC[LE_REFL];
      MATCH_MP_TAC CLOG_ONE_PLUS_NZ THEN ASM_REWRITE_TAC[]];
    MP_TAC(SPEC `E:complex` CLOG_ONE_PLUS_SMALL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Monic reduction. F(t,1) = a_0 prod_k (t - t_k); the monic polynomial      *)
(* G(X,1) = a_0^(n-1) F(X / a_0, 1) has integer coefficients and the roots   *)
(* a_0 t_k, again all of degree n; a_0^(n-1) F(x,y) = prod_k (a_0 x - a_0    *)
(* t_k y).                                                                   *)
(* ------------------------------------------------------------------------- *)

let THUE_VSUM_REFLECT = prove
 (`!n (a:num->real) w.
        vsum(0..n) (\i. Cx(a i) * w pow (n - i)) =
        vsum(0..n) (\i. Cx(a(n - i)) * w pow i)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [VSUM_REFLECT] THEN
  REWRITE_TAC[LT; SUB_0] THEN BETA_TAC THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i <= n ==> n - (n - i) = i`]);;

let THUE_FORM_FACTOR = prove
 (`!n (a:num->real).
        ~(a 0 = &0)
        ==> ?t. !w. vsum(0..n) (\i. Cx(a i) * w pow (n - i)) =
                    Cx(a 0) * cproduct(1..n) (\k. w - t k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `\j. Cx((a:num->real)(n - j))`]
    COMPLEX_POLYFUN_FACTOR) THEN
  BETA_TAC THEN REWRITE_TAC[SUB_REFL; CX_INJ] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:num->complex` THEN
  DISCH_TAC THEN X_GEN_TAC `w:complex` THEN
  ASM_REWRITE_TAC[THUE_VSUM_REFLECT]);;

let THUE_COMPLEX_POW_PRED = prove
 (`!(x:complex) n. 1 <= n ==> x pow n = x pow (n - 1) * x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = SUC(n - 1)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[complex_pow; COMPLEX_MUL_SYM]]);;

let THUE_MONIC_FACTOR = prove
 (`!n (a:num->real) t.
     1 <= n /\ ~(a 0 = &0) /\
     (!w. vsum(0..n) (\i. Cx(a i) * w pow (n - i)) =
          Cx(a 0) * cproduct(1..n) (\k. w - t k))
     ==> !z. vsum(0..n)
              (\i. Cx(if i = n then &1 else a(n - i) * a 0 pow (n - i - 1)) *
                   z pow i) =
             cproduct(1..n) (\k. z - Cx(a 0) * t k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "fac"))) THEN
  SUBGOAL_THEN `~(Cx((a:num->real) 0) = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CX_INJ]; ALL_TAC] THEN
  MP_TAC(SPECL [`Cx((a:num->real) 0)`; `n:num`] THUE_COMPLEX_POW_PRED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w. vsum(0..n)
         (\i. Cx(if i = n then &1
                 else (a:num->real)(n - i) * a 0 pow (n - i - 1)) *
              (Cx(a 0) * w) pow i) =
        cproduct(1..n) (\k. Cx(a 0) * w - Cx(a 0) * t k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:complex` THEN
    SUBGOAL_THEN
     `cproduct(1..n) (\k. Cx((a:num->real) 0) * w - Cx(a 0) * t k) =
      Cx(a 0) pow (n - 1) * vsum(0..n) (\i. Cx(a(n - i)) * w pow i)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `cproduct(1..n) (\k. Cx((a:num->real) 0) * w - Cx(a 0) * t k) =
        cproduct(1..n) (\k. Cx(a 0) * (w - t k))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC CPRODUCT_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
        CONV_TAC COMPLEX_RING;
        ALL_TAC] THEN
      SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG; CPRODUCT_CONST_NUMSEG;
               ADD_SUB] THEN
      REWRITE_TAC[GSYM THUE_VSUM_REFLECT] THEN
      USE_THEN "fac" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC[SUB_REFL; COMPLEX_POW_MUL; COMPLEX_MUL_LID] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `Cx((a:num->real) 0) pow (n - i - 1) * Cx(a 0) pow i =
      Cx(a 0) pow (n - 1)`
    MP_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CX_MUL; CX_POW; COMPLEX_POW_MUL] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z / Cx((a:num->real) 0)`) THEN
  SUBGOAL_THEN `Cx((a:num->real) 0) * z / Cx(a 0) = z` SUBST1_TAC THENL
   [UNDISCH_TAC `~(Cx((a:num->real) 0) = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[]]);;

let THUE_MONIC_ROOT_DEGREE = prove
 (`!n (a:num->real) t.
     (!i. integer(a i)) /\ ~(a 0 = &0) /\
     (!w. vsum(0..n) (\i. Cx(a i) * w pow (n - i)) =
          Cx(a 0) * cproduct(1..n) (\k. w - t k)) /\
     (!w. vsum(0..n) (\i. Cx(a i) * w pow (n - i)) = Cx(&0)
          ==> !d b. d < n /\ (!i. integer(b i)) /\
                    vsum(0..d) (\i. Cx(b i) * w pow i) = Cx(&0)
                    ==> !i. i <= d ==> b i = &0)
     ==> !k m b. k IN 1..n /\ m < n /\ (!i. integer(b i)) /\
                 vsum(0..m) (\i. Cx(b i) * (Cx(a 0) * t k) pow i) = Cx(&0)
                 ==> !i. i <= m ==> b i = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "fac") (LABEL_TAC "deg")))) THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `m:num`; `b:num->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "van")))) THEN
  REMOVE_THEN "deg" (MP_TAC o SPEC `(t:num->complex) k`) THEN
  ANTS_TAC THENL
   [USE_THEN "fac" (fun th -> REWRITE_TAC[th; COMPLEX_ENTIRE]) THEN
    DISJ2_TAC THEN SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[COMPLEX_SUB_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`m:num`; `\i. (b:num->real) i * (a:num->real) 0 pow i`]) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    REMOVE_THEN "van" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[CX_MUL; CX_POW; COMPLEX_POW_MUL; COMPLEX_MUL_AC];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0]);;

let THUE_MONIC_NF_DATA = prove
 (`!n (a:num->real) t.
     1 <= n /\ (!i. integer(a i)) /\ ~(a 0 = &0) /\
     (!w. vsum(0..n) (\i. Cx(a i) * w pow (n - i)) =
          Cx(a 0) * cproduct(1..n) (\k. w - t k)) /\
     (!w. vsum(0..n) (\i. Cx(a i) * w pow (n - i)) = Cx(&0)
          ==> !d b. d < n /\ (!i. integer(b i)) /\
                    vsum(0..d) (\i. Cx(b i) * w pow i) = Cx(&0)
                    ==> !i. i <= d ==> b i = &0)
     ==> nf_data n (\j. if j = n then &1 else a(n - j) * a 0 pow (n - j - 1))
                   (\k. Cx(a 0) * t k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[nf_data] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN COND_CASES_TAC THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN MATCH_MP_TAC INTEGER_MUL THEN
    CONJ_TAC THEN TRY(MATCH_MP_TAC INTEGER_POW) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC THUE_MONIC_FACTOR THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC THUE_MONIC_ROOT_DEGREE THEN ASM_REWRITE_TAC[]]);;

let THUE_FORM_HOMOG = prove
 (`!n (a:num->real) t x y.
     1 <= n /\
     (!w. vsum(0..n) (\i. Cx(a i) * w pow (n - i)) =
          Cx(a 0) * cproduct(1..n) (\k. w - t k))
     ==> Cx(a 0 pow (n - 1) * sum(0..n) (\i. a i * x pow (n - i) * y pow i)) =
         cproduct(1..n) (\k. Cx(a 0 * x) - Cx y * Cx(a 0) * t k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fac")) THEN
  ASM_CASES_TAC `y = &0` THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_SUB_RZERO;
                    CPRODUCT_CONST_NUMSEG; ADD_SUB] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
    SUBGOAL_THEN
     `sum(1..n) (\i. (a:num->real) i * x pow (n - i) * &0 pow i) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_POW_ZERO; ARITH_RULE `1 <= i ==> ~(i = 0)`;
                   REAL_MUL_RZERO];
      ALL_TAC] THEN
    REWRITE_TAC[real_pow; SUB_0; REAL_MUL_RID; REAL_ADD_RID] THEN
    REWRITE_TAC[GSYM CX_POW; CX_INJ; REAL_POW_MUL] THEN
    ASM_SIMP_TAC[REAL_POW_PRED] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cproduct(1..n) (\k. Cx((a:num->real) 0 * x) - Cx y * Cx(a 0) * t k) =
    (Cx y * Cx(a 0)) pow n * cproduct(1..n) (\k. Cx(x / y) - t k)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `cproduct(1..n) (\k. Cx((a:num->real) 0 * x) - Cx y * Cx(a 0) * t k) =
      cproduct(1..n) (\k. (Cx y * Cx(a 0)) * (Cx(x / y) - t k))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      BETA_TAC THEN REWRITE_TAC[CX_MUL; CX_DIV] THEN
      UNDISCH_TAC `~(y = &0)` THEN REWRITE_TAC[GSYM CX_INJ] THEN
      CONV_TAC COMPLEX_FIELD;
      SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG; CPRODUCT_CONST_NUMSEG; ADD_SUB]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(sum(0..n) (\i. (a:num->real) i * (x / y) pow (n - i))) =
    Cx(a 0) * cproduct(1..n) (\k. Cx(x / y) - t k)`
  ASSUME_TAC THENL
   [REMOVE_THEN "fac" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[GSYM VSUM_CX; CX_MUL; CX_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..n) (\i. (a:num->real) i * x pow (n - i) * y pow i) =
    y pow n * sum(0..n) (\i. a i * (x / y) pow (n - i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `y pow n = y pow (n - i) * y pow i` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `~(y pow (n - i) = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_EQ_0]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[CX_MUL] THEN ONCE_REWRITE_TAC[CX_MUL] THEN
  ASM_REWRITE_TAC[CX_POW; COMPLEX_POW_MUL] THEN
  ASM_SIMP_TAC[THUE_COMPLEX_POW_PRED] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Size estimates for the conjugates beta_k = X - y r_k of a solution.       *)
(* ------------------------------------------------------------------------- *)

let THUE_ROOT_CONSTANTS = prove
 (`!n c r. nf_data n c r
           ==> ?R delta. &1 <= R /\ &0 < delta /\
                         (!k. k IN 1..n ==> norm(r k) <= R) /\
                         (!j k. j IN 1..n /\ k IN 1..n /\ ~(j = k)
                                ==> delta <= norm(r j - r k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k. norm((r:num->complex) k)`; `1..n`]
    UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(X_CHOOSE_TAC `R0:real`) THEN
  MP_TAC(ISPECL
   [`\p:num#num. inv(norm((r:num->complex)(FST p) - r(SND p)))`;
    `{p:num#num | FST p IN 1..n /\ SND p IN 1..n /\ ~(FST p = SND p)}`]
    UPPER_BOUND_FINITE_SET_REAL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(1..n) CROSS (1..n)` THEN
    SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS] THEN
    SIMP_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `D:real`)] THEN
  MAP_EVERY EXISTS_TAC [`max (&1) R0`; `inv(max (&1) D)`] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_ARITH `(x:real) <= R0 ==> x <= max (&1) R0`];
    MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm((r:num->complex) j - r k)` ASSUME_TAC THENL
     [REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
      ASM_MESON_TAC[NF_DATA_ROOTS_DISTINCT];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `k:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV] THEN
    ASM_REAL_ARITH_TAC]);;

let THUE_THREE_INDICES = prove
 (`!n i. 3 <= n /\ i IN 1..n
         ==> ?j k. j IN 1..n /\ k IN 1..n /\
                   ~(i = j) /\ ~(i = k) /\ ~(j = k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
  ASM_CASES_TAC `i = 1` THENL
   [MAP_EVERY EXISTS_TAC [`2`; `3`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i = 2` THENL
   [MAP_EVERY EXISTS_TAC [`1`; `3`] THEN ASM_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`1`; `2`] THEN ASM_ARITH_TAC]);;

let THUE_PRODUCT_OTHERS_LE = prove
 (`!s (f:A->real) a U.
        FINITE s /\ a IN s /\
        (!x. x IN s /\ ~(x = a) ==> &0 <= f x /\ f x <= U)
        ==> product(s DELETE a) f <= U pow (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `product(s DELETE (a:A)) (\x. U)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
    ASM_SIMP_TAC[PRODUCT_CONST; FINITE_DELETE; CARD_DELETE; REAL_LE_REFL]]);;

let THUE_PRODUCT_OTHERS_GE = prove
 (`!s (f:A->real) a D.
        FINITE s /\ a IN s /\ &0 <= D /\
        (!x. x IN s /\ ~(x = a) ==> D <= f x)
        ==> D pow (CARD s - 1) <= product(s DELETE a) f`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `product(s DELETE (a:A)) (\x. D)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[PRODUCT_CONST; FINITE_DELETE; CARD_DELETE; REAL_LE_REFL];
    MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

let THUE_NORM_PRODUCT = prove
 (`!n (beta:num->complex) M.
        cproduct(1..n) beta = Cx M
        ==> product(1..n) (\k. norm(beta k)) = abs M`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM NORM_CPRODUCT; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[ETA_AX; COMPLEX_NORM_CX]);;

let THUE_MIN_LE_NORM = prove
 (`!n (f:num->real) i M.
        1 <= n /\ i IN 1..n /\ &1 <= M /\
        (!k. k IN 1..n ==> &0 <= f k /\ f i <= f k) /\
        product(1..n) f = M
        ==> f i <= M`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(f:num->real) i <= &1` THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(f:num->real) i pow n` THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM PRODUCT_CONST_NUMSEG_1] THEN
    MATCH_MP_TAC PRODUCT_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    BETA_TAC THEN ASM_MESON_TAC[]]);;

let THUE_PRODUCT_SPLIT = prove
 (`!n (f:num->real) i.
        i IN 1..n ==> product(1..n) f = f i * product((1..n) DELETE i) f`,
  SIMP_TAC[PRODUCT_DELETE; FINITE_NUMSEG]);;

let THUE_OTHERS_LARGE = prove
 (`!X y (ri:complex) rj delta.
        delta <= norm(ri - rj) /\
        norm(Cx X - Cx y * ri) <= norm(Cx X - Cx y * rj)
        ==> delta * abs y / &2 <= norm(Cx X - Cx y * rj)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `abs y * norm(ri - rj:complex) <= &2 * norm(Cx X - Cx y * rj)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `abs y * norm(ri - rj:complex) =
      norm((Cx X - Cx y * rj) - (Cx X - Cx y * ri))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_NORM_CX; GSYM COMPLEX_NORM_MUL] THEN
      AP_TERM_TAC THEN CONV_TAC COMPLEX_RING;
      MATCH_MP_TAC(NORM_ARITH
       `!b c:complex. norm b <= norm c ==> norm(c - b) <= &2 * norm c`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`delta:real`; `norm(ri - rj:complex)`; `abs y`]
    REAL_LE_RMUL) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC);;

let THUE_CONJ_UPPER = prove
 (`!X y (ri:complex) rl R M.
        norm(Cx X - Cx y * ri) <= abs M /\ norm ri <= R /\ norm rl <= R
        ==> norm(Cx X - Cx y * rl) <= abs M + &2 * R * abs y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx X - Cx y * rl = (Cx X - Cx y * ri) + Cx y * (ri - rl)`
  SUBST1_TAC THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b:complex p q. norm a <= p /\ norm b <= q ==> norm(a + b) <= p + q`) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `norm(ri - rl:complex) <= &2 * R` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`norm(ri:complex) <= R`; `norm(rl:complex) <= R`] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MP_TAC(SPECL [`abs y`; `norm(ri - rl:complex)`; `&2 * R`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC);;

let THUE_X_UPPER = prove
 (`!X y (ri:complex) R M.
        norm(Cx X - Cx y * ri) <= abs M /\ norm ri <= R
        ==> abs X <= abs M + R * abs y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs X = norm((Cx X - Cx y * ri) + Cx y * ri)` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_RING `(a - b) + b:complex = a`; COMPLEX_NORM_CX];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!a b:complex p q. norm a <= p /\ norm b <= q ==> norm(a + b) <= p + q`) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  MP_TAC(SPECL [`abs y`; `norm(ri:complex)`; `R:real`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC);;

let THUE_LOG_ABS_LE = prove
 (`!x K m. &0 < x /\ x <= K /\ &1 <= K /\ 1 <= m /\ &1 <= x * K pow m
           ==> abs(log x) <= &m * log K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log K /\ log x <= log K` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log x + &m * log K` ASSUME_TAC THENL
   [SUBGOAL_THEN `log x + &m * log K = log(x * K pow m)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT];
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log K <= &m * log K` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let THUE_E_BOUND = prove
 (`!ee p q u v R delta yy Mabs n.
        ee * (p * u) = q * v /\ &0 <= ee /\ &0 <= p /\ &0 <= u /\ &0 <= v /\
        q <= &2 * R /\ delta <= p /\ delta * yy / &2 <= u /\
        v * (delta * yy / &2) pow (n - 1) <= Mabs /\
        &0 < delta /\ &0 <= yy /\ &0 <= R /\ 1 <= n
        ==> ee * yy pow n <= (&2 * R * Mabs) / (delta * (delta / &2) pow n)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = delta * yy / &2` THEN
  SUBGOAL_THEN `&0 <= (D:real)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ee:real) * (delta * D) <= (&2 * R) * v` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(ee:real) * (p * u)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((ee:real) * (delta * D)) * D pow (n - 1) <= &2 * R * Mabs`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `((&2 * R) * v) * (D:real) pow (n - 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE];
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real) pow n = D pow (n - 1) * D` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_PRED]; ALL_TAC] THEN
  SUBGOAL_THEN `(D:real) pow n = (delta / &2) pow n * yy pow n`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM REAL_POW_MUL] THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < delta * (delta / &2) pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN
   `((ee:real) * yy pow n) * (delta * (delta / &2) pow n) =
    (ee * (delta * D)) * D pow (n - 1)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(D:real) pow n = D pow (n - 1) * D`;
      `(D:real) pow n = (delta / &2) pow n * yy pow n`] THEN
    CONV_TAC REAL_RING;
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Siegel identity for three conjugates and the decomposition of the     *)
(* ratio (r_i - r_j) beta_k / ((r_i - r_k) beta_j) into a fixed algebraic    *)
(* number times a product of powers of unit ratios.                          *)
(* ------------------------------------------------------------------------- *)

let THUE_SIEGEL = prove
 (`!X y (ri:complex) rj rk.
        ~(ri = rk) /\ ~(Cx X - Cx y * rj = Cx(&0))
        ==> Cx(&1) + ((rk - rj) * (Cx X - Cx y * ri)) /
                     ((ri - rk) * (Cx X - Cx y * rj)) =
            ((ri - rj) * (Cx X - Cx y * rk)) /
            ((ri - rk) * (Cx X - Cx y * rj))`,
  CONV_TAC COMPLEX_FIELD);;

let THUE_UNIT_RATIO_PRODUCT = prove
 (`!(S:(num->complex)->bool) (mm:(num->complex)->num) j k.
        FINITE S /\ (!s. s IN S ==> ~(s j = Cx(&0)))
        ==> cproduct S (\s. s k pow mm s) =
            cproduct S (\s. (s k / s j) pow mm s) *
            cproduct S (\s. s j pow mm s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM CPRODUCT_MUL] THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `s:num->complex` THEN DISCH_TAC THEN
  BETA_TAC THEN REWRITE_TAC[GSYM COMPLEX_POW_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[COMPLEX_DIV_RMUL]);;

let THUE_DECOMP_RATIO = prove
 (`!(S:(num->complex)->bool) (mm:(num->complex)->num) (b:num->complex)
    bek bej cc dd j k.
        FINITE S /\ (!s. s IN S ==> ~(s j = Cx(&0))) /\
        bek = b k * cproduct S (\s. s k pow mm s) /\
        bej = b j * cproduct S (\s. s j pow mm s) /\
        ~(bej = Cx(&0)) /\ ~(dd = Cx(&0))
        ==> (cc * bek) / (dd * bej) =
            ((cc * b k) / (dd * b j)) * cproduct S (\s. (s k / s j) pow mm s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:(num->complex)->bool`; `mm:(num->complex)->num`;
                `j:num`; `k:num`] THUE_UNIT_RATIO_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `~((b:num->complex) j = Cx(&0)) /\
    ~(cproduct S (\s:num->complex. s j pow mm s) = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(bej = Cx(&0))` THEN ASM_REWRITE_TAC[COMPLEX_ENTIRE] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`~((b:num->complex) j = Cx(&0))`;
    `~(cproduct S (\s:num->complex. s j pow mm s) = Cx(&0))`;
    `~(dd = Cx(&0))`] THEN
  CONV_TAC COMPLEX_FIELD);;

let NF_ORDER_ALGEBRAIC = prove
 (`!n c r a k. nf_data n c r /\ nf_order n r a /\ k IN 1..n
               ==> algebraic_number(a k)`,
  MESON_TAC[NF_ORDER_ALGEBRAIC_INTEGER;
            ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER]);;

let THUE_ROOT_ALGEBRAIC = prove
 (`!n c r k. nf_data n c r /\ k IN 1..n ==> algebraic_number(r k)`,
  MESON_TAC[NF_DATA_ALGEBRAIC_INTEGER;
            ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER]);;

(* ------------------------------------------------------------------------- *)
(* Estimates for one solution with y <> 0: three distinct indices i, j, k    *)
(* (i the smallest conjugate), logarithmic size of all conjugates, and the   *)
(* smallness |E| |y|^n <= K2 of E = (r_k - r_j) beta_i / ((r_i - r_k)        *)
(* beta_j).                                                                  *)
(* ------------------------------------------------------------------------- *)

let THUE_SOLUTION_ESTIMATES = prove
 (`!n (r:num->complex) R delta M X y.
     3 <= n /\ &1 <= R /\ &0 < delta /\
     (!k. k IN 1..n ==> norm(r k) <= R) /\
     (!j k. j IN 1..n /\ k IN 1..n /\ ~(j = k) ==> delta <= norm(r j - r k)) /\
     &1 <= abs M /\ &1 <= abs y /\
     cproduct(1..n) (\k. Cx X - Cx y * r k) = Cx M
     ==> ?i j k. i IN 1..n /\ j IN 1..n /\ k IN 1..n /\
                 ~(i = j) /\ ~(i = k) /\ ~(j = k) /\
                 (!l. l IN 1..n ==> ~(Cx X - Cx y * r l = Cx(&0))) /\
                 (!l. l IN 1..n
                      ==> abs(log(norm(Cx X - Cx y * r l))) <=
                          &(n - 1) * log((abs M + &2 * R) * abs y)) /\
                 norm(((r k - r j) * (Cx X - Cx y * r i)) /
                      ((r i - r k) * (Cx X - Cx y * r j))) * abs y pow n
                 <= (&2 * R * abs M) / (delta * (delta / &2) pow n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `product(1..n) (\k. norm(Cx X - Cx y * (r:num->complex) k)) = abs M`
  ASSUME_TAC THENL
   [MATCH_MP_TAC THUE_NORM_PRODUCT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l IN 1..n ==> ~(Cx X - Cx y * (r:num->complex) l = Cx(&0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `cproduct(1..n) (\k. Cx X - Cx y * (r:num->complex) k) = Cx(&0)`
    MP_TAC THENL
     [SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN EXISTS_TAC `l:num` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `\k. norm(Cx X - Cx y * (r:num->complex) k)`]
    REAL_MIN_INDEX_NUMSEG) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `i:num`] THUE_THREE_INDICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num`
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm(Cx X - Cx y * (r:num->complex) i) <= abs M`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `\k. norm(Cx X - Cx y * (r:num->complex) k)`;
                  `i:num`; `abs M`] THUE_MIN_LE_NORM) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l IN 1..n /\ ~(l = i)
        ==> delta * abs y / &2 <= norm(Cx X - Cx y * (r:num->complex) l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC THUE_OTHERS_LARGE THEN
    EXISTS_TAC `(r:num->complex) i` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l IN 1..n
        ==> norm(Cx X - Cx y * (r:num->complex) l) <= (abs M + &2 * R) * abs y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC REAL_LE_TRANS `abs M + &2 * R * abs y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC THUE_CONJ_UPPER THEN EXISTS_TAC `(r:num->complex) i` THEN
      ASM_SIMP_TAC[];
      MP_TAC(SPECL [`abs M`; `&1`; `abs y`] REAL_LE_LMUL) THEN
      ASM_REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `l:num` THEN DISCH_TAC THEN MATCH_MP_TAC THUE_LOG_ABS_LE THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[NORM_POS_LT; COMPLEX_VEC_0];
      ASM_SIMP_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= x ==> &1 <= x`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`1..n`; `\k. norm(Cx X - Cx y * (r:num->complex) k)`;
                   `l:num`; `(abs M + &2 * R) * abs y`]
      THUE_PRODUCT_OTHERS_LE) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; NORM_POS_LE] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `\k. norm(Cx X - Cx y * (r:num->complex) k)`;
                  `l:num`] THUE_PRODUCT_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS
     `norm(Cx X - Cx y * (r:num->complex) l) *
      product((1..n) DELETE l) (\k. norm(Cx X - Cx y * r k))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `delta <= norm((r:num->complex) i - r k) /\
    delta <= norm((r:num->complex) k - r j) /\
    norm((r:num->complex) k - r j) <= &2 * R`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `delta:real` (concl th) &&
        not(free_in `abs(y:real)` (concl th)))) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `delta:real` (concl th) &&
        not(free_in `abs(y:real)` (concl th)))) THEN ASM_MESON_TAC[];
      MATCH_MP_TAC(NORM_ARITH
       `!a b:complex R. norm a <= R /\ norm b <= R
                       ==> norm(a - b) <= &2 * R`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((r:num->complex) i = r k) /\ ~((r:num->complex) k = r j)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `delta <= norm((r:num->complex) i - r k)`;
      UNDISCH_TAC `delta <= norm((r:num->complex) k - r j)`] THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(Cx X - Cx y * (r:num->complex) i) * (delta * abs y / &2) pow (n - 1)
    <= abs M`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1..n`; `\k. norm(Cx X - Cx y * (r:num->complex) k)`;
                   `i:num`; `delta * abs y / &2`] THUE_PRODUCT_OTHERS_GE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC];
      REWRITE_TAC[CARD_NUMSEG_1] THEN DISCH_TAC] THEN
    MP_TAC(SPECL [`n:num`; `\k. norm(Cx X - Cx y * (r:num->complex) k)`;
                  `i:num`] THUE_PRODUCT_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC THUE_E_BOUND THEN
  MAP_EVERY EXISTS_TAC
   [`norm((r:num->complex) i - r k)`; `norm((r:num->complex) k - r j)`;
    `norm(Cx X - Cx y * (r:num->complex) j)`;
    `norm(Cx X - Cx y * (r:num->complex) i)`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_MUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC COMPLEX_DIV_RMUL THEN
    ASM_SIMP_TAC[COMPLEX_ENTIRE; DE_MORGAN_THM; COMPLEX_SUB_0];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Main step: for a fixed non-zero norm M, |y| is bounded on all solutions   *)
(* of prod_k (X - y r_k) = M (one application of BAKER_FELDMAN, uniformly    *)
(* over the finitely many choices of b in M and of the indices i, j, k).     *)
(* ------------------------------------------------------------------------- *)

let THUE_Y_BOUND = prove
 (`!n c r M.
        3 <= n /\ nf_data n c r /\ integer M /\ ~(M = &0)
        ==> ?Y. !X y. integer X /\ integer y /\
                      cproduct(1..n) (\k. Cx X - Cx y * r k) = Cx M
                      ==> abs y <= Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= abs M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`]
    THUE_ROOT_CONSTANTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (X_CHOOSE_THEN `delta:real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `M:real`]
    NF_NORM_EQ_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ms:(num->complex)->bool`
   (X_CHOOSE_THEN `S:(num->complex)->bool` (X_CHOOSE_THEN `C2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (LABEL_TAC "dec")))))))) THEN
  ABBREV_TAC
   `alpha = \u:(num->complex)#num#num#num.
      (((r:num->complex)(FST(SND u)) - r(FST(SND(SND u)))) *
       FST u (SND(SND(SND u)))) /
      ((r(FST(SND u)) - r(SND(SND(SND u)))) * FST u (FST(SND(SND u))))` THEN
  MP_TAC(ISPECL
   [`{u | u IN (Ms:(num->complex)->bool) CROSS
               ((1..n) CROSS ((1..n) CROSS (1..n))) /\
          ~((alpha:(num->complex)#num#num#num->complex) u = Cx(&0))}`;
    `S:(num->complex)->bool`;
    `\(u:(num->complex)#num#num#num) (s:num->complex).
        s(SND(SND(SND u))) / s(FST(SND(SND u)))`;
    `alpha:(num->complex)#num#num#num->complex`] BAKER_ONE_PLUS_E) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN
      ASM_SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG];
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS] THEN
    MAP_EVERY X_GEN_TAC [`b:num->complex`; `i:num`; `j:num`; `k:num`] THEN
    EXPAND_TAC "alpha" THEN BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC ALGEBRAIC_NUMBER_DIV ORELSE
             MATCH_MP_TAC ALGEBRAIC_NUMBER_MUL ORELSE
             MATCH_MP_TAC ALGEBRAIC_NUMBER_SUB ORELSE CONJ_TAC) THEN
      ASM_MESON_TAC[THUE_ROOT_ALGEBRAIC; NF_ORDER_ALGEBRAIC];
      X_GEN_TAC `s:num->complex` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((s:num->complex) k = Cx(&0)) /\ ~(s j = Cx(&0))`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[NF_UNIT_NONZERO]; ALL_TAC] THEN
      ASM_REWRITE_TAC[COMPLEX_DIV_EQ_0] THEN
      MATCH_MP_TAC ALGEBRAIC_NUMBER_DIV THEN
      ASM_MESON_TAC[NF_ORDER_ALGEBRAIC; nf_unit]];
    DISCH_THEN(X_CHOOSE_THEN `C:num` (LABEL_TAC "baker"))] THEN
  ABBREV_TAC `K2 = (&2 * R * abs M) / (delta * (delta / &2) pow n)` THEN
  SUBGOAL_THEN `&0 <= K2` ASSUME_TAC THENL
   [EXPAND_TAC "K2" THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(abs M + &2 * R)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL
   [`&2 * K2`; `&2 + abs C2 * (&1 + &(n - 1) * log(abs M + &2 * R))`;
    `abs C2 * &(n - 1)`; `n:num`; `C:num`] POLYLOG_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_POS];
      ASM_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `Y1:real` (LABEL_TAC "poly"))] THEN
  EXISTS_TAC `max (&1) (max (&2 * K2) Y1)` THEN
  MAP_EVERY X_GEN_TAC [`X:real`; `y:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `y = &0` THENL
   [ASM_REWRITE_TAC[REAL_ABS_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= abs y` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `r:num->complex`; `R:real`; `delta:real`; `M:real`;
                `X:real`; `y:real`] THUE_SOLUTION_ESTIMATES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num`
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `~((r:num->complex) i = r j) /\ ~(r i = r k) /\ ~(r k = r j)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`i IN 1..n`; `j IN 1..n`; `k IN 1..n`; `~(i:num = j)`;
      `~(i:num = k)`; `~(j:num = k)`; `nf_data n c (r:num->complex)`] THEN
    MESON_TAC[NF_DATA_ROOTS_DISTINCT];
    ALL_TAC] THEN
  ABBREV_TAC
   `E = (((r:num->complex) k - r j) * (Cx X - Cx y * r i)) /
        ((r i - r k) * (Cx X - Cx y * r j))` THEN
  SUBGOAL_THEN `~(E = Cx(&0))` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    ASM_SIMP_TAC[COMPLEX_DIV_EQ_0; COMPLEX_ENTIRE; COMPLEX_SUB_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 / &2 < norm(E:complex)` THENL
   [MATCH_MP_TAC(REAL_ARITH
     `(x:real) <= &2 * K2 ==> x <= max (&1) (max (&2 * K2) Y1)`) THEN
    MATCH_MP_TAC REAL_POW_LE_BOUND_HALF THEN
    MAP_EVERY EXISTS_TAC [`norm(E:complex)`; `n:num`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(E:complex) <= &1 / &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "dec" (MP_TAC o SPECL
   [`\k. Cx X - Cx y * (r:num->complex) k`;
    `&(n - 1) * log((abs M + &2 * R) * abs y)`]) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NF_ORDER_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC NF_ORDER_CX THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC NF_ORDER_MUL THEN REWRITE_TAC[ETA_AX; NF_ORDER_ROOT] THEN
      MATCH_MP_TAC NF_ORDER_CX THEN ASM_REWRITE_TAC[]];
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `b:num->complex`
      (X_CHOOSE_THEN `mm:(num->complex)->num` STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN
   `Cx(&1) + E =
    (((r:num->complex) i - r j) * (Cx X - Cx y * r k)) /
    ((r i - r k) * (Cx X - Cx y * r j))`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC THUE_SIEGEL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((r:num->complex) i - r j) * (Cx X - Cx y * r k)) /
    ((r i - r k) * (Cx X - Cx y * r j)) =
    (((r i - r j) * b k) / ((r i - r k) * b j)) *
    cproduct S (\s. (s k / s j) pow mm s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC THUE_DECOMP_RATIO THEN ASM_SIMP_TAC[COMPLEX_SUB_0] THEN
    ASM_MESON_TAC[NF_UNIT_NONZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((((r:num->complex) i - r j) * b k) / ((r i - r k) * b j) = Cx(&0))`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `E:complex` COMPLEX_ONE_PLUS_NZ) THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  REMOVE_THEN "baker" (MP_TAC o SPECL
   [`(b:num->complex),(i:num),(j:num),(k:num)`;
    `mm:(num->complex)->num`; `E:complex`]) THEN
  EXPAND_TAC "alpha" THEN
  REWRITE_TAC[FST; SND; IN_ELIM_THM; IN_CROSS] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(x:real) <= Y1 ==> x <= max (&1) (max (&2 * K2) Y1)`) THEN
  REMOVE_THEN "poly" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_BOUND_CHAIN THEN
  MAP_EVERY EXISTS_TAC
   [`&2 + &(nsum S (mm:(num->complex)->num))`; `norm(E:complex)`;
    `&2 * norm(E:complex)`] THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_REFL] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `nsum S (mm:(num->complex)->num)` REAL_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LINEAR_BOUND_ABS THEN ASM_SIMP_TAC[LOG_POS] THEN
  SUBGOAL_THEN
   `log((abs M + &2 * R) * abs y) = log(abs M + &2 * R) + log(abs y)`
  (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC LOG_MUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bound for x, the degenerate norm 0, and finiteness for monic forms.       *)
(* ------------------------------------------------------------------------- *)

let THUE_X_BOUND = prove
 (`!n (r:num->complex) R M X y.
        1 <= n /\ (!k. k IN 1..n ==> norm(r k) <= R) /\ &1 <= abs M /\
        cproduct(1..n) (\k. Cx X - Cx y * r k) = Cx M
        ==> abs X <= abs M + R * abs y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `\k. norm(Cx X - Cx y * (r:num->complex) k)`]
    REAL_MIN_INDEX_NUMSEG) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC THUE_X_UPPER THEN EXISTS_TAC `(r:num->complex) i` THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `\k. norm(Cx X - Cx y * (r:num->complex) k)`;
                `i:num`; `abs M`] THUE_MIN_LE_NORM) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[NORM_POS_LE] THEN MATCH_MP_TAC THUE_NORM_PRODUCT THEN
  ASM_REWRITE_TAC[]);;

let THUE_ZERO_NORM = prove
 (`!n c r X y.
        3 <= n /\ nf_data n c r /\ integer X /\ integer y /\
        cproduct(1..n) (\k. Cx X - Cx y * r k) = Cx(&0)
        ==> X = &0 /\ y = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `cproduct(1..n) (\k. Cx X - Cx y * (r:num->complex) k) = Cx(&0)` THEN
  SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `nf_data n c (r:num->complex)` THEN REWRITE_TAC[nf_data] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`k:num`; `1`; `\i. if i = 0 then --X else if i = 1 then y else &0`] o
   last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
      ASM_SIMP_TAC[INTEGER_CLOSED];
      SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
      REWRITE_TAC[ARITH; VSUM_SING_NUMSEG; complex_pow; COMPLEX_POW_1] THEN
      REWRITE_TAC[CX_NEG] THEN
      UNDISCH_TAC `Cx X - Cx y * (r:num->complex) k = Cx(&0)` THEN
      CONV_TAC COMPLEX_RING];
    DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th)) THEN
    REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC]);;

let THUE_MONIC_BOUND = prove
 (`!n c r M.
        3 <= n /\ nf_data n c r /\ integer M
        ==> ?A. !X y. integer X /\ integer y /\
                      cproduct(1..n) (\k. Cx X - Cx y * r k) = Cx M
                      ==> abs X <= A /\ abs y <= A`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `M = &0` THENL
   [EXISTS_TAC `&0` THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `X:real`;
                  `y:real`] THUE_ZERO_NORM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `M:real`]
    THUE_Y_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Y:real`) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`]
    THUE_ROOT_CONSTANTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (X_CHOOSE_THEN `delta:real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `max (abs M + R * Y) Y` THEN
  MAP_EVERY X_GEN_TAC [`X:real`; `y:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs y <= Y` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`X:real`; `y:real`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs X <= abs M + R * abs y` ASSUME_TAC THENL
   [MATCH_MP_TAC THUE_X_BOUND THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `r:num->complex`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `R * abs y <= R * Y` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Thue theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let THUE = prove
 (`!n (a:num->real) m.
      3 <= n /\ (!i. integer(a i)) /\ ~(a 0 = &0) /\ integer m /\
      (!t. vsum(0..n) (\i. Cx(a i) * t pow (n - i)) = Cx(&0)
           ==> !d b. d < n /\ (!i. integer(b i)) /\
                     vsum(0..d) (\i. Cx(b i) * t pow i) = Cx(&0)
                     ==> !i. i <= d ==> b i = &0)
      ==> FINITE {(x,y) | integer x /\ integer y /\
                          sum(0..n) (\i. a i * x pow (n - i) * y pow i) = m}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "deg"))))) THEN
  MP_TAC(SPECL [`n:num`; `a:num->real`] THUE_FORM_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `t:num->complex`) THEN
  MP_TAC(SPECL [`n:num`; `a:num->real`; `t:num->complex`]
    THUE_MONIC_NF_DATA) THEN
  REMOVE_THEN "deg" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL
   [`n:num`;
    `\j. if j = n then &1
         else (a:num->real)(n - j) * a 0 pow (n - j - 1)`;
    `\k. Cx((a:num->real) 0) * (t:num->complex) k`;
    `(a:num->real) 0 pow (n - 1) * m`] THUE_MONIC_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGER_MUL THEN ASM_SIMP_TAC[INTEGER_POW];
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC `A:real`)] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x | integer x /\ --A <= x /\ x <= A} CROSS
              {x | integer x /\ --A <= x /\ x <= A}` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_INTSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS;
              IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(a:num->real) 0 * x`; `y:real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INTEGER_MUL] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC THUE_FORM_HOMOG THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs x <= abs((a:num->real) 0 * x)` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Example: x^3 - 2 y^3 = m (every root of t^3 - 2 has degree 3:             *)
(* NF_CUBE2_DEGREE). THUE_SUM_0_3 and THUE_VSUM_SMALL are also used in       *)
(* Baker/mordell.ml.                                                         *)
(* ------------------------------------------------------------------------- *)

let THUE_SUM_0_3 = prove
 (`!f. sum(0..3) f = f 0 + f 1 + f 2 + f 3`,
  GEN_TAC THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`;
              SUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[REAL_ADD_AC]);;

let THUE_VSUM_SMALL = prove
 (`!f:num->complex.
        vsum(0..0) f = f 0 /\
        vsum(0..1) f = f 0 + f 1 /\
        vsum(0..2) f = f 0 + f 1 + f 2 /\
        vsum(0..3) f = f 0 + f 1 + f 2 + f 3`,
  GEN_TAC THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`;
              VSUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[COMPLEX_ADD_AC]);;

let THUE_CUBIC_2 = prove
 (`!m. integer m
       ==> FINITE {(x,y) | integer x /\ integer y /\
                           x pow 3 - &2 * y pow 3 = m}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`3`; `\i. if i = 0 then &1 else if i = 3 then -- &2 else &0`;
                `m:real`] THUE) THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `!x y. sum(0..3) (\i. (if i = 0 then &1 else if i = 3 then -- &2 else &0) *
                         x pow (3 - i) * y pow i) =
          x pow 3 - &2 * y pow 3`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[THUE_SUM_0_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  X_GEN_TAC `t:complex` THEN REWRITE_TAC[THUE_VSUM_SMALL] THEN BETA_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t pow 3 = Cx(&2)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`d:num`; `b:num->real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC NF_CUBE2_DEGREE THEN
  EXISTS_TAC `t:complex` THEN ASM_REWRITE_TAC[]);;
