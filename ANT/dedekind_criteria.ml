(* ========================================================================= *)
(* Characterizations of Dedekind domains, and Dedekind domains with finitely *)
(* many primes.                                                              *)
(*                                                                           *)
(* Main results: a Dedekind domain with finitely many maximal ideals is a    *)
(* PID (DEDEKIND_SEMILOCAL_IMP_PID); a domain is Dedekind iff its nonzero    *)
(* ideals are invertible, that is j k = (e) for an ideal k and a nonzero e   *)
(* (DEDEKIND_EQ_IDEALS_INVERTIBLE), iff J J^-1 = h(r) for every fractional   *)
(* ideal J in a field of fractions k along h                                 *)
(* (DEDEKIND_EQ_FRACTIONAL_IDEALS_INVERTIBLE); a Noetherian domain is        *)
(* Dedekind iff its localizations at the nonzero primes are DVRs             *)
(* (DEDEKIND_EQ_LOCALIZATIONS_DVR).                                          *)
(*                                                                           *)
(* Routes. Finitely many primes: weak approximation                          *)
(* (DEDEKIND_WEAK_APPROXIMATION) gives an x with v_P(x) = v_P(j) at all of   *)
(* them, so (x) = j. Invertible ideals: (a) j SUBSET (b) j forces b | a      *)
(* (INVERTIBLE_IDEAL_DIVIDES), which with a homogeneous monic relation       *)
(* (RING_HOMOGENEOUS_RELATION_IDEAL) gives integral closure                  *)
(* (INVERTIBLE_IDEALS_IMP_INTEGRALLY_CLOSED); invertible ideals are finitely *)
(* generated (INVERTIBLE_IDEALS_IMP_NOETHERIAN) and can be cancelled         *)
(* (INVERTIBLE_IDEAL_PROD_CANCEL), so a nonzero prime p in a maximal m       *)
(* satisfies p = m L with L = m^-1 p, and L SUBSET p would give m = r, hence *)
(* p = m (INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL). Localizations: a nonzero     *)
(* prime p in a maximal m gives two nonzero primes of the DVR at m, so p = m *)
(* (LOCALLY_DVR_PRIME_IMP_MAXIMAL); for a homogeneous relation of a and b    *)
(* the ideal of the y with b | y a is the unit ideal, else b | a in the DVR  *)
(* at a maximal ideal above it would put an element outside that ideal into  *)
(* it (LOCALLY_DVR_IMP_INTEGRALLY_CLOSED).                                   *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, ANT/integral.ml (INTEGRALLY_CLOSED_ALT),     *)
(* ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml (DVR,         *)
(* DEDEKIND_WEAK_APPROXIMATION), ANT/dedekind_local.ml (DVR_LOCALIZATION)    *)
(* and ANT/fractional_ideals.ml.                                             *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "ANT/integral.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_struct.ml";;
needs "ANT/dedekind_local.ml";;
needs "ANT/fractional_ideals.ml";;

(* ------------------------------------------------------------------------- *)
(* A Dedekind domain with finitely many maximal ideals is a PID.             *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_SEMILOCAL_IMP_PID = prove
 (`!r:A ring.
        dedekind_domain r /\ FINITE {m | maximal_ideal r m} ==> PID r`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  ASM_REWRITE_TAC[PID] THEN X_GEN_TAC `j:A->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j = {ring_0 r:A}` THEN ASM_REWRITE_TAC[PRINCIPAL_IDEAL_0] THEN
  MP_TAC(ISPECL [`r:A ring`;
                 `{p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})}`;
                 `\p. ideal_valuation r p (j:A->bool)`]
    DEDEKIND_WEAK_APPROXIMATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:A->bool | maximal_ideal r m}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL];
    REWRITE_TAC[IN_ELIM_THM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[principal_ideal] THEN EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_generated r {a:A}`; `j:A->bool`]
    DEDEKIND_IDEAL_EQ_VALUATION) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* A domain in which every nonzero ideal is invertible is Dedekind.          *)
(* ------------------------------------------------------------------------- *)

(* With invertible ideals, (a) j SUBSET (b) j for a nonzero j forces b | a. *)

let INVERTIBLE_IDEAL_DIVIDES = prove
 (`!r j k (a:A) b e.
        integral_domain r /\ ring_ideal r j /\ ring_ideal r k /\
        e IN ring_carrier r /\ ~(e = ring_0 r) /\
        ideal_prod r j k = ideal_generated r {e} /\
        a IN ring_carrier r /\ b IN ring_carrier r /\
        IMAGE (ring_mul r a) j SUBSET IMAGE (ring_mul r b) j
        ==> ring_divides r b a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e:A) IN ideal_prod r j k` MP_TAC THENL
   [ASM_SIMP_TAC[IN_IDEAL_GENERATED_SELF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`] IDEAL_PROD_EXPLICIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `u:num->A`; `v:num->A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i < n ==> (u:num->A) i IN ring_carrier r /\
     (v:num->A) i IN ring_carrier r`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?w. i < n ==> w IN j /\ ring_mul r a ((u:num->A) i) = ring_mul r b w`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `ring_mul r a ((u:num->A) i) IN IMAGE (ring_mul r b) j`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE];
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `w:num->A` THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `ring_sum r {i | i < n} (\i. ring_mul r ((w:num->A) i) (v i)) IN
    ideal_generated r {e:A}`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      lhand(concl th) = `ideal_prod r j (k:A->bool)`)) THEN
    MATCH_MP_TAC IN_RING_IDEAL_SUM THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_PROD; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN
    ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
    ASM_SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM; ring_divides]] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  REWRITE_TAC[ring_divides] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `t:A` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_RCANCEL THEN
  MAP_EVERY EXISTS_TAC [`r:A ring`; `e:A`] THEN
  ASM_SIMP_TAC[RING_MUL] THEN
  TRANS_TAC EQ_TRANS
   `ring_mul r b (ring_sum r {i | i < n}
                   (\i. ring_mul r ((w:num->A) i) (v i)))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      lhand(concl th) = `e:A`)) THEN
    SUBGOAL_THEN `!i. i < n ==> (w:num->A) i IN ring_carrier r`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM RING_SUM_LMUL; FINITE_NUMSEG_LT; IN_ELIM_THM;
                 RING_MUL; RING_SUM] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC];
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[RING_SUM; RING_RULE
     `ring_mul r b (ring_mul r s t) = ring_mul r (ring_mul r b t) (s:A)`]]);;

(* A homogeneous monic relation a^(m+1) + sum c_i a^i b^(m+1-i) = 0 gives    *)
(* a j SUBSET b j for the ideal j generated by the a^i b^(m-i), i <= m.      *)

let RING_HOMOGENEOUS_RELATION_IDEAL = prove
 (`!r (a:A) b c m.
        a IN ring_carrier r /\ b IN ring_carrier r /\
        (!i. i < SUC m ==> c i IN ring_carrier r) /\
        ring_add r (ring_pow r a (SUC m))
          (ring_sum r {i | i < SUC m}
             (\i. ring_mul r (c i)
                    (ring_mul r (ring_pow r a i) (ring_pow r b (SUC m - i))))) =
        ring_0 r
        ==> IMAGE (ring_mul r a)
              (ideal_generated r
                 (IMAGE (\i. ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))
                        {i | i <= m})) SUBSET
            IMAGE (ring_mul r b)
              (ideal_generated r
                 (IMAGE (\i. ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))
                        {i | i <= m}))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `j = ideal_generated r
         (IMAGE (\i. ring_mul r (ring_pow r (a:A) i) (ring_pow r b (m - i)))
                {i | i <= m})` THEN
  SUBGOAL_THEN `ring_ideal r (j:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= m
        ==> ring_mul r (ring_pow r (a:A) i) (ring_pow r b (m - i)) IN j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "j" THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[RING_MUL; RING_POW] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_ideal r (IMAGE (ring_mul r b) (j:A->bool))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM IDEAL_PROD_SCALE; RING_IDEAL_IDEAL_PROD]; ALL_TAC] THEN
  SUBGOAL_THEN
   `j SUBSET {x:A | x IN ring_carrier r /\
                    ring_mul r a x IN IMAGE (ring_mul r b) j}`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o
    check (fun th -> rand(concl th) = `j:A->bool`)) THEN
  MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[RING_IDEAL; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN
    ASM_SIMP_TAC[RING_0; RING_MUL_RZERO; IN_RING_IDEAL_0; RING_ADD; RING_MUL;
                 RING_ADD_LDISTRIB; IN_RING_IDEAL_ADD] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_mul r a (ring_mul r x y) = ring_mul r x (ring_mul r a (y:A))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul r a (ring_mul r x y) = ring_mul r x (ring_mul r a (y:A))`) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[IN_RING_IDEAL_LMUL]]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[RING_MUL; RING_POW] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  ASM_CASES_TAC `p:num = m` THENL
   [ALL_TAC;
    EXISTS_TAC
     `ring_mul r (ring_pow r (a:A) (SUC p)) (ring_pow r b (m - SUC p))` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `m - p = SUC(m - SUC p)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[ring_pow]] THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul r a (ring_mul r x (ring_mul r b y)) =
        ring_mul r b (ring_mul r (ring_mul r a x) (y:A))`) THEN
      ASM_SIMP_TAC[RING_POW];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  EXISTS_TAC
   `ring_neg r (ring_sum r {i | i < SUC m}
      (\i. ring_mul r ((c:num->A) i)
             (ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC IN_RING_IDEAL_NEG THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IN_RING_IDEAL_SUM THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[SUB_REFL; ring_pow] THEN ASM_SIMP_TAC[RING_MUL_RID; RING_POW] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `ring_0 r:A`)) THEN
  REWRITE_TAC[ring_pow] THEN
  SUBGOAL_THEN
   `ring_sum r {i | i < SUC m}
      (\i. ring_mul r ((c:num->A) i)
             (ring_mul r (ring_pow r a i) (ring_pow r b (SUC m - i)))) =
    ring_mul r b (ring_sum r {i | i < SUC m}
      (\i. ring_mul r (c i)
             (ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`r:A ring`;
      `\i. ring_mul r ((c:num->A) i)
                     (ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))`;
      `b:A`; `{i:num | i < SUC m}`] RING_SUM_LMUL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; RING_POW];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `SUC m - q = SUC(m - q)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ring_pow]] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul r c (ring_mul r x (ring_mul r b y)) =
      ring_mul r b (ring_mul r c (ring_mul r x (y:A)))`) THEN
    ASM_SIMP_TAC[RING_POW];
    ALL_TAC] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_add r x (ring_mul r b s) = ring_0 r
    ==> x = ring_mul r b (ring_neg r (s:A))`) THEN
  ASM_SIMP_TAC[RING_MUL; RING_POW; RING_SUM]);;

let INVERTIBLE_IDEALS_IMP_INTEGRALLY_CLOSED = prove
 (`!r:A ring.
        integral_domain r /\
        (!j. ring_ideal r j /\ ~(j = {ring_0 r})
             ==> ?k e. ring_ideal r k /\ e IN ring_carrier r /\
                       ~(e = ring_0 r) /\
                       ideal_prod r j k = ideal_generated r {e})
        ==> integrally_closed r`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INTEGRALLY_CLOSED_ALT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`; `c:num->A`; `n:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_TAC
     `ring_add r (ring_pow r a n)
       (ring_sum r {i | i < n}
         (\i. ring_mul r (c i) (ring_mul r (ring_pow r (a:A) i)
                                           (ring_pow r b (n - i))))) =
      ring_0 r` THEN
    ASM_REWRITE_TAC[ring_pow; LT; EMPTY_GSPEC; RING_SUM_CLAUSES] THEN
    ASM_SIMP_TAC[RING_ADD_RZERO; RING_1; INTEGRAL_DOMAIN_NONTRIVIAL];
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
      MATCH_MP (MESON[num_CASES] `~(n = 0) ==> ?m. n = SUC m`))] THEN
  ABBREV_TAC
   `j = ideal_generated r
         (IMAGE (\i. ring_mul r (ring_pow r (a:A) i) (ring_pow r b (m - i)))
                {i | i <= m})` THEN
  SUBGOAL_THEN `ring_ideal r (j:A->bool) /\ ~(j = {ring_0 r})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED];
      MATCH_MP_TAC(SET_RULE `!x:A. x IN j /\ ~(x = z) ==> ~(j = {z})`) THEN
      EXISTS_TAC `ring_pow r (b:A) m` THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_POW_EQ_0] THEN
      EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[RING_MUL; RING_POW] THEN EXISTS_TAC `0` THEN
      ASM_SIMP_TAC[LE_0; ring_pow; SUB_0; RING_MUL_LID; RING_POW]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:A->bool`; `e:A`] THEN STRIP_TAC THEN
  MATCH_MP_TAC INVERTIBLE_IDEAL_DIVIDES THEN
  MAP_EVERY EXISTS_TAC [`j:A->bool`; `k:A->bool`; `e:A`] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "j" THEN
  MATCH_MP_TAC RING_HOMOGENEOUS_RELATION_IDEAL THEN
  EXISTS_TAC `c:num->A` THEN ASM_REWRITE_TAC[]);;

(* Invertible ideals are finitely generated: from a = sum u_i v_i in       *)
(* j k = (a) every x of j is the combination of the u_i with the x v_i / a. *)

let INVERTIBLE_IDEALS_IMP_NOETHERIAN = prove
 (`!r:A ring.
        integral_domain r /\
        (!j. ring_ideal r j /\ ~(j = {ring_0 r})
             ==> ?k e. ring_ideal r k /\ e IN ring_carrier r /\
                       ~(e = ring_0 r) /\
                       ideal_prod r j k = ideal_generated r {e})
        ==> noetherian_ring r`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC[noetherian_ring; finitely_generated_ideal] THEN
  X_GEN_TAC `j:A->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j = {ring_0 r:A}` THENL
   [EXISTS_TAC `{}:A->bool` THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; IDEAL_GENERATED_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:A->bool`; `e:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:A) IN ideal_prod r j k` MP_TAC THENL
   [ASM_SIMP_TAC[IN_IDEAL_GENERATED_SELF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`] IDEAL_PROD_EXPLICIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `u:num->A`; `v:num->A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    lhand(concl th) = `e:A`)) THEN
  SUBGOAL_THEN
   `!i. i < n ==> (u:num->A) i IN ring_carrier r /\
     (v:num->A) i IN ring_carrier r`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (u:num->A) {i | i < n}` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC] THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?t. i < n ==> t IN ring_carrier r /\
                     ring_mul r x ((v:num->A) i) = ring_mul r e t`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `ring_mul r x ((v:num->A) i) IN ideal_generated r {e:A}`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        lhand(concl th) = `ideal_prod r j (k:A->bool)`)) THEN
      MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM; ring_divides] THEN
      MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `t:num->A` THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `x = ring_sum r {i | i < n} (\i. ring_mul r ((t:num->A) i) (u i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`r:A ring`; `e:A`] THEN
    ASM_SIMP_TAC[RING_SUM] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r {i | i < n}
        (\i. ring_mul r (ring_mul r ((u:num->A) i) (v i)) x)` THEN
    CONJ_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL
       [`r:A ring`; `\i. ring_mul r ((u:num->A) i) (v i)`; `x:A`;
        `{i:num | i < n}`] RING_SUM_RMUL)) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(BETA_RULE(ISPECL
       [`r:A ring`; `\i. ring_mul r ((t:num->A) i) (u i)`; `e:A`;
        `{i:num | i < n}`] RING_SUM_LMUL)) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
       `ring_mul r x v = ring_mul r e t
        ==> ring_mul r (ring_mul r u v) x =
            ring_mul r e (ring_mul r t (u:A))`)) THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC IN_RING_IDEAL_SUM THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]]);;

(* Cancellation of an invertible ideal j, with j k = (e).                    *)

let INVERTIBLE_IDEAL_PROD_CANCEL = prove
 (`!r j k (e:A) x y.
        integral_domain r /\ ring_ideal r j /\ ring_ideal r k /\
        e IN ring_carrier r /\ ~(e = ring_0 r) /\
        ideal_prod r j k = ideal_generated r {e} /\
        ring_ideal r x /\ ring_ideal r y /\
        ideal_prod r j x = ideal_prod r j y
        ==> x = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `e:A`; `x:A->bool`; `y:A->bool`]
    IDEAL_PROD_PRINCIPAL_CANCEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    lhand(concl th) = `ideal_prod r j (k:A->bool)`)) THEN
  TRANS_TAC EQ_TRANS `ideal_prod r k (ideal_prod r j (x:A->bool))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[IDEAL_PROD_AC; RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_PROD;
             ASSUME `ring_ideal r (j:A->bool)`;
             ASSUME `ring_ideal r (k:A->bool)`;
             ASSUME `ring_ideal r (x:A->bool)`];
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[IDEAL_PROD_AC; RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_PROD;
             ASSUME `ring_ideal r (j:A->bool)`;
             ASSUME `ring_ideal r (k:A->bool)`;
             ASSUME `ring_ideal r (y:A->bool)`]]);;

(* Nonzero primes are maximal: for p SUBSET m maximal, m^-1 p is an ideal L  *)
(* with m L = p, and L SUBSET p would give p = m p, so m = r by cancellation. *)

let INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL = prove
 (`!r p:A->bool.
        integral_domain r /\
        (!j. ring_ideal r j /\ ~(j = {ring_0 r})
             ==> ?k e. ring_ideal r k /\ e IN ring_carrier r /\
                       ~(e = ring_0 r) /\
                       ideal_prod r j k = ideal_generated r {e}) /\
        prime_ideal r p /\ ~(p = {ring_0 r})
        ==> maximal_ideal r p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  FIRST_X_ASSUM(LABEL_TAC "inv" o check (is_forall o concl)) THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A->bool`] MAXIMAL_SUPERIDEAL_EXISTS) THEN
  ASM_SIMP_TAC[PRIME_IMP_PROPER_IDEAL; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `p:A->bool = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `~(m = {ring_0 r:A})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[IN_RING_IDEAL_0; SET_RULE
     `(z:A) IN p /\ p SUBSET {z} ==> p = {z}`];
    ALL_TAC] THEN
  USE_THEN "inv" (MP_TAC o SPEC `m:A->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`k:A->bool`; `a:A`] THEN STRIP_TAC THEN
  ABBREV_TAC
   `L = {t:A | t IN ring_carrier r /\
               ring_mul r a t IN ideal_prod r p k}` THEN
  SUBGOAL_THEN `ring_ideal r (L:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[RING_IDEAL; SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[] THEN
    ASM_SIMP_TAC[RING_0; RING_MUL_RZERO; IN_RING_IDEAL_0;
                 RING_IDEAL_IDEAL_PROD; RING_ADD; RING_MUL;
                 RING_ADD_LDISTRIB; IN_RING_IDEAL_ADD] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_mul r a (ring_mul r x y) = ring_mul r x (ring_mul r a (y:A))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul r a (ring_mul r x y) = ring_mul r x (ring_mul r a (y:A))`) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[IN_RING_IDEAL_LMUL; RING_IDEAL_IDEAL_PROD]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ideal_prod r (ideal_generated r {a}) L = ideal_prod r p (k:A->bool)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[IDEAL_PROD_SCALE] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC] THEN
    SUBGOAL_THEN `(y:A) IN ideal_generated r {a}` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        lhand(concl th) = `ideal_prod r m (k:A->bool)`)) THEN
      MP_TAC(ISPECL [`r:A ring`; `p:A->bool`; `m:A->bool`; `k:A->bool`;
                     `k:A->bool`] IDEAL_PROD_MONO) THEN
      ASM SET_TAC[];
      ASM_SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM; ring_divides]] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    EXISTS_TAC `t:A` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ideal_prod r m (L:A->bool) = p` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `a:A`; `ideal_prod r m (L:A->bool)`;
                   `p:A->bool`] IDEAL_PROD_PRINCIPAL_CANCEL) THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_PROD] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
    TRANS_TAC EQ_TRANS
     `ideal_prod r m (ideal_prod r (ideal_generated r {a:A}) L)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[IDEAL_PROD_AC; RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_PROD;
       RING_IDEAL_IDEAL_GENERATED; ASSUME `ring_ideal r (m:A->bool)`; ASSUME
       `ring_ideal r (L:A->bool)`];
      ASM_REWRITE_TAC[]] THEN
    TRANS_TAC EQ_TRANS `ideal_prod r p (ideal_prod r m (k:A->bool))` THEN
    CONJ_TAC THENL
     [SIMP_TAC[IDEAL_PROD_AC; RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_PROD;
       ASSUME `ring_ideal r (m:A->bool)`; ASSUME `ring_ideal r (p:A->bool)`;
       ASSUME `ring_ideal r (k:A->bool)`];
      ASM_REWRITE_TAC[]] THEN
    SIMP_TAC[IDEAL_PROD_AC; RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_PROD;
      RING_IDEAL_IDEAL_GENERATED; ASSUME `ring_ideal r (p:A->bool)`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A->bool`; `m:A->bool`; `L:A->bool`]
    IDEAL_PROD_SUBSET_PRIME_IDEAL) THEN
  ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; SUBSET_REFL] THEN STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ideal_prod r p m = ideal_prod r p (ring_carrier r:A->bool)`
  MP_TAC THENL
   [ASM_SIMP_TAC[IDEAL_PROD_CARRIER] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IDEAL_PROD_SUBSET_LEFT THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET];
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o
        check (fun th -> concl th = `ideal_prod r m (L:A->bool) = p`)) THEN
      TRANS_TAC SUBSET_TRANS `ideal_prod r m (p:A->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
        MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `p:A->bool`]
          IDEAL_PROD_COMM) THEN
        ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; SUBSET_REFL]]];
    DISCH_TAC] THEN
  USE_THEN "inv" (MP_TAC o SPEC `p:A->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`k':A->bool`; `e:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = ring_carrier r:A->bool` MP_TAC THENL
   [MATCH_MP_TAC INVERTIBLE_IDEAL_PROD_CANCEL THEN
    MAP_EVERY EXISTS_TAC [`r:A ring`; `p:A->bool`; `k':A->bool`; `e:A`] THEN
    ASM_REWRITE_TAC[RING_IDEAL_CARRIER];
    ASM_MESON_TAC[MAXIMAL_IMP_PROPER_IDEAL; PROPER_IDEAL_ALT]]);;

(* The characterization: a domain is Dedekind iff its nonzero ideals are    *)
(* invertible.                                                               *)

let DEDEKIND_EQ_IDEALS_INVERTIBLE = prove
 (`!r:A ring.
        dedekind_domain r <=>
        integral_domain r /\
        !j. ring_ideal r j /\ ~(j = {ring_0 r})
            ==> ?k e. ring_ideal r k /\ e IN ring_carrier r /\
                      ~(e = ring_0 r) /\
                      ideal_prod r j k = ideal_generated r {e}`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `j:A->bool`]
      DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[dedekind_domain] THEN
    ASM_SIMP_TAC[INVERTIBLE_IDEALS_IMP_NOETHERIAN;
                 INVERTIBLE_IDEALS_IMP_INTEGRALLY_CLOSED] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL THEN
    ASM_REWRITE_TAC[]]);;

(* The same with fractional ideals: r is Dedekind iff J J^-1 = h(r) for every *)
(* fractional ideal J of r in a field of fractions k.                        *)

let DEDEKIND_EQ_FRACTIONAL_IDEALS_INVERTIBLE = prove
 (`!r k (h:A->B).
        field_of_fractions (r,k) h
        ==> (dedekind_domain r <=>
             !J. fractional_ideal (r,k) h J
                 ==> ring_span (r,k) h
                       (ring_setmul k J (fractional_ideal_inv (r,k) h J)) =
                     IMAGE h (ring_carrier r))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[DEDEKIND_FRACTIONAL_IDEAL_MUL_INV]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) THEN
  REWRITE_TAC[DEDEKIND_EQ_IDEALS_INVERTIBLE] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `fractional_ideal (r,k) (h:A->B) (IMAGE h j)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IMP_FRACTIONAL_IDEAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                 `fractional_ideal_inv (r,k) (h:A->B) (IMAGE h j)`]
    FRACTIONAL_IDEAL_SCALED_IDEAL) THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:A`; `m:A->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m:A->bool`; `d:A`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `IMAGE (h:A->B) j`;
                 `fractional_ideal_inv (r,k) (h:A->B) (IMAGE h j)`;
                 `ring_1 r:A`; `j:A->bool`; `d:A`; `m:A->bool`]
    FRACTIONAL_IDEAL_SCALED_IDEAL_MUL) THEN
  ASM_SIMP_TAC[FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV; RING_1] THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:A. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:A->B) s`) THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RING_MUL_LID THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_IDEAL_IMP_SUBSET;
                  SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_LID; GSYM IMAGE_HOMOMORPHISM_MUL; SUBSET_REFL] THEN
  SUBGOAL_THEN
   `IMAGE (ring_mul r d) (ring_carrier r) = ideal_generated r {d:A}`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM IDEAL_PROD_SCALE; RING_IDEAL_CARRIER] THEN
    MATCH_MP_TAC IDEAL_PROD_CARRIER THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!(f:A->B) u. (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
                 s SUBSET u /\ t SUBSET u
                 ==> IMAGE f t = IMAGE f s ==> s = t`) THEN
  EXISTS_TAC `ring_carrier r:A->bool` THEN
  REWRITE_TAC[ideal_prod; IDEAL_GENERATED_SUBSET] THEN
  ASM_MESON_TAC[RING_MONOMORPHISM_INJECTIVE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* A Noetherian domain whose localizations at the nonzero primes are DVRs is *)
(* Dedekind.                                                                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM = prove
 (`!r p:A->bool.
        integral_domain r /\ prime_ideal r p
        ==> ring_monomorphism
             (r,ring_localization r (ring_carrier r DIFF p))
             (ring_fractionate r (ring_carrier r DIFF p))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_FRACTIONATE_GEN; RING_MULTSYS_NONPRIME] THEN
  ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; INTEGRAL_DOMAIN_REGULAR] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL]);;

(* Nonzero primes are maximal: for p SUBSET m maximal, p and m extend to     *)
(* nonzero primes of the DVR r_m, which has only one nonzero prime.          *)

let LOCALLY_DVR_PRIME_IMP_MAXIMAL = prove
 (`!r p:A->bool.
        integral_domain r /\
        (!q. prime_ideal r q /\ ~(q = {ring_0 r})
             ==> DVR(ring_localization r (ring_carrier r DIFF q))) /\
        prime_ideal r p /\ ~(p = {ring_0 r})
        ==> maximal_ideal r p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A->bool`] MAXIMAL_SUPERIDEAL_EXISTS) THEN
  ASM_SIMP_TAC[PRIME_IMP_PROPER_IDEAL; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `p:A->bool = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_PRIME_IDEAL) THEN
  SUBGOAL_THEN `~(m = {ring_0 r:A})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL; SET_RULE
     `(z:A) IN p /\ p SUBSET {z} ==> p = {z}`];
    ALL_TAC] THEN
  ABBREV_TAC `s = ring_carrier r DIFF (m:A->bool)` THEN
  SUBGOAL_THEN `ring_multsys r (s:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[RING_MULTSYS_NONPRIME]; ALL_TAC] THEN
  SUBGOAL_THEN `p INTER s = {} /\ m INTER (s:A->bool) = {}`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DVR(ring_localization r (s:A->bool))` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `P' = {ring_localequiv r s (a,b) | a,b | (a:A) IN p /\ b IN s}` THEN
  SUBGOAL_THEN
   `prime_ideal (ring_localization r s) (P':(A#A->bool)->bool) /\
    prime_ideal (ring_localization r s)
     {ring_localequiv r s (a,b) | a,b | (a:A) IN m /\ b IN s}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P'" THEN ASM_SIMP_TAC[PRIME_IDEAL_LOCALIZATION];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(P' = {ring_0(ring_localization r (s:A->bool))})`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `?a:A. a IN p /\ ~(a = ring_0 r)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL; SET_RULE
       `(z:A) IN s /\ ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)`];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!x:A#A->bool. x IN s /\ ~(x = z) ==> ~(s = {z})`) THEN
    EXISTS_TAC `ring_fractionate r s (a:A)` THEN CONJ_TAC THENL
     [EXPAND_TAC "P'" THEN REWRITE_TAC[ring_fractionate; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`a:A`; `ring_1 r:A`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ring_multsys];
      MP_TAC(ISPECL [`r:A ring`; `m:A->bool`]
        INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`r:A ring`; `ring_localization r (s:A->bool)`;
                     `ring_fractionate r (s:A->bool)`; `a:A`]
        RING_MONOMORPHISM_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[PRIME_IMP_RING_IDEAL; RING_IDEAL_IMP_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(P':(A#A->bool)->bool) =
    {ring_localequiv r s (a,b) | a,b | (a:A) IN m /\ b IN s}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_localization r (s:A->bool)`; `P':(A#A->bool)->bool`]
      DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL) THEN
    ASM_SIMP_TAC[DVR_IMP_DEDEKIND; maximal_ideal] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC
     `{ring_localequiv r s (a,b) | a,b | (a:A) IN m /\ b IN s}` o
     CONJUNCT2) THEN
    ASM_SIMP_TAC[PRIME_IMP_PROPER_IDEAL; PSUBSET] THEN
    MATCH_MP_TAC(TAUT `p ==> ~(p /\ ~q) ==> q`) THEN
    EXPAND_TAC "P'" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `p:A->bool`; `x:A`; `ring_1 r:A`]
    RING_LOCALEQUIV_IN_LOCALIZED_IDEAL) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ring_multsys; MAXIMAL_IDEAL_IMP_SUBSET; SUBSET];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`x:A`; `ring_1 r:A`] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[ring_multsys]);;

(* Integrally closed: for a homogeneous relation of a and b, the ideal L of  *)
(* the y with b | y a is not proper, else b | a in r_m for a maximal m above  *)
(* L would put a denominator from outside m into L.                          *)

let LOCALLY_DVR_IMP_INTEGRALLY_CLOSED = prove
 (`!r:A ring.
        integral_domain r /\
        (!q. prime_ideal r q /\ ~(q = {ring_0 r})
             ==> DVR(ring_localization r (ring_carrier r DIFF q)))
        ==> integrally_closed r`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INTEGRALLY_CLOSED_ALT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`; `c:num->A`; `n:num`] THEN STRIP_TAC THEN
  ABBREV_TAC
   `L = {y:A | y IN ring_carrier r /\ ring_divides r b (ring_mul r y a)}` THEN
  SUBGOAL_THEN `ring_ideal r (L:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[RING_IDEAL; SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[] THEN ASM_SIMP_TAC[RING_0; RING_MUL_LZERO; RING_DIVIDES_0] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RING_ADD; RING_MUL] THENL
     [ASM_SIMP_TAC[RING_ADD_RDISTRIB] THEN MATCH_MP_TAC RING_DIVIDES_ADD THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[GSYM RING_MUL_ASSOC] THEN
      MATCH_MP_TAC RING_DIVIDES_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `ring_1 r:A IN L` THENL
   [UNDISCH_TAC `ring_1 r:A IN L` THEN EXPAND_TAC "L" THEN
    ASM_SIMP_TAC[IN_ELIM_THM; RING_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `L:A->bool`] MAXIMAL_SUPERIDEAL_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PROPER_IDEAL_ALT] THEN ASM_MESON_TAC[RING_1];
    DISCH_THEN(X_CHOOSE_THEN `m:A->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(b:A) IN L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC[RING_DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m = {ring_0 r:A})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_PRIME_IDEAL) THEN
  ABBREV_TAC `s = ring_carrier r DIFF (m:A->bool)` THEN
  SUBGOAL_THEN `ring_multsys r (s:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[RING_MULTSYS_NONPRIME]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_monomorphism (r,ring_localization r s)
                      (ring_fractionate r (s:A->bool))`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `integrally_closed (ring_localization r (s:A->bool))`
  MP_TAC THENL
   [MATCH_MP_TAC PID_IMP_INTEGRALLY_CLOSED THEN
    SUBGOAL_THEN `DVR(ring_localization r (s:A->bool))` MP_TAC THENL
     [EXPAND_TAC "s" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[DVR]];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRALLY_CLOSED_ALT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`ring_fractionate r s (a:A)`; `ring_fractionate r s (b:A)`;
    `\i. ring_fractionate r s ((c:num->A) i)`; `n:num`] o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_FRACTIONATE_IN_CARRIER] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `ring_localization r (s:A->bool)`;
                     `ring_fractionate r (s:A->bool)`; `b:A`]
        RING_MONOMORPHISM_EQ_0) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `ring_localization r (s:A->bool)`;
                   `ring_fractionate r (s:A->bool)`; `a:A`; `b:A`;
                   `c:num->A`; `n:num`]
      INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && rand(concl th) = `ring_0 r:A`)) THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ring_divides; RING_FRACTIONATE_IN_CARRIER] THEN
  ASM_SIMP_TAC[RING_LOCALIZATION_CARRIER; IN_ELIM_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z:A#A->bool`; `t:A`; `u:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)
    MP_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    lhand(concl th) = `z:A#A->bool`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_multsys]) THEN
  SUBGOAL_THEN `(u:A) IN ring_carrier r /\ ~(u IN m)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(u:A) IN s` THEN EXPAND_TAC "s" THEN SIMP_TAC[IN_DIFF];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ring_fractionate; RING_LOCALIZATION_MUL] THEN
  ASM_SIMP_TAC[GSYM RING_LOCALEQUIV_EQUIV; RING_MUL; RING_LOCALEQUIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  SUBGOAL_THEN `(v:A) IN ring_carrier r /\ ~(v = ring_0 r)` STRIP_ASSUME_TAC
  THENL
   [UNDISCH_TAC `(v:A) IN s` THEN EXPAND_TAC "s" THEN REWRITE_TAC[IN_DIFF] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[IN_RING_IDEAL_0; MAXIMAL_IMP_RING_IDEAL];
    ALL_TAC] THEN
  UNDISCH_TAC `~((u:A) IN m)` THEN MATCH_MP_TAC(TAUT `q ==> ~q ==> p`) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ring_divides] THEN ASM_SIMP_TAC[RING_MUL] THEN
  EXISTS_TAC `t:A` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `ring_mul r v (ring_sub r (ring_mul r a (ring_mul r (ring_1 r) u))
                             (ring_mul r (ring_mul r b t) (ring_1 r))) =
    ring_0 r:A` THEN
  ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_RID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_sub r (ring_mul r a u) (ring_mul r b t) = ring_0 r:A`
  MP_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `v:A`;
                   `ring_sub r (ring_mul r a u) (ring_mul r b t):A`]
      INTEGRAL_DOMAIN_MUL_EQ_0) THEN
    ASM_SIMP_TAC[RING_SUB; RING_MUL] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    UNDISCH_TAC
     `ring_mul r v (ring_sub r (ring_mul r a u)
                               (ring_mul r (ring_mul r b t) (ring_1 r))) =
      ring_0 r:A` THEN
    ASM_SIMP_TAC[RING_MUL; RING_MUL_RID];
    ASM_SIMP_TAC[RING_SUB_EQ_0; RING_MUL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_MUL_SYM THEN
    ASM_REWRITE_TAC[]]);;

let DEDEKIND_EQ_LOCALIZATIONS_DVR = prove
 (`!r:A ring.
        dedekind_domain r <=>
        integral_domain r /\ noetherian_ring r /\
        !p. prime_ideal r p /\ ~(p = {ring_0 r})
            ==> DVR(ring_localization r (ring_carrier r DIFF p))`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN; DEDEKIND_IMP_NOETHERIAN;
             DVR_LOCALIZATION];
    STRIP_TAC THEN ASM_REWRITE_TAC[dedekind_domain] THEN
    ASM_SIMP_TAC[LOCALLY_DVR_IMP_INTEGRALLY_CLOSED] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_DVR_PRIME_IMP_MAXIMAL THEN
    ASM_REWRITE_TAC[]]);;
