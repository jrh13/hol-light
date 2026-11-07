(* ========================================================================= *)
(* Baker theorem on linear forms in logarithms: the effective lower bounds.  *)
(*                                                                           *)
(* Purpose: the Baker-Feldman bound (Baker, Transcendental Number Theory,    *)
(* Thm 3.1) and its version for independent logarithms. Throughout, lg 1,    *)
(* ..., lg n are complex numbers with cexp(lg r) algebraic (any choice of    *)
(* logarithms), and "beta of degree <= Dx and height <= B" means that beta   *)
(* is a root of an integer polynomial a 0 + ... + a d x^d with 1 <= d <= Dx, *)
(* a d <> 0 and all |a i| <= B.                                              *)
(*                                                                           *)
(* Main results:                                                             *)
(* BAKER_LOWER_BOUND_INDEPENDENT (lg 1, ..., lg n linearly independent over  *)
(* the rationals): there is C such that for all B >= 2 and all beta 0, ...,  *)
(* beta n of degree <= Dx and height <= B, not all zero,                     *)
(*     B^-C <= |beta 0 + beta 1 lg 1 + ... + beta n lg n|.                   *)
(* Proof: take the largest r0 with beta r0 <> 0. If r0 = 0 the simple root   *)
(* bound gives |beta 0| >= B^-2; otherwise apply BAKER_CORE_EXISTS_PREFIX    *)
(* (BAKER_CORE_EXISTS for the prefix lg 1, ..., lg r0 of the family) with    *)
(* the beta j as extra variables and the coordinate projections as the g j.  *)
(* BAKER_FELDMAN (arbitrary logarithms, Thm 3.1): there is C such that for   *)
(* all B >= 2 and all beta j of degree <= Dx and height <= B,                *)
(* Lambda = beta 0 + sum beta r lg r is either 0 or |Lambda| >= B^-C.        *)
(* Proof: by INTEGER_INDEPENDENT_SUBFAMILY there are an independent          *)
(* subfamily lg(sg 1), ..., lg(sg t) and integers N <> 0, c r s with         *)
(* N lg r = sum_s c r s lg(sg s), hence (LINEAR_FORM_SUBFAMILY)              *)
(*     N Lambda = N beta 0 + sum_s gamma_s lg(sg s),                         *)
(*     gamma_s = sum_r c r s beta r (a linear intpoly in the betas).         *)
(* If all gamma_s = 0 then Lambda = beta 0 <> 0 and the simple root bound    *)
(* applies; otherwise BAKER_CORE_EXISTS_PREFIX is applied as in the          *)
(* independent case, with the largest r0 such that gamma_r0 <> 0.            *)
(*                                                                           *)
(* Uses: Baker/explicit.ml (BAKER_CORE_EXISTS), Baker/simple.ml              *)
(* (ALGEBRAIC_ROOT_LOWER_BOUND_POW), Baker/bridge.ml                         *)
(* (ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT_1), Baker/intpoly.ml (intpoly and       *)
(* INTPOLY_VAR, INTPOLY_CMUL, INTPOLY_LINEAR, INTPOLY_MONO), Baker/prelim.ml *)
(* (VSUM_NUMSEG_SPLIT_LAST).                                                 *)
(* ========================================================================= *)

needs "Baker/bridge.ml";;
needs "Baker/simple.ml";;
needs "Baker/explicit.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Independent logarithms. BAKER_CORE_EXISTS_PREFIX is BAKER_CORE_EXISTS for *)
(* the prefix lg 1, ..., lg r0 of an independent family lg 1, ..., lg n.     *)
(* ------------------------------------------------------------------------- *)

let BAKER_CORE_EXISTS_PREFIX = prove
 (`!n m lg (a:num->num->real) (d:num->num) (H:num->real) (e:num->num) G0 Dx
    r0.
     1 <= r0 /\ r0 <= n /\ 1 <= Dx /\ &1 <= G0 /\
     (!r. r IN 1..n
          ==> 1 <= d r /\ &1 <= H r /\
              (!j. integer(a r j) /\ abs(a r j) <= H r) /\
              ~(a r (d r) = &0) /\
              vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0)) /\
     (!b. (!r. r IN 1..n ==> integer(b r)) /\
          vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
          ==> !r. r IN 1..n ==> b r = &0)
     ==> ?C. !B (theta:num->complex) (g:num->(num->complex)->complex)
               (dx:num->num) (ax:num->num->real).
           &2 <= B /\
           (!r. r IN 1..r0 ==> theta r = cexp(lg r)) /\
           (!r. r IN (r0 + 1)..(r0 + m)
                ==> 1 <= dx r /\ dx r <= Dx /\
                    (!j. integer(ax r j) /\ abs(ax r j) <= B) /\
                    ~(ax r (dx r) = &0) /\
                    vsum(0..dx r) (\j. Cx(ax r j) * theta r pow j) = Cx(&0)) /\
           (!j. j <= r0 ==> intpoly (1..(r0 + m)) e G0 (g j)) /\
           ~(g r0 theta = Cx(&0))
           ==> inv(B pow C) <=
               norm(g 0 theta + vsum(1..r0) (\r. g r theta * lg r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`r0:num`; `m:num`; `lg:num->complex`;
                       `a:num->num->real`; `d:num->num`; `H:num->real`;
                       `e:num->num`; `G0:real`; `Dx:num`]
                      BAKER_CORE_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `a:num->num->real` (concl th))) THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    X_GEN_TAC `b:num->real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o BETA_RULE o
      SPEC `\r:num. if r <= r0 then (b:num->real) r else &0` o
      check (fun th ->
        is_forall(concl th) &&
        type_of(fst(dest_forall(concl th))) = `:num->real`)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
        COND_CASES_TAC THEN REWRITE_TAC[INTEGER_CLOSED] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && is_comb(lhand(concl th)))) THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC
       `vsum(1..r0) (\r. Cx(if r <= r0 then (b:num->real) r else &0) *
                         (lg:num->complex) r)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_SUPERSET THEN
        REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
        SUBGOAL_THEN `~(r <= r0)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_ARITH_TAC; REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO]];
        MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
        REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(fun th -> X_GEN_TAC `r:num` THEN DISCH_TAC THEN
        MP_TAC(SPEC `r:num` th)) THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_NUMSEG] o check (fun th ->
        concl th = `(r:num) IN 1..r0`)) THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]]);;

let BAKER_LOWER_BOUND_INDEPENDENT = prove
 (`!n (lg:num->complex) (a:num->num->real) (d:num->num) (H:num->real) Dx.
     1 <= n /\ 1 <= Dx /\
     (!r. r IN 1..n
          ==> 1 <= d r /\ &1 <= H r /\
              (!j. integer(a r j) /\ abs(a r j) <= H r) /\
              ~(a r (d r) = &0) /\
              vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0)) /\
     (!b. (!r. r IN 1..n ==> integer(b r)) /\
          vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
          ==> !r. r IN 1..n ==> b r = &0)
     ==> ?C. !B (beta:num->complex) (db:num->num) (ab:num->num->real).
           &2 <= B /\
           (!j. j <= n
                ==> 1 <= db j /\ db j <= Dx /\
                    (!i. integer(ab j i) /\ abs(ab j i) <= B) /\
                    ~(ab j (db j) = &0) /\
                    vsum(0..db j) (\i. Cx(ab j i) * beta j pow i) = Cx(&0)) /\
           ~(!j. j <= n ==> beta j = Cx(&0))
           ==> inv(B pow C) <= norm(beta 0 + vsum(1..n) (\r. beta r * lg r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(GEN `r0:num` (ISPECL
   [`n:num`; `r0 + 1`; `lg:num->complex`; `a:num->num->real`;
    `d:num->num`; `H:num->real`; `\r:num. 1`; `&1`; `Dx:num`; `r0:num`]
   BAKER_CORE_EXISTS_PREFIX)) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_TAC `Cf:num->num` o
             REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  EXISTS_TAC `nsum(1..n) Cf + 2` THEN
  MAP_EVERY X_GEN_TAC [`B:real`; `beta:num->complex`; `db:num->num`;
                       `ab:num->num->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?r0. (r0 <= n /\ ~((beta:num->complex) r0 = Cx(&0))) /\
         (!j. j <= n /\ ~(beta j = Cx(&0)) ==> j <= r0)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\j. j <= n /\ ~((beta:num->complex) j = Cx(&0))` num_MAX) THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        is_neg(concl th) && is_forall(rand(concl th)))) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP];
      EXISTS_TAC `n:num` THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..n) (\r. (beta:num->complex) r * lg r) =
    vsum(1..r0) (\r. beta r * lg r)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(beta:num->complex) r = Cx(&0)`
     (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `r0:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c <= nsum(1..n) Cf + 2
        ==> inv(B pow (nsum(1..n) Cf + 2)) <= inv(B pow c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `r0 = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_EQ; GSYM COMPLEX_VEC_0;
                VECTOR_ADD_RID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(B pow 2)` THEN
    CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      is_forall(concl th) && free_in `ab:num->num->real` (concl th))) THEN
    REWRITE_TAC[LE_0] THEN STRIP_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_ROOT_LOWER_BOUND_POW THEN
    MAP_EVERY EXISTS_TAC [`(ab:num->num->real) 0`; `(db:num->num) 0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r0:num` o check (fun th ->
    is_forall(concl th) && free_in `Cf:num->num` (concl th) &&
    can (find_term ((=) `1 <= r0`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`B:real`;
    `\r. if r <= r0 then cexp((lg:num->complex) r)
         else (beta:num->complex)(r - (r0 + 1))`;
    `\j (x:num->complex). x(r0 + 1 + j)`;
    `\r. (db:num->num)(r - (r0 + 1))`;
    `\r. (ab:num->num->real)(r - (r0 + 1))`]) THEN
  BETA_TAC THEN
  REWRITE_TAC[ARITH_RULE `~(r0 + 1 + j <= r0)`;
              ARITH_RULE `(r0 + 1 + j) - (r0 + 1) = j`] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[IN_NUMSEG];
      X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(r <= r0)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `ab:num->num->real` (concl th))) THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC INTPOLY_VAR THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_LE_REFL; LE_REFL] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> b <= c ==> a <= c`) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `a <= s ==> a <= s + 2`) THEN
  MP_TAC(ISPECL [`Cf:num->num`; `1..n`; `r0:num`] NSUM_DELETE) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A maximal subfamily of lg 1, ..., lg n that is linearly independent       *)
(* over the rationals, with integer relations for the whole family.          *)
(* ------------------------------------------------------------------------- *)

let INTEGER_INDEPENDENT_SUBFAMILY = prove
 (`!n (lg:num->complex).
     ?t sg N (c:num->num->real).
       t <= n /\ (!s. s IN 1..t ==> sg s IN 1..n) /\
       (!b. (!s. s IN 1..t ==> integer(b s)) /\
            vsum(1..t) (\s. Cx(b s) * lg(sg s)) = Cx(&0)
            ==> !s. s IN 1..t ==> b s = &0) /\
       integer N /\ ~(N = &0) /\
       (!r s. r IN 1..n /\ s IN 1..t ==> integer(c r s)) /\
       (!r. r IN 1..n
            ==> Cx N * lg r = vsum(1..t) (\s. Cx(c r s) * lg(sg s)))`,
  INDUCT_TAC THEN GEN_TAC THENL
   [MAP_EVERY EXISTS_TAC [`0`; `\s:num. 0`; `&1`; `\r:num s:num. &0`] THEN
    REWRITE_TAC[NUMSEG_CLAUSES; ARITH_EQ; NOT_IN_EMPTY; LE_REFL;
                INTEGER_CLOSED; REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:num` (X_CHOOSE_THEN `sg:num->num`
    (X_CHOOSE_THEN `N:real` (X_CHOOSE_THEN `c:num->num->real`
      STRIP_ASSUME_TAC))) o SPEC `lg:num->complex`) THEN
  ASM_CASES_TAC
   `!b. (!s. s IN 1..SUC t ==> integer(b s)) /\
        vsum(1..SUC t)
         (\s. Cx(b s) * (lg:num->complex)
                         (if s = SUC t then SUC n else sg s)) = Cx(&0)
        ==> !s. s IN 1..SUC t ==> b s = &0` THENL
   [MAP_EVERY EXISTS_TAC
     [`SUC t`; `\s. if s = SUC t then SUC n else (sg:num->num) s`;
      `N:real`;
      `\r s. if r = SUC n then (if s = SUC t then N else &0)
             else if s = SUC t then &0 else (c:num->num->real) r s`] THEN
    BETA_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `s:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      COND_CASES_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(sg:num->num) s IN 1..n` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC];
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      MP_TAC(ISPECL
       [`\s. Cx(if r = SUC n then &0 else (c:num->num->real) r s) *
             (lg:num->complex)(sg s)`;
        `\s. Cx(if r = SUC n then (if s = SUC t then N else &0)
                else if s = SUC t then &0 else (c:num->num->real) r s) *
             (lg:num->complex)(if s = SUC t then SUC n else sg s)`;
        `t:num`] VSUM_NUMSEG_SPLIT_LAST) THEN
      ANTS_TAC THENL
       [X_GEN_TAC `s:num` THEN DISCH_TAC THEN BETA_TAC THEN
        SUBGOAL_THEN `~(s = SUC t)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN REWRITE_TAC[]] THEN
      ASM_CASES_TAC `r = SUC n` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[COMPLEX_MUL_LZERO] THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_0; VECTOR_ADD_LID;
                  VECTOR_ADD_RID] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL
   [`\s. Cx((b:num->real) s) * (lg:num->complex)(sg s)`;
    `\s. Cx((b:num->real) s) *
         (lg:num->complex)(if s = SUC t then SUC n else sg s)`;
    `t:num`] VSUM_NUMSEG_SPLIT_LAST) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `s:num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(s = SUC t)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    BETA_TAC THEN REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC] THEN
  SUBGOAL_THEN `~((b:num->real)(SUC t) = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b:num->real` o check (fun th ->
      is_forall(concl th) &&
      type_of(fst(dest_forall(concl th))) = `:num->real`)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `s:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC;
        UNDISCH_TAC
         `vsum(1..t) (\s. Cx((b:num->real) s) * (lg:num->complex)(sg s)) +
          Cx(b(SUC t)) * lg(SUC n) = Cx(&0)` THEN
        ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID]];
      DISCH_TAC THEN UNDISCH_TAC `~((b:num->real) k = &0)` THEN
      REWRITE_TAC[] THEN UNDISCH_TAC `k IN 1..SUC t` THEN
      REWRITE_TAC[IN_NUMSEG] THEN ASM_CASES_TAC `k = SUC t` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`t:num`; `sg:num->num`; `N * (b:num->real)(SUC t)`;
    `\r s. if r = SUC n then --(N * (b:num->real) s)
           else b(SUC t) * (c:num->num->real) r s`] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(sg:num->num) s IN 1..n` MP_TAC THENL
     [ASM_SIMP_TAC[]; REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC];
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC INTEGER_MUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ASM_REWRITE_TAC[REAL_ENTIRE];
    MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN `integer((b:num->real) s)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC;
        SIMP_TAC[INTEGER_CLOSED; ASSUME `integer(N:real)`]];
      SUBGOAL_THEN
       `integer((b:num->real)(SUC t)) /\ integer((c:num->num->real) r s)`
      MP_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
        SIMP_TAC[INTEGER_CLOSED]]];
    X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_CASES_TAC `r = SUC n` THEN ASM_REWRITE_TAC[] THENL
     [SIMP_TAC[CX_NEG; CX_MUL; COMPLEX_MUL_LNEG; GSYM COMPLEX_MUL_ASSOC;
               VSUM_NEG; VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
      UNDISCH_TAC
       `vsum(1..t) (\s. Cx((b:num->real) s) * (lg:num->complex)(sg s)) +
        Cx(b(SUC t)) * lg(SUC n) = Cx(&0)` THEN
      CONV_TAC COMPLEX_RING;
      SIMP_TAC[CX_MUL; GSYM COMPLEX_MUL_ASSOC; VSUM_COMPLEX_LMUL;
               FINITE_NUMSEG] THEN
      SUBGOAL_THEN
       `Cx N * (lg:num->complex) r =
        vsum(1..t) (\s. Cx((c:num->num->real) r s) * lg(sg s))`
      MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC;
        CONV_TAC COMPLEX_RING]]]);;

(* ------------------------------------------------------------------------- *)
(* Arbitrary logarithms: the Baker-Feldman bound.                            *)
(* ------------------------------------------------------------------------- *)

let LINEAR_FORM_SUBFAMILY = prove
 (`!n t (lg:num->complex) (sg:num->num) N (c:num->num->real)
    (beta:num->complex).
     (!r. r IN 1..n ==> Cx N * lg r = vsum(1..t) (\s. Cx(c r s) * lg(sg s)))
     ==> Cx N * (beta 0 + vsum(1..n) (\r. beta r * lg r)) =
         Cx N * beta 0 +
         vsum(1..t) (\s. vsum(1..n) (\r. Cx(c r s) * beta r) * lg(sg s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_ADD_LDISTRIB] THEN
  AP_TERM_TAC THEN SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  TRANS_TAC EQ_TRANS
   `vsum(1..n) (\r. vsum(1..t) (\s. (beta:num->complex) r *
                   Cx((c:num->num->real) r s) * lg((sg:num->num) s)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    BETA_TAC THEN SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC COMPLEX_RING;
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    BETA_TAC THEN SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    CONV_TAC COMPLEX_RING]);;


let BAKER_FELDMAN = prove
 (`!n (lg:num->complex) Dx.
     (!r. r IN 1..n ==> algebraic_number(cexp(lg r)))
     ==> ?C. !B (beta:num->complex) (db:num->num) (ab:num->num->real).
           &2 <= B /\
           (!j. j <= n
                ==> 1 <= db j /\ db j <= Dx /\
                    (!i. integer(ab j i) /\ abs(ab j i) <= B) /\
                    ~(ab j (db j) = &0) /\
                    vsum(0..db j) (\i. Cx(ab j i) * beta j pow i) = Cx(&0)) /\
           ~(beta 0 + vsum(1..n) (\r. beta r * lg r) = Cx(&0))
           ==> inv(B pow C) <= norm(beta 0 + vsum(1..n) (\r. beta r * lg r))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `Dx = 0` THENL
   [EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      is_forall(concl th) && free_in `db:num->num` (concl th))) THEN
    ASM_REWRITE_TAC[LE_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN `F` CONTR_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Dx` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d (a:num->num->real) (H:num->real).
      !r. r IN 1..n
          ==> 1 <= d r /\ &1 <= H r /\
              (!j. integer(a r j) /\ abs(a r j) <= H r) /\
              ~(a r (d r) = &0) /\
              vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT_1 THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `lg:num->complex`] INTEGER_INDEPENDENT_SUBFAMILY) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`t:num`; `sg:num->num`; `N:real`; `c:num->num->real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `G = &1 + abs N +
        sum(1..t) (\s. sum(1..n) (\r. abs((c:num->num->real) r s)))` THEN
  SUBGOAL_THEN
   `abs N <= G /\
    (!s. s IN 1..t ==> sum(1..n) (\r. abs((c:num->num->real) r s)) <= G) /\
    &1 <= G`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    SUBGOAL_THEN
     `!s. &0 <= sum(1..n) (\r. abs((c:num->num->real) r s))`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REWRITE_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= sum(1..t) (\s. sum(1..n) (\r. abs((c:num->num->real) r s)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `N:real` REAL_ABS_POS) THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:num` THEN DISCH_TAC THEN
      MP_TAC(BETA_RULE(ISPECL
       [`\s. sum(1..n) (\r. abs((c:num->num->real) r s))`;
        `sum(1..t) (\s. sum(1..n) (\r. abs((c:num->num->real) r s)))`;
        `1..t`] SUM_POS_BOUND)) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL] THEN
      DISCH_THEN(MP_TAC o SPEC `s:num`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r IN 1..t
        ==> 1 <= (d:num->num)((sg:num->num) r) /\
            &1 <= (H:num->real)(sg r) /\
            (!j. integer((a:num->num->real) (sg r) j) /\
                 abs(a (sg r) j) <= H(sg r)) /\
            ~(a (sg r) (d(sg r)) = &0) /\
            vsum(0..d(sg r))
             (\j. Cx(a (sg r) j) * cexp((lg:num->complex)(sg r)) pow j) =
            Cx(&0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `a:num->num->real` (concl th))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(GEN `r0:num` (BETA_RULE(ISPECL
   [`t:num`; `n + 1`; `\r. (lg:num->complex)((sg:num->num) r)`;
    `\r. (a:num->num->real)((sg:num->num) r)`;
    `\r. (d:num->num)((sg:num->num) r)`;
    `\r. (H:num->real)((sg:num->num) r)`;
    `\r:num. 1`; `G:real`; `Dx:num`; `r0:num`]
   BAKER_CORE_EXISTS_PREFIX))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `Cf:num->num` o
             REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  SUBGOAL_THEN `?K. abs N <= (&2:real) pow K` (X_CHOOSE_TAC `K:num`) THENL
   [UNDISCH_TAC `integer N` THEN REWRITE_TAC[integer] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN EXISTS_TAC `k:num` THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LT_POW2_REFL];
    ALL_TAC] THEN
  EXISTS_TAC `nsum(1..t) Cf + K + 2` THEN
  MAP_EVERY X_GEN_TAC [`B:real`; `beta:num->complex`; `db:num->num`;
                       `ab:num->num->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. m <= nsum(1..t) Cf + K + 2
        ==> inv(B pow (nsum(1..t) Cf + K + 2)) <= inv(B pow m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `gam = \s. vsum(1..n) (\r. Cx((c:num->num->real) r s) *
                              (beta:num->complex) r)` THEN
  SUBGOAL_THEN
   `Cx N * (beta 0 + vsum(1..n) (\r. beta r * lg r)) =
    Cx N * beta 0 + vsum(1..t) (\s. (gam:num->complex) s * lg(sg s))`
  ASSUME_TAC THENL
   [EXPAND_TAC "gam" THEN MATCH_MP_TAC LINEAR_FORM_SUBFAMILY THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `!s. s IN 1..t ==> (gam:num->complex) s = Cx(&0)` THENL
   [SUBGOAL_THEN
     `vsum(1..t) (\s. (gam:num->complex) s *
                     (lg:num->complex)((sg:num->num) s)) = Cx(&0)`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
      SIMP_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0; ASSUME
        `!s. s IN 1..t ==> (gam:num->complex) s = Cx(&0)`];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `beta 0 + vsum(1..n) (\r. (beta:num->complex) r * lg r) = beta 0`
    ASSUME_TAC THENL
     [UNDISCH_TAC
       `Cx N * (beta 0 + vsum(1..n) (\r. beta r * lg r)) =
        Cx N * beta 0 +
        vsum(1..t) (\s. (gam:num->complex) s * lg(sg s))` THEN
      ASM_REWRITE_TAC[COMPLEX_ADD_RID] THEN
      UNDISCH_TAC `~(N = &0)` THEN REWRITE_TAC[GSYM CX_INJ] THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((B:real) pow 2)` THEN
    CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      is_forall(concl th) && free_in `ab:num->num->real` (concl th))) THEN
    REWRITE_TAC[LE_0] THEN STRIP_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_ROOT_LOWER_BOUND_POW THEN
    MAP_EVERY EXISTS_TAC [`(ab:num->num->real) 0`; `(db:num->num) 0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r0. (r0 IN 1..t /\ ~((gam:num->complex) r0 = Cx(&0))) /\
         (!s. s IN 1..t /\ ~(gam s = Cx(&0)) ==> s <= r0)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\s. s IN 1..t /\ ~((gam:num->complex) s = Cx(&0))`
           num_MAX) THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        is_neg(concl th) && is_forall(rand(concl th)))) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP];
      EXISTS_TAC `t:num` THEN SIMP_TAC[IN_NUMSEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= r0 /\ r0 <= t /\ ~(r0 = 0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r0 IN 1..t` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..t) (\s. (gam:num->complex) s *
                     (lg:num->complex)((sg:num->num) s)) =
    vsum(1..r0) (\s. gam s * lg(sg s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(gam:num->complex) s = Cx(&0)`
     (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:num` o check (fun th ->
      is_forall(concl th) && free_in `r0:num` (concl th))) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `theta = \r. if r <= r0 then cexp((lg:num->complex)((sg:num->num) r))
                else (beta:num->complex)(r - (r0 + 1))` THEN
  ABBREV_TAC
   `g = \j (x:num->complex).
          if j = 0 then Cx N * x(r0 + 1)
          else vsum(1..n) (\r. Cx((c:num->num->real) r j) * x(r0 + 1 + r))` THEN
  SUBGOAL_THEN
   `(g:num->(num->complex)->complex) 0 theta = Cx N * beta 0`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN EXPAND_TAC "theta" THEN
    REWRITE_TAC[ARITH_RULE `~(r0 + 1 <= r0)`; SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. ~(j = 0) ==> (g:num->(num->complex)->complex) j theta = gam j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN EXPAND_TAC "theta" THEN EXPAND_TAC "gam" THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(r0 + 1 + r <= r0)`;
                    ARITH_RULE `(r0 + 1 + r) - (r0 + 1) = r`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r0:num` o check (fun th ->
    is_forall(concl th) && free_in `Cf:num->num` (concl th) &&
    can (find_term ((=) `1 <= r0`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`B:real`; `theta:num->complex`; `g:num->(num->complex)->complex`;
    `\r. (db:num->num)(r - (r0 + 1))`;
    `\r. (ab:num->num->real)(r - (r0 + 1))`]) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "theta" THEN SIMP_TAC[IN_NUMSEG];
      X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      EXPAND_TAC "theta" THEN
      SUBGOAL_THEN `~(r <= r0)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `ab:num->num->real` (concl th))) THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
      ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC INTPOLY_MONO THEN
        EXISTS_TAC `\r:num. 1` THEN EXISTS_TAC `abs N * &1` THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC INTPOLY_CMUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC INTPOLY_VAR THEN
          REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_LE_REFL] THEN
          ARITH_TAC;
          REWRITE_TAC[LE_REFL];
          ASM_REWRITE_TAC[REAL_MUL_RID]];
        SUBGOAL_THEN `1 <= j /\ j <= t` STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`j <= r0`; `~(j = 0)`; `r0 <= t`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        MATCH_MP_TAC INTPOLY_MONO THEN
        EXISTS_TAC `\r:num. 1` THEN
        EXISTS_TAC `sum(1..n) (\r. abs((c:num->num->real) r j))` THEN
        REPEAT CONJ_TAC THENL
         [MP_TAC(BETA_RULE(ISPECL
           [`1..(r0 + (n + 1))`; `\r. (c:num->num->real) r j`;
            `\r. r0 + 1 + r`; `1..n`] INTPOLY_LINEAR)) THEN
          REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
          X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
            UNDISCH_TAC `r <= n` THEN ARITH_TAC];
          REWRITE_TAC[LE_REFL];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]]];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..r0) (\r. (g:num->(num->complex)->complex) r theta *
                     lg((sg:num->num) r)) =
    vsum(1..r0) (\s. gam s * lg(sg s))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g:num->(num->complex)->complex) 0 theta +
    vsum(1..r0) (\s. (gam:num->complex) s * lg(sg s)) =
    Cx N * (beta 0 + vsum(1..n) (\r. beta r * lg r))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS `inv((B:real) pow (Cf(r0:num) + K))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `a <= s ==> a + k <= s + k + 2`) THEN
    MP_TAC(ISPECL [`Cf:num->num`; `nsum(1..t) Cf`; `1..t`]
                  NSUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (B:real) pow K /\ abs N <= B pow K`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(&2:real) pow K` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_INV_MUL; GSYM real_div] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; ASSUME `&0 < (B:real) pow K`] THEN
  TRANS_TAC REAL_LE_TRANS
   `abs N * norm(beta 0 + vsum(1..n) (\r. (beta:num->complex) r * lg r))` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]);;
