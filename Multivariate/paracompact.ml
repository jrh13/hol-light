(* ========================================================================= *)
(* More advanced or exotic results around paracompact spaces. This includes  *)
(* Nagata-Smirnov metrization results as well as Michael's characterization  *)
(* of paracompact spaces via closure-preserving closed refinements.          *)
(* ========================================================================= *)

needs "Multivariate/metric.ml";;

(* Engelking Section 5.2: Countably paracompact space *)
let countably_paracompact_space = new_definition
 `countably_paracompact_space (top:A topology) <=>
        !U. COUNTABLE U /\
            (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
            ==> ?V. (!v. v IN V ==> open_in top v) /\
                    UNIONS V = topspace top /\
                    (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                    locally_finite_in top V`;;

(* Paracompact implies countably paracompact *)
let PARACOMPACT_IMP_COUNTABLY_PARACOMPACT_SPACE = prove
 (`!top:A topology.
        paracompact_space top ==> countably_paracompact_space top`,
  GEN_TAC THEN REWRITE_TAC[paracompact_space; countably_paracompact_space] THEN
  DISCH_TAC THEN X_GEN_TAC `U:(A->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Corollary: Metrizable implies countably paracompact *)
let METRIZABLE_IMP_COUNTABLY_PARACOMPACT_SPACE = prove
 (`!top:A topology.
        metrizable_space top ==> countably_paracompact_space top`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC PARACOMPACT_IMP_COUNTABLY_PARACOMPACT_SPACE THEN
  MATCH_MP_TAC METRIZABLE_IMP_PARACOMPACT_SPACE THEN
  ASM_REWRITE_TAC[]);;

(* Forward direction of Dowker characterization: countably paracompact
   implies the shrinking condition. Does NOT need normality. *)
let COUNTABLY_PARACOMPACT_IMP_DOWKER = prove
 (`!top:A topology.
        countably_paracompact_space top
        ==> !f. (!n. closed_in top (f n)) /\
                (!n. f(SUC n) SUBSET f n) /\
                INTERS {f n | n IN (:num)} = {}
                ==> ?g. (!n. open_in top (g n)) /\
                        (!n. f n SUBSET g n) /\
                        INTERS {g n | n IN (:num)} = {}`,
  let DECREASING_CHAIN_SUBSET = prove
   (`!f:num->(A->bool).
          (!n. f(SUC n) SUBSET f n) ==> !m n. m <= n ==> f n SUBSET f m`,
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
    [REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[];
     REWRITE_TAC[LE] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      ASM SET_TAC[]]]) in
  GEN_TAC THEN REWRITE_TAC[countably_paracompact_space] THEN
  DISCH_TAC THEN X_GEN_TAC `f:num->(A->bool)` THEN STRIP_TAC THEN
  (* From INTERS = {}: every element avoids some f(n) *)
  SUBGOAL_THEN `!x:A. ?n:num. ~(x IN f n)` ASSUME_TAC THENL
  [GEN_TAC THEN
   UNDISCH_TAC `INTERS {(f:num->(A->bool)) n | n IN (:num)} = {}` THEN
   REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTERS; IN_ELIM_THM; IN_UNIV] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  (* Apply countable paracompactness to {topspace DIFF f(n)} *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `IMAGE (\n:num. topspace top DIFF (f:num->(A->bool)) n) (:num)`) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]; ALL_TAC] THEN
   CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN GEN_TAC THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
   REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    GEN_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t ==> t DIFF s SUBSET t`) THEN
    MATCH_MP_TAC CLOSED_IN_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_DIFF] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]];
   DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC)] THEN
  (* Skolemize the refinement to get nv *)
  SUBGOAL_THEN
    `?nv:(A->bool)->num. !v:A->bool. v IN V
        ==> v SUBSET topspace top DIFF (f:num->(A->bool))(nv v)`
    (X_CHOOSE_TAC `nv:(A->bool)->num`) THENL
  [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `v:A->bool` THEN
   ASM_CASES_TAC `(v:A->bool) IN V` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Define g(n) = UNIONS {v IN V | v meets f(n)} *)
  EXISTS_TAC
    `\n:num. UNIONS {v:A->bool | v IN V /\
                     ~(v INTER (f:num->(A->bool)) n = {})}` THEN
  REWRITE_TAC[] THEN
  (* Remove !x. ?n. ~(x IN f n) to reduce assumption count *)
  UNDISCH_THEN `!x:A. ?n:num. ~(x IN f n)` (K ALL_TAC) THEN
  CONJ_TAC THENL
  [(* g(n) is open: union of open sets from V *)
   GEN_TAC THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN CONJ_TAC THENL
  [(* f(n) SUBSET g(n) *)
   X_GEN_TAC `n:num` THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET o SPEC `n:num`) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(x:A) IN UNIONS V` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[IN_UNIONS] THEN
   DISCH_THEN(X_CHOOSE_THEN `v0:A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `v0:A->bool` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN
   ASM_REWRITE_TAC[IN_INTER];
   ALL_TAC] THEN
  (* INTERS {g n | n IN (:num)} = {} *)
  (* First prove pointwise: every x avoids some g(n) *)
  SUBGOAL_THEN
    `!x:A. ?n:num. ~(x IN UNIONS {v:A->bool | v IN V /\
                      ~(v INTER (f:num->(A->bool)) n = {})})`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN topspace top` THENL
   [ALL_TAC;
    (* x not in topspace: x not in any v IN V, so x not in g(0) *)
    EXISTS_TAC `0` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM; DE_MORGAN_THM] THEN
    X_GEN_TAC `w:A->bool` THEN
    ASM_CASES_TAC `(w:A->bool) IN V` THENL
    [DISJ2_TAC THEN
     UNDISCH_TAC `locally_finite_in top (V:(A->bool)->bool)` THEN
     REWRITE_TAC[locally_finite_in] THEN
     DISCH_THEN(MP_TAC o SPEC `w:A->bool` o CONJUNCT1) THEN
     ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
     ASM_REWRITE_TAC[]]] THEN
   (* x in topspace: use local finiteness to bound *)
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [locally_finite_in]) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `x:A`)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `FINITE {v:A->bool | v IN V /\ (x:A) IN v}`
     ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{v:A->bool | v IN V /\ ~(v INTER u = {})}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `w:A->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o SPEC `nv:(A->bool)->num` o
     MATCH_MP UPPER_BOUND_FINITE_SET) THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   EXISTS_TAC `N:num` THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
   X_GEN_TAC `w:A->bool` THEN
   DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)
     ASSUME_TAC) THEN
   (* w IN V, ~(w INTER f N = {}), x IN w *)
   FIRST_X_ASSUM(MP_TAC o SPEC `w:A->bool`) THEN
   ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
   SUBGOAL_THEN `(f:num->(A->bool)) N SUBSET f(nv(w:A->bool))`
     ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      MATCH_MP_TAC(SPECL [`(nv:(A->bool)->num) w`; `N:num`]
        (MATCH_MP DECREASING_CHAIN_SUBSET th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   UNDISCH_TAC
     `!v:A->bool. v IN V
        ==> v SUBSET topspace top DIFF (f:num->(A->bool))
              ((nv:(A->bool)->num) v)` THEN
   DISCH_THEN(MP_TAC o SPEC `w:A->bool`) THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `~((w:A->bool) INTER (f:num->(A->bool)) N = {})` THEN
   UNDISCH_TAC `(f:num->(A->bool)) N SUBSET f((nv:(A->bool)->num) w)` THEN
   SET_TAC[];
   ALL_TAC] THEN
  (* Now derive INTERS = {} from the pointwise claim *)
  MATCH_MP_TAC(SET_RULE `(!x:A. ~(x IN s)) ==> s = {}`) THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_INTERS] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN
  DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `UNIONS {v:A->bool | v IN V /\
             ~(v INTER (f:num->(A->bool)) (n0:num) = {})}`) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
   EXISTS_TAC `n0:num` THEN REWRITE_TAC[];
   DISCH_TAC THEN
   UNDISCH_TAC
     `~((y:A) IN UNIONS {v:A->bool | v IN V /\
         ~(v INTER (f:num->(A->bool)) (n0:num) = {})})` THEN
   ASM_REWRITE_TAC[]]);;

(* Backward direction of Dowker: Dowker condition + normality implies
   countably paracompact *)
let DOWKER_BACKWARD = prove
 (`!top:A topology.
        normal_space top /\
        (!f. (!n. closed_in top (f n)) /\
             (!n. f(SUC n) SUBSET f n) /\
             INTERS {f n | n IN (:num)} = {}
             ==> ?g. (!n. open_in top (g n)) /\
                     (!n. f n SUBSET g n) /\
                     INTERS {g n | n IN (:num)} = {})
        ==> countably_paracompact_space top`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "dowker")) THEN
  REWRITE_TAC[countably_paracompact_space] THEN
  X_GEN_TAC `U:(A->bool)->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `U:(A->bool)->bool = {}` THENL
  [EXISTS_TAC `{}:(A->bool)->bool` THEN
   UNDISCH_TAC `UNIONS U = topspace (top:A topology)` THEN
   ASM_REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY] THEN DISCH_TAC THEN
   REWRITE_TAC[locally_finite_in; NOT_IN_EMPTY] THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[NOT_IN_EMPTY];
   ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP(REWRITE_RULE[IMP_CONJ] COUNTABLE_AS_IMAGE)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num->A->bool` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FORALL_IN_IMAGE; IN_UNIV]) THEN
  UNDISCH_THEN `COUNTABLE(IMAGE (u:num->A->bool) (:num))` (K ALL_TAC) THEN
  REMOVE_THEN "dowker" (MP_TAC o SPEC
    `\n:num. topspace top DIFF
      UNIONS(IMAGE (u:num->A->bool) {i:num | i <= n})`) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
    REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN
    MATCH_MP_TAC(SET_RULE
      `(s:(A->bool)->bool) SUBSET t
       ==> u DIFF UNIONS t SUBSET u DIFF UNIONS s`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTERS;
                FORALL_IN_GSPEC; IN_UNIV] THEN
    X_GEN_TAC `x:A` THEN REWRITE_TAC[NOT_FORALL_THM] THEN
    ASM_CASES_TAC `(x:A) IN topspace top` THENL
    [SUBGOAL_THEN `?k:num. (x:A) IN u k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC
       `UNIONS(IMAGE (u:num->A->bool) (:num)) = topspace top` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `k:num` THEN
      REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[LE_REFL]];
     EXISTS_TAC `0` THEN ASM_REWRITE_TAC[IN_DIFF]]];
   DISCH_THEN(X_CHOOSE_THEN `g:num->A->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
    `?H:num->A->bool. !n. open_in top (H n) /\
      topspace top DIFF UNIONS(IMAGE (u:num->A->bool) {i | i <= n})
        SUBSET H n /\
      top closure_of H n SUBSET (g:num->A->bool) n`
    (X_CHOOSE_TAC `H:num->A->bool`) THENL
  [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NORMAL_SPACE_ALT]) THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
   MATCH_MP_TAC OPEN_IN_UNIONS THEN
   REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  EXISTS_TAC
    `IMAGE (\n:num. (u:num->A->bool) n INTER
      INTERS(IMAGE (H:num->A->bool) {i:num | i < n})) (:num)` THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
  CONJ_TAC THENL
  [(* V_n is open *)
   X_GEN_TAC `n:num` THEN
   ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[LT; EMPTY_GSPEC; NOT_IN_EMPTY; IMAGE_CLAUSES; INTERS_0;
                    INTER_UNIV];
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_INTERS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LT];
     REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
     REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
     EXISTS_TAC `0` THEN ASM_ARITH_TAC;
     GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN CONJ_TAC THENL
  [(* UNIONS V = topspace *)
   REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC(SET_RULE
      `(s:A->bool) SUBSET t ==> s INTER u SUBSET t`) THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n:num. (x:A) IN u n` MP_TAC THENL
    [UNDISCH_TAC
      `UNIONS(IMAGE (u:num->A->bool) (:num)) = topspace top` THEN
     REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
     DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
     MESON_TAC[];
     GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
     DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `n:num` THEN REWRITE_TAC[IN_INTER; IN_INTERS;
       FORALL_IN_IMAGE; IN_ELIM_THM] THEN
     ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN
       `(x:A) IN topspace top DIFF
        UNIONS(IMAGE (u:num->A->bool) {i:num | i <= j})` MP_TAC
     THENL
      [REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
       ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[NOT_EXISTS_THM;
                    TAUT `~(p /\ q) <=> p ==> ~q`] THEN
       X_GEN_TAC `i:num` THEN DISCH_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `j:num` THEN
       ASM_REWRITE_TAC[];
       FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC `j:num`) THEN
       REWRITE_TAC[SUBSET] THEN
       DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
       DISCH_THEN ACCEPT_TAC]]];
   ALL_TAC] THEN CONJ_TAC THENL
  [(* V refines U *)
   X_GEN_TAC `n:num` THEN
   EXISTS_TAC `(u:num->A->bool) n` THEN
   REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
   CONJ_TAC THENL [MESON_TAC[]; SET_TAC[]];
   ALL_TAC] THEN
  (* Locally finite *)
  REWRITE_TAC[locally_finite_in] THEN CONJ_TAC THENL
  [(* V_n SUBSET topspace *)
   REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `n:num` THEN
   MATCH_MP_TAC(SET_RULE
     `(s:A->bool) SUBSET t ==> s INTER u SUBSET t`) THEN
   MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n0:num. ~((x:A) IN (g:num->A->bool) n0)`
    (X_CHOOSE_TAC `n0:num`) THENL
  [FIRST_ASSUM(MP_TAC o check (fun th ->
     try snd(dest_eq(concl th)) = `{}:A->bool` with _ -> false)) THEN
   REWRITE_TAC[EXTENSION; IN_INTERS; NOT_IN_EMPTY;
               FORALL_IN_GSPEC; IN_UNIV] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  EXISTS_TAC `topspace top DIFF top closure_of (H:num->A->bool) n0` THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
   REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
   (* x IN topspace DIFF closure_of H n0 *)
   ASM_REWRITE_TAC[IN_DIFF] THEN
   FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `n0:num`) THEN
   FIRST_X_ASSUM(fun th ->
     if is_neg(concl th) then MP_TAC th else failwith "x") THEN
   SET_TAC[];
   (* FINITE {v IN V | v INTER w != {}} *)
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC
     `IMAGE (\n:num. (u:num->A->bool) n INTER
       INTERS(IMAGE (H:num->A->bool) {i:num | i < n}))
       {j:num | j <= n0}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `s:A->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `m:num` ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) then SUBST_ALL_TAC th else failwith "") THEN
    EXISTS_TAC `m:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if (is_neg (concl th)) then MP_TAC th else failwith "not neg") THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
      `(s:A->bool) SUBSET c ==> s INTER (t DIFF c) = {}`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(H:num->A->bool) n0` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC(SET_RULE
       `(h:A->bool) IN s ==> t INTER INTERS s SUBSET h`) THEN
     REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
     EXISTS_TAC `n0:num` THEN
     ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
     MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
     MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]]]]);;

(* Engelking 5.2.1/5.2.2 (Dowker): Characterization of countably paracompact
   normal spaces *)
let NORMAL_COUNTABLY_PARACOMPACT_CHARACTERIZATION = prove
 (`!top:A topology.
        normal_space top
        ==> (countably_paracompact_space top <=>
             !f. (!n. closed_in top (f n)) /\
                 (!n. f(SUC n) SUBSET f n) /\
                 INTERS {f n | n IN (:num)} = {}
                 ==> ?g. (!n. open_in top (g n)) /\
                         (!n. f n SUBSET g n) /\
                         INTERS {g n | n IN (:num)} = {})`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
  [(* Forward direction: doesn't need normality *)
   MATCH_ACCEPT_TAC COUNTABLY_PARACOMPACT_IMP_DOWKER;
   (* Backward direction: needs normality *)
   DISCH_TAC THEN MATCH_MP_TAC DOWKER_BACKWARD THEN
   ASM_REWRITE_TAC[]]);;

(* Closed subspace of countably paracompact is countably paracompact *)
let COUNTABLY_PARACOMPACT_SPACE_CLOSED_SUBSET = prove
 (`!top s:A->bool.
        countably_paracompact_space top /\ closed_in top s
        ==> countably_paracompact_space(subtopology top s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[countably_paracompact_space] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; CLOSED_IN_SUBSET] THEN
  X_GEN_TAC `U:(A->bool)->bool` THEN STRIP_TAC THEN
  (* Each u in U is open in subtopology, so u = s INTER f(u) for some choice f *)
  SUBGOAL_THEN
    `?f:(A->bool)->(A->bool).
       !u. u IN U ==> open_in top (f u) /\ u = s INTER f u`
    (X_CHOOSE_TAC `f:(A->bool)->(A->bool)`) THENL
  [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `u:A->bool` THEN
   ASM_CASES_TAC `(u:A->bool) IN U` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN MESON_TAC[INTER_COMM];
    EXISTS_TAC `{}:A->bool` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Apply countably_paracompact to (topspace DIFF s) INSERT IMAGE f U *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(topspace top DIFF s:A->bool) INSERT IMAGE (f:(A->bool)->(A->bool)) U`) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[COUNTABLE_INSERT] THEN
    MATCH_MP_TAC COUNTABLE_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
     ASM_REWRITE_TAC[];
     GEN_TAC THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `x:A->bool`) THEN ASM_REWRITE_TAC[] THEN
     SIMP_TAC[]];
    ALL_TAC] THEN
   REWRITE_TAC[UNIONS_INSERT] THEN
   SUBGOAL_THEN `(s:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP CLOSED_IN_SUBSET); ALL_TAC] THEN
   SUBGOAL_THEN `!u:A->bool. u IN U ==> u SUBSET (f:(A->bool)->(A->bool)) u`
     ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[]; ALL_TAC] THEN
   UNDISCH_THEN `COUNTABLE(U:(A->bool)->bool)` (K ALL_TAC) THEN
   SUBGOAL_THEN
     `!u:A->bool. u IN U ==> (f:(A->bool)->(A->bool)) u SUBSET topspace top`
     ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
    FIRST_X_ASSUM(K ALL_TAC o SPEC `u:A->bool`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:A->bool`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
   UNDISCH_THEN
     `!u:A->bool. u IN U ==> open_in top ((f:(A->bool)->(A->bool)) u) /\
                              u = s INTER f u` (K ALL_TAC) THEN
   UNDISCH_THEN `closed_in top (s:A->bool)` (K ALL_TAC) THEN
   ASM SET_TAC[];
   DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC)] THEN
  (* Remove COUNTABLE from context - causes ASM tactics to hang *)
  UNDISCH_THEN `COUNTABLE(U:(A->bool)->bool)` (K ALL_TAC) THEN
  (* Produce the subtopology cover: {s INTER v | v IN V, not(v SUBSET DIFF s)} *)
  EXISTS_TAC
    `{s INTER v:A->bool | v | v IN V /\ ~(v SUBSET topspace top DIFF s)}` THEN
  REPEAT CONJ_TAC THENL
  [(* open_in subtopology for each s INTER v *)
   REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
   EXISTS_TAC `v:A->bool` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_ACCEPT_TAC INTER_COMM];
   (* UNIONS covers s *)
   REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
    UNDISCH_TAC `(x:A) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(x:A) IN UNIONS V` MP_TAC THENL
   [UNDISCH_TAC `UNIONS (V:(A->bool)->bool) = topspace top` THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[IN_UNIONS] THEN
   DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `s INTER v:A->bool` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN v` THEN UNDISCH_TAC `(x:A) IN s` THEN SET_TAC[];
    REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[]];
   (* Refinement: each s INTER v refines some u IN U *)
   REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `v:A->bool`) THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[EXISTS_IN_INSERT; EXISTS_IN_IMAGE] THEN
   STRIP_TAC THENL
   [UNDISCH_TAC `~((v:A->bool) SUBSET topspace top DIFF s)` THEN
    ASM_REWRITE_TAC[];
    (* Case: x IN U /\ v SUBSET f x *)
    EXISTS_TAC `x:A->bool` THEN CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    (* Goal: s INTER v SUBSET x *)
    FIRST_X_ASSUM(K ALL_TAC o SPEC `x:A->bool`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC) THEN
    (* Goal: s INTER v SUBSET s INTER f x *)
    UNDISCH_TAC `(v:A->bool) SUBSET (f:(A->bool)->(A->bool)) x` THEN
    SET_TAC[]];
   (* Locally finite in subtopology *)
   MATCH_MP_TAC LOCALLY_FINITE_IN_SUBTOPOLOGY THEN
   REWRITE_TAC[FORALL_IN_GSPEC; INTER_SUBSET] THEN
   MATCH_MP_TAC LOCALLY_FINITE_IN_SUBSET THEN
   EXISTS_TAC `{(s:A->bool) INTER v | v IN V}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC LOCALLY_FINITE_IN_REFINEMENT THEN
    REWRITE_TAC[INTER_SUBSET] THEN ASM_REWRITE_TAC[];
    SET_TAC[]]]);;

(* Product with compact preserves countable paracompactness *)
(* Same tube argument as PARACOMPACT_SPACE_PRODUCT_COMPACT_LEFT
   but indexes by finite subsets F of U (countable). *)

let COUNTABLY_PARACOMPACT_SPACE_PRODUCT_COMPACT = prove
 (`!(top:A topology) (top':B topology).
        countably_paracompact_space top /\ compact_space top'
        ==> countably_paracompact_space(prod_topology top top')`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[countably_paracompact_space; TOPSPACE_PROD_TOPOLOGY] THEN
  X_GEN_TAC `U:((A#B)->bool)->bool` THEN STRIP_TAC THEN
  (* Step 1: Tube lemma - for each x, get V(x) and finite Ux(x) *)
  SUBGOAL_THEN
    `!x:A. x IN topspace top
           ==> ?v (Ux:((A#B)->bool)->bool). open_in top v /\ x IN v /\
                      FINITE Ux /\ Ux SUBSET U /\
                      (v:A->bool) CROSS topspace top' SUBSET UNIONS Ux`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC COMPACT_TUBE_COVER THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_SING; IN_UNIONS] THEN
   MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
   DISCH_THEN(MP_TAC o SPEC `(x:A,b:B)`) THEN
   REWRITE_TAC[IN_UNIONS; IN_CROSS] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Skolemize to get V and Ux *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SKOLEM_THM_GEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->(A->bool)` MP_TAC) THEN
  REWRITE_TAC[SKOLEM_THM_GEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ux:A->((A#B)->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Step 2: Group V(x) by the value of Ux(x) to get a countable cover of top *)
  ABBREV_TAC
    `W = \(G:((A#B)->bool)->bool).
       UNIONS {(V:A->(A->bool)) x | x | x IN topspace top /\
               (Ux:A->((A#B)->bool)->bool) x = G}` THEN
  (* Key property: W(Ux p) CROSS topspace top' SUBSET UNIONS(Ux p) *)
  SUBGOAL_THEN
    `!p:A. p IN topspace top
           ==> (W:(((A#B)->bool)->bool)->(A->bool))(Ux p) CROSS topspace top'
               SUBSET UNIONS ((Ux:A->((A#B)->bool)->bool) p)`
    ASSUME_TAC THENL
  [X_GEN_TAC `p:A` THEN DISCH_TAC THEN EXPAND_TAC "W" THEN
   REWRITE_TAC[] THEN
   REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS] THEN
   MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN STRIP_TAC THEN
   (* a IN UNIONS {V x | ...}, b IN topspace top'. Unpack the UNIONS. *)
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC)
                       ASSUME_TAC)) THEN
   (* x0 IN topspace top, Ux x0 = Ux p, t = V x0, a IN t *)
   REWRITE_TAC[IN_UNIONS] THEN
   SUBGOAL_THEN
     `(a:A,b:B) IN UNIONS ((Ux:A->((A#B)->bool)->bool) x0)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x0:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_CROSS] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[IN_UNIONS]];
   ALL_TAC] THEN
  (* Remove COUNTABLE U from context to prevent ASM_ tactic explosions.
     First establish the countability we need. *)
  SUBGOAL_THEN
    `COUNTABLE (IMAGE (Ux:A->((A#B)->bool)->bool) (topspace top))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC COUNTABLE_SUBSET THEN
   EXISTS_TAC `{G:((A#B)->bool)->bool | G SUBSET U /\ FINITE G}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_FINITE_SUBSETS THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `G:((A#B)->bool)->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
   ALL_TAC] THEN
  UNDISCH_THEN `COUNTABLE(U:((A#B)->bool)->bool)` (K ALL_TAC) THEN
  (* Apply countably_paracompact_space to the grouped cover *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [countably_paracompact_space]) THEN
  DISCH_THEN(MP_TAC o SPEC
    `IMAGE (W:(((A#B)->bool)->bool)->(A->bool))
           (IMAGE (Ux:A->((A#B)->bool)->bool) (topspace top))`) THEN
  ANTS_TAC THENL
  [(* Remove W key property to prevent FIRST_X_ASSUM from matching it
     instead of the tube lemma. Not needed inside ANTS_TAC. *)
   UNDISCH_THEN
     `!p:A. p IN topspace top
            ==> (W:(((A#B)->bool)->bool)->(A->bool))
                ((Ux:A->((A#B)->bool)->bool) p) CROSS
                topspace (top':B topology) SUBSET UNIONS (Ux p)`
     (K ALL_TAC) THEN
   REPEAT CONJ_TAC THENL
   [(* Countable *)
    MATCH_MP_TAC COUNTABLE_IMAGE THEN ASM_REWRITE_TAC[];
    (* Each element is open - FORALL_IN_IMAGE applies twice due to
       IMAGE W (IMAGE Ux ...), so universally quantified var is :A *)
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[];
    (* Covers topspace top - EXISTS_IN_IMAGE applies twice similarly *)
    REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN EQ_TAC THENL
    [DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN
       `open_in top ((W:(((A#B)->bool)->bool)->(A->bool))
                     ((Ux:A->((A#B)->bool)->bool) q))`
       MP_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `y:A` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]];
     DISCH_TAC THEN
     EXISTS_TAC `x:A` THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      EXPAND_TAC "W" THEN REWRITE_TAC[] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `(V:A->(A->bool)) x` THEN
      CONJ_TAC THENL
      [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
       FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
       SIMP_TAC[]]]]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Step 3: For each z in Z, pick xw(z) in topspace top *)
  SUBGOAL_THEN
    `?xw:(A->bool)->A. !z. z IN Z
       ==> xw z IN topspace top /\
           z SUBSET (W:(((A#B)->bool)->bool)->(A->bool))
                    ((Ux:A->((A#B)->bool)->bool)(xw z))`
    STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[GSYM SKOLEM_THM_GEN] THEN
   X_GEN_TAC `z:A->bool` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `z:A->bool`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
   DISCH_THEN(X_CHOOSE_THEN `G:((A#B)->bool)->bool` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
   DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[SUBSET_TRANS];
   ALL_TAC] THEN
  (* Step 4: Build the product refinement *)
  EXISTS_TAC `{(z:A->bool) CROSS topspace top' INTER (u:(A#B)->bool) |
               z IN Z /\ u IN (Ux:A->((A#B)->bool)->bool)((xw:(A->bool)->A) z)}` THEN
  REPEAT CONJ_TAC THENL
  [(* Each element is open in the product *)
   REWRITE_TAC[FORALL_IN_GSPEC] THEN
   MAP_EVERY X_GEN_TAC [`z:A->bool`; `u:(A#B)->bool`] THEN STRIP_TAC THEN
   MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_CROSS; OPEN_IN_TOPSPACE];
    ASM_MESON_TAC[SUBSET]];
   (* Covers the product space *)
   REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; FORALL_PAIR_THM;
               IN_CROSS] THEN
   MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN EQ_TAC THENL
   [(* Forward: element of tube => in product topspace *)
    DISCH_THEN(X_CHOOSE_THEN `s:(A#B)->bool` STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_CROSS]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[locally_finite_in]) THEN
    ASM_MESON_TAC[SUBSET];
    (* Backward: (a,b) in product topspace => find a tube *)
    STRIP_TAC THEN
    SUBGOAL_THEN `(a:A) IN UNIONS Z` MP_TAC THENL
    [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A->bool` STRIP_ASSUME_TAC) THEN
    (* a IN W(Ux(xw z)) since z SUBSET W(Ux(xw z)) *)
    SUBGOAL_THEN
      `(a:A,b:B) IN UNIONS ((Ux:A->((A#B)->bool)->bool)((xw:(A->bool)->A) z))`
      MP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `(xw:(A->bool)->A) z`) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_PAIR_THM;
       IN_CROSS]) THEN
     ASM_MESON_TAC[SUBSET];
     ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:(A#B)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(z:A->bool) CROSS topspace top' INTER (u:(A#B)->bool)` THEN
    CONJ_TAC THENL
    [EXISTS_TAC `z:A->bool` THEN EXISTS_TAC `u:(A#B)->bool` THEN
     ASM_REWRITE_TAC[];
     REWRITE_TAC[IN_INTER; IN_CROSS] THEN ASM_REWRITE_TAC[]]];
   (* Each element refines U *)
   EXISTS_TAC `\v:(A#B)->bool. @u:(A#B)->bool.
     ?w:A->bool. (w IN Z /\ u IN (Ux:A->((A#B)->bool)->bool)
       ((xw:(A->bool)->A) w)) /\
                 v = w CROSS topspace top' INTER u` THEN
   REWRITE_TAC[FORALL_IN_GSPEC] THEN
   MAP_EVERY X_GEN_TAC [`z:A->bool`; `u:(A#B)->bool`] THEN STRIP_TAC THEN
   REWRITE_TAC[] THEN
   SUBGOAL_THEN `?u':(A#B)->bool. ?w':A->bool.
     (w' IN Z /\ u' IN (Ux:A->((A#B)->bool)->bool)((xw:(A->bool)->A) w')) /\
     (z:A->bool) CROSS topspace top' INTER (u:(A#B)->bool) =
     w' CROSS topspace top' INTER u'`
     MP_TAC THENL
   [EXISTS_TAC `u:(A#B)->bool` THEN EXISTS_TAC `z:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SELECT_RULE) THEN
   DISCH_THEN(X_CHOOSE_THEN `w':A->bool` STRIP_ASSUME_TAC) THEN
   CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM SET_TAC[]];
   (* Locally finite - use LOCALLY_FINITE_PRODUCT_TUBES *)
   MATCH_MP_TAC LOCALLY_FINITE_PRODUCT_TUBES THEN
   EXISTS_TAC `U:((A#B)->bool)->bool` THEN
   ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[SUBSET_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* Nagata-Smirnov metrization (Munkres Sections 39-40)                       *)
(* ------------------------------------------------------------------------- *)

(* Helper: In a regular space with sigma-locally-finite open base,
   every closed set is G_delta *)
let CLOSED_G_DELTA_IN_SIGMA_LOCALLY_FINITE_BASE = prove
 (`!top:A topology C (B:(A->bool)->bool).
        regular_space top /\
        closed_in top C /\
        (!b. b IN B ==> open_in top b) /\
        (!x u. open_in top u /\ x IN u
               ==> ?b. b IN B /\ x IN b /\ b SUBSET u) /\
        sigma_locally_finite_in top B
        ==> gdelta_in top C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Unfold sigma_locally_finite_in to get Bn *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sigma_locally_finite_in]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Bn:num->(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GDELTA_IN_ALT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CLOSED_IN_SUBSET]; ALL_TAC] THEN
  (* For each n, Sn = {b in Bn(n) : closure_of b disjoint from C} *)
  ABBREV_TAC
    `Sn = \n:num. {b:A->bool | b IN Bn n /\
                                top closure_of b INTER C = {}}` THEN
  SUBGOAL_THEN `!n:num. locally_finite_in top ((Sn:num->(A->bool)->bool) n)`
    ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN
   SUBGOAL_THEN
     `(Sn:num->(A->bool)->bool) n SUBSET (Bn:num->(A->bool)->bool) n`
     MP_TAC THENL
   [EXPAND_TAC "Sn" THEN SET_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[LOCALLY_FINITE_IN_SUBSET];
   ALL_TAC] THEN
  (* closure of UNIONS(Sn n) is disjoint from C *)
  SUBGOAL_THEN
    `!n:num. top closure_of
             (UNIONS ((Sn:num->(A->bool)->bool) n)) INTER C = {}`
    ASSUME_TAC THENL
  [X_GEN_TAC `n:num` THEN ASM_SIMP_TAC[CLOSURE_OF_LOCALLY_FINITE_UNIONS] THEN
   REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
   X_GEN_TAC `b:A->bool` THEN
   EXPAND_TAC "Sn" THEN REWRITE_TAC[IN_ELIM_THM] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  (* For x not in C, x is in UNIONS(Sn m) for some m *)
  SUBGOAL_THEN
    `!x:A. x IN topspace top /\ ~(x IN C)
           ==> ?m:num. x IN UNIONS ((Sn:num->(A->bool)->bool) m)`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
   (* Use regularity: for x in open topspace\C, get closed v with x in u
      subset v subset topspace\C *)
   MP_TAC(REWRITE_RULE[NEIGHBOURHOOD_BASE_OF]
     (REWRITE_RULE[GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN]
       (ASSUME `regular_space (top:A topology)`))) THEN
   DISCH_THEN(MP_TAC o SPECL
     [`topspace top DIFF C:A->bool`; `x:A`]) THEN
   ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF] THEN
   DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
     (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC)) THEN
   (* Use base property to find b in B with x in b subset u *)
   FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `u:A->bool`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC) THEN
   (* b subset u subset v (closed), so cl(b) subset v subset topspace\C *)
   SUBGOAL_THEN `top closure_of (b:A->bool) INTER C = {}` ASSUME_TAC THENL
   [SUBGOAL_THEN `top closure_of (b:A->bool) SUBSET v` ASSUME_TAC THENL
    [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
     ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
     ASM SET_TAC[]];
    ALL_TAC] THEN
   (* b in B = UNIONS {Bn n | n}, so b in Bn m for some m *)
   SUBGOAL_THEN `?m:num. (b:A->bool) IN (Bn:num->(A->bool)->bool) m`
     (X_CHOOSE_THEN `m:num` ASSUME_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
   (* Therefore b in Sn m, and x in UNIONS(Sn m) *)
   EXISTS_TAC `m:num` THEN REWRITE_TAC[IN_UNIONS] THEN
   EXISTS_TAC `b:A->bool` THEN ASM_REWRITE_TAC[] THEN
   EXPAND_TAC "Sn" THEN REWRITE_TAC[IN_ELIM_THM] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Now build the gdelta_in witness *)
  REWRITE_TAC[INTERSECTION_OF] THEN
  EXISTS_TAC `IMAGE (\n:num. topspace top DIFF
                top closure_of (UNIONS ((Sn:num->(A->bool)->bool) n)))
              (:num)` THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
  [(* COUNTABLE *)
   MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
   (* Each element is open *)
   X_GEN_TAC `n:num` THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
   REWRITE_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_CLOSURE_OF];
   (* INTERS = C *)
   REWRITE_TAC[EXTENSION; IN_INTERS; FORALL_IN_IMAGE; IN_UNIV; IN_DIFF] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [(* INTERS subset C: if x in all Gn then x in C *)
    DISCH_TAC THEN
    (* Suppose x not in C. Then x in UNIONS(Sn m) for some m. *)
    ASM_CASES_TAC `(x:A) IN C` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
     MP_TAC(ISPECL [`top:A topology`;
                     `UNIONS ((Sn:num->(A->bool)->bool) 0)`]
                    CLOSURE_OF_SUBSET_TOPSPACE) THEN
     SET_TAC[];
     ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` ASSUME_TAC) THEN
    (* x in UNIONS(Sn m) implies x in cl(UNIONS(Sn m)), contradiction *)
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`;
                    `UNIONS ((Sn:num->(A->bool)->bool) m)`]
                   CLOSURE_OF_SUBSET) THEN
    SUBGOAL_THEN
      `UNIONS ((Sn:num->(A->bool)->bool) m) SUBSET topspace top`
      (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[UNIONS_SUBSET] THEN
     ASM_MESON_TAC[locally_finite_in];
     ASM SET_TAC[]];
    (* C subset INTERS: if x in C then x in each Gn *)
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN CONJ_TAC THENL
    [ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET];
     FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
     MP_TAC(ISPECL [`top:A topology`;
                     `UNIONS ((Sn:num->(A->bool)->bool) n)`]
                    CLOSURE_OF_SUBSET_TOPSPACE) THEN
     ASM SET_TAC[]]]]);;

(* Helper: In a normal space, for a closed G_delta set A,
   there exists continuous f with f^{-1}(0) = A *)
let URYSOHN_FUNCTION_G_DELTA = prove
 (`!top:A topology A.
        normal_space top /\ closed_in top A /\ gdelta_in top A
        ==> ?f. continuous_map(top,euclideanreal) f /\
                (!x. x IN topspace top ==> &0 <= f x /\ f x <= &1) /\
                (!x. x IN topspace top ==> (f x = &0 <=> x IN A))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: Extract countable family of open sets from gdelta_in *)
  UNDISCH_TAC `gdelta_in (top:A topology) (A:A->bool)` THEN
  REWRITE_TAC[GDELTA_IN_ALT; INTERSECTION_OF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:(A->bool)->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `(topspace top:A->bool) INSERT u` COUNTABLE_AS_IMAGE) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[COUNTABLE_INSERT] THEN SET_TAC[];
   DISCH_THEN(X_CHOOSE_TAC `U:num->A->bool`)] THEN
  SUBGOAL_THEN `!n:num. open_in top ((U:num->A->bool) n)` ASSUME_TAC THENL
  [GEN_TAC THEN
   SUBGOAL_THEN `(U:num->A->bool) n IN (topspace top:A->bool) INSERT u`
     MP_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    REWRITE_TAC[IN_INSERT] THEN
    DISCH_THEN(DISJ_CASES_TAC) THENL
    [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]; ASM_MESON_TAC[]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `(A:A->bool) = INTERS {U n | n IN (:num)}` ASSUME_TAC THENL
  [SUBGOAL_THEN
     `{(U:num->A->bool) n | n IN (:num)} = topspace top INSERT u`
     SUBST1_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE] THEN FIRST_ASSUM(ACCEPT_TAC o SYM);
    REWRITE_TAC[INTERS_INSERT] THEN ASM SET_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. (A:A->bool) SUBSET U n` ASSUME_TAC THENL
  [GEN_TAC THEN FIRST_ASSUM(fun th ->
     GEN_REWRITE_TAC LAND_CONV [th]) THEN
   REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_GSPEC; IN_UNIV] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  (* Step 2: Get Urysohn functions for each n *)
  SUBGOAL_THEN
    `!n. ?fn:A->real.
       continuous_map
         (top, subtopology euclideanreal (real_interval[&0,&1])) fn /\
       (!x. x IN A ==> fn x = &0) /\
       (!x. x IN topspace top DIFF (U:num->A->bool) n ==> fn x = &1)`
    MP_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`top:A topology`; `A:A->bool`;
                   `topspace top DIFF (U:num->A->bool) n`;
                   `&0`; `&1`] URYSOHN_LEMMA) THEN
   ASM_REWRITE_TAC[REAL_POS] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC CLOSED_IN_DIFF THEN
     ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
     REWRITE_TAC[DISJOINT] THEN ASM SET_TAC[]];
    MESON_TAC[]];
   REWRITE_TAC[SKOLEM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `fn:num->A->real` MP_TAC) THEN
   REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  (* Extract continuity into euclideanreal and bounds *)
  SUBGOAL_THEN
    `(!n:num. continuous_map(top,euclideanreal) ((fn:num->A->real) n)) /\
     (!n x:A. x IN topspace top ==> &0 <= fn n x /\ fn n x <= &1)`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
      `continuous_map
         (top:A topology,
          subtopology euclideanreal (real_interval [&0,&1]))
         ((fn:num->A->real) n)`
      MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `continuous_map
         (top:A topology,
          subtopology euclideanreal (real_interval [&0,&1]))
         ((fn:num->A->real) n)`
      MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 3: Prove partial sums are continuous *)
  SUBGOAL_THEN
    `!n. continuous_map(top:A topology, euclideanreal)
          (\x. sum(0..n) (\k. (fn:num->A->real) k x * inv(&2) pow (k + 1)))`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN
   REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
   ASM_SIMP_TAC[ETA_AX];
   ALL_TAC] THEN
  (* Step 4: Apply uniform Cauchy limit to get limit function *)
  MP_TAC(ISPECL
   [`top:A topology`; `real_euclidean_metric`;
    `(\n x:A. sum(0..n)
       (\k. (fn:num->A->real) k x * inv(&2) pow (k + 1))):num->A->real`]
   CONTINUOUS_MAP_UNIFORMLY_CAUCHY_LIMIT) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; MTOPOLOGY_REAL_EUCLIDEAN_METRIC;
                  EVENTUALLY_TRUE; MCOMPLETE_REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN
  DISCH_TAC THEN
  (* Get the limit function via CONTINUOUS_MAP_UNIFORMLY_CAUCHY_LIMIT *)
  SUBGOAL_THEN
    `?g:A->real. continuous_map(top,euclideanreal) g /\
       (!e. &0 < e
            ==> eventually
                  (\n. !(x:A). x IN topspace top
                       ==> abs(g x - sum (0..n)
                              (\k. (fn:num->A->real) k x *
                                   inv(&2) pow (k + 1))) < e)
                  sequentially)`
    (X_CHOOSE_THEN `g:A->real` STRIP_ASSUME_TAC) THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`inv(&2)`; `e:real`] ARCH_EVENTUALLY_POW_INV) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
   MATCH_MP_TAC WLOG_LT THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM];
    MESON_TAC[REAL_ABS_SUB];
    (* Case m < n *)
    MAP_EVERY X_GEN_TAC [`m:num`; `nn:num`] THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `sum(0..nn) (\k. (fn:num->A->real) k x * inv(&2) pow (k + 1)) -
       sum(0..m) (\k. fn k x * inv(&2) pow (k + 1)) =
       sum(m+1..nn) (\k. fn k x * inv(&2) pow (k + 1))`
      ASSUME_TAC THENL
    [MP_TAC(ISPECL
       [`\k. (fn:num->A->real) k x * inv(&2) pow (k + 1)`;
        `0`; `m:num`; `nn:num`] SUM_COMBINE_R) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `&0 <= sum(m+1..nn)
        (\k. (fn:num->A->real) k x * inv(&2) pow (k + 1))`
      ASSUME_TAC THENL
    [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
     BETA_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET];
      MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
     ALL_TAC] THEN
    TRANS_TAC REAL_LET_TRANS
      `sum(m+1..nn) (\k. (fn:num->A->real) k x * inv(&2) pow (k + 1))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH
       `a - b = c /\ &0 <= c ==> abs(a - b) <= c`) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    TRANS_TAC REAL_LET_TRANS
      `sum(m+1..nn) (\k. inv(&2) pow (k + 1))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
     BETA_TAC THEN
     GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET];
      MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
     ALL_TAC] THEN
    TRANS_TAC REAL_LET_TRANS `inv(&2) pow m` THEN CONJ_TAC THENL
    [(* Geometric sum bound using SUM_GP_MULTIPLIED *)
     REWRITE_TAC[GSYM ADD1; CONJUNCT2 real_pow; SUM_LMUL] THEN
     MP_TAC(ISPECL [`inv(&2)`; `SUC m`; `nn:num`] SUM_GP_MULTIPLIED) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `&1 - inv(&2) = inv(&2)`
       (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `a <= b /\ &0 <= c ==> a - c <= b`) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO_INV THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
     FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[REAL_ABS_POW; REAL_ABS_INV; REAL_ABS_NUM] THEN
     SIMP_TAC[]]];
    (* Step 5: g already extracted by SUBGOAL_THEN, prove properties *)
    EXISTS_TAC `g:A->real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [(* Part 1: &0 <= g x /\ g x <= &1 *)
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN
       `!m. &0 <= sum(0..m)
              (\k. (fn:num->A->real) k x * inv(&2) pow (k+1)) /\
            sum(0..m)
              (\k. fn k x * inv(&2) pow (k+1)) <= &1`
       ASSUME_TAC THENL
     [GEN_TAC THEN CONJ_TAC THENL
      [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
       BETA_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
       TRANS_TAC REAL_LE_TRANS
         `sum(0..m) (\k. inv(&2) pow (k + 1))` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
        BETA_TAC THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
        [ASM_MESON_TAC[];
         MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
        REWRITE_TAC[GSYM ADD1; CONJUNCT2 real_pow; SUM_LMUL] THEN
        MP_TAC(ISPECL [`inv(&2)`; `0`; `m:num`] SUM_GP_MULTIPLIED) THEN
        REWRITE_TAC[LE_0] THEN
        SUBGOAL_THEN `&1 - inv(&2) = inv(&2)`
          (fun th -> REWRITE_TAC[th]) THENL
        [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
        REWRITE_TAC[CONJUNCT1 real_pow] THEN
        DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> &1 - b <= &1`) THEN
        MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV]];
      ALL_TAC] THEN
     CONJ_TAC THENL
     [(* &0 <= g x *)
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `--((g:A->real) x)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
      REWRITE_TAC[LE_REFL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
      UNDISCH_TAC `(g:A->real) x < &0` THEN REAL_ARITH_TAC;
      (* g x <= &1 *)
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `(g:A->real) x - &1`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
      REWRITE_TAC[LE_REFL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
      UNDISCH_TAC `&1 < (g:A->real) x` THEN REAL_ARITH_TAC];
     (* Part 2: g x = 0 iff x in INTERS{U n | n} *)
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN EQ_TAC THENL
     [(* g x = 0 ==> x IN INTERS{U n | n} *)
      DISCH_TAC THEN
      REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_UNIV] THEN
      X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `(fn:num->A->real) n x = &1` ASSUME_TAC THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `inv(&2) pow (n + 1)`) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC REAL_POW_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
       ALL_TAC] THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `N + n:num`) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN
      SUBGOAL_THEN
        `inv(&2) pow (n + 1) <=
           sum(0..N + n)
             (\k. (fn:num->A->real) k x * inv(&2) pow (k + 1))`
        MP_TAC THENL
      [MP_TAC(ISPECL [`n..n`; `0..N + n`;
         `\k:num. (fn:num->A->real) k (x:A) * inv(&2) pow (k + 1)`]
         SUM_SUBSET_SIMPLE) THEN
       ANTS_TAC THENL
       [REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG] THEN
        CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[IN_DIFF; IN_NUMSEG] THEN
        REPEAT STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
        [ASM_MESON_TAC[];
         MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
        REWRITE_TAC[SUM_SING_NUMSEG] THEN BETA_TAC THEN
        ASM_REWRITE_TAC[REAL_MUL_LID]];
       ALL_TAC] THEN
      SUBGOAL_THEN
        `&0 <= sum(0..N + n)
           (\k. (fn:num->A->real) k x * inv(&2) pow (k + 1))`
        MP_TAC THENL
      [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
       BETA_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
       REAL_ARITH_TAC];
      (* x IN INTERS{U n | n} ==> g x = 0 *)
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN A` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `!n:num. (fn:num->A->real) n x = &0` ASSUME_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
        `!m. sum(0..m)
               (\k. (fn:num->A->real) k x * inv(&2) pow (k+1)) = &0`
        ASSUME_TAC THENL
      [GEN_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
       REPEAT STRIP_TAC THEN BETA_TAC THEN
       ASM_REWRITE_TAC[REAL_MUL_LZERO];
       ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `abs((g:A->real) x)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
      REWRITE_TAC[LE_REFL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
      REAL_ARITH_TAC]]]);;

(* Helper: open sets in regular spaces with sigma-LF base have
   "closure covers": W = UNIONS{En n} with closure(En n) SUBSET W *)
let OPEN_SIGMA_LF_CLOSURE_COVER = prove
 (`!top:A topology B W.
        regular_space top /\ open_in top W /\
        (!b. b IN B ==> open_in top b) /\
        (!x u. open_in top u /\ x IN u
               ==> ?b. b IN B /\ x IN b /\ b SUBSET u) /\
        sigma_locally_finite_in top B
        ==> ?En. (!n. open_in top (En n)) /\
                 (!n. top closure_of (En n) SUBSET W) /\
                 W SUBSET UNIONS {En n | n IN (:num)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sigma_locally_finite_in]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Bn:num->(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `!n:num (b:A->bool). b IN (Bn:num->(A->bool)->bool) n ==> open_in top b`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   EXISTS_TAC `(Bn:num->(A->bool)->bool) (n:num)` THEN
   ASM_REWRITE_TAC[] THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[];
   ALL_TAC] THEN
  EXISTS_TAC `\n. UNIONS {b:A->bool | b IN (Bn:num->(A->bool)->bool) n /\
                          top closure_of b SUBSET W}` THEN
  SUBGOAL_THEN
    `!n. locally_finite_in top
         {b:A->bool | b IN (Bn:num->(A->bool)->bool) n /\
                      top closure_of b SUBSET W}`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC LOCALLY_FINITE_IN_SUBSET THEN
   EXISTS_TAC `(Bn:num->(A->bool)->bool) n` THEN ASM SET_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [(* open *)
   GEN_TAC THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM SET_TAC[];
   (* closure SUBSET W *)
   GEN_TAC THEN ASM_SIMP_TAC[CLOSURE_OF_LOCALLY_FINITE_UNIONS] THEN
   REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
   SIMP_TAC[];
   (* covering: W SUBSET UNIONS *)
   ONCE_REWRITE_TAC[SUBSET] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   MP_TAC(REWRITE_RULE[NEIGHBOURHOOD_BASE_OF]
     (REWRITE_RULE[GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN]
       (ASSUME `regular_space (top:A topology)`))) THEN
   DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `x:A`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
     (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN
     `?b:A->bool. b IN B /\ (x:A) IN b /\ b SUBSET (u:A->bool)`
     (X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC) THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `top closure_of (b:A->bool) SUBSET W` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `v:A->bool` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `u:A->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `?m:num. (b:A->bool) IN (Bn:num->(A->bool)->bool) m`
     (X_CHOOSE_THEN `m:num` ASSUME_TAC) THENL
   [UNDISCH_TAC `(b:A->bool) IN B` THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:(A->bool)->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `p:num`) ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   EXISTS_TAC
     `UNIONS {b':A->bool | b' IN (Bn:num->(A->bool)->bool) m /\
                            top closure_of b' SUBSET W}` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `m:num` THEN REWRITE_TAC[];
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `b:A->bool` THEN ASM_REWRITE_TAC[]]]);;

(* Normal space from regular + sigma-locally-finite base *)
let NORMAL_SPACE_SIGMA_LOCALLY_FINITE_BASE = prove
 (`!top:A topology B.
        regular_space top /\
        (!b. b IN B ==> open_in top b) /\
        (!x u. open_in top u /\ x IN u
               ==> ?b. b IN B /\ x IN b /\ b SUBSET u) /\
        sigma_locally_finite_in top B
        ==> normal_space top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[normal_space] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `t:A->bool`] THEN STRIP_TAC THEN
  (* Get sigma-LF closure covers for the two complements *)
  MP_TAC(ISPECL [`top:A topology`; `B:(A->bool)->bool`;
                 `topspace top DIFF t:A->bool`]
    OPEN_SIGMA_LF_CLOSURE_COVER) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
   ASM_MESON_TAC[CLOSED_IN_SUBSET; SET_RULE
     `(s:A->bool) SUBSET u /\ DISJOINT s t ==> s SUBSET u DIFF t`];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:num->A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `B:(A->bool)->bool`;
                 `topspace top DIFF s:A->bool`]
    OPEN_SIGMA_LF_CLOSURE_COVER) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
   ASM_MESON_TAC[CLOSED_IN_SUBSET; SET_RULE
     `(t:A->bool) SUBSET u /\ DISJOINT s t ==> t SUBSET u DIFF s`];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:num->A->bool` STRIP_ASSUME_TAC) THEN
  (* Abbreviate the shrunk open sets *)
  ABBREV_TAC
    `U' = \n. (U:num->A->bool) n DIFF
              UNIONS (IMAGE (\k. top closure_of ((V:num->A->bool) k))
                            (0..n))` THEN
  ABBREV_TAC
    `V' = \n. (V:num->A->bool) n DIFF
              UNIONS (IMAGE (\k. top closure_of ((U:num->A->bool) k))
                            (0..n))` THEN
  EXISTS_TAC `UNIONS {(U':num->A->bool) n | n IN (:num)}` THEN
  EXISTS_TAC `UNIONS {(V':num->A->bool) n | n IN (:num)}` THEN
  (* Each shrunk set is open *)
  SUBGOAL_THEN `!n. open_in top ((U':num->A->bool) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "U'" THEN
   MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC CLOSED_IN_UNIONS THEN
   SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
   REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n. open_in top ((V':num->A->bool) n)` ASSUME_TAC THENL
  [GEN_TAC THEN EXPAND_TAC "V'" THEN
   MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC CLOSED_IN_UNIONS THEN
   SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
   REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [(* open_in top U'' *)
   MATCH_MP_TAC OPEN_IN_UNIONS THEN
   REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN ASM_REWRITE_TAC[];
   (* open_in top V'' *)
   MATCH_MP_TAC OPEN_IN_UNIONS THEN
   REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN ASM_REWRITE_TAC[];
   (* s SUBSET UNIONS U' *)
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(x:A) IN UNIONS {(U:num->A->bool) n | n IN (:num)}`
     MP_TAC THENL
   [SUBGOAL_THEN `(x:A) IN topspace top DIFF t` MP_TAC THENL
    [SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET]; ALL_TAC] THEN
     ASM SET_TAC[];
     ASM SET_TAC[]];
    ALL_TAC] THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `su:A->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`) ASSUME_TAC)) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   EXISTS_TAC `(U':num->A->bool) m` THEN
   CONJ_TAC THENL [EXISTS_TAC `m:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
   EXPAND_TAC "U'" THEN
   REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_IMAGE] THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
   X_GEN_TAC `c:A->bool` THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))
     ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   UNDISCH_TAC
     `!n:num. top closure_of (V:num->A->bool) n
              SUBSET topspace top DIFF s` THEN
   DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
   REWRITE_TAC[SUBSET; IN_DIFF] THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
   (* t SUBSET UNIONS V' *)
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(x:A) IN UNIONS {(V:num->A->bool) n | n IN (:num)}`
     MP_TAC THENL
   [SUBGOAL_THEN `(x:A) IN topspace top DIFF s` MP_TAC THENL
    [SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET]; ALL_TAC] THEN
     ASM SET_TAC[];
     ASM SET_TAC[]];
    ALL_TAC] THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   DISCH_THEN(X_CHOOSE_THEN `sv:A->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`) ASSUME_TAC)) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   EXISTS_TAC `(V':num->A->bool) m` THEN
   CONJ_TAC THENL [EXISTS_TAC `m:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
   EXPAND_TAC "V'" THEN
   REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_IMAGE] THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
   X_GEN_TAC `c:A->bool` THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))
     ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   UNDISCH_TAC
     `!n:num. top closure_of (U:num->A->bool) n
              SUBSET topspace top DIFF t` THEN
   DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
   REWRITE_TAC[SUBSET; IN_DIFF] THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
   (* DISJOINT UNIONS U' UNIONS V' *)
   REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x:A. x IN s ==> ~(x IN t)`] THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `x:A` THEN DISCH_THEN(X_CHOOSE_THEN `su:A->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`) ASSUME_TAC)) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   REWRITE_TAC[NOT_EXISTS_THM] THEN
   X_GEN_TAC `sv:A->bool` THEN
   DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `p:num`) ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   (* Now have x IN U' m and x IN V' p, goal is F *)
   SUBGOAL_THEN
     `(x:A) IN (U:num->A->bool) m /\
      (!k. k IN (0..m)
           ==> ~(x IN top closure_of ((V:num->A->bool) k)))`
     STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN (U':num->A->bool) m` THEN
    EXPAND_TAC "U'" THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_IMAGE; NOT_EXISTS_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `top closure_of ((V:num->A->bool) k)`) THEN
    SUBGOAL_THEN
      `?k':num. top closure_of ((V:num->A->bool) k) =
                top closure_of (V k') /\ k' IN 0..m`
      ASSUME_TAC THENL
    [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(x:A) IN (V:num->A->bool) p /\
      (!k. k IN (0..p)
           ==> ~(x IN top closure_of ((U:num->A->bool) k)))`
     STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN (V':num->A->bool) p` THEN
    EXPAND_TAC "V'" THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_IMAGE; NOT_EXISTS_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `top closure_of ((U:num->A->bool) k)`) THEN
    SUBGOAL_THEN
      `?k':num. top closure_of ((U:num->A->bool) k) =
                top closure_of (U k') /\ k' IN 0..p`
      ASSUME_TAC THENL
    [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   DISJ_CASES_TAC(SPECL [`m:num`; `p:num`] LE_CASES) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `(U:num->A->bool) m`]
      CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL
    [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM_MESON_TAC[SUBSET]];
    UNDISCH_TAC
      `!k. k IN 0..m
           ==> ~((x:A) IN top closure_of ((V:num->A->bool) k))` THEN
    DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `(V:num->A->bool) p`]
      CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL
    [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM_MESON_TAC[SUBSET]]]]
   );;

(* Helper: closed sets are Gdelta in regular spaces with sigma-LF base *)
let CLOSED_GDELTA_IN_SIGMA_LF_BASE = prove
 (`!top:A topology B s.
     regular_space top /\
     (!b. b IN B ==> open_in top b) /\
     (!x u. open_in top u /\ x IN u
            ==> ?b. b IN B /\ x IN b /\ b SUBSET u) /\
     sigma_locally_finite_in top B /\
     closed_in top s
     ==> gdelta_in top s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `B:(A->bool)->bool`;
                  `topspace top DIFF s:A->bool`]
    OPEN_SIGMA_LF_CLOSURE_COVER) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `En:num->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `s:A->bool =
     INTERS {topspace top DIFF top closure_of (En n) | n IN (:num)}`
  SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_INTERS; FORALL_IN_GSPEC; IN_UNIV; IN_DIFF] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [(* Forward: x IN s ==> x IN all topspace\cl(En n) *)
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN CONJ_TAC THENL
    [ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
      REWRITE_RULE[SUBSET]) THEN
    ASM SET_TAC[];
    (* Backward: x IN all topspace\cl(En n) ==> x IN s *)
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN SET_TAC[]; ALL_TAC] THEN
    (* Proof by contradiction *)
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    (* Goal: F. Have ~(x IN s), x IN topspace *)
    SUBGOAL_THEN `?m:num. (x:A) IN (En:num->A->bool) m`
      STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `(x:A) IN UNIONS {(En:num->A->bool) n | n IN (:num)}`
      MP_TAC THENL
     [UNDISCH_TAC
        `topspace top DIFF s SUBSET
         UNIONS {(En:num->A->bool) n | n IN (:num)}` THEN
      ASM SET_TAC[];
      SET_TAC[]];
     ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    MP_TAC(ISPECL [`top:A topology`; `(En:num->A->bool) m`]
      CLOSURE_OF_SUBSET) THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET; IN_INTER; IN_DIFF]];
   ALL_TAC] THEN
  MATCH_MP_TAC GDELTA_IN_INTERS THEN
  SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; UNIV_NOT_EMPTY; IN_UNIV] THEN
  X_GEN_TAC `n:num` THEN MATCH_MP_TAC OPEN_IMP_GDELTA_IN THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN
  REWRITE_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_CLOSURE_OF]);;

(* Munkres Lemma 40.2: In a normal space, a closed Gdelta set is a zero set.
   More precisely: there exists continuous f:[0,1] with f=0 on s, f>0 off s *)
let URYSOHN_FUNCTION_CLOSED_GDELTA = prove
 (`!top:A topology s.
     normal_space top /\ closed_in top s /\ gdelta_in top s
     ==> ?f. continuous_map(top, euclideanreal) f /\
             (!x. x IN topspace top ==> &0 <= f x /\ f x <= &1) /\
             (!x. x IN s ==> f x = &0) /\
             (!x. x IN topspace top DIFF s ==> &0 < f x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GDELTA_IN_DESCENDING]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:A->bool) SUBSET topspace top` ASSUME_TAC THENL
  [ASM_MESON_TAC[CLOSED_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. (s:A->bool) SUBSET (c:num->A->bool) n` ASSUME_TAC THENL
  [GEN_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_GSPEC; IN_UNIV] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `?h:num->A->real.
     (!n. continuous_map(top, euclideanreal) (h n)) /\
     (!n x:A. x IN topspace top ==> &0 <= h n x /\ h n x <= &1) /\
     (!n x:A. x IN s ==> h n x = &0) /\
     (!n x:A. x IN topspace top DIFF (c:num->A->bool) n ==> h n x = &1)`
   STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN
    `!n:num. ?f:A->real.
       continuous_map(top, euclideanreal) f /\
       (!x. x IN topspace top ==> &0 <= f x /\ f x <= &1) /\
       (!x. x IN s ==> f x = &0) /\
       (!x. x IN topspace top DIFF (c:num->A->bool) n ==> f x = &1)`
    MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `s:A->bool`;
                    `topspace top DIFF (c:num->A->bool) n`;
                    `&0`; `&1`] URYSOHN_LEMMA) THEN
    ANTS_TAC THENL
    [ASM_SIMP_TAC[REAL_POS; CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE] THEN
     ASM SET_TAC[];
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:A->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `f:A->real` THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o
       GEN_REWRITE_RULE I [CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
     SIMP_TAC[];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(f:A->real) y IN real_interval[&0,&1]` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o
        CONJUNCT2 o GEN_REWRITE_RULE I [CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_REAL_INTERVAL]];
     ASM_MESON_TAC[]];
    ALL_TAC] THEN
   REWRITE_TAC[SKOLEM_THM] THEN MESON_TAC[];
   ALL_TAC] THEN
  (* Apply CONTINUOUS_MAP_UNIFORMLY_CAUCHY_LIMIT to partial sums *)
  MP_TAC(ISPECL
   [`top:A topology`; `real_euclidean_metric`;
    `(\n (x:A). sum(0..n) (\k. (h:num->A->real) k x *
                                inv(&2 pow (k + 1))))`]
   CONTINUOUS_MAP_UNIFORMLY_CAUCHY_LIMIT) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; MCOMPLETE_REAL_EUCLIDEAN_METRIC;
                  MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
  ANTS_TAC THENL
  [(* Two conditions: eventually continuous, and Cauchy *)
   CONJ_TAC THENL
   [(* Eventually continuous: each partial sum is continuous *)
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    REPEAT STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    (* Cauchy condition: partial sums form a uniform Cauchy sequence *)
    REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    SUBGOAL_THEN
     `!a b. sum(a..b) (\k. inv(&2) pow (k + 1)) <= inv(&2) pow a`
     ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN
     SUBGOAL_THEN
      `(\k. inv(&2) pow (k + 1)) =
       (\k. inv(&2) pow k - inv(&2) pow (k + 1))`
      SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      REWRITE_TAC[GSYM ADD1; real_pow] THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[SUM_DIFFS] THEN COND_CASES_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
       MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
       MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV]];
     ALL_TAC] THEN
    MATCH_MP_TAC WLOG_LT THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
    CONJ_TAC THENL
    [MESON_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m':num`; `q:num`] THEN DISCH_TAC THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    (* Express difference as partial sum over (m'+1..q) *)
    SUBGOAL_THEN
     `sum(0..q) (\k. (h:num->A->real) k y * inv (&2 pow (k + 1))) -
      sum(0..m') (\k. h k y * inv (&2 pow (k + 1))) =
      sum(m'+1..q) (\k. h k y * inv (&2 pow (k + 1)))`
     SUBST1_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `a + b = c ==> c - a = b`) THEN
     MATCH_MP_TAC SUM_COMBINE_R THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    (* The sum is non-negative, so abs = identity *)
    SUBGOAL_THEN
     `&0 <= sum(m'+1..q)
             (\k. (h:num->A->real) k y * inv (&2 pow (k + 1)))`
     (fun th -> REWRITE_TAC[MATCH_MP
       (REAL_ARITH `&0 <= x ==> abs x = x`) th]) THENL
    [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_LE_INV THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
     ALL_TAC] THEN
    (* Chain: sum <= geom_sum <= inv(2)^(m'+1) <= inv(2)^N < e *)
    TRANS_TAC REAL_LET_TRANS `inv(&2) pow N` THEN
    CONJ_TAC THENL
    [TRANS_TAC REAL_LE_TRANS `inv(&2) pow (m' + 1)` THEN
     CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS
       `sum(m'+1..q) (\k. inv(&2) pow (k + 1))` THEN
      CONJ_TAC THENL
      [(* Each term: h k y * inv(2^(k+1)) <= inv(2)^(k+1) *)
       MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN
       STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC[REAL_INV_POW] THEN
       GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
       MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
       (* Geometric sum <= inv(2)^(m'+1): use helper *)
       ASM_MESON_TAC[]];
      (* inv(2)^(m'+1) <= inv(2)^N by monotonicity *)
      MATCH_MP_TAC REAL_POW_MONO_INV THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_ARITH_TAC];
     ASM_MESON_TAC[]]];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:A->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:A->real` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [(* Part 1: g bounded in [0,1] *)
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   CONJ_TAC THENL
   [(* g x >= 0: contradiction if g x < 0 *)
    SUBGOAL_THEN `~((g:A->real) x < &0)`
      (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `--((g:A->real) x)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    (* Need: partial sum >= 0 *)
    SUBGOAL_THEN
     `&0 <= sum(0..M)
              (\k. (h:num->A->real) k x * inv(&2 pow (k + 1)))`
     (fun th -> MP_TAC th THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [ASM_MESON_TAC[];
     MATCH_MP_TAC REAL_LE_INV THEN
     MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
    (* g x <= 1: contradiction if g x > 1 *)
    SUBGOAL_THEN `~(&1 < (g:A->real) x)`
      (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `(g:A->real) x - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    (* Need: partial sum <= 1 *)
    SUBGOAL_THEN
     `sum(0..M) (\k. (h:num->A->real) k x * inv(&2 pow (k + 1))) <= &1`
     (fun th -> MP_TAC th THEN ASM_REAL_ARITH_TAC) THEN
    TRANS_TAC REAL_LE_TRANS
      `sum(0..M) (\k. inv(&2) pow (k + 1))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN
     STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[REAL_INV_POW] THEN
     GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
     SUBGOAL_THEN
      `(\k. inv(&2) pow (k + 1)) =
       (\k. inv(&2) pow k - inv(&2) pow (k + 1))`
      SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      REWRITE_TAC[GSYM ADD1; real_pow] THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[SUM_DIFFS] THEN COND_CASES_TAC THENL
      [REWRITE_TAC[real_pow] THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &1 - y <= &1`) THEN
       MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
       CONV_TAC REAL_RAT_REDUCE_CONV]]]];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [(* Part 2: g = 0 on s *)
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
    `!n. sum(0..n) (\k. (h:num->A->real) k x * inv(&2 pow (k+1))) = &0`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SUBGOAL_THEN `(h:num->A->real) i x = &0` SUBST1_TAC THENL
    [ASM_MESON_TAC[]; REWRITE_TAC[REAL_MUL_LZERO]];
    ALL_TAC] THEN
   SUBGOAL_THEN `~(&0 < abs((g:A->real) x))`
    (fun th -> ASM_MESON_TAC[th;
       REAL_ARITH `~(&0 < abs x) ==> x = &0`]) THEN
   DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `abs((g:A->real) x)`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M:num`)) THEN
   REWRITE_TAC[LE_REFL] THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN ASM_REAL_ARITH_TAC;
   (* Part 3: g > 0 on complement of s *)
   X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
   (* x not in s = INTERS{c n}, so there exists n0 with x not in c(n0) *)
   SUBGOAL_THEN `?n0:num. ~((x:A) IN c n0)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   (* h(n0)(x) = 1 *)
   SUBGOAL_THEN `(h:num->A->real) n0 x = &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`n0:num`; `x:A`]) THEN
    ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
   (* For n >= n0, partial sum >= inv(2^(n0+1)) *)
   SUBGOAL_THEN
    `!n. n0 <= n ==>
         inv(&2 pow (n0 + 1)) <=
         sum(0..n) (\k. (h:num->A->real) k x * inv(&2 pow (k + 1)))`
    ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS
     `sum {n0} (\k. (h:num->A->real) k x * inv(&2 pow (k + 1)))` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[SUM_SING] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     ASM_REWRITE_TAC[REAL_MUL_LID; REAL_LE_REFL];
     MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
     REWRITE_TAC[FINITE_NUMSEG] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SING; IN_NUMSEG] THEN ASM_ARITH_TAC;
      X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_DIFF; IN_NUMSEG; IN_SING] THEN
      STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [ASM_MESON_TAC[];
       MATCH_MP_TAC REAL_LE_INV THEN
       MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC]]];
    ALL_TAC] THEN
   (* Contradiction: assume g(x) <= 0 *)
   SUBGOAL_THEN `~((g:A->real) x <= &0)`
     (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
   DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `inv(&2 pow (n0 + 1))`) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   DISCH_THEN(X_CHOOSE_THEN `M:num` ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `M + n0:num`) THEN
   REWRITE_TAC[LE_ADD] THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `M + n0:num`) THEN
   REWRITE_TAC[LE_ADDR] THEN
   DISCH_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Nagata-Smirnov metrization (hard direction):
   regular Hausdorff + sigma-locally-finite base => metrizable *)
let NAGATA_SMIRNOV_METRIZATION = prove
 (`!top:A topology.
        regular_space top /\ hausdorff_space top /\
        (?B. (!b. b IN B ==> open_in top b) /\
             (!x u. open_in top u /\ x IN u
                    ==> ?b. b IN B /\ x IN b /\ b SUBSET u) /\
             sigma_locally_finite_in top B)
        ==> metrizable_space top`,
  let REAL_OPEN_ABS_LT = prove
   (`!a:real d. &0 < d ==> real_open {t | abs(t - a) < d}`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[real_open; IN_ELIM_THM] THEN
    X_GEN_TAC `t0:real` THEN DISCH_TAC THEN
    EXISTS_TAC `d - abs(t0 - a)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t':real` THEN ASM_REAL_ARITH_TAC) in
  GEN_TAC THEN STRIP_TAC THEN
  (* Handle empty topspace *)
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
  [SUBGOAL_THEN `top:A topology = discrete_topology ({}:A->bool)`
    (fun th -> REWRITE_TAC[th; METRIZABLE_SPACE_DISCRETE_TOPOLOGY]) THEN
   REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_DISCRETE_TOPOLOGY; SUBSET_EMPTY] THEN
   GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_IN_EMPTY]];
   ALL_TAC] THEN
  (* Unfold sigma-LF to get Bn decomposition *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sigma_locally_finite_in]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Bn:num->(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Reconstruct sigma_locally_finite_in for later use *)
  SUBGOAL_THEN `sigma_locally_finite_in top (B:(A->bool)->bool)`
    ASSUME_TAC THENL
  [REWRITE_TAC[sigma_locally_finite_in] THEN
   EXISTS_TAC `Bn:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Show normality *)
  SUBGOAL_THEN `normal_space (top:A topology)` ASSUME_TAC THENL
  [MATCH_MP_TAC NORMAL_SPACE_SIGMA_LOCALLY_FINITE_BASE THEN
   EXISTS_TAC `B:(A->bool)->bool` THEN
   REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  (* Show closed sets are G_delta *)
  SUBGOAL_THEN `!s:A->bool. closed_in top s ==> gdelta_in top s`
    ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC CLOSED_GDELTA_IN_SIGMA_LF_BASE THEN
   EXISTS_TAC `B:(A->bool)->bool` THEN
   REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  (* Construct separating functions: for each b IN B, get g_b *)
  SUBGOAL_THEN
    `!b:A->bool. b IN B ==>
        ?f. continuous_map(top, euclideanreal) f /\
            (!x. x IN topspace top ==> &0 <= f x /\ f x <= &1) /\
            (!x. x IN topspace top /\ ~(x IN b) ==> f x = &0) /\
            (!x. x IN b ==> &0 < f x)`
  MP_TAC THENL
  [X_GEN_TAC `b:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN `open_in top (b:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(b:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
   MP_TAC(ISPECL [`top:A topology`; `topspace top DIFF b:A->bool`]
    URYSOHN_FUNCTION_CLOSED_GDELTA) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC CLOSED_IN_DIFF THEN
     ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     MATCH_MP_TAC CLOSED_IN_DIFF THEN
     ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE]];
    DISCH_THEN(X_CHOOSE_THEN `f:A->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `f:A->real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
    [REWRITE_TAC[GSYM IN_DIFF] THEN FIRST_ASSUM ACCEPT_TAC;
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN
     UNDISCH_TAC
      `!x:A. x IN topspace top DIFF (topspace top DIFF b) ==> &0 < f x` THEN
     DISCH_THEN MATCH_MP_TAC THEN
     UNDISCH_TAC `(x:A) IN b` THEN
     UNDISCH_TAC `(b:A->bool) SUBSET topspace top` THEN
     SET_TAC[]]];
   ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->A->real` STRIP_ASSUME_TAC) THEN
  (* Now: g b continuous, [0,1]-valued, g b = 0 off b, g b > 0 on b *)
  (* Show B is nonempty *)
  SUBGOAL_THEN `~(B:(A->bool)->bool = {})` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
   DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `topspace top:A->bool`]) THEN
   REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; MESON_TAC[]];
   ALL_TAC] THEN
  (* Define the embedding into funspace *)
  ABBREV_TAC
    `J = {(n:num,b:A->bool) | b IN Bn n}` THEN
  (* J is nonempty since B = UNIONS{Bn n} is nonempty *)
  SUBGOAL_THEN `~(J:num#(A->bool)->bool = {})` ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   SUBGOAL_THEN `?n0:num (b0:A->bool). b0 IN Bn n0` MP_TAC THENL
   [UNDISCH_TAC `~(B:(A->bool)->bool = {})` THEN
    UNDISCH_TAC `B = UNIONS {(Bn:num->(A->bool)->bool) n | n IN (:num)}` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n0:num`; `b0:A->bool`] THEN DISCH_TAC THEN
    EXISTS_TAC `n0:num,(b0:A->bool)` THEN
    EXISTS_TAC `n0:num` THEN EXISTS_TAC `b0:A->bool` THEN
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step: Introduce the distance function (uncurried for is_metric_space) *)
  SUBGOAL_THEN
    `?d:A#A->real. !x y.
       d(x,y) = sup {abs(g (b:A->bool) x * inv(&(SUC n)) -
                         g b y * inv(&(SUC n))) |
                     n,b | b IN Bn n}`
    (X_CHOOSE_TAC `d:A#A->real`) THENL
  [EXISTS_TAC `\p:A#A.
     sup {abs(g (b:A->bool) (FST p) * inv(&(SUC n)) -
              g b (SND p) * inv(&(SUC n))) |
          n,b | b IN Bn n}` THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[FST; SND];
   ALL_TAC] THEN
  (* Step: The sup set is always nonempty *)
  SUBGOAL_THEN
    `!x:A y:A.
       ~({abs(g (b:A->bool) x * inv(&(SUC n)) -
              g b y * inv(&(SUC n))) |
          n,b | b IN Bn n} = {})`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   UNDISCH_TAC `~(J:num#(A->bool)->bool = {})` THEN
   EXPAND_TAC "J" THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  (* Helper: b IN Bn n ==> b IN B *)
  SUBGOAL_THEN `!n:num (b:A->bool). b IN Bn n ==> b IN B` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   UNDISCH_TAC `B = UNIONS {(Bn:num->(A->bool)->bool) n | n IN (:num)}` THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
   EXISTS_TAC `(Bn:num->(A->bool)->bool) n` THEN
   CONJ_TAC THENL
   [EXISTS_TAC `n:num` THEN REFL_TAC;
    FIRST_ASSUM ACCEPT_TAC];
   ALL_TAC] THEN
  (* Helper: extract g bounds for easier use *)
  SUBGOAL_THEN
    `!b:A->bool x:A.
       b IN B /\ x IN topspace top ==> &0 <= g b x /\ g b x <= &1`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN
   UNDISCH_TAC `!b:A->bool. b IN B
     ==> continuous_map(top,euclideanreal) (g b) /\
         (!x. x IN topspace top ==> &0 <= g b x /\ g b x <= &1) /\
         (!x. x IN topspace top /\ ~(x IN b) ==> g b x = &0) /\
         (!x. x IN b ==> &0 < g b x)` THEN
   DISCH_THEN(MP_TAC o SPEC `b:A->bool`) THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Step: The sup set is bounded above by &1 for x,y in topspace *)
  SUBGOAL_THEN
    `!x:A y:A z.
       x IN topspace top /\ y IN topspace top /\
       z IN {abs(g (b:A->bool) x * inv(&(SUC n)) -
                  g b y * inv(&(SUC n))) |
              n,b | b IN Bn n}
       ==> z <= &1`
    ASSUME_TAC THENL
  [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `n':num` (X_CHOOSE_THEN `b':A->bool`
         (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))) THEN
   MATCH_MP_TAC(REAL_ARITH
     `&0 <= u /\ u <= &1 /\ &0 <= v /\ v <= &1 ==> abs(u - v) <= &1`) THEN
   SUBGOAL_THEN `(b':A->bool) IN B` ASSUME_TAC THENL
   [UNDISCH_TAC `!n:num (b:A->bool). b IN Bn n ==> b IN B` THEN
    DISCH_THEN(MP_TAC o SPECL [`n':num`; `b':A->bool`]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (g:(A->bool)->A->real) b' x /\ g b' x <= &1`
     STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!b:A->bool x:A.
      b IN B /\ x IN topspace top ==> &0 <= g b x /\ g b x <= &1` THEN
    DISCH_THEN(MP_TAC o SPECL [`b':A->bool`; `x:A`]) THEN
    ANTS_TAC THENL
    [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (g:(A->bool)->A->real) b' y /\ g b' y <= &1`
     STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!b:A->bool x:A.
      b IN B /\ x IN topspace top ==> &0 <= g b x /\ g b x <= &1` THEN
    DISCH_THEN(MP_TAC o SPECL [`b':A->bool`; `y:A`]) THEN
    ANTS_TAC THENL
    [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= inv(&(SUC n')) /\ inv(&(SUC n')) <= &1`
     STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
     ARITH_TAC];
    ALL_TAC] THEN
   REPEAT CONJ_TAC THENL
   [(* 0 <= g b' x * inv(SUC n') *)
    MATCH_MP_TAC REAL_LE_MUL THEN
    UNDISCH_TAC `&0 <= (g:(A->bool)->A->real) b' x` THEN
    UNDISCH_TAC `&0 <= inv(&(SUC n'))` THEN REAL_ARITH_TAC;
    (* g b' x * inv(SUC n') <= 1 *)
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL2 THEN
     UNDISCH_TAC `&0 <= (g:(A->bool)->A->real) b' x` THEN
     UNDISCH_TAC `(g:(A->bool)->A->real) b' x <= &1` THEN
     UNDISCH_TAC `&0 <= inv(&(SUC n'))` THEN
     UNDISCH_TAC `inv(&(SUC n')) <= &1` THEN REAL_ARITH_TAC;
     REAL_ARITH_TAC];
    (* 0 <= g b' y * inv(SUC n') *)
    MATCH_MP_TAC REAL_LE_MUL THEN
    UNDISCH_TAC `&0 <= (g:(A->bool)->A->real) b' y` THEN
    UNDISCH_TAC `&0 <= inv(&(SUC n'))` THEN REAL_ARITH_TAC;
    (* g b' y * inv(SUC n') <= 1 *)
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL2 THEN
     UNDISCH_TAC `&0 <= (g:(A->bool)->A->real) b' y` THEN
     UNDISCH_TAC `(g:(A->bool)->A->real) b' y <= &1` THEN
     UNDISCH_TAC `&0 <= inv(&(SUC n'))` THEN
     UNDISCH_TAC `inv(&(SUC n')) <= &1` THEN REAL_ARITH_TAC;
     REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Step: is_metric_space -- structured into 4 axioms *)
  SUBGOAL_THEN `is_metric_space(topspace top:A->bool, d:A#A->real)`
    ASSUME_TAC THENL
  [REWRITE_TAC[is_metric_space] THEN REPEAT CONJ_TAC THENL
   [(* Non-negativity: d(x,y) >= 0 *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `!x:A y:A. d(x,y) = sup {abs(g (b:A->bool) x *
      inv(&(SUC n)) - g b y * inv(&(SUC n))) | n,b | b IN Bn n}` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &1 ==> &0 <= x`) THEN
    MATCH_MP_TAC REAL_SUP_BOUNDS THEN CONJ_TAC THENL
    [UNDISCH_TAC `!x:A y:A.
       ~({abs(g (b:A->bool) x * inv(&(SUC n)) -
              g b y * inv(&(SUC n))) |
          n,b | b IN Bn n} = {})` THEN
     DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
     DISCH_THEN ACCEPT_TAC;
     X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     DISCH_THEN(X_CHOOSE_THEN `n':num` (X_CHOOSE_THEN `b':A->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
     REWRITE_TAC[REAL_ABS_POS] THEN
     UNDISCH_TAC `!x:A y:A z.
       x IN topspace top /\ y IN topspace top /\
       z IN {abs(g (b:A->bool) x * inv(&(SUC n)) -
                 g b y * inv(&(SUC n))) |
             n,b | b IN Bn n}
       ==> z <= &1` THEN
     DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`;
       `abs((g:(A->bool)->A->real) b' x * inv(&(SUC n')) -
            g b' y * inv(&(SUC n')))`]) THEN
     ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       FIRST_ASSUM ACCEPT_TAC;
       REWRITE_TAC[IN_ELIM_THM] THEN
       EXISTS_TAC `n':num` THEN EXISTS_TAC `b':A->bool` THEN
       CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REFL_TAC]];
      DISCH_THEN ACCEPT_TAC]];
    (* Identity: d(x,y) = 0 <=> x = y *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
    [(* Forward: d(x,y) = 0 ==> x = y *)
     DISCH_TAC THEN
     ASM_CASES_TAC `x:A = y` THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `&0 < (d:A#A->real)(x,y)` (fun th ->
       MP_TAC th THEN UNDISCH_TAC `(d:A#A->real)(x,y) = &0` THEN
       REAL_ARITH_TAC) THEN
     UNDISCH_TAC `!x:A y:A. d(x,y) = sup {abs(g (b:A->bool) x *
       inv(&(SUC n)) - g b y * inv(&(SUC n))) | n,b | b IN Bn n}` THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
     (* Goal: 0 < sup{...} -- find separating base element *)
     UNDISCH_TAC `!x:A u. open_in top u /\ x IN u ==>
       ?b. b IN B /\ x IN b /\ b SUBSET u` THEN
     DISCH_THEN(MP_TAC o SPECL [`x:A`; `topspace top DIFF {y:A}`]) THEN
     ANTS_TAC THENL
     [CONJ_TAC THENL
      [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
       MATCH_MP_TAC CLOSED_IN_HAUSDORFF_SING THEN
       CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
       REWRITE_TAC[IN_DIFF; IN_SING] THEN
       CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `b0:A->bool` STRIP_ASSUME_TAC) THEN
     (* ~(y IN b0) *)
     SUBGOAL_THEN `~((y:A) IN b0)` ASSUME_TAC THENL
     [UNDISCH_TAC `(b0:A->bool) SUBSET topspace top DIFF {y:A}` THEN
      SET_TAC[];
      ALL_TAC] THEN
     (* b0 IN Bn n0 for some n0 *)
     SUBGOAL_THEN `?n0:num. (b0:A->bool) IN Bn n0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(b0:A->bool) IN B` THEN
      UNDISCH_TAC `B = UNIONS {(Bn:num->(A->bool)->bool) n | n IN (:num)}` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:(A->bool)->bool`
        (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `m:num` ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      EXISTS_TAC `m:num` THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
     (* Extract g properties for b0 *)
     UNDISCH_TAC `!b:A->bool. b IN B ==>
       continuous_map(top,euclideanreal) (g b) /\
       (!x. x IN topspace top ==> &0 <= g b x /\ g b x <= &1) /\
       (!x. x IN topspace top /\ ~(x IN b) ==> g b x = &0) /\
       (!x. x IN b ==> &0 < g b x)` THEN
     DISCH_THEN(MP_TAC o SPEC `b0:A->bool`) THEN
     ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
       (CONJUNCTS_THEN2 (K ALL_TAC)
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
     (* g(b0)(x) > 0 *)
     SUBGOAL_THEN `&0 < (g:(A->bool)->A->real) b0 x` ASSUME_TAC THENL
     [UNDISCH_TAC `!x:A. x IN b0 ==> &0 < (g:(A->bool)->A->real) b0 x` THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] THEN
     (* g(b0)(y) = 0 *)
     SUBGOAL_THEN `(g:(A->bool)->A->real) b0 y = &0` ASSUME_TAC THENL
     [UNDISCH_TAC
        `!x:A. x IN topspace top /\ ~(x IN b0) ==>
               (g:(A->bool)->A->real) b0 x = &0` THEN
      DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
      ANTS_TAC THENL
      [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] THEN
     (* 0 < g b0 x * inv(SUC n0) and this element is in the sup set *)
     MATCH_MP_TAC REAL_LTE_TRANS THEN
     EXISTS_TAC `(g:(A->bool)->A->real) b0 x * inv(&(SUC n0))` THEN
     CONJ_TAC THENL
     [(* 0 < g b0 x * inv(SUC n0) *)
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       MATCH_MP_TAC REAL_LT_INV THEN
       REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
      (* g b0 x * inv(SUC n0) <= sup{...} *)
      SUBGOAL_THEN
        `(g:(A->bool)->A->real) b0 x * inv(&(SUC n0)) =
         abs(g b0 x * inv(&(SUC n0)) - g b0 y * inv(&(SUC n0)))`
        SUBST1_TAC THENL
      [UNDISCH_TAC `(g:(A->bool)->A->real) b0 y = &0` THEN
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
       CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ABS_REFL] THEN
       MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < (g:(A->bool)->A->real) b0 x` THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC];
       ALL_TAC] THEN
      (* abs(...) <= sup{...} via ELEMENT_LE_SUP *)
      MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
      [(* bounded above *)
       EXISTS_TAC `&1` THEN
       X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
       DISCH_THEN(X_CHOOSE_THEN `n':num` (X_CHOOSE_THEN `b':A->bool`
         (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
       UNDISCH_TAC `!x:A y:A z.
         x IN topspace top /\ y IN topspace top /\
         z IN {abs(g (b:A->bool) x * inv(&(SUC n)) -
                   g b y * inv(&(SUC n))) |
               n,b | b IN Bn n}
         ==> z <= &1` THEN
       DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`;
         `abs((g:(A->bool)->A->real) b' x * inv(&(SUC n')) -
              g b' y * inv(&(SUC n')))`]) THEN
       ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
        [FIRST_ASSUM ACCEPT_TAC;
         FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[IN_ELIM_THM] THEN
         EXISTS_TAC `n':num` THEN EXISTS_TAC `b':A->bool` THEN
         CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REFL_TAC]];
        DISCH_THEN ACCEPT_TAC];
       (* element IN S *)
       REWRITE_TAC[IN_ELIM_THM] THEN
       EXISTS_TAC `n0:num` THEN EXISTS_TAC `b0:A->bool` THEN
       CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REFL_TAC]]];
     (* Backward: x = y ==> d(x,y) = 0 *)
     DISCH_THEN SUBST1_TAC THEN
     UNDISCH_TAC `!x:A y:A. d(x,y) = sup {abs(g (b:A->bool) x *
       inv(&(SUC n)) - g b y * inv(&(SUC n))) | n,b | b IN Bn n}` THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
     REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
     MATCH_MP_TAC REAL_SUP_BOUNDS THEN CONJ_TAC THENL
     [UNDISCH_TAC `!x:A y:A.
        ~({abs(g (b:A->bool) x * inv(&(SUC n)) -
               g b y * inv(&(SUC n))) |
           n,b | b IN Bn n} = {})` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:A`; `x:A`]) THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM];
      X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `n':num` (X_CHOOSE_THEN `b':A->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
      REAL_ARITH_TAC]];
    (* Symmetry: d(x,y) = d(y,x) *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `!x:A y:A. d(x,y) = sup {abs(g (b:A->bool) x *
      inv(&(SUC n)) - g b y * inv(&(SUC n))) | n,b | b IN Bn n}` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ABS_SUB] THEN
    REFL_TAC;
    (* Triangle inequality: d(x,z) <= d(x,y) + d(y,z) *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `!x:A y:A. d(x,y) = sup {abs(g (b:A->bool) x *
      inv(&(SUC n)) - g b y * inv(&(SUC n))) | n,b | b IN Bn n}` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    (* Goal: sup S_xz <= sup S_xy + sup S_yz *)
    MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
    [(* Nonemptiness of S_xz *)
     UNDISCH_TAC `!x:A y:A.
       ~({abs(g (b:A->bool) x * inv(&(SUC n)) -
              g b y * inv(&(SUC n))) |
          n,b | b IN Bn n} = {})` THEN
     DISCH_THEN(MP_TAC o SPECL [`x:A`; `z:A`]) THEN
     DISCH_THEN ACCEPT_TAC;
     (* For each element w of S_xz: w <= sup S_xy + sup S_yz *)
     X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
     DISCH_THEN(X_CHOOSE_THEN `n':num` (X_CHOOSE_THEN `b':A->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
     (* |a-c| <= |a-b| + |b-c| then bound each by its sup *)
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `abs((g:(A->bool)->A->real) b' x * inv(&(SUC n')) -
                     g b' y * inv(&(SUC n'))) +
                 abs(g b' y * inv(&(SUC n')) -
                     g b' z * inv(&(SUC n')))` THEN
     CONJ_TAC THENL
     [(* Real triangle inequality: |a-c| <= |a-b| + |b-c| *)
      REAL_ARITH_TAC;
      (* |...(x,y)| + |...(y,z)| <= sup S_xy + sup S_yz *)
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
      [(* |...(x,y)| <= sup S_xy via ELEMENT_LE_SUP *)
       MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
       [(* S_xy bounded above *)
        EXISTS_TAC `&1` THEN
        X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `n'':num` (X_CHOOSE_THEN `b'':A->bool`
          (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
        UNDISCH_TAC `!x:A y:A z.
          x IN topspace top /\ y IN topspace top /\
          z IN {abs(g (b:A->bool) x * inv(&(SUC n)) -
                    g b y * inv(&(SUC n))) |
                n,b | b IN Bn n}
          ==> z <= &1` THEN
        DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`;
          `abs((g:(A->bool)->A->real) b'' x * inv(&(SUC n'')) -
               g b'' y * inv(&(SUC n'')))`]) THEN
        ANTS_TAC THENL
        [REPEAT CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM ACCEPT_TAC;
          REWRITE_TAC[IN_ELIM_THM] THEN
          EXISTS_TAC `n'':num` THEN EXISTS_TAC `b'':A->bool` THEN
          CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REFL_TAC]];
         DISCH_THEN ACCEPT_TAC];
        (* element IN S_xy *)
        REWRITE_TAC[IN_ELIM_THM] THEN
        EXISTS_TAC `n':num` THEN EXISTS_TAC `b':A->bool` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REFL_TAC]];
       (* |...(y,z)| <= sup S_yz via ELEMENT_LE_SUP *)
       MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
       [(* S_yz bounded above *)
        EXISTS_TAC `&1` THEN
        X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `n'':num` (X_CHOOSE_THEN `b'':A->bool`
          (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
        UNDISCH_TAC `!x:A y:A z.
          x IN topspace top /\ y IN topspace top /\
          z IN {abs(g (b:A->bool) x * inv(&(SUC n)) -
                    g b y * inv(&(SUC n))) |
                n,b | b IN Bn n}
          ==> z <= &1` THEN
        DISCH_THEN(MP_TAC o SPECL [`y:A`; `z:A`;
          `abs((g:(A->bool)->A->real) b'' y * inv(&(SUC n'')) -
               g b'' z * inv(&(SUC n'')))`]) THEN
        ANTS_TAC THENL
        [REPEAT CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM ACCEPT_TAC;
          REWRITE_TAC[IN_ELIM_THM] THEN
          EXISTS_TAC `n'':num` THEN EXISTS_TAC `b'':A->bool` THEN
          CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REFL_TAC]];
         DISCH_THEN ACCEPT_TAC];
        (* element IN S_yz *)
        REWRITE_TAC[IN_ELIM_THM] THEN
        EXISTS_TAC `n':num` THEN EXISTS_TAC `b':A->bool` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REFL_TAC]]]]]];
   ALL_TAC] THEN
  (* Step: topology equivalence top = mtopology(metric(topspace top, d)) *)
  SUBGOAL_THEN
    `top:A topology = mtopology(metric(topspace top:A->bool, d:A#A->real))`
    (fun th -> REWRITE_TAC[metrizable_space] THEN
               EXISTS_TAC `metric(topspace top:A->bool, d:A#A->real)` THEN
               ACCEPT_TAC th) THEN
  (* Establish mspace and mdist for our metric *)
  SUBGOAL_THEN
    `mspace(metric(topspace top:A->bool, d:A#A->real)) = topspace top`
    ASSUME_TAC THENL
  [MATCH_MP_TAC MSPACE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `mdist(metric(topspace top:A->bool, d:A#A->real)) = d:A#A->real`
    ASSUME_TAC THENL
  [MATCH_MP_TAC MDIST THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* Helper: d(x,x) = 0 *)
  SUBGOAL_THEN `!a:A. a IN topspace top ==> (d:A#A->real)(a,a) = &0`
    ASSUME_TAC THENL
  [X_GEN_TAC `a:A` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`metric(topspace top:A->bool,d:A#A->real)`; `a:A`]
     MDIST_REFL) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* d-ball openness: metric balls are open in top *)
  SUBGOAL_THEN
    `!x:A r. x IN topspace top /\ &0 < r
       ==> open_in top {y | y IN topspace top /\ (d:A#A->real)(x,y) < r}`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
   X_GEN_TAC `y0:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
   ABBREV_TAC `eps = r - (d:A#A->real)(x,y0)` THEN
   SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN
    UNDISCH_TAC `(d:A#A->real)(x,y0) < r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `?N0:num. ~(N0 = 0) /\ &0 < inv(&N0) /\ inv(&N0) < eps / &4`
     STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN
    UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* Get local finiteness neighborhoods for all n (via SKOLEM) *)
   SUBGOAL_THEN
     `?LF:num->A->bool. !n. open_in top (LF n) /\ y0 IN LF n /\
        FINITE {b:A->bool | b IN Bn n /\ ~(b INTER LF n = {})}`
     (X_CHOOSE_TAC `LF:num->A->bool`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `nn:num` THEN
    SUBGOAL_THEN `locally_finite_in top ((Bn:num->(A->bool)->bool) nn)`
      MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[locally_finite_in] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `y0:A`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Key subgoal: find V open with y0 IN V and d(y0,z) < eps for z in V *)
   SUBGOAL_THEN
     `?V:A->bool. open_in top V /\ y0 IN V /\
        !z. z IN V /\ z IN topspace top ==> (d:A#A->real)(y0,z) < eps`
     (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC) THENL
   [
    (* For each n <= N0, get open Vn containing y0 bounding all terms *)
    SUBGOAL_THEN
      `!n:num. n <= N0 ==>
         ?Vn:A->bool. open_in top Vn /\ y0 IN Vn /\
           !z:A (b:A->bool). z IN Vn /\ z IN topspace top /\
                 b IN (Bn:num->(A->bool)->bool) n
             ==> abs((g:(A->bool)->A->real) b z * inv(&(SUC n)) -
                     g b y0 * inv(&(SUC n))) <= eps / &2`
      ASSUME_TAC THENL
    [X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
     ABBREV_TAC
       `Fb = {b:A->bool | b IN (Bn:num->(A->bool)->bool) nn /\
                           ~(b INTER (LF:num->A->bool) nn = {})}` THEN
     SUBGOAL_THEN `FINITE (Fb:(A->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Fb" THEN
      UNDISCH_TAC `!n:num. open_in top ((LF:num->A->bool) n) /\
        y0 IN LF n /\
        FINITE {b:A->bool | b IN Bn n /\ ~(b INTER LF n = {})}` THEN
      DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN
      SIMP_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN
       `!b:A->bool. b IN Fb ==>
          ?Wb:A->bool. open_in top Wb /\ y0 IN Wb /\
            !z:A. z IN Wb /\ z IN topspace top
              ==> abs((g:(A->bool)->A->real) b z - g b y0) < eps / &2`
       ASSUME_TAC THENL
     [X_GEN_TAC `b0:A->bool` THEN DISCH_TAC THEN
      (* b0 IN Bn nn, hence b0 IN B *)
      SUBGOAL_THEN `(b0:A->bool) IN B` ASSUME_TAC THENL
      [UNDISCH_TAC `!n:num (b:A->bool). b IN Bn n ==> b IN B` THEN
       DISCH_THEN(MP_TAC o SPECL [`nn:num`; `b0:A->bool`]) THEN
       ANTS_TAC THENL
       [UNDISCH_TAC `(b0:A->bool) IN Fb` THEN
        EXPAND_TAC "Fb" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        SIMP_TAC[];
        DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
      (* g b0 is continuous *)
      SUBGOAL_THEN
        `continuous_map(top,euclideanreal) ((g:(A->bool)->A->real) b0)`
        ASSUME_TAC THENL
      [UNDISCH_TAC `!b:A->bool. b IN B
         ==> continuous_map(top,euclideanreal) (g b) /\
             (!x. x IN topspace top ==> &0 <= g b x /\ g b x <= &1) /\
             (!x. x IN topspace top /\ ~(x IN b) ==> g b x = &0) /\
             (!x. x IN b ==> &0 < g b x)` THEN
       DISCH_THEN(MP_TAC o SPEC `b0:A->bool`) THEN
       ASM_REWRITE_TAC[] THEN SIMP_TAC[];
       ALL_TAC] THEN
      (* The preimage of an open ball around g b0 y0 is open *)
      SUBGOAL_THEN
        `open_in top {z:A | z IN topspace top /\
           abs((g:(A->bool)->A->real) b0 z - g b0 y0) < eps / &2}`
        ASSUME_TAC THENL
      [MP_TAC(ISPECL [`(g:(A->bool)->A->real) b0`; `top:A topology`;
                        `euclideanreal`;
                        `{t:real | abs(t - (g:(A->bool)->A->real) b0 y0) < eps / &2}`]
          OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
       ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OPEN_IN] THEN
        MATCH_MP_TAC REAL_OPEN_ABS_LT THEN
        UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
       MATCH_MP_TAC(TAUT `(a ==> b) ==> a ==> b`) THEN
       DISCH_TAC THEN
       SUBGOAL_THEN
         `{z:A | z IN topspace top /\
            abs((g:(A->bool)->A->real) b0 z - g b0 y0) < eps / &2} =
          {x | x IN topspace top /\
            g b0 x IN {t:real | abs(t - g b0 y0) < eps / &2}}`
         SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
       ALL_TAC] THEN
      EXISTS_TAC
        `{z:A | z IN topspace top /\
           abs((g:(A->bool)->A->real) b0 z - g b0 y0) < eps / &2}` THEN
      REPEAT CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN
       UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC;
       REWRITE_TAC[IN_ELIM_THM] THEN
       REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
     DISCH_THEN(X_CHOOSE_TAC `Wb:(A->bool)->A->bool`) THEN
     ASM_CASES_TAC `Fb:(A->bool)->bool = {}` THENL
     [(* Fb = {}: LF nn suffices since all b INTER LF nn = {} *)
      EXISTS_TAC `(LF:num->A->bool) nn` THEN
      UNDISCH_TAC `!n:num. open_in top ((LF:num->A->bool) n) /\
        y0 IN LF n /\
        FINITE {b:A->bool | b IN Bn n /\ ~(b INTER LF n = {})}` THEN
      DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
      ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `z:A` THEN X_GEN_TAC `b:A->bool` THEN STRIP_TAC THEN
      (* b INTER LF nn = {} because b NOT IN Fb = {} *)
      SUBGOAL_THEN `(b:A->bool) INTER (LF:num->A->bool) nn = {}`
        ASSUME_TAC THENL
      [UNDISCH_TAC `Fb:(A->bool)->bool = {}` THEN EXPAND_TAC "Fb" THEN
       REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
       DISCH_THEN(MP_TAC o SPEC `b:A->bool`) THEN
       ASM_REWRITE_TAC[] THEN MESON_TAC[];
       ALL_TAC] THEN
      (* y0 NOT IN b and z NOT IN b *)
      SUBGOAL_THEN `~((y0:A) IN b)` ASSUME_TAC THENL
      [UNDISCH_TAC `(b:A->bool) INTER (LF:num->A->bool) nn = {}` THEN
       REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
       DISCH_THEN(MP_TAC o SPEC `y0:A`) THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      SUBGOAL_THEN `~((z:A) IN b)` ASSUME_TAC THENL
      [UNDISCH_TAC `(b:A->bool) INTER (LF:num->A->bool) nn = {}` THEN
       REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
       DISCH_THEN(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      (* b IN B *)
      SUBGOAL_THEN `(b:A->bool) IN B` ASSUME_TAC THENL
      [UNDISCH_TAC `!n:num (b:A->bool). b IN Bn n ==> b IN B` THEN
       DISCH_THEN(MP_TAC o SPECL [`nn:num`; `b:A->bool`]) THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
      (* g b y0 = 0 *)
      SUBGOAL_THEN `(g:(A->bool)->A->real) b y0 = &0` ASSUME_TAC THENL
      [UNDISCH_TAC `!b:A->bool. b IN B
         ==> continuous_map(top,euclideanreal) (g b) /\
             (!x. x IN topspace top ==> &0 <= g b x /\ g b x <= &1) /\
             (!x. x IN topspace top /\ ~(x IN b) ==> g b x = &0) /\
             (!x. x IN b ==> &0 < g b x)` THEN
       DISCH_THEN(MP_TAC o SPEC `b:A->bool`) THEN ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o SPEC `y0:A` o el 2 o CONJUNCTS) THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      (* g b z = 0 *)
      SUBGOAL_THEN `(g:(A->bool)->A->real) b z = &0` ASSUME_TAC THENL
      [UNDISCH_TAC `!b:A->bool. b IN B
         ==> continuous_map(top,euclideanreal) (g b) /\
             (!x. x IN topspace top ==> &0 <= g b x /\ g b x <= &1) /\
             (!x. x IN topspace top /\ ~(x IN b) ==> g b x = &0) /\
             (!x. x IN b ==> &0 < g b x)` THEN
       DISCH_THEN(MP_TAC o SPEC `b:A->bool`) THEN ASM_REWRITE_TAC[] THEN
       DISCH_THEN(MP_TAC o SPEC `z:A` o el 2 o CONJUNCTS) THEN
       ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_REFL; REAL_ABS_NUM] THEN
      UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC;
      (* Fb != {}: use LF nn INTER INTERS(IMAGE Wb Fb) *)
      EXISTS_TAC
        `(LF:num->A->bool) nn INTER
         INTERS(IMAGE (Wb:(A->bool)->A->bool) Fb)` THEN
      REPEAT CONJ_TAC THENL
      [(* open_in *)
       MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
       [UNDISCH_TAC `!n:num. open_in top ((LF:num->A->bool) n) /\
          y0 IN LF n /\
          FINITE {b:A->bool | b IN Bn n /\ ~(b INTER LF n = {})}` THEN
        DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN SIMP_TAC[];
        ALL_TAC] THEN
       MATCH_MP_TAC OPEN_IN_INTERS THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE] THEN
        X_GEN_TAC `b0:A->bool` THEN DISCH_TAC THEN
        UNDISCH_TAC `!b:A->bool. b IN Fb ==>
          open_in top ((Wb:(A->bool)->A->bool) b) /\ y0 IN Wb b /\
          !z:A. z IN Wb b /\ z IN topspace top
            ==> abs((g:(A->bool)->A->real) b z - g b y0) < eps / &2` THEN
        DISCH_THEN(MP_TAC o SPEC `b0:A->bool`) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
       (* y0 IN LF nn INTER INTERS(IMAGE Wb Fb) *)
       REWRITE_TAC[IN_INTER; IN_INTERS; FORALL_IN_IMAGE] THEN
       CONJ_TAC THENL
       [UNDISCH_TAC `!n:num. open_in top ((LF:num->A->bool) n) /\
          y0 IN LF n /\
          FINITE {b:A->bool | b IN Bn n /\ ~(b INTER LF n = {})}` THEN
        DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN SIMP_TAC[];
        X_GEN_TAC `b0:A->bool` THEN DISCH_TAC THEN
        UNDISCH_TAC `!b:A->bool. b IN Fb ==>
          open_in top ((Wb:(A->bool)->A->bool) b) /\ y0 IN Wb b /\
          !z:A. z IN Wb b /\ z IN topspace top
            ==> abs((g:(A->bool)->A->real) b z - g b y0) < eps / &2` THEN
        DISCH_THEN(MP_TAC o SPEC `b0:A->bool`) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
       (* The bound *)
       REWRITE_TAC[IN_INTER; IN_INTERS; FORALL_IN_IMAGE] THEN
       X_GEN_TAC `z:A` THEN X_GEN_TAC `b0:A->bool` THEN STRIP_TAC THEN
       SUBGOAL_THEN
         `abs((g:(A->bool)->A->real) b0 z * inv(&(SUC nn)) -
              g b0 y0 * inv(&(SUC nn))) =
          abs(g b0 z - g b0 y0) * inv(&(SUC nn))`
         SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_SUB_RDISTRIB; REAL_ABS_MUL] THEN
        AP_TERM_TAC THEN REWRITE_TAC[REAL_ABS_REFL] THEN
        MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
       ASM_CASES_TAC `(b0:A->bool) IN Fb` THENL
       [(* b0 IN Fb *)
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs((g:(A->bool)->A->real) b0 z - g b0 y0)` THEN
        CONJ_TAC THENL
        [GEN_REWRITE_TAC (RAND_CONV) [GSYM REAL_MUL_RID] THEN
         MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_INV_LE_1 THEN
          REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
         MATCH_MP_TAC REAL_LT_IMP_LE THEN
         UNDISCH_TAC `!b:A->bool. b IN Fb ==>
           open_in top ((Wb:(A->bool)->A->bool) b) /\ y0 IN Wb b /\
           !z:A. z IN Wb b /\ z IN topspace top
             ==> abs((g:(A->bool)->A->real) b z - g b y0) < eps / &2` THEN
         DISCH_THEN(MP_TAC o SPEC `b0:A->bool`) THEN
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o SPEC `z:A` o CONJUNCT2 o CONJUNCT2) THEN
         ANTS_TAC THENL
         [SUBGOAL_THEN `(z:A) IN (Wb:(A->bool)->A->bool) b0`
            ASSUME_TAC THENL
          [ASM_MESON_TAC[]; ALL_TAC] THEN
          ASM_REWRITE_TAC[];
          DISCH_THEN ACCEPT_TAC]];
        (* b0 NOT IN Fb *)
        SUBGOAL_THEN `(b0:A->bool) INTER (LF:num->A->bool) nn = {}`
          ASSUME_TAC THENL
        [UNDISCH_TAC `~((b0:A->bool) IN Fb)` THEN
         EXPAND_TAC "Fb" THEN REWRITE_TAC[IN_ELIM_THM] THEN
         ASM_REWRITE_TAC[] THEN MESON_TAC[];
         ALL_TAC] THEN
        SUBGOAL_THEN `~((y0:A) IN b0)` ASSUME_TAC THENL
        [UNDISCH_TAC `(b0:A->bool) INTER (LF:num->A->bool) nn = {}` THEN
         REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
         DISCH_THEN(MP_TAC o SPEC `y0:A`) THEN
         UNDISCH_TAC `!n:num. open_in top ((LF:num->A->bool) n) /\
           y0 IN LF n /\
           FINITE {b:A->bool | b IN Bn n /\ ~(b INTER LF n = {})}` THEN
         DISCH_THEN(MP_TAC o SPEC `nn:num`) THEN SIMP_TAC[];
         ALL_TAC] THEN
        SUBGOAL_THEN `~((z:A) IN b0)` ASSUME_TAC THENL
        [UNDISCH_TAC `(b0:A->bool) INTER (LF:num->A->bool) nn = {}` THEN
         REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
         DISCH_THEN(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
        SUBGOAL_THEN `(b0:A->bool) IN B` ASSUME_TAC THENL
        [UNDISCH_TAC `!n:num (b:A->bool). b IN Bn n ==> b IN B` THEN
         DISCH_THEN(MP_TAC o SPECL [`nn:num`; `b0:A->bool`]) THEN
         ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(g:(A->bool)->A->real) b0 y0 = &0` ASSUME_TAC THENL
        [UNDISCH_TAC `!b:A->bool. b IN B
           ==> continuous_map(top,euclideanreal) (g b) /\
               (!x. x IN topspace top ==> &0 <= g b x /\ g b x <= &1) /\
               (!x. x IN topspace top /\ ~(x IN b) ==> g b x = &0) /\
               (!x. x IN b ==> &0 < g b x)` THEN
         DISCH_THEN(MP_TAC o SPEC `b0:A->bool`) THEN ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o SPEC `y0:A` o el 2 o CONJUNCTS) THEN
         ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(g:(A->bool)->A->real) b0 z = &0` ASSUME_TAC THENL
        [UNDISCH_TAC `!b:A->bool. b IN B
           ==> continuous_map(top,euclideanreal) (g b) /\
               (!x. x IN topspace top ==> &0 <= g b x /\ g b x <= &1) /\
               (!x. x IN topspace top /\ ~(x IN b) ==> g b x = &0) /\
               (!x. x IN b ==> &0 < g b x)` THEN
         DISCH_THEN(MP_TAC o SPEC `b0:A->bool`) THEN ASM_REWRITE_TAC[] THEN
         DISCH_THEN(MP_TAC o SPEC `z:A` o el 2 o CONJUNCTS) THEN
         ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
        UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC]]];
    ALL_TAC] THEN
    (* Skolemize *)
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_TAC `Vn:num->A->bool`) THEN
    (* V = INTERS {Vn n | n <= N0} *)
    EXISTS_TAC
      `INTERS (IMAGE (Vn:num->A->bool) {m:num | m <= N0})` THEN
    REPEAT CONJ_TAC THENL
    [(* open_in top V *)
     MATCH_MP_TAC OPEN_IN_INTERS THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LE];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      UNDISCH_TAC `~(N0 = 0)` THEN ARITH_TAC;
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])];
     (* y0 IN V *)
     REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
     X_GEN_TAC `m:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]);
     (* !z. z IN V /\ z IN topspace top ==> d(y0,z) < eps *)
     X_GEN_TAC `z:A` THEN
     REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
     STRIP_TAC THEN
     (* d(y0,z) = sup{...} *)
     UNDISCH_TAC `!x:A y:A. (d:A#A->real)(x,y) = sup {abs(g (b:A->bool) x *
       inv(&(SUC n)) - g b y * inv(&(SUC n))) | n,b | b IN Bn n}` THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
     (* sup S < eps follows from sup S <= eps/2 < eps *)
     MATCH_MP_TAC REAL_LET_TRANS THEN
     EXISTS_TAC `eps / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
      [(* Nonemptiness *)
       UNDISCH_TAC `!x:A y:A.
         ~({abs(g (b:A->bool) x * inv(&(SUC n)) -
                g b y * inv(&(SUC n))) |
            n,b | b IN Bn n} = {})` THEN
       DISCH_THEN(MP_TAC o SPECL [`y0:A`; `z:A`]) THEN
       DISCH_THEN ACCEPT_TAC;
       (* Every element <= eps/2 *)
       X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
       DISCH_THEN(X_CHOOSE_THEN `nn':num` (X_CHOOSE_THEN `b':A->bool`
         (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
       ASM_CASES_TAC `(nn':num) <= (N0:num)` THENL
       [(* nn' <= N0: use Vn property *)
        (* First derive z IN Vn nn' from !m. m <= N0 ==> z IN Vn m *)
        SUBGOAL_THEN `(z:A) IN (Vn:num->A->bool) nn'` ASSUME_TAC THENL
        [FIRST_X_ASSUM(MP_TAC o SPEC `nn':num`) THEN
         ASM_REWRITE_TAC[];
         ALL_TAC] THEN
        ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
        (* Push the Vn property for nn' *)
        FIRST_X_ASSUM(fun th ->
          let sp = SPEC `nn':num` th in
          try let _,c = dest_imp(concl sp) in
              if is_conj c then MP_TAC sp
              else failwith ""
          with _ -> failwith "") THEN
        (* Goal: (nn' <= N0 ==> conj) ==> abs(...) <= eps/2 *)
        ANTS_TAC THENL
        [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(fun th ->
          MP_TAC(SPECL [`z:A`; `b':A->bool`] (CONJUNCT2(CONJUNCT2 th)))) THEN
        ASM_REWRITE_TAC[];
        (* nn' > N0: bound by inv(N0) < eps/4 < eps/2 *)
        (* Step 1: b' IN B *)
        SUBGOAL_THEN `(b':A->bool) IN B` ASSUME_TAC THENL
        [ASM_MESON_TAC[];
         ALL_TAC] THEN
        (* Step 2: Factor out inv(SUC nn') *)
        SUBGOAL_THEN
          `abs((g:(A->bool)->A->real) b' y0 * inv(&(SUC nn')) -
               g b' z * inv(&(SUC nn'))) =
           abs(g b' y0 - g b' z) * inv(&(SUC nn'))`
          SUBST1_TAC THENL
        [REWRITE_TAC[GSYM REAL_SUB_RDISTRIB; REAL_ABS_MUL] THEN
         AP_TERM_TAC THEN REWRITE_TAC[REAL_ABS_REFL] THEN
         MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS];
         ALL_TAC] THEN
        (* Step 3: abs(g b' y0 - g b' z) <= 1 *)
        SUBGOAL_THEN `abs((g:(A->bool)->A->real) b' y0 - g b' z) <= &1`
          ASSUME_TAC THENL
        [SUBGOAL_THEN
           `&0 <= (g:(A->bool)->A->real) b' y0 /\ g b' y0 <= &1`
           STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[];
          ALL_TAC] THEN
         SUBGOAL_THEN
           `&0 <= (g:(A->bool)->A->real) b' z /\ g b' z <= &1`
           STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[];
          ALL_TAC] THEN
         ASM_REAL_ARITH_TAC;
         ALL_TAC] THEN
        (* Step 4: inv(SUC nn') <= inv(N0) *)
        SUBGOAL_THEN `inv(&(SUC nn')) <= inv(&(N0:num))` ASSUME_TAC THENL
        [MATCH_MP_TAC REAL_LE_INV2 THEN
         REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
         UNDISCH_TAC `~((nn':num) <= (N0:num))` THEN
         UNDISCH_TAC `~(N0:num = 0)` THEN
         ARITH_TAC;
         ALL_TAC] THEN
        (* Step 5: Combine: <= 1 * inv(N0) = inv(N0) < eps/4 < eps/2 *)
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1 * inv(&(N0:num))` THEN CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_MUL2 THEN
         ASM_REWRITE_TAC[REAL_ABS_POS] THEN
         MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_POS];
         REWRITE_TAC[REAL_MUL_LID] THEN
         MATCH_MP_TAC REAL_LT_IMP_LE THEN
         MATCH_MP_TAC REAL_LT_TRANS THEN
         EXISTS_TAC `eps / &4` THEN
         ASM_REWRITE_TAC[] THEN
         UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC]]];
      (* eps/2 < eps *)
      UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
   (* V works: it's contained in the d-ball via triangle inequality *)
   EXISTS_TAC `V:A->bool` THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
    [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    (* d(x,z) <= d(x,y0) + d(y0,z) < d(x,y0) + eps = r *)
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(d:A#A->real)(x,y0) + d(y0,z)` THEN
    CONJ_TAC THENL
    [(* triangle inequality: d(x,z) <= d(x,y0) + d(y0,z) *)
     MP_TAC(ISPECL [`metric(topspace top:A->bool,d:A#A->real)`;
                     `x:A`; `y0:A`; `z:A`] MDIST_TRIANGLE) THEN
     UNDISCH_TAC
       `mspace(metric(topspace top:A->bool,d:A#A->real)) = topspace top` THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
     UNDISCH_TAC
       `mdist(metric(topspace top:A->bool,d:A#A->real)) = (d:A#A->real)` THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
     DISCH_THEN MATCH_MP_TAC THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
     (* d(x,y0) + d(y0,z) < r via d(y0,z) < eps = r - d(x,y0) *)
     SUBGOAL_THEN `(d:A#A->real)(y0,z) < eps` MP_TAC THENL
     [UNDISCH_TAC
        `!z:A. z IN V /\ z IN topspace top ==> (d:A#A->real)(y0,z) < eps` THEN
      DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "eps" THEN REAL_ARITH_TAC]]];
   ALL_TAC] THEN
  (* Use TOPOLOGY_EQ *)
  REWRITE_TAC[TOPOLOGY_EQ] THEN X_GEN_TAC `u:A->bool` THEN EQ_TAC THENL
  [(* Forward: open_in top u ==> open_in (mtopology m) u *)
   DISCH_TAC THEN REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
    [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    (* Find base element b0 with x IN b0 SUBSET u *)
    UNDISCH_TAC `!x:A u:A->bool. open_in top u /\ x IN u
      ==> ?b. b IN B /\ x IN b /\ b SUBSET u` THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `u:A->bool`]) THEN
    ANTS_TAC THENL
    [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b0:A->bool` STRIP_ASSUME_TAC) THEN
    (* b0 IN Bn n0 for some n0 *)
    SUBGOAL_THEN `?n0:num. (b0:A->bool) IN Bn n0` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `(b0:A->bool) IN B` THEN
     UNDISCH_TAC `B = UNIONS {(Bn:num->(A->bool)->bool) n | n IN (:num)}` THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
     DISCH_THEN(X_CHOOSE_THEN `s:(A->bool)->bool`
       (CONJUNCTS_THEN2
         (X_CHOOSE_THEN `mm:num` ASSUME_TAC) ASSUME_TAC)) THEN
     FIRST_X_ASSUM SUBST_ALL_TAC THEN
     EXISTS_TAC `mm:num` THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    (* Extract g properties for b0 *)
    SUBGOAL_THEN
      `(!x:A. x IN topspace top /\ ~(x IN b0) ==>
         (g:(A->bool)->A->real) b0 x = &0) /\
       (!x:A. x IN b0 ==> &0 < (g:(A->bool)->A->real) b0 x)`
      STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `!b:A->bool. b IN B ==>
      continuous_map(top,euclideanreal) (g b) /\
      (!x. x IN topspace top ==> &0 <= g b x /\ g b x <= &1) /\
      (!x. x IN topspace top /\ ~(x IN b) ==> g b x = &0) /\
      (!x. x IN b ==> &0 < g b x)` THEN
     DISCH_THEN(MP_TAC o SPEC `b0:A->bool`) THEN
     ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
       (CONJUNCTS_THEN2 (K ALL_TAC) ACCEPT_TAC));
     ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (g:(A->bool)->A->real) b0 x` ASSUME_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    (* r = g(b0)(x) * inv(SUC n0) *)
    EXISTS_TAC `(g:(A->bool)->A->real) b0 x * inv(&(SUC n0))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
     (* mball SUBSET u: if d(x,y) < r then y IN b0 SUBSET u *)
     REWRITE_TAC[SUBSET; IN_MBALL] THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `y:A` THEN STRIP_TAC THEN
     ASM_CASES_TAC `(y:A) IN b0` THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
     (* ~(y IN b0): derive contradiction *)
     SUBGOAL_THEN `(g:(A->bool)->A->real) b0 y = &0` ASSUME_TAC THENL
     [UNDISCH_TAC
       `!x:A. x IN topspace top /\ ~(x IN b0) ==>
        (g:(A->bool)->A->real) b0 x = &0` THEN
      DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN `F` (fun th -> MESON_TAC[th]) THEN
     UNDISCH_TAC
       `sup {abs ((g:(A->bool)->A->real) b x * inv (&(SUC n)) -
                  g b y * inv (&(SUC n))) |
             n,b | b IN Bn n} <
        (g:(A->bool)->A->real) b0 x * inv (&(SUC n0))` THEN
     REWRITE_TAC[REAL_NOT_LT] THEN
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC
       `abs((g:(A->bool)->A->real) b0 x * inv(&(SUC n0)) -
            g b0 y * inv(&(SUC n0)))` THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
      [EXISTS_TAC `&1` THEN
       X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN
       DISCH_THEN(X_CHOOSE_THEN `n':num` (X_CHOOSE_THEN `b':A->bool`
         (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
       UNDISCH_TAC `!x:A y:A z.
         x IN topspace top /\ y IN topspace top /\
         z IN {abs(g (b:A->bool) x * inv(&(SUC n)) -
                   g b y * inv(&(SUC n))) |
               n,b | b IN Bn n}
         ==> z <= &1` THEN
       DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`;
         `abs((g:(A->bool)->A->real) b' x * inv(&(SUC n')) -
              g b' y * inv(&(SUC n')))`]) THEN
       ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
        [FIRST_ASSUM ACCEPT_TAC;
         FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[IN_ELIM_THM] THEN
         EXISTS_TAC `n':num` THEN EXISTS_TAC `b':A->bool` THEN
         CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REFL_TAC]];
        DISCH_THEN ACCEPT_TAC];
       REWRITE_TAC[IN_ELIM_THM] THEN
       EXISTS_TAC `n0:num` THEN EXISTS_TAC `b0:A->bool` THEN
       CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REFL_TAC]]]]];
   (* Backward: open_in (mtopology m) u ==> open_in top u *)
   DISCH_TAC THEN
   (* Extract u SUBSET topspace and ball condition from OPEN_IN_MTOPOLOGY *)
   SUBGOAL_THEN
     `(u:A->bool) SUBSET topspace top /\
      !x. x IN u ==>
        ?r. &0 < r /\
            mball(metric(topspace top:A->bool,d:A#A->real)) (x,r) SUBSET u`
     STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
      `open_in (mtopology(metric(topspace top:A->bool,d:A#A->real)))
               (u:A->bool)` THEN
    REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN
    UNDISCH_TAC
      `mspace(metric(topspace top:A->bool,d:A#A->real)) = topspace top` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
   (* Use OPEN_IN_SUBOPEN -- ONCE to avoid infinite rewriting loop *)
   ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   (* Get x IN topspace top *)
   SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
   (* Get r > 0 and mball SUBSET u *)
   UNDISCH_TAC
     `!x:A. x IN u
      ==> ?r. &0 < r /\
          mball(metric(topspace top:A->bool,d:A#A->real)) (x,r) SUBSET u` THEN
   DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
   (* Witness: the d-ball in top *)
   EXISTS_TAC `{y:A | y IN topspace top /\ (d:A#A->real)(x,y) < r}` THEN
   REPEAT CONJ_TAC THENL
   [(* open_in top {y | ...} *)
    UNDISCH_TAC `!x:A r. x IN topspace top /\ &0 < r
      ==> open_in top {y:A | y IN topspace top /\ (d:A#A->real)(x,y) < r}` THEN
    DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
    (* x IN {y | ...} *)
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     UNDISCH_TAC `!a:A. a IN topspace top ==> (d:A#A->real)(a,a) = &0` THEN
     DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
     ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
     FIRST_ASSUM ACCEPT_TAC];
    (* {y | ...} SUBSET u *)
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    (* z is in the mball, hence in u *)
    UNDISCH_TAC
      `mball(metric(topspace top:A->bool,d:A#A->real)) (x:A,r) SUBSET
       (u:A->bool)` THEN
    REWRITE_TAC[SUBSET; IN_MBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC
      `mspace(metric(topspace top:A->bool,d:A#A->real)) = topspace top` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC
      `mdist(metric(topspace top:A->bool,d:A#A->real)) = (d:A#A->real)` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     FIRST_ASSUM ACCEPT_TAC;
     FIRST_ASSUM ACCEPT_TAC]]]);;

(* Paracompact Hausdorff locally metrizable => sigma-locally-finite base *)
let PARACOMPACT_LOCALLY_METRIZABLE_SIGMA_LF_BASE = prove
 (`!top:A topology.
        paracompact_space top /\ hausdorff_space top /\
        (!x. x IN topspace top
             ==> ?u. open_in top u /\ x IN u /\
                     metrizable_space(subtopology top u))
        ==> ?B. (!b. b IN B ==> open_in top b) /\
                (!x u. open_in top u /\ x IN u
                       ==> ?b. b IN B /\ x IN b /\ b SUBSET u) /\
                sigma_locally_finite_in top B`,
  GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: Apply paracompactness to cover by metrizable opens *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [paracompact_space]) THEN
  DISCH_THEN(MP_TAC o SPEC
    `{u:A->bool | open_in top u /\ metrizable_space(subtopology top u)}`) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN EQ_TAC THENL
    [DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
     ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
     DISCH_TAC THEN ASM_MESON_TAC[]]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `CC:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Each element of CC is metrizable *)
  SUBGOAL_THEN
    `!c:A->bool. c IN CC ==> metrizable_space(subtopology top c)`
    ASSUME_TAC THENL
  [X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `c:A->bool`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `subtopology (subtopology top u) (c:A->bool) =
                  subtopology top c` (fun th ->
     ASM_MESON_TAC[th; METRIZABLE_SPACE_SUBTOPOLOGY]) THEN
   REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN ASM SET_TAC[];
   ALL_TAC] THEN
  (* Choose metrics for each c in CC *)
  SUBGOAL_THEN
    `?mc:(A->bool)->A metric.
       !c. c IN CC ==> subtopology top c = mtopology (mc c)`
    STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[GSYM SKOLEM_THM] THEN ASM_MESON_TAC[metrizable_space];
   ALL_TAC] THEN
  (* Useful: mspace(mc c) = c for c in CC *)
  SUBGOAL_THEN `!c:A->bool. c IN CC ==> mspace((mc:(A->bool)->A metric) c) = c`
    ASSUME_TAC THENL
  [X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN `subtopology top (c:A->bool) =
     mtopology ((mc:(A->bool)->A metric) c)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th ->
     MP_TAC(AP_TERM `topspace:(A)topology->A->bool` th)) THEN
   REWRITE_TAC[TOPSPACE_MTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
   SUBGOAL_THEN `(c:A->bool) SUBSET topspace top` MP_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `topspace top INTER (c:A->bool) = c`
     (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; MESON_TAC[]];
   ALL_TAC] THEN
  (* Step 2: For each m, get locally finite refinement of 1/(m+1)-balls *)
  SUBGOAL_THEN
    `!m:num. ?Dm:(A->bool)->bool.
       (!d. d IN Dm ==> open_in top d) /\
       UNIONS Dm = topspace top /\
       (!d. d IN Dm ==>
            ?c (x:A). c IN CC /\ x IN c /\
                      d SUBSET mball ((mc:(A->bool)->A metric) c)
                                     (x, inv(&(m + 1)))) /\
       locally_finite_in top Dm`
    MP_TAC THENL
  [X_GEN_TAC `m:num` THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [paracompact_space]) THEN
   DISCH_THEN(MP_TAC o SPEC
     `{mball ((mc:(A->bool)->A metric) c) ((x:A), inv(&(m + 1))) |
       c IN CC /\ x IN c}`) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [(* All balls are open in top *)
     REWRITE_TAC[FORALL_IN_GSPEC] THEN
     MAP_EVERY X_GEN_TAC [`c:A->bool`; `x':A`] THEN STRIP_TAC THEN
     SUBGOAL_THEN `open_in (subtopology top (c:A->bool))
       (mball ((mc:(A->bool)->A metric) c) ((x':A), inv(&(m + 1))))`
       MP_TAC THENL
     [SUBGOAL_THEN `subtopology top (c:A->bool) =
       mtopology ((mc:(A->bool)->A metric) c)` (fun th -> REWRITE_TAC[th])
      THENL [ASM_MESON_TAC[]; REWRITE_TAC[OPEN_IN_MBALL]];
      ALL_TAC] THEN
     REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
     DISCH_THEN(X_CHOOSE_THEN `v:A->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
     MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[];
     (* Balls cover topspace *)
     REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC] THEN
     X_GEN_TAC `z:A` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `c:A->bool`
        (X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(z:A) IN mspace((mc:(A->bool)->A metric) c)` MP_TAC THENL
      [ASM_MESON_TAC[MBALL_SUBSET_MSPACE; SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      DISCH_TAC THEN
      SUBGOAL_THEN `?c:A->bool. c IN CC /\ z IN c`
        (X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THENL
      [ASM_MESON_TAC[EXTENSION; IN_UNIONS]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`c:A->bool`; `z:A`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CENTRE_IN_MBALL THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN ARITH_TAC]];
    ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `Dm:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `Dm:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `d:A->bool` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `d:A->bool`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
   MAP_EVERY X_GEN_TAC [`c:A->bool`; `x':A`] THEN STRIP_TAC THEN
   MAP_EVERY EXISTS_TAC [`c:A->bool`; `x':A`] THEN
   ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `D:num->(A->bool)->bool`) THEN
  (* Step 3: B = UNIONS {D m | m IN (:num)} *)
  EXISTS_TAC `UNIONS {(D:num->(A->bool)->bool) m | m IN (:num)}` THEN
  REPEAT CONJ_TAC THENL
  [(* All elements of B are open *)
   REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
   ASM_MESON_TAC[];
   (* B is a basis *)
   MAP_EVERY X_GEN_TAC [`x:A`; `u:A->bool`] THEN STRIP_TAC THEN
   SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [locally_finite_in]) THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A`)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `!c:A->bool. c IN CC /\ x IN c
       ==> ?e. &0 < e /\
               mball ((mc:(A->bool)->A metric) c) ((x:A),e) SUBSET u INTER c`
     MP_TAC THENL
   [X_GEN_TAC `c:A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `open_in (mtopology((mc:(A->bool)->A metric) c))
      (u INTER c:A->bool)` MP_TAC THENL
    [SUBGOAL_THEN `subtopology top (c:A->bool) =
       mtopology ((mc:(A->bool)->A metric) c)` (fun th -> REWRITE_TAC[GSYM th])
     THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
     EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_MTOPOLOGY; SUBSET; IN_MBALL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A`)) THEN
    ASM_SIMP_TAC[IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[SUBSET; IN_MBALL; IN_INTER] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   DISCH_THEN(MP_TAC o
     REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
   DISCH_THEN(X_CHOOSE_TAC `eps:(A->bool)->real`) THEN
   ABBREV_TAC `CC_x = {c:A->bool | c IN CC /\ x IN c}` THEN
   SUBGOAL_THEN `FINITE (CC_x:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{c:A->bool | c IN CC /\ ~(c INTER w = {})}` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "CC_x" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `c:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `~(CC_x:(A->bool)->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "CC_x" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    ASM_MESON_TAC[EXTENSION; IN_UNIONS]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < inf (IMAGE (eps:(A->bool)->real) CC_x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    EXPAND_TAC "CC_x" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
   MP_TAC(SPEC `inf(IMAGE (eps:(A->bool)->real) CC_x) / &2` REAL_ARCH_INV) THEN
   ASM_REWRITE_TAC[REAL_HALF] THEN
   DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `?d:A->bool. d IN (D:num->(A->bool)->bool) (N - 1) /\ x IN d`
     (X_CHOOSE_THEN `d:A->bool` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[EXTENSION; IN_UNIONS]; ALL_TAC] THEN
   EXISTS_TAC `d:A->bool` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `N - 1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   (* d refines some ball *)
   FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
     SPEC `N - 1`) THEN
   DISCH_THEN(MP_TAC o SPEC `d:A->bool`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `c0:A->bool`
     (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `(x:A) IN c0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:A) IN mspace((mc:(A->bool)->A metric) c0)` MP_TAC THENL
    [SUBGOAL_THEN `x IN mball ((mc:(A->bool)->A metric) c0)
       ((y:A),inv(&((N - 1) + 1)))` MP_TAC THENL
     [ASM SET_TAC[]; MESON_TAC[MBALL_SUBSET_MSPACE; SUBSET]];
     ASM_SIMP_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN `(c0:A->bool) IN CC_x` ASSUME_TAC THENL
   [EXPAND_TAC "CC_x" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
   (* d SUBSET u via: d SUBSET mball(y,r) SUBSET
      mball(x,eps c0) SUBSET u INTER c0 SUBSET u *)
   SUBGOAL_THEN `inf(IMAGE (eps:(A->bool)->real) CC_x) <= eps(c0:A->bool)`
     ASSUME_TAC THENL
   [MP_TAC(SPEC `IMAGE (eps:(A->bool)->real) CC_x` INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `c0:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `(d:A->bool) SUBSET
      mball((mc:(A->bool)->A metric) c0) ((x:A), eps(c0:A->bool))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mball((mc:(A->bool)->A metric) c0)
      ((y:A), inv(&(N - 1 + 1)))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MBALL_SUBSET THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[];
     SUBGOAL_THEN
       `(x:A) IN mball((mc:(A->bool)->A metric) c0)
          ((y:A), inv(&(N - 1 + 1)))` MP_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[IN_MBALL] THEN STRIP_TAC] THEN
     SUBGOAL_THEN
       `mdist ((mc:(A->bool)->A metric) c0) ((y:A),(x:A)) +
        inv(&(N - 1 + 1)) < &2 * inv(&(N - 1 + 1))`
       ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a < b ==> a + b < &2 * b`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     SUBGOAL_THEN `&2 * inv(&(N - 1 + 1)) <= eps(c0:A->bool)`
       ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inf(IMAGE (eps:(A->bool)->real) CC_x)` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LT_IMP_LE THEN
       SUBGOAL_THEN `(N - 1) + 1 = N` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a < b / &2 ==> &2 * a < b`) THEN
        ASM_REWRITE_TAC[]];
       ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
     MATCH_MP_TAC(REAL_ARITH
       `a + b < &2 * b /\ &2 * b <= c ==> a + b <= c`) THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `mball((mc:(A->bool)->A metric) c0)
     ((x:A), eps(c0:A->bool))` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `u INTER (c0:A->bool)` THEN
   REWRITE_TAC[INTER_SUBSET] THEN
   ASM_SIMP_TAC[];
   (* sigma_locally_finite_in top B *)
   REWRITE_TAC[sigma_locally_finite_in] THEN
   EXISTS_TAC `D:num->(A->bool)->bool` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Collectionwise normal spaces (Engelking 5.1.17-5.1.18)                    *)
(* ------------------------------------------------------------------------- *)

(* Collectionwise normal space (Engelking 5.1.17) *)
let collectionwise_normal_space = new_definition
 `collectionwise_normal_space (top:A topology) <=>
        !F. (!c. c IN F ==> closed_in top c) /\
            pairwise DISJOINT F /\
            locally_finite_in top F
            ==> ?G. (!c. c IN F ==> open_in top (G c) /\ c SUBSET G c) /\
                    pairwise (\c d. DISJOINT (G c) (G d)) F`;;

(* Helper: If s SUBSET a and t SUBSET b and DISJOINT a b then DISJOINT s t *)
(* Engelking 5.1.18: Paracompact Hausdorff is collectionwise normal
   Proof: Given locally finite pairwise disjoint closed family F:
   1. Build open cover {O_c | c in F} UNION {topspace \ UNIONS F}
      where O_c = topspace \ UNIONS(F DELETE c)
   2. Get locally finite open refinement W
   3. Each w meeting c is SUBSET O_c, so meets at most one member of F
   4. Apply NORMAL_SPACE_ALT: for each c, get H(c) with cl(H(c)) SUBSET O_c
   5. Define G(c) = H(c) \ UNIONS{cl(H(d)) | d != c}
   6. The cl(H(d)) family is locally finite, so the union is closed, G(c) is open
   7. c SUBSET G(c) since cl(H(d)) INTER c = {} for d != c
   8. G(c) INTER G(d) = {} since G(c) SUBSET cl(H(c)) and G(d) avoids cl(H(c)) *)
let PARACOMPACT_HAUSDORFF_IMP_COLLECTIONWISE_NORMAL = prove
 (`!top:A topology.
        paracompact_space top /\ hausdorff_space top
        ==> collectionwise_normal_space top`,
  let DISJOINT_SUBSET_SUBSET = prove
   (`!s t a b:A->bool.
          s SUBSET a /\ t SUBSET b /\ DISJOINT a b ==> DISJOINT s t`,
    SET_TAC[]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[collectionwise_normal_space] THEN
  X_GEN_TAC `fam:(A->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  (* normal_space top *)
  SUBGOAL_THEN `normal_space (top:A topology)` ASSUME_TAC THENL
  [MATCH_MP_TAC PARACOMPACT_HAUSDORFF_IMP_NORMAL_SPACE THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* For each c, UNIONS(F DELETE c) is closed *)
  SUBGOAL_THEN
    `!c:A->bool. c IN fam ==> closed_in top (UNIONS(fam DELETE c))`
    ASSUME_TAC THENL
  [X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   MATCH_MP_TAC CLOSED_IN_LOCALLY_FINITE_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC LOCALLY_FINITE_IN_SUBSET THEN
   EXISTS_TAC `fam:(A->bool)->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET];
   ALL_TAC] THEN
  (* UNIONS F is closed *)
  SUBGOAL_THEN `closed_in top (UNIONS (fam:(A->bool)->bool))` ASSUME_TAC THENL
  [MATCH_MP_TAC CLOSED_IN_LOCALLY_FINITE_UNIONS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* For each c, c SUBSET topspace DIFF UNIONS(F DELETE c) *)
  SUBGOAL_THEN
    `!c:A->bool. c IN fam
     ==> c SUBSET (topspace top DIFF UNIONS(fam DELETE c))`
    ASSUME_TAC THENL
  [X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_DELETE] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET]; ALL_TAC] THEN
   REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN
   X_GEN_TAC `d:A->bool` THEN
   ASM_CASES_TAC `(d:A->bool) = c` THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `pairwise DISJOINT (fam:(A->bool)->bool)` THEN
   REWRITE_TAC[pairwise] THEN
   DISCH_THEN(MP_TAC o SPECL [`c:A->bool`; `d:A->bool`]) THEN
   ASM_REWRITE_TAC[DISJOINT] THEN ASM SET_TAC[];
   ALL_TAC] THEN
  (* Apply paracompact_space to get locally finite refinement W *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [paracompact_space]) THEN
  DISCH_THEN(MP_TAC o SPEC
    `(topspace top DIFF UNIONS (fam:(A->bool)->bool)) INSERT
     IMAGE (\c:A->bool. topspace top DIFF UNIONS(fam DELETE c)) fam`) THEN
  ANTS_TAC THENL
  [(* Prove this is an open cover *)
   CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
   MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_INSERT; IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_DIFF]; ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_INSERT; IN_IMAGE] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   ASM_CASES_TAC `(x:A) IN UNIONS fam` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `topspace top DIFF UNIONS((fam:(A->bool)->bool) DELETE c)` THEN
    CONJ_TAC THENL
    [DISJ2_TAC THEN EXISTS_TAC `c:A->bool` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET];
    EXISTS_TAC `topspace top DIFF UNIONS (fam:(A->bool)->bool)` THEN
    CONJ_TAC THENL [DISJ1_TAC THEN REFL_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_DIFF]];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Key: each w meeting c is contained in topspace DIFF UNIONS(F DELETE c) *)
  SUBGOAL_THEN
    `!w c:A->bool. w IN W /\ c IN fam /\ ~(w INTER c = {})
     ==> w SUBSET topspace top DIFF UNIONS(fam DELETE c)`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `w:A->bool`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
   UNDISCH_TAC
     `(u:A->bool) IN (topspace top DIFF UNIONS (fam:(A->bool)->bool)) INSERT
       IMAGE (\c. topspace top DIFF UNIONS(fam DELETE c)) fam` THEN
   REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN
   DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `c':A->bool` STRIP_ASSUME_TAC)) THENL
   [(* u = topspace DIFF UNIONS fam: contradicts w INTER c != {} *)
    UNDISCH_TAC `~(w INTER c:A->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:A) IN UNIONS fam` MP_TAC THENL
    [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `c:A->bool` THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET; IN_DIFF]; ALL_TAC] THEN
   ASM_CASES_TAC `c':A->bool = c` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   (* c' != c: then c SUBSET UNIONS(F DELETE c'), contradicts w INTER c != {} *)
   UNDISCH_TAC `~(w INTER c:A->bool = {})` THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
   DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `(c:A->bool) SUBSET UNIONS(fam DELETE c')` MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_DELETE] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    EXISTS_TAC `c:A->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[SUBSET; IN_DIFF];
   ALL_TAC] THEN
  (* Apply NORMAL_SPACE_ALT: for each c get H(c) open with c SUBSET H(c)
     and closure(H(c)) SUBSET UNIONS{w | w IN W, w INTER c != {}} *)
  SUBGOAL_THEN
    `!c:A->bool. c IN fam
     ==> ?v. open_in top v /\ c SUBSET v /\
             top closure_of v SUBSET
               UNIONS {w:A->bool | w IN W /\ ~(w INTER c = {})}`
    MP_TAC THENL
  [X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NORMAL_SPACE_ALT]) THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   SUBGOAL_THEN `(x:A) IN UNIONS W` MP_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET]; ALL_TAC] THEN
   REWRITE_TAC[IN_UNIONS] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
   ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `H:(A->bool)->(A->bool)` STRIP_ASSUME_TAC) THEN
  (* closure(H c) SUBSET topspace DIFF UNIONS(F DELETE c) *)
  SUBGOAL_THEN
    `!c:A->bool. c IN fam
     ==> top closure_of ((H:(A->bool)->(A->bool)) c) SUBSET
         topspace top DIFF UNIONS(fam DELETE c)`
    ASSUME_TAC THENL
  [X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `UNIONS {w:A->bool | w IN W /\ ~(w INTER c = {})}` THEN
   ASM_SIMP_TAC[] THEN REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Key: closure(H c) INTER d = {} for c != d *)
  SUBGOAL_THEN
    `!c d:A->bool. c IN fam /\ d IN fam /\ ~(c = d)
     ==> DISJOINT (top closure_of ((H:(A->bool)->(A->bool)) c)) d`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC DISJOINT_SUBSET_SUBSET THEN
   MAP_EVERY EXISTS_TAC
     [`topspace top DIFF UNIONS((fam:(A->bool)->bool) DELETE c)`;
      `UNIONS((fam:(A->bool)->bool) DELETE c)`] THEN
   REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    ASM SET_TAC[];
    SET_TAC[]];
   ALL_TAC] THEN
  (* {closure(H c) | c IN F} is locally finite *)
  SUBGOAL_THEN
    `locally_finite_in top
      {top closure_of (H:(A->bool)->(A->bool)) c |
       c IN (fam:(A->bool)->bool)}`
    ASSUME_TAC THENL
  [REWRITE_TAC[locally_finite_in; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE]; ALL_TAC] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   UNDISCH_TAC `locally_finite_in top (W:(A->bool)->bool)` THEN
   REWRITE_TAC[locally_finite_in] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `x:A`)) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC
     `IMAGE (\w:A->bool. top closure_of ((H:(A->bool)->(A->bool))
        (@c. c IN fam /\ ~(w INTER c = {}))))
      {w:A->bool | w IN W /\ ~(V INTER w = {})}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
   X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `c:A->bool`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
   (* cl(H c) meets V, cl(H c) SUBSET UNIONS{w | w meets c} *)
   UNDISCH_TAC `~(top closure_of ((H:(A->bool)->(A->bool)) c)
     INTER (V:A->bool) = {})` THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
   DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `(z:A) IN UNIONS {w:A->bool | w IN W /\ ~(w INTER c = {})}`
     MP_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `w:A->bool` THEN
   CONJ_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
   (* Variable capture prevents AP_TERM_TAC, so use SUBGOAL_THEN *)
   SUBGOAL_THEN
     `(@c':A->bool. c' IN fam /\ (?x:A. x IN w /\ x IN c')) = c`
     (fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC SELECT_UNIQUE THEN
   X_GEN_TAC `c':A->bool` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `~(w INTER c':A->bool = {})` ASSUME_TAC THENL
    [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `c':A->bool = c` THEN
    ASM_REWRITE_TAC[] THEN
    (* c' != c: extract c' IN fam from beta-application, derive contradiction *)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o
      check (fun th -> is_comb(concl th) && is_abs(rator(concl th)))) THEN
    SUBGOAL_THEN
      `(w:A->bool) SUBSET topspace top DIFF UNIONS(fam DELETE c':A->bool)`
      MP_TAC THENL
    [FIRST_ASSUM(MATCH_MP_TAC o SPECL [`w:A->bool`; `c':A->bool`]) THEN
     ASM_REWRITE_TAC[];
     UNDISCH_TAC `~(w INTER c:A->bool = {})` THEN
     UNDISCH_TAC `(c:A->bool) IN fam` THEN
     UNDISCH_TAC `~(c':A->bool = c)` THEN
     REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_DELETE;
                 EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
     MESON_TAC[]];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]];
   ALL_TAC] THEN
  (* For each c, UNIONS{cl(H d) | d IN F, d != c} is closed *)
  SUBGOAL_THEN
    `!c:A->bool. c IN fam
     ==> closed_in top
           (UNIONS {top closure_of (H:(A->bool)->(A->bool)) d |
                    d IN (fam:(A->bool)->bool) /\ ~(d = c)})`
    ASSUME_TAC THENL
  [X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   MATCH_MP_TAC CLOSED_IN_LOCALLY_FINITE_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN MESON_TAC[CLOSED_IN_CLOSURE_OF];
    ALL_TAC] THEN
   MATCH_MP_TAC LOCALLY_FINITE_IN_SUBSET THEN
   EXISTS_TAC
     `{top closure_of (H:(A->bool)->(A->bool)) d |
       d IN (fam:(A->bool)->bool)}` THEN ASM SET_TAC[];
   ALL_TAC] THEN
  (* Witness with G'(c) = H(c) DIFF UNIONS{cl(H d) | d IN F, d != c} *)
  EXISTS_TAC
    `\c:A->bool. (H:(A->bool)->(A->bool)) c DIFF
       UNIONS {(top:A topology) closure_of H d |
               d IN (fam:(A->bool)->bool) /\ ~(d = c)}` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
  [(* For each c: open_in top (G' c) /\ c SUBSET G' c *)
   X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
   [(* open_in: H(c) is open, UNIONS{...} is closed *)
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_SIMP_TAC[];
    (* c SUBSET G'(c) *)
    REWRITE_TAC[SUBSET; IN_DIFF] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONJ_TAC THENL
    [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `d:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`d:A->bool`; `c:A->bool`]) THEN
    ASM_REWRITE_TAC[DISJOINT] THEN ASM SET_TAC[]];
   (* Pairwise disjointness *)
   REWRITE_TAC[pairwise] THEN
   MAP_EVERY X_GEN_TAC [`c:A->bool`; `d:A->bool`] THEN STRIP_TAC THEN
   (* G'(c) SUBSET cl(H c) and G'(d) INTER cl(H c) = {} *)
   MATCH_MP_TAC(SET_RULE
     `!u:A->bool. s SUBSET u /\ DISJOINT u t ==> DISJOINT s t`) THEN
   EXISTS_TAC `top closure_of ((H:(A->bool)->(A->bool)) c)` THEN
   CONJ_TAC THENL
   [(* G'(c) SUBSET cl(H c): G'(c) SUBSET H(c) SUBSET cl(H c) *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(H:(A->bool)->(A->bool)) c` THEN CONJ_TAC THENL
    [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    (* DISJOINT (cl H c) (G'(d)) *)
    REWRITE_TAC[DISJOINT] THEN
    ONCE_REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_INTER; IN_DIFF] THEN
    X_GEN_TAC `x:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `c:A->bool` THEN ASM_REWRITE_TAC[]]]);;

(* Collectionwise normal implies normal *)
(* Proof sketch: For disjoint closed sets s, t, apply collectionwise normality
   to the two-element family {s, t} to get disjoint open neighborhoods *)
let COLLECTIONWISE_NORMAL_IMP_NORMAL = prove
 (`!top:A topology.
        collectionwise_normal_space top /\ t1_space top
        ==> normal_space top`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[collectionwise_normal_space; normal_space] THEN
  INTRO_TAC "cn t1" THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `t:A->bool`] THEN
  INTRO_TAC "cs ct dis" THEN
  (* Handle degenerate case s = t first *)
  ASM_CASES_TAC `s:A->bool = t` THENL
  [ASM_MESON_TAC[DISJOINT_EMPTY_REFL; OPEN_IN_EMPTY;
                  EMPTY_SUBSET; DISJOINT_EMPTY];
   ALL_TAC] THEN
  (* Apply collectionwise normality to the two-element family {s, t} *)
  REMOVE_THEN "cn" (MP_TAC o SPEC `{s:A->bool, t}`) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN
  (* Prove pairwise DISJOINT {s, t} *)
  SUBGOAL_THEN `pairwise DISJOINT {s:A->bool, t}`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[pairwise; IN_INSERT; NOT_IN_EMPTY] THEN
   ASM_MESON_TAC[DISJOINT_SYM];
   ALL_TAC] THEN
  SUBGOAL_THEN `locally_finite_in top {s:A->bool, t}`
    (fun th -> REWRITE_TAC[th]) THENL
  [MATCH_MP_TAC FINITE_IMP_LOCALLY_FINITE_IN THEN
   REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
   REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY; UNION_SUBSET] THEN
   ASM_MESON_TAC[CLOSED_IN_SUBSET];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:(A->bool)->(A->bool)` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`(G:(A->bool)->(A->bool)) s`;
    `(G:(A->bool)->(A->bool)) t`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `pairwise (\c d. DISJOINT ((G:(A->bool)->(A->bool)) c) (G d))
             {s, t}` THEN
  REWRITE_TAC[pairwise; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;

(* Metrizable implies collectionwise normal *)
let METRIZABLE_IMP_COLLECTIONWISE_NORMAL = prove
 (`!top:A topology.
        metrizable_space top ==> collectionwise_normal_space top`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC PARACOMPACT_HAUSDORFF_IMP_COLLECTIONWISE_NORMAL THEN
  ASM_SIMP_TAC[METRIZABLE_IMP_PARACOMPACT_SPACE;
               METRIZABLE_IMP_HAUSDORFF_SPACE]);;

(* Cf. Engelking Exercise 5.1.C(a): Closed subspace of
   CW normal is CW normal *)
let COLLECTIONWISE_NORMAL_SPACE_CLOSED_SUBSET = prove
 (`!top s:A->bool.
        collectionwise_normal_space top /\ closed_in top s
        ==> collectionwise_normal_space(subtopology top s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[collectionwise_normal_space] THEN
  INTRO_TAC "cn cs" THEN X_GEN_TAC `CC:(A->bool)->bool` THEN
  INTRO_TAC "closed pw lf" THEN
  (* Each c IN CC is closed in top (by CLOSED_IN_CLOSED_SUBTOPOLOGY) *)
  SUBGOAL_THEN
   `!c:A->bool. c IN CC ==> closed_in top c /\ c SUBSET s`
   ASSUME_TAC THENL
  [X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `c:A->bool`) THEN ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC[CLOSED_IN_CLOSED_SUBTOPOLOGY];
   ALL_TAC] THEN
  (* CC is locally finite in top (from locally finite in subtopology) *)
  SUBGOAL_THEN `locally_finite_in top (CC:(A->bool)->bool)` ASSUME_TAC THENL
  [REMOVE_THEN "lf" MP_TAC THEN
   ASM_SIMP_TAC[LOCALLY_FINITE_IN_SUBTOPOLOGY_EQ] THEN MESON_TAC[];
   ALL_TAC] THEN
  (* Apply collectionwise normality of top to CC *)
  FIRST_X_ASSUM(MP_TAC o SPEC `CC:(A->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:(A->bool)->(A->bool)` STRIP_ASSUME_TAC) THEN
  (* Define G' c = G c INTER s *)
  EXISTS_TAC `\c:A->bool. (G:(A->bool)->(A->bool)) c INTER (s:A->bool)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
  [X_GEN_TAC `c:A->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `(G:(A->bool)->(A->bool)) c` THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `c:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM SET_TAC[]];
   REWRITE_TAC[pairwise] THEN
   MAP_EVERY X_GEN_TAC [`c:A->bool`; `d:A->bool`] THEN STRIP_TAC THEN
   MATCH_MP_TAC(SET_RULE
    `!a b c:A->bool. DISJOINT a b ==> DISJOINT (a INTER c) (b INTER c)`) THEN
   UNDISCH_TAC
    `pairwise (\c d. DISJOINT ((G:(A->bool)->(A->bool)) c) (G d)) CC` THEN
   REWRITE_TAC[pairwise] THEN
   DISCH_THEN(MP_TAC o SPECL [`c:A->bool`; `d:A->bool`]) THEN
   ASM_REWRITE_TAC[]]);;

(* Munkres 42.1 (Smirnov): Paracompact locally metrizable is metrizable *)
let PARACOMPACT_LOCALLY_METRIZABLE_IMP_METRIZABLE = prove
 (`!top:A topology.
        paracompact_space top /\ hausdorff_space top /\
        (!x. x IN topspace top
             ==> ?u. open_in top u /\ x IN u /\
                     metrizable_space(subtopology top u))
        ==> metrizable_space top`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC NAGATA_SMIRNOV_METRIZATION THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC NORMAL_T1_IMP_REGULAR_SPACE THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC COLLECTIONWISE_NORMAL_IMP_NORMAL THEN
    ASM_SIMP_TAC[PARACOMPACT_HAUSDORFF_IMP_COLLECTIONWISE_NORMAL;
                 HAUSDORFF_IMP_T1_SPACE];
    ASM_SIMP_TAC[HAUSDORFF_IMP_T1_SPACE]];
   MP_TAC(SPEC `top:A topology`
     PARACOMPACT_LOCALLY_METRIZABLE_SIGMA_LF_BASE) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Realcompact spaces (cf. Engelking 3.11)                                   *)
(* ------------------------------------------------------------------------- *)

(* Realcompact space (cf. Engelking 3.11)
   A Tychonoff space X is realcompact if it is homeomorphic to a closed
   subspace of some R^kappa. We use topspace top as the index set. *)
let realcompact_space = new_definition
 `realcompact_space (top:A topology) <=>
        completely_regular_space top /\
        ?f:A->A->real.
            embedding_map(top, product_topology (topspace top) (\i. euclideanreal)) f /\
            closed_in (product_topology (topspace top) (\i. euclideanreal))
                      (IMAGE f (topspace top))`;;

(* Realcompact closed subset, product, and Lindelof-Tychonoff results are
   standard but require substantial infrastructure beyond what is needed
   for the Nagata-Smirnov metrization theorem. *)

(* ------------------------------------------------------------------------- *)
(* Smirnov metrization and further characterizations                         *)
(* ------------------------------------------------------------------------- *)

(* Definition: Locally metrizable space *)
let locally_metrizable_space = new_definition
 `locally_metrizable_space (top:A topology) <=>
  !x. x IN topspace top
      ==> ?U. open_in top U /\ x IN U /\ metrizable_space (subtopology top U)`;;

(* Smirnov metrization theorem:
   A topological space is metrizable iff it is paracompact, Hausdorff,
   and locally metrizable. *)
let SMIRNOV_METRIZATION = prove
 (`!top:A topology.
        metrizable_space top <=>
        paracompact_space top /\ hausdorff_space top /\ locally_metrizable_space top`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[METRIZABLE_IMP_PARACOMPACT_SPACE];
      ASM_MESON_TAC[METRIZABLE_IMP_HAUSDORFF_SPACE];
      REWRITE_TAC[locally_metrizable_space] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      EXISTS_TAC `topspace top:A->bool` THEN
      ASM_SIMP_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE]];
    REWRITE_TAC[locally_metrizable_space] THEN STRIP_TAC THEN
    MATCH_MP_TAC PARACOMPACT_LOCALLY_METRIZABLE_IMP_METRIZABLE THEN
    ASM_REWRITE_TAC[]]);;

(* Corollary: Second countable case follows from Urysohn metrization *)
let SMIRNOV_METRIZATION_SECOND_COUNTABLE = prove
 (`!top:A topology.
        paracompact_space top /\ hausdorff_space top /\
        locally_metrizable_space top /\ second_countable top
        ==> metrizable_space top`,
  MESON_TAC[SMIRNOV_METRIZATION]);;

(* ------------------------------------------------------------------ *)
(* Michael's characterization of paracompactness                      *)
(* and sharper closed map image theorem                               *)
(*                                                                    *)
(* E. Michael, "Another note on paracompact spaces",                  *)
(* Proc. Amer. Math. Soc. 8 (1957), 822-828.                          *)
(*                                                                    *)
(* Michael proved that a regular space is paracompact iff every open  *)
(* cover has a closure-preserving closed refinement. This gives a     *)
(* sharper image theorem: continuous closed surjection from           *)
(* paracompact Hausdorff preserves paracompactness (no need for       *)
(* compact fibres / perfect map).                                     *)
(* ------------------------------------------------------------------ *)

(* Helper: earlier pieces of a shrunk sequence are disjoint from later *)

let SHRINK_DISJOINT_LATER = prove
 (`!(f:num->A->bool) m n.
        m < n
        ==> f m INTER (f n DIFF UNIONS {f k | k < n}) = {}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
    `(s:A->bool) SUBSET t ==> s INTER (u DIFF t) = {}`) THEN
  REWRITE_TAC[UNIONS_GSPEC; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]);;

(* For a sequence of open sets covering topspace, the shrunk pieces
   S_n = f(n) \ UNIONS{f(k) | k < n} form a locally finite family *)

let SHRINK_SEQUENCE_LOCALLY_FINITE = prove
 (`!top:A topology f.
        (!n. open_in top (f n)) /\
        UNIONS {f n | n IN (:num)} = topspace top
        ==> locally_finite_in top
              {f n DIFF UNIONS {f k | k < n} | n IN (:num)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[locally_finite_in] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(f:num->A->bool) n` THEN
    REWRITE_TAC[SUBSET_DIFF] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?m:num. (x:A) IN f m /\ (!k. k < m ==> ~(x IN f k))`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\p:num. (x:A) IN f p` num_WOP) THEN REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(x:A) IN UNIONS {f n | n IN (:num)}` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(f:num->A->bool) m` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
    `IMAGE (\n. (f:num->A->bool) n DIFF UNIONS {f k | k < n})
           {n | n <= m}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LE];
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `u:A->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) ASSUME_TAC) THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `(f:num->A->bool) m INTER (f n DIFF UNIONS {f k | k < n}) = {}`
      ASSUME_TAC THENL
     [MATCH_MP_TAC SHRINK_DISJOINT_LATER THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `((f:num->A->bool) n DIFF UNIONS {f k | k < n}) INTER f m = {}`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(u:A->bool) INTER (f:num->A->bool) m = {}`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

(* The shrunk sets still cover the space *)

let SHRINK_SEQUENCE_COVERS = prove
 (`!top:A topology f.
        UNIONS {f n | n IN (:num)} = topspace top
        ==> UNIONS {f n DIFF UNIONS {f k | k < n} | n IN (:num)} =
            topspace top`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "cover") THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV; IN_DIFF] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:A->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) ASSUME_TAC)) THEN
    USE_THEN "cover" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `(f:num->A->bool) n` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `n:num` THEN REFL_TAC; ASM SET_TAC[]];
    DISCH_TAC THEN
    SUBGOAL_THEN `x:A IN UNIONS {f n | n IN (:num)}` MP_TAC THENL
     [USE_THEN "cover" SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:A->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n':num`) ASSUME_TAC)) THEN
    SUBGOAL_THEN `?m:num. (x:A) IN f m /\ (!k. k < m ==> ~(x IN f k))`
      STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `\p:num. (x:A) IN f p` num_WOP) THEN REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `(f:num->A->bool) m DIFF UNIONS {f k | k < m}` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `m:num` THEN REFL_TAC;
      REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]]]);;

(* If {A n | n} is LF and pairwise disjoint, and each f n is LF with
   elements subset of A n, then UNIONS {f n | n} is locally finite *)

let LOCALLY_FINITE_LEVEL_UNION_GEN = prove
 (`!top:A topology A f.
        locally_finite_in top {A n | n IN (:num)} /\
        (!n. locally_finite_in top ((f:num->(A->bool)->bool) n)) /\
        (!n (s:A->bool). s IN f n ==> s SUBSET A n) /\
        (!m n. ~(m = n) ==> A m INTER A n = {})
        ==> locally_finite_in top (UNIONS {f n | n IN (:num)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lfA")
    (CONJUNCTS_THEN2 (LABEL_TAC "lfF")
      (CONJUNCTS_THEN2 (LABEL_TAC "sub") (LABEL_TAC "disj")))) THEN
  SUBGOAL_THEN `!n. (A:num->A->bool) n SUBSET topspace top`
    (LABEL_TAC "Atop") THENL
   [USE_THEN "lfA" MP_TAC THEN
    REWRITE_TAC[locally_finite_in; IN_ELIM_THM; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[locally_finite_in] THEN
  SUBGOAL_THEN
    `!s:A->bool. s IN UNIONS {(f:num->(A->bool)->bool) n | n IN (:num)} <=>
                 ?n. s IN f n`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:A->bool` THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  USE_THEN "lfA" (MP_TAC o CONJUNCT2 o REWRITE_RULE[locally_finite_in]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `N0 = {n:num | ~((A:num->A->bool) n INTER W0 = {})}` THEN
  SUBGOAL_THEN `FINITE (N0:num->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
      `!n1 n2:num. n1 IN N0 /\ n2 IN N0 /\
                   (A:num->A->bool) n1 = A n2 ==> n1 = n2`
      (fun th -> REWRITE_TAC[GSYM(MATCH_MP FINITE_IMAGE_INJ_EQ th)]) THENL
     [REPEAT GEN_TAC THEN EXPAND_TAC "N0" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_CASES_TAC `n1:num = n2` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "disj" (MP_TAC o SPECL [`n1:num`; `n2:num`]) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
      `{u:A->bool | u IN {(A:num->A->bool) k | k IN (:num)} /\
                     ~(u INTER W0 = {})}` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    GEN_TAC THEN EXPAND_TAC "N0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!n:num. ?W:A->bool. open_in top W /\ x IN W /\
       FINITE {s:A->bool | s IN (f:num->(A->bool)->bool) n /\
                            ~(s INTER W = {})}`
    MP_TAC THENL
   [GEN_TAC THEN
    USE_THEN "lfF" (fun th ->
      MP_TAC(CONJUNCT2(REWRITE_RULE[locally_finite_in]
        (SPEC `n:num` th)))) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Wfn:num->A->bool` MP_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `N0:num->bool = {}` THENL
   [EXISTS_TAC `W0:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[FINITE_EMPTY]
      `(s:(A->bool)->bool) = {} ==> FINITE s`) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s:A->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n0:num`) ASSUME_TAC) THEN
    SUBGOAL_THEN `n0 IN (N0:num->bool)` MP_TAC THENL
     [EXPAND_TAC "N0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      USE_THEN "sub" (MP_TAC o SPECL [`n0:num`; `s:A->bool`]) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[NOT_IN_EMPTY]];
    ALL_TAC] THEN
  EXISTS_TAC `W0 INTER INTERS(IMAGE (Wfn:num->A->bool) N0)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_INTERS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTER; IN_INTERS; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE
    (\n. {s:A->bool | s IN (f:num->(A->bool)->bool) n /\
                      ~(s INTER (Wfn:num->A->bool) n = {})})
    N0)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN
  X_GEN_TAC `s:A->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n0:num`) ASSUME_TAC) THEN
  EXISTS_TAC `n0:num` THEN
  SUBGOAL_THEN `n0 IN (N0:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    USE_THEN "sub" (MP_TAC o SPECL [`n0:num`; `s:A->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
    `INTERS(IMAGE (Wfn:num->A->bool) N0) SUBSET Wfn n0`
    MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* Regularity shrink for open covers: each point gets an open nbhd whose
   closure is contained in some member of the original cover *)

let REGULAR_OPEN_COVER_CLOSURE_SHRINK = prove
 (`!top:A topology U.
        regular_space top /\
        (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
        ==> ?W. (!w. w IN W ==> open_in top w) /\
                UNIONS W = topspace top /\
                (!w. w IN W ==> ?u. u IN U /\ top closure_of w SUBSET u)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
    `{b:A->bool | open_in top b /\
                   ?u. u IN U /\ top closure_of b SUBSET u}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REGULAR_CLOSURE_REFINEMENT_COVERS THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* Point-finite CP closed cover is locally finite *)

let POINT_FINITE_CP_CLOSED_IMP_LOCALLY_FINITE = prove
 (`!top:A topology V.
        regular_space top /\
        (!v. v IN V ==> closed_in top v) /\
        UNIONS V = topspace top /\
        (!W. W SUBSET V ==> closed_in top (UNIONS W)) /\
        (!x. x IN topspace top ==> FINITE {v | v IN V /\ x IN v})
        ==> locally_finite_in top V`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[locally_finite_in] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `v:A->bool` THEN DISCH_TAC THEN
    ASM_MESON_TAC[closed_in; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ABBREV_TAC `CX = UNIONS {v:A->bool | v IN V /\ ~(x IN v)}` THEN
  SUBGOAL_THEN `closed_in top (CX:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "CX" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:A) IN CX)` ASSUME_TAC THENL
   [EXPAND_TAC "CX" THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top DIFF CX` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REGULAR_SPACE]) THEN
  DISCH_THEN(MP_TAC o SPECL [`CX:A->bool`; `x:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `O:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{v:A->bool | v IN V /\ x IN v}` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `v:A->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(O:A->bool) SUBSET top closure_of O` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `top:A topology` CLOSURE_OF_SUBSET) THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `(x:A) IN v` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:A->bool) SUBSET CX` ASSUME_TAC THENL
   [EXPAND_TAC "CX" THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(v INTER (O:A->bool) = {})` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT CX (top closure_of (O:A->bool))` THEN
  UNDISCH_TAC `(v:A->bool) SUBSET CX` THEN
  UNDISCH_TAC `(O:A->bool) SUBSET top closure_of O` THEN
  REWRITE_TAC[DISJOINT] THEN SET_TAC[]);;

(* Munkres Lemma 41.3 (1)=>(3): a sigma-locally-finite open refinement
   (with closure containment) gives an LF closed refinement *)

let CLF_OPEN_CLOSURE_IMP_LF_CLOSED = prove
 (`!top:A topology U R.
        (!r. r IN R ==> open_in top r) /\
        UNIONS R = topspace top /\
        (!r. r IN R ==> ?u. u IN U /\ top closure_of r SUBSET u) /\
        sigma_locally_finite_in top R
        ==> ?V. (!v. v IN V ==> closed_in top v) /\
                UNIONS V = topspace top /\
                (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                locally_finite_in top V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sigma_locally_finite_in]) THEN
  DISCH_THEN(X_CHOOSE_THEN `fn:num->(A->bool)->bool`
    (CONJUNCTS_THEN2 (LABEL_TAC "fnlf") (LABEL_TAC "fnR"))) THEN
  SUBGOAL_THEN `!n:num. (fn:num->(A->bool)->bool) n SUBSET R`
    (LABEL_TAC "fnsub") THENL
   [GEN_TAC THEN USE_THEN "fnR" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `P = \n:num. UNIONS ((fn:num->(A->bool)->bool) n)` THEN
  SUBGOAL_THEN `!n:num. open_in top ((P:num->A->bool) n)`
    (LABEL_TAC "Popen") THENL
   [GEN_TAC THEN EXPAND_TAC "P" THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(P:num->A->bool) n | n IN (:num)} = topspace top`
    (LABEL_TAC "Pcover") THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN UNIONS R` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:A->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?n0:num. (r:A->bool) IN (fn:num->(A->bool)->bool) n0`
        STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(r:A->bool) IN R` THEN
        USE_THEN "fnR" SUBST1_TAC THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `(P:num->A->bool) n0` THEN CONJ_TAC THENL
       [EXISTS_TAC `n0:num` THEN REFL_TAC;
        EXPAND_TAC "P" THEN REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `r:A->bool` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC
    `S = \n:num. (P:num->A->bool) n DIFF UNIONS {P k | k < n}` THEN
  SUBGOAL_THEN
    `locally_finite_in top {(S:num->A->bool) n | n IN (:num)}`
    (LABEL_TAC "Slf") THENL
   [EXPAND_TAC "S" THEN
    MATCH_MP_TAC(ISPEC `top:A topology` SHRINK_SEQUENCE_LOCALLY_FINITE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `UNIONS {(S:num->A->bool) n | n IN (:num)} = topspace top`
    (LABEL_TAC "Scover") THENL
   [EXPAND_TAC "S" THEN
    MATCH_MP_TAC(ISPEC `top:A topology` SHRINK_SEQUENCE_COVERS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n:num. ~(m = n) ==> (S:num->A->bool) m INTER S n = {}`
    (LABEL_TAC "Sdisj") THENL
   [EXPAND_TAC "S" THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP
      (ARITH_RULE `~(m:num = n) ==> m < n \/ n < m`)) THENL
     [MP_TAC(SPECL [`P:num->A->bool`; `m:num`; `n:num`]
        SHRINK_DISJOINT_LATER) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
        `(s:A->bool) INTER t = {} ==> (s DIFF a) INTER t = {}`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(SPECL [`P:num->A->bool`; `n:num`; `m:num`]
        SHRINK_DISJOINT_LATER) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
        `(s:A->bool) INTER t = {} ==> t INTER (s DIFF a) = {}`) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
    `Dn = \n:num. {r INTER (S:num->A->bool) n |
                    r | r IN (fn:num->(A->bool)->bool) n}` THEN
  SUBGOAL_THEN `!n:num. locally_finite_in top ((Dn:num->(A->bool)->bool) n)`
    (LABEL_TAC "Dnlf") THENL
   [GEN_TAC THEN EXPAND_TAC "Dn" THEN
    REWRITE_TAC[locally_finite_in; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `r:A->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:A->bool` THEN
      REWRITE_TAC[INTER_SUBSET] THEN
      USE_THEN "fnlf" (MP_TAC o CONJUNCT1 o
        REWRITE_RULE[locally_finite_in] o SPEC `n:num`) THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "fnlf" (MP_TAC o CONJUNCT2 o
      REWRITE_RULE[locally_finite_in] o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `O:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\r:A->bool. r INTER (S:num->A->bool) n)
                      {r | r IN (fn:num->(A->bool)->bool) n /\
                           ~(r INTER O = {})}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `s:A->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `r:A->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      EXISTS_TAC `r:A->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      UNDISCH_TAC `~((s:A->bool) INTER (O:A->bool) = {})` THEN
      UNDISCH_TAC `(s:A->bool) = r INTER (S:num->A->bool) n` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!n:num (s:A->bool). s IN (Dn:num->(A->bool)->bool) n
                          ==> s SUBSET (S:num->A->bool) n`
    (LABEL_TAC "DnsubS") THENL
   [GEN_TAC THEN EXPAND_TAC "Dn" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `locally_finite_in top
       (UNIONS {(Dn:num->(A->bool)->bool) n | n IN (:num)})`
    (LABEL_TAC "Dlf") THENL
   [MATCH_MP_TAC(ISPEC `top:A topology` LOCALLY_FINITE_LEVEL_UNION_GEN) THEN
    EXISTS_TAC `S:num->A->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
    `{top closure_of d:A->bool |
      d IN UNIONS {(Dn:num->(A->bool)->bool) n | n IN (:num)}}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE];
      USE_THEN "Scover" (fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:A` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:A->bool`
        (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n0:num`) ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:A) IN (P:num->A->bool) n0` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:A) IN (s:A->bool)` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
        REWRITE_TAC[IN_DIFF] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `?r:A->bool. r IN (fn:num->(A->bool)->bool) n0 /\ x IN r`
        STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "P" THEN
        UNDISCH_TAC `(x:A) IN (P:num->A->bool) n0` THEN
        EXPAND_TAC "P" THEN
        REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `top closure_of (r INTER (S:num->A->bool) n0)` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `r INTER (S:num->A->bool) n0` THEN CONJ_TAC THENL
         [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
          EXISTS_TAC `(Dn:num->(A->bool)->bool) n0` THEN CONJ_TAC THENL
           [EXISTS_TAC `n0:num` THEN REFL_TAC;
            EXPAND_TAC "Dn" THEN REWRITE_TAC[IN_ELIM_THM] THEN
            EXISTS_TAC `r:A->bool` THEN ASM_REWRITE_TAC[]];
          REFL_TAC];
        SUBGOAL_THEN `(x:A) IN r INTER (S:num->A->bool) n0` ASSUME_TAC THENL
         [REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `r INTER (S:num->A->bool) n0 SUBSET topspace top`
          ASSUME_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:A->bool` THEN
          REWRITE_TAC[INTER_SUBSET] THEN
          USE_THEN "fnlf" (MP_TAC o CONJUNCT1 o
            REWRITE_RULE[locally_finite_in] o SPEC `n0:num`) THEN
          DISCH_THEN(MP_TAC o SPEC `r:A->bool`) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `r INTER (S:num->A->bool) n0 SUBSET
                      top closure_of (r INTER (S:num->A->bool) n0)`
          ASSUME_TAC THENL
         [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `d:A->bool` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `Dn0:(A->bool)->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n0:num`) ASSUME_TAC)) THEN
    SUBGOAL_THEN `?r:A->bool. r IN (fn:num->(A->bool)->bool) n0 /\
                               d = r INTER (S:num->A->bool) n0`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(d:A->bool) IN Dn0` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Dn" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(r:A->bool) IN R` ASSUME_TAC THENL
     [USE_THEN "fnsub" (MP_TAC o REWRITE_RULE[SUBSET] o SPEC `n0:num`) THEN
      DISCH_THEN(MP_TAC o SPEC `r:A->bool`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:A->bool` o
      REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "clru"))) THEN
    EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `top closure_of (r:A->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_OF_MONO THEN ASM_REWRITE_TAC[INTER_SUBSET];
    MATCH_MP_TAC(ISPEC `top:A topology` LOCALLY_FINITE_IN_CLOSURES) THEN
    ASM_REWRITE_TAC[]]);;

(* Michael's Lemma 1: Indexed CP closed refinement *)

let CP_INDEXED_CLOSED_COVER = prove
 (`!top:A topology U.
        (!U'. (!u. u IN U' ==> open_in top u) /\ UNIONS U' = topspace top
              ==> ?V. (!v. v IN V ==> closed_in top v) /\
                      UNIONS V = topspace top /\
                      (!v. v IN V ==> ?u. u IN U' /\ v SUBSET u) /\
                      (!W. W SUBSET V ==> closed_in top (UNIONS W))) /\
        (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
        ==> ?c. (!u. u IN U ==> closed_in top (c u)) /\
                (!u. u IN U ==> c u SUBSET u) /\
                UNIONS {c u | u IN U} = topspace top /\
                (!S. S SUBSET U
                     ==> closed_in top (UNIONS {c u | u IN S}))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hyp") STRIP_ASSUME_TAC) THEN
  USE_THEN "hyp" (MP_TAC o SPEC `U:(A->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool`
    (CONJUNCTS_THEN2 (LABEL_TAC "Vcl")
     (CONJUNCTS_THEN2 (LABEL_TAC "Vcov")
      (CONJUNCTS_THEN2 (LABEL_TAC "Vref") (LABEL_TAC "Vcp"))))) THEN
  SUBGOAL_THEN
    `?f:(A->bool)->(A->bool). !v. v IN V ==> f v IN U /\ v SUBSET f v`
    (X_CHOOSE_THEN `f:(A->bool)->(A->bool)` (LABEL_TAC "fprop")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
    `\u:A->bool. UNIONS {v:A->bool | v IN V /\
                         (f:(A->bool)->(A->bool)) v = u}` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
    USE_THEN "Vcp" MATCH_MP_TAC THEN SET_TAC[];
    X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN UNIONS V` MP_TAC THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(f:(A->bool)->(A->bool)) v` THEN
      ASM_SIMP_TAC[] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `S:(A->bool)->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `UNIONS {UNIONS {v:A->bool | v IN V /\
                (f:(A->bool)->(A->bool)) v = u} | u IN S} =
       UNIONS {v:A->bool | v IN V /\ (f:(A->bool)->(A->bool)) v IN S}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
      EQ_TAC THENL
       [DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
          (CONJUNCTS_THEN2
            (X_CHOOSE_THEN `u0:A->bool` STRIP_ASSUME_TAC)
            ASSUME_TAC)) THEN
        SUBGOAL_THEN `(x:A) IN UNIONS {v:A->bool | v IN V /\
          (f:(A->bool)->(A->bool)) v = u0}` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `w:A->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC
          `UNIONS {v':A->bool | v' IN V /\
            (f:(A->bool)->(A->bool)) v' =
            (f:(A->bool)->(A->bool)) w}` THEN
        CONJ_TAC THENL
         [EXISTS_TAC `(f:(A->bool)->(A->bool)) w` THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
          EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[]]];
      USE_THEN "Vcp" MATCH_MP_TAC THEN SET_TAC[]]]);;

(* CP closed refinement hypothesis implies normality *)

let CP_IMPLIES_NORMAL_SPACE = prove
 (`!top:A topology.
        (!U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
             ==> ?V. (!v. v IN V ==> closed_in top v) /\
                     UNIONS V = topspace top /\
                     (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                     (!W. W SUBSET V ==> closed_in top (UNIONS W)))
        ==> normal_space top`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "cp") THEN
  REWRITE_TAC[normal_space] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `t:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "disj"))) THEN
  SUBGOAL_THEN `s SUBSET topspace (top:A topology) /\ t SUBSET topspace top`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_SUBSET]; ALL_TAC] THEN
  USE_THEN "cp" (MP_TAC o SPEC
    `{topspace top DIFF s, topspace top DIFF t}:(A->bool)->bool`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
      CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
      USE_THEN "disj" MP_TAC THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                   IN_UNION; IN_DIFF] THEN
      ASM_MESON_TAC[SUBSET]];
    DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool`
      (CONJUNCTS_THEN2 (LABEL_TAC "Vcl")
        (CONJUNCTS_THEN2 (LABEL_TAC "Vcov")
          (CONJUNCTS_THEN2 (LABEL_TAC "Vref") (LABEL_TAC "Vcp"))))) THEN
    SUBGOAL_THEN `!v:A->bool. v IN V
                  ==> v SUBSET topspace top DIFF s \/
                      v SUBSET topspace top DIFF t`
      (LABEL_TAC "Vdich") THENL
     [X_GEN_TAC `v:A->bool` THEN DISCH_TAC THEN
      USE_THEN "Vref" (MP_TAC o SPEC `v:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o
        REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY]) THENL
       [DISJ1_TAC; DISJ2_TAC] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `V1 = {v:A->bool | v IN V /\
                      v SUBSET (topspace top DIFF s)}` THEN
    SUBGOAL_THEN `V1 SUBSET (V:(A->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "V1" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `closed_in top (UNIONS V1:A->bool)` ASSUME_TAC THENL
     [USE_THEN "Vcp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `closed_in top (UNIONS (V DIFF V1):A->bool)`
      ASSUME_TAC THENL
     [USE_THEN "Vcp" MATCH_MP_TAC THEN
      REWRITE_TAC[SUBSET; IN_DIFF] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!v:A->bool. v IN V DIFF V1
                  ==> v SUBSET topspace top DIFF t` ASSUME_TAC THENL
     [X_GEN_TAC `v:A->bool` THEN EXPAND_TAC "V1" THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
      USE_THEN "Vdich" (MP_TAC o SPEC `v:A->bool`) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `UNIONS V1 UNION UNIONS (V DIFF V1:(A->bool)->bool) =
       topspace top:A->bool` ASSUME_TAC THENL
     [USE_THEN "Vcov" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      UNDISCH_TAC `V1 SUBSET (V:(A->bool)->bool)` THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIONS; IN_DIFF; SUBSET] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `topspace top DIFF UNIONS V1:A->bool` THEN
    EXISTS_TAC
      `topspace top DIFF UNIONS (V DIFF V1:(A->bool)->bool):A->bool` THEN
    SUBGOAL_THEN `UNIONS V1 SUBSET topspace top DIFF (s:A->bool)`
      ASSUME_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET] THEN
      X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
      UNDISCH_TAC `(w:A->bool) IN V1` THEN
      EXPAND_TAC "V1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS (V DIFF V1) SUBSET topspace top DIFF (t:A->bool)`
      ASSUME_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      ASM SET_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]]]);;

(* Dowker's expansion lemma: pairwise disjoint open sets in a normal space
   with a closed union of inscribed subsets can be expanded to a locally
   finite family of open sets *)

let DOWKER_DISCRETE_EXPANSION = prove
 (`!top:A topology (s:K->bool) (f:K->A->bool) (d:K->A->bool).
    normal_space top /\
    (!k. k IN s ==> open_in top (f k)) /\
    pairwise (\a b. DISJOINT (f a:A->bool) (f b)) s /\
    (!k. k IN s ==> d k SUBSET f k) /\
    closed_in top (UNIONS {d k | k IN s})
    ==> ?w:K->A->bool.
          (!k. k IN s ==> open_in top (w k)) /\
          (!k. k IN s ==> d k SUBSET w k) /\
          (!k. k IN s ==> w k SUBSET f k) /\
          locally_finite_in top {w k | k IN s}`,
  let FINITE_AT_MOST_ONE = prove
   (`!s:A->bool. (!x y. x IN s /\ y IN s ==> x = y) ==> FINITE s`,
    GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:A->bool = {}` THENL
     [ASM_REWRITE_TAC[FINITE_EMPTY];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{a:A}` THEN
      REWRITE_TAC[FINITE_SING] THEN ASM SET_TAC[]]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
    `S':A->bool = {x | ?v. open_in top v /\ x IN v /\
       !k1:K k2:K. k1 IN s /\ k2 IN s /\
       ~(v INTER (f:K->A->bool) k1 = {}) /\
       ~(v INTER f k2 = {}) ==> k1 = k2}` THEN
  SUBGOAL_THEN `open_in top (S':A->bool)` (LABEL_TAC "Sopen") THENL
   [EXPAND_TAC "S'" THEN
    GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `v0:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v0:A->bool` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    EXISTS_TAC `v0:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(d:K->A->bool) k | k IN s} SUBSET S'`
    (LABEL_TAC "dinS") THENL
   [EXPAND_TAC "S'" THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `k0:K` STRIP_ASSUME_TAC)
        ASSUME_TAC)) THEN
    EXISTS_TAC `(f:K->A->bool) k0` THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`k1:K`; `k2:K`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!k':K. k' IN s /\ ~((f:K->A->bool) k0 INTER f k' = {})
                         ==> k' = k0`
      (fun th -> ASM_MESON_TAC[th]) THEN
    X_GEN_TAC `k':K` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((f:K->A->bool) k0 INTER f k' = {})` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `pairwise (\a b. DISJOINT ((f:K->A->bool) a) (f b)) s` THEN
    REWRITE_TAC[pairwise] THEN
    DISCH_THEN(MP_TAC o SPECL [`k0:K`; `k':K`]) THEN
    ASM_REWRITE_TAC[DISJOINT];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `?R:A->bool. open_in top R /\
       UNIONS {(d:K->A->bool) k | k IN s} SUBSET R /\
       top closure_of R SUBSET S'`
    (X_CHOOSE_THEN `R:A->bool` STRIP_ASSUME_TAC) THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [normal_space]) THEN
    DISCH_THEN(MP_TAC o SPECL
      [`UNIONS {(d:K->A->bool) k | k IN s}`;
       `topspace top DIFF S':A->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_IN_DIFF THEN
        ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
        REWRITE_TAC[DISJOINT] THEN
        MATCH_MP_TAC(SET_RULE
          `(d:A->bool) SUBSET s /\ s SUBSET u
           ==> d INTER (u DIFF s) = {}`) THEN
        ASM_SIMP_TAC[OPEN_IN_SUBSET]];
      DISCH_THEN(X_CHOOSE_THEN `u0:A->bool`
        (X_CHOOSE_THEN `v0:A->bool` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `u0:A->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `topspace top DIFF v0:A->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
         [SUBGOAL_THEN `u0 SUBSET topspace top:A->bool` MP_TAC THENL
           [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
          UNDISCH_TAC `DISJOINT u0 (v0:A->bool)` THEN
          REWRITE_TAC[DISJOINT] THEN SET_TAC[];
          MATCH_MP_TAC CLOSED_IN_DIFF THEN
          ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE]];
        SUBGOAL_THEN `S' SUBSET topspace top:A->bool` MP_TAC THENL
         [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
        UNDISCH_TAC `topspace top DIFF S' SUBSET (v0:A->bool)` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `\k:K. (f:K->A->bool) k INTER R` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:K` THEN DISCH_TAC THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[];
    X_GEN_TAC `k:K` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
      `(a:A->bool) SUBSET b /\ a SUBSET c ==> a SUBSET b INTER c`) THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {(d:K->A->bool) k | k IN s}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    EXISTS_TAC `(d:K->A->bool) k` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `k:K` THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[INTER_SUBSET];
    REWRITE_TAC[locally_finite_in] THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE
        `(a:A->bool) SUBSET t ==> a INTER r SUBSET t`) THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:A) IN top closure_of R` THENL
     [SUBGOAL_THEN `(x:A) IN S'` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:A) IN S'` THEN EXPAND_TAC "S'" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `v1:A->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "atmost1")))) THEN
      EXISTS_TAC `v1:A->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\k:K. (f:K->A->bool) k INTER R)
                    {k | k IN s /\ ~((f k INTER R) INTER v1 = {})}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_AT_MOST_ONE THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY X_GEN_TAC [`k1:K`; `k2:K`] THEN STRIP_TAC THEN
        USE_THEN "atmost1" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `~(((f:K->A->bool) k1 INTER R) INTER v1 = {})` THEN
          SET_TAC[];
          UNDISCH_TAC `~(((f:K->A->bool) k2 INTER R) INTER v1 = {})` THEN
          SET_TAC[]];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
        X_GEN_TAC `t:A->bool` THEN
        DISCH_THEN(CONJUNCTS_THEN2
          (X_CHOOSE_THEN `k0:K` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
        EXISTS_TAC `k0:K` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_MESON_TAC[]];
      EXISTS_TAC `topspace top DIFF top closure_of R:A->bool` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_DIFF THEN
        REWRITE_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_CLOSURE_OF];
        ASM SET_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{}:(A->bool)->bool` THEN
        REWRITE_TAC[FINITE_EMPTY; SUBSET; NOT_IN_EMPTY; IN_ELIM_THM] THEN
        X_GEN_TAC `t:A->bool` THEN
        DISCH_THEN(CONJUNCTS_THEN2
          (X_CHOOSE_THEN `k0:K` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
        SUBGOAL_THEN `(f:K->A->bool) k0 INTER R SUBSET top closure_of R`
          MP_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `R:A->bool` THEN
          REWRITE_TAC[INTER_SUBSET] THEN
          MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
          ASM_MESON_TAC[OPEN_IN_SUBSET];
          UNDISCH_TAC
            `~(t INTER (topspace top DIFF top closure_of R:A->bool) =
               {})` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[]]]]]);;

(* Helper: LF closed refinement property implies paracompactness
   (when regularity is available). Uses LF_COVERING_IMP_LF_OPEN. *)

let CLOSED_REFINEMENT_IMP_PARACOMPACT = prove
 (`!top:A topology.
        regular_space top /\
        (!U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
             ==> ?V. (!v. v IN V ==> closed_in top v) /\
                     UNIONS V = topspace top /\
                     (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                     locally_finite_in top V)
        ==> paracompact_space top`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[paracompact_space] THEN
  X_GEN_TAC `U:(A->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `top:A topology` LF_COVERING_IMP_LF_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `B:(A->bool)->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `B:(A->bool)->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `C:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `U:(A->bool)->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `W:(A->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let MICHAEL_PARACOMPACT = prove
 (`!top:A topology.
        regular_space top /\
        (!U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
             ==> ?V. (!v. v IN V ==> closed_in top v) /\
                     UNIONS V = topspace top /\
                     (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                     (!W. W SUBSET V ==> closed_in top (UNIONS W)))
        ==> paracompact_space top`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "reg") (LABEL_TAC "cp")) THEN
  MATCH_MP_TAC CLOSED_REFINEMENT_IMP_PARACOMPACT THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `U:(A->bool)->bool` THEN STRIP_TAC THEN
  (* Shrink cover by regularity *)
  MP_TAC(ISPECL [`top:A topology`; `U:(A->bool)->bool`]
    REGULAR_OPEN_COVER_CLOSURE_SHRINK) THEN
  ANTS_TAC THENL
   [USE_THEN "reg" (fun th -> ASM_REWRITE_TAC[th]); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  (* Build sigma-LF open refinement with closure containment in U *)
  SUBGOAL_THEN
    `?R:(A->bool)->bool.
       (!r. r IN R ==> open_in top r) /\
       UNIONS R = topspace top /\
       (!r. r IN R ==> ?u. u IN U /\ top closure_of r SUBSET u) /\
       sigma_locally_finite_in top R`
    STRIP_ASSUME_TAC THENL
   [(* ============================================================== *)
    (* Michael's iterative construction: produce sigma-LF open R      *)
    (* ============================================================== *)
    (* Step 1: Normality from CP *)
    SUBGOAL_THEN `normal_space (top:A topology)` (LABEL_TAC "norm") THENL
     [MATCH_MP_TAC CP_IMPLIES_NORMAL_SPACE THEN
      USE_THEN "cp" ACCEPT_TAC; ALL_TAC] THEN
    (* Step 2: Well-order W *)
    MP_TAC(ISPEC `W:(A->bool)->bool` WO) THEN
    DISCH_THEN(X_CHOOSE_THEN `ord:(A->bool)->(A->bool)->bool`
      (CONJUNCTS_THEN2 (LABEL_TAC "wos") (LABEL_TAC "fldW"))) THEN
    (* Step 3: Initial CP indexed closed cover of W *)
    MP_TAC(ISPECL [`top:A topology`; `W:(A->bool)->bool`]
      CP_INDEXED_CLOSED_COVER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [USE_THEN "cp" ACCEPT_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:(A->bool)->(A->bool)`
      (CONJUNCTS_THEN2 (LABEL_TAC "c0cl")
       (CONJUNCTS_THEN2 (LABEL_TAC "c0sub")
        (CONJUNCTS_THEN2 (LABEL_TAC "c0cov") (LABEL_TAC "c0cp"))))) THEN
    (* Step 3b: Define nxt using Hilbert choice *)
    ABBREV_TAC
      `nxt = \(c:(A->bool)->(A->bool)).
         @c':(A->bool)->(A->bool).
           (!w:A->bool. w IN W ==> closed_in top (c' w)) /\
           (!w:A->bool. w IN W ==>
              c' w SUBSET w DIFF
                UNIONS {c v | v IN W /\
                  (ord:(A->bool)->(A->bool)->bool) v w /\ ~(v = w)}) /\
           UNIONS {c' w | w IN W} = topspace top /\
           (!ss:(A->bool)->bool. ss SUBSET W ==>
              closed_in top (UNIONS {c' w | w IN ss}))` THEN
    (* Step 4: Build sequence C : num -> ((A->bool) -> (A->bool)) *)
    MP_TAC(ISPECL
      [`c0:(A->bool)->(A->bool)`;
       `\(c:(A->bool)->(A->bool)) (n:num).
          (nxt:((A->bool)->(A->bool))->(A->bool)->(A->bool)) c`]
       num_RECURSION) THEN
    DISCH_THEN(X_CHOOSE_THEN `C:num->(A->bool)->(A->bool)`
      (CONJUNCTS_THEN2 (LABEL_TAC "C0") (LABEL_TAC "Csuc"))) THEN
    (* Step 4a: C n has the CP properties for all n (by induction) *)
    SUBGOAL_THEN
      `!n:num.
        (!w:A->bool. w IN W ==> closed_in top (C n w)) /\
        (!w:A->bool. w IN W ==> C n w SUBSET w) /\
        UNIONS {(C:num->(A->bool)->(A->bool)) n w | w IN W} =
          topspace top /\
        (!ss:(A->bool)->bool. ss SUBSET W ==>
           closed_in top (UNIONS {C n w | w IN ss}))`
      (LABEL_TAC "Cvalid") THENL
     [INDUCT_TAC THENL
       [(* Base case: n = 0, C 0 = c0 *)
        USE_THEN "C0" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "c0cl" (fun cl ->
        USE_THEN "c0sub" (fun sub ->
        USE_THEN "c0cov" (fun cov ->
        USE_THEN "c0cp" (fun cp ->
          ACCEPT_TAC(CONJ cl (CONJ sub (CONJ cov cp)))))));
        (* Inductive step: IH for C n, prove for C(SUC n) *)
        POP_ASSUM(fun ih ->
          LABEL_TAC "IHcl" (CONJUNCT1 ih) THEN
          LABEL_TAC "IHsub" (CONJUNCT1(CONJUNCT2 ih)) THEN
          LABEL_TAC "IHcov" (CONJUNCT1(CONJUNCT2(CONJUNCT2 ih))) THEN
          LABEL_TAC "IHcp" (CONJUNCT2(CONJUNCT2(CONJUNCT2 ih)))) THEN
        (* Step I-1: The predecessor-reduced open sets cover topspace *)
        SUBGOAL_THEN
          `(!w:A->bool. w IN W ==>
             open_in top (w DIFF UNIONS
               {(C:num->(A->bool)->(A->bool)) n v | v |
                v IN W /\ (ord:(A->bool)->(A->bool)->bool) v w /\
                ~(v = w)})) /\
           UNIONS {w DIFF UNIONS
             {(C:num->(A->bool)->(A->bool)) n v | v |
              v IN W /\ (ord:(A->bool)->(A->bool)->bool) v w /\
              ~(v = w)} | w | w IN W} = topspace top`
          STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [(* Each element is open: w is open, UNIONS{C n v|...} closed *)
            X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
            MATCH_MP_TAC OPEN_IN_DIFF THEN CONJ_TAC THENL
             [ASM_MESON_TAC[];
              USE_THEN "IHcp" (MP_TAC o SPEC
                `{v:A->bool | v IN W /\
                   (ord:(A->bool)->(A->bool)->bool) v w /\
                   ~(v = w)}`) THEN
              ANTS_TAC THENL
               [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
                REWRITE_TAC[IN_ELIM_THM]]];
            (* The family covers topspace *)
            MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
             [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
              X_GEN_TAC `ww:A->bool` THEN DISCH_TAC THEN
              MATCH_MP_TAC SUBSET_TRANS THEN
              EXISTS_TAC `ww:A->bool` THEN
              CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[OPEN_IN_SUBSET]];
              (* topspace SUBSET UNIONS{...} via well-ordering least element *)
              REWRITE_TAC[SUBSET] THEN
              X_GEN_TAC `xx:A` THEN DISCH_TAC THEN
              REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
              (* Find ord-least ww with xx IN C n ww *)
              USE_THEN "wos"
                (MP_TAC o CONJUNCT2 o REWRITE_RULE[WOSET]) THEN
              USE_THEN "fldW" (fun th -> REWRITE_TAC[th]) THEN
              DISCH_THEN(MP_TAC o SPEC
                `{w:A->bool | w IN W /\
                   (xx:A) IN (C:num->(A->bool)->(A->bool)) n w}`) THEN
              ANTS_TAC THENL
               [CONJ_TAC THENL
                 [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
                  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
                  SUBGOAL_THEN
                    `(xx:A) IN UNIONS
                       {(C:num->(A->bool)->(A->bool)) n w | w IN W}`
                    MP_TAC THENL
                   [USE_THEN "IHcov" (fun th -> ASM_REWRITE_TAC[th]);
                    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
                    MESON_TAC[]]];
                ALL_TAC] THEN
              REWRITE_TAC[IN_ELIM_THM] THEN
              DISCH_THEN(X_CHOOSE_THEN `ww:A->bool`
                STRIP_ASSUME_TAC) THEN
              (* ww is ord-least with xx IN C n ww *)
              EXISTS_TAC
                `ww DIFF UNIONS
                  {(C:num->(A->bool)->(A->bool)) n v | v |
                   v IN W /\
                   (ord:(A->bool)->(A->bool)->bool) v ww /\
                   ~(v = ww)}` THEN
              CONJ_TAC THENL
               [EXISTS_TAC `ww:A->bool` THEN ASM_REWRITE_TAC[];
                ALL_TAC] THEN
              REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
              CONJ_TAC THENL
               [USE_THEN "IHsub" (MP_TAC o SPEC `ww:A->bool`) THEN
                ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
                REWRITE_TAC[NOT_EXISTS_THM;
                  TAUT `~(p /\ q) <=> p ==> ~q`] THEN
                X_GEN_TAC `ss:A->bool` THEN
                DISCH_THEN(X_CHOOSE_THEN `vv:A->bool`
                  STRIP_ASSUME_TAC) THEN
                ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
                MP_TAC(MATCH_MP WOSET_ANTISYM
                  (ASSUME
                    `woset(ord:(A->bool)->(A->bool)->bool)`)) THEN
                ASM_MESON_TAC[]]]];
          ALL_TAC] THEN
        (* Step I-2: Apply CP to get indexed closed cover *)
        SUBGOAL_THEN
          `?c':(A->bool)->(A->bool).
             (!w. w IN W ==> closed_in top (c' w)) /\
             (!w:A->bool. w IN W ==>
                c' w SUBSET w DIFF UNIONS
                  {(C:num->(A->bool)->(A->bool)) n v |
                   v IN W /\
                   (ord:(A->bool)->(A->bool)->bool) v w /\
                   ~(v = w)}) /\
             UNIONS {c' w | w IN W} = topspace top /\
             (!ss:(A->bool)->bool. ss SUBSET W ==>
                closed_in top (UNIONS {c' w | w IN ss}))`
          STRIP_ASSUME_TAC THENL
         [(* Apply CP to the open cover *)
          USE_THEN "cp" (MP_TAC o SPEC
            `{w DIFF UNIONS
               {(C:num->(A->bool)->(A->bool)) n v | v |
                v IN W /\
                (ord:(A->bool)->(A->bool)->bool) v w /\
                ~(v = w)} |
              w | (w:A->bool) IN W}`) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[FORALL_IN_GSPEC]; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool`
            (CONJUNCTS_THEN2 (LABEL_TAC "Vcl")
             (CONJUNCTS_THEN2 (LABEL_TAC "Vcov")
              (CONJUNCTS_THEN2 (LABEL_TAC "Vref")
                (LABEL_TAC "Vcp"))))) THEN
          (* For each v IN V, pick g(v) IN W with v SUBSET OO(g(v)) *)
          SUBGOAL_THEN
            `?g:(A->bool)->(A->bool). !v:A->bool. v IN V ==>
               g v IN W /\
               v SUBSET g v DIFF UNIONS
                 {(C:num->(A->bool)->(A->bool)) n u |
                  u IN W /\
                  (ord:(A->bool)->(A->bool)->bool) u (g v) /\
                  ~(u = g v)}`
            (X_CHOOSE_THEN `g:(A->bool)->(A->bool)`
              (LABEL_TAC "gprop")) THENL
           [REWRITE_TAC[GSYM SKOLEM_THM] THEN
            X_GEN_TAC `v:A->bool` THEN
            ASM_CASES_TAC `(v:A->bool) IN V` THENL
             [USE_THEN "Vref" (MP_TAC o SPEC `v:A->bool`) THEN
              ANTS_TAC THENL
               [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
              DISCH_THEN(X_CHOOSE_THEN `oo:A->bool`
                (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
              REWRITE_TAC[IN_ELIM_THM] THEN
              DISCH_THEN(X_CHOOSE_THEN `w':A->bool`
                (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
              EXISTS_TAC `w':A->bool` THEN
              DISCH_TAC THEN ASM_REWRITE_TAC[];
              EXISTS_TAC `v:A->bool` THEN ASM_MESON_TAC[]];
            ALL_TAC] THEN
          (* Define c'(w) = UNIONS{v IN V | g(v) = w} *)
          EXISTS_TAC
            `\w:A->bool. UNIONS {v:A->bool | v IN V /\
               (g:(A->bool)->(A->bool)) v = w}` THEN
          REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
           [(* c'(w) closed: {v | v IN V /\ g v = w} SUBSET V *)
            X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
            USE_THEN "Vcp" MATCH_MP_TAC THEN SET_TAC[];
            (* c'(w) SUBSET OO(w) *)
            X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
            REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
            X_GEN_TAC `v:A->bool` THEN
            DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
              (fun th -> SUBST_ALL_TAC(SYM th))) THEN
            USE_THEN "gprop" (MP_TAC o SPEC `v:A->bool`) THEN
            ANTS_TAC THENL
             [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
            DISCH_THEN(fun th -> REWRITE_TAC[th]);
            (* UNIONS{c'(w) | w IN W} = topspace *)
            USE_THEN "Vcov" (fun th -> REWRITE_TAC[SYM th]) THEN
            MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
             [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
              X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
              REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
              SET_TAC[];
              REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
              X_GEN_TAC `x:A` THEN
              DISCH_THEN(X_CHOOSE_THEN `v:A->bool`
                STRIP_ASSUME_TAC) THEN
              EXISTS_TAC `UNIONS {v':A->bool | v' IN V /\
                (g:(A->bool)->(A->bool)) v' =
                  (g:(A->bool)->(A->bool)) v}` THEN
              CONJ_TAC THENL
               [REWRITE_TAC[IN_ELIM_THM] THEN
                EXISTS_TAC `(g:(A->bool)->(A->bool)) v` THEN
                CONJ_TAC THENL
                 [USE_THEN "gprop" (MP_TAC o SPEC `v:A->bool`) THEN
                  ANTS_TAC THENL
                   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
                  MESON_TAC[];
                  REFL_TAC];
                REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
                EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[]]];
            (* CP: UNIONS{c'(w) | w IN ss} closed *)
            X_GEN_TAC `ss:(A->bool)->bool` THEN DISCH_TAC THEN
            SUBGOAL_THEN
              `UNIONS {UNIONS {v:A->bool | v IN V /\
                 (g:(A->bool)->(A->bool)) v = w} |
                 (w:A->bool) IN ss} =
               UNIONS {v:A->bool | v IN V /\ g v IN ss}`
              (fun th -> REWRITE_TAC[th]) THENL
             [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
               [(* forward *)
                REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
                X_GEN_TAC `ww:A->bool` THEN DISCH_TAC THEN
                REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
                X_GEN_TAC `vv:A->bool` THEN DISCH_TAC THEN
                REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
                X_GEN_TAC `y:A` THEN DISCH_TAC THEN
                EXISTS_TAC `vv:A->bool` THEN
                ASM_MESON_TAC[];
                (* backward *)
                REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
                X_GEN_TAC `y:A` THEN
                DISCH_THEN(X_CHOOSE_THEN `vv:A->bool`
                  STRIP_ASSUME_TAC) THEN
                EXISTS_TAC
                  `UNIONS {v':A->bool | v' IN V /\
                    (g:(A->bool)->(A->bool)) v' =
                    (g:(A->bool)->(A->bool)) vv}` THEN
                CONJ_TAC THENL
                 [EXISTS_TAC `(g:(A->bool)->(A->bool)) vv` THEN
                  ASM_REWRITE_TAC[];
                  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
                  EXISTS_TAC `vv:A->bool` THEN ASM_REWRITE_TAC[]]];
              USE_THEN "Vcp" MATCH_MP_TAC THEN SET_TAC[]]];
          ALL_TAC] THEN
        (* Step I-3: nxt(C n) satisfies the properties via SELECT *)
        SUBGOAL_THEN
          `(!w:A->bool. w IN W ==>
             closed_in top
               ((nxt:((A->bool)->(A->bool))->(A->bool)->(A->bool))
                ((C:num->(A->bool)->(A->bool)) n) w)) /\
           (!w:A->bool. w IN W ==>
             nxt (C n) w SUBSET w DIFF UNIONS
               {C n v | v IN W /\
                (ord:(A->bool)->(A->bool)->bool) v w /\ ~(v = w)}) /\
           UNIONS {nxt (C n) w | w IN W} = topspace top /\
           (!ss:(A->bool)->bool. ss SUBSET W ==>
             closed_in top (UNIONS {nxt (C n) w | w IN ss}))`
          STRIP_ASSUME_TAC THENL
         [(* nxt(C n) = @c'. P(C n, c'), and we have ?c'. P(C n, c') *)
          (* Build the existential from assumptions, then use SELECT_RULE *)
          SUBGOAL_THEN
            `?c':(A->bool)->(A->bool).
               (!w. w IN W ==> closed_in top (c' w)) /\
               (!w:A->bool. w IN W ==>
                  c' w SUBSET w DIFF UNIONS
                    {(C:num->(A->bool)->(A->bool)) n v |
                     v IN W /\
                     (ord:(A->bool)->(A->bool)->bool) v w /\
                     ~(v = w)}) /\
               UNIONS {c' w | w IN W} = topspace top /\
               (!ss:(A->bool)->bool. ss SUBSET W ==>
                  closed_in top (UNIONS {c' w | w IN ss}))`
            MP_TAC THENL
           [EXISTS_TAC `c':(A->bool)->(A->bool)` THEN
            ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          EXPAND_TAC "nxt" THEN REWRITE_TAC[] THEN
          DISCH_THEN(fun th -> ACCEPT_TAC(SELECT_RULE th));
          ALL_TAC] THEN
        (* Step I-4: Extract the 4 Cvalid properties for C(SUC n) *)
        USE_THEN "Csuc" (fun th ->
          REWRITE_TAC[SPEC `n:num` th]) THEN
        REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          (* C(SUC n) w SUBSET w: from nxt SUBSET w DIFF ... SUBSET w *)
          X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `w DIFF UNIONS
            {(C:num->(A->bool)->(A->bool)) n v |
             v IN W /\
             (ord:(A->bool)->(A->bool)->bool) v w /\
             ~(v = w)}` THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
            SET_TAC[]];
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    (* Step 4a2: Stronger subset property via nxt/SELECT *)
    SUBGOAL_THEN
      `!n:num w:A->bool. w IN W ==>
        (C:num->(A->bool)->(A->bool)) (SUC n) w SUBSET
        w DIFF UNIONS {C n v | v IN W /\
          (ord:(A->bool)->(A->bool)->bool) v w /\ ~(v = w)}`
      (LABEL_TAC "Csub_strong") THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "Csuc" (fun th -> REWRITE_TAC[SPEC `n:num` th]) THEN
      REWRITE_TAC[] THEN
      (* Expand nxt so goal becomes (@c'. P(C n, c')) w SUBSET ... *)
      EXPAND_TAC "nxt" THEN REWRITE_TAC[] THEN
      (* Show ?c'. P(C n, c'), then SELECT gives the result *)
      USE_THEN "Cvalid" (MP_TAC o SPEC `n:num`) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Ccl_n")
        (CONJUNCTS_THEN2 (LABEL_TAC "Csb_n")
          (CONJUNCTS_THEN2 (LABEL_TAC "Ccv_n")
            (LABEL_TAC "Ccp_n")))) THEN
      SUBGOAL_THEN
        `?c':(A->bool)->(A->bool).
           (!w'. w' IN W ==> closed_in top (c' w')) /\
           (!w':A->bool. w' IN W ==>
              c' w' SUBSET w' DIFF UNIONS
                {(C:num->(A->bool)->(A->bool)) n v | v IN W /\
                 (ord:(A->bool)->(A->bool)->bool) v w' /\ ~(v = w')}) /\
           UNIONS {c' w' | w' IN W} = topspace top /\
           (!ss:(A->bool)->bool. ss SUBSET W ==>
              closed_in top (UNIONS {c' w' | w' IN ss}))`
        (fun th ->
          let sr = SELECT_RULE th in
          ACCEPT_TAC(MP (SPEC `w:A->bool` (CONJUNCT1(CONJUNCT2 sr)))
            (ASSUME `(w:A->bool) IN W`))) THEN
      (* Prove existence via cp *)
      USE_THEN "cp" (MP_TAC o SPEC
        `{w' DIFF UNIONS
           {(C:num->(A->bool)->(A->bool)) n v | v |
            v IN W /\ (ord:(A->bool)->(A->bool)->bool) v w' /\
            ~(v = w')} |
          w' | (w':A->bool) IN W}`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
         [(* Each OO(w') is open *)
          X_GEN_TAC `w':A->bool` THEN DISCH_TAC THEN
          MATCH_MP_TAC OPEN_IN_DIFF THEN CONJ_TAC THENL
           [ASM_MESON_TAC[];
            USE_THEN "Ccp_n" (MP_TAC o SPEC
              `{v:A->bool | v IN W /\
                 (ord:(A->bool)->(A->bool)->bool) v w' /\
                 ~(v = w')}`) THEN
            ANTS_TAC THENL
             [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
              REWRITE_TAC[IN_ELIM_THM]]];
          (* UNIONS covers topspace - well-ordering argument *)
          MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
           [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
            X_GEN_TAC `w':A->bool` THEN DISCH_TAC THEN
            MATCH_MP_TAC SUBSET_TRANS THEN
            EXISTS_TAC `w':A->bool` THEN
            CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[OPEN_IN_SUBSET]];
            REWRITE_TAC[SUBSET] THEN X_GEN_TAC `xx:A` THEN DISCH_TAC THEN
            REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
            USE_THEN "wos"
              (MP_TAC o CONJUNCT2 o REWRITE_RULE[WOSET]) THEN
            USE_THEN "fldW" (fun th -> REWRITE_TAC[th]) THEN
            DISCH_THEN(MP_TAC o SPEC
              `{ww:A->bool | ww IN W /\
                 (xx:A) IN (C:num->(A->bool)->(A->bool)) n ww}`) THEN
            ANTS_TAC THENL
             [CONJ_TAC THENL
               [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
                REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
                SUBGOAL_THEN
                  `(xx:A) IN UNIONS
                     {(C:num->(A->bool)->(A->bool)) n ww | ww IN W}`
                  MP_TAC THENL
                 [USE_THEN "Ccv_n" (fun th -> ASM_REWRITE_TAC[th]);
                  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
                  MESON_TAC[]]];
              ALL_TAC] THEN
            REWRITE_TAC[IN_ELIM_THM] THEN
            DISCH_THEN(X_CHOOSE_THEN `ww:A->bool`
              STRIP_ASSUME_TAC) THEN
            EXISTS_TAC
              `ww DIFF UNIONS
                {(C:num->(A->bool)->(A->bool)) n v | v |
                 v IN W /\
                 (ord:(A->bool)->(A->bool)->bool) v ww /\
                 ~(v = ww)}` THEN
            CONJ_TAC THENL
             [EXISTS_TAC `ww:A->bool` THEN ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
            CONJ_TAC THENL
             [USE_THEN "Csb_n" (MP_TAC o SPEC `ww:A->bool`) THEN
              ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
              REWRITE_TAC[NOT_EXISTS_THM;
                TAUT `~(p /\ q) <=> p ==> ~q`] THEN
              X_GEN_TAC `ss:A->bool` THEN
              DISCH_THEN(X_CHOOSE_THEN `vv:A->bool`
                STRIP_ASSUME_TAC) THEN
              ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
              MP_TAC(MATCH_MP WOSET_ANTISYM
                (ASSUME
                  `woset(ord:(A->bool)->(A->bool)->bool)`)) THEN
              ASM_MESON_TAC[]]]];
        ALL_TAC] THEN
      (* Got V from CP. Construct c' indexed by W *)
      DISCH_THEN(X_CHOOSE_THEN `V2:(A->bool)->bool`
        (CONJUNCTS_THEN2 (LABEL_TAC "V2cl")
          (CONJUNCTS_THEN2 (LABEL_TAC "V2cov")
            (CONJUNCTS_THEN2 (LABEL_TAC "V2ref")
              (LABEL_TAC "V2cp"))))) THEN
      SUBGOAL_THEN
        `?g2:(A->bool)->(A->bool). !v:A->bool. v IN V2 ==>
           g2 v IN W /\
           v SUBSET g2 v DIFF UNIONS
             {(C:num->(A->bool)->(A->bool)) n u |
              u IN W /\
              (ord:(A->bool)->(A->bool)->bool) u (g2 v) /\
              ~(u = g2 v)}`
        (X_CHOOSE_THEN `g2:(A->bool)->(A->bool)`
          (LABEL_TAC "g2prop")) THENL
       [REWRITE_TAC[GSYM SKOLEM_THM] THEN
        X_GEN_TAC `v:A->bool` THEN
        ASM_CASES_TAC `(v:A->bool) IN V2` THENL
         [USE_THEN "V2ref" (MP_TAC o SPEC `v:A->bool`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          DISCH_THEN(X_CHOOSE_THEN `oo:A->bool`
            (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
          DISCH_THEN(X_CHOOSE_THEN `w':A->bool`
            (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
          EXISTS_TAC `w':A->bool` THEN
          DISCH_TAC THEN CONJ_TAC THENL
           [FIRST_ASSUM ACCEPT_TAC;
            FIRST_ASSUM ACCEPT_TAC];
          EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      EXISTS_TAC
        `\w':A->bool. UNIONS {v:A->bool | v IN V2 /\
           (g2:(A->bool)->(A->bool)) v = w'}` THEN
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [(* closed *)
        X_GEN_TAC `w':A->bool` THEN DISCH_TAC THEN
        USE_THEN "V2cp" MATCH_MP_TAC THEN SET_TAC[];
        (* subset *)
        X_GEN_TAC `w':A->bool` THEN DISCH_TAC THEN
        REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `v:A->bool` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
          (fun th -> SUBST_ALL_TAC(SYM th))) THEN
        USE_THEN "g2prop" (MP_TAC o SPEC `v:A->bool`) THEN
        ANTS_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]);
        (* covering *)
        USE_THEN "V2cov" (fun th -> REWRITE_TAC[SYM th]) THEN
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
          X_GEN_TAC `w':A->bool` THEN DISCH_TAC THEN
          REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
          X_GEN_TAC `v:A->bool` THEN DISCH_TAC THEN
          REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
          X_GEN_TAC `y:A` THEN DISCH_TAC THEN
          EXISTS_TAC `v:A->bool` THEN ASM_MESON_TAC[];
          REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
          X_GEN_TAC `y:A` THEN
          DISCH_THEN(X_CHOOSE_THEN `v:A->bool`
            STRIP_ASSUME_TAC) THEN
          EXISTS_TAC
            `UNIONS {v':A->bool | v' IN V2 /\
              (g2:(A->bool)->(A->bool)) v' = g2 v}` THEN
          CONJ_TAC THENL
           [EXISTS_TAC `(g2:(A->bool)->(A->bool)) v` THEN
            CONJ_TAC THENL
             [ASM_MESON_TAC[];
              REFL_TAC];
            REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
            EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[]]];
        (* cp *)
        X_GEN_TAC `ss:(A->bool)->bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN
          `UNIONS {UNIONS {v:A->bool | v IN V2 /\
             (g2:(A->bool)->(A->bool)) v = w'} |
            w' | (w':A->bool) IN ss} =
           UNIONS {v:A->bool | v IN V2 /\ g2 v IN ss}`
          SUBST1_TAC THENL
         [MATCH_MP_TAC SUBSET_ANTISYM THEN
          REWRITE_TAC[UNIONS_GSPEC; SUBSET; IN_ELIM_THM] THEN
          POP_ASSUM_LIST(K ALL_TAC) THEN
          CONJ_TAC THEN X_GEN_TAC `a:A` THEN MESON_TAC[];
          USE_THEN "V2cp" MATCH_MP_TAC THEN SET_TAC[]]];
      ALL_TAC] THEN
    (* Step 4b: Disjointness: C(SUC n)(w1) INTER C(n)(w2) = {} when w2 < w1 *)
    SUBGOAL_THEN
      `!n:num w1 w2:A->bool.
         w1 IN W /\ w2 IN W /\
         (ord:(A->bool)->(A->bool)->bool) w2 w1 /\ ~(w2 = w1)
         ==> (C:num->(A->bool)->(A->bool)) (SUC n) w1 INTER
             C n w2 = {}`
      (LABEL_TAC "Cdisj") THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN
        `(C:num->(A->bool)->(A->bool)) (SUC n) w1 SUBSET
         w1 DIFF UNIONS {C n v | v IN W /\
           (ord:(A->bool)->(A->bool)->bool) v w1 /\ ~(v = w1)}`
        ASSUME_TAC THENL
       [USE_THEN "Csub_strong" (MP_TAC o SPECL [`n:num`; `w1:A->bool`]) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
        `(C:num->(A->bool)->(A->bool)) n w2 SUBSET
         UNIONS {C n v | v IN W /\
           (ord:(A->bool)->(A->bool)->bool) v w1 /\ ~(v = w1)}`
        ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `y:A` THEN DISCH_TAC THEN
        EXISTS_TAC `(C:num->(A->bool)->(A->bool)) n w2` THEN
        CONJ_TAC THENL
         [EXISTS_TAC `w2:A->bool` THEN ASM_REWRITE_TAC[];
          FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    (* Step 5: Define VV n w = topspace \ UNIONS{C n v | v <> w} *)
    ABBREV_TAC `VV = \(n:num) (w:A->bool).
      topspace top DIFF
        UNIONS {(C:num->(A->bool)->(A->bool)) n v | v IN W /\
                ~(v = w)}` THEN
    (* Step 5a: VV n w is open *)
    SUBGOAL_THEN
      `!n:num w:A->bool. w IN W ==>
        open_in top ((VV:num->(A->bool)->(A->bool)) n w)`
      (LABEL_TAC "Vopen") THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "VV" THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
      USE_THEN "Cvalid" (MP_TAC o SPEC `n:num`) THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPEC `{v:A->bool | v IN W /\ ~(v = w)}`) THEN
      ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
        `{(C:num->(A->bool)->(A->bool)) n w' |
           w' IN {v:A->bool | v IN W /\ ~(v = w)}} =
         {C n v | v IN W /\ ~(v = w)}`
        (fun th -> REWRITE_TAC[th]) THEN
      SET_TAC[];
      ALL_TAC] THEN
    (* Step 5b: VV n w SUBSET C n w *)
    SUBGOAL_THEN
      `!n:num w:A->bool. w IN W ==>
        (VV:num->(A->bool)->(A->bool)) n w SUBSET C n w`
      (LABEL_TAC "VsubC") THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "VV" THEN
      REWRITE_TAC[SUBSET; IN_DIFF] THEN
      X_GEN_TAC `y:A` THEN STRIP_TAC THEN
      USE_THEN "Cvalid" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      SUBGOAL_THEN
        `?v:A->bool. v IN W /\
            (y:A) IN (C:num->(A->bool)->(A->bool)) n v`
        STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN
          `(y:A) IN UNIONS {(C:num->(A->bool)->(A->bool)) n v | v IN W}`
          MP_TAC THENL
         [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_UNIONS; IN_ELIM_THM]] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `v:A->bool = w` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN
        `(y:A) IN
         UNIONS {(C:num->(A->bool)->(A->bool)) n v' |
                 v' IN W /\ ~(v' = w)}`
        MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `(C:num->(A->bool)->(A->bool)) n v` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:A->bool` THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    (* Step 5c: VV n w are pairwise disjoint for fixed n *)
    SUBGOAL_THEN
      `!n:num w1 w2:A->bool. w1 IN W /\ w2 IN W /\ ~(w1 = w2)
         ==> (VV:num->(A->bool)->(A->bool)) n w1 INTER VV n w2 = {}`
      (LABEL_TAC "Vpd") THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      (* VV n w1 SUBSET C n w1 *)
      SUBGOAL_THEN
        `(VV:num->(A->bool)->(A->bool)) n w1 SUBSET
         (C:num->(A->bool)->(A->bool)) n w1`
        ASSUME_TAC THENL
       [USE_THEN "VsubC" (fun th ->
          MATCH_MP_TAC(SPECL [`n:num`; `w1:A->bool`] th)) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      (* C n w1 SUBSET UNIONS{C n v | v IN W, v <> w2} since w1 <> w2 *)
      SUBGOAL_THEN
        `(C:num->(A->bool)->(A->bool)) n w1 SUBSET
         UNIONS {C n v | v IN W /\ ~(v = w2)}`
        ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `y:A` THEN DISCH_TAC THEN
        EXISTS_TAC `(C:num->(A->bool)->(A->bool)) n w1` THEN
        ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `w1:A->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      (* VV n w2 INTER C n w1 = {} *)
      SUBGOAL_THEN
        `(VV:num->(A->bool)->(A->bool)) n w2 INTER
         (C:num->(A->bool)->(A->bool)) n w1 = {}`
        ASSUME_TAC THENL
       [EXPAND_TAC "VV" THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    (* Step 6: {VV (SUC n) w | n, w} covers X *)
    SUBGOAL_THEN
      `!x:A. x IN topspace top ==>
        ?n:num w:A->bool. w IN W /\
          x IN (VV:num->(A->bool)->(A->bool)) (SUC n) w`
      (LABEL_TAC "Vcover") THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      (* For each n, find the ord-least w with x IN C n w *)
      SUBGOAL_THEN
        `!n:num. ?w0:A->bool. w0 IN W /\
           (x:A) IN (C:num->(A->bool)->(A->bool)) n w0 /\
           !v. v IN W /\ x IN C n v ==>
             (ord:(A->bool)->(A->bool)->bool) w0 v`
        MP_TAC THENL
       [GEN_TAC THEN
        USE_THEN "wos"
          (MP_TAC o CONJUNCT2 o REWRITE_RULE[WOSET]) THEN
        USE_THEN "fldW" (fun th -> REWRITE_TAC[th]) THEN
        DISCH_THEN(MP_TAC o SPEC
          `{w:A->bool | w IN W /\
             (x:A) IN (C:num->(A->bool)->(A->bool)) n w}`) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
            REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
            USE_THEN "Cvalid" (MP_TAC o SPEC `n:num`) THEN
            DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
            DISCH_TAC THEN
            SUBGOAL_THEN
              `(x:A) IN UNIONS
                 {(C:num->(A->bool)->(A->bool)) n w | w IN W}`
              MP_TAC THENL
             [ASM_REWRITE_TAC[];
              REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]]];
          REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[SKOLEM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `mn:num->(A->bool)`
        (LABEL_TAC "mnprop")) THEN
      (* mn(SUC n) <= mn(n) in the well-order *)
      SUBGOAL_THEN
        `!k:num. (ord:(A->bool)->(A->bool)->bool)
           ((mn:num->(A->bool)) (SUC k)) (mn k)`
        (LABEL_TAC "mn_dec") THENL
       [GEN_TAC THEN
        (* By totality: ord mn(SUC k) mn(k) or ord mn(k) mn(SUC k) *)
        USE_THEN "wos" (MP_TAC o MATCH_MP WOSET_TOTAL) THEN
        USE_THEN "fldW" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "mnprop" (STRIP_ASSUME_TAC o SPEC `SUC k`) THEN
        USE_THEN "mnprop" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
        DISCH_THEN(MP_TAC o SPECL
          [`(mn:num->(A->bool)) (SUC k)`;
           `(mn:num->(A->bool)) k`]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[IN]; ALL_TAC] THEN
        DISCH_THEN(DISJ_CASES_THEN2
          (fun th -> ACCEPT_TAC th)
          ASSUME_TAC) THEN
        (* Case: ord mn(k) mn(SUC k) *)
        ASM_CASES_TAC
          `(mn:num->(A->bool)) k = mn (SUC k)` THENL
         [(* Equal: use reflexivity *)
          USE_THEN "wos" (MP_TAC o MATCH_MP WOSET_REFL) THEN
          USE_THEN "fldW" (fun th -> REWRITE_TAC[th]) THEN
          ASM_MESON_TAC[IN];
          (* Distinct: derive contradiction via Csub_strong *)
          SUBGOAL_THEN
            `~((x:A) IN (C:num->(A->bool)->(A->bool)) k
              ((mn:num->(A->bool)) k))`
            (fun th -> ASM_MESON_TAC[th]) THEN
          USE_THEN "Csub_strong"
            (MP_TAC o SPECL [`k:num`;
              `(mn:num->(A->bool)) (SUC k)`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
          DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
          REWRITE_TAC[NOT_EXISTS_THM;
            TAUT `~(p /\ q) <=> p ==> ~q`] THEN
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      (* Range {mn k | k} has a least element by WOSET_WELL *)
      USE_THEN "wos"
        (MP_TAC o CONJUNCT2 o REWRITE_RULE[WOSET]) THEN
      USE_THEN "fldW" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(MP_TAC o SPEC
        `{(mn:num->(A->bool)) k | k IN (:num)}`) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN
          X_GEN_TAC `z:A->bool` THEN
          DISCH_THEN(X_CHOOSE_THEN `kk:num` SUBST1_TAC) THEN
          USE_THEN "mnprop" (STRIP_ASSUME_TAC o SPEC `kk:num`) THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_UNIV] THEN
          EXISTS_TAC `(mn:num->(A->bool)) 0` THEN
          EXISTS_TAC `0` THEN REWRITE_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `w_min:A->bool` MP_TAC) THEN
      DISCH_THEN(fun th ->
        let eq_th = CONJUNCT1 th and min_th = CONJUNCT2 th in
        X_CHOOSE_THEN `n0:num`
          (fun eq -> SUBST_ALL_TAC eq THEN
                     ASSUME_TAC(REWRITE_RULE[eq] min_th)) eq_th) THEN
      (* mn(n0) is the least in the range, so mn(n0+1) = mn(n0) *)
      SUBGOAL_THEN
        `(mn:num->(A->bool)) (SUC n0) = mn n0`
        (LABEL_TAC "mn_stab") THENL
       [MP_TAC(MATCH_MP WOSET_ANTISYM
          (ASSUME `woset(ord:(A->bool)->(A->bool)->bool)`)) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        CONJ_TAC THENL
         [USE_THEN "mn_dec" (ACCEPT_TAC o SPEC `n0:num`);
          FIRST_X_ASSUM(MP_TAC o SPEC
            `(mn:num->(A->bool)) (SUC n0)`) THEN
          ANTS_TAC THENL
           [EXISTS_TAC `SUC n0` THEN REWRITE_TAC[];
            REWRITE_TAC[]]];
        ALL_TAC] THEN
      (* Now show x IN VV(SUC n0)(mn(n0)) *)
      EXISTS_TAC `n0:num` THEN
      EXISTS_TAC `(mn:num->(A->bool)) n0` THEN
      USE_THEN "mnprop" (STRIP_ASSUME_TAC o SPEC `n0:num`) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "VV" THEN REWRITE_TAC[IN_DIFF] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      REWRITE_TAC[NOT_EXISTS_THM;
        TAUT `~(p /\ q) <=> p ==> ~q`] THEN
      X_GEN_TAC `s:A->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN
      (* Need: x NOT IN C(SUC n0)(v) *)
      GEN_REWRITE_TAC I [TAUT `~p <=> (p ==> F)`] THEN
      DISCH_TAC THEN
      (* v IN {w | x IN C(SUC n0)(w)}, mn(SUC n0) is least *)
      USE_THEN "mnprop" (MP_TAC o SPEC `SUC n0`) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (K ALL_TAC)
          (MP_TAC o SPEC `v:A->bool`))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      (* ord mn(SUC n0) v, i.e., ord mn(n0) v *)
      USE_THEN "mn_stab" (fun th -> REWRITE_TAC[th]) THEN
      GEN_REWRITE_TAC I [TAUT `~p <=> (p ==> F)`] THEN
      DISCH_THEN ASSUME_TAC THEN
      (* Since v != mn(n0) and ord mn(n0) v *)
      (* Csub_strong: C(SUC n0)(v) SUBSET v DIFF UNIONS{...} *)
      USE_THEN "Csub_strong"
        (MP_TAC o SPECL [`n0:num`; `v:A->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    (* Step 7: Apply CP to the cover {VV (SUC n) w} to get cc *)
    MP_TAC(ISPECL [`top:A topology`;
      `{(VV:num->(A->bool)->(A->bool)) (SUC n) (w:A->bool) |
        n IN (:num) /\ w IN W}`]
      CP_INDEXED_CLOSED_COVER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [USE_THEN "cp" ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN
        X_GEN_TAC `nn:num` THEN X_GEN_TAC `ww:A->bool` THEN
        DISCH_THEN(fun wW ->
          USE_THEN "Vopen" (fun vth ->
            ACCEPT_TAC(MP (SPECL [`SUC nn`; `ww:A->bool`] vth) wW)));
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
          REPEAT STRIP_TAC THEN EXPAND_TAC "VV" THEN
          REWRITE_TAC[SUBSET_DIFF];
          REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
          USE_THEN "Vcover" (MP_TAC o SPEC `x:A`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `n0:num`
            (X_CHOOSE_THEN `w0:A->bool` STRIP_ASSUME_TAC)) THEN
          REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
          EXISTS_TAC `(VV:num->(A->bool)->(A->bool)) (SUC n0) w0` THEN
          CONJ_TAC THENL
           [MAP_EVERY EXISTS_TAC [`n0:num`; `w0:A->bool`] THEN
            ASM_REWRITE_TAC[IN_UNIV]; ASM_REWRITE_TAC[]]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:(A->bool)->(A->bool)`
      (CONJUNCTS_THEN2 (LABEL_TAC "cccl")
       (CONJUNCTS_THEN2 (LABEL_TAC "ccsub")
        (CONJUNCTS_THEN2 (LABEL_TAC "cccov") (LABEL_TAC "cccp"))))) THEN
    (* Step 8: For each n, apply Dowker *)
    SUBGOAL_THEN
      `!n:num. ?EE:(A->bool)->(A->bool).
         (!w:A->bool. w IN W ==> open_in top (EE w)) /\
         (!w:A->bool. w IN W ==>
            cc ((VV:num->(A->bool)->(A->bool)) (SUC n) w) SUBSET EE w) /\
         (!w:A->bool. w IN W ==> EE w SUBSET VV (SUC n) w) /\
         locally_finite_in top {EE w | w IN W}`
      (LABEL_TAC "dowker_all") THENL
     [X_GEN_TAC `nn:num` THEN
      MP_TAC(ISPECL
        [`top:A topology`; `W:(A->bool)->bool`;
         `\(w:A->bool). (VV:num->(A->bool)->(A->bool)) (SUC nn) w`;
         `\(w:A->bool). (cc:(A->bool)->(A->bool))
            ((VV:num->(A->bool)->(A->bool)) (SUC nn) w)`]
        DOWKER_DISCRETE_EXPANSION) THEN
      REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> MATCH_MP_TAC th THEN
        CONJ_TAC THENL [USE_THEN "norm" ACCEPT_TAC; ALL_TAC] THEN
        CONJ_TAC THENL
         [X_GEN_TAC `k:A->bool` THEN
          DISCH_THEN(fun kW ->
            USE_THEN "Vopen" (fun th ->
              ACCEPT_TAC(MP (SPECL [`SUC nn`; `k:A->bool`] th) kW)));
          ALL_TAC] THEN
        CONJ_TAC THENL
         [(* pairwise disjoint *)
          REWRITE_TAC[pairwise; DISJOINT] THEN
          MAP_EVERY X_GEN_TAC [`a:A->bool`; `b:A->bool`] THEN
          DISCH_THEN(fun h ->
            USE_THEN "Vpd" (fun vpd ->
              ACCEPT_TAC(MP (SPECL [`SUC nn`; `a:A->bool`; `b:A->bool`]
                vpd) h)));
          ALL_TAC] THEN
        CONJ_TAC THENL
         [(* cc subset VV *)
          X_GEN_TAC `k:A->bool` THEN DISCH_TAC THEN
          USE_THEN "ccsub" (MP_TAC o SPEC
            `(VV:num->(A->bool)->(A->bool)) (SUC nn) k`) THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          ANTS_TAC THENL
           [MAP_EVERY EXISTS_TAC [`nn:num`; `k:A->bool`] THEN
            REWRITE_TAC[IN_UNIV] THEN FIRST_ASSUM ACCEPT_TAC;
            REWRITE_TAC[]];
          ALL_TAC] THEN
        (* closed *)
        SUBGOAL_THEN
          `UNIONS {(cc:(A->bool)->(A->bool))
             ((VV:num->(A->bool)->(A->bool)) (SUC nn) k) |
             k IN W} =
           UNIONS {cc u | u IN {VV (SUC nn) w | w IN W}}`
          SUBST1_TAC THENL
         [AP_TERM_TAC THEN SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "cccp" MATCH_MP_TAC THEN
        REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `w':A->bool` THEN DISCH_TAC THEN
        REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`nn:num`; `w':A->bool`] THEN
        REWRITE_TAC[IN_UNIV] THEN FIRST_ASSUM ACCEPT_TAC);
      ALL_TAC] THEN
    (* Skolemize *)
    USE_THEN "dowker_all" (MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `EE:num->(A->bool)->(A->bool)`
      (LABEL_TAC "Eprop")) THEN
    (* Step 9: Define R and prove all four properties *)
    EXISTS_TAC
      `UNIONS {{(EE:num->(A->bool)->(A->bool)) n w | w IN W} |
               n IN (:num)}` THEN
    CONJ_TAC THENL
     [(* open_in: each r IN R is open *)
      X_GEN_TAC `r:A->bool` THEN DISCH_TAC THEN
      POP_ASSUM(MP_TAC o REWRITE_RULE[IN_UNIONS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `F':(A->bool)->bool`
        (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      GEN_REWRITE_TAC LAND_CONV [IN_ELIM_THM] THEN
      REWRITE_TAC[IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `nn:num` SUBST_ALL_TAC) THEN
      POP_ASSUM(STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
      USE_THEN "Eprop" (MP_TAC o SPEC `nn:num`) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [(* UNIONS = topspace *)
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [(* SUBSET topspace *)
        REWRITE_TAC[UNIONS_SUBSET] THEN
        X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
        POP_ASSUM(MP_TAC o REWRITE_RULE[IN_UNIONS]) THEN
        DISCH_THEN(X_CHOOSE_THEN `F':(A->bool)->bool`
          (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
        GEN_REWRITE_TAC LAND_CONV [IN_ELIM_THM] THEN
        REWRITE_TAC[IN_UNIV] THEN
        DISCH_THEN(X_CHOOSE_THEN `nn:num` SUBST_ALL_TAC) THEN
        POP_ASSUM(fun th ->
          let th' = BETA_RULE(GEN_REWRITE_RULE I [IN_ELIM_THM] th) in
          X_CHOOSE_THEN `w':A->bool`
            (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) th') THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `(VV:num->(A->bool)->(A->bool)) (SUC nn) w'` THEN
        CONJ_TAC THENL
         [USE_THEN "Eprop" (fun th ->
            MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2
              (SPEC `nn:num` th))))) THEN
          ASM_REWRITE_TAC[];
          EXPAND_TAC "VV" THEN REWRITE_TAC[SUBSET_DIFF]];
        (* topspace SUBSET *)
        REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        REWRITE_TAC[IN_UNIONS] THEN
        SUBGOAL_THEN
          `(x:A) IN UNIONS {(cc:(A->bool)->(A->bool)) u |
             u IN {(VV:num->(A->bool)->(A->bool)) (SUC n) w |
               n IN (:num) /\ w IN W}}`
          MP_TAC THENL
         [USE_THEN "cccov" (fun th -> REWRITE_TAC[th]) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
        STRIP_TAC THEN
        EXISTS_TAC `(EE:num->(A->bool)->(A->bool)) n w` THEN
        CONJ_TAC THENL
         [EXISTS_TAC
           `{(EE:num->(A->bool)->(A->bool)) n w'' | w'' IN W}` THEN
          CONJ_TAC THENL
           [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
            EXISTS_TAC `n:num` THEN REWRITE_TAC[];
            REWRITE_TAC[IN_ELIM_THM] THEN
            EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[]];
          (* x IN EE n w: substitute t=cc u, u=VV(SUC n)w *)
          FIRST_X_ASSUM SUBST_ALL_TAC THEN
          FIRST_X_ASSUM SUBST_ALL_TAC THEN
          (* now x IN cc(VV(SUC n) w) is in assumptions *)
          USE_THEN "Eprop" (fun th ->
            let th_n = SPEC `n:num` th in
            let th_sub = CONJUNCT1(CONJUNCT2 th_n) in
            MP_TAC(SPEC `w:A->bool` th_sub)) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[SUBSET] THEN
          DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
          ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [(* closure containment *)
      X_GEN_TAC `r:A->bool` THEN DISCH_TAC THEN
      POP_ASSUM(MP_TAC o REWRITE_RULE[IN_UNIONS]) THEN
      DISCH_THEN(X_CHOOSE_THEN `F':(A->bool)->bool`
        (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      GEN_REWRITE_TAC LAND_CONV [IN_ELIM_THM] THEN
      REWRITE_TAC[IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `nn:num` SUBST_ALL_TAC) THEN
      POP_ASSUM(fun th ->
        let th' = BETA_RULE(GEN_REWRITE_RULE I [IN_ELIM_THM] th) in
        X_CHOOSE_THEN `ww:A->bool`
          (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) th') THEN
      (* Now r = EE nn ww with ww IN W *)
      SUBGOAL_THEN
        `(EE:num->(A->bool)->(A->bool)) nn ww SUBSET ww`
        ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `(VV:num->(A->bool)->(A->bool)) (SUC nn) ww` THEN
        CONJ_TAC THENL
         [USE_THEN "Eprop" (fun th ->
            MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2
              (SPEC `nn:num` th))))) THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC
            `(C:num->(A->bool)->(A->bool)) (SUC nn) ww` THEN
          CONJ_TAC THENL
           [USE_THEN "VsubC" MATCH_MP_TAC THEN
            ASM_REWRITE_TAC[];
            USE_THEN "Cvalid" (fun th ->
              MATCH_MP_TAC(CONJUNCT1(CONJUNCT2
                (SPEC `SUC nn` th)))) THEN
            ASM_REWRITE_TAC[]]];
        ALL_TAC] THEN
      SUBGOAL_THEN
        `?u:A->bool. u IN U /\
           top closure_of (ww:A->bool) SUBSET u`
        STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `ww:A->bool`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `top closure_of (ww:A->bool)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSURE_OF_MONO THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    (* sigma-LF *)
    REWRITE_TAC[sigma_locally_finite_in] THEN
    EXISTS_TAC
      `\nn:num. {(EE:num->(A->bool)->(A->bool)) nn w | w IN W}` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `nn:num` THEN REWRITE_TAC[] THEN
      USE_THEN "Eprop" (fun th ->
        ACCEPT_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2
          (SPEC `nn:num` th)))));
      REWRITE_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `U:(A->bool)->bool`; `R:(A->bool)->bool`]
      CLF_OPEN_CLOSURE_IMP_LF_CLOSED) THEN
    ASM_REWRITE_TAC[]]);;

(* Michael's biconditional characterization: for regular spaces,
   paracompact iff every open cover has a closure-preserving closed
   refinement (i.e., unions of arbitrary subcollections are closed). *)

let MICHAEL_PARACOMPACT_EQ = prove
 (`!top:A topology.
        regular_space top
        ==> (paracompact_space top <=>
             !U. (!u. u IN U ==> open_in top u) /\ UNIONS U = topspace top
                 ==> ?V. (!v. v IN V ==> closed_in top v) /\
                         UNIONS V = topspace top /\
                         (!v. v IN V ==> ?u. u IN U /\ v SUBSET u) /\
                         (!W. W SUBSET V ==> closed_in top (UNIONS W)))`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [(* Forward: paracompact ==> CP closed refinement.
      Get LF closed refinement, then LF closed ==> closure-preserving. *)
    DISCH_TAC THEN
    X_GEN_TAC `U:(A->bool)->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PARACOMPACT_SPACE_EQ_CLOSED_REFINEMENT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `U:(A->bool)->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `V:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `W:(A->bool)->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC CLOSED_IN_LOCALLY_FINITE_UNIONS THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC LOCALLY_FINITE_IN_SUBSET THEN
    EXISTS_TAC `V:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    (* Backward: CP closed refinement ==> paracompact.
       Directly from MICHAEL_PARACOMPACT. *)
    DISCH_TAC THEN MATCH_MP_TAC MICHAEL_PARACOMPACT THEN
    ASM_REWRITE_TAC[]]);;

(* Sharper closed map image theorem: paracompact Hausdorff is preserved
   by closed continuous surjections (not just perfect maps).
   Uses MICHAEL_PARACOMPACT and CP_IMPLIES_NORMAL_SPACE. *)

let PARACOMPACT_SPACE_CLOSED_MAP_IMAGE = prove
 (`!top top' (f:A->B).
        paracompact_space top /\ hausdorff_space top /\
        continuous_map(top,top') f /\
        closed_map(top,top') f /\
        IMAGE f (topspace top) = topspace top'
        ==> paracompact_space top'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: regular_space top *)
  SUBGOAL_THEN `regular_space (top:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PARACOMPACT_HAUSDORFF_IMP_REGULAR_SPACE]; ALL_TAC] THEN
  (* Step 2: Every open cover of Y has a CP closed refinement *)
  SUBGOAL_THEN
    `!U:(B->bool)->bool.
         (!u:B->bool. u IN U ==> open_in top' u) /\
         UNIONS U = topspace top'
         ==> ?V:(B->bool)->bool.
                 (!v:B->bool. v IN V ==> closed_in top' v) /\
                 UNIONS V = topspace top' /\
                 (!v:B->bool. v IN V ==> ?u:B->bool. u IN U /\ v SUBSET u) /\
                 (!W:(B->bool)->bool. W SUBSET V ==> closed_in top' (UNIONS W))`
    (LABEL_TAC "cp'") THENL
   [X_GEN_TAC `U:(B->bool)->bool` THEN STRIP_TAC THEN
    (* Get LF closed refinement of pullback cover in X *)
    FIRST_ASSUM(MP_TAC o MATCH_MP PARACOMPACT_SPACE_EQ_CLOSED_REFINEMENT) THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC
      `{({x | x IN topspace top /\ (f:A->B) x IN u}) | u IN U}`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `u:B->bool` THEN
        DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
        EXISTS_TAC `top':B topology` THEN ASM_MESON_TAC[];
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; SUBSET;
                       IN_ELIM_THM] THEN MESON_TAC[];
          REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
          X_GEN_TAC `x:A` THEN DISCH_TAC THEN
          SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
           [ASM_MESON_TAC[continuous_map]; ALL_TAC] THEN
          SUBGOAL_THEN `(f:A->B) x IN UNIONS U` MP_TAC THENL
           [ASM_MESON_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
          DISCH_THEN(X_CHOOSE_THEN `u:B->bool` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `{x:A | x IN topspace top /\ (f:A->B) x IN u}` THEN
          REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:(A->bool)->bool`
      (CONJUNCTS_THEN2 (LABEL_TAC "Kclosed")
        (CONJUNCTS_THEN2 (LABEL_TAC "Kcov")
          (CONJUNCTS_THEN2 (LABEL_TAC "Kref") (LABEL_TAC "Klf"))))) THEN
    (* Push forward K via f *)
    EXISTS_TAC `{IMAGE (f:A->B) k | k IN K}` THEN
    REPEAT CONJ_TAC THENL
     [(* Each IMAGE f k is closed in Y *)
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `k:A->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [closed_map]) THEN
      DISCH_THEN(MP_TAC o SPEC `k:A->bool`) THEN
      ASM_MESON_TAC[];
      (* Covers Y *)
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `k:A->bool` THEN DISCH_TAC THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (f:A->B) (topspace top)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN
          ASM_MESON_TAC[closed_in; SUBSET];
          ASM SET_TAC[]];
        REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `y:B` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(y:B) IN IMAGE (f:A->B) (topspace top)` MP_TAC THENL
         [ASM SET_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(x:A) IN UNIONS K` MP_TAC THENL
         [ASM SET_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
        DISCH_THEN(X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `IMAGE (f:A->B) k` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]];
      (* Refines U *)
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `k0:A->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN
        `?u0:B->bool. u0 IN U /\
                       (k0:A->bool) SUBSET
                       {x | x IN topspace top /\ (f:A->B) x IN u0}`
        STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN
          `?preimg:(A->bool).
             preimg IN
             {{x | x IN topspace top /\ (f:A->B) x IN u} |
              (u:B->bool) IN U} /\
             (k0:A->bool) SUBSET preimg` STRIP_ASSUME_TAC THENL
         [USE_THEN "Kref" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
        DISCH_THEN(X_CHOOSE_THEN `u0':B->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `u0':B->bool` THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `u0:B->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN
      X_GEN_TAC `y:B` THEN
      DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a:A) IN {x | x IN topspace top /\ (f:A->B) x IN u0}`
        MP_TAC THENL [ASM SET_TAC[]; SIMP_TAC[IN_ELIM_THM]];
      (* Closure-preserving: every sub-union is closed *)
      X_GEN_TAC `SS:(B->bool)->bool` THEN DISCH_TAC THEN
      ABBREV_TAC `S0 = {k:A->bool | k IN K /\ IMAGE (f:A->B) k IN SS}` THEN
      SUBGOAL_THEN `(S0:(A->bool)->bool) SUBSET K` ASSUME_TAC THENL
       [EXPAND_TAC "S0" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `SS = {IMAGE (f:A->B) k | k IN S0}` ASSUME_TAC THENL
       [EXPAND_TAC "S0" THEN
        ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `s:B->bool` THEN EQ_TAC THENL
         [DISCH_TAC THEN
          UNDISCH_TAC `SS SUBSET {IMAGE (f:A->B) k | k IN K}` THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          DISCH_THEN(MP_TAC o SPEC `s:B->bool`) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(X_CHOOSE_THEN `kk:A->bool` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `kk:A->bool` THEN ASM_MESON_TAC[];
          DISCH_THEN(X_CHOOSE_THEN `kk:A->bool` STRIP_ASSUME_TAC) THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      (* UNIONS {IMAGE f k | k IN S0} = IMAGE f (UNIONS S0) *)
      SUBGOAL_THEN `UNIONS {IMAGE (f:A->B) k | k IN S0} =
                    IMAGE f (UNIONS S0)` SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[EXTENSION] THEN
        X_GEN_TAC `bb:B` THEN
        REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
        EQ_TAC THENL
         [DISCH_THEN(X_CHOOSE_THEN `t0:B->bool` MP_TAC) THEN
          DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
          DISCH_THEN(X_CHOOSE_THEN `k0':A->bool` STRIP_ASSUME_TAC) THEN
          UNDISCH_TAC `(bb:B) IN t0` THEN
          ASM_REWRITE_TAC[IN_IMAGE] THEN
          DISCH_THEN(X_CHOOSE_THEN `a0:A` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `a0:A` THEN ASM_REWRITE_TAC[] THEN
          EXISTS_TAC `k0':A->bool` THEN ASM_REWRITE_TAC[];
          DISCH_THEN(X_CHOOSE_THEN `a0:A` MP_TAC) THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          DISCH_THEN(X_CHOOSE_THEN `k0':A->bool` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `IMAGE (f:A->B) k0'` THEN
          CONJ_TAC THENL
           [EXISTS_TAC `k0':A->bool` THEN ASM_REWRITE_TAC[];
            ASM_REWRITE_TAC[IN_IMAGE] THEN
            EXISTS_TAC `a0:A` THEN ASM_REWRITE_TAC[]]];
        ALL_TAC] THEN
      (* UNIONS S0 is closed in X *)
      SUBGOAL_THEN `closed_in top (UNIONS S0:A->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC CLOSED_IN_LOCALLY_FINITE_UNIONS THEN CONJ_TAC THENL
         [REPEAT STRIP_TAC THEN USE_THEN "Kclosed" MATCH_MP_TAC THEN
          ASM SET_TAC[];
          MATCH_MP_TAC LOCALLY_FINITE_IN_SUBSET THEN
          EXISTS_TAC `K:(A->bool)->bool` THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      (* IMAGE f (closed) is closed *)
      UNDISCH_TAC `closed_map(top:A topology,top':B topology) f` THEN
      REWRITE_TAC[closed_map] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* Step 3: CP -> normal *)
  SUBGOAL_THEN `normal_space (top':B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC CP_IMPLIES_NORMAL_SPACE THEN
    USE_THEN "cp'" ACCEPT_TAC;
    ALL_TAC] THEN
  (* Step 4: t1_space top' via closed map image *)
  SUBGOAL_THEN `t1_space (top':B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC T1_SPACE_CLOSED_MAP_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`f:A->B`; `top:A topology`] THEN
    ASM_MESON_TAC[HAUSDORFF_IMP_T1_SPACE];
    ALL_TAC] THEN
  (* Step 5: normal + T1 -> regular *)
  SUBGOAL_THEN `regular_space (top':B topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORMAL_T1_IMP_REGULAR_SPACE]; ALL_TAC] THEN
  (* Step 6: Apply MICHAEL_PARACOMPACT *)
  MATCH_MP_TAC MICHAEL_PARACOMPACT THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    USE_THEN "cp'" ACCEPT_TAC]);;
