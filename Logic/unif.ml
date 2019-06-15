(* ========================================================================= *)
(* Yet another formalized unification algorithm.                             *)
(* ========================================================================= *)

let LEFT_AND_EX_THM = prove
  (`!P Q l. EX P l /\ Q <=> EX (\x. P x /\ Q) l`,
   GEN_TAC THEN GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX] THEN CONV_TAC TAUT);;

let EX_ADHOC = prove
 (`!l. (!x. ~(P x) ==> (Q x <=> R x)) ==> (~EX P l ==> (EX Q l <=> EX R l))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[EX] THEN ASM_MESON_TAC[]);;

let ALL_ADHOC = prove
 (`!l. ALL (\x. f x = g x) l ==> (EX f l <=> EX g l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; EX] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Yet more wellfoundedness lemmas.                                          *)
(* ------------------------------------------------------------------------- *)

let WF_FINITE_LEMMA = prove
 (`!(<<) s. FINITE s /\
            (!x:A. ~(TC(<<) x x)) /\ (!x y. x << y ==> y IN s)
            ==> WF(<<)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WF_DCHAIN] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:num->A`) THEN
  SUBGOAL_THEN `!n. (u:num->A)(n) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:num->A`; `s:A->bool`] FINITE_IMAGE_INJ) THEN
  REWRITE_TAC[ASSUME `FINITE(s:A->bool)`; NOT_IMP] THEN
  SUBGOAL_THEN `{n | (u:num->A)(n) IN s} = UNIV:num->bool` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[num_INFINITE; GSYM INFINITE] THEN
  SUBGOAL_THEN `!m n. m < n ==> TC(<<) ((u:num->A) n) (u m)`
   (fun th -> ASM_MESON_TAC[th; LT_CASES]) THEN
  SIMP_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:num` THEN GEN_TAC THEN X_GEN_TAC `d:num` THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `!d. RTC(<<) ((u:num->A)(n + d))(u n) ` MP_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; RTC_REFL] THEN
    ASM_MESON_TAC[RTC_TRANS; RTC_INC];
    REWRITE_TAC[RTC; RC_CASES] THEN ASM_MESON_TAC[TC_INC; TC_CASES_R]]);;

let TC_REV = prove
 (`!x:A y. TC (\u v. R v u) x y <=> TC R y x`,
  REWRITE_TAC[TAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`; FORALL_AND_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[SWAP_FORALL_THM]] THEN
  MATCH_MP_TAC TC_INDUCT THEN SIMP_TAC[TC_INC] THEN MESON_TAC[TC_TRANS]);;

let WF_DISJ = prove
 (`WF(R) /\ WF(\x y. ?z. S x z /\ RTC(R) z y) ==> WF(\x:A y. R x y \/ S x y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[WF] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `P:A->bool` THEN
  MATCH_MP_TAC(TAUT `(b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (snd(EQ_IMP_RULE(SPEC_ALL WF_TC)))) THEN
  REWRITE_TAC[WF] THEN DISCH_THEN(MP_TAC o SPEC `\y:A. P(y) /\ TC R y a`) THEN
  REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[RTC; RC_CASES]) THEN
  ASM_MESON_TAC[TC_INC; TC_TRANS]);;

let WF_ALTERNATION = prove
 (`WF(\x y. R x y \/ S x y) /\ (!x y z. ~(P x y /\ P y z))
   ==> WF(\(x1:A,y1) (x2,y2). S x1 x2 /\ S y1 y2 \/
                              R x1 x2 /\ (y1 = y2) \/
                              P x2 y2 /\ (x1 = y2) /\ (x2 = y1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WF] THEN X_GEN_TAC `s:A#A->bool` THEN
  REWRITE_TAC[EXISTS_PAIR_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [WF]) THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. ?y:A. s(x,y) \/ s(y,x)`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:A` ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [ASM_CASES_TAC `(P:A->A->bool) a b0` THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_CASES_TAC `(s:A#A->bool)(b0,a)` THENL
     [ALL_TAC;
      MAP_EVERY EXISTS_TAC [`a:A`; `b0:A`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
    ASM_CASES_TAC `?y:A. R y (b0:A) /\ s(y,a:A)` THENL
     [ALL_TAC;
      MAP_EVERY EXISTS_TAC [`b0:A`; `a:A`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [WF]) THEN
    DISCH_THEN(MP_TAC o SPEC `\y:A. s(y,a:A):bool`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`b:A`; `a:A`] THEN ASM_MESON_TAC[];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [WF]) THEN
    DISCH_THEN(MP_TAC o SPEC `\y:A. s(y,a:A):bool`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(P:A->A->bool) b a /\ s(a,b)` THENL
     [MAP_EVERY EXISTS_TAC [`a:A`; `b:A`];
      MAP_EVERY EXISTS_TAC [`b:A`; `a:A`]] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MULTISET_FILTEREQ = prove
 (`multiplicity (multiset (\x:A. LENGTH (FILTER ((=) x) l))) a =
        LENGTH (FILTER ((=) a) l)`,
  MP_TAC(ISPEC `\x:A. LENGTH (FILTER ((=) x) l)`
   (CONJUNCT2 multiset_tybij)) THEN
  MATCH_MP_TAC(TAUT `(b ==> c) /\ a ==> ((a <=> b) ==> c)`) THEN
  SIMP_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{a:A | MEM a l}` THEN CONJ_TAC THENL
   [SPEC_TAC(`l:(A)list`,`l:(A)list`) THEN LIST_INDUCT_TAC THENL
     [SUBGOAL_THEN `{a:A | MEM a []} = EMPTY`
        (fun th -> REWRITE_TAC[th; FINITE_RULES]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; MEM; NOT_IN_EMPTY];
      SUBGOAL_THEN `{a:A | MEM a (CONS h t)} = h INSERT {a | MEM a t}`
        (fun th -> ASM_SIMP_TAC[th; FINITE_RULES]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; MEM] THEN
      REWRITE_TAC[DISJ_ACI]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    SPEC_TAC(`l:(A)list`,`l:(A)list`) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[FILTER; LENGTH; MEM] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; MEM]]);;

let WF_MULTIZIP = prove
 (`WF(R)
   ==> WF(\l1 l2. ?h:A t l0.
             (l2 = CONS h t) /\ (l1 = APPEND l0 t) /\
             (!k. MEM k l0 ==> R k h))`,
  let lemma = INST_TYPE [`:(A)list`,`:A`] WF_MEASURE_GEN in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\l. multiset(\x:A. LENGTH (FILTER ((=) x) l))` o
                      MATCH_MP lemma o MATCH_MP MORDER_WF) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
                        WF_SUBSET) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[morder; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `l:(A)list`; `m:(A)list`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN DISCH_TAC THEN
  EXISTS_TAC `multiset(\x:A. LENGTH (FILTER ((=) x) l))` THEN
  EXISTS_TAC `a:A` THEN
  EXISTS_TAC `multiset(\x:A. LENGTH (FILTER ((=) x) m))` THEN
  REWRITE_TAC[mmember; MEXTENSION; MULTISET_FILTEREQ; MUNION; MSING] THEN
  REWRITE_TAC[FILTER_APPEND; LENGTH_APPEND; LENGTH; FILTER; ADD_AC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[LENGTH; ADD1; ADD_AC; ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:A l. ~(LENGTH (FILTER ((=) a) l) = 0) ==> MEM a l`
   (fun th -> ASM_MESON_TAC[th]) THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; LENGTH; MEM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; MEM]);;

let WF_MEASURE_OR_NONINC = prove
 (`!R (m:A->num).
        WF(R) /\ (!x y. R x y ==> m x <= m y)
        ==> WF(\x y. MEASURE m x y \/ R x y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WF] THEN
  X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `m:A->num` WF_MEASURE) THEN REWRITE_TAC[WF; MEASURE] THEN
  DISCH_THEN(MP_TAC o SPEC `P:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `?y. (R:A->A->bool) y a /\ P y` THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SPEC `\y. TC (R:A->A->bool) y a /\ P y` o
              GEN_REWRITE_RULE I [WF]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[TC_INC]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(m:A->num)(b) <= m(a)`
   (fun th -> ASM_MESON_TAC[th; TC_INC; TC_TRANS; LTE_TRANS]) THEN
  UNDISCH_TAC `TC R b (a:A)` THEN
  MAP_EVERY SPEC_TAC [`a:A`,`a:A`; `b:A`,`b:A`] THEN
  MATCH_MP_TAC TC_INDUCT THEN ASM_REWRITE_TAC[LE_TRANS]);;

let WF_PROJ_EQ = prove
 (`(!x. P x ==> WF(R x))
   ==> WF(\(x',y') (x:A,y:B). P(x) /\ (x' = x) /\ R x y' y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WF_DCHAIN] THEN
  DISCH_THEN(X_CHOOSE_TAC `s:num->A#B`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `FST((s:num->A#B) 0)`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN
  SUBST1_TAC(SYM(ISPEC `(s:num->A#B) 0` PAIR)) THEN
  SUBST1_TAC(SYM(ISPEC `(s:num->A#B) (SUC 0)` PAIR)) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  REWRITE_TAC[WF_DCHAIN] THEN
  EXISTS_TAC `SND o (s:num->A#B)` THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `FST((s:num->A#B) 0) = FST(s n)` SUBST1_TAC THENL
   [SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `FST((s:num->A#B) n)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  SUBST1_TAC(SYM(ISPEC `(s:num->A#B) n` PAIR)) THEN
  SUBST1_TAC(SYM(ISPEC `(s:num->A#B) (SUC n)` PAIR)) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC[FST; SND]);;

(* ------------------------------------------------------------------------- *)
(* Definition of loop-freeness.                                              *)
(* ------------------------------------------------------------------------- *)

let OCC = new_definition
  `OCC env (x:num) y <=> ?t. MEM (x,t) env /\ y IN FVT(t)`;;

let LOOPFREE = new_definition
  `LOOPFREE env <=> !z. ~(TC (OCC env) z z)`;;

(* ------------------------------------------------------------------------- *)
(* Main preservation theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let LOOP_BREAK = prove
 (`!env x t u v.
        TC(OCC (CONS (x,t) env)) u v /\ ~(TC(OCC env) u v)
        ==> ?y. RTC(OCC env) u x /\ y IN FVT(t) /\ RTC(OCC env) y v`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ ~b ==> c <=> a ==> ~b ==> c`] THEN
  MATCH_MP_TAC TC_INDUCT_L THEN REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `OCC (CONS (x,t) env) u v` THEN
    REWRITE_TAC[OCC; MEM; PAIR_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[RTC_CASES]; ALL_TAC] THEN
    UNDISCH_TAC `~TC (OCC env) u v` THEN
    ONCE_REWRITE_TAC[TC_CASES_L] THEN REWRITE_TAC[OCC] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `TC (OCC env) u v` THENL
   [UNDISCH_TAC `OCC (CONS (x,t) env) v z` THEN
    REWRITE_TAC[OCC; MEM; PAIR_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC) THENL
     [REWRITE_TAC[RTC; RC_CASES] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~TC (OCC env) u z` THEN
     MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
    ONCE_REWRITE_TAC[TC_CASES_L] THEN DISJ2_TAC THEN
    REWRITE_TAC[OCC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_imp o concl) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `OCC (CONS (x,t) env) v z` THEN
  REWRITE_TAC[OCC; MEM; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC) THENL
   [REWRITE_TAC[RTC; RC_CASES] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[RTC_CASES_L; OCC]]);;

let LOOPFREE_PRESERVE = prove
 (`LOOPFREE env /\ ~(?y. y IN FVT(t) /\ RTC (OCC env) y x)
   ==> LOOPFREE (CONS (x,t) env)`,
  MESON_TAC[LOOPFREE; RTC_CASES; LOOP_BREAK]);;

let LOOPFREE_PRESERVE_EQ = prove
 (`LOOPFREE env
   ==> (LOOPFREE (CONS (x,t) env) = ~(?y. y IN FVT(t) /\ RTC (OCC env) y x))`,
  MATCH_MP_TAC(TAUT `(a /\ ~c ==> b) /\ (c ==> ~b) ==> (a ==> (b <=> ~c))`) THEN
  REWRITE_TAC[LOOPFREE_PRESERVE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LOOPFREE] THEN DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[TC_RTC_CASES_R] THEN
  EXISTS_TAC `y:num` THEN REWRITE_TAC[OCC; MEM; PAIR_EQ] THEN CONJ_TAC THENL
   [EXISTS_TAC `t:term` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `RTC (OCC env) y x` THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] RTC_MONO) THEN
    SIMP_TAC[OCC; MEM; PAIR_EQ] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* If existing env is loopfree, a naive algorithm works.                     *)
(* ------------------------------------------------------------------------- *)

let LOOPFREE_WF = prove
 (`!env. LOOPFREE env ==> WF(\x y. OCC env y x)`,
  REWRITE_TAC[LOOPFREE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WF_FINITE_LEMMA THEN
  EXISTS_TAC `set_of_list (MAP FST (env:(num#term)list))` THEN
  ASM_REWRITE_TAC[FINITE_SET_OF_LIST] THEN
  ONCE_REWRITE_TAC[TC_REV] THEN
  CONV_TAC(DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[OCC] THEN
  SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; set_of_list; MEM; IN_INSERT] THEN
  ASM_MESON_TAC[FST]);;

let LOOPFREE_WF_TERM = prove
 (`!env. LOOPFREE(env) ==> WF(\s t. ?y. y IN FVT(t) /\ MEM (y,s) env)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LOOPFREE_WF) THEN
  REWRITE_TAC[WF_DCHAIN; OCC; TAUT `~a ==> ~b <=> b ==> a`; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->term` (X_CHOOSE_THEN `x:num->num`
        STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`x:num->num`; `\n. s(SUC n):term`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* This would be so much nicer with TFL...                                   *)
(* ------------------------------------------------------------------------- *)

let LOOPCHECK_EXISTS = prove
 (`!env x.
     LOOPFREE(env)
     ==> ?loopcheck. !t.
               loopcheck t <=>
                  ?y. y IN FVT(t) /\
                            ((y = x) \/ ?s. MEM (y,s) env /\ loopcheck s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WF_REC o MATCH_MP LOOPFREE_WF_TERM) THEN
  REWRITE_TAC[] THEN MESON_TAC[]);;

let loopcheck_raw =
  new_specification ["loopcheck"]
   (REWRITE_RULE[SKOLEM_THM; RIGHT_IMP_EXISTS_THM] LOOPCHECK_EXISTS);;

let loopcheck = prove
 (`!env x.
        LOOPFREE(env)
        ==> (!x y. loopcheck env x (V y) <=>
                   (y = x) \/ ?s. MEM (y,s) env /\ loopcheck env x s) /\
            (!f args. loopcheck env x (Fn f args) <=>
                   EX (loopcheck env x) args)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
     GEN_REWRITE_TAC LAND_CONV [MATCH_MP loopcheck_raw th]) THEN
  REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; UNWIND_THM2; IN_LIST_UNION] THEN
  REWRITE_TAC[LEFT_AND_EX_THM; EXISTS_EX; EX_MAP; o_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP loopcheck_raw th)]) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Prove that it does indeed work.                                           *)
(* ------------------------------------------------------------------------- *)

let LOOPCHECK = prove
 (`!env x t. LOOPFREE(env)
             ==> (loopcheck env x t <=> ~LOOPFREE (CONS (x,t) env))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `?y. y IN FVT t /\ RTC (OCC env) y x` THEN
  ASM_SIMP_TAC[LOOPFREE_PRESERVE_EQ] THEN SPEC_TAC(`t:term`,`t:term`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LOOPFREE_WF_TERM) THEN
  REWRITE_TAC[WF_IND] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `t:term` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP loopcheck_raw th]) THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[RTC_CASES_R] THEN
  ASM_CASES_TAC `x:num = y` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[OCC; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Final transformation to solved form. More non-TFL hell.                   *)
(* ------------------------------------------------------------------------- *)

let rightsubst = new_definition
  `rightsubst (x,t) (y:num,s) =
     y,termsubst (\z. if z = x then t else V(z)) s`;;

let SOLVE_EXISTS = prove
 (`?SOLVE. !pr. SOLVE pr =
                  if SND pr = [] then FST pr
                  else SOLVE (CONS (HD(SND pr))
                                   (MAP (rightsubst (HD(SND pr))) (FST pr)),
                              MAP (rightsubst (HD(SND pr))) (TL(SND pr)))`,
  let lemma = prove
   (`(if b then x else y) = (if ~b then y else x)`,
    BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]) in
  ONCE_REWRITE_TAC[lemma] THEN REWRITE_TAC[WF_REC_TAIL]);;

let SOLVEC_RAW = new_specification ["SOLVEC"] SOLVE_EXISTS;;

let SOLVE = new_definition
  `SOLVE sol uns = SOLVEC (sol,uns)`;;

let SOLVE = prove
 (`(!sol. SOLVE sol [] = sol) /\
   (!sol p oth. SOLVE sol (CONS p oth) =
                SOLVE (CONS p (MAP (rightsubst p) sol))
                      (MAP (rightsubst p) oth))`,
  REWRITE_TAC[SOLVE] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SOLVEC_RAW] THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL]);;

(* ------------------------------------------------------------------------- *)
(* Fact that the list gives no conflicting definitions.                      *)
(* ------------------------------------------------------------------------- *)

let CONFLICTFREE = new_definition
  `CONFLICTFREE l <=> !x. LENGTH (FILTER (\(y:num,s:term). y = x) l) <= 1`;;

(* ------------------------------------------------------------------------- *)
(* Solve step preserves loop-freeness.                                       *)
(* ------------------------------------------------------------------------- *)

let SOLVE_PRESERVES_LOOPFREE_LEMMA = prove
 (`!p oth x y.
        TC(OCC (MAP (rightsubst p) oth)) x y ==> TC(OCC (CONS p oth)) x y`,
  ONCE_REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `t:term`; `oth:(num#term)list`] THEN
  GEN_REWRITE_TAC (funpow 2 BINDER_CONV o RAND_CONV o funpow 2 RATOR_CONV)
    [GSYM TC_IDEMP] THEN
  MATCH_MP_TAC TC_MONO THEN MAP_EVERY X_GEN_TAC [`u:num`; `v:num`] THEN
  REWRITE_TAC[OCC; MEM_MAP; EXISTS_PAIR_THM; rightsubst; PAIR_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:term`; `y:num`; `s:term`] THEN STRIP_TAC THEN
  UNDISCH_TAC `v IN FVT p` THEN ASM_REWRITE_TAC[TERMSUBST_FVT] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `z:num` MP_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY] THENL
   [STRIP_TAC THEN MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC `x:num` THEN CONJ_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)] THEN
  MATCH_MP_TAC TC_INC THEN REWRITE_TAC[OCC] THEN ASM_MESON_TAC[MEM]);;

let SOLVE_PRESERVES_LOOPFREE = prove
 (`!p oth. LOOPFREE(CONS p oth) ==> LOOPFREE(MAP (rightsubst p) oth)`,
  REWRITE_TAC[LOOPFREE] THEN MESON_TAC[SOLVE_PRESERVES_LOOPFREE_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* ...and the absence of conflicts.                                          *)
(* ------------------------------------------------------------------------- *)

let SOLVE_PRESERVES_CONFLICTFREE_LEMMA = prove
 (`!p x. (\(y,s). y = x) o rightsubst p = (\(y,s). y = x)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM; rightsubst] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[EQ_SYM]);;

let SOLVE_PRESERVES_CONFLICTFREE = prove
 (`CONFLICTFREE(APPEND sol (CONS p oth))
   ==> CONFLICTFREE(APPEND (CONS p (MAP (rightsubst p) sol))
                           (MAP (rightsubst p) oth))`,
  REWRITE_TAC[CONFLICTFREE; FILTER_APPEND; FILTER; LENGTH_APPEND;
              FILTER_MAP; LENGTH_MAP] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; LENGTH_MAP] THEN
  REWRITE_TAC[SOLVE_PRESERVES_CONFLICTFREE_LEMMA] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* ...and preserves the invariant of removing free variables.                *)
(* ------------------------------------------------------------------------- *)

let SOLVE_PRESERVES_DEFREE = prove
 (`LOOPFREE(CONS p oth) /\
   (!x y s t. MEM (x,t) sol /\ MEM (y,s) (APPEND sol (CONS p oth))
              ==> ~(x IN FVT(s)))
   ==> (!x y s t. MEM (x,t) (CONS p (MAP (rightsubst p) sol)) /\
                  MEM (y,s) (APPEND (CONS p (MAP (rightsubst p) sol))
                                    (MAP (rightsubst p) oth))
                  ==> ~(x IN FVT(s)))`,
  ONCE_REWRITE_TAC[GSYM LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM LEFT_AND_EXISTS_THM] THEN
  SUBGOAL_THEN `!x. (?t. MEM (x,t) (CONS p (MAP (rightsubst p) sol))) <=>
                    (?t. MEM (x,t) (CONS p sol))`
    (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[MEM; EXISTS_OR_THM] THEN AP_TERM_TAC THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
    SUBST1_TAC(SYM(ISPEC `p:num#term` PAIR)) THEN
    PURE_REWRITE_TAC[rightsubst; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[MEM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THENL
   [UNDISCH_TAC
     `MEM (y,s)
       (APPEND (CONS (x,t) (MAP (rightsubst (x,t)) sol))
       (MAP (rightsubst (x,t)) oth))` THEN
    REWRITE_TAC[APPEND; GSYM MAP_APPEND] THEN
    REWRITE_TAC[MEM; MEM_MAP; PAIR_EQ] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (CONJUNCTS_THEN SUBST1_TAC) MP_TAC) THENL
     [ALL_TAC;
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
      SIMP_TAC[PAIR_EQ; rightsubst; TERMSUBST_FVT] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:num` (MP_TAC o CONJUNCT2)) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY]] THEN
    UNDISCH_TAC `LOOPFREE (CONS (x,t) oth)` THEN REWRITE_TAC[LOOPFREE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN DISCH_TAC THEN
    MATCH_MP_TAC TC_INC THEN REWRITE_TAC[OCC] THEN
    EXISTS_TAC `t:term` THEN ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
  UNDISCH_TAC
   `MEM (y,s)
        (APPEND (CONS p (MAP (rightsubst p) sol))
                (MAP (rightsubst p) oth))` THEN
  REWRITE_TAC[APPEND; MEM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[MEM; APPEND; MEM_APPEND] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MAP_APPEND; MEM_MAP; LEFT_IMP_EXISTS_THM;
              FORALL_PAIR_THM] THEN
  SUBST_ALL_TAC(SYM(ISPEC `p:num#term` PAIR)) THEN
  REWRITE_TAC[rightsubst; PAIR_EQ] THEN GEN_TAC THEN X_GEN_TAC `u:term` THEN
  MAP_EVERY ABBREV_TAC [`z = FST(p:num#term)`; `r = SND(p:num#term)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST1_TAC) THEN
  REWRITE_TAC[TERMSUBST_FVT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num` MP_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY] THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST_ALL_TAC o SYM))] THEN
  ASM_MESON_TAC[MEM_APPEND; MEM]);;

(* ------------------------------------------------------------------------- *)
(* ...and maintains exactly the same set of unifiers.                        *)
(* ------------------------------------------------------------------------- *)

let SOLVE_PRESERVES_UNIFIERS = prove
 (`(!x t. MEM (x,t) (APPEND sol (CONS p oth))
          ==> (i(x) = termsubst i t)) <=>
   (!x t. MEM (x,t) (APPEND (CONS p (MAP (rightsubst p) sol))
                            (MAP (rightsubst p) oth))
          ==> (i(x) = termsubst i t))`,
  let lemma = prove
   (`(!x t y s. P y s /\ (x = y) /\ (t = f s) ==> Q x t) <=>
     (!x t s. P x s ==> Q x (f s))`,
    MESON_TAC[]) in
  REWRITE_TAC[MEM_APPEND; MEM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [TAUT `a \/ b \/ c <=> b \/ a \/ c`] THEN
  REWRITE_TAC[GSYM DISJ_ASSOC; GSYM MEM_APPEND; GSYM MAP_APPEND] THEN
  SPEC_TAC(`APPEND sol (oth:(num#term)list)`,`l:(num#term)list`) THEN
  GEN_TAC THEN REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  SPEC_TAC(`p:num#term`,`p:num#term`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:num`; `s:term`] THEN
  SIMP_TAC[PAIR_EQ; GSYM LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  DISCH_TAC THEN SIMP_TAC[MEM_MAP; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[rightsubst; PAIR_EQ; lemma] THEN
  REWRITE_TAC[TERMSUBST_TERMSUBST; o_DEF] THEN
  SUBGOAL_THEN `(\x. termsubst i (if x = y then s else V x)) = i`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[termsubst]);;

(* ------------------------------------------------------------------------- *)
(* Hence it works.                                                           *)
(* ------------------------------------------------------------------------- *)

let SOLVE_WORKS_GENERAL = prove
 (`!n env sol. (LENGTH env = n) /\
               LOOPFREE(env) /\
               CONFLICTFREE(APPEND sol env) /\
               (!x y s t. MEM (x,t) sol /\ MEM (y,s) (APPEND sol env)
                          ==> ~(x IN FVT(s)))
               ==> CONFLICTFREE(SOLVE sol env) /\
                   (!i. (!x t. MEM (x,t) (APPEND sol env)
                               ==> (i x = termsubst i t)) <=>
                        (!x t. MEM (x,t) (SOLVE sol env)
                               ==> (i x = termsubst i t))) /\
                   !x y s t. MEM (x,t) (SOLVE sol env) /\
                             MEM (y,s) (SOLVE sol env)
                             ==> ~(x IN FVT(s))`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC] THENL
   [SIMP_TAC[SOLVE; APPEND_NIL] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUC_INJ; SOLVE] THEN X_GEN_TAC `sol:(num#term)list` THEN
  FIRST_X_ASSUM(K ALL_TAC o check is_imp o snd o dest_forall o concl) THEN
  REWRITE_TAC[SOLVE_PRESERVES_UNIFIERS] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LENGTH_MAP; SOLVE_PRESERVES_LOOPFREE;
               SOLVE_PRESERVES_CONFLICTFREE] THEN
  MATCH_MP_TAC SOLVE_PRESERVES_DEFREE THEN ASM_REWRITE_TAC[]);;

let SOLVE_WORKS = prove
 (`!env.
        LOOPFREE(env) /\ CONFLICTFREE(env)
        ==> CONFLICTFREE(SOLVE [] env) /\
            (!i. (!x t. MEM (x,t) env ==> (i x = termsubst i t)) <=>
                 (!x t. MEM (x,t) (SOLVE [] env) ==> (i x = termsubst i t))) /\
            !x y s t. MEM (x,t) (SOLVE [] env) /\ MEM (y,s) (SOLVE [] env)
                      ==> ~(x IN FVT s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:num t:term. MEM (x,t) env = MEM (x,t) (APPEND [] env)`
   (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  MATCH_MP_TAC SOLVE_WORKS_GENERAL THEN
  ASM_REWRITE_TAC[MEM; APPEND; GSYM EXISTS_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The "actual code".                                                        *)
(* ------------------------------------------------------------------------- *)

let retval_INDUCT,retval_RECURSION = define_type
  "retval = TT | FF | Exception";;

let retval_DISTINCT = prove_constructors_distinct retval_RECURSION;;

let ISTRIV_EXISTS = prove
 (`!env x. LOOPFREE(env) /\ CONFLICTFREE(env)
     ==> ?istriv. !t. istriv t =
     if t = V x then TT
     else if ?y. (t = V y) /\ MEM y (MAP FST env)
          then istriv (ASSOC (@y. (t = V y) /\ MEM y (MAP FST env)) env)
     else if x IN FVT(t) then Exception
     else if ?y s. y IN FVT(t) /\ MEM (y,s) env /\ ~(istriv s = FF)
          then Exception else FF`,
  REWRITE_TAC[CONFLICTFREE] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WF_REC o MATCH_MP LOOPFREE_WF_TERM) THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(ASM (GEN_MESON_TAC 0 10 1) []) THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[FVT; IN_INSERT; term_INJ] THEN
  SUBGOAL_THEN `(@y. (z = y) /\ MEM y (MAP FST (env:(num#term)list))) = z`
  SUBST1_TAC THENL
    [MATCH_MP_TAC SELECT_UNIQUE THEN
     X_GEN_TAC `w:num` THEN REWRITE_TAC[] THEN EQ_TAC THEN
     ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `MEM z (MAP FST (env:(num#term)list))` THEN
  UNDISCH_TAC `!x. LENGTH (FILTER (\(y:num,s:term). y = x) env) <= 1` THEN
  DISCH_THEN(MP_TAC o SPEC `z:num`) THEN
  SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; ASSOC; FILTER] THEN
  SPEC_TAC(`h:num#term`,`h:num#term`) THEN
  ONCE_REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:num`; `s:term`] THEN
  REWRITE_TAC[FST; SND] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_CASES_TAC `y:num = z` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let istriv_raw =
  new_specification ["istriv"]
   (REWRITE_RULE[SKOLEM_THM; RIGHT_IMP_EXISTS_THM] ISTRIV_EXISTS);;

let istriv = prove
 (`!env x.
        LOOPFREE(env) /\ CONFLICTFREE(env)
        ==> (!x y. istriv env x (V y) =
                        if y = x then TT
                        else if MEM y (MAP FST env) then
                           istriv env x (ASSOC y env)
                        else FF) /\
            (!f args. istriv env x (Fn f args) =
                        if EX (\a. ~(istriv env x a = FF)) args
                        then Exception else FF)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
     GEN_REWRITE_TAC LAND_CONV [MATCH_MP istriv_raw th]) THEN
  REWRITE_TAC[term_INJ; term_DISTINCT] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[UNWIND_THM1] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; UNWIND_THM2] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC SELECT_UNIQUE THEN
      X_GEN_TAC `w:num` THEN REWRITE_TAC[] THEN EQ_TAC THEN
      ASM_SIMP_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~MEM y (MAP FST (env:(num#term)list))` THEN
    MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
    FIRST_ASSUM(CHOOSE_THEN (MP_TAC o CONJUNCT1)) THEN
    SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
    ASM_SIMP_TAC[FST]; ALL_TAC] THEN
  ASM_CASES_TAC `x IN FVT(Fn f args)` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~EX (\a. ~(istriv env x a = FF)) args` THEN
    MATCH_MP_TAC(TAUT `a ==> ~a ==> b`) THEN
    UNDISCH_TAC `x IN FVT (Fn f args)` THEN
    REWRITE_TAC[FVT; IN_LIST_UNION; EX_MAP] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
                 EX_IMP) THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    TRY(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP istriv_raw th]) THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[FVT; IN_INSERT; NOT_IN_EMPTY]) THEN
      ASM_REWRITE_TAC[retval_DISTINCT];
      ASM_REWRITE_TAC[term_DISTINCT; retval_DISTINCT]]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FVT; IN_LIST_UNION; EX_MAP] THEN
  REWRITE_TAC[LEFT_AND_EX_THM] THEN REWRITE_TAC[EXISTS_EX] THEN
  REWRITE_TAC[o_THM] THEN UNDISCH_TAC `~(x IN FVT (Fn f args))` THEN
  REWRITE_TAC[FVT; IN_LIST_UNION; EX_MAP] THEN
  MATCH_MP_TAC EX_ADHOC THEN X_GEN_TAC `t:term` THEN
  REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
    (RAND_CONV o RAND_CONV o LAND_CONV) [MATCH_MP istriv_raw th]) THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `~(x IN FVT t)` THEN
    ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `?y. (t = V y) /\ MEM y (MAP FST (env:(num#term)list))` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[retval_DISTINCT]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; term_INJ] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  SUBGOAL_THEN `(@z. (y = z) /\ MEM z (MAP FST (env:(num#term)list))) = y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `w:num` THEN REWRITE_TAC[] THEN EQ_TAC THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. MEM (y:num,s:term) env <=> (s = ASSOC y env)`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN UNDISCH_TAC `MEM y (MAP FST (env:(num#term)list))` THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
  SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; MAP] THEN
  SPEC_TAC(`h:num#term`,`h:num#term`) THEN
  ONCE_REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `t:term`] THEN
  REWRITE_TAC[FST; SND; PAIR_EQ; ASSOC] THEN
  ASM_CASES_TAC `x:num = y` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(TAUT `(b ==> ~a) ==> (a ==> (c \/ b <=> c))`) THEN
    DISCH_TAC THEN REWRITE_TAC[CONFLICTFREE] THEN
    DISCH_THEN(MP_TAC o SPEC `y:num`) THEN
    REWRITE_TAC[FILTER; LENGTH] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC n <= 1) <=> ~(n = 0)`] THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN
    DISCH_THEN(MP_TAC o AP_TERM `MEM (y:num,s:term)`) THEN
    ASM_REWRITE_TAC[MEM; MEM_FILTER] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REFL_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `CONFLICTFREE t` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONFLICTFREE]) THEN
  REWRITE_TAC[CONFLICTFREE; MEM; FILTER] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Prove that it works.                                                      *)
(* ------------------------------------------------------------------------- *)

let EQV = new_definition
  `EQV env x y = MEM (x,V y) env`;;

let EQV_IMP_OCC = prove
 (`!env x y. EQV env x y ==> OCC env x y`,
  REWRITE_TAC[EQV; OCC] THEN MESON_TAC[IN_INSERT; FVT]);;

let ISTRIV_WORKS = prove
 (`!env x t. LOOPFREE(env) /\ CONFLICTFREE(env)
             ==> (istriv env x t =
                    if ?y. (t = V y) /\ RTC (EQV env) y x then TT
                    else if ?y. y IN FVT t /\ RTC (OCC env) y x then Exception
                    else FF)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  GEN_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP LOOPFREE_WF_TERM o CONJUNCT1) THEN
  REWRITE_TAC[WF_IND] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `t:term` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP istriv_raw th]) THEN
  ASM_CASES_TAC `t = V x` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[term_INJ; RTC_REFL]; ALL_TAC] THEN
  ASM_CASES_TAC `?y. (t = V y) /\ MEM y (MAP FST (env:(num#term)list))` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[term_INJ; UNWIND_THM1] THEN
    SUBGOAL_THEN `(@y. (z = y) /\ MEM y (MAP FST (env:(num#term)list))) = z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN
      X_GEN_TAC `w:num` THEN REWRITE_TAC[] THEN EQ_TAC THEN
      ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ASSOC z (env:(num#term)list)`) THEN
    ANTS_TAC THENL
     [EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[FVT; IN_INSERT] THEN
      UNDISCH_TAC `MEM z (MAP FST (env:(num#term)list))` THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[CONFLICTFREE] THEN
      DISCH_THEN(MP_TAC o SPEC `z:num`) THEN
      SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; ASSOC; FILTER] THEN
      SPEC_TAC(`h:num#term`,`h:num#term`) THEN
      ONCE_REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`y:num`; `s:term`] THEN
      REWRITE_TAC[FST; SND] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      ASM_CASES_TAC `y:num = z` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; UNWIND_THM2] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [RTC_CASES_R] THEN
    ASM_CASES_TAC `x:num = z` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[OCC; EQV] THEN
    SUBGOAL_THEN `!s. MEM (z:num,s:term) env = (s = ASSOC z env)`
      (fun th -> REWRITE_TAC[th])
    THENL
     [GEN_TAC THEN UNDISCH_TAC `MEM z (MAP FST (env:(num#term)list))` THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
      SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC[MEM; MAP] THEN
      SPEC_TAC(`h:num#term`,`h:num#term`) THEN
      ONCE_REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:num`; `t:term`] THEN
      REWRITE_TAC[FST; SND; PAIR_EQ; ASSOC] THEN
      ASM_CASES_TAC `x:num = z` THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC(TAUT `(b ==> ~a) ==> (a ==> (c \/ b <=> c))`) THEN
        DISCH_TAC THEN REWRITE_TAC[CONFLICTFREE] THEN
        DISCH_THEN(MP_TAC o SPEC `z:num`) THEN
        REWRITE_TAC[FILTER; LENGTH] THEN
        CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC n <= 1) <=> ~(n = 0)`] THEN
        REWRITE_TAC[LENGTH_EQ_NIL] THEN
        DISCH_THEN(MP_TAC o AP_TERM `MEM (z:num,s:term)`) THEN
        ASM_REWRITE_TAC[MEM; MEM_FILTER] THEN
        CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REFL_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `CONFLICTFREE t` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONFLICTFREE]) THEN
      REWRITE_TAC[CONFLICTFREE; MEM; FILTER] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV o BINDER_CONV o
                     LAND_CONV) [EQ_SYM_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNWIND_THM2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(?y. (t = V y) /\ RTC (EQV env) y x)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `~(?y. (t = V y) /\ MEM y (MAP FST (env:(num#term)list)))` THEN
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
    ONCE_REWRITE_TAC[RTC_CASES_R] THEN REWRITE_TAC[EQV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:num` THEN
    ASM_CASES_TAC `y = x:num` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[MEM_MAP] THEN MESON_TAC[FST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `x IN FVT(t)` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `?y. y IN FVT t /\ RTC (OCC env) y x`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[RTC_REFL]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:num` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC[RTC_CASES_R] THEN
  ASM_CASES_TAC `y = x:num` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[OCC; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:term` THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:term`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `?y. (s = V y) /\ RTC (EQV env) y x` THEN
  ASM_REWRITE_TAC[retval_DISTINCT] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[FVT; IN_INSERT] THEN
    ASM_MESON_TAC[RTC_MONO; EQV_IMP_OCC]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[retval_DISTINCT]);;

(* ------------------------------------------------------------------------- *)
(* Wellfoundedness lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

let SUB1 = new_definition
  `SUB1 s t <=> ?f args. (t = Fn f args) /\ MEM s args`;;

let WF_SUB1 = prove
 (`WF(SUB1)`,
  SIMP_TAC[WF_IND; SUB1; LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[term_DISTINCT; term_INJ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[]);;

let RTC_SUB1 = prove
 (`!x t. RTC(SUB1) (V x) t <=> x IN FVT(t)`,
  GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; IN_LIST_UNION] THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[RTC_CASES_L] THEN
  REWRITE_TAC[SUB1; term_INJ; term_DISTINCT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `?y. RTC SUB1 (V x) y /\ MEM y l` THEN CONJ_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EX_MAP; o_DEF] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP ALL_ADHOC) THEN
  REWRITE_TAC[EX_MEM]);;

let WF_SUBCOMPONENT = prove
 (`LOOPFREE(env) ==> WF(\s t. ?x. MEM (x,s) env /\ RTC(SUB1) (V x) t)`,
  REWRITE_TAC[RTC_SUB1] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[LOOPFREE_WF_TERM]);;

let WF_DESCENT = prove
 (`LOOPFREE(env)
   ==> WF(\s t. (?x. (t = V x) /\ MEM (x,s) env) \/
                (?f args. (t = Fn f args) /\ MEM s args))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[DISJ_SYM] THEN
  MATCH_MP_TAC WF_DISJ THEN REWRITE_TAC[GSYM SUB1] THEN
  CONV_TAC(TOP_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[WF_SUB1] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  ASM_SIMP_TAC[WF_SUBCOMPONENT]);;

(* ------------------------------------------------------------------------- *)
(* Existence of unify.                                                       *)
(* ------------------------------------------------------------------------- *)

let termcases = new_recursive_definition term_RECURSION
  `(termcases cv cf (V v) = cv v) /\
   (termcases cv cf (Fn f args) = cf f args)`;;

let tpcases_def = new_definition
  `tpcases c1 c2 c3 (t1,t2) =
        termcases (\v1. termcases
                            (\v2. c2 v1 (V v2))
                            (\f2 args2. c2 v1 (Fn f2 args2)) t2)
                  (\f1 args1. termcases
                                (\v2. c3 f1 args1 v2)
                                (\f2 args2. c1 f1 args1 f2 args2) t2)
                  t1`;;

let tpcases = prove
 (`(tpcases c1 c2 c3 (Fn f1 args1,Fn f2 args2) = c1 f1 args1 f2 args2) /\
   (tpcases c1 c2 c3 (V v1,t2) = c2 v1 t2) /\
   (tpcases c1 c2 c3 (Fn f1 args1,V v2) = c3 f1 args1 v2)`,
  SPEC_TAC(`t2:term`,`t2:term`) THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[tpcases_def; termcases]);;

let MLEFT = new_definition
  `MLEFT (env,eqs) =
       CARD(FVT(Fn 0 (MAP FST eqs)) UNION
            FVT(Fn 0 (MAP SND eqs)) UNION
            FVT(Fn 0 (MAP SND env)) UNION
            FVT(Fn 0 (MAP (V o FST) env))) -
       CARD(FVT(Fn 0 (MAP (V o FST) env)))`;;

let CRIGHT = new_definition
  `CRIGHT (env',eqs') (env,eqs) <=>
         LOOPFREE(env) /\
         (env' = env) /\
         ((?f args1 args2 oth.
                (LENGTH args1 = LENGTH args2) /\
                (eqs = CONS (Fn f args1,Fn f args2) oth) /\
                (eqs' = APPEND (ZIP args1 args2) oth)) \/
          (?x t oth. (eqs = CONS (V x,t) oth) /\
                     (MEM x (MAP FST env) /\
                      (eqs' = CONS (ASSOC x env,t) oth) \/
                      ~(MEM x (MAP FST env)) /\
                      (istriv env x t = TT) /\
                      (eqs' = oth))) \/
          (?x f args oth. (eqs = CONS (Fn f args,V x) oth) /\
                          (eqs' = CONS (V x,Fn f args) oth)))`;;

let CALLORDER = new_definition
  `CALLORDER (env',eqs') (env,eqs) <=>
        MEASURE MLEFT (env',eqs') (env,eqs) \/
        CRIGHT (env',eqs') (env,eqs)`;;

let PAIRED_ETA_THM = prove
 (`!g:A#B->C. (\(p1,p2). g (p1,p2)) = g`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let WF_CRIGHT = prove
 (`WF CRIGHT`,
  SUBGOAL_THEN `CRIGHT = \(env',eqs') (env,eqs). CRIGHT (env',eqs') (env,eqs)`
  SUBST1_TAC THENL
   [REWRITE_TAC[PAIRED_ETA_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV ETA_CONV) THEN REFL_TAC; ALL_TAC] THEN
  REWRITE_TAC[CRIGHT] THEN MATCH_MP_TAC WF_PROJ_EQ THEN
  X_GEN_TAC `env:(num#term)list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WF_DESCENT) THEN
  DISCH_THEN(MP_TAC o GEN_ALL o MATCH_MP (ONCE_REWRITE_RULE
      [IMP_CONJ] WF_ALTERNATION)) THEN
  DISCH_THEN(MP_TAC o SPEC
   `\s t. (?f args. s = Fn f args) /\ (?x. t = V x)`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [MESON_TAC[term_DISTINCT]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WF_MULTIZIP) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE
      [IMP_CONJ] WF_SUBSET) THEN
  MAP_EVERY X_GEN_TAC [`eqs2:(term#term)list`; `eqs1:(term#term)list`] THEN
  REWRITE_TAC[] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`(Fn f args1,Fn f args2)`;
      `oth:(term#term)list`;
      `(ZIP args1 args2):(term#term)list`] THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:term`; `t:term`] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    DISCH_TAC THEN DISJ1_TAC THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`f:num`; `args1:term list`; `f:num`; `args2:term list`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP MAP_FST_ZIP);
      FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP MAP_SND_ZIP)] THEN
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[FST; SND];
    MAP_EVERY EXISTS_TAC
     [`(V x,t:term)`;
      `oth:(term#term)list`;
      `[ASSOC x (env:(num#term)list),t:term]`] THEN
    ASM_REWRITE_TAC[APPEND] THEN GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:term`; `u:term`] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[MEM; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[] THEN EXISTS_TAC `x:num` THEN
    ASM_REWRITE_TAC[MEM_ASSOC];
    MAP_EVERY EXISTS_TAC
     [`(V x,t:term)`; `oth:(term#term)list`; `[]:(term#term)list`] THEN
    ASM_REWRITE_TAC[APPEND; MEM];
    MAP_EVERY EXISTS_TAC
     [`(Fn f args,V x)`; `oth:(term#term)list`; `[V x,Fn f args]`] THEN
    ASM_REWRITE_TAC[APPEND] THEN GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:term`; `u:term`] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[MEM; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN
    REPEAT DISJ2_TAC THEN MESON_TAC[]]);;

let WF_CALLORDER = prove
 (`WF CALLORDER`,
  SUBGOAL_THEN
   `CALLORDER = \(env',eqs') (env,eqs). CALLORDER (env',eqs') (env,eqs)`
  SUBST1_TAC THENL
   [REWRITE_TAC[PAIRED_ETA_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV ETA_CONV) THEN REFL_TAC; ALL_TAC] THEN
  REWRITE_TAC[CALLORDER] THEN
  REWRITE_TAC[PAIRED_ETA_THM] THEN
  MATCH_MP_TAC WF_MEASURE_OR_NONINC THEN
  REWRITE_TAC[WF_CRIGHT; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`env':(num#term)list`; `eqs':(term#term)list`;
    `env:(num#term)list`; `eqs:(term#term)list`] THEN
  REWRITE_TAC[CRIGHT; MLEFT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(ARITH_RULE `a <= c:num ==> a - b <= c - b`) THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  REWRITE_TAC[FINITE_UNION; FVT_FINITE] THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `x:num` THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; MAP_APPEND; FVT; LIST_UNION; LIST_UNION_APPEND] THEN
  REWRITE_TAC[IN_UNION; GSYM DISJ_ASSOC] THENL
   [MATCH_MP_TAC(TAUT `(a' <=> a) /\ (c' <=> c)
                       ==> a \/ b \/ c \/ d ==> a' \/ b \/ c' \/ d`) THEN
    ASM_SIMP_TAC[MAP_FST_ZIP; MAP_SND_ZIP];
    MATCH_MP_TAC(TAUT
      `(a ==> e)
       ==> a \/ b \/ c \/ d \/ e \/ f
           ==> a' \/ b \/ c \/ d \/ e \/ f`) THEN
    UNDISCH_TAC `MEM x' (MAP FST (env:(num#term)list))` THEN
    SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP; ASSOC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[LIST_UNION; IN_UNION];
    CONV_TAC TAUT;
    CONV_TAC TAUT]);;

let UNIFY_EXISTS_RAW = prove
 (`?unify.
      !pr. unify pr =
              if ~LOOPFREE(FST pr) then NONE
              else if SND pr = [] then SOME(FST pr)
              else tpcases
                        (\f fargs g gargs.
                                if (f = g) /\ (LENGTH fargs = LENGTH gargs)
                                then unify (FST pr,APPEND (ZIP fargs gargs)
                                                          (TL(SND pr)))
                                else NONE)
                        (\x t. if MEM x (MAP FST (FST pr)) then
                                  unify (FST pr,CONS (ASSOC x (FST pr),t)
                                                     (TL(SND pr)))
                               else if istriv (FST pr) x t = Exception then
                                  NONE
                               else if istriv (FST pr) x t = TT then
                                  unify(FST pr,TL(SND pr))
                               else
                                  unify(CONS (x,t) (FST pr),TL(SND pr)))
                        (\f args x. unify (FST pr,
                                           CONS (V x,Fn f args)
                                                (TL(SND pr))))
                        (HD(SND pr))`,
  MATCH_MP_TAC(MATCH_MP WF_REC WF_CALLORDER) THEN
  MAP_EVERY X_GEN_TAC
   [`unify1:(num#term)list#(term#term)list->((num#term)list)option`;
    `unify2:(num#term)list#(term#term)list->((num#term)list)option`] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`env1:(num#term)list`; `eqs1:(term#term)list`] THEN
  DISCH_THEN(MP_TAC o GENL
   [`env2:(num#term)list`; `eqs2:(term#term)list`] o SPEC
    `(env2,eqs2):(num#term)list#(term#term)list`) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  ASM_CASES_TAC `LOOPFREE env1` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `eqs1:(term#term)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hpr:term#term` (X_CHOOSE_THEN
   `oth:(term#term)list` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL] THEN
  SUBST_ALL_TAC(GSYM(ISPEC `hpr:term#term` PAIR)) THEN
  MP_TAC(ISPEC `FST(hpr:term#term)` term_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2
   (X_CHOOSE_THEN `x:num` SUBST_ALL_TAC)
   (X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `fargs:term list` SUBST_ALL_TAC)))
  THENL
   [ABBREV_TAC `t = SND(hpr:term#term)`;
    MP_TAC(ISPEC `SND(hpr:term#term)` term_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2
     (X_CHOOSE_THEN `x:num` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `g:num` (X_CHOOSE_THEN `gargs:term list`
         SUBST_ALL_TAC)))] THEN
  REWRITE_TAC[tpcases] THENL
   [ALL_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CALLORDER] THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[CRIGHT] THEN
    REPEAT DISJ2_TAC THEN ASM_MESON_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CALLORDER] THEN DISJ2_TAC THEN ASM_REWRITE_TAC[CRIGHT] THEN
    ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `MEM x (MAP FST (env1:(num#term)list))` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CALLORDER] THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[CRIGHT] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `istriv env1 x t = Exception` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `istriv env1 x t = TT` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CALLORDER] THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[CRIGHT] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CALLORDER] THEN
  DISJ1_TAC THEN REWRITE_TAC[MEASURE; MLEFT] THEN
  REWRITE_TAC[MAP; FST; SND; LENGTH] THEN
  MATCH_MP_TAC(ARITH_RULE
   `(a' = a) /\ (b' = b + 1) /\ b' <= a' ==> a' - b' < a - b`) THEN
  SUBGOAL_THEN
   `FVT(Fn 0 (CONS ((V o FST) (x,t:term)) (MAP (V o FST) env1))) =
    x INSERT FVT(Fn 0 (MAP (V o FST) (env1:(num#term)list)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FVT; MAP; LIST_UNION; o_THM; FST] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FVT(Fn 0 (CONS (V x) (MAP FST (oth:(term#term)list)))) =
    x INSERT FVT(Fn 0 (MAP FST oth))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FVT; MAP; LIST_UNION; o_THM; FST] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FVT(Fn 0 (CONS t (MAP SND env1))) =
    FVT(t) UNION FVT(Fn 0 (MAP SND (env1:(num#term)list)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FVT; MAP; LIST_UNION; o_THM; FST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FVT(Fn 0 (CONS t (MAP SND oth))) =
    FVT(t) UNION FVT(Fn 0 (MAP SND (oth:(term#term)list)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FVT; MAP; LIST_UNION; o_THM; FST]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; DISJ_ACI; IN_INSERT];
    SIMP_TAC[CARD_CLAUSES; FVT_FINITE; ADD1] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `x IN FVT (Fn 0 (MAP (V o FST) (env1:(num#term)list)))` THEN
    UNDISCH_TAC `~MEM x (MAP FST (env1:(num#term)list))` THEN
    MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> b ==> c`) THEN
    SPEC_TAC(`env1:(num#term)list`,`env1:(num#term)list`) THEN
    REWRITE_TAC[FVT] THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[LIST_UNION; MEM; MAP; NOT_IN_EMPTY] THEN
    REWRITE_TAC[o_THM; FVT; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_UNION; FVT_FINITE; FINITE_INSERT] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_INSERT] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let unify_raw = new_specification ["unify"] UNIFY_EXISTS_RAW;;

let unify = prove
 (`LOOPFREE(env)
   ==> (unify (env,CONS (Fn f fargs,Fn g gargs) oth) =
            if (f = g) /\ (LENGTH fargs = LENGTH gargs)
            then unify (env,APPEND (ZIP fargs gargs) oth)
            else NONE) /\
       (unify (env,CONS (V x,t) oth) =
            if MEM x (MAP FST env) then unify (env,CONS (ASSOC x env,t) oth)
            else if istriv env x t = Exception then NONE
            else if istriv env x t = TT then unify (env,oth)
            else unify (CONS (x,t) env,oth)) /\
       (unify (env,CONS (Fn f fargs,V x) oth) =
        unify (env,CONS (V x,Fn f fargs) oth))`,
  DISCH_TAC THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [unify_raw] THEN
  ASM_REWRITE_TAC[FST; SND; HD; TL; NOT_CONS_NIL; tpcases]);;

(* ------------------------------------------------------------------------- *)
(* Show that it does indeed work.                                            *)
(* ------------------------------------------------------------------------- *)

let unifies = new_definition
  `unifies i l <=> ALL (\(s,t). termsubst i s = termsubst i t) l`;;

let OPTION_DISTINCT = prove_constructors_distinct option_RECURSION;;

let OPTION_INJ = prove_constructors_injective option_RECURSION;;

let TC_SUB1_IRREFL = prove
 (`!s t. TC SUB1 s t ==> ~(s = t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a ==> ~b <=> b ==> ~a`] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC WF_REFL THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  REWRITE_TAC[WF_TC; WF_SUB1]);;

let UNIFY_OCCURS = prove
 (`!env i.
        ALL (\(x,t). i x = termsubst i t) env
        ==> !x y. RTC (OCC env) x y ==> RTC SUB1 (i y) (i x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN
  REWRITE_TAC[RTC_REFL] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[RTC_TRANS]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[OCC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:term` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM]) THEN
  DISCH_THEN(MP_TAC o SPEC `(x:num,t:term)`) THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC[] THEN
  DISCH_TAC THEN UNDISCH_TAC `y IN FVT(t)` THEN SPEC_TAC(`y:num`,`y:num`) THEN
  SPEC_TAC(`t:term`,`t:term`) THEN MATCH_MP_TAC term_INDUCT THEN
  SIMP_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; termsubst; RTC_REFL] THEN
  MAP_EVERY X_GEN_TAC [`f:num`; `args:term list`] THEN
  DISCH_TAC THEN X_GEN_TAC `z:num` THEN REWRITE_TAC[IN_LIST_UNION] THEN
  REWRITE_TAC[EX_MAP; o_DEF] THEN REWRITE_TAC[GSYM EX_MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `termsubst i s` THEN CONJ_TAC THENL
   [UNDISCH_TAC
     `ALL (\t. !y. y IN FVT t ==> RTC SUB1 (i y) (termsubst i t)) args` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUB1] THEN EXISTS_TAC `f:num` THEN
    EXISTS_TAC `MAP (termsubst i) args` THEN
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]]);;

let UNIFY_OCCURS_PROPER = prove
 (`!env i.
        ALL (\(x,t). i x = termsubst i t) env
        ==> !x y. RTC (OCC env) x y
                  ==> RTC (EQV env) x y \/ TC SUB1 (i y) (i x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN
  REWRITE_TAC[RTC_REFL] THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[RTC_TRANS];
      DISJ2_TAC THEN ONCE_REWRITE_TAC[TC_TC_RTC_CASES];
      DISJ2_TAC THEN ONCE_REWRITE_TAC[TC_RTC_TC_CASES];
      ASM_MESON_TAC[TC_TRANS]] THEN
    EXISTS_TAC `(i:num->term) y` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP UNIFY_OCCURS) THEN
    ASM_MESON_TAC[EQV_IMP_OCC; RTC_MONO]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[OCC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:term` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM]) THEN
  DISCH_THEN(MP_TAC o SPEC `(x:num,t:term)`) THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!t y. y IN FVT t ==> (t = V y) \/ TC SUB1 (i y) (termsubst i t)`
  MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[EQV; RTC_INC]] THEN
  SUBGOAL_THEN `!t y. y IN FVT t ==> RTC SUB1 (V y) t` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[RTC; RC_CASES] THEN
    SUBGOAL_THEN
     `!s t. TC SUB1 s t ==> TC SUB1 (termsubst i s) (termsubst i t)`
     (fun th -> MESON_TAC[th; termsubst]) THEN
    MATCH_MP_TAC TC_INDUCT THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[TC_TRANS]] THEN
    MAP_EVERY X_GEN_TAC [`s:term`; `u:term`] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC TC_INC THEN MP_TAC th) THEN
    REWRITE_TAC[SUB1] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `args:term list`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`f:num`; `MAP (termsubst i) args`] THEN
    ASM_REWRITE_TAC[termsubst; MEM_MAP] THEN ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC term_INDUCT THEN
  SIMP_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; RTC_REFL] THEN
  MAP_EVERY X_GEN_TAC [`f:num`; `args:term list`] THEN
  DISCH_TAC THEN REWRITE_TAC[IN_LIST_UNION] THEN
  REWRITE_TAC[EX_MAP; o_DEF] THEN X_GEN_TAC `z:num` THEN
  REWRITE_TAC[GSYM EX_MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `s:term` THEN CONJ_TAC THENL
   [UNDISCH_TAC
     `ALL (\t. !y. y IN FVT t ==> RTC SUB1 (V y) t) args` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUB1] THEN ASM_MESON_TAC[]]);;

let GOODLOOP_UNIFIABLE = prove
 (`!env x t.
        LOOPFREE(env) /\ CONFLICTFREE(env) /\ (istriv env x t = TT)
   ==> !i. unifies i (CONS (V x,t) (MAP (\(x,t). V x,t) env)) =
           unifies i (MAP (\(x,t). V x,t) env)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[ISTRIV_WORKS] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[retval_DISTINCT]) THEN
  X_GEN_TAC `i:num->term` THEN REWRITE_TAC[unifies; ALL] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b <=> b) <=> (b ==> a)`] THEN
  REWRITE_TAC[ALL_MAP; o_DEF] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PAIRED_ETA_THM] THEN
  REWRITE_TAC[] THEN CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[termsubst] THEN DISCH_TAC THEN
  UNDISCH_TAC `?y. (t = V y) /\ RTC (EQV env) y x` THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  SPEC_TAC(`x:num`,`x:num`) THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
  SUBGOAL_THEN `!x y. RTC (EQV env) x y ==> (i x :term = i y)`
    (fun th -> MESON_TAC[th; termsubst]) THEN
  MATCH_MP_TAC RTC_INDUCT THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`u:num`; `v:num`] THEN REWRITE_TAC[EQV] THEN
  UNDISCH_TAC `ALL (\(p1,p2). i p1 = termsubst i p2) env` THEN
  SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ALL; MEM] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[termsubst]);;

let BADLOOP_UNUNIFIABLE = prove
 (`!env x t.
        LOOPFREE(env) /\ CONFLICTFREE(env) /\ (istriv env x t = Exception)
        ==> !i. ~(unifies i (CONS (V x,t) (MAP (\(x,t). V x,t) env)))`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[ISTRIV_WORKS] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[retval_DISTINCT]) THEN
  X_GEN_TAC `i:num->term` THEN REWRITE_TAC[unifies; ALL] THEN
  MATCH_MP_TAC(TAUT `(b ==> ~a) ==> ~(a /\ b)`) THEN
  REWRITE_TAC[ALL_MAP; o_DEF] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PAIRED_ETA_THM] THEN
  REWRITE_TAC[] THEN CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[termsubst] THEN DISCH_TAC THEN
  UNDISCH_TAC `?y. y IN FVT t /\ RTC (OCC env) y x` THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `y:num` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:num`) THEN
  ASM_CASES_TAC `RTC (EQV env) y x` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN STRIP_TAC THEN MATCH_MP_TAC TC_SUB1_IRREFL THEN
    ONCE_REWRITE_TAC[TC_RTC_TC_CASES] THEN
    EXISTS_TAC `(i:num->term) y` THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP UNIFY_OCCURS) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!t y. y IN FVT t ==> (t = V y) \/ TC SUB1 (i y) (termsubst i t)`
     (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `!t y. y IN FVT t ==> RTC SUB1 (V y) t` MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[RTC; RC_CASES] THEN
      SUBGOAL_THEN
       `!s t. TC SUB1 s t ==> TC SUB1 (termsubst i s) (termsubst i t)`
       (fun th -> MESON_TAC[th; termsubst]) THEN
      MATCH_MP_TAC TC_INDUCT THEN
      CONJ_TAC THENL [ALL_TAC; MESON_TAC[TC_TRANS]] THEN
      MAP_EVERY X_GEN_TAC [`s:term`; `u:term`] THEN
      DISCH_THEN(fun th -> MATCH_MP_TAC TC_INC THEN MP_TAC th) THEN
      REWRITE_TAC[SUB1] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `args:term list`
          STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`f:num`; `MAP (termsubst i) args`] THEN
      ASM_REWRITE_TAC[termsubst; MEM_MAP] THEN ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC term_INDUCT THEN
    SIMP_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; RTC_REFL] THEN
    MAP_EVERY X_GEN_TAC [`f:num`; `args:term list`] THEN
    DISCH_TAC THEN REWRITE_TAC[IN_LIST_UNION] THEN
    REWRITE_TAC[EX_MAP; o_DEF] THEN X_GEN_TAC `z:num` THEN
    REWRITE_TAC[GSYM EX_MEM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `s:term` THEN CONJ_TAC THENL
     [UNDISCH_TAC
       `ALL (\t. !y. y IN FVT t ==> RTC SUB1 (V y) t) args` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUB1] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC TC_SUB1_IRREFL THEN
  ONCE_REWRITE_TAC[TC_TC_RTC_CASES] THEN
  EXISTS_TAC `(i:num->term) y` THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP UNIFY_OCCURS_PROPER) THEN
    DISCH_THEN(MP_TAC o SPECL [`y:num`; `x:num`]) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t y. y IN FVT t ==> RTC SUB1 (V y) t` MP_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `!s t. RTC SUB1 s t ==> RTC SUB1 (termsubst i s) (termsubst i t)`
     (fun th -> ASM_MESON_TAC[th; termsubst]) THEN
    MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[RTC_REFL] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[RTC_TRANS]] THEN
    MAP_EVERY X_GEN_TAC [`s:term`; `u:term`] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC RTC_INC THEN MP_TAC th) THEN
    REWRITE_TAC[SUB1] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `args:term list`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`f:num`; `MAP (termsubst i) args`] THEN
    ASM_REWRITE_TAC[termsubst; MEM_MAP] THEN ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC term_INDUCT THEN
  SIMP_TAC[FVT; IN_INSERT; NOT_IN_EMPTY; RTC_REFL] THEN
  MAP_EVERY X_GEN_TAC [`f:num`; `args:term list`] THEN
  DISCH_TAC THEN REWRITE_TAC[IN_LIST_UNION] THEN
  REWRITE_TAC[EX_MAP; o_DEF] THEN X_GEN_TAC `z:num` THEN
  REWRITE_TAC[GSYM EX_MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC `s:term` THEN CONJ_TAC THENL
   [UNDISCH_TAC
     `ALL (\t. !y. y IN FVT t ==> RTC SUB1 (V y) t) args` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUB1] THEN ASM_MESON_TAC[]]);;

let UNIFY_WORKS_RAW = prove
 (`!pr. LOOPFREE(FST pr) /\ CONFLICTFREE(FST pr)
        ==> ((unify pr = NONE)
             ==> !i. ~(unifies i (APPEND (MAP (\(x,t). V x,t) (FST pr))
                                         (SND pr)))) /\
            !ans. (unify pr = SOME ans)
                  ==> LOOPFREE(ans) /\ CONFLICTFREE(ans) /\
                      !i. unifies i (APPEND (MAP (\(x,t). V x,t) (FST pr))
                                            (SND pr)) =
                          unifies i (MAP (\(x,t). V x,t) ans)`,
  MATCH_MP_TAC(REWRITE_RULE[WF_IND] WF_CALLORDER) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`env:(num#term)list`; `eqs:(term#term)list`] THEN
  DISCH_THEN(MP_TAC o GENL [`env':(num#term)list`; `eqs':(term#term)list`] o
                SPEC `env':(num#term)list,eqs':(term#term)list`) THEN
  REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[unify_raw] THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPEC `eqs:(term#term)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
   [ASM_REWRITE_TAC[APPEND_NIL; OPTION_INJ; OPTION_DISTINCT] THEN
    GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [EXISTS_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:term` (X_CHOOSE_THEN `t:term`
        (X_CHOOSE_THEN `oth:(term#term)list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL] THEN
  MP_TAC(SPEC `s:term` term_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2
   (X_CHOOSE_THEN `x:num` SUBST_ALL_TAC)
   (X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `fargs:term list`
        SUBST_ALL_TAC)))
  THENL
   [ALL_TAC;
    MP_TAC(ISPEC `t:term` term_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2
     (X_CHOOSE_THEN `x:num` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `g:num` (X_CHOOSE_THEN `gargs:term list`
         SUBST_ALL_TAC)))] THEN
  REWRITE_TAC[tpcases] THENL
   [ASM_CASES_TAC `MEM x (MAP FST (env:(num#term)list))` THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL
       [`env:(num#term)list`;
        `CONS (ASSOC (x:num) env,t) (oth:(term#term)list)`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[CALLORDER; CRIGHT] THEN
        DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!i. unifies i
              (APPEND (MAP (\(x,t). V x,t) env) (CONS (ASSOC x env,t) oth)) =
            unifies i
              (APPEND (MAP (\(x,t). V x,t) env) (CONS (V x,t) oth))`
       (fun th -> REWRITE_TAC[th]) THEN
      X_GEN_TAC `i:num->term` THEN
      REWRITE_TAC[unifies; ALL; ALL_APPEND] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[ALL_MAP] THEN
      MATCH_MP_TAC(TAUT
       `(a ==> (b <=> b')) ==> (a /\ b /\ c <=> a /\ b' /\ c)`) THEN
      UNDISCH_TAC `MEM x (MAP FST (env:(num#term)list))` THEN
      SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[MEM; ALL; MAP] THEN
      GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`y:num`; `s:term`; `eev:(num#term)list`] THEN
      REWRITE_TAC[FST; SND; o_DEF] THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      ASM_CASES_TAC `x = y:num` THEN ASM_REWRITE_TAC[ASSOC] THEN
      MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `istriv env x t = Exception` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[OPTION_DISTINCT] THEN
      MP_TAC(SPECL [`env:(num#term)list`; `x:num`; `t:term`]
              BADLOOP_UNUNIFIABLE) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[unifies; ALL_APPEND; ALL] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN CONV_TAC TAUT; ALL_TAC] THEN
    ASM_CASES_TAC `istriv env x t = TT` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL
        [`env:(num#term)list`; `oth:(term#term)list`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[CALLORDER; CRIGHT] THEN
        DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!i. unifies i
              (APPEND (MAP (\(x,t). V x,t) env) (CONS (V x,t) oth)) =
            unifies i
              (APPEND (MAP (\(x,t). V x,t) env) oth)`
       (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(SPECL [`env:(num#term)list`; `x:num`; `t:term`]
              GOODLOOP_UNIFIABLE) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[unifies; ALL_APPEND; ALL] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN CONV_TAC TAUT;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
        [`CONS (x:num,t:term) env`; `oth:(term#term)list`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[CALLORDER] THEN DISJ1_TAC THEN
      REWRITE_TAC[MEASURE; MLEFT] THEN
      REWRITE_TAC[MAP; FST; SND; LENGTH] THEN
      MATCH_MP_TAC(ARITH_RULE
       `(a' = a) /\ (b' = b + 1) /\ b' <= a' ==> a' - b' < a - b`) THEN
      SUBGOAL_THEN
       `FVT(Fn 0 (CONS ((V o FST) (x,t:term)) (MAP (V o FST) env))) =
        x INSERT FVT(Fn 0 (MAP (V o FST) (env:(num#term)list)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FVT; MAP; LIST_UNION; o_THM; FST] THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `FVT(Fn 0 (CONS (V x) (MAP FST (oth:(term#term)list)))) =
        x INSERT FVT(Fn 0 (MAP FST oth))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FVT; MAP; LIST_UNION; o_THM; FST] THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `FVT(Fn 0 (CONS t (MAP SND env))) =
        FVT(t) UNION FVT(Fn 0 (MAP SND (env:(num#term)list)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FVT; MAP; LIST_UNION; o_THM; FST]; ALL_TAC] THEN
      SUBGOAL_THEN
       `FVT(Fn 0 (CONS t (MAP SND oth))) =
        FVT(t) UNION FVT(Fn 0 (MAP SND (oth:(term#term)list)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FVT; MAP; LIST_UNION; o_THM; FST]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; DISJ_ACI; IN_INSERT];
        SIMP_TAC[CARD_CLAUSES; FVT_FINITE; ADD1] THEN
        COND_CASES_TAC THEN REWRITE_TAC[] THEN
        UNDISCH_TAC
         `x IN FVT (Fn 0 (MAP (V o FST) (env:(num#term)list)))` THEN
        UNDISCH_TAC `~MEM x (MAP FST (env:(num#term)list))` THEN
        MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> b ==> c`) THEN
        SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
        REWRITE_TAC[FVT] THEN LIST_INDUCT_TAC THEN
        REWRITE_TAC[LIST_UNION; MEM; MAP; NOT_IN_EMPTY] THEN
        REWRITE_TAC[o_THM; FVT; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
        STRIP_TAC THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC CARD_SUBSET THEN
        REWRITE_TAC[FINITE_UNION; FVT_FINITE; FINITE_INSERT] THEN
        REWRITE_TAC[SUBSET; IN_UNION; IN_INSERT] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    ANTS_TAC THENL
     [MP_TAC(SPECL [`env:(num#term)list`; `x:num`; `t:term`] ISTRIV_WORKS) THEN
      ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[LOOPFREE_PRESERVE_EQ] THEN
      UNDISCH_TAC `CONFLICTFREE env` THEN
      REWRITE_TAC[CONFLICTFREE; LENGTH; FILTER] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:num` THEN
      ASM_CASES_TAC `x:num = y` THEN ASM_REWRITE_TAC[LENGTH] THEN
      MATCH_MP_TAC(ARITH_RULE `(x = 0) ==> y <= z ==> SUC x <= 1`) THEN
      UNDISCH_THEN `x:num = y` (SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC[LENGTH_EQ_NIL] THEN
      UNDISCH_TAC `~(MEM x (MAP FST (env:(num#term)list)))` THEN
      SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC[MEM; MAP; FILTER; NOT_CONS_NIL] THEN
      SUBST1_TAC(SYM(ISPEC `h:num#term` PAIR)) THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[FST; SND] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. unifies i (APPEND (MAP (\(x,t). V x,t) (CONS (x,t) env)) oth) =
          unifies i (APPEND (MAP (\(x,t). V x,t) env) (CONS (V x,t) oth))`
     (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[unifies; ALL_APPEND; ALL; MAP] THEN GEN_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC TAUT;

    FIRST_X_ASSUM(MP_TAC o SPECL
     [`env:(num#term)list`; `CONS (V x,Fn f fargs) oth`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[CALLORDER; CRIGHT] THEN
      REPEAT DISJ2_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[unifies; ALL_APPEND; ALL] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[EQ_SYM_EQ];

    COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_DISTINCT] THENL
     [ALL_TAC;
      REWRITE_TAC[unifies; ALL; ALL_APPEND] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[termsubst; term_INJ] THEN
      ASM_MESON_TAC[LENGTH_MAP]] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`env:(num#term)list`;
      `APPEND (ZIP fargs gargs) (oth:(term#term)list)`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[CALLORDER; CRIGHT] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. unifies i (APPEND (MAP (\(x,t). V x,t) env)
                            (APPEND (ZIP fargs gargs) oth)) =
          unifies i (APPEND (MAP (\(x,t). V x,t) env)
                            (CONS (Fn g fargs,Fn g gargs) oth))`
     (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `i:num->term` THEN REWRITE_TAC[unifies; ALL; ALL_APPEND] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[termsubst; term_INJ] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
    SPEC_TAC(`gargs:term list`,`gargs:term list`) THEN
    SPEC_TAC(`fargs:term list`,`fargs:term list`) THEN
    LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[LENGTH; ALL; MAP; NOT_SUC; ZIP] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_SIMP_TAC[SUC_INJ; CONS_11]]);;

(* ------------------------------------------------------------------------- *)
(* Constructively show that unifiers exist via "solve".                      *)
(* ------------------------------------------------------------------------- *)

let THE = new_recursive_definition option_RECURSION
  `THE(SOME x) = x`;;

let unifier = new_definition
  `unifier env =
     let sol = SOLVE [] env in ITLIST valmod sol V`;;

let ITLIST_VALMOD_LEMMA = prove
 (`!env x. CONFLICTFREE(env)
           ==> !t. (ITLIST valmod env V x = t) <=>
                   MEM (x,t) env \/ (t = V x) /\ ~(MEM x (MAP FST env))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONFLICTFREE] THEN
  DISCH_THEN(MP_TAC o SPEC `x:num`) THEN
  SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; LENGTH; ITLIST; MAP; MEM] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`h:num#term`,`h:num#term`) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`z:num`; `s:term`] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_CASES_TAC `z = x:num` THEN
  ASM_REWRITE_TAC[PAIR_EQ; LENGTH; valmod] THEN
  REWRITE_TAC[ARITH_RULE `SUC n <= 1 <=> (n = 0)`; LENGTH_EQ_NIL] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> ~c) /\ (b <=> b') ==> a ==> (b <=> b' \/ c)`) THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[EQ_SYM_EQ]] THEN
  DISCH_THEN(MP_TAC o AP_TERM `MEM (x:num,t':term)`) THEN
  REWRITE_TAC[MEM; MEM_FILTER] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let UNIFIER_WORKS = prove
 (`!env. LOOPFREE(env) /\ CONFLICTFREE(env)
         ==> unifies (unifier env) (MAP (\(x,t). V x,t) env)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[unifier] THEN LET_TAC  THEN
  MP_TAC(SPEC `env:(num#term)list` SOLVE_WORKS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `i = ITLIST valmod sol V` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SPEC `i:num->term`) MP_TAC) THEN
  DISCH_TAC THEN
  REWRITE_TAC[unifies; ALL_MAP; o_DEF] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM PAIRED_ETA_THM] THEN
  REWRITE_TAC[] THEN CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[termsubst; GSYM ALL_MEM] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `t:term`] THEN DISCH_TAC THEN
  EXPAND_TAC "i" THEN ASM_SIMP_TAC[ITLIST_VALMOD_LEMMA] THEN
  SUBGOAL_THEN `termsubst i t = t` (fun th -> ASM_REWRITE_TAC[th]) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM TERMSUBST_TRIV] THEN
  MATCH_MP_TAC TERMSUBST_VALUATION THEN X_GEN_TAC `z:num` THEN DISCH_TAC THEN
  EXPAND_TAC "i" THEN ASM_SIMP_TAC[ITLIST_VALMOD_LEMMA] THEN
  DISJ2_TAC THEN REWRITE_TAC[MEM_MAP] THEN
  ONCE_REWRITE_TAC[EXISTS_PAIR_THM] THEN ASM_MESON_TAC[FST]);;

let UNIFIER_MGU = prove
 (`!env. LOOPFREE(env) /\ CONFLICTFREE(env)
         ==> !i. unifies i (MAP (\(x,t). V x,t) env)
                 ==> (termsubst i =
                      termsubst i o
                      termsubst (ITLIST valmod env V))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  X_GEN_TAC `s:term` THEN REWRITE_TAC[TERMSUBST_TERMSUBST] THEN
  MATCH_MP_TAC TERMSUBST_VALUATION THEN X_GEN_TAC `y:num` THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[o_THM] THEN
  UNDISCH_TAC `unifies i (MAP (\(x,t). V x,t) env)` THEN
  REWRITE_TAC[unifies; ALL_MAP; o_DEF] THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM PAIRED_ETA_THM] THEN
  REWRITE_TAC[] THEN CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN
  SPEC_TAC(`env:(num#term)list`,`env:(num#term)list`) THEN
  REWRITE_TAC[termsubst] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; TERMSUBST_TRIV; termsubst] THEN
  SPEC_TAC(`h:num#term`,`h:num#term`) THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`z:num`; `s:term`] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[unifies; ALL; MAP] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_THEN `y = z:num` (SUBST_ALL_TAC o SYM) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence we can strengthen the main theorem.                                 *)
(* ------------------------------------------------------------------------- *)

let UNIFY_WORKS = prove
 (`!env eqs.
     LOOPFREE(env) /\ CONFLICTFREE(env)
     ==> ((unify (env,eqs) = NONE)
          ==> !i. ~(unifies i (APPEND (MAP (\(x,t). V x,t) env) eqs))) /\
         ((unify (env,eqs) = SOME ans)
          ==> LOOPFREE(ans) /\ CONFLICTFREE(ans) /\
              unifies (unifier ans) (APPEND (MAP (\(x,t). V x,t) env) eqs) /\
              !i. unifies i (APPEND (MAP (\(x,t). V x,t) env) eqs)
                  ==> (termsubst i = termsubst i o termsubst (unifier ans)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `env:(num#term)list,eqs:(term#term)list` UNIFY_WORKS_RAW) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `ans:(num#term)list`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[unifier] THEN LET_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPEC `ans:(num#term)list` SOLVE_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `ans:(num#term)list` UNIFIER_WORKS) THEN
  MP_TAC(SPEC `sol:(num#term)list` UNIFIER_MGU) THEN
  SUBGOAL_THEN `LOOPFREE(sol)` ASSUME_TAC THENL
   [REWRITE_TAC[LOOPFREE] THEN X_GEN_TAC `z:num` THEN
    ONCE_REWRITE_TAC[TC_RTC_CASES_R] THEN
    ONCE_REWRITE_TAC[RTC_CASES_R] THEN
    REWRITE_TAC[OCC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i. unifies i (MAP (\(x,t). V x,t) ans) =
                    unifies i (MAP (\(x,t). V x,t) sol)`
   (fun th -> SIMP_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[unifies; ALL_MAP; o_DEF] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ONCE_REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_REWRITE_TAC[termsubst]; ALL_TAC] THEN
  ASM_REWRITE_TAC[unifier] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Special case where there is no initial environment.                       *)
(* ------------------------------------------------------------------------- *)

let UNIFY_WORKS_SIMPLE = prove
 (`!eqs. ((unify ([],eqs) = NONE) ==> !i. ~(unifies i eqs)) /\
         ((unify ([],eqs) = SOME ans)
          ==> LOOPFREE(ans) /\ CONFLICTFREE(ans) /\
              unifies (unifier ans) eqs /\
              !i. unifies i eqs
                  ==> (termsubst i = termsubst i o termsubst (unifier ans)))`,
  GEN_TAC THEN MP_TAC(SPEC `[]:(num#term)list` UNIFY_WORKS) THEN
  REWRITE_TAC[MAP; APPEND] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[LOOPFREE; CONFLICTFREE; LENGTH; FILTER; ARITH] THEN
  ONCE_REWRITE_TAC[TC_CASES_L] THEN REWRITE_TAC[OCC; MEM]);;

(* ------------------------------------------------------------------------- *)
(* Slight variant: MGU of a set (not list of pairs) of formulas (not terms)  *)
(* ------------------------------------------------------------------------- *)

let Unifies_DEF = new_definition
  `Unifies i s <=> !p q. p IN s /\ q IN s ==> (formsubst i p = formsubst i q)`;;

let UNIFIES = prove
 (`Unifies i s <=> ?q. !p. p IN s ==> (formsubst i p = q)`,
  MESON_TAC[Unifies_DEF]);;

let UNIFIER_FORMPAIR_TERMLIST = prove
 (`!p q. qfree(p) /\ qfree(q)
         ==> ?l. !i. (formsubst i p = formsubst i q) <=> unifies i l`,
  let lemma = prove
   (`?l. !i. ~(unifies i l)`,
    EXISTS_TAC `[Fn 0 [], Fn 1 []]` THEN
    REWRITE_TAC[ALL; unifies] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[termsubst; term_INJ; ARITH]) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[qfree] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`f:num`; `fargs:term list`];
    MAP_EVERY X_GEN_TAC [`p:form`; `q:form`] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[qfree] THEN
  REWRITE_TAC[formsubst; form_DISTINCT; lemma] THENL
   [EXISTS_TAC `[]:(term#term)list` THEN REWRITE_TAC[unifies; ALL];
    MAP_EVERY X_GEN_TAC [`g:num`; `gargs:term list`] THEN
    REWRITE_TAC[form_INJ] THEN
    ASM_CASES_TAC `f:num = g` THEN ASM_REWRITE_TAC[lemma] THEN
    ASM_CASES_TAC `LENGTH(fargs:term list) = LENGTH(gargs:term list)` THENL
     [ALL_TAC; ASM_MESON_TAC[LENGTH_MAP; lemma]] THEN
    EXISTS_TAC `ZIP (fargs:term list) (gargs:term list)` THEN
    REWRITE_TAC[unifies] THEN X_GEN_TAC `i:num->term` THEN
    UNDISCH_TAC `LENGTH(fargs:term list) = LENGTH(gargs:term list)` THEN
    SPEC_TAC(`gargs:term list`,`gargs:term list`) THEN
    SPEC_TAC(`fargs:term list`,`fargs:term list`) THEN
    LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; NOT_SUC; MAP; ZIP; ALL; SUC_INJ] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC[CONS_11];
    MAP_EVERY X_GEN_TAC [`r:form`; `s:form`] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[form_INJ] THEN
    UNDISCH_TAC
     `!q. qfree q
          ==> (?l. !i. (formsubst i p = formsubst i q) <=> unifies i l)` THEN
    DISCH_THEN(MP_TAC o SPEC `r:form`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:(term#term)list`
     (fun th -> REWRITE_TAC[th])) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:form`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l2:(term#term)list`
     (fun th -> REWRITE_TAC[th])) THEN
    EXISTS_TAC `APPEND (l1:(term#term)list) l2` THEN
    REWRITE_TAC[unifies; ALL_APPEND]]);;

let UNIFIER_SUBTERMS = prove
 (`!A. FINITE A /\ (!p. p IN A ==> qfree p)
       ==> ?l. !i. Unifies i A = unifies i l`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = {(x:form,y) | x IN A /\ y IN A}` THEN
  SUBGOAL_THEN `!i. Unifies i A =
                    !p q. (p,q) IN B ==> (formsubst i p = formsubst i q)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [EXPAND_TAC "B" THEN
    REWRITE_TAC[IN_ELIM_THM; Unifies_DEF; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!p q. (p,q) IN B ==> qfree p /\ qfree q` MP_TAC THENL
   [EXPAND_TAC "B" THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(B:(form#form)->bool)` MP_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC FINITE_PRODUCT THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`B:(form#form)->bool`,`B:(form#form)->bool`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN MATCH_MP_TAC FINITE_INDUCT THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `[]:(term#term)list` THEN
    REWRITE_TAC[NOT_IN_EMPTY; ALL; unifies]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:form`; `q:form`; `B:(form#form)->bool`] THEN
  REWRITE_TAC[IN_INSERT; PAIR_EQ] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL;
           LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:(term#term)list`) THEN
  MP_TAC(SPECL [`p:form`; `q:form`] UNIFIER_FORMPAIR_TERMLIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:(term#term)list`) THEN
  EXISTS_TAC `APPEND (l:(term#term)list) m` THEN
  REWRITE_TAC[unifies; ALL_APPEND] THEN
  ASM_REWRITE_TAC[GSYM unifies] THEN REWRITE_TAC[CONJ_ACI]);;

let MGU_EXISTS = prove
 (`FINITE s /\ (!p. p IN s ==> qfree p)
   ==> ((?i. Unifies i s) <=>
        (?i. Unifies i s /\
             !j. Unifies j s
                 ==> !p. qfree p
                         ==> (formsubst j p = formsubst j (formsubst i p))))`,
  DISCH_THEN(X_CHOOSE_THEN `l:(term#term)list` (fun th -> REWRITE_TAC[th]) o
              MATCH_MP UNIFIER_SUBTERMS) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num->term` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  EXISTS_TAC `unifier(THE(unify([],l)))` THEN
  MP_TAC(GEN `ans:(num#term)list`
    (SPEC `l:(term#term)list` UNIFY_WORKS_SIMPLE)) THEN
  SPEC_TAC(`unify ([],l)`,`u:((num#term)list)option`) THEN
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[prove_constructors_distinct option_RECURSION;
              prove_constructors_injective option_RECURSION] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `u:(num#term)list` THEN
  DISCH_THEN(MP_TAC o SPEC `u:(num#term)list`) THEN REWRITE_TAC[THE] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `j:num->term` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[formsubst; qfree] THEN SIMP_TAC[] THEN
  REWRITE_TAC[GSYM MAP_o] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  ASM_REWRITE_TAC[o_THM; ALL_T]);;

let mgu = new_definition
  `mgu s = @i. Unifies i s /\
               !j. Unifies j s
                   ==> !p. qfree p
                           ==> (formsubst j p =
                                formsubst j (formsubst i p))`;;

let MGU = prove
 (`!s. FINITE s /\ (!p. p IN s ==> qfree p) /\ (?i. Unifies i s)
       ==> Unifies (mgu s) s /\
           !i. Unifies i s
               ==> !p. qfree p
                       ==> (formsubst i p =
                            formsubst i (formsubst (mgu s) p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mgu] THEN
  CONV_TAC SELECT_CONV THEN ASM_SIMP_TAC[GSYM MGU_EXISTS] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* General notion of an MGU.                                                 *)
(* ------------------------------------------------------------------------- *)

let FORMSUBST_TERMSUBST_LEMMA = prove
 (`(!p. qfree(p) ==> (formsubst i p = formsubst j (formsubst k p))) <=>
   (termsubst i = termsubst j o termsubst k)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `t:term` THEN FIRST_X_ASSUM(MP_TAC o SPEC `Atom p [t]`) THEN
    REWRITE_TAC[qfree; formsubst; MAP; form_INJ; CONS_11];
    MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[qfree] THEN
    SIMP_TAC[formsubst] THEN REWRITE_TAC[form_INJ; GSYM MAP_o] THEN
    GEN_TAC THEN MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC[o_THM; ALL_T]]);;

let ismgu = new_definition
  `ismgu s i <=> Unifies i s /\
                 !j. Unifies j s
                     ==> ?k. (termsubst j = termsubst k o termsubst i)`;;

let ISMGU = prove
 (`ismgu s i <=> Unifies i s /\
                 !j. Unifies j s
                     ==> ?k. !p. qfree(p)
                                 ==> (formsubst j p =
                                      formsubst k (formsubst i p))`,
  REWRITE_TAC[ismgu; FORMSUBST_TERMSUBST_LEMMA]);;

let ISMGU_MGU = prove
 (`!s. FINITE(s) /\ (!p. p IN s ==> qfree p) /\ (?i. Unifies i s)
       ==> ismgu s (mgu s)`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MGU) THEN
  ASM_REWRITE_TAC[ISMGU] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Renaming. Note that we assume a bijection; the usual definition demands   *)
(* only the existence of a left inverse, but then you need to be explicit    *)
(* about the fact that the support is finite, hence the right inverse exists *)
(* anyway.                                                                   *)
(* ------------------------------------------------------------------------- *)

let renaming = new_definition
  `renaming i <=> ?j. (termsubst j o termsubst i = I) /\
                      (termsubst i o termsubst j = I)`;;

let RENAMING = prove
 (`renaming i ==> (!x. ?y. i(x) = V y) /\
                  (!x x'. (i(x') = i(x)) ==> (x' = x))`,
  REWRITE_TAC[renaming; FUN_EQ_THM; o_THM; I_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num->term` (ASSUME_TAC o CONJUNCT1)) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `V x`) THEN
    REWRITE_TAC[termsubst] THEN
    MESON_TAC[term_CASES; termsubst; term_DISTINCT];
    MAP_EVERY X_GEN_TAC [`x1:num`; `x2:num`] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `V x1` th) THEN
                            MP_TAC(SPEC `V x2` th)) THEN
    REWRITE_TAC[termsubst] THEN MESON_TAC[term_INJ]]);;
