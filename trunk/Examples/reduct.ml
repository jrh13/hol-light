(* ========================================================================= *)
(* General "reduction" properties of binary relations,                       *)
(* ========================================================================= *)

needs "Library/rstc.ml";;

(* ------------------------------------------------------------------------- *)
(* Field of a binary relation.                                               *)
(* ------------------------------------------------------------------------- *)

let FL = new_definition
  `FL(R) x <=> (?y:A. R x y) \/ (?y. R y x)`;;

(* ------------------------------------------------------------------------ *)
(* Normality of a term w.r.t. a reduction relation                          *)
(* ------------------------------------------------------------------------ *)

let NORMAL = new_definition
  `NORMAL(R:A->A->bool) x <=> ~(?y. R x y)`;;

(* ------------------------------------------------------------------------ *)
(* Full Church-Rosser property.                                             *)
(*                                                                          *)
(* Note that we deviate from most term rewriting literature which call this *)
(* the "diamond property" and calls a relation "Church-Rosser" iff its RTC  *)
(* has the diamond property. But this seems simpler and more natural.       *)
(* ------------------------------------------------------------------------ *)

let CR = new_definition
  `CR(R:A->A->bool) <=> !x y1 y2. R x y1 /\ R x y2 ==> ?z. R y1 z /\ R y2 z`;;

(* ------------------------------------------------------------------------ *)
(* Weak Church-Rosser property, i.e. the rejoining may take several steps.  *)
(* ------------------------------------------------------------------------ *)

let WCR = new_definition
  `WCR(R:A->A->bool) <=>
   !x y1 y2. R x y1 /\ R x y2 ==> ?z. RTC R y1 z /\ RTC R y2 z`;;

(* ------------------------------------------------------------------------ *)
(* (Weak) normalization: every term has a normal form.                      *)
(* ------------------------------------------------------------------------ *)

let WN = new_definition
  `WN(R:A->A->bool) <=> !x. ?y. RTC R x y /\ NORMAL(R) y`;;

(* ------------------------------------------------------------------------ *)
(* Strong normalization: every reduction sequence terminates (Noetherian)   *)
(* ------------------------------------------------------------------------ *)

let SN = new_definition
  `SN(R:A->A->bool) <=> ~(?seq. !n. R (seq n) (seq (SUC n)))`;;

(* ------------------------------------------------------------------------- *)
(* Definition of a tree.                                                     *)
(* ------------------------------------------------------------------------- *)

let TREE = new_definition
  `TREE(R:A->A->bool) <=>
        (!y. ~(TC R y y)) /\
        ?a. a IN FL(R) /\
            !y. y IN FL(R) ==> (y = a) \/ TC R a y /\ ?!x. R x y`;;

(* ------------------------------------------------------------------------- *)
(* Local finiteness (finitely branching).                                    *)
(* ------------------------------------------------------------------------- *)

let LF = new_definition
  `LF(R:A->A->bool) <=> !x. FINITE {y | R x y}`;;

(* ------------------------------------------------------------------------- *)
(* Wellfoundedness apparatus for SN relations.                               *)
(* ------------------------------------------------------------------------- *)

let SN_WF = prove
 (`!R:A->A->bool. SN(R) <=> WF(INV R)`,
  REWRITE_TAC[SN; WF_DCHAIN; INV]);;

let SN_PRESERVE = prove
 (`!R:A->A->bool. SN(R) <=> !P. (!x. P x ==> ?y. P y /\ R x y) ==> ~(?x. P x)`,
  REWRITE_TAC[SN_WF; WF; INV] THEN MESON_TAC[]);;

let SN_NOETHERIAN = prove
 (`!R:A->A->bool. SN(R) <=> !P. (!x. (!y. R x y ==> P y) ==> P x) ==> !x. P x`,
  REWRITE_TAC[WF_IND; SN_WF; INV]);;

(* ------------------------------------------------------------------------ *)
(* Normality and weak normalization is preserved by transitive closure.     *)
(* ------------------------------------------------------------------------ *)

let NORMAL_TC = prove
 (`!R:A->A->bool. NORMAL(TC R) x <=> NORMAL(R) x`,
  REWRITE_TAC[NORMAL] THEN MESON_TAC[TC_CASES_R; TC_INC]);;

let NORMAL_RTC = prove
 (`!R:A->A->bool. NORMAL(R) x ==> !y. RTC R x y <=> (x = y)`,
  ONCE_REWRITE_TAC[GSYM NORMAL_TC] THEN
  REWRITE_TAC[NORMAL; RTC; RC_EXPLICIT] THEN MESON_TAC[]);;

let WN_TC = prove
 (`!R:A->A->bool. WN(TC R) <=> WN R`,
  REWRITE_TAC[WN; NORMAL_TC; RTC; TC_IDEMP]);;

(* ------------------------------------------------------------------------- *)
(* Wellfoundedness and strong normalization are too.                         *)
(* ------------------------------------------------------------------------- *)

let WF_TC = prove
 (`!R:A->A->bool. WF(TC R) <=> WF(R)`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[WF_SUBSET; TC_INC];
    REWRITE_TAC[WF] THEN DISCH_TAC THEN X_GEN_TAC `P:A->bool` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\y:A. ?z. P z /\ TC(R) z y`) THEN
    REWRITE_TAC[] THEN MESON_TAC[TC_CASES_L]]);;

(******************* Alternative --- intuitionistic --- proof

let WF_TC = prove
 (`!R:A->A->bool. WF(TC R) <=> WF(R)`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[WF_SUBSET; TC_INC];
    REWRITE_TAC[WF_IND]] THEN
  DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\z:A. !u:A. TC(R) u z ==> P(u)`) THEN
  REWRITE_TAC[] THEN MESON_TAC[TC_CASES_L]);;

let WF_TC_EXPLICIT = prove
 (`!R:A->A->bool. WF(R) ==> WF(TC(R))`,
  GEN_TAC THEN REWRITE_TAC[WF_IND] THEN DISCH_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\z:A. !u:A. TC(R) u z ==> P(u)`) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN X_GEN_TAC `z:A` THEN
  FIRST_ASSUM MATCH_MP_TAC THEN SPEC_TAC(`z:A`,`z:A`) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o REDEPTH_CONV)
   [RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  DISCH_TAC THEN X_GEN_TAC `u:A` THEN
  ONCE_REWRITE_TAC[TC_CASES_L] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC(ASSUME `!x:A. (!y. TC R y x ==> P y) ==> P x`) THEN
    X_GEN_TAC `v:A` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `u:A` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `w:A` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

***********************)

let SN_TC = prove
 (`!R:A->A->bool. SN(TC R) <=> SN R`,
  GEN_TAC THEN REWRITE_TAC[SN_WF; GSYM TC_INV; WF_TC]);;

(* ------------------------------------------------------------------------ *)
(* Strong normalization implies normalization                               *)
(* ------------------------------------------------------------------------ *)

let SN_WN = prove
 (`!R:A->A->bool. SN(R) ==> WN(R)`,
  GEN_TAC THEN REWRITE_TAC[SN_WF; WF; WN] THEN DISCH_TAC THEN
  X_GEN_TAC `a:A` THEN POP_ASSUM(MP_TAC o SPEC `\y:A. RTC R a y`) THEN
  REWRITE_TAC[INV; NORMAL] THEN MESON_TAC[RTC_REFL; RTC_TRANS_L]);;

(* ------------------------------------------------------------------------ *)
(* Reflexive closure preserves Church-Rosser property (pretty trivial)      *)
(* ------------------------------------------------------------------------ *)

let RC_CR = prove
 (`!R:A->A->bool. CR(R) ==> CR(RC R)`,
  REWRITE_TAC[CR; RC_EXPLICIT] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* The strip lemma leads us halfway to the fact that transitive        x    *)
(* closure preserves the Church-Rosser property. It's no harder       / \   *)
(* to prove it for two separate reduction relations. This then       /   y2 *)
(* allows us to prove the desired theorem simply by using the       /    /  *)
(* strip lemma twice with a bit of conjunct-swapping.              y1   /   *)
(*                                                                   \ /    *)
(* The diagram on the right shows the use of the variables.           z     *)
(* ------------------------------------------------------------------------ *)

let STRIP_LEMMA = prove
 (`!R S. (!x y1 y2.    R x y1 /\ S x y2 ==> ?z:A. S y1 z /\    R y2 z) ==>
         (!x y1 y2. TC R x y1 /\ S x y2 ==> ?z:A. S y1 z /\ TC R y2 z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> (b ==> c)`] THEN
  REWRITE_TAC[GSYM RIGHT_IMP_FORALL_THM] THEN
  MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC[TC_INC; TC_TRANS]);;

(* ------------------------------------------------------------------------ *)
(* Transitive closure preserves Church-Rosser property.                     *)
(* ------------------------------------------------------------------------ *)

let TC_CR = prove
 (`!R:A->A->bool. CR(R) ==> CR(TC R)`,
  GEN_TAC THEN REWRITE_TAC[CR] THEN DISCH_TAC THEN
  MATCH_MP_TAC STRIP_LEMMA THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  RULE_INDUCT_TAC STRIP_LEMMA THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Reflexive transitive closure preserves Church-Rosser property.           *)
(* ------------------------------------------------------------------------ *)

let RTC_CR = prove
 (`!R:A->A->bool. CR(R) ==> CR(RTC R)`,
  REWRITE_TAC[RTC] THEN MESON_TAC[RC_CR; TC_CR]);;

(* ------------------------------------------------------------------------ *)
(* Equivalent `Church-Rosser` property for the equivalence relation.        *)
(* ------------------------------------------------------------------------ *)

let STC_CR = prove
 (`!R:A->A->bool. CR(RTC R) <=>
        !x y. RSTC R x y ==> ?z:A. RTC R x z /\ RTC R y z`,
  GEN_TAC THEN REWRITE_TAC[CR] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC RSTC_INDUCT THEN
    ASM_MESON_TAC[RTC_REFL; RTC_INC; RTC_TRANS];
    MESON_TAC[RSTC_INC_RTC; RSTC_SYM; RSTC_TRANS]]);;

(* ------------------------------------------------------------------------ *)
(* Under normalization, Church-Rosser is equivalent to uniqueness of NF     *)
(* ------------------------------------------------------------------------ *)

let NORM_CR = prove
 (`!R:A->A->bool. WN(R) ==>
     (CR(RTC R) <=> (!x y1 y2. RTC R x y1 /\ NORMAL(R) y1 /\
                               RTC R x y2 /\ NORMAL(R) y2 ==> (y1 = y2)))`,
  GEN_TAC THEN REWRITE_TAC[CR; WN] THEN DISCH_TAC THEN EQ_TAC THENL
   [MESON_TAC[NORMAL_RTC]; ASM_MESON_TAC[RTC_TRANS]]);;

(* ------------------------------------------------------------------------ *)
(* Normalizing and Church-Rosser iff every term has a unique normal form    *)
(* ------------------------------------------------------------------------ *)

let CR_NORM = prove
 (`!R:A->A->bool. WN(R) /\ CR(RTC R) <=> !x. ?!y. RTC R x y /\ NORMAL(R) y`,
  GEN_TAC THEN ONCE_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  REWRITE_TAC[FORALL_AND_THM; GSYM WN] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP NORM_CR th]) THEN
  REWRITE_TAC[CONJ_ASSOC]);;

(* ------------------------------------------------------------------------ *)
(* Newman's lemma: weak Church-Rosser plus                   x              *)
(* strong normalization implies full Church-                / \             *)
(* Rosser. By the above (and SN ==> WN) it                 z1 z2            *)
(* is sufficient to show normal forms are                 / | | \           *)
(* unique. We use the Noetherian induction               /  \ /  \          *)
(* form of SN, so we need only prove that if            /    z    \         *)
(* some term has multiple normal forms, so             /     |     \        *)
(* does a `successor`. See the diagram on the         /      |      \       *)
(* right for the use of variables.                   y1      w       y2     *)
(* ------------------------------------------------------------------------ *)

let NEWMAN_LEMMA = prove
 (`!R:A->A->bool. SN(R) /\ WCR(R) ==> CR(RTC R)`,
  GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP SN_WN) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[WN] th) THEN MP_TAC th) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP NORM_CR th]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[WF_IND; SN_WF]) THEN
  REWRITE_TAC[INV] THEN X_GEN_TAC `x:A` THEN REPEAT STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`RTC R (x:A) y1`; `RTC R (x:A) y2`] THEN
  ONCE_REWRITE_TAC[RTC_CASES_R] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `z2:A`)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `z1:A`)) THENL
   [ASM_MESON_TAC[];ASM_MESON_TAC[NORMAL];ASM_MESON_TAC[NORMAL]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [WCR]) THEN
  ASM_MESON_TAC[RTC_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* A variant of Koenig's lemma.                                              *)
(* ------------------------------------------------------------------------- *)

let LF_TC_FINITE = prove
 (`!R. LF(R) /\ SN(R) ==> !x:A. FINITE {y | TC(R) x y}`,
  GEN_TAC THEN REWRITE_TAC[LF] THEN STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[WF_IND; SN_WF; INV]) THEN
  GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN
    `{y:A | TC(R) x y} = {y | R x y} UNION
                         (UNIONS { s | ?z. R x z /\ (s = {y | TC(R) z y})})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIONS] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[IN] THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [TC_CASES_R] THEN
    AP_TERM_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FINITE_UNION; FINITE_UNIONS] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\z:A. {y | TC R z y}`; `{z | (R:A->A->bool) x z}`]
                  FINITE_IMAGE_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN; IN_ELIM_THM];
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [IN_ELIM_THM] THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let SN_NOLOOP = prove
 (`!R:A->A->bool. SN(R) ==> !z. ~(TC(R) z z)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM SN_TC] THEN
  SPEC_TAC(`TC(R:A->A->bool)`,`R:A->A->bool`) THEN
  GEN_TAC THEN REWRITE_TAC[SN_WF; INV; WF] THEN
  DISCH_THEN(fun th -> GEN_TAC THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. x = z`) THEN
  REWRITE_TAC[] THEN MESON_TAC[]);;

let RELPOW_RTC = prove
 (`!R:A->A->bool. !n x y. RELPOW n R x y ==> RTC(R) x y`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[RELPOW] THEN
  ASM_MESON_TAC[RTC_REFL; RTC_TRANS_L]);;

let RTC_TC_LEMMA = prove
 (`!R x:A. {y:A | RTC(R) x y} = x INSERT {y:A | TC(R) x y}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
  REWRITE_TAC[RTC; RC_EXPLICIT; DISJ_ACI; EQ_SYM_EQ]);;

let HAS_SIZE_SUBSET = prove
 (`!s:A->bool t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ s SUBSET t ==> m <= n`,
  REWRITE_TAC[HAS_SIZE] THEN MESON_TAC[CARD_SUBSET]);;

let FC_FINITE_BOUND_LEMMA = prove
 (`!R. (!z. ~(TC R z z))
       ==> !n. {y:A | RTC(R) x y} HAS_SIZE n
               ==> !m y. RELPOW m R x y ==> m <= n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC o
    REWRITE_RULE[RELPOW_SEQUENCE]) THEN
  SUBGOAL_THEN `!i. i <= m ==> RELPOW i R (x:A) (f i)` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[RELPOW] THEN
    REWRITE_TAC[LE_SUC_LT] THEN ASM_MESON_TAC[LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `{z:A | ?i:num. i < m /\ (z = f i)} SUBSET {y | RTC R x y}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[RELPOW_RTC; LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p <= m ==> {z:A | ?i. i < p /\ (z = f i)} HAS_SIZE p`
  (fun th -> ASSUME_TAC(MATCH_MP th (SPEC `m:num` LE_REFL))) THENL
   [ALL_TAC;
    MATCH_MP_TAC HAS_SIZE_SUBSET THEN
    EXISTS_TAC `{z:A | ?i. i < m /\ (z = f i)}` THEN
    EXISTS_TAC `{y:A | RTC(R) x y}` THEN ASM_REWRITE_TAC[]] THEN
  INDUCT_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[HAS_SIZE_0; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `{z:A | ?i. i < SUC p /\ (z = f i)} =
                f(p) INSERT {z | ?i. i < p /\ (z = f i)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    REWRITE_TAC[LT] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE; CARD_CLAUSES; SUC_INJ] THEN
  SUBGOAL_THEN `{z:A | ?i. i < p /\ (z = f i)} HAS_SIZE p` MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `SUC p <= m` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT2 CARD_CLAUSES) th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FINITE_INSERT] THEN
  UNDISCH_TAC `f p IN {z:A | ?i:num. i < p /\ (z = f i)}` THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `q:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `TC(R) ((f:num->A) q) (f p)` (fun th -> ASM_MESON_TAC[th]) THEN
  UNDISCH_TAC `SUC p <= m` THEN UNDISCH_TAC `q < p` THEN
  REWRITE_TAC[LT_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
    MATCH_MP_TAC TC_INC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `SUC (SUC q) <= m` THEN ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC TC_TRANS_L THEN
    EXISTS_TAC `(f:num->A)(q + SUC d)` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[ADD_CLAUSES]] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `SUC (q + SUC (SUC d)) <= m` THEN ARITH_TAC]);;

let FC_FINITE_BOUND = prove
 (`!R (x:A). FINITE {y | RTC(R) x y} /\
             (!z. ~(TC R z z))
             ==> ?N. !n y. RELPOW n R x y ==> n <= N`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_TAC THEN EXISTS_TAC `CARD {y:A | RTC(R) x y}` THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP FC_FINITE_BOUND_LEMMA) THEN
  ASM_REWRITE_TAC[HAS_SIZE]);;

let BOUND_SN = prove
 (`!R. (!x:A. ?N. !n y. RELPOW n R x y ==> n <= N) ==> SN(R)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SN_WF; WF_DCHAIN; INV] THEN
  DISCH_THEN(X_CHOOSE_TAC `f:num->A`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(f:num->A) 0`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num`
   (MP_TAC o SPECL [`SUC N`; `f(SUC N):A`])) THEN
  REWRITE_TAC[GSYM NOT_LT; LT] THEN
  SUBGOAL_THEN `!n. RELPOW n R (f 0 :A) (f n)` (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[RELPOW] THEN ASM_MESON_TAC[]);;

let LF_SN_BOUND = prove
 (`!R. LF(R) ==> (SN(R) <=> !x:A. ?N. !n y. RELPOW n R x y ==> n <= N)`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN REWRITE_TAC[BOUND_SN] THEN
  DISCH_TAC THEN GEN_TAC THEN MATCH_MP_TAC FC_FINITE_BOUND THEN CONJ_TAC THENL
   [SPEC_TAC(`x:A`,`x:A`) THEN REWRITE_TAC[RTC_TC_LEMMA; FINITE_INSERT] THEN
    MATCH_MP_TAC LF_TC_FINITE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SN_NOLOOP THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Koenig's lemma.                                                           *)
(* ------------------------------------------------------------------------- *)

let TREE_FL = prove
 (`!R. TREE(R) ==> ?a:A. FL(R) = {y | RTC(R) a y}`,
  GEN_TAC THEN REWRITE_TAC[TREE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `a:A` THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[RTC; RC_EXPLICIT] THEN
    MESON_TAC[]; ONCE_REWRITE_TAC[RTC_CASES_L] THEN ASM_MESON_TAC[IN; FL]]);;

let KOENIG_LEMMA = prove
 (`!R:A->A->bool. TREE(R) /\ LF(R) /\ SN(R) ==> FINITE (FL R)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` SUBST1_TAC o MATCH_MP TREE_FL) THEN
  REWRITE_TAC[RTC_TC_LEMMA; FINITE_INSERT] THEN
  SPEC_TAC(`a:A`,`a:A`) THEN MATCH_MP_TAC LF_TC_FINITE THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Rephrasing in terms of joinability.                                       *)
(* ------------------------------------------------------------------------- *)

let JOINABLE = new_definition
  `JOINABLE R s t <=> ?u. RTC R s u /\ RTC R t u`;;

let JOINABLE_REFL = prove
 (`!R t. JOINABLE R t t`,
  REWRITE_TAC[JOINABLE] THEN MESON_TAC[RTC_CASES]);;

let JOINABLE_SYM = prove
 (`!R s t. JOINABLE R s t <=> JOINABLE R t s`,
  REWRITE_TAC[JOINABLE] THEN MESON_TAC[]);;

let JOINABLE_TRANS_R = prove
 (`!R s t u. R s t /\ JOINABLE R t u ==> JOINABLE R s u`,
  REWRITE_TAC[JOINABLE] THEN MESON_TAC[RTC_CASES_R]);;

let CR_RSTC_JOINABLE = prove
 (`!R. CR(RTC R) ==> !x:A y. RSTC(R) x y <=> JOINABLE(R) x y`,
  GEN_TAC THEN REWRITE_TAC[STC_CR; JOINABLE] THEN
  ASM_MESON_TAC[RSTC_TRANS; RSTC_SYM; RSTC_INC_RTC]);;

(* ------------------------------------------------------------------------- *)
(* CR is equivalent to transitivity of joinability.                          *)
(* ------------------------------------------------------------------------- *)

let JOINABLE_TRANS = prove
 (`!R. CR(RTC R) <=>
       !x y z. JOINABLE(R) x y /\ JOINABLE(R) y z ==> JOINABLE(R) x z`,
  REWRITE_TAC[CR; JOINABLE] THEN MESON_TAC[RTC_REFL; RTC_TRANS; RTC_SYM]);;
