(* ========================================================================= *)
(* #88: Formula for the number of derangements: round[n!/e]                  *)
(* ========================================================================= *)

needs "Library/transc.ml";;
needs "Library/calc_real.ml";;
needs "Library/floor.ml";;

let PAIR_BETA_THM = GEN_BETA_CONV `(\(x,y). P x y) (a,b)`;;

(* ------------------------------------------------------------------------- *)
(* Domain and range of a relation.                                           *)
(* ------------------------------------------------------------------------- *)

let domain = new_definition
 `domain r = {x | ?y. r(x,y)}`;;

let range = new_definition
 `range r = {y | ?x. r(x,y)}`;;

(* ------------------------------------------------------------------------- *)
(* Relational composition.                                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("%",(26, "right"));;

let compose = new_definition
 `(r % s) (x,y) <=> ?z. r(x,z) /\ s(z,y)`;;

(* ------------------------------------------------------------------------- *)
(* Identity relation on a domain.                                            *)
(* ------------------------------------------------------------------------- *)

let id = new_definition
 `id(s) (x,y) <=> x IN s /\ x = y`;;

(* ------------------------------------------------------------------------- *)
(* Converse relation.                                                        *)
(* ------------------------------------------------------------------------- *)

let converse = new_definition
 `converse(r) (x,y) = r(y,x)`;;

(* ------------------------------------------------------------------------- *)
(* Transposition.                                                            *)
(* ------------------------------------------------------------------------- *)

let swap = new_definition
 `swap(a,b) (x,y) <=> x = a /\ y = b \/ x = b /\ y = a`;;

(* ------------------------------------------------------------------------- *)
(* When a relation "pairs up" two sets bijectively.                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("pairsup",(12,"right"));;

let pairsup = new_definition
 `r pairsup (s,t) <=> (r % converse(r) = id(s)) /\ (converse(r) % r = id(t))`;;

(* ------------------------------------------------------------------------- *)
(* Special case of a permutation.                                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("permutes",(12,"right"));;

let permutes = new_definition
 `r permutes s <=> r pairsup (s,s)`;;

(* ------------------------------------------------------------------------- *)
(* Even more special case of derangement.                                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("deranges",(12,"right"));;

let deranges = new_definition
 `r deranges s <=> r permutes s /\ !x. ~(r(x,x))`;;

(* ------------------------------------------------------------------------- *)
(* Trivial tactic for properties of relations.                               *)
(* ------------------------------------------------------------------------- *)

let REL_TAC =
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM; PAIR_BETA_THM;
              permutes; pairsup; domain; range; compose; id; converse; swap;
              deranges; IN_INSERT; IN_DELETE; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  REWRITE_TAC[IN; EMPTY; INSERT; DELETE; UNION; IN_ELIM_THM; PAIR_EQ;
              id; converse; swap] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  ASM_MESON_TAC[];;

let REL_RULE tm = prove(tm,REL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some general properties of relations.                                     *)
(* ------------------------------------------------------------------------- *)

let CONVERSE_COMPOSE = prove
 (`!r s. converse(r % s) = converse(s) % converse(r)`,
  REL_TAC);;

let CONVERSE_CONVERSE = prove
 (`!r. converse(converse r) = r`,
  REL_TAC);;

(* ------------------------------------------------------------------------- *)
(* More "explicit" definition of pairing and permutation.                    *)
(* ------------------------------------------------------------------------- *)

let PAIRSUP_EXPLICIT = prove
 (`!p s t.
        p pairsup (s,t) <=>
        (!x y. p(x,y) ==> x IN s /\ y IN t) /\
        (!x. x IN s ==> ?!y. y IN t /\ p(x,y)) /\
        (!y. y IN t ==> ?!x. x IN s /\ p(x,y))`,
  REL_TAC);;

let PERMUTES_EXPLICIT = prove
 (`!p s. p permutes s <=>
         (!x y. p(x,y) ==> x IN s /\ y IN s) /\
         (!x. x IN s ==> ?!y. y IN s /\ p(x,y)) /\
         (!y. y IN s ==> ?!x. x IN s /\ p(x,y))`,
  REL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Other low-level properties.                                               *)
(* ------------------------------------------------------------------------- *)

let PAIRSUP_DOMRAN = prove
 (`!p s t. p pairsup (s,t) ==> domain p = s /\ range p = t`,
  REL_TAC);;

let PERMUTES_DOMRAN = prove
 (`!p s. p permutes s ==> domain p = s /\ range p = s`,
  REL_TAC);;

let PAIRSUP_FUNCTIONAL = prove
 (`!p s t. p pairsup (s,t) ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`,
  REL_TAC);;

let PERMUTES_FUNCTIONAL = prove
 (`!p s. p permutes s ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`,
  REL_TAC);;

let PAIRSUP_COFUNCTIONAL = prove
 (`!p s t. p pairsup (s,t) ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`,
  REL_TAC);;

let PERMUTES_COFUNCTIONAL = prove
 (`!p s. p permutes s ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`,
  REL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some more abstract properties.                                            *)
(* ------------------------------------------------------------------------- *)

let PAIRSUP_ID = prove
 (`!s. id(s) pairsup (s,s)`,
  REL_TAC);;

let PERMUTES_ID = prove
 (`!s. id(s) permutes s`,
  REL_TAC);;

let PAIRSUP_CONVERSE = prove
 (`!p s t. p pairsup (s,t) ==> converse(p) pairsup (t,s)`,
  REL_TAC);;

let PERMUTES_CONVERSE = prove
 (`!p s. p permutes s ==> converse(p) permutes s`,
  REL_TAC);;

let PAIRSUP_COMPOSE = prove
 (`!p p' s t u. p pairsup (s,t) /\ p' pairsup (t,u) ==> (p % p') pairsup (s,u)`,
  REL_TAC);;

let PERMUTES_COMPOSE = prove
 (`!p p' s. p permutes s /\ p' permutes s ==> (p % p') permutes s`,
  REL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Transpositions are permutations.                                          *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_SWAP = prove
 (`swap(a,b) permutes {a,b}`,
  REL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Clausal theorems for cases on first set.                                  *)
(* ------------------------------------------------------------------------- *)

let PAIRSUP_EMPTY = prove
 (`p pairsup ({},{}) <=> (p = {})`,
  REL_TAC);;

let PAIRSUP_INSERT = prove
 (`!x:A s t:B->bool p.
        p pairsup (x INSERT s,t) <=>
          if x IN s then p pairsup (s,t)
          else ?y q. y IN t /\ p = (x,y) INSERT q /\ q pairsup (s,t DELETE y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SET_RULE `x IN s ==> x INSERT s = s`] THEN EQ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `?y. y IN t /\ p(x:A,y:B)` MP_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  EXISTS_TAC `p DELETE (x:A,y:B)` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Number of pairings and permutations.                                      *)
(* ------------------------------------------------------------------------- *)

let NUMBER_OF_PAIRINGS = prove
 (`!n s:A->bool t:B->bool.
        s HAS_SIZE n /\ t HAS_SIZE n
        ==> {p | p pairsup (s,t)} HAS_SIZE (FACT n)`,
  let lemma = prove
   (`{p | ?y. y IN t /\ A y p} = UNIONS {{p | A y p} | y IN t} /\
     {p | ?q. p = (a,y) INSERT q /\ A y q} =
           IMAGE (\q. (a,y) INSERT q) {q | A y q}`,
    CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS; IN_IMAGE] THEN SET_TAC[]) in
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[HAS_SIZE_CLAUSES] THEN
    SIMP_TAC[PAIRSUP_EMPTY; SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH; FACT];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [HAS_SIZE_CLAUSES] THEN
  REWRITE_TAC[HAS_SIZE_SUC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[PAIRSUP_INSERT; RIGHT_EXISTS_AND_THM; lemma; FACT] THEN
  MATCH_MP_TAC HAS_SIZE_UNIONS THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE_SUC];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_SIMP_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC]);;

let NUMBER_OF_PERMUTATIONS = prove
 (`!s n. s HAS_SIZE n ==> {p | p permutes s} HAS_SIZE (FACT n)`,
  SIMP_TAC[permutes; NUMBER_OF_PAIRINGS]);;

(* ------------------------------------------------------------------------- *)
(* Number of derangements (we need to justify this later).                   *)
(* ------------------------------------------------------------------------- *)

let derangements = define
 `(derangements 0 = 1) /\
  (derangements 1 = 0) /\
  (derangements(n + 2) = (n + 1) * (derangements n + derangements(n + 1)))`;;

let DERANGEMENT_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Expanding a derangement.                                                  *)
(* ------------------------------------------------------------------------- *)

let DERANGEMENT_ADD2 = prove
 (`!p s x y.
        p deranges s /\ ~(x IN s) /\ ~(y IN s) /\ ~(x = y)
        ==> ((x,y) INSERT (y,x) INSERT p) deranges (x INSERT y INSERT s)`,
  REL_TAC);;

let DERANGEMENT_ADD1 = prove
 (`!p s y x. p deranges s /\ ~(y IN s) /\ p(x,z)
             ==> ((x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
                 deranges (y INSERT s)`,
  REL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Number of derangements.                                                   *)
(* ------------------------------------------------------------------------- *)

let DERANGEMENT_EMPTY = prove
 (`!p. p deranges {} <=> p = {}`,
  REL_TAC);;

let DERANGEMENT_SING = prove
 (`!x p. ~(p deranges {x})`,
  REL_TAC);;

let NUMBER_OF_DERANGEMENTS = prove
 (`!n s:A->bool. s HAS_SIZE n ==> {p | p deranges s} HAS_SIZE (derangements n)`,
  MATCH_MP_TAC DERANGEMENT_INDUCT THEN REWRITE_TAC[derangements] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `{}:A#A->bool` THEN
    ASM_REWRITE_TAC[DERANGEMENT_EMPTY; EXTENSION; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_SING] THEN MESON_TAC[MEMBER_NOT_EMPTY];
    CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[DERANGEMENT_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN X_GEN_TAC `t:A->bool` THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(n + 1)`; HAS_SIZE_CLAUSES] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `{p | p deranges (x:A INSERT s)} =
        (IMAGE (\(y,p). (x,y) INSERT (y,x) INSERT p)
               {(y,p) | y IN s /\ p IN {p | p deranges (s DELETE y)}}) UNION
        (IMAGE (\(y,p). let z = @z. p(x,z) in
                        (x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
               {(y,p) | y IN s /\
                        p IN {p | p deranges (x INSERT (s DELETE y))}})`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[TAUT `(a <=> b) <=> (b ==> a) /\ (a ==> b)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNION; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`;
                  FORALL_AND_THM; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[FORALL_PAIR_THM; PAIR_BETA_THM; IN_ELIM_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
      CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`y:A`; `p:A#A->bool`] THEN
      STRIP_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
         `y IN s ==> s = y INSERT (s DELETE y)`)) THEN
        MATCH_MP_TAC DERANGEMENT_ADD2 THEN ASM_REWRITE_TAC[IN_DELETE] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      ABBREV_TAC `z = @z. p(x:A,z:A)` THEN
      SUBGOAL_THEN `(p:A#A->bool)(x:A,z:A)` STRIP_ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
        CONV_TAC SELECT_CONV THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `z:A IN s` STRIP_ASSUME_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      SUBGOAL_THEN `(x:A) INSERT s = y INSERT (x INSERT (s DELETE y))`
      SUBST1_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC DERANGEMENT_ADD1 THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[IN_DELETE; IN_INSERT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `p:A#A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?y. y IN s /\ p(x:A,y:A)` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN ASM_CASES_TAC `(p:A#A->bool)(y,x)` THENL
     [DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `y:A,(p DELETE (y,x)) DELETE (x:A,y:A)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[PAIR_BETA_THM] THEN MAP_EVERY UNDISCH_TAC
         [`(p:A#A->bool)(x,y)`; `(p:A#A->bool)(y,x)`] THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `?z. p(y:A,z:A)` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `z:A IN s` ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_BETA_THM] THEN
    EXISTS_TAC `y:A` THEN
    EXISTS_TAC `(x:A,z:A) INSERT ((p DELETE (x,y)) DELETE (y,z))` THEN
    SUBGOAL_THEN
     `(@w:A. ((x,z) INSERT (p DELETE (x,y) DELETE (y,z))) (x,w)) = z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; PAIR_BETA_THM] THEN
      REWRITE_TAC[IN; INSERT; DELETE; PAIR_BETA_THM; IN_ELIM_THM; PAIR_EQ] THEN
      MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN
      ASM_CASES_TAC `u:A = x` THEN ASM_REWRITE_TAC[] THENL
       [ALL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN MATCH_MP_TAC HAS_SIZE_UNION THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
      REWRITE_TAC[FUN_EQ_THM; INSERT; IN_ELIM_THM; FORALL_PAIR_THM;
                  PAIR_EQ] THEN
      UNDISCH_TAC `~(x:A IN s)` THEN REL_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:A->bool) HAS_SIZE (n + 1)` THEN
    SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE] THEN
    ASM_REWRITE_TAC[ADD_SUB];

    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN MAP_EVERY X_GEN_TAC
       [`y:A`; `p:(A#A)->bool`; `y':A`; `p':(A#A->bool)`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      MAP_EVERY ABBREV_TAC [`z = @z. p(x:A,z:A)`; `z' = @z. p'(x:A,z:A)`] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      SUBGOAL_THEN `p(x:A,z:A) /\ p'(x:A,z':A)` STRIP_ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
        CONJ_TAC THEN CONV_TAC SELECT_CONV THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
        ALL_TAC] THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o SYM)) THEN
      SUBGOAL_THEN `z:A IN s /\ z':A IN s` STRIP_ASSUME_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
                           CONJ_TAC THEN MP_TAC th)
      THENL
       [DISCH_THEN(MP_TAC o C AP_THM `(x:A,y:A)`) THEN
        REWRITE_TAC[INSERT; DELETE; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_CASES_TAC `z':A = z` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC;
        DISCH_THEN(MP_TAC o C AP_THM `(y:A,z:A)`) THEN
        REWRITE_TAC[INSERT; DELETE; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `a INSERT b INSERT s = a INSERT b INSERT t
        ==> ~(a IN s) /\ ~(a IN t) /\ ~(b IN s) /\ ~(b IN t) ==> s = t`)) THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:A->bool) HAS_SIZE n + 1` THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_DELETE] THEN
    ASM_SIMP_TAC[CARD_DELETE; CARD_CLAUSES; FINITE_DELETE] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN ARITH_TAC;

    REWRITE_TAC[DISJOINT] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_INTER; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `p:A#A->bool`] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:A`; `q:A#A->bool`] THEN
    REWRITE_TAC[PAIR_BETA_THM; IN_ELIM_THM; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `w = @w. q(x:A,w:A)` THEN
    SUBGOAL_THEN `(q:A#A->bool)(x:A,w:A)` STRIP_ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
      CONV_TAC SELECT_CONV THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `w:A IN s` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN FIRST_X_ASSUM(K ALL_TAC o SYM) THEN
    ASM_CASES_TAC `w:A = z` THEN ASM_REWRITE_TAC[] THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `w:A = y` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `y:A = z` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC; ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Trivia.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SUM_1 = prove
 (`sum(0..1) f = f 0 + f 1`,
  REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0]);;

let SUM_2 = prove
 (`sum(0..2) f = f 0 + f 1 + f 2`,
  SIMP_TAC[num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0;
           REAL_ADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* The key result.                                                           *)
(* ------------------------------------------------------------------------- *)

let DERANGEMENTS = prove
 (`!n. ~(n = 0)
       ==> &(derangements n) =
           &(FACT n) * sum(0..n) (\k. --(&1) pow k / &(FACT k))`,
  MATCH_MP_TAC DERANGEMENT_INDUCT THEN REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[derangements; SUM_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[derangements; ARITH; SUM_2; SUM_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = (n + 1) + 1`] THEN
  SIMP_TAC[SUM_ADD_SPLIT; LE_0; SUM_SING_NUMSEG] THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[real_pow] THEN REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPEC `n:num` FACT_LT) THEN UNDISCH_TAC `~(n = 0)` THEN
  REWRITE_TAC[GSYM LT_NZ; REAL_POW_NEG; GSYM REAL_OF_NUM_LT; REAL_POW_ONE] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* A more "explicit" formula. We could sharpen 1/2 to 0.3678794+epsilon      *)
(* ------------------------------------------------------------------------- *)

let DERANGEMENTS_EXP = prove
 (`!n. ~(n = 0)
       ==> let e = exp(&1) in
           abs(&(derangements n) - &(FACT n) / e) < &1 / &2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DERANGEMENTS; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[real_div; GSYM REAL_EXP_NEG] THEN ASM_CASES_TAC `n < 5` THENL
   [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
     (ARITH_RULE `n < 5 ==> n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4`)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC(map (num_CONV o mk_small_numeral) (1--5)) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `abs x < a <=> --a < x /\ x < a`] THEN
    REWRITE_TAC[real_sub] THEN CONJ_TAC THEN CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`-- &1`; `n + 1`] MCLAURIN_EXP_LE) THEN
  SIMP_TAC[PSUM_SUM_NUMSEG; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[ARITH_RULE `(0 + n + 1) - 1 = n`; GSYM real_div] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `abs(a * b - a * (b + c)) = abs(a * c)`] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NEG] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  SIMP_TAC[REAL_OF_NUM_LT; FACT_LT; REAL_FIELD
   `&0 < a ==> a * b / ((&n + &1) * a) = b / (&n + &1)`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[real_abs; REAL_EXP_POS_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(&1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    UNDISCH_TAC `abs(u) <= abs(-- &1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&3` THEN CONJ_TAC THENL
   [CONV_TAC REALCALC_REL_CONV; ALL_TAC] THEN
  UNDISCH_TAC `~(n < 5)` THEN REWRITE_TAC[NOT_LT; GSYM REAL_OF_NUM_LE] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence the critical "rounding" property.                                   *)
(* ------------------------------------------------------------------------- *)

let round = new_definition
 `round x = @n. integer(n) /\ n - &1 / &2 <= x /\ x < n + &1 / &2`;;

let ROUND_WORKS = prove
 (`!x. integer(round x) /\ round x - &1 / &2 <= x /\ x < round x + &1 / &2`,
  GEN_TAC THEN REWRITE_TAC[round] THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `floor(x + &1 / &2)` THEN MP_TAC(SPEC `x + &1 / &2` FLOOR) THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let DERANGEMENTS_EXP = prove
 (`!n. ~(n = 0)
       ==> let e = exp(&1) in &(derangements n) = round(&(FACT n) / e)`,
  REPEAT STRIP_TAC THEN LET_TAC THEN
  MATCH_MP_TAC REAL_EQ_INTEGERS_IMP THEN
  REWRITE_TAC[INTEGER_CLOSED; ROUND_WORKS] THEN
  MP_TAC(SPEC `&(FACT n) / e` ROUND_WORKS) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DERANGEMENTS_EXP) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Put them together.                                                        *)
(* ------------------------------------------------------------------------- *)

let THE_DERANGEMENTS_FORMULA = prove
 (`!n s. s HAS_SIZE n /\ ~(n = 0)
         ==> FINITE {p | p deranges s} /\
             let e = exp(&1) in
             &(CARD {p | p deranges s}) = round(&(FACT n) / e)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP NUMBER_OF_DERANGEMENTS) THEN
  ASM_SIMP_TAC[HAS_SIZE; DERANGEMENTS_EXP]);;
