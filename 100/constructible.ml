(* ========================================================================= *)
(* Non-constructibility of irrational cubic equation solutions.              *)
(*                                                                           *)
(* This gives the two classic impossibility results: trisecting an angle or  *)
(* constructing the cube using traditional geometric constructions.          *)
(*                                                                           *)
(* This elementary proof (not using field extensions etc.) is taken from     *)
(* Dickson's "First Course in the Theory of Equations", chapter III.         *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/floor.ml";;
needs "Multivariate/transcendentals.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* The critical lemma.                                                       *)
(* ------------------------------------------------------------------------- *)

let STEP_LEMMA = prove
 (`!P. (!n. P(&n)) /\
       (!x. P x ==> P(--x)) /\
       (!x. P x /\ ~(x = &0) ==> P(inv x)) /\
       (!x y. P x /\ P y ==> P(x + y)) /\
       (!x y. P x /\ P y ==> P(x * y))
       ==> !a b c z u v s.
               P a /\ P b /\ P c /\
               z pow 3 + a * z pow 2 + b * z + c = &0 /\
               P u /\ P v /\ P(s * s) /\ z = u + v * s
               ==> ?w. P w /\ w pow 3 + a * w pow 2 + b * w + c = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `v * s = &0` THENL
   [ASM_REWRITE_TAC[REAL_ADD_RID] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`A = a * s pow 2 * v pow 2 + &3 * s pow 2 * u * v pow 2 +
         a * u pow 2 + u pow 3 +  b * u + c`;
    `B = s pow 2 * v pow 3 + &2 * a * u * v + &3 * u pow 2 * v + b * v`] THEN
  SUBGOAL_THEN `A + B * s = &0` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `(P:real->bool) s` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `B = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `~P(s:real)` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_FIELD
     `A + B * s = &0 ==> ~(B = &0) ==> s = --A / B`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[REAL_ARITH `x pow 3 = x * x * x`; REAL_POW_2] THEN
    REPEAT(FIRST_ASSUM MATCH_ACCEPT_TAC ORELSE
           (FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC));
    ALL_TAC] THEN
  EXISTS_TAC `--(a + &2 * u)` THEN ASM_SIMP_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check ((not) o is_forall o concl))) THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Instantiate to square roots.                                              *)
(* ------------------------------------------------------------------------- *)

let STEP_LEMMA_SQRT = prove
 (`!P. (!n. P(&n)) /\
       (!x. P x ==> P(--x)) /\
       (!x. P x /\ ~(x = &0) ==> P(inv x)) /\
       (!x y. P x /\ P y ==> P(x + y)) /\
       (!x y. P x /\ P y ==> P(x * y))
       ==> !a b c z u v s.
               P a /\ P b /\ P c /\
               z pow 3 + a * z pow 2 + b * z + c = &0 /\
               P u /\ P v /\ P(s) /\ &0 <= s /\ z = u + v * sqrt(s)
               ==> ?w. P w /\ w pow 3 + a * w pow 2 + b * w + c = &0`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP STEP_LEMMA) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[SQRT_POW_2; REAL_POW_2]);;

(* ------------------------------------------------------------------------- *)
(* Numbers definable by radicals involving square roots only.                *)
(* ------------------------------------------------------------------------- *)

let radical_RULES,radical_INDUCT,radical_CASES = new_inductive_definition
 `(!x. rational x ==> radical x) /\
  (!x. radical x ==> radical (--x)) /\
  (!x. radical x /\ ~(x = &0) ==> radical (inv x)) /\
  (!x y. radical x /\ radical y ==> radical (x + y)) /\
  (!x y. radical x /\ radical y ==> radical (x * y)) /\
  (!x. radical x /\ &0 <= x ==> radical (sqrt x))`;;

let RADICAL_RULES = prove
 (`(!n. radical(&n)) /\
   (!x. rational x ==> radical x) /\
   (!x. radical x ==> radical (--x)) /\
   (!x. radical x /\ ~(x = &0) ==> radical (inv x)) /\
   (!x y. radical x /\ radical y ==> radical (x + y)) /\
   (!x y. radical x /\ radical y ==> radical (x - y)) /\
   (!x y. radical x /\ radical y ==> radical (x * y)) /\
   (!x y. radical x /\ radical y /\ ~(y = &0) ==> radical (x / y)) /\
   (!x n. radical x ==> radical(x pow n)) /\
   (!x. radical x /\ &0 <= x ==> radical (sqrt x))`,
  SIMP_TAC[real_div; real_sub; radical_RULES; RATIONAL_NUM] THEN
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[radical_RULES; real_pow; RATIONAL_NUM]);;

let RADICAL_TAC =
  REPEAT(MATCH_ACCEPT_TAC (CONJUNCT1 RADICAL_RULES) ORELSE
         (MAP_FIRST MATCH_MP_TAC(tl(tl(CONJUNCTS RADICAL_RULES))) THEN
          REPEAT CONJ_TAC));;

(* ------------------------------------------------------------------------- *)
(* Explicit "expressions" to support inductive proof.                        *)
(* ------------------------------------------------------------------------- *)

let expression_INDUCT,expression_RECURSION = define_type
 "expression = Constant real
             | Negation expression
             | Inverse expression
             | Addition expression expression
             | Multiplication expression expression
             | Sqrt expression";;

(* ------------------------------------------------------------------------- *)
(* Interpretation.                                                           *)
(* ------------------------------------------------------------------------- *)

let value = define
 `(value(Constant x) = x) /\
  (value(Negation e) = --(value e)) /\
  (value(Inverse e) = inv(value e)) /\
  (value(Addition e1 e2) = value e1 + value e2) /\
  (value(Multiplication e1 e2) = value e1 * value e2) /\
  (value(Sqrt e) = sqrt(value e))`;;

(* ------------------------------------------------------------------------- *)
(* Wellformedness of an expression.                                          *)
(* ------------------------------------------------------------------------- *)

let wellformed = define
 `(wellformed(Constant x) <=> rational x) /\
  (wellformed(Negation e) <=> wellformed e) /\
  (wellformed(Inverse e) <=> ~(value e = &0) /\ wellformed e) /\
  (wellformed(Addition e1 e2) <=> wellformed e1 /\ wellformed e2) /\
  (wellformed(Multiplication e1 e2) <=> wellformed e1 /\ wellformed e2) /\
  (wellformed(Sqrt e) <=> &0 <= value e /\ wellformed e)`;;

(* ------------------------------------------------------------------------- *)
(* The set of radicals in an expression.                                     *)
(* ------------------------------------------------------------------------- *)

let radicals = define
 `(radicals(Constant x) = {}) /\
  (radicals(Negation e) = radicals e) /\
  (radicals(Inverse e) = radicals e) /\
  (radicals(Addition e1 e2) = (radicals e1) UNION (radicals e2)) /\
  (radicals(Multiplication e1 e2) = (radicals e1) UNION (radicals e2)) /\
  (radicals(Sqrt e) = e INSERT (radicals e))`;;

let FINITE_RADICALS = prove
 (`!e. FINITE(radicals e)`,
  MATCH_MP_TAC expression_INDUCT THEN
  SIMP_TAC[radicals; FINITE_RULES; FINITE_UNION]);;

let WELLFORMED_RADICALS = prove
 (`!e. wellformed e ==> !r. r IN radicals(e) ==> &0 <= value r`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; wellformed; NOT_IN_EMPTY; IN_UNION; IN_INSERT] THEN
  MESON_TAC[]);;

let RADICALS_WELLFORMED = prove
 (`!e. wellformed e ==> !r. r IN radicals e ==> wellformed r`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; wellformed; NOT_IN_EMPTY; IN_UNION; IN_INSERT] THEN
  MESON_TAC[]);;

let RADICALS_SUBSET = prove
 (`!e r. r IN radicals e ==> radicals(r) SUBSET radicals(e)`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; IN_UNION; NOT_IN_EMPTY; IN_INSERT; SUBSET] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Show that every radical is the interpretation of a wellformed expresion.  *)
(* ------------------------------------------------------------------------- *)

let RADICAL_EXPRESSION = prove
 (`!x. radical x <=> ?e. wellformed e /\ x = value e`,
  GEN_TAC THEN EQ_TAC THEN SPEC_TAC(`x:real`,`x:real`) THENL
   [MATCH_MP_TAC radical_INDUCT THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_MESON_TAC[value; wellformed];
    SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
    MATCH_MP_TAC expression_INDUCT THEN
    REWRITE_TAC[value; wellformed] THEN SIMP_TAC[radical_RULES]]);;

(* ------------------------------------------------------------------------- *)
(* Nesting depth of radicals in an expression.                               *)
(* ------------------------------------------------------------------------- *)

let LT_MAX = prove
 (`!a b c. a < MAX b c <=> a < b \/ a < c`,
  ARITH_TAC);;

let depth = define
 `(depth(Constant x) = 0) /\
  (depth(Negation e) = depth e) /\
  (depth(Inverse e) = depth e) /\
  (depth(Addition e1 e2) = MAX (depth e1) (depth e2)) /\
  (depth(Multiplication e1 e2) = MAX (depth e1) (depth e2)) /\
  (depth(Sqrt e) = 1 + depth e)`;;

let IN_RADICALS_SMALLER = prove
 (`!r s. s IN radicals(r) ==> depth(s) < depth(r)`,
  MATCH_MP_TAC expression_INDUCT THEN REWRITE_TAC[radicals; depth] THEN
  REWRITE_TAC[IN_UNION; NOT_IN_EMPTY; IN_INSERT; LT_MAX] THEN
  MESON_TAC[ARITH_RULE `s = a \/ s < a ==> s < 1 + a`]);;

let NOT_IN_OWN_RADICALS = prove
 (`!r. ~(r IN radicals r)`,
  MESON_TAC[IN_RADICALS_SMALLER; LT_REFL]);;

let RADICALS_EMPTY_RATIONAL = prove
 (`!e. wellformed e /\ radicals e = {} ==> rational(value e)`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[wellformed; value; radicals; EMPTY_UNION; NOT_INSERT_EMPTY] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Crucial point about splitting off some "topmost" radical.                 *)
(* ------------------------------------------------------------------------- *)

let FINITE_MAX = prove
 (`!s. FINITE s ==> ~(s = {}) ==> ?b:num. b IN s /\ !a. a IN s ==> a <= b`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:num->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; UNWIND_THM2; LE_REFL] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let RADICAL_TOP = prove
 (`!e. ~(radicals e = {})
       ==> ?r. r IN radicals e /\
               !s. s IN radicals(e) ==> ~(r IN radicals s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE depth (radicals e)` FINITE_MAX) THEN
  ASM_SIMP_TAC[IMAGE_EQ_EMPTY; FINITE_IMAGE; FINITE_RADICALS] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  MESON_TAC[IN_RADICALS_SMALLER; NOT_LT]);;

(* ------------------------------------------------------------------------- *)
(* By rearranging the expression we can use it in a canonical way.           *)
(* ------------------------------------------------------------------------- *)

let RADICAL_CANONICAL_TRIVIAL = prove
 (`!e r.
     (r IN radicals e
            ==> (?a b.
                   wellformed a /\
                   wellformed b /\
                   value e = value a + value b * sqrt (value r) /\
                   radicals a SUBSET radicals e DELETE r /\
                   radicals b SUBSET radicals e DELETE r /\
                   radicals r SUBSET radicals e DELETE r))
     ==> wellformed e
         ==> ?a b. wellformed a /\
                   wellformed b /\
                   value e = value a + value b * sqrt (value r) /\
                   radicals a SUBSET (radicals e UNION radicals r) DELETE r /\
                   radicals b SUBSET (radicals e UNION radicals r) DELETE r /\
                   radicals r SUBSET (radicals e UNION radicals r) DELETE r`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r IN radicals e` THEN ASM_SIMP_TAC[] THENL
   [DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN SET_TAC[];
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`e:expression`; `Constant(&0)`] THEN
    ASM_REWRITE_TAC[wellformed; value; radicals] THEN
    REWRITE_TAC[RATIONAL_NUM; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    UNDISCH_TAC `~(r IN radicals e)` THEN
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN SET_TAC[]]);;

let RADICAL_CANONICAL = prove
 (`!e. wellformed e /\ ~(radicals e = {})
       ==> ?r. r IN radicals(e) /\
               ?a b. wellformed(Addition a (Multiplication b (Sqrt r))) /\
                     value e = value(Addition a (Multiplication b (Sqrt r))) /\
                     (radicals a) SUBSET (radicals(e) DELETE r) /\
                     (radicals b) SUBSET (radicals(e) DELETE r) /\
                     (radicals r) SUBSET (radicals(e) DELETE r)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP RADICAL_TOP) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:expression` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= value r /\ wellformed r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[WELLFORMED_RADICALS; RADICALS_WELLFORMED]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`wellformed e`; `r IN radicals e`] THEN
  ASM_REWRITE_TAC[IMP_IMP; wellformed; value; GSYM CONJ_ASSOC] THEN
  SPEC_TAC(`e:expression`,`e:expression`) THEN
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[wellformed; radicals; value; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; IN_UNION] THEN REPEAT CONJ_TAC THEN
  X_GEN_TAC `e1:expression` THEN TRY(X_GEN_TAC `e2:expression`) THENL
   [DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:expression`; `b:expression`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`Negation a`; `Negation b`] THEN
    ASM_REWRITE_TAC[value; wellformed; radicals] THEN REAL_ARITH_TAC;

    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:expression`; `b:expression`] THEN
    ASM_CASES_TAC `value b * sqrt(value r) = value a` THENL
     [ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`Inverse(Multiplication (Constant(&2)) a)`; `Constant(&0)`] THEN
      ASM_REWRITE_TAC[value; radicals; wellformed] THEN
      REWRITE_TAC[RATIONAL_NUM; EMPTY_SUBSET; CONJ_ASSOC] THEN CONJ_TAC THENL
       [UNDISCH_TAC `~(value a + value a = &0)` THEN CONV_TAC REAL_FIELD;
        REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`Multiplication a (Inverse
        (Addition (Multiplication a a)
                  (Multiplication (Multiplication b b) (Negation r))))`;
      `Multiplication (Negation b) (Inverse
        (Addition (Multiplication a a)
                  (Multiplication (Multiplication b b) (Negation r))))`] THEN
    ASM_REWRITE_TAC[value; wellformed; radicals; UNION_SUBSET] THEN
    UNDISCH_TAC `~(value b * sqrt (value r) = value a)` THEN
    UNDISCH_TAC `~(value e1 = &0)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP SQRT_POW_2) THEN CONV_TAC REAL_FIELD;

    REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    DISCH_THEN(fun th ->
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN(MP_TAC o
      MATCH_MP RADICAL_CANONICAL_TRIVIAL)) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`a1:expression`; `b1:expression`; `a2:expression`; `b2:expression`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`Addition a1 a2`; `Addition b1 b2`] THEN
    ASM_REWRITE_TAC[value; wellformed; radicals] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN
    MP_TAC(SPECL [`e1:expression`; `r:expression`] RADICALS_SUBSET) THEN
    MP_TAC(SPECL [`e2:expression`; `r:expression`] RADICALS_SUBSET) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[];

    REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    DISCH_THEN(fun th ->
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN(MP_TAC o
      MATCH_MP RADICAL_CANONICAL_TRIVIAL)) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`a1:expression`; `b1:expression`; `a2:expression`; `b2:expression`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`Addition (Multiplication a1 a2)
                (Multiplication (Multiplication b1 b2) r)`;
      `Addition (Multiplication a1 b2) (Multiplication a2 b1)`] THEN
    ASM_REWRITE_TAC[value; wellformed; radicals] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP SQRT_POW_2) THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN
    MP_TAC(SPECL [`e1:expression`; `r:expression`] RADICALS_SUBSET) THEN
    MP_TAC(SPECL [`e2:expression`; `r:expression`] RADICALS_SUBSET) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[];

    REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    REPEAT(DISCH_THEN(K ALL_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`Constant(&0)`; `Constant(&1)`] THEN
    REWRITE_TAC[wellformed; value; REAL_ADD_LID; REAL_MUL_LID] THEN
    REWRITE_TAC[radicals; RATIONAL_NUM] THEN
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Now we quite easily get an inductive argument.                            *)
(* ------------------------------------------------------------------------- *)

let CUBIC_ROOT_STEP = prove
 (`!a b c. rational a /\ rational b /\ rational c
           ==> !e. wellformed e /\
                   ~(radicals e = {}) /\
                   (value e) pow 3 + a * (value e) pow 2 +
                                     b * (value e) + c = &0
                   ==> ?e'. wellformed e' /\
                            (radicals e') PSUBSET (radicals e) /\
                            (value e') pow 3 + a * (value e') pow 2 +
                                     b * (value e') + c = &0`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `e:expression` RADICAL_CANONICAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (X_CHOOSE_THEN `r:expression` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`eu:expression`; `ev:expression`] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `\x. ?ex. wellformed ex /\
                        radicals ex SUBSET (radicals(e) DELETE r) /\
                        value ex = x`
              STEP_LEMMA_SQRT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN EXISTS_TAC `Constant(&n)` THEN
      REWRITE_TAC[wellformed; radicals; RATIONAL_NUM; value; EMPTY_SUBSET];
      X_GEN_TAC `x:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `ex:expression` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `Negation ex` THEN
      ASM_REWRITE_TAC[wellformed; radicals; value];
      X_GEN_TAC `x:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `ex:expression` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `Inverse ex` THEN
      ASM_REWRITE_TAC[wellformed; radicals; value];
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `ex:expression` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `ey:expression` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `Addition ex ey` THEN
      ASM_REWRITE_TAC[wellformed; radicals; value; UNION_SUBSET];
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `ex:expression` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `ey:expression` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `Multiplication ex ey` THEN
      ASM_REWRITE_TAC[wellformed; radicals; value; UNION_SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`a:real`; `b:real`; `c:real`;
    `value e`; `value eu`; `value ev`; `value r`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `Constant a` THEN
      ASM_REWRITE_TAC[wellformed; radicals; EMPTY_SUBSET; value];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `Constant b` THEN
      ASM_REWRITE_TAC[wellformed; radicals; EMPTY_SUBSET; value];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `Constant c` THEN
      ASM_REWRITE_TAC[wellformed; radicals; EMPTY_SUBSET; value];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wellformed]) THEN
    ASM_REWRITE_TAC[value] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e':expression` THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence the main result.                                                    *)
(* ------------------------------------------------------------------------- *)

let CUBIC_ROOT_RADICAL_INDUCT = prove
 (`!a b c. rational a /\ rational b /\ rational c
           ==> !n e. wellformed e /\ CARD (radicals e) = n /\
                     (value e) pow 3 + a * (value e) pow 2 +
                                b * (value e) + c = &0
                 ==> ?x. rational x /\
                         x pow 3 + a * x pow 2 + b * x + c = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `e:expression` THEN
  STRIP_TAC THEN ASM_CASES_TAC `radicals e = {}` THENL
   [ASM_MESON_TAC[RADICALS_EMPTY_RATIONAL]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:expression`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':expression` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD(radicals e')`) THEN ANTS_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `CARD(radicals e) = n`)] THEN
    MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[FINITE_RADICALS];
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `e':expression` THEN
    ASM_REWRITE_TAC[]]);;

let CUBIC_ROOT_RATIONAL = prove
 (`!a b c. rational a /\ rational b /\ rational c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. rational x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`,
  REWRITE_TAC[RADICAL_EXPRESSION] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_RADICAL_INDUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`CARD(radicals e)`; `e:expression`] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Now go further to an *integer*, since the polynomial is monic.            *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;

let RATIONAL_LOWEST_LEMMA = prove
 (`!p q. ~(q = 0) ==> ?p' q'. ~(q' = 0) /\ coprime(p',q') /\ p * q' = p' * q`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `coprime(p,q)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [coprime]) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
  REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p':num` SUBST_ALL_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `q':num` SUBST_ALL_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q':num`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [ARITH_RULE `a < b <=> 1 * a < b`] THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(d = 0) /\ ~(d = 1) ==> 1 < d`] THEN
  DISCH_THEN(MP_TAC o SPEC `p':num`) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN SIMP_TAC[] THEN
  CONV_TAC NUM_RING);;

prioritize_real();;

let RATIONAL_LOWEST = prove
 (`!x. rational x <=> ?p q. ~(q = 0) /\ coprime(p,q) /\ abs(x) = &p / &q`,
  GEN_TAC THEN REWRITE_TAC[RATIONAL_ALT] THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  STRIP_TAC THEN MP_TAC(SPECL [`p:num`; `q:num`] RATIONAL_LOWEST_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  UNDISCH_TAC `~(q = 0)` THEN SIMP_TAC[GSYM REAL_OF_NUM_EQ] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN CONV_TAC REAL_FIELD);;

let RATIONAL_ROOT_INTEGER = prove
 (`!a b c x. integer a /\ integer b /\ integer c /\ rational x /\
             x pow 3 + a * x pow 2 + b * x + c = &0
             ==> integer x`,
  REWRITE_TAC[RATIONAL_LOWEST; GSYM REAL_OF_NUM_EQ] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP(REAL_ARITH
   `abs x = a ==> x = a \/ x = --a`)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(q = &0)
     ==> ((p / q) pow 3 + a * (p / q) pow 2 + b * (p / q) + c = &0 <=>
          (p pow 3 = q * --(a * p pow 2 + b * p * q + c * q pow 2))) /\
         ((--(p / q)) pow 3 + a * (--(p / q)) pow 2 +
           b * (--(p / q)) + c = &0 <=>
          p pow 3 = q * (a * p pow 2 - b * p * q + c * q pow 2))`] THEN
  (W(fun(asl,w) ->
       SUBGOAL_THEN(mk_comb(`integer`,rand(rand(lhand w)))) MP_TAC THENL
    [REPEAT(MAP_FIRST MATCH_MP_TAC (tl(CONJUNCTS INTEGER_CLOSED)) THEN
            REPEAT CONJ_TAC) THEN
     ASM_REWRITE_TAC[INTEGER_CLOSED];
     ALL_TAC])) THEN
  REWRITE_TAC[integer] THEN DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
  DISCH_THEN(MP_TAC o AP_TERM `abs`) THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NUM; REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_EQ] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COPRIME_SYM]) THEN
  DISCH_THEN(MP_TAC o SPEC `3` o MATCH_MP COPRIME_EXP) THEN
  REWRITE_TAC[coprime] THEN DISCH_THEN(MP_TAC o SPEC `q:num`) THEN
  ASM_CASES_TAC `q = 1` THEN
  ASM_SIMP_TAC[REAL_DIV_1; REAL_ABS_NUM; REAL_OF_NUM_EQ; GSYM EXISTS_REFL] THEN
  MESON_TAC[divides; DIVIDES_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Hence we have our big final theorem.                                      *)
(* ------------------------------------------------------------------------- *)

let CUBIC_ROOT_INTEGER = prove
 (`!a b c. integer a /\ integer b /\ integer c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. integer x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_RATIONAL) THEN
  ASM_SIMP_TAC[RATIONAL_INTEGER] THEN
  ASM_MESON_TAC[RATIONAL_ROOT_INTEGER]);;

(* ------------------------------------------------------------------------- *)
(* Geometrical definitions.                                                  *)
(* ------------------------------------------------------------------------- *)

let length = new_definition
  `length(a:real^2,b:real^2) = norm(b - a)`;;

let parallel = new_definition
 `parallel (a:real^2,b:real^2) (c:real^2,d:real^2) <=>
        (a$1 - b$1) * (c$2 - d$2) = (a$2 - b$2) * (c$1 - d$1)`;;

let collinear3 = new_definition
  `collinear3 (a:real^2) b c <=> parallel (a,b) (a,c)`;;

let is_intersection = new_definition
  `is_intersection p (a,b) (c,d) <=> collinear3 a p b /\ collinear3 c p d`;;

let on_circle = new_definition
 `on_circle x (centre,pt) <=> length(centre,x) = length(centre,pt)`;;

(* ------------------------------------------------------------------------- *)
(* A trivial lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

let SQRT_CASES_LEMMA = prove
 (`!x y. y pow 2 = x ==> &0 <= x /\ (sqrt(x) = y \/ sqrt(x) = --y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
  MP_TAC(SPEC `y:real` (GEN_ALL POW_2_SQRT)) THEN
  MP_TAC(SPEC `--y` (GEN_ALL POW_2_SQRT)) THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_POW_NEG; ARITH] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Show that solutions to certain classes of equations are radical.          *)
(* ------------------------------------------------------------------------- *)

let RADICAL_LINEAR_EQUATION = prove
 (`!a b x. radical a /\ radical b /\ ~(a = &0 /\ b = &0) /\ a * x + b = &0
           ==> radical x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(a = &0) /\ x = --b / a`
   (fun th -> ASM_SIMP_TAC[th; RADICAL_RULES]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let RADICAL_SIMULTANEOUS_LINEAR_EQUATION = prove
 (`!a b c d e f x.
        radical a /\ radical b /\ radical c /\
        radical d /\ radical e /\ radical f /\
        ~(a * e = b * d /\ a * f = c * d /\ e * c = b * f) /\
        a * x + b * y = c /\ d * x + e * y = f
        ==> radical(x) /\ radical(y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN
   `~(a * e - b * d = &0) /\
    x = (e * c - b * f) / (a * e - b * d) /\
    y = (a * f - d * c) / (a * e - b * d)`
  STRIP_ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[RADICAL_RULES]]);;

let RADICAL_QUADRATIC_EQUATION = prove
 (`!a b c x. radical a /\ radical b /\ radical c /\
             a * x pow 2 + b * x + c = &0 /\
             ~(a = &0 /\ b = &0 /\ c = &0)
             ==> radical x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
    MESON_TAC[RADICAL_LINEAR_EQUATION];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC RADICAL_LINEAR_EQUATION THEN
  EXISTS_TAC `&2 * a` THEN
  ASM_SIMP_TAC[RADICAL_RULES; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  SUBGOAL_THEN `&0 <= b pow 2 - &4 * a * c /\
                ((&2 * a) * x + (b - sqrt(b pow 2 - &4 * a * c)) = &0 \/
                 (&2 * a) * x + (b + sqrt(b pow 2 - &4 * a * c)) = &0)`
  MP_TAC THENL
   [REWRITE_TAC[real_sub; REAL_ARITH `a + (b + c) = &0 <=> c = --(a + b)`] THEN
    REWRITE_TAC[REAL_EQ_NEG2] THEN MATCH_MP_TAC SQRT_CASES_LEMMA THEN
    FIRST_X_ASSUM(MP_TAC o SYM) THEN CONV_TAC REAL_RING;
    STRIP_TAC THENL
     [EXISTS_TAC `b - sqrt(b pow 2 - &4 * a * c)`;
      EXISTS_TAC `b + sqrt(b pow 2 - &4 * a * c)`] THEN
    ASM_REWRITE_TAC[] THEN RADICAL_TAC THEN ASM_REWRITE_TAC[]]);;

let RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC = prove
 (`!a b c d e f x.
        radical a /\ radical b /\ radical c /\
        radical d /\ radical e /\ radical f /\
        ~(d = &0 /\ e = &0 /\ f = &0) /\
        (x - a) pow 2 + (y - b) pow 2 = c /\ d * x + e * y = f
        ==> radical x /\ radical y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d pow 2 + e pow 2` RADICAL_QUADRATIC_EQUATION) THEN
  DISCH_THEN MATCH_MP_TAC THENL
   [EXISTS_TAC `&2 * b * d * e - &2 * a * e pow 2 - &2 * d * f` THEN
    EXISTS_TAC `b pow 2 * e pow 2 + a pow 2 * e pow 2 +
                f pow 2 - c * e pow 2 - &2 * b * e * f`;
    EXISTS_TAC `&2 * a * d * e - &2 * b * d pow 2 - &2 * f * e` THEN
    EXISTS_TAC `a pow 2 * d pow 2 + b pow 2 * d pow 2 +
                f pow 2 - c * d pow 2 - &2 * a * d * f`] THEN
  (REPLICATE_TAC 3
    (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
   CONJ_TAC THENL
    [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   REWRITE_TAC[REAL_SOS_EQ_0] THEN REPEAT(POP_ASSUM MP_TAC) THEN
   CONV_TAC REAL_RING));;

let RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC = prove
 (`!a b c d e f x.
        radical a /\ radical b /\ radical c /\
        radical d /\ radical e /\ radical f /\
        ~(a = d /\ b = e /\ c = f) /\
        (x - a) pow 2 + (y - b) pow 2 = c /\
        (x - d) pow 2 + (y - e) pow 2 = f
        ==> radical x /\ radical y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC THEN
  MAP_EVERY EXISTS_TAC
   [`a:real`; `b:real`; `c:real`; `&2 * (d - a)`; `&2 * (e - b)`;
    `(d pow 2 - a pow 2) + (e pow 2 - b pow 2) + (c - f)`] THEN
  ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 3
   (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Analytic criterion for constructibility.                                  *)
(* ------------------------------------------------------------------------- *)

let constructible_RULES,constructible_INDUCT,constructible_CASES =
 new_inductive_definition
  `(!x:real^2. rational(x$1) /\ rational(x$2) ==> constructible x) /\
// Intersection of two non-parallel lines AB and CD
  (!a b c d x. constructible a /\ constructible b /\
               constructible c /\ constructible d /\
               ~parallel (a,b) (c,d) /\ is_intersection x (a,b) (c,d)
               ==> constructible x) /\
// Intersection of a nontrivial line AB and circle with centre C, radius DE
  (!a b c d e x. constructible a /\ constructible b /\
                 constructible c /\ constructible d /\
                 constructible e /\
                 ~(a = b) /\ collinear3 a x b /\ length (c,x) = length(d,e)
                 ==> constructible x) /\
// Intersection of distinct circles with centres A and D, radii BD and EF
  (!a b c d e f x. constructible a /\ constructible b /\
                   constructible c /\ constructible d /\
                   constructible e /\ constructible f /\
                   ~(a = d /\ length (b,c) = length (e,f)) /\
                   length (a,x) = length (b,c) /\ length (d,x) = length (e,f)
                   ==> constructible x)`;;

(* ------------------------------------------------------------------------- *)
(* Some "coordinate geometry" lemmas.                                        *)
(* ------------------------------------------------------------------------- *)

let RADICAL_LINE_LINE_INTERSECTION = prove
 (`!a b c d x.
        radical(a$1) /\ radical(a$2) /\
        radical(b$1) /\ radical(b$2) /\
        radical(c$1) /\ radical(c$2) /\
        radical(d$1) /\ radical(d$2) /\
        ~(parallel (a,b) (c,d)) /\ is_intersection x (a,b) (c,d)
        ==> radical(x$1) /\ radical(x$2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[parallel; collinear3; is_intersection] THEN STRIP_TAC THEN
  MATCH_MP_TAC RADICAL_SIMULTANEOUS_LINEAR_EQUATION THEN
  MAP_EVERY EXISTS_TAC
   [`(b:real^2)$2 - (a:real^2)$2`; `(a:real^2)$1 - (b:real^2)$1`;
    `(a:real^2)$2 * (a$1 - (b:real^2)$1) - (a:real^2)$1 * (a$2 - b$2)`;
    `(d:real^2)$2 - (c:real^2)$2`; `(c:real^2)$1 - (d:real^2)$1`;
    `(c:real^2)$2 * (c$1 - (d:real^2)$1) - (c:real^2)$1 * (c$2 - d$2)`] THEN
  REPLICATE_TAC 6
   (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

let RADICAL_LINE_CIRCLE_INTERSECTION = prove
 (`!a b c d e x.
        radical(a$1) /\ radical(a$2) /\
        radical(b$1) /\ radical(b$2) /\
        radical(c$1) /\ radical(c$2) /\
        radical(d$1) /\ radical(d$2) /\
        radical(e$1) /\ radical(e$2) /\
        ~(a = b) /\ collinear3 a x b /\ length(c,x) = length(d,e)
        ==> radical(x$1) /\ radical(x$2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[length; NORM_EQ; collinear3; parallel] THEN
  SIMP_TAC[CART_EQ; FORALL_2; dot; SUM_2; DIMINDEX_2; VECTOR_SUB_COMPONENT;
           GSYM REAL_POW_2] THEN
  STRIP_TAC THEN MATCH_MP_TAC RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC THEN
  MAP_EVERY EXISTS_TAC
   [`(c:real^2)$1`; `(c:real^2)$2`;
    `((e:real^2)$1 - (d:real^2)$1) pow 2 + (e$2 - d$2) pow 2`;
    `(b:real^2)$2 - (a:real^2)$2`;
    `(a:real^2)$1 - (b:real^2)$1`;
    `a$2 * ((a:real^2)$1 - (b:real^2)$1) - a$1 * (a$2 - b$2)`] THEN
  REPLICATE_TAC 6
   (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

let RADICAL_CIRCLE_CIRCLE_INTERSECTION = prove
 (`!a b c d e f x.
        radical(a$1) /\ radical(a$2) /\
        radical(b$1) /\ radical(b$2) /\
        radical(c$1) /\ radical(c$2) /\
        radical(d$1) /\ radical(d$2) /\
        radical(e$1) /\ radical(e$2) /\
        radical(f$1) /\ radical(f$2) /\
        length(a,x) = length(b,c) /\
        length(d,x) = length(e,f) /\
        ~(a = d /\ length(b,c) = length(e,f))
        ==> radical(x$1) /\ radical(x$2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[length; NORM_EQ; collinear3; parallel] THEN
  SIMP_TAC[CART_EQ; FORALL_2; dot; SUM_2; DIMINDEX_2; VECTOR_SUB_COMPONENT;
           GSYM REAL_POW_2] THEN
  STRIP_TAC THEN MATCH_MP_TAC RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC THEN
  MAP_EVERY EXISTS_TAC
   [`(a:real^2)$1`; `(a:real^2)$2`;
    `((c:real^2)$1 - (b:real^2)$1) pow 2 + (c$2 - b$2) pow 2`;
    `(d:real^2)$1`; `(d:real^2)$2`;
    `((f:real^2)$1 - (e:real^2)$1) pow 2 + (f$2 - e$2) pow 2`] THEN
  REPLICATE_TAC 6
   (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* So constructible points have radical coordinates.                         *)
(* ------------------------------------------------------------------------- *)

let CONSTRUCTIBLE_RADICAL = prove
 (`!x. constructible x ==> radical(x$1) /\ radical(x$2)`,
  MATCH_MP_TAC constructible_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[RADICAL_RULES];
    MATCH_MP_TAC RADICAL_LINE_LINE_INTERSECTION THEN ASM_MESON_TAC[];
    MATCH_MP_TAC RADICAL_LINE_CIRCLE_INTERSECTION THEN ASM_MESON_TAC[];
    MATCH_MP_TAC RADICAL_CIRCLE_CIRCLE_INTERSECTION THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Impossibility of doubling the cube.                                       *)
(* ------------------------------------------------------------------------- *)

let DOUBLE_THE_CUBE_ALGEBRA = prove
 (`~(?x. radical x /\ x pow 3 = &2)`,
  STRIP_TAC THEN MP_TAC(SPECL [`&0`; `&0`; `-- &2`] CUBIC_ROOT_INTEGER) THEN
  SIMP_TAC[INTEGER_CLOSED; NOT_IMP] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[GSYM real_sub; REAL_SUB_0] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `abs`) THEN
  REWRITE_TAC[REAL_ABS_POW] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[integer]) THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_POW; REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(ARITH_RULE
   `n EXP 3 <= 1 EXP 3 \/ 2 EXP 3 <= n EXP 3 ==> ~(n EXP 3 = 2)`) THEN
  REWRITE_TAC[num_CONV `3`; EXP_MONO_LE_SUC] THEN ARITH_TAC);;

let DOUBLE_THE_CUBE = prove
 (`!x. x pow 3 = &2 ==> ~(constructible(vector[x; &0]))`,
  GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONSTRUCTIBLE_RADICAL) THEN
  REWRITE_TAC[VECTOR_2; RADICAL_RULES] THEN
  ASM_MESON_TAC[DOUBLE_THE_CUBE_ALGEBRA]);;

(* ------------------------------------------------------------------------- *)
(* Impossibility of trisecting                                               *)
(* ------------------------------------------------------------------------- *)

let COS_TRIPLE = prove
 (`!x. cos(&3 * x) = &4 * cos(x) pow 3 - &3 * cos(x)`,
  GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `&3 * x = x + x + x`; SIN_ADD; COS_ADD] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let COS_PI3 = prove
 (`cos(pi / &3) = &1 / &2`,
  MP_TAC(SPEC `pi / &3` COS_TRIPLE) THEN
  SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH; COS_PI] THEN
  REWRITE_TAC[REAL_RING
   `-- &1 = &4 * c pow 3 - &3 * c <=> c = &1 / &2 \/ c = -- &1`] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC MP_TAC) THEN
  MP_TAC(SPEC `pi / &3` COS_POS_PI) THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let TRISECT_60_DEGREES_ALGEBRA = prove
 (`~(?x. radical x /\ x pow 3 - &3 * x - &1 = &0)`,
  STRIP_TAC THEN MP_TAC(SPECL [`&0`; `-- &3`; `-- &1`] CUBIC_ROOT_INTEGER) THEN
  SIMP_TAC[INTEGER_CLOSED; NOT_IMP] THEN REWRITE_TAC[REAL_ADD_ASSOC] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LNEG; GSYM real_sub] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `x pow 3 - &3 * x - &1 = &0 <=> x * (x pow 2 - &3) = &1`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `abs`) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[integer]) THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC (ARITH_RULE
   `n = 0 \/ n = 1 \/ n = 2 + (n - 2)`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `(&2 + m) pow 2 - &3 = m pow 2 + &4 * m + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_ABS_NUM;
              REAL_OF_NUM_EQ; MULT_EQ_1] THEN
  ARITH_TAC);;

let TRISECT_60_DEGREES = prove
 (`!y. ~(constructible(vector[cos(pi / &9); y]))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CONSTRUCTIBLE_RADICAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[VECTOR_2] THEN
  DISCH_TAC THEN MP_TAC(SPEC `pi / &9` COS_TRIPLE) THEN
  SIMP_TAC[REAL_ARITH `&3 * x / &9 = x / &3`; COS_PI3] THEN
  REWRITE_TAC[REAL_ARITH
   `&1 / &2 = &4 * c pow 3 - &3 * c <=>
    (&2 * c) pow 3 - &3 * (&2 * c) - &1 = &0`] THEN
  ASM_MESON_TAC[TRISECT_60_DEGREES_ALGEBRA; RADICAL_RULES]);;
