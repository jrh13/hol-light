(* ========================================================================= *)
(* Prime ideals in integral extensions: lying over, going up,                *)
(* incomparability and maximal ideals, for a ring homomorphism f : r -> s    *)
(* such that every element of s is integral over r along f.                  *)
(*                                                                           *)
(* Main results: for a prime p of r and an ideal j of s whose preimage lies  *)
(* in p, some prime q of s containing j has preimage p                       *)
(* (INTEGRAL_EXTENSION_PRIME_ABOVE); hence lying over, some prime above each *)
(* prime p containing the kernel of f (INTEGRAL_EXTENSION_LYING_OVER), and   *)
(* going up (INTEGRAL_EXTENSION_GOING_UP). An ideal containing a prime q     *)
(* with the same preimage is q (INTEGRAL_EXTENSION_INCOMPARABLE); a prime q  *)
(* is maximal iff its preimage is (INTEGRAL_EXTENSION_MAXIMAL_IDEAL); for a  *)
(* monomorphism into a domain, nonzero primes have nonzero preimages         *)
(* (INTEGRAL_EXTENSION_PRIME_NONZERO).                                       *)
(*                                                                           *)
(* Routes. Primes above: the ideal j + p s does not meet the multiplicative  *)
(* set f(r - p). If f(t) lies in it, the span of finitely many integral      *)
(* elements (INTEGRAL_SPAN_FINITE_SET) gives congruences f(t) x == sum_y f(a *)
(* x y) y (mod j) with all a x y in p (RING_SPAN_IDEAL_COMBINATION), and the *)
(* determinant of t I - a has its image in j, so it lies in p, while it is   *)
(* congruent to t^n modulo p (INTEGRAL_DETERMINANT_TRICK_IDEAL,              *)
(* RING_DET_DIAGONAL_CONGRUENCE of Library/ring_det.ml). A prime above j + p *)
(* s avoiding f(r - p) (PRIME_SUPERIDEAL_EXCLUDING_EXISTS) is the required   *)
(* q; no localization is used. Incomparability: for y in the larger ideal    *)
(* and not in q, a monic relation for y modulo q of least degree has its     *)
(* constant term in the common preimage, hence in q, and dividing by y gives *)
(* a smaller degree. The maximality criterion follows from going up and from *)
(* incomparability with a maximal ideal above q.                             *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (RING_MONIC_RELATION_FACTOR),                 *)
(* Library/fieldtheory.ml (ring_span), Library/ring_det.ml (ring_det,        *)
(* RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL, RING_DET_DIAGONAL_CONGRUENCE) and   *)
(* ANT/integral.ml (integral_element, INTEGRAL_SPAN_FINITE_SET).             *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_det.ml";;
needs "ANT/integral.ml";;

(* ------------------------------------------------------------------------- *)
(* The determinant trick modulo ideals.                                      *)
(* ------------------------------------------------------------------------- *)

(* If f(t) x == sum_y f(a x y) y modulo j for the x of a finite set g whose *)
(* span contains 1, with all a x y in p, then f(d) IN j for some d with     *)
(* d == t^n modulo p, n the size of g (d the determinant of t I - a).       *)

let INTEGRAL_DETERMINANT_TRICK_IDEAL = prove
 (`!r s (f:A->B) j p (g:B->bool) (a:B->B->A) t.
        ring_homomorphism(r,s) f /\ ring_ideal s j /\ ring_ideal r p /\
        FINITE g /\ g SUBSET ring_carrier s /\
        ring_1 s IN ring_span (r,s) f g /\ t IN ring_carrier r /\
        (!x y. x IN g /\ y IN g ==> a x y IN p) /\
        (!x. x IN g
             ==> ring_sub s (ring_mul s (f t) x)
                   (ring_sum s g (\y. ring_mul s (f(a x y)) y)) IN j)
        ==> ?d. d IN ring_carrier r /\ f d IN j /\
                ring_sub r d (ring_pow r t (CARD g)) IN p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y:B. x IN g /\ y IN g ==> (a:B->B->A) x y IN ring_carrier r`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC
   `m = \x y:B. ring_sub r (if x = y then t else ring_0 r)
                           ((a:B->B->A) x y)` THEN
  SUBGOAL_THEN
   `!x y:B. x IN g /\ y IN g ==> (m:B->B->A) x y IN ring_carrier r`
  ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_SUB; RING_0];
    ALL_TAC] THEN
  EXISTS_TAC `ring_det r g (m:B->B->A)` THEN REWRITE_TAC[RING_DET] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC RING_DET_DIAGONAL_CONGRUENCE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    EXPAND_TAC "m" THEN
    SUBGOAL_THEN `(if (x:B) = y then t else ring_0 r:A) IN ring_carrier r`
    MP_TAC THENL [COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0]; ALL_TAC] THEN
    SPEC_TAC(`if (x:B) = y then t else ring_0 r:A`,`c:A`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_sub r (ring_sub r c ((a:B->B->A) x y)) c = ring_neg r (a x y)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
       `ring_sub r (ring_sub r c b) c = ring_neg r (b:A)`)) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC IN_RING_IDEAL_NEG THEN ASM_SIMP_TAC[]]] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `g:B->bool`;
                 `m:B->B->A`] RING_DET_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  ABBREV_TAC
   `D = ring_det s (g:B->bool) (\x y. (f:A->B)((m:B->B->A) x y))` THEN
  SUBGOAL_THEN `(D:B) IN ring_carrier s` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[RING_DET]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:B. z IN g ==> ring_mul s z D IN j` ASSUME_TAC THENL
   [X_GEN_TAC `z:B` THEN DISCH_TAC THEN EXPAND_TAC "D" THEN
    MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
     [`s:B ring`; `j:B->bool`; `g:B->bool`;
      `\x y. (f:A->B)((m:B->B->A) x y)`; `\x:B. x`; `z:B`]
     RING_DET_DEPENDENT_COLUMNS_MUL_IDEAL)) THEN
    ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier s` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B` o check (fun th ->
      can (find_term ((=) `ring_sub s:B->B->B`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[] `(x:B) = y ==> x IN j ==> y IN j`) THEN
    TRANS_TAC EQ_TRANS
     `ring_sum s g
        (\y. ring_sub s (if y = x then ring_mul s ((f:A->B) t) x
                         else ring_0 s)
                        (ring_mul s (f((a:B->B->A) x y)) y))` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SUB o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
        CONJ_TAC THENL [COND_CASES_TAC; ALL_TAC] THEN
        ASM_MESON_TAC[RING_MUL; RING_0; SUBSET];
        DISCH_THEN SUBST1_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[RING_SUM_DELTA; RING_MUL];
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:B) IN ring_carrier s` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(if (x:B) = y then t else ring_0 r:A) IN ring_carrier r`
      ASSUME_TAC THENL [COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0]; ALL_TAC] THEN
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUB th]) THEN
      ASM_SIMP_TAC[RING_SUB_RDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_CASES_TAC `y:B = x` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[RING_MUL_LZERO]];
    ALL_TAC] THEN
  UNDISCH_TAC `ring_1 s IN ring_span (r,s) (f:A->B) g` THEN
  ASM_SIMP_TAC[RING_SPAN_FINITE; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:B->A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `D = ring_mul s (ring_1 s) (D:B)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_LID]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th ->
    lhand(concl th) = `ring_1 s:B`)) THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[RING_MUL; SUBSET]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:B) IN ring_carrier s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC] THEN
  MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC[]);;

(* A sum of products f(u i) y_i with u i in an ideal p and y_i in the span  *)
(* of a finite set g is a combination of g with coefficients in p.          *)

let RING_SPAN_IDEAL_COMBINATION = prove
 (`!r s (f:A->B) p g (k:K->bool) u y.
        ring_homomorphism(r,s) f /\ ring_ideal r p /\
        FINITE g /\ g SUBSET ring_carrier s /\
        (!i. i IN k ==> u i IN p /\ y i IN ring_span (r,s) f g)
        ==> ?a. (!e. e IN g ==> a e IN p) /\
                ring_sum s k (\i. ring_mul s (f(u i)) (y i)) =
                ring_sum s g (\e. ring_mul s (f(a e)) e)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  SUBGOAL_THEN `!e:B. e IN g ==> e IN ring_carrier s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN p ==> x IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
   [`s:B ring`;
    `\z. ?a. (!e. e IN g ==> a e IN p) /\
             z = ring_sum s g (\e. ring_mul s ((f:A->B)(a e)) e)`]
   RING_SUM_CLOSED)) THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `\e:B. ring_0 r:A` THEN ASM_SIMP_TAC[IN_RING_IDEAL_0] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
    ASM_SIMP_TAC[RING_MUL_LZERO];
    MAP_EVERY X_GEN_TAC [`x1:B`; `x2:B`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `a1:B->A` STRIP_ASSUME_TAC)
                      (X_CHOOSE_THEN `a2:B->A` STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `\e:B. ring_add r ((a1:B->A) e) (a2 e)` THEN
    ASM_SIMP_TAC[IN_RING_IDEAL_ADD] THEN
    SUBGOAL_THEN
     `!e:B. e IN g
            ==> (a1:B->A) e IN ring_carrier r /\ (a2:B->A) e IN ring_carrier r`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_ADD o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `e:B` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RING_ADD_RDISTRIB];
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[RING_SPAN_FINITE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `b:B->A` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `\e:B. ring_mul r ((u:K->A) i) ((b:B->A) e)` THEN
    ASM_SIMP_TAC[IN_RING_IDEAL_RMUL] THEN
    SUBGOAL_THEN `(u:K->A) i IN ring_carrier r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `e:B` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* Primes above: for s integral over r along f, a prime p of r and an ideal  *)
(* j of s whose preimage lies in p, some prime q of s above j has preimage   *)
(* p. Lying over (j = {0}) and going up (j a prime above a smaller prime)    *)
(* are the special cases.                                                    *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_EXTENSION_PRIME_ABOVE = prove
 (`!r s (f:A->B) p j.
        ring_homomorphism(r,s) f /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal r p /\ ring_ideal s j /\
        (!x. x IN ring_carrier r /\ f x IN j ==> x IN p)
        ==> ?q. prime_ideal s q /\ j SUBSET q /\
                {x | x IN ring_carrier r /\ f x IN q} = p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  SUBGOAL_THEN `!x:A. x IN p ==> x IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:A->B) p SUBSET ring_carrier s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:B ring`; `IMAGE (f:A->B) (ring_carrier r DIFF p)`;
                 `ring_setadd s j (ideal_generated s (IMAGE (f:A->B) p))`]
    PRIME_SUPERIDEAL_EXCLUDING_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_SETADD; RING_IDEAL_IDEAL_GENERATED] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_MULTSYS_HOMOMORPHIC_IMAGE THEN
      EXISTS_TAC `r:A ring` THEN ASM_SIMP_TAC[RING_MULTSYS_NONPRIME];
      ALL_TAC] THEN
    REWRITE_TAC[SET_RULE
     `DISJOINT s (IMAGE (f:A->B) t) <=> !x. x IN t ==> ~(f x IN s)`] THEN
    X_GEN_TAC `t:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    REWRITE_TAC[ring_setadd; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:B`; `w:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?k. FINITE k /\ k SUBSET p /\
          (w:B) IN ideal_generated s (IMAGE (f:A->B) k)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w:B) IN ideal_generated s (IMAGE (f:A->B) p)` THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [IDEAL_GENERATED_FINITARY] THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; FINITE_SUBSET_IMAGE] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(w:B) IN ideal_generated s (IMAGE (f:A->B) k)` THEN
    MP_TAC(ISPECL [`s:B ring`; `k:A->bool`; `f:A->B`]
      IDEAL_GENERATED_FINITE_IMAGE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A->B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!i:A. i IN k
            ==> i IN p /\ i IN ring_carrier r /\ (f:A->B) i IN ring_carrier s`
    ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `IMAGE (c:A->B) k`]
      INTEGRAL_SPAN_FINITE_SET) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:B->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!e:B. e IN g
            ==> ?a. (!y. y IN g ==> a y IN p) /\
                    ring_mul s w e =
                    ring_sum s g (\y. ring_mul s ((f:A->B)(a y)) y)`
    MP_TAC THENL
     [X_GEN_TAC `e:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(e:B) IN ring_carrier s` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `p:A->bool`;
                     `g:B->bool`; `k:A->bool`; `\i:A. i`;
                     `\i:A. ring_mul s ((c:A->B) i) e`]
        RING_SPAN_IDEAL_COMBINATION) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [X_GEN_TAC `i:A` THEN DISCH_TAC THEN CONJ_TAC THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[RING_SPAN_INC]];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:B->A` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o lhand o snd) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(f:A->B) i IN ring_carrier s /\ (c:A->B) i IN ring_carrier s`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
       `ring_mul s (ring_mul s c u) e =
        ring_mul s u (ring_mul s c (e:B))`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:B->B->A`) THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      is_eq(concl th) && lhand(concl th) = `w:B`)) THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier s /\ (w:B) IN ring_carrier s`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET; RING_IDEAL_IDEAL_GENERATED];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `j:B->bool`;
                   `p:A->bool`; `g:B->bool`; `a:B->B->A`; `t:A`]
      INTEGRAL_DETERMINANT_TRICK_IDEAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `e:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(e:B) IN ring_carrier s` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:B` o check (fun th ->
        can (find_term ((=) `a:B->B->A`)) (concl th) &&
        is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      SUBGOAL_THEN
       `ring_sub s (ring_mul s (ring_add s x w) e) (ring_mul s w e) =
        ring_mul s x (e:B)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
         `ring_sub s (ring_mul s (ring_add s x w) e) (ring_mul s w e) =
          ring_mul s x (e:B)`)) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `(d:A) IN p` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_pow r (t:A) (CARD(g:B->bool)) IN p` MP_TAC THENL
     [SUBGOAL_THEN
       `ring_pow r (t:A) (CARD(g:B->bool)) =
        ring_sub r d (ring_sub r d (ring_pow r t (CARD g)))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
         `y = ring_sub r d (ring_sub r d (y:A))`)) THEN
        ASM_SIMP_TAC[RING_POW];
        MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[RING_POW_IN_PRIME_IDEAL]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:B->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [TRANS_TAC SUBSET_TRANS
       `ring_setadd s j (ideal_generated s (IMAGE (f:A->B) p))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_SETADD_SUPERSET_LEFT THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; IN_RING_IDEAL_0;
                   RING_IDEAL_IDEAL_GENERATED];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:A` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM SET_TAC[]; DISCH_TAC] THEN
      ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `ring_setadd s:(B->bool)->(B->bool)->B->bool`))
            (concl th))) THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET; RIGHT_IMP_FORALL_THM; IMP_IMP]
        RING_SETADD_SUPERSET_RIGHT) THEN
      ASM_SIMP_TAC[IN_RING_IDEAL_0; RING_IDEAL_IDEAL_GENERATED] THEN
      CONJ_TAC THENL
       [MESON_TAC[IDEAL_GENERATED_SUBSET; SUBSET];
        MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* Lying over, going up, incomparability and maximal ideals.                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_EXTENSION_LYING_OVER = prove
 (`!r s (f:A->B) p.
        ring_homomorphism(r,s) f /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal r p /\
        (!x. x IN ring_carrier r /\ f x = ring_0 s ==> x IN p)
        ==> ?q. prime_ideal s q /\ {x | x IN ring_carrier r /\ f x IN q} = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `p:A->bool`;
                 `{ring_0 s:B}`] INTEGRAL_EXTENSION_PRIME_ABOVE) THEN
  ASM_REWRITE_TAC[RING_IDEAL_0; IN_SING] THEN MESON_TAC[]);;

let INTEGRAL_EXTENSION_GOING_UP = prove
 (`!r s (f:A->B) p p' q.
        ring_homomorphism(r,s) f /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal s q /\ {x | x IN ring_carrier r /\ f x IN q} = p /\
        prime_ideal r p' /\ p SUBSET p'
        ==> ?q'. prime_ideal s q' /\ q SUBSET q' /\
                 {x | x IN ring_carrier r /\ f x IN q'} = p'`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_EXTENSION_PRIME_ABOVE THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN ASM SET_TAC[]);;

(* Incomparability: for y in the larger ideal but not in q, a monic        *)
(* relation for y modulo q of least degree has its constant term in the     *)
(* common preimage, hence in q, and dividing by y gives one of smaller      *)
(* degree.                                                                   *)

let INTEGRAL_EXTENSION_INCOMPARABLE = prove
 (`!r s (f:A->B) q q'.
        ring_homomorphism(r,s) f /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal s q /\ ring_ideal s q' /\ q SUBSET q' /\
        {x | x IN ring_carrier r /\ f x IN q'} =
        {x | x IN ring_carrier r /\ f x IN q}
        ==> q = q'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  SUBGOAL_THEN `!z:B. z IN q ==> z IN q'` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN ASM_REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:B) IN ring_carrier s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~p ==> F`] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPEC
   `\n. ?c. (!i. i < n ==> c i IN ring_carrier r) /\
            ring_add s (ring_pow s y n)
              (ring_sum s {i | i < n}
                 (\i. ring_mul s ((f:A->B)(c i)) (ring_pow s y i))) IN q`
   num_WOP)) THEN
  MATCH_MP_TAC(TAUT `p /\ ~q ==> (p <=> q) ==> F`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `y:B`]
      INTEGRAL_ELEMENT_RELATION) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `c:num->A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IN_RING_IDEAL_0];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
   (X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_TAC
     `ring_add s (ring_pow s y n)
        (ring_sum s {i | i < n}
           (\i. ring_mul s ((f:A->B)(c i)) (ring_pow s y i))) IN q` THEN
    ASM_REWRITE_TAC[ring_pow; LT; EMPTY_GSPEC; RING_SUM_CLAUSES] THEN
    ASM_SIMP_TAC[RING_ADD_RZERO; RING_1] THEN
    ASM_MESON_TAC[RING_1_NOT_IN_PRIME_IDEAL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN EXISTS_TAC `\i. (c:num->A)(i + 1)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:B ring`; `y:B`; `\i. (f:A->B)((c:num->A) i)`; `n:num`]
    RING_MONIC_RELATION_FACTOR) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(fun th ->
    FIRST_X_ASSUM(MP_TAC o check (fun th' ->
      can (find_term ((=) `ring_pow s (y:B) n`)) (concl th'))) THEN
    REWRITE_TAC[th]) THEN
  ABBREV_TAC
   `R = ring_add s (ring_pow s y (n - 1))
          (ring_sum s {i | i < n - 1}
             (\i. ring_mul s ((f:A->B)((c:num->A)(i + 1)))
                             (ring_pow s y i)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(R:B) IN ring_carrier s` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_SIMP_TAC[RING_ADD; RING_POW; RING_SUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:num->A) 0 IN ring_carrier r` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B)((c:num->A) 0) IN q` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(c:num->A) 0 IN {x | x IN ring_carrier r /\ (f:A->B) x IN q'}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(f:A->B)((c:num->A) 0) =
        ring_sub s (ring_add s (f(c 0)) (ring_mul s y R)) (ring_mul s y R)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
         `a = ring_sub s (ring_add s a b) (b:B)`)) THEN
        ASM_SIMP_TAC[RING_MUL];
        MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_mul s y (R:B) IN q` MP_TAC THENL
   [SUBGOAL_THEN
     `ring_mul s y (R:B) =
      ring_sub s (ring_add s (f((c:num->A) 0)) (ring_mul s y R))
                 ((f:A->B)(c 0))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
       `b = ring_sub s (ring_add s a b) (a:B)`)) THEN
      ASM_SIMP_TAC[RING_MUL];
      MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[RING_MUL_IN_PRIME_IDEAL]]);;

(* A prime q above p is maximal iff p is: by going up for one direction and *)
(* by incomparability with a maximal ideal above q for the other.          *)

let INTEGRAL_EXTENSION_MAXIMAL_IDEAL = prove
 (`!r s (f:A->B) q.
        ring_homomorphism(r,s) f /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal s q
        ==> (maximal_ideal s q <=>
             maximal_ideal r {x | x IN ring_carrier r /\ f x IN q})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `p = {x | x IN ring_carrier r /\ (f:A->B) x IN q}` THEN
  SUBGOAL_THEN `prime_ideal r (p:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN
    EXISTS_TAC `s:B ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `p:A->bool`] MAXIMAL_SUPERIDEAL_EXISTS) THEN
    ASM_SIMP_TAC[PRIME_IMP_PROPER_IDEAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:A->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `p:A->bool`;
                   `m:A->bool`; `q:B->bool`] INTEGRAL_EXTENSION_GOING_UP) THEN
    ASM_SIMP_TAC[MAXIMAL_IMP_PRIME_IDEAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `q':B->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `q':B->bool = q` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [maximal_ideal] o
        check (fun th -> concl th = `maximal_ideal s (q:B->bool)`)) THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `q':B->bool`) THEN
      ASM_SIMP_TAC[PRIME_IMP_PROPER_IDEAL; PSUBSET] THEN ASM SET_TAC[];
      ASM_MESON_TAC[]];
    MP_TAC(ISPECL [`s:B ring`; `q:B->bool`] MAXIMAL_SUPERIDEAL_EXISTS) THEN
    ASM_SIMP_TAC[PRIME_IMP_PROPER_IDEAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:B->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `q:B->bool = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC INTEGRAL_EXTENSION_INCOMPARABLE THEN
    MAP_EVERY EXISTS_TAC [`r:A ring`; `s:B ring`; `f:A->B`] THEN
    ASM_SIMP_TAC[MAXIMAL_IMP_RING_IDEAL] THEN
    SUBGOAL_THEN
     `proper_ideal r {x | x IN ring_carrier r /\ (f:A->B) x IN m}`
    MP_TAC THENL
     [MATCH_MP_TAC PROPER_IDEAL_HOMOMORPHIC_PREIMAGE THEN
      EXISTS_TAC `s:B ring` THEN ASM_SIMP_TAC[MAXIMAL_IMP_PROPER_IDEAL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [maximal_ideal] o
      check (fun th -> concl th = `maximal_ideal r (p:A->bool)`)) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o
      SPEC `{x | x IN ring_carrier r /\ (f:A->B) x IN m}`) THEN
    REWRITE_TAC[PSUBSET] THEN EXPAND_TAC "p" THEN ASM SET_TAC[]]);;

(* For a monomorphism into a domain, a nonzero prime has nonzero preimage   *)
(* (incomparability with the zero ideal).                                    *)

let INTEGRAL_EXTENSION_PRIME_NONZERO = prove
 (`!r s (f:A->B) q.
        ring_monomorphism(r,s) f /\ integral_domain s /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        prime_ideal s q /\ ~(q = {ring_0 s})
        ==> ~({x | x IN ring_carrier r /\ f x IN q} = {ring_0 r})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `{ring_0 s:B}`;
                 `q:B->bool`] INTEGRAL_EXTENSION_INCOMPARABLE) THEN
  ASM_SIMP_TAC[PRIME_IDEAL_0; PRIME_IMP_RING_IDEAL; SING_SUBSET;
               IN_RING_IDEAL_0] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]; ASM_MESON_TAC[RING_0]]);;
