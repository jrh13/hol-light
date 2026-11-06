(* ========================================================================= *)
(* Free algebras: products and isomorphic copies; isomorphic number fields.  *)
(*                                                                           *)
(* For a ring l with a free basis g of size n over k along h                 *)
(* (free_basis, basis_coordinates, mul_matrix, the trace algebra_trace and   *)
(* the discriminant basis_discriminant of Library/ring_det.ml, where also    *)
(* the trace forms are treated: BASIS_DISCRIMINANT_EQ_0,                     *)
(* BASIS_DISCRIMINANT_DEGENERATE, ALGEBRA_TRACE_NILPOTENT,                   *)
(* BASIS_DISCRIMINANT_NILPOTENT):                                            *)
(*                                                                           *)
(* - free bases, coordinates and traces of a product ring prod_ring l1 l2    *)
(*   (FREE_BASIS_PROD_RING, BASIS_COORDINATES_PROD_RING,                     *)
(*   ALGEBRA_TRACE_PROD_RING);                                               *)
(* - a ring isomorphism carries free bases and traces                        *)
(*   (FREE_BASIS_ISOMORPHIC_IMAGE, ALGEBRA_TRACE_ISOMORPHIC_IMAGE, from      *)
(*   the base change lemma ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE of           *)
(*   Library/ring_det.ml);                                                   *)
(* - finite dimensional algebras over a field have free bases, of size the   *)
(*   extension degree (FREE_BASIS_EXISTS of Library/fieldtheory.ml; every    *)
(*   free basis has that size: FREE_BASIS_EXTENSION_DEGREE of                *)
(*   Library/fieldtheory.ml);                                                *)
(* - a ring isomorphic to a number field is a number field of the same       *)
(*   degree and discriminant (NUMBER_FIELD_ISOMORPHIC_IMAGE).                *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (prod_ring, sums in prod_ring:                *)
(* RING_SUM_PROD_RING), Library/fieldtheory.ml (extension_degree),           *)
(* Library/ring_det.ml (free bases, the base change lemma                    *)
(* ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE), ANT/numfield.ml,                   *)
(* ANT/ring_of_integers.ml (RING_OF_INTEGERS_FREE) and ANT/discriminant.ml   *)
(* (number_field_discriminant).                                              *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/discriminant.ml";;

(* ------------------------------------------------------------------------- *)
(* Products.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* A combination of the concatenated basis is the pair of combinations.      *)
let EXTENSION_LINCOMB_PROD_RING = prove
 (`!k:A ring l1:B ring l2:C ring h1 h2 n1 n2 g1 g2 c.
        ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
        (!i. i < n1:num ==> g1 i IN ring_carrier l1) /\
        (!i. i < n2 ==> g2 i IN ring_carrier l2) /\
        (!i. i < n1 + n2 ==> c i IN ring_carrier k)
        ==> ring_sum (prod_ring l1 l2) {i | i < n1 + n2}
              (\i. ring_mul (prod_ring l1 l2) (h1(c i),h2(c i))
                     (if i < n1 then (g1 i,ring_0 l2)
                      else (ring_0 l1,g2(i - n1)))) =
            ring_sum l1 {i | i < n1} (\i. ring_mul l1 (h1(c i)) (g1 i)),
            ring_sum l2 {i | i < n2} (\i. ring_mul l2 (h2(c(n1 + i))) (g2 i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i < n1 + n2
        ==> (h1:A->B)((c:num->A) i) IN ring_carrier l1 /\
            (h2:A->C)(c i) IN ring_carrier l2`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_PROD_RING o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_MUL THEN
    ASM_SIMP_TAC[PROD_RING; IN_CROSS] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[IN_CROSS; RING_0] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[PAIR_EQ; o_DEF; RING_SUM_NUMSEG_LT_ADD] THEN
  REWRITE_TAC[ARITH_RULE `~(n1 + i < n1:num)`; ADD_SUB2] THEN
  REWRITE_TAC[PROD_RING; COND_RAND] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[RING_ADD_RZERO; RING_SUM]
     `ring_sum r t (f:num->B) = ring_0 r /\
      ring_sum r (s:num->bool) g = ring_sum r s h
      ==> ring_add r (ring_sum r s g) (ring_sum r t f) = ring_sum r s h`);
    MATCH_MP_TAC(MESON[RING_ADD_LZERO; RING_SUM]
     `ring_sum r t (f:num->C) = ring_0 r /\
      ring_sum r (s:num->bool) g = ring_sum r s h
      ==> ring_add r (ring_sum r t f) (ring_sum r s g) = ring_sum r s h`)] THEN
  CONJ_TAC THEN
  (MATCH_MP_TAC RING_SUM_EQ_0 ORELSE MATCH_MP_TAC RING_SUM_EQ) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_MUL_RZERO; ARITH_RULE `i < n1 ==> i < n1 + n2:num`;
               ARITH_RULE `i < n2 ==> n1 + i < n1 + n2:num`]);;

let FREE_BASIS_PROD_RING = prove
 (`!k:A ring l1:B ring l2:C ring h1 h2 n1 n2 g1 g2.
        ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
        free_basis (k,l1) h1 n1 g1 /\ free_basis (k,l2) h2 n2 g2
        ==> free_basis (k,prod_ring l1 l2) (\a. h1 a,h2 a) (n1 + n2)
              (\i. if i < n1 then (g1 i,ring_0 l2)
                   else (ring_0 l1,g2(i - n1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h1:A->B`; `k:A ring`; `l1:B ring`; `n1:num`; `g1:num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`h2:A->C`; `k:A ring`; `l2:C ring`; `n2:num`; `g2:num->C`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[free_basis; CONJUNCT1 PROD_RING; FORALL_PAIR_THM; IN_CROSS] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[IN_CROSS; RING_0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`y1:B`; `y2:C`] THEN STRIP_TAC THEN
    EXISTS_TAC
     `\i. if i < n1 then basis_coordinates (k,l1) (h1:A->B) n1 g1 y1 i
          else basis_coordinates (k,l2) (h2:A->C) n2 g2 y2 (i - n1)` THEN
    SUBGOAL_THEN
     `!i. i < n1 + n2
          ==> (if i < n1 then basis_coordinates (k,l1) (h1:A->B) n1 g1 y1 i
               else basis_coordinates (k,l2) (h2:A->C) n2 g2 y2 (i - n1)) IN
              ring_carrier k`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      MATCH_MP_TAC BASIS_COORDINATES_IN_CARRIER THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`k:A ring`; `l1:B ring`; `l2:C ring`; `h1:A->B`;
      `h2:A->C`; `n1:num`; `n2:num`; `g1:num->B`; `g2:num->C`;
      `\i. if i < n1 then basis_coordinates (k,l1) (h1:A->B) n1 g1 y1 i
           else basis_coordinates (k,l2) (h2:A->C) n2 g2 y2 (i - n1)`]
      EXTENSION_LINCOMB_PROD_RING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(n1 + i < n1:num)`; ADD_SUB2; PAIR_EQ] THEN
    CONJ_TAC THEN CONV_TAC SYM_CONV THENL
     [TRANS_TAC EQ_TRANS
       `ring_sum l1 {i | i < n1}
          (\i. ring_mul l1 ((h1:A->B)(basis_coordinates (k,l1) h1 n1 g1 y1 i))
                           ((g1:num->B) i))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `c:num->A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l1:B ring`; `l2:C ring`; `h1:A->B`;
      `h2:A->C`; `n1:num`; `n2:num`; `g1:num->B`; `g2:num->C`; `c:num->A`]
      EXTENSION_LINCOMB_PROD_RING) THEN
    ASM_REWRITE_TAC[PROD_RING; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o SYM)) THEN
    MP_TAC(ISPECL [`h1:A->B`; `k:A ring`; `l1:B ring`; `n1:num`; `g1:num->B`;
                   `c:num->A`] FREE_BASIS_INDEPENDENT) THEN
    MP_TAC(ISPECL [`h2:A->C`; `k:A ring`; `l2:C ring`; `n2:num`; `g2:num->C`;
                   `\i. (c:num->A)(n1 + i)`] FREE_BASIS_INDEPENDENT) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n1 ==> i < n1 + n2:num`;
                 ARITH_RULE `i < n2 ==> n1 + i < n1 + n2:num`] THEN
    DISCH_THEN(LABEL_TAC "2") THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i:num < n1` THEN ASM_SIMP_TAC[] THEN
    REMOVE_THEN "2" (MP_TAC o SPEC `i - n1:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i:num < n1) /\ i < n1 + n2 ==> i - n1 < n2`;
                 ARITH_RULE `~(i:num < n1) ==> n1 + i - n1 = i`]]);;

let BASIS_COORDINATES_PROD_RING = prove
 (`!k:A ring l1:B ring l2:C ring h1 h2 n1 n2 g1 g2 y1 y2 i.
        ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
        free_basis (k,l1) h1 n1 g1 /\ free_basis (k,l2) h2 n2 g2 /\
        y1 IN ring_carrier l1 /\ y2 IN ring_carrier l2 /\ i < n1 + n2
        ==> basis_coordinates (k,prod_ring l1 l2) (\a. h1 a,h2 a) (n1 + n2)
              (\i. if i < n1 then (g1 i,ring_0 l2)
                   else (ring_0 l1,g2(i - n1)))
              (y1,y2) i =
            if i < n1 then basis_coordinates (k,l1) h1 n1 g1 y1 i
            else basis_coordinates (k,l2) h2 n2 g2 y2 (i - n1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h1:A->B`; `k:A ring`; `l1:B ring`; `n1:num`; `g1:num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`h2:A->C`; `k:A ring`; `l2:C ring`; `n2:num`; `g2:num->C`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`\a. (h1:A->B) a,(h2:A->C) a`; `k:A ring`;
    `prod_ring (l1:B ring) (l2:C ring)`; `n1 + n2:num`;
    `\i. if i < n1 then ((g1:num->B) i,ring_0 l2)
         else (ring_0 l1,(g2:num->C)(i - n1))`; `(y1:B,y2:C)`]
    BASIS_COORDINATES) THEN
  ASM_SIMP_TAC[FREE_BASIS_PROD_RING; CONJUNCT1 PROD_RING; IN_CROSS] THEN
  ABBREV_TAC
   `c = basis_coordinates (k,prod_ring l1 l2) (\a. (h1:A->B) a,(h2:A->C) a)
          (n1 + n2) (\i. if i < n1 then ((g1:num->B) i,ring_0 l2)
                         else (ring_0 l1,(g2:num->C)(i - n1))) (y1,y2)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `l1:B ring`; `l2:C ring`; `h1:A->B`;
      `h2:A->C`; `n1:num`; `n2:num`; `g1:num->B`; `g2:num->C`; `c:num->A`]
      EXTENSION_LINCOMB_PROD_RING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`h1:A->B`; `k:A ring`; `l1:B ring`; `n1:num`;
                   `g1:num->B`; `y1:B`; `c:num->A`]
      BASIS_COORDINATES_UNIQUE) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n1 ==> i < n1 + n2:num`];
    MP_TAC(ISPECL [`h2:A->C`; `k:A ring`; `l2:C ring`; `n2:num`;
                   `g2:num->C`; `y2:C`; `\i. (c:num->A)(n1 + i)`]
      BASIS_COORDINATES_UNIQUE) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n2 ==> n1 + i < n1 + n2:num`] THEN
    DISCH_THEN(MP_TAC o SPEC `i - n1:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i:num < n1) /\ i < n1 + n2 ==> i - n1 < n2`;
                 ARITH_RULE `~(i:num < n1) ==> n1 + i - n1 = i`]]);;

let ALGEBRA_TRACE_PROD_RING = prove
 (`!k:A ring l1:B ring l2:C ring h1 h2 n1 n2 g1 g2 x1 x2.
        ring_homomorphism(k,l1) h1 /\ ring_homomorphism(k,l2) h2 /\
        free_basis (k,l1) h1 n1 g1 /\ free_basis (k,l2) h2 n2 g2 /\
        x1 IN ring_carrier l1 /\ x2 IN ring_carrier l2
        ==> algebra_trace (k,prod_ring l1 l2) (\a. h1 a,h2 a) (x1,x2) =
            ring_add k (algebra_trace (k,l1) h1 x1)
                       (algebra_trace (k,l2) h2 x2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h1:A->B`; `k:A ring`; `l1:B ring`; `n1:num`; `g1:num->B`]
    FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`h2:A->C`; `k:A ring`; `l2:C ring`; `n2:num`; `g2:num->C`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l1:B ring`; `l2:C ring`; `h1:A->B`; `h2:A->C`;
                 `n1:num`; `n2:num`; `g1:num->B`; `g2:num->C`]
    FREE_BASIS_PROD_RING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\a. (h1:A->B) a,(h2:A->C) a`; `k:A ring`;
    `prod_ring (l1:B ring) (l2:C ring)`; `n1 + n2:num`;
    `\i. if i < n1 then ((g1:num->B) i,ring_0 l2)
         else (ring_0 l1,(g2:num->C)(i - n1))`; `(x1:B,x2:C)`]
    ALGEBRA_TRACE_FREE_BASIS) THEN
  MP_TAC(ISPECL [`h1:A->B`; `k:A ring`; `l1:B ring`; `n1:num`; `g1:num->B`;
                 `x1:B`] ALGEBRA_TRACE_FREE_BASIS) THEN
  MP_TAC(ISPECL [`h2:A->C`; `k:A ring`; `l2:C ring`; `n2:num`; `g2:num->C`;
                 `x2:C`] ALGEBRA_TRACE_FREE_BASIS) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_PAIRED; CONJUNCT1 PROD_RING;
                  IN_CROSS] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[mul_matrix; RING_SUM_NUMSEG_LT_ADD;
              ARITH_RULE `~(n1 + i < n1:num)`; ADD_SUB2] THEN
  BINOP_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[PROD_RING; RING_MUL_RZERO] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) BASIS_COORDINATES_PROD_RING o
    lhand o snd) THEN
  ASM_SIMP_TAC[RING_MUL; RING_0; ARITH_RULE `i < n1 ==> i < n1 + n2:num`;
               ARITH_RULE `i < n2 ==> n1 + i < n1 + n2:num`;
               ARITH_RULE `~(n1 + i < n1:num)`; ADD_SUB2]);;

(* ------------------------------------------------------------------------- *)
(* Isomorphic copies (by the base change lemmas of Library/ring_det.ml).     *)
(* ------------------------------------------------------------------------- *)

let FREE_BASIS_ISOMORPHIC_IMAGE = prove
 (`!k:A ring l:B ring l':C ring h f n g.
        ring_homomorphism(k,l) h /\ ring_isomorphism(l,l') f /\
        free_basis (k,l) h n g
        ==> free_basis (k,l') (f o h) n (f o g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RING_ISOMORPHISM] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN
   `!c. (!i. i < n ==> c i IN ring_carrier k)
        ==> (f:B->C)(ring_sum l {i | i < n}
                       (\i. ring_mul l ((h:A->B)(c i)) ((g:num->B) i))) =
            ring_sum l' {i | i < n} (\i. ring_mul l' (f(h(c i))) (f(g i)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`l:B ring`; `l':C ring`; `f:B->C`;
      `{i:num | i < n}`; `\i. (h:A->B)((c:num->A) i)`; `g:num->B`]
      RING_HOMOMORPHISM_SUM_MUL)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[free_basis; o_THM] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `l:B ring` THEN ASM_SIMP_TAC[];
    X_GEN_TAC `y:C` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    EXISTS_TAC `basis_coordinates (k,l) (h:A->B) n g x` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis_coordinates (k,l) (h:A->B) n g x`) THEN
    ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER; BASIS_COORDINATES_EXPAND];
    X_GEN_TAC `c:num->A` THEN STRIP_TAC THEN
    MATCH_MP_TAC FREE_BASIS_INDEPENDENT THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `l:B ring`; `g:num->B`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!x y. x IN ring_carrier l /\ y IN ring_carrier l /\
                       (f:B->C) x = f y ==> x = y` THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `l':C ring`; `f:B->C`] RING_HOMOMORPHISM_0) THEN
    ASM_SIMP_TAC[RING_SUM; RING_0]]);;

let ALGEBRA_TRACE_ISOMORPHIC_IMAGE = prove
 (`!k:A ring l:B ring l':C ring h f n g x.
        ring_homomorphism(k,l) h /\ ring_isomorphism(l,l') f /\
        free_basis (k,l) h n g /\ x IN ring_carrier l
        ==> algebra_trace (k,l') (f o h) (f x) =
            algebra_trace (k,l) h x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `l':C ring`; `h:A->B`; `f:B->C`;
                 `n:num`; `g:num->B`] FREE_BASIS_ISOMORPHIC_IMAGE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `ring_homomorphism(k,l') ((f:B->C) o (h:A->B))` ASSUME_TAC
  THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `(f:B->C) o (h:A->B)`; `I:A->A`; `f:B->C`;
    `k:A ring`; `l:B ring`; `k:A ring`; `l':C ring`; `n:num`; `g:num->B`;
    `x:B`] ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_I; I_THM; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Number fields: degree and discriminant of an isomorphic copy.             *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_ISOMORPHIC_IMAGE = prove
 (`!(k:A ring) (l:B ring) f.
        number_field k /\ ring_isomorphism(k,l) f
        ==> number_field l /\
            extension_degree(subfield_generated l {ring_0 l},l) I =
            extension_degree(subfield_generated k {ring_0 k},k) I /\
            number_field_discriminant l = number_field_discriminant k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `field(l:B ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ISOMORPHIC_RING_FIELDNESS; isomorphic_ring]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`]
    PRIME_SUBFIELD_TOWER_LAW) THEN
  ASM_SIMP_TAC[FINITE_EXTENSION_ISOMORPHISM; EXTENSION_DEGREE_ISOMORPHISM] THEN
  REWRITE_TAC[MULT_CLAUSES] THEN STRIP_TAC THEN
  SUBGOAL_THEN `number_field(l:B ring)` ASSUME_TAC THENL
   [REWRITE_TAC[number_field] THEN ASM_MESON_TAC[number_field]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FREE) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)` THEN
  DISCH_THEN(X_CHOOSE_TAC `w:num->A`) THEN
  SUBGOAL_THEN
   `ring_isomorphism(ring_of_integers k,ring_of_integers l) (f:A->B)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_ISOMORPHISM_RING_OF_INTEGERS];
                    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism(integer_ring,ring_of_integers k) (ring_of_int k:int->A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers k:A ring`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) o ring_of_int k = ring_of_int l` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_RING_OF_INT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`integer_ring`; `ring_of_integers k:A ring`;
                 `ring_of_integers l:B ring`; `ring_of_int k:int->A`;
                 `f:A->B`; `n:num`; `w:num->A`]
    FREE_BASIS_ISOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `n:num`; `(f:A->B) o (w:num->A)`]
    NUMBER_FIELD_DISCRIMINANT_BASIS) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    NUMBER_FIELD_DISCRIMINANT_BASIS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[basis_discriminant] THEN MATCH_MP_TAC RING_DET_EQ THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(w:num->A) i IN ring_carrier(ring_of_integers k) /\
    w j IN ring_carrier(ring_of_integers k)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FREE_BASIS_IN_CARRIER]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN
   `ring_mul (ring_of_integers l) ((f:A->B) (w i)) (f (w j)) =
    f (ring_mul (ring_of_integers k) ((w:num->A) i) (w j))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                   `f:A->B`] RING_HOMOMORPHISM_MUL) THEN
    ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`integer_ring`; `ring_of_integers k:A ring`;
                 `ring_of_integers l:B ring`; `ring_of_int k:int->A`;
                 `f:A->B`; `n:num`; `w:num->A`;
                 `ring_mul (ring_of_integers k) ((w:num->A) i) (w j)`]
    ALGEBRA_TRACE_ISOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_MUL]);;
