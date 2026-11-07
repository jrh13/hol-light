(* ========================================================================= *)
(* The Mordell curves y^2 = x^3 + k (Mordell 1922; Baker, Transcendental     *)
(* Number Theory, Ch. 4).                                                    *)
(*                                                                           *)
(* Purpose: finiteness of the integer points on y^2 = x^3 + k for every      *)
(* non-zero integer k, via THUE and the reduction theory of binary cubic     *)
(* forms. Route (Mordell correspondence): to a solution (x,y) attach the     *)
(* form F(u,v) = u^3 - 3 x u v^2 - 2 y v^3 of discriminant -108 k.           *)
(*  - If F has a non-trivial integer zero then t^3 - 3 x t - 2 y has an      *)
(*    integer root t, and (x - t^2)^2 (4 x - t^2) = -4 k bounds x and y.     *)
(*  - Otherwise F = G o gamma with G in the finite set Phi of the            *)
(*    reduction theory and gamma = (p q; r s) in SL2(Z); G(p,r) = 1 and G    *)
(*    has no non-trivial integer zero, so every root of G(t,1) has degree    *)
(*    3 and THUE applies; (x,y) is determined by (G,p,r).                    *)
(*                                                                           *)
(* Main results: MORDELL, MORDELL_THUE_CUBIC (THUE for integer cubic forms   *)
(* without non-trivial integer zeros).                                       *)
(*                                                                           *)
(* Uses: Baker/thue.ml (THUE, THUE_SUM_0_3, THUE_VSUM_SMALL),                *)
(* Baker/cubic_reduction.ml (CUBIC_FORM_REDUCTION), Baker/nf_order.ml        *)
(* (NF_CUBIC_ROOT_DEGREE), Baker/algint.ml                                   *)
(* (ALGEBRAIC_INTEGER_RATIONAL).                                             *)
(* ========================================================================= *)

needs "Baker/thue.ml";;
needs "Baker/cubic_reduction.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Cubic forms without non-trivial integer zeros: the leading coefficient    *)
(* is non-zero and G(t,1) has no rational root.                              *)
(* ------------------------------------------------------------------------- *)

let MORDELL_NZ_LEADING = prove
 (`!a b c d.
        (!u v. integer u /\ integer v /\
               a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 +
               d * v pow 3 = &0
               ==> u = &0 /\ v = &0)
        ==> ~(a = &0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPECL [`&1:real`; `&0:real`]) THEN
  REWRITE_TAC[INTEGER_CLOSED] THEN CONV_TAC REAL_RING);;

let MORDELL_NZ_NO_RATIONAL_ROOT = prove
 (`!a b c d.
        (!u v. integer u /\ integer v /\
               a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 +
               d * v pow 3 = &0
               ==> u = &0 /\ v = &0)
        ==> !q. rational q
                ==> ~(a * q pow 3 + b * q pow 2 + c * q + d = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[rational; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:real`; `m:real`; `n:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:real`; `n:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(n:real = &0)` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The Thue theorem for integer cubic forms without non-trivial integer      *)
(* zeros.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MORDELL_THUE_CUBIC = prove
 (`!a b c d m.
        integer a /\ integer b /\ integer c /\ integer d /\ integer m /\
        (!u v. integer u /\ integer v /\
               a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 +
               d * v pow 3 = &0
               ==> u = &0 /\ v = &0)
        ==> FINITE {(u,v) | integer u /\ integer v /\
                            a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 +
                            d * v pow 3 = m}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MORDELL_NZ_LEADING) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MORDELL_NZ_NO_RATIONAL_ROOT) THEN
  MP_TAC(SPECL [`3`; `\i. if i = 0 then a else if i = 1 then b
                          else if i = 2 then c else d:real`;
                `m:real`] THUE) THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `!u v. sum(0..3) (\i. (if i = 0 then a else if i = 1 then b
                          else if i = 2 then c else d) *
                         u pow (3 - i) * v pow i) =
          a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 + d * v pow 3`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[THUE_SUM_0_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:complex` THEN REWRITE_TAC[THUE_VSUM_SMALL] THEN BETA_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_POW_1; complex_pow; COMPLEX_MUL_RID] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `e:num->real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC NF_CUBIC_ROOT_DEGREE THEN
  MAP_EVERY EXISTS_TAC
   [`a:real`; `b:real`; `c:real`; `d:real`; `t:complex`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transport of the zero-freeness along an SL2(Z) substitution.              *)
(* ------------------------------------------------------------------------- *)

let MORDELL_NZ_TRANSPORT = prove
 (`!a b c d a1 b1 c1 d1 p q r s.
        integer p /\ integer q /\ integer r /\ integer s /\
        p * s - q * r = &1 /\
        (!u v. a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 +
               d * v pow 3 =
               a1 * (p * u + q * v) pow 3 +
               b1 * (p * u + q * v) pow 2 * (r * u + s * v) +
               c1 * (p * u + q * v) * (r * u + s * v) pow 2 +
               d1 * (r * u + s * v) pow 3) /\
        (!u v. integer u /\ integer v /\
               a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 +
               d * v pow 3 = &0
               ==> u = &0 /\ v = &0)
        ==> (!u v. integer u /\ integer v /\
                   a1 * u pow 3 + b1 * u pow 2 * v + c1 * u * v pow 2 +
                   d1 * v pow 3 = &0
                   ==> u = &0 /\ v = &0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "id") (LABEL_TAC "nz"))))))) THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "nz"
   (MP_TAC o SPECL [`s * u - q * v:real`; `p * v - r * u:real`]) THEN
  REMOVE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(p:real) * (s * u - q * v) + q * (p * v - r * u) = u /\
                r * (s * u - q * v) + s * (p * v - r * u) = v`
   (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `(p:real) * s - q * r = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  UNDISCH_TAC `(p:real) * s - q * r = &1` THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Injectivity: two solutions with the same (G,p,r) coincide.                *)
(* ------------------------------------------------------------------------- *)

let MORDELL_SHIFT = prove
 (`!x1 y1 x2 y2 a1 b1 c1 d1 p r q1 s1 q2 s2.
        (p:real) * s1 - q1 * r = &1 /\ p * s2 - q2 * r = &1 /\
        (!u v. &1 * u pow 3 + &0 * u pow 2 * v + --(&3 * x1) * u * v pow 2 +
               --(&2 * y1) * v pow 3 =
               a1 * (p * u + q1 * v) pow 3 +
               b1 * (p * u + q1 * v) pow 2 * (r * u + s1 * v) +
               c1 * (p * u + q1 * v) * (r * u + s1 * v) pow 2 +
               d1 * (r * u + s1 * v) pow 3) /\
        (!u v. &1 * u pow 3 + &0 * u pow 2 * v + --(&3 * x2) * u * v pow 2 +
               --(&2 * y2) * v pow 3 =
               a1 * (p * u + q2 * v) pow 3 +
               b1 * (p * u + q2 * v) pow 2 * (r * u + s2 * v) +
               c1 * (p * u + q2 * v) * (r * u + s2 * v) pow 2 +
               d1 * (r * u + s2 * v) pow 3)
        ==> x1 = x2 /\ y1 = y2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "f1") (LABEL_TAC "f2")))) THEN
  SUBGOAL_THEN `?j:real. q2 = q1 + j * p /\ s2 = s1 + j * r`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `s1 * (q2 - q1) - q1 * (s2 - s1):real` THEN
    MAP_EVERY UNDISCH_TAC
     [`(p:real) * s1 - q1 * r = &1`; `(p:real) * s2 - q2 * r = &1`] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. &1 * (u:real) pow 3 + &0 * u pow 2 * v + --(&3 * x2) * u * v pow 2 +
          --(&2 * y2) * v pow 3 =
          &1 * (u + j * v) pow 3 + &0 * (u + j * v) pow 2 * v +
          --(&3 * x1) * (u + j * v) * v pow 2 + --(&2 * y1) * v pow 3`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
    SUBGOAL_THEN `(p:real) * u + q2 * v = p * (u + j * v) + q1 * v /\
                  r * u + s2 * v = r * (u + j * v) + s1 * v`
     STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REMOVE_THEN "f2" (fun th -> REWRITE_TAC[th]) THEN
    REMOVE_THEN "f1" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`&0:real`; `&1:real`] th) THEN
    MP_TAC(SPECL [`&1:real`; `&1:real`] th) THEN
    MP_TAC(SPECL [`-- &1:real`; `&1:real`] th)) THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* A finiteness principle: a set related to a finite set by a relation       *)
(* that is total on it and injective is finite.                              *)
(* ------------------------------------------------------------------------- *)

let MORDELL_FINITE_REL = prove
 (`!(R:A->B->bool) s t.
        FINITE t /\
        (!x. x IN s ==> ?y. y IN t /\ R x y) /\
        (!x x' y. x IN s /\ x' IN s /\ y IN t /\ R x y /\ R x' y ==> x = x')
        ==> FINITE s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:A->B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `t:B->bool`; `s:A->bool`]
    FINITE_IMAGE_INJ_GENERAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The reducible case: an integer root t of t^3 - 3 x t - 2 y.               *)
(* ------------------------------------------------------------------------- *)

let MORDELL_INTEGER_ABS_LE_POW2 = prove
 (`!n. integer n ==> abs n <= n pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n:real = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPEC `n:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`abs(n:real) - &1`; `abs(n:real)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `n:real` REAL_POW2_ABS) THEN CONV_TAC REAL_ARITH);;

let MORDELL_RED_BOUND = prove
 (`!k x y t.
        integer k /\ ~(k = &0) /\ integer x /\ integer y /\ integer t /\
        y pow 2 = x pow 3 + k /\ &2 * y = t pow 3 - &3 * x * t
        ==> abs x <= &28 * abs k pow 3 /\ abs y <= &28 * abs k pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A = (x:real) - t pow 2` THEN
  ABBREV_TAC `B = &4 * (x:real) - t pow 2` THEN
  SUBGOAL_THEN `(A:real) pow 2 * B = --(&4 * k)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real) pow 2 = x pow 3 + k`;
      `&2 * (y:real) = t pow 3 - &3 * x * t`] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `integer(A:real) /\ integer(B:real)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REPEAT(MATCH_MP_TAC INTEGER_SUB ORELSE MATCH_MP_TAC INTEGER_MUL ORELSE
           MATCH_MP_TAC INTEGER_POW ORELSE CONJ_TAC) THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((A:real) = &0) /\ ~((B:real) = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `(A:real) pow 2 * B = --(&4 * k)` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((k:real) = &0)` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(SPEC `A:real` REAL_ABS_INTEGER_LEMMA) THEN
  MP_TAC(SPEC `B:real` REAL_ABS_INTEGER_LEMMA) THEN
  MP_TAC(SPEC `k:real` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs(A:real) pow 2 * abs(B:real) = &4 * abs(k:real)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_POW; GSYM REAL_ABS_MUL] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_NUM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`abs(A:real) - &1`; `abs(A:real)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `&1 <= abs(A:real)` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`abs(A:real) pow 2 - &1`; `abs(B:real)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_ABS_POS] THEN
    UNDISCH_TAC `&0 <= (abs(A:real) - &1) * abs A` THEN
    UNDISCH_TAC `&1 <= abs(A:real)` THEN CONV_TAC REAL_ARITH;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`abs(A:real) pow 2`; `abs(B:real) - &1`] REAL_LE_MUL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN UNDISCH_TAC `&1 <= abs(B:real)` THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `abs(A:real) <= &4 * abs(k:real) /\ abs(B:real) <= &4 * abs(k:real)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&0 <= (abs(A:real) - &1) * abs A`;
      `&0 <= (abs(A:real) pow 2 - &1) * abs(B:real)`;
      `&0 <= abs(A:real) pow 2 * (abs(B:real) - &1)`;
      `abs(A:real) pow 2 * abs(B:real) = &4 * abs(k:real)`] THEN
    CONV_TAC REAL_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(x:real) <= &3 * abs(k:real)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&3 * (t:real) pow 2 = B - &4 * A /\ &4 * x = B + t pow 2`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
    MAP_EVERY UNDISCH_TAC
     [`&3 * (t:real) pow 2 = B - &4 * A`; `&4 * (x:real) = B + t pow 2`;
      `abs(A:real) <= &4 * abs(k:real)`;
      `abs(B:real) <= &4 * abs(k:real)`] THEN
    CONV_TAC REAL_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(k:real) <= abs k pow 3` ASSUME_TAC THENL
   [MP_TAC(SPECL [`1`; `3`; `abs(k:real)`] REAL_POW_MONO) THEN
    ASM_REWRITE_TAC[REAL_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(x:real) pow 3 <= (&3 * abs(k:real)) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  MP_TAC(SPEC `y:real` MORDELL_INTEGER_ABS_LE_POW2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(y:real) pow 2 <= abs(x:real) pow 3 + abs(k:real)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(a:real) <= abs a /\ abs a = b ==> a + k <= b + abs k`) THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_ABS_LE]; REWRITE_TAC[REAL_ABS_POW]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`abs(x:real) <= &3 * abs(k:real)`; `abs(k:real) <= abs k pow 3`;
    `abs(x:real) pow 3 <= (&3 * abs(k:real)) pow 3`;
    `abs(y:real) <= y pow 2`;
    `(y:real) pow 2 <= abs(x:real) pow 3 + abs(k:real)`] THEN
  MP_TAC(SPECL [`abs(k:real)`; `3`] REAL_POW_LE) THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONV_TAC REAL_ARITH);;

let MORDELL_REDUCIBLE_FINITE = prove
 (`!k. integer k /\ ~(k = &0)
       ==> FINITE {(x,y) | integer x /\ integer y /\ y pow 2 = x pow 3 + k /\
                           ?t. integer t /\ &2 * y = t pow 3 - &3 * x * t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{x | integer x /\ --(&28 * abs(k:real) pow 3) <= x /\
         x <= &28 * abs k pow 3} CROSS
    {x | integer x /\ --(&28 * abs(k:real) pow 3) <= x /\
         x <= &28 * abs k pow 3}` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_INTSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS;
              IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:real`; `x:real`; `y:real`; `t:real`] MORDELL_RED_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A non-trivial integer zero of u^3 - 3 x u v^2 - 2 y v^3 gives an integer  *)
(* root of t^3 - 3 x t - 2 y (a rational root of a monic integer cubic).     *)
(* ------------------------------------------------------------------------- *)

let MORDELL_CASE_SPLIT = prove
 (`!x y. integer x /\ integer y /\
         ~(!u v. integer u /\ integer v /\
                 &1 * u pow 3 + &0 * u pow 2 * v + --(&3 * x) * u * v pow 2 +
                 --(&2 * y) * v pow 3 = &0
                 ==> u = &0 /\ v = &0)
         ==> ?t. integer t /\ &2 * y = t pow 3 - &3 * x * t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `~(v:real = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(u:real = &0 /\ v = &0)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `&1 * (u:real) pow 3 + &0 * u pow 2 * v + --(&3 * x) * u * v pow 2 +
      --(&2 * y) * v pow 3 = &0` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `((u:real) / v) pow 3 - &3 * x * (u / v) - &2 * y = &0`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `&1 * (u:real) pow 3 + &0 * u pow 2 * v + --(&3 * x) * u * v pow 2 +
      --(&2 * y) * v pow 3 = &0` THEN
    UNDISCH_TAC `~(v:real = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  EXISTS_TAC `(u:real) / v` THEN CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `((u:real) / v) pow 3 - &3 * x * (u / v) - &2 * y = &0` THEN
    CONV_TAC REAL_RING] THEN
  MATCH_MP_TAC ALGEBRAIC_INTEGER_RATIONAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC RATIONAL_DIV THEN ASM_SIMP_TAC[RATIONAL_INTEGER];
    ALL_TAC] THEN
  REWRITE_TAC[algebraic_integer] THEN
  MAP_EVERY EXISTS_TAC
   [`3`; `\i. if i = 0 then --(&2 * y) else if i = 1 then --(&3 * x)
              else if i = 2 then &0 else &1:real`] THEN
  REWRITE_TAC[THUE_VSUM_SMALL] THEN BETA_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  UNDISCH_TAC `((u:real) / v) pow 3 - &3 * x * (u / v) - &2 * y = &0` THEN
  REWRITE_TAC[GSYM CX_INJ; CX_SUB; CX_MUL; CX_POW; CX_NEG] THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* The irreducible case: reduction theory and THUE.                          *)
(* ------------------------------------------------------------------------- *)

let MORDELL_IRREDUCIBLE_FINITE = prove
 (`!k. integer k /\ ~(k = &0)
       ==> FINITE {(x,y) | integer x /\ integer y /\ y pow 2 = x pow 3 + k /\
                           !u v. integer u /\ integer v /\
                                 &1 * u pow 3 + &0 * u pow 2 * v +
                                 --(&3 * x) * u * v pow 2 +
                                 --(&2 * y) * v pow 3 = &0
                                 ==> u = &0 /\ v = &0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `--(&108 * k):real` CUBIC_FORM_REDUCTION) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real#real#real#real->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "red")))) THEN
  MATCH_MP_TAC(INST_TYPE [`:(real#real#real#real)#(real#real)`,`:B`]
    MORDELL_FINITE_REL) THEN
  EXISTS_TAC
   `\(x:real,y:real) ((a1:real,b1:real,c1:real,d1:real),(p:real,r:real)).
      ?q s. integer q /\ integer s /\ p * s - q * r = &1 /\
            !u v. &1 * u pow 3 + &0 * u pow 2 * v + --(&3 * x) * u * v pow 2 +
                  --(&2 * y) * v pow 3 =
                  a1 * (p * u + q * v) pow 3 +
                  b1 * (p * u + q * v) pow 2 * (r * u + s * v) +
                  c1 * (p * u + q * v) * (r * u + s * v) pow 2 +
                  d1 * (r * u + s * v) pow 3` THEN
  EXISTS_TAC
   `{(G,pr) | G IN Phi /\
              pr IN (\(a1:real,b1:real,c1:real,d1:real).
                       {(p:real,r:real) |
                          integer p /\ integer r /\
                          (!u v. integer u /\ integer v /\
                                 a1 * u pow 3 + b1 * u pow 2 * v +
                                 c1 * u * v pow 2 + d1 * v pow 3 = &0
                                 ==> u = &0 /\ v = &0) /\
                          a1 * p pow 3 + b1 * p pow 2 * r +
                          c1 * p * r pow 2 + d1 * r pow 3 = &1}) G}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a1:real`; `b1:real`; `c1:real`; `d1:real`] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC
     `!u v. integer u /\ integer v /\
            a1 * u pow 3 + b1 * u pow 2 * v + c1 * u * v pow 2 +
            d1 * v pow 3 = &0
            ==> u = &0 /\ v = &0` THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC MORDELL_THUE_CUBIC THEN ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{}:real#real->bool` THEN
      REWRITE_TAC[FINITE_EMPTY; SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
                  NOT_IN_EMPTY]];
    REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
    USE_THEN "red" (MP_TAC o SPECL
     [`&1:real`; `&0:real`; `--(&3 * x):real`; `--(&2 * y):real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC INTEGER_MUL THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
        MATCH_MP_TAC INTEGER_MUL THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
        UNDISCH_TAC `(y:real) pow 2 = x pow 3 + k` THEN CONV_TAC REAL_RING];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a1:real`; `b1:real`; `c1:real`; `d1:real`;
                         `p:real`; `q:real`; `r:real`; `s:real`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a1:real`; `b1:real`; `c1:real`; `d1:real`;
                          `p:real`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MORDELL_NZ_TRANSPORT THEN
      MAP_EVERY EXISTS_TAC [`&1:real`; `&0:real`; `--(&3 * x):real`;
                            `--(&2 * y):real`; `p:real`; `q:real`; `r:real`;
                            `s:real`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`&1:real`; `&0:real`] o
        check (is_forall o concl)) THEN
      CONV_TAC REAL_RING;
      MAP_EVERY EXISTS_TAC [`q:real`; `s:real`] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`x1:real`; `y1:real`; `x2:real`; `y2:real`;
                         `a1:real`; `b1:real`; `c1:real`; `d1:real`;
                         `p:real`; `r:real`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q2:real` (X_CHOOSE_THEN `s2:real`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q1:real` (X_CHOOSE_THEN `s1:real`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MORDELL_SHIFT THEN
    MAP_EVERY EXISTS_TAC [`a1:real`; `b1:real`; `c1:real`; `d1:real`;
                          `p:real`; `r:real`; `q1:real`; `s1:real`;
                          `q2:real`; `s2:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Mordell theorem.                                                      *)
(* ------------------------------------------------------------------------- *)

let MORDELL = prove
 (`!k. integer k /\ ~(k = &0)
       ==> FINITE {(x,y) | integer x /\ integer y /\ y pow 2 = x pow 3 + k}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{(x,y) | integer x /\ integer y /\ y pow 2 = x pow 3 + k /\
             ?t. integer t /\ &2 * y = t pow 3 - &3 * x * t} UNION
    {(x,y) | integer x /\ integer y /\ y pow 2 = x pow 3 + k /\
             !u v. integer u /\ integer v /\
                   &1 * u pow 3 + &0 * u pow 2 * v +
                   --(&3 * x) * u * v pow 2 +
                   --(&2 * y) * v pow 3 = &0
                   ==> u = &0 /\ v = &0}` THEN
  ASM_SIMP_TAC[FINITE_UNION; MORDELL_REDUCIBLE_FINITE;
               MORDELL_IRREDUCIBLE_FINITE] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_UNION] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~b ==> a) ==> a \/ b`) THEN DISCH_TAC THEN
  MATCH_MP_TAC MORDELL_CASE_SPLIT THEN ASM_REWRITE_TAC[]);;
