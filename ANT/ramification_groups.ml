(* ========================================================================= *)
(* Higher ramification groups (Serre, Local Fields IV 1-2) at a prime Q of a *)
(* ring b in a finite Galois extension (k,l) h, b a subring of l stable      *)
(* under G = galois_group(k,l) h as in ANT/decomposition.ml. No new          *)
(* constant: the lower numbering group G_i (i >= 0) is the inertia group of  *)
(* the ideal Q^(i+1),                                                        *)
(*                                                                           *)
(*   inertia_group (k,l) h b (ideal_pow b Q (i + 1))                         *)
(*     = the f in D_Q with f(x) == x (mod Q^(i+1)) for all x in b            *)
(*                                                                           *)
(* (INERTIA_GROUP_IDEAL_POW; for Q prime the decomposition group of Q^(i+1)  *)
(* is D_Q, DECOMPOSITION_GROUP_IDEAL_POW), so G_0 = I_Q                      *)
(* (INERTIA_GROUP_IDEAL_POW_0). The G_i decrease                             *)
(* (INERTIA_GROUP_IDEAL_POW_MONO), are normal in D_Q                         *)
(* (INERTIA_GROUP_IDEAL_POW_NORMAL), consist of automorphisms of b fixing    *)
(* every Q^j (INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) and, for b a Dedekind    *)
(* domain with fraction field l, field_of_fractions (b,l) I, and Q nonzero,  *)
(* are trivial for large i (INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL).     *)
(*                                                                           *)
(* For b Dedekind, Q nonzero with b / Q finite of characteristic p =         *)
(* ring_char(quotient_ring b Q), and t a uniformizer, t IN Q DIFF Q^2        *)
(* (DEDEKIND_PRIME_IDEAL_UNIFORMIZER):                                       *)
(*                                                                           *)
(*   f IN G_0 is in G_n iff f(t) == t (mod Q^(n+1))                          *)
(*                            (INERTIA_GROUP_IDEAL_POW_UNIFORMIZER)          *)
(*   f IN G_i has f(t) == (1 + a) t (mod Q^(i+2)) for some a IN Q^i          *)
(*                            (INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS)   *)
(*   if x == c t (mod Q^(n+1)), then x == d t (mod Q^(n+1)) iff              *)
(*   c == d (mod Q^n)         (DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE)        *)
(*   for f, g IN G_i with f(t) == c t and g(t) == d t (mod Q^(i+2)),         *)
(*   (f o g)(t) == c d t (mod Q^(i+2))                                       *)
(*                            (INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL)      *)
(*   for i >= 1 and a, c IN Q^i, f(t) == (1 + a) t and g(t) == (1 + c) t     *)
(*   (mod Q^(i+2)) give (f o g)(t) == (1 + a + c) t (mod Q^(i+2))            *)
(*                            (INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD)      *)
(*   for f IN G_i with f(t) == c t (mod Q^(i+2)), f IN G_(i+1) iff           *)
(*   c == 1 (mod Q^(i+1))     (INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL)   *)
(*   f |-> f(t)/t mod Q, the coset of c with f(t) == c t (mod Q^2), is a     *)
(*   homomorphism G_0 -> unit_group(b / Q) with kernel G_1                   *)
(*                            (INERTIA_GROUP_TAME_HOMOMORPHISM)              *)
(*   G_0 / G_1 is cyclic of order dividing |b / Q| - 1, prime to p           *)
(*                            (INERTIA_GROUP_TAME_QUOTIENT)                  *)
(*   for i >= 1, f |-> f(t)/t - 1, the class in Q^i / Q^(i+1) of a with      *)
(*   f(t) == (1 + a) t (mod Q^(i+2)), is a homomorphism from G_i to the      *)
(*   additive group of b / Q^(i+1) with kernel G_(i+1)                       *)
(*                            (INERTIA_GROUP_WILD_HOMOMORPHISM)              *)
(*   for i >= 1, f IN G_i ==> f^p IN G_(i+1)                                 *)
(*                            (INERTIA_GROUP_IDEAL_POW_CHAR_POW)             *)
(*   G_1 is a p-group         (INERTIA_GROUP_WILD_PGROUP)                    *)
(*   G_1 lies in a subgroup c of G_0 iff the index of c is prime to p        *)
(*                            (INERTIA_GROUP_WILD_SUBSET)                    *)
(*   G_1 = {1} iff p does not divide |I_Q|                                   *)
(*                            (INERTIA_GROUP_WILD_TRIVIAL)                   *)
(*                                                                           *)
(* and for a Galois extension of number fields (galois_extension(k,l) h and  *)
(* number_field l) G_1 = {1} iff p does not divide e(Q|p)                    *)
(* (NUMBER_FIELD_WILD_INERTIA_TRIVIAL). The wild map takes values in the     *)
(* cosets of elements of Q^i, the subgroup Q^i / Q^(i+1) of                  *)
(* ring_additive_group(quotient_ring b (ideal_pow b Q (i + 1)))              *)
(* (Library/ring_groups.ml); INERTIA_GROUP_WILD_MAP states it by its values, *)
(* additivity, defining congruence and kernel.                               *)
(*                                                                           *)
(* Routes, without localization: the key lemma                               *)
(* DEDEKIND_UNIFORMIZER_CONGRUENCE is for a ring endomorphism f of b with f  *)
(* == id (mod Q) and d = f - id: if d(b) SUBSET Q^n, n >= 1, and d(t) IN     *)
(* Q^(n+1), then d(b) SUBSET Q^(n+1) (DEDEKIND_UNIFORMIZER_CONGRUENCE_STEP). *)
(* By d(xy) = d(x) f(y) + x d(y) and an s NOTIN Q with s Q SUBSET (t)        *)
(* (DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR of ANT/dedekind.ml, from (t) = Q    *)
(* J), d(Q) SUBSET Q^(n+1); for x NOTIN Q, x^q == x (mod Q) with q = |b / Q| *)
(* IN Q (MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD of ANT/ideal_euler.ml), and  *)
(* x d(x^q) == q x^q d(x) (mod Q^(n+1)) as d(x)^2 IN Q^(n+1)                 *)
(* (RING_HOMOMORPHISM_POW_DIFFERENCE), so x d(x^q) and d(x^q) are in         *)
(* Q^(n+1). Membership in Q^n is decided by the Q-adic valuation             *)
(* (DEDEKIND_IDEAL_POW_MUL_CANCEL of ANT/dedekind.ml), and Q^(n+1) = t Q^n + *)
(* Q^(n+2) elementwise (DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT of              *)
(* ANT/dedekind.ml). The tame and the wild maps send f to the class of the   *)
(* coefficient c with f(t) == c t (mod Q^(i+2)), for i = 0 and for i >= 1    *)
(* with c = 1 + a: for f IN G_i, f(t) - t IN Q^(i+1) = t Q^i + Q^(i+2); the  *)
(* coefficient is unique modulo Q^(i+1) as t x IN Q^(n+1) iff x IN Q^n       *)
(* (DEDEKIND_IDEAL_POW_UNIFORMIZER_MUL); for g(t) = d t + w, (f o g)(t) =    *)
(* f(d) f(t) + f(w) == c d t as f(d) == d (mod Q^(i+1)) and f(t) IN Q; and   *)
(* (1 + a)(1 + c) == 1 + a + c (mod Q^(i+1)) for a, c IN Q^i, i >= 1         *)
(* (INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD). G_0 / G_1 is the image of      *)
(* the tame map, a subgroup of the cyclic unit group of the finite field     *)
(* b / Q (FINITE_FIELD_CYCLIC_UNIT_GROUP); the wild map gives theta(f^p) =   *)
(* p theta(f) = 0, and f^(p^m) IN G_(m+1) with the G_i eventually trivial    *)
(* makes the orders in G_1 powers of p. Then |G_0| = |G_0 / G_1| |G_1|       *)
(* with the first factor prime to p, and |I_Q| = e for number fields         *)
(* (NUMBER_FIELD_DECOMPOSITION_GROUP); a normal p-subgroup lies in every     *)
(* subgroup of index prime to p (NORMAL_PGROUP_SUBSET_COPRIME_INDEX of       *)
(* Library/grouptheory.ml, by Sylow), which gives INERTIA_GROUP_WILD_SUBSET, *)
(* and its case c = {1} gives INERTIA_GROUP_WILD_TRIVIAL.                    *)
(*                                                                           *)
(* Not here: real-indexed groups, the Herbrand function and upper numbering. *)
(*                                                                           *)
(* Uses: ANT/relative_split.ml (NUMBER_FIELD_PRIME_IDEAL_ABOVE),             *)
(* ANT/nf_decomposition.ml (ANT/decomposition.ml and the number field        *)
(* instance), Library/grouptheory.ml (NORMAL_PGROUP_SUBSET_COPRIME_INDEX),   *)
(* Library/ring_groups.ml (unit_group, ring_additive_group),                 *)
(* ANT/dedekind.ml (ideal powers and uniformizers,                           *)
(* DEDEKIND_IN_IDEAL_POW_VALUATION), ANT/ideal_arith.ml (ideal_pow),         *)
(* ANT/ideal_euler.ml (MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD) and           *)
(* Library/finite_fields.ml (FINITE_FIELD_CYCLIC_UNIT_GROUP).                *)
(* ========================================================================= *)

needs "ANT/relative_split.ml";;
needs "ANT/nf_decomposition.ml";;
needs "Library/ring_groups.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/ideal_euler.ml";;
needs "Library/finite_fields.ml";;

(* ------------------------------------------------------------------------- *)
(* Endomorphisms congruent to the identity: the key congruence.              *)
(* ------------------------------------------------------------------------- *)

let RING_HOMOMORPHISM_POW_DIFFERENCE = prove
 (`!r k (f:A->A) x m.
        ring_homomorphism(r,r) f /\ ring_ideal r k /\ x IN ring_carrier r /\
        ring_mul r (ring_sub r (f x) x) (ring_sub r (f x) x) IN k
        ==> ring_sub r
             (ring_mul r x (ring_sub r (f(ring_pow r x m)) (ring_pow r x m)))
             (ring_mul r (ring_of_num r m)
               (ring_mul r (ring_pow r x m) (ring_sub r (f x) x))) IN k`,
  let lemma = prove
   (`!r k x a X Y M:A.
        ring_ideal r k /\ x IN ring_carrier r /\ a IN ring_carrier r /\
        X IN ring_carrier r /\ Y IN ring_carrier r /\ M IN ring_carrier r /\
        ring_sub r (ring_mul r x (ring_sub r Y X))
                   (ring_mul r M (ring_mul r X (ring_sub r a x))) IN k /\
        ring_mul r (ring_sub r a x) (ring_sub r a x) IN k
        ==> ring_sub r
             (ring_mul r x (ring_sub r (ring_mul r a Y) (ring_mul r x X)))
             (ring_mul r (ring_add r M (ring_1 r))
               (ring_mul r (ring_mul r x X) (ring_sub r a x))) IN k`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_sub r
       (ring_mul r x (ring_sub r (ring_mul r a Y) (ring_mul r x X)))
       (ring_mul r (ring_add r M (ring_1 r))
         (ring_mul r (ring_mul r x X) (ring_sub r a x))) =
      ring_add r
       (ring_mul r (ring_sub r (ring_mul r x (ring_sub r Y X))
                     (ring_mul r M (ring_mul r X (ring_sub r a x)))) a)
       (ring_mul r M (ring_mul r X
         (ring_mul r (ring_sub r a x) (ring_sub r a (x:A)))))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `!r x a X Y M:A.
          x IN ring_carrier r /\ a IN ring_carrier r /\
          X IN ring_carrier r /\ Y IN ring_carrier r /\ M IN ring_carrier r
          ==> ring_sub r
               (ring_mul r x (ring_sub r (ring_mul r a Y) (ring_mul r x X)))
               (ring_mul r (ring_add r M (ring_1 r))
                 (ring_mul r (ring_mul r x X) (ring_sub r a x))) =
              ring_add r
               (ring_mul r (ring_sub r (ring_mul r x (ring_sub r Y X))
                             (ring_mul r M (ring_mul r X (ring_sub r a x)))) a)
               (ring_mul r M (ring_mul r X
                 (ring_mul r (ring_sub r a x) (ring_sub r a x))))`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC[]]]) in
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    CONJUNCT1 o REWRITE_RULE[ring_homomorphism]) THEN
  SUBGOAL_THEN `(f:A->A) x IN ring_carrier r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ring_pow; RING_OF_NUM_0] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    ASM_SIMP_TAC[RING_SUB_REFL; RING_1; RING_MUL_RZERO; RING_MUL_LZERO;
                 RING_MUL; RING_SUB; RING_0; IN_RING_IDEAL_0];
    REWRITE_TAC[ring_pow; ring_of_num] THEN
    FIRST_ASSUM(fun th ->
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th; RING_POW]) THEN
    MATCH_MP_TAC lemma THEN ASM_SIMP_TAC[RING_POW; RING_OF_NUM]]);;

let DEDEKIND_UNIFORMIZER_CONGRUENCE_STEP = prove
 (`!r p (f:A->A) t n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r p)) /\
        ring_homomorphism(r,r) f /\
        t IN p /\ ~(t IN ideal_pow r p 2) /\ ~(n = 0) /\
        (!x. x IN ring_carrier r ==> ring_sub r (f x) x IN ideal_pow r p n) /\
        ring_sub r (f t) t IN ideal_pow r p (n + 1)
        ==> !x. x IN ring_carrier r
                ==> ring_sub r (f x) x IN ideal_pow r p (n + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `maximal_ideal r (p:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    CONJUNCT1 o REWRITE_RULE[ring_homomorphism]) THEN
  SUBGOAL_THEN `(p:A->bool) SUBSET ring_carrier r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ideal_pow r p n SUBSET (p:A->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `p:A->bool`; `1:num`; `n:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[IDEAL_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN p ==> (f:A->A) y IN p` ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:A->A) y = ring_add r (ring_sub r (f y) y) y`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_RULE `ring_add r (ring_sub r a b) b = a:A`];
      MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check
       (fun th -> concl th = `ideal_pow r p n SUBSET (p:A->bool)`)) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN p ==> ring_sub r ((f:A->A) y) y IN ideal_pow r p (n + 1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `p:A->bool`; `t:A`]
      DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:A` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_mul r ((f:A->A) s) (f y) = ring_mul r (f t) (f z)`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_MUL) THEN
      DISCH_THEN(fun th -> ASM_SIMP_TAC[GSYM th]);
      ALL_TAC] THEN
    MATCH_MP_TAC DEDEKIND_IDEAL_POW_MUL_CANCEL THEN
    MAP_EVERY EXISTS_TAC [`s:A`; `0:num`] THEN
    ASM_SIMP_TAC[RING_SUB; ADD_CLAUSES; IDEAL_POW_1] THEN
    SUBGOAL_THEN
     `ring_mul r s (ring_sub r ((f:A->A) y) y) =
      ring_sub r (ring_add r (ring_mul r (ring_sub r (f t) t) (f z))
                             (ring_mul r t (ring_sub r (f z) z)))
                 (ring_mul r (ring_sub r (f s) s) (f y))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `!r s y t z fs fy ft fz:A.
          s IN ring_carrier r /\ y IN ring_carrier r /\
          t IN ring_carrier r /\ z IN ring_carrier r /\
          fs IN ring_carrier r /\ fy IN ring_carrier r /\
          ft IN ring_carrier r /\ fz IN ring_carrier r /\
          ring_mul r s y = ring_mul r t z /\
          ring_mul r fs fy = ring_mul r ft fz
          ==> ring_mul r s (ring_sub r fy y) =
              ring_sub r (ring_add r (ring_mul r (ring_sub r ft t) fz)
                                     (ring_mul r t (ring_sub r fz z)))
                         (ring_mul r (ring_sub r fs s) fy)`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IN_RING_IDEAL_ADD THEN
      REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN
        ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW];
        ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN
        ASM_SIMP_TAC[IDEAL_POW_1]];
      MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC[IDEAL_POW_1]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:A) IN p` THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `q = CARD(ring_carrier(quotient_ring r (p:A->bool)))` THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A->bool`]
    MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:A->A) x IN ring_carrier r /\
                ring_pow r x q IN ring_carrier r /\
                f(ring_pow r x q) IN ring_carrier r`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_POW]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_pow r p (n + 1):A->bool`; `f:A->A`;
                 `x:A`; `q:num`] RING_HOMOMORPHISM_POW_DIFFERENCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC[IDEAL_POW_1] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check
     (fun th -> concl th = `ideal_pow r p n SUBSET (p:A->bool)`)) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!a b:A. a IN ring_carrier r /\ b IN ideal_pow r p (n + 1) /\
            ring_sub r a b IN ideal_pow r p (n + 1)
            ==> a IN ideal_pow r p (n + 1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(b:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IDEAL_POW; RING_IDEAL_IMP_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `a:A = ring_add r (ring_sub r a b) b` SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_RULE `ring_add r (ring_sub r a b) b = a:A`];
      ASM_SIMP_TAC[IN_RING_IDEAL_ADD; RING_IDEAL_IDEAL_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub r ((f:A->A)(ring_pow r x q)) (ring_pow r x q)
    IN ideal_pow r p (n + 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DEDEKIND_IDEAL_POW_MUL_CANCEL THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `0:num`] THEN
    ASM_SIMP_TAC[ADD_CLAUSES; IDEAL_POW_1; RING_SUB] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC
     `ring_mul r (ring_of_num r q)
        (ring_mul r (ring_pow r x q) (ring_sub r ((f:A->A) x) x))` THEN
    ASM_SIMP_TAC[RING_MUL; RING_SUB] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN
    ASM_SIMP_TAC[IDEAL_POW_1] THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub r ((f:A->A) x) x =
    ring_sub r (ring_sub r (f(ring_pow r x q)) (ring_pow r x q))
               (ring_sub r (f(ring_sub r (ring_pow r x q) x))
                           (ring_sub r (ring_pow r x q) x))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUB th]) THEN
    MATCH_MP_TAC(RING_RULE
     `!r a b c d:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\
        c IN ring_carrier r /\ d IN ring_carrier r
        ==> ring_sub r a b =
            ring_sub r (ring_sub r c d)
                       (ring_sub r (ring_sub r c a) (ring_sub r d b))`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW]]);;

let DEDEKIND_UNIFORMIZER_CONGRUENCE = prove
 (`!r p (f:A->A) t n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r p)) /\
        ring_homomorphism(r,r) f /\
        (!x. x IN ring_carrier r ==> ring_sub r (f x) x IN p) /\
        t IN p /\ ~(t IN ideal_pow r p 2)
        ==> ((!x. x IN ring_carrier r
                  ==> ring_sub r (f x) x IN ideal_pow r p (n + 1)) <=>
             ring_sub r (f t) t IN ideal_pow r p (n + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_RING_IDEAL; RING_IDEAL_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  EQ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [ASM_SIMP_TAC[ADD_CLAUSES; IDEAL_POW_1; PRIME_IMP_RING_IDEAL]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC DEDEKIND_UNIFORMIZER_CONGRUENCE_STEP THEN
  EXISTS_TAC `t:A` THEN ASM_REWRITE_TAC[NOT_SUC] THEN
  REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A->bool`; `n + 1:num`; `SUC n + 1`]
    IDEAL_POW_ANTIMONO) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_IDEAL_IMP_SUBSET;
               ARITH_RULE `n + 1 <= SUC n + 1`] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The lower numbering groups G_i = I(Q^(i+1)): decreasing, normal, trivial  *)
(* for large i, detected by a uniformizer.                                   *)
(* ------------------------------------------------------------------------- *)

let DECOMPOSITION_GROUP_IDEAL_POW = prove
 (`!(h:A->B) k l b Q i.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q
        ==> decomposition_group(k,l) h (ideal_pow b Q (i + 1)) =
            decomposition_group(k,l) h Q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[decomposition_group] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:B->B` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `f IN group_carrier(galois_group(k,l) (h:A->B))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `f:B->B`]
    GALOIS_GROUP_SUBRING_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL [`b:B ring`; `b:B ring`; `f:B->B`; `Q:B->bool`; `i + 1:num`]
    RING_ISOMORPHISM_IDEAL_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `f:B->B`;
                 `Q:B->bool`] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN
  ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN STRIP_TAC THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!J:B->bool. ring_ideal b J ==> ideal_pow b J (i + 1) SUBSET J`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`b:B ring`; `J:B->bool`; `1:num`; `i + 1:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`; `IMAGE (f:B->B) Q`; `i + 1:num`]
      IDEAL_POW_SUBSET_PRIME_IDEAL) THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; ADD_EQ_0; ARITH_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`b:B ring`; `IMAGE (f:B->B) Q`; `Q:B->bool`; `i + 1:num`]
      IDEAL_POW_SUBSET_PRIME_IDEAL) THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; ADD_EQ_0; ARITH_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `ideal_pow b (IMAGE (f:B->B) Q) (i + 1) = ideal_pow b Q (i + 1)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[]]);;

let INERTIA_GROUP_IDEAL_POW_0 = prove
 (`!(h:A->B) k l b Q.
        ring_ideal b Q
        ==> inertia_group(k,l) h b (ideal_pow b Q 1) =
            inertia_group(k,l) h b Q`,
  SIMP_TAC[IDEAL_POW_1]);;

let INERTIA_GROUP_IDEAL_POW = prove
 (`!(h:A->B) k l b Q i.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q
        ==> group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) =
            {f | f IN group_carrier(decomposition_group(k,l) h Q) /\
                 !x. x IN ring_carrier b
                     ==> ring_sub l (f x) x IN ideal_pow b Q (i + 1)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `i:num`] DECOMPOSITION_GROUP_IDEAL_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[INERTIA_GROUP; RING_IDEAL_IDEAL_POW; DECOMPOSITION_GROUP;
               IN_ELIM_THM] THEN
  SET_TAC[]);;

let INERTIA_GROUP_IDEAL_POW_MONO = prove
 (`!(h:A->B) k l b Q i j.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q /\ i <= j
        ==> group_carrier(inertia_group(k,l) h b (ideal_pow b Q (j + 1)))
            SUBSET
            group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INERTIA_GROUP_IDEAL_POW] THEN
  MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`; `i + 1:num`; `j + 1:num`]
    IDEAL_POW_ANTIMONO) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_IDEAL_IMP_SUBSET;
               LE_ADD_RCANCEL] THEN
  SET_TAC[]);;

let INERTIA_GROUP_IDEAL_POW_NORMAL = prove
 (`!(h:A->B) k l b Q i.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q
        ==> group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
            normal_subgroup_of decomposition_group(k,l) h Q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `i:num`] DECOMPOSITION_GROUP_IDEAL_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INERTIA_GROUP_NORMAL_SUBGROUP THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW]);;

let INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL = prove
 (`!(h:A->B) k l b Q.
        finite_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ field_of_fractions(b,l) I /\
        prime_ideal b Q /\ ~(Q = {ring_0 l})
        ==> ?N. !i. N <= i
                    ==> group_carrier
                         (inertia_group(k,l) h b (ideal_pow b Q (i + 1))) =
                        {I}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_0 b = ring_0 (l:B ring) /\ ring_sub b = ring_sub l /\
    ring_mul b = ring_mul l /\ ring_carrier b SUBSET ring_carrier l`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED;
                RING_CARRIER_SUBRING_GENERATED_SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[I_THM] o
    GEN_REWRITE_RULE I [field_of_fractions]) THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k,l) (h:A->B)) /\ ~(f = I)
        ==> ?x. x IN ring_carrier b /\ ~(f x = x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
      ASM_CASES_TAC `!x:B. x IN ring_carrier b ==> f x = x` THENL
       [ALL_TAC; ASM_MESON_TAC[]] THEN
      UNDISCH_TAC `~(f:B->B = I)` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      REWRITE_TAC[FUN_EQ_THM; I_THM] THEN X_GEN_TAC `z:B` THEN
      ASM_CASES_TAC `(z:B) IN ring_carrier l` THENL
       [ALL_TAC;
        FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[permutes] o
          MATCH_MP GALOIS_GROUP_PERMUTES) THEN
        ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:B` o check (fun th ->
        can (find_term ((=) `ring_mul (l:B ring)`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:B`; `s:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:B) IN ring_carrier l /\ (a:B) IN ring_carrier l`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:B->B) z IN ring_carrier l` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
      DISCH_THEN(fun th -> ASM_REWRITE_TAC[MATCH_MP PERMUTES_IN_IMAGE th]);
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`l:B ring`; `s:B`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
    DISCH_THEN(MP_TAC o SPECL [`s:B`; `z:B`] o
      MATCH_MP RING_HOMOMORPHISM_MUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[] THEN
  TRANS_TAC EQ_TRANS `(f:B->B)(ring_mul l s z)` THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
      DISCH_THEN(MP_TAC o SPECL [`s:B`; `z:B`] o
        MATCH_MP RING_HOMOMORPHISM_MUL) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier(galois_group(k,l) (h:A->B)) /\ ~(f = I)
        ==> ?m. ~(f IN group_carrier
                        (inertia_group(k,l) h b (ideal_pow b Q (m + 1))))`
  MP_TAC THENL
   [X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:B->B`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `ring_sub l ((f:B->B) x) x IN ring_carrier b /\
      ~(ring_sub l (f x) x = ring_0 b)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ring_sub b = ring_sub (l:B ring)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN `(f:B->B) x IN ring_carrier b` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[RING_SUB; RING_SUB_EQ_0];
      ALL_TAC] THEN
    EXISTS_TAC
     `ideal_valuation b Q (ideal_generated b {ring_sub l ((f:B->B) x) x})` THEN
    ASM_SIMP_TAC[INERTIA_GROUP_IDEAL_POW; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:B` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`; `ring_sub l ((f:B->B) x) x`;
                   `ideal_valuation b Q
                     (ideal_generated b {ring_sub l ((f:B->B) x) x}) + 1`]
      DEDEKIND_IN_IDEAL_POW_VALUATION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:(B->B)->num`) THEN
  MP_TAC(ISPEC
   `IMAGE (m:(B->B)->num) (group_carrier(galois_group(k,l) (h:A->B)))`
   num_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_GALOIS_GROUP; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:B->B` THEN
  REWRITE_TAC[IN_SING] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `f IN group_carrier(galois_group(k,l) (h:A->B))`
        ASSUME_TAC THENL
         [UNDISCH_TAC
           `f IN group_carrier(inertia_group(k,l) (h:A->B) b
                                (ideal_pow b Q (i + 1)))` THEN
          ASM_SIMP_TAC[INERTIA_GROUP_IDEAL_POW; DECOMPOSITION_GROUP;
                       IN_ELIM_THM];
          ALL_TAC] THEN
        ASM_CASES_TAC `f:B->B = I` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
       `group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))
        SUBSET
        group_carrier(inertia_group(k,l) h b (ideal_pow b Q (m(f:B->B) + 1)))`
      MP_TAC THENL
       [MATCH_MP_TAC INERTIA_GROUP_IDEAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        TRANS_TAC LE_TRANS `N:num` THEN ASM_SIMP_TAC[];
        ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPEC
       `inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))` GROUP_ID) THEN
      REWRITE_TAC[CONJUNCT1(CONJUNCT2 INERTIA_GROUP)]]);;

let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER = prove
 (`!(h:A->B) k l b Q t f n.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\
        t IN Q /\ ~(t IN ideal_pow b Q 2) /\
        f IN group_carrier(inertia_group(k,l) h b Q)
        ==> (f IN group_carrier
                    (inertia_group(k,l) h b (ideal_pow b Q (n + 1))) <=>
             ring_sub l (f t) t IN ideal_pow b Q (n + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_0 b = ring_0 (l:B ring) /\ ring_sub b = ring_sub l`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED];
    ALL_TAC] THEN
  UNDISCH_TAC `f IN group_carrier(inertia_group(k,l) (h:A->B) b Q)` THEN
  ASM_SIMP_TAC[INERTIA_GROUP; INERTIA_GROUP_IDEAL_POW; PRIME_IMP_RING_IDEAL;
               DECOMPOSITION_GROUP; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `f:B->B`]
    GALOIS_GROUP_SUBRING_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> concl th = `ring_sub b = ring_sub (l:B ring)`)) THEN
  MATCH_MP_TAC DEDEKIND_UNIFORMIZER_CONGRUENCE THEN
  ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* The action of G_i on a uniformizer t: f(t) == (1 + a) t (mod Q^(i+2))     *)
(* with a in Q^i; the coefficient of t is unique modulo Q^(i+1),             *)
(* multiplicative under composition, and congruent to 1 modulo Q^(i+1)       *)
(* exactly on G_(i+1). These give the tame and the wild maps below.          *)
(* ------------------------------------------------------------------------- *)

(* Multiplication by a uniformizer t shifts the p-adic filtration by one:    *)
(* t x is in p^(n+1) iff x is in p^n.                                        *)
let DEDEKIND_IDEAL_POW_UNIFORMIZER_MUL = prove
 (`!r p (t:A) x n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        t IN p /\ ~(t IN ideal_pow r p 2) /\ x IN ring_carrier r
        ==> (ring_mul r t x IN ideal_pow r p (n + 1) <=>
             x IN ideal_pow r p n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `(p:A->bool) SUBSET ring_carrier r /\ (t:A) IN ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC DEDEKIND_IDEAL_POW_MUL_CANCEL THEN
    MAP_EVERY EXISTS_TAC [`t:A`; `1:num`] THEN ASM_REWRITE_TAC[ARITH];
    MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC[IDEAL_POW_1]]);;

(* Independence of representatives: if x == c t (mod p^(n+1)) for a          *)
(* uniformizer t, then x == d t (mod p^(n+1)) iff c == d (mod p^n).          *)
let DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE = prove
 (`!r p (t:A) x c d n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        t IN p /\ ~(t IN ideal_pow r p 2) /\
        x IN ring_carrier r /\ c IN ring_carrier r /\ d IN ring_carrier r /\
        ring_sub r x (ring_mul r c t) IN ideal_pow r p (n + 1)
        ==> (ring_sub r x (ring_mul r d t) IN ideal_pow r p (n + 1) <=>
             ring_sub r c d IN ideal_pow r p n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_RING_IDEAL; RING_IDEAL_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub r x (ring_mul r d t) =
    ring_add r (ring_sub r x (ring_mul r c t))
               (ring_mul r t (ring_sub r c d)):A`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_RULE
     `ring_add r (ring_sub r x (ring_mul r c t))
                 (ring_mul r t (ring_sub r c d)) =
      ring_sub r x (ring_mul r d t):A`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_pow r p (n + 1):A->bool`;
                 `ring_sub r x (ring_mul r c t):A`;
                 `ring_mul r t (ring_sub r c d):A`] RING_IDEAL_ADD_IN_EQ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RING_MUL; RING_SUB]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC DEDEKIND_IDEAL_POW_UNIFORMIZER_MUL THEN
  ASM_SIMP_TAC[RING_SUB]);;

(* An element of G_i is an automorphism of b fixing every Q^j and acting     *)
(* trivially on b / Q^(i+1).                                                 *)
let INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM = prove
 (`!(h:A->B) k l b Q i f.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q /\
        f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
        ==> ring_isomorphism(b,b) f /\
            (!j x. x IN ideal_pow b Q j ==> f x IN ideal_pow b Q j) /\
            (!x. x IN ring_carrier b
                 ==> ring_sub l (f x) x IN ideal_pow b Q (i + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  UNDISCH_TAC
   `f IN group_carrier
          (inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))` THEN
  ASM_SIMP_TAC[INERTIA_GROUP_IDEAL_POW; DECOMPOSITION_GROUP; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `f:B->B`]
    GALOIS_GROUP_SUBRING_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `x:B`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`b:B ring`; `b:B ring`; `f:B->B`; `Q:B->bool`; `j:num`]
    RING_ISOMORPHISM_IDEAL_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* For f in G_i, f(t) == (1 + a) t (mod Q^(i+2)) with a in Q^i, as f(t) - t  *)
(* is in Q^(i+1) = t Q^i + Q^(i+2).                                          *)
let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS = prove
 (`!(h:A->B) k l b Q t i f.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        t IN Q /\ ~(t IN ideal_pow b Q 2) /\
        f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
        ==> ?a. a IN ideal_pow b Q i /\
                ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
                IN ideal_pow b Q (i + 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `i:num`; `f:B->B`] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
    ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
    ring_add l = ring_add b`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `!j. ideal_pow b Q j SUBSET ring_carrier (b:B ring)`
  ASSUME_TAC THENL
   [MESON_TAC[RING_IDEAL_IDEAL_POW; RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:B) IN ring_carrier b /\ (f:B->B) t IN ring_carrier b`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
      ONCE_REWRITE_TAC[GSYM(ISPECL [`b:B ring`; `Q:B->bool`] IDEAL_POW_0)] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`; `t:B`;
                 `ring_sub b ((f:B->B) t) t`; `i:num`]
    DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT) THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:B` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:B) IN ring_carrier b /\ (w:B) IN ring_carrier b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub b ((f:B->B) t) (ring_mul b (ring_add b (ring_1 b) a) t) = w`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(RING_RULE
   `!r F t a w:B.
      F IN ring_carrier r /\ t IN ring_carrier r /\ a IN ring_carrier r /\
      w IN ring_carrier r /\ ring_sub r F t = ring_add r (ring_mul r t a) w
      ==> ring_sub r F (ring_mul r (ring_add r (ring_1 r) a) t) = w`) THEN
  ASM_REWRITE_TAC[]);;

(* The homomorphism law: f(t) == c t and g(t) == d t (mod Q^(i+2)) for f, g  *)
(* in G_i give (f o g)(t) == c d t (mod Q^(i+2)).                            *)
let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL = prove
 (`!(h:A->B) k l b Q t i f g c d.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q /\ t IN Q /\
        f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
        g IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
        c IN ring_carrier b /\ d IN ring_carrier b /\
        ring_sub l (f t) (ring_mul l c t) IN ideal_pow b Q (i + 2) /\
        ring_sub l (g t) (ring_mul l d t) IN ideal_pow b Q (i + 2)
        ==> ring_sub l ((f o g) t) (ring_mul l (ring_mul l c d) t)
            IN ideal_pow b Q (i + 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `i:num`; `g:B->B`] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `i:num`; `f:B->B`] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (ASSUME_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM)
   STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
    ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
    ring_add l = ring_add b`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `!j. ideal_pow b Q j SUBSET ring_carrier (b:B ring)`
  ASSUME_TAC THENL
   [MESON_TAC[RING_IDEAL_IDEAL_POW; RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Q:B->bool) SUBSET ring_carrier b /\ (t:B) IN ideal_pow b Q 1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; IDEAL_POW_1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ring_carrier b
        ==> (f:B->B) x IN ring_carrier b /\ (g:B->B) x IN ring_carrier b`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM(ISPECL [`b:B ring`; `Q:B->bool`] IDEAL_POW_0)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:B) IN ring_carrier b` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w = ring_sub b ((g:B->B) t) (ring_mul b d t)` THEN
  SUBGOAL_THEN `(w:B) IN ring_carrier b` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ASM_SIMP_TAC[RING_SUB; RING_MUL]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(g:B->B) t = ring_add b (ring_mul b d t) w` SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN
    ASM_SIMP_TAC[RING_MUL; RING_RULE `ring_add r a (ring_sub r x a) = x:B`];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_ADD th;
                 MATCH_MP RING_HOMOMORPHISM_MUL th; RING_MUL]) THEN
  SUBGOAL_THEN
   `ring_sub b
     (ring_add b (ring_mul b ((f:B->B) d) (f t)) (f w))
     (ring_mul b (ring_mul b c d) t) =
    ring_add b
     (ring_add b (ring_mul b (ring_sub b (f d) d) (f t))
                 (ring_mul b d (ring_sub b (f t) (ring_mul b c t))))
     (f w)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `!r A F W c d t:B.
        A IN ring_carrier r /\ F IN ring_carrier r /\ W IN ring_carrier r /\
        c IN ring_carrier r /\ d IN ring_carrier r /\ t IN ring_carrier r
        ==> ring_sub r (ring_add r (ring_mul r A F) W)
                       (ring_mul r (ring_mul r c d) t) =
            ring_add r
             (ring_add r (ring_mul r (ring_sub r A d) F)
                         (ring_mul r d (ring_sub r F (ring_mul r c t))))
             W`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `i + 2 = (i + 1) + 1` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW]]);;

(* For i >= 1 the coefficients 1 + a add: f(t) == (1 + a) t and              *)
(* g(t) == (1 + c) t (mod Q^(i+2)) with a, c in Q^i give                     *)
(* (f o g)(t) == (1 + (a + c)) t (mod Q^(i+2)), as a c t is in               *)
(* Q^(2 i + 1).                                                              *)
let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD = prove
 (`!(h:A->B) k l b Q t i f g a c.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q /\ t IN Q /\ 1 <= i /\
        f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
        g IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
        a IN ideal_pow b Q i /\ c IN ideal_pow b Q i /\
        ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
        IN ideal_pow b Q (i + 2) /\
        ring_sub l (g t) (ring_mul l (ring_add l (ring_1 l) c) t)
        IN ideal_pow b Q (i + 2)
        ==> ring_sub l ((f o g) t)
             (ring_mul l (ring_add l (ring_1 l) (ring_add l a c)) t)
            IN ideal_pow b Q (i + 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun v ->
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                   `i:num`; v] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `0:num` o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[IDEAL_POW_0] THEN DISCH_TAC)
   [`f:B->B`; `g:B->B`] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `t:B`; `i:num`; `f:B->B`; `g:B->B`;
                 `ring_add l (ring_1 l) (a:B)`; `ring_add l (ring_1 l) (c:B)`]
    INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL) THEN
  SUBGOAL_THEN
   `ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
    ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
    ring_add l = ring_add b`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `!j. ideal_pow b Q j SUBSET ring_carrier (b:B ring)`
  ASSUME_TAC THENL
   [MESON_TAC[RING_IDEAL_IDEAL_POW; RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(t:B) IN ring_carrier b /\ (a:B) IN ring_carrier b /\
    (c:B) IN ring_carrier b`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1:num` th) THEN
                            MP_TAC(SPEC `i:num` th)) THEN
    ASM_SIMP_TAC[IDEAL_POW_1; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `((f:B->B) o (g:B->B)) t IN ring_carrier b` ASSUME_TAC THENL
   [REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_ADD; RING_1]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `ring_sub b (((f:B->B) o (g:B->B)) t)
     (ring_mul b (ring_add b (ring_1 b) (ring_add b a c)) t) =
    ring_add b
     (ring_sub b ((f o g) t)
       (ring_mul b (ring_mul b (ring_add b (ring_1 b) a)
                               (ring_add b (ring_1 b) c)) t))
     (ring_mul b (ring_mul b a c) t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `!r x a c t:B.
        x IN ring_carrier r /\ a IN ring_carrier r /\
        c IN ring_carrier r /\ t IN ring_carrier r
        ==> ring_sub r x
             (ring_mul r (ring_add r (ring_1 r) (ring_add r a c)) t) =
            ring_add r
             (ring_sub r x
               (ring_mul r (ring_mul r (ring_add r (ring_1 r) a)
                                       (ring_add r (ring_1 r) c)) t))
             (ring_mul r (ring_mul r a c) t)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
  SUBGOAL_THEN
   `ideal_pow b Q ((i + i) + 1) SUBSET ideal_pow b (Q:B->bool) (i + 2)`
  MP_TAC THENL
   [MATCH_MP_TAC IDEAL_POW_ANTIMONO THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC] THEN
  MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN
  ASM_SIMP_TAC[IDEAL_POW_1; RING_MUL_IN_IDEAL_POW; RING_IDEAL_IMP_SUBSET]);;

(* The kernel: if f(t) == c t (mod Q^(i+2)) for f in G_i, then f is in       *)
(* G_(i+1) iff c == 1 (mod Q^(i+1)).                                         *)
let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL = prove
 (`!(h:A->B) k l b Q t i f c.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\
        t IN Q /\ ~(t IN ideal_pow b Q 2) /\
        f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
        c IN ring_carrier b /\
        ring_sub l (f t) (ring_mul l c t) IN ideal_pow b Q (i + 2)
        ==> (f IN group_carrier
                   (inertia_group(k,l) h b (ideal_pow b Q (i + 2))) <=>
             ring_sub l c (ring_1 l) IN ideal_pow b Q (i + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `t:B`; `f:B->B`; `i + 1:num`]
    INERTIA_GROUP_IDEAL_POW_UNIFORMIZER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`;
                   `Q:B->bool`; `0:num`; `i:num`]
      INERTIA_GROUP_IDEAL_POW_MONO) THEN
    ASM_SIMP_TAC[LE_0; ADD_CLAUSES; INERTIA_GROUP_IDEAL_POW_0] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ARITH_RULE `(i + 1) + 1 = i + 2`] THEN
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `i:num`; `f:B->B`] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN
   `ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
    ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
    ring_add l = ring_add b`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:B) IN ring_carrier b /\ (f:B->B) t IN ring_carrier b`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
      ONCE_REWRITE_TAC[GSYM(ISPECL [`b:B ring`; `Q:B->bool`] IDEAL_POW_0)] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`; `t:B`; `(f:B->B) t`; `c:B`;
                 `ring_1 b:B`; `i + 1:num`]
    DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE) THEN
  ASM_SIMP_TAC[RING_1; RING_MUL_LID; ARITH_RULE `(i + 1) + 1 = i + 2`]);;

(* ------------------------------------------------------------------------- *)
(* The tame quotient G_0 / G_1 in the units of b / Q.                        *)
(* ------------------------------------------------------------------------- *)

let INERTIA_GROUP_TAME_HOMOMORPHISM = prove
 (`!(h:A->B) k l b Q t.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\
        t IN Q /\ ~(t IN ideal_pow b Q 2)
        ==> ?theta.
              group_homomorphism
               (inertia_group(k,l) h b Q,unit_group(quotient_ring b Q))
               theta /\
              (!f c. f IN group_carrier(inertia_group(k,l) h b Q) /\
                     c IN ring_carrier b /\
                     ring_sub l (f t) (ring_mul l c t) IN ideal_pow b Q 2
                     ==> theta f = ring_coset b Q c) /\
              group_kernel(inertia_group(k,l) h b Q,
                           unit_group(quotient_ring b Q)) theta =
              group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN
   `inertia_group(k,l) (h:A->B) b (ideal_pow b Q (0 + 1)) =
    inertia_group(k,l) h b Q /\
    ideal_pow b Q (0 + 1) = Q /\ 0 + 2 = 2 /\
    ideal_pow b (Q:B->bool) 0 = ring_carrier b`
  (LABEL_TAC "i0") THENL
   [ASM_SIMP_TAC[ADD_CLAUSES; IDEAL_POW_1; IDEAL_POW_0;
                 INERTIA_GROUP_IDEAL_POW_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
    ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
    ring_add l = ring_add b`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
             LABEL_TAC "lb" th) THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:B) IN ring_carrier b` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!f x. f IN group_carrier(inertia_group(k,l) (h:A->B) b Q) /\
          x IN ring_carrier b
          ==> f x IN ring_carrier b`
  ASSUME_TAC THENL
   [REWRITE_TAC[inertia_group] THEN
    ASM_MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET;
                  FUN_IN_IMAGE];
    ALL_TAC] THEN
  (* the coefficients c_f with f(t) == c_f t (mod Q^2) *)
  SUBGOAL_THEN
   `!f. f IN group_carrier(inertia_group(k,l) (h:A->B) b Q)
        ==> ?c. c IN ring_carrier b /\
                ring_sub b (f t) (ring_mul b c t) IN ideal_pow b Q 2`
  MP_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                   `t:B`; `0:num`; `f:B->B`]
      INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS) THEN
    REMOVE_THEN "lb" (fun th -> REWRITE_TAC[th] THEN LABEL_TAC "lb" th) THEN
    USE_THEN "i0" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ring_add b (ring_1 b) a:B` THEN
    ASM_SIMP_TAC[RING_ADD; RING_1];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(B->B)->B` (LABEL_TAC "C") o
    REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  (* the coset of c_f depends only on f *)
  SUBGOAL_THEN
   `!f c. f IN group_carrier(inertia_group(k,l) (h:A->B) b Q) /\
          c IN ring_carrier b /\
          ring_sub b (f t) (ring_mul b c t) IN ideal_pow b Q 2
          ==> ring_coset b Q ((C:(B->B)->B) f) = ring_coset b Q c`
  (LABEL_TAC "uniq") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "C" (MP_TAC o SPEC `f:B->B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_SIMP_TAC[RING_COSET_EQ] THEN
    MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`; `t:B`; `(f:B->B) t`;
                   `(C:(B->B)->B) f`; `c:B`; `1:num`]
      DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE) THEN
    ASM_SIMP_TAC[ARITH; IDEAL_POW_1];
    ALL_TAC] THEN
  (* the multiplicative law *)
  SUBGOAL_THEN
   `!f g. f IN group_carrier(inertia_group(k,l) (h:A->B) b Q) /\
          g IN group_carrier(inertia_group(k,l) h b Q)
          ==> ring_coset b Q ((C:(B->B)->B) (f o g)) =
              ring_mul (quotient_ring b Q)
               (ring_coset b Q (C f)) (ring_coset b Q (C g))`
  (LABEL_TAC "mul") THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY (fun v -> USE_THEN "C" (MP_TAC o SPEC v) THEN
                        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
     [`f:B->B`; `g:B->B`] THEN
    ASM_SIMP_TAC[QUOTIENT_RING_MUL] THEN
    USE_THEN "uniq" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_MUL] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `inertia_group(k,l) (h:A->B) b Q` GROUP_MUL) THEN
      ASM_SIMP_TAC[CONJUNCT2 INERTIA_GROUP];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                   `t:B`; `0:num`; `f:B->B`; `g:B->B`;
                   `(C:(B->B)->B) f`; `(C:(B->B)->B) g`]
      INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL) THEN
    USE_THEN "lb" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "i0" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(I:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b Q)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `inertia_group(k,l) (h:A->B) b Q` GROUP_ID) THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 INERTIA_GROUP)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_coset b Q ((C:(B->B)->B) I) = ring_coset b Q (ring_1 b)`
  ASSUME_TAC THENL
   [USE_THEN "uniq" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[I_THM; RING_MUL_LID; RING_SUB_REFL; IN_RING_IDEAL_0;
                 RING_IDEAL_IDEAL_POW; RING_1];
    ALL_TAC] THEN
  EXISTS_TAC `\f:B->B. ring_coset b Q ((C:(B->B)->B) f)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[CONJUNCT2 INERTIA_GROUP; UNIT_GROUP; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `inverse(f:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b Q)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`inertia_group(k,l) (h:A->B) b Q`; `f:B->B`]
        GROUP_INV) THEN
      ASM_REWRITE_TAC[CONJUNCT2 INERTIA_GROUP];
      ALL_TAC] THEN
    REWRITE_TAC[ring_unit] THEN
    ASM_SIMP_TAC[CONJUNCT1 QUOTIENT_RING; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `ring_coset b Q ((C:(B->B)->B) (inverse f))` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "mul" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
     (CONJ (ASSUME
       `(f:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b Q)`)
      (ASSUME
       `inverse(f:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b Q)`)))])
    THEN
    MP_TAC(ISPECL [`inertia_group(k,l) (h:A->B) b Q`; `f:B->B`]
      GROUP_MUL_RINV) THEN
    ASM_REWRITE_TAC[CONJUNCT2 INERTIA_GROUP] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[QUOTIENT_RING_1];
    ALL_TAC] THEN
  REWRITE_TAC[group_kernel; UNIT_GROUP] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:B->B` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[QUOTIENT_RING_1] THEN
  ASM_CASES_TAC `f IN group_carrier(inertia_group(k,l) (h:A->B) b Q)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`;
                   `Q:B->bool`; `0:num`; `1:num`]
      INERTIA_GROUP_IDEAL_POW_MONO) THEN
    USE_THEN "i0" (fun th -> REWRITE_TAC[th; ARITH]) THEN
    ASM_REWRITE_TAC[ARITH] THEN ASM SET_TAC[]] THEN
  USE_THEN "C" (MP_TAC o SPEC `f:B->B`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_SIMP_TAC[RING_COSET_EQ; RING_1] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `t:B`; `0:num`; `f:B->B`; `(C:(B->B)->B) f`]
    INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL) THEN
  USE_THEN "lb" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "i0" (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[]);;

let INERTIA_GROUP_TAME_QUOTIENT = prove
 (`!(h:A->B) k l b Q.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q))
        ==> cyclic_group
             (quotient_group (inertia_group(k,l) h b Q)
               (group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2)))) /\
            CARD(group_carrier
             (quotient_group (inertia_group(k,l) h b Q)
               (group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2)))))
            divides CARD(ring_carrier(quotient_ring b Q)) - 1 /\
            coprime(CARD(group_carrier
                     (quotient_group (inertia_group(k,l) h b Q)
                       (group_carrier
                         (inertia_group(k,l) h b (ideal_pow b Q 2))))),
                    ring_char(quotient_ring b Q))`,
  let lemma = prove
   (`!d:num q:num p:num.
          d divides q - 1 /\ p divides q /\ ~(q = 0) ==> coprime(d,p)`,
    GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1; ADD1] THEN
    NUMBER_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_0 b = ring_0 (l:B ring)` ASSUME_TAC THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`]
    DEDEKIND_PRIME_IDEAL_UNIFORMIZER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `t:B`] INERTIA_GROUP_TAME_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `theta:(B->B)->(B->bool)` (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIRST_GROUP_ISOMORPHISM_THEOREM) THEN
  SUBGOAL_THEN `field(quotient_ring b (Q:B->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_QUOTIENT_RING; PRIME_IMP_RING_IDEAL] THEN
    MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(group_carrier(unit_group(quotient_ring b (Q:B->bool))))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_UNIT_GROUP; FINITE_DIFF]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBGROUP_GROUP_IMAGE) THEN
  SUBGOAL_THEN
   `CARD(group_carrier(quotient_group (inertia_group(k,l) (h:A->B) b Q)
      (group_kernel(inertia_group(k,l) h b Q,unit_group(quotient_ring b Q))
                   theta))) =
    CARD(group_image(inertia_group(k,l) h b Q,unit_group(quotient_ring b Q))
                    theta)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_EQ_CARD_IMP THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `group_carrier(unit_group(quotient_ring b (Q:B->bool)))` THEN
      ASM_MESON_TAC[subgroup_of];
      FIRST_ASSUM(MP_TAC o MATCH_MP ISOMORPHIC_GROUP_CARD_EQ) THEN
      ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(group_carrier(unit_group(quotient_ring b (Q:B->bool)))) =
    CARD(ring_carrier(quotient_ring b Q)) - 1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_UNIT_GROUP; SET_RULE `(s:A->bool) DIFF {a} = s DELETE a`;
                 CARD_DELETE; RING_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(group_image(inertia_group(k,l) (h:A->B) b Q,
                     unit_group(quotient_ring b Q)) theta) divides
    CARD(ring_carrier(quotient_ring b Q)) - 1`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC LAGRANGE_THEOREM THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP ISOMORPHIC_GROUP_CYCLICITY th]) THEN
    MATCH_MP_TAC SUBGROUP_OF_CYCLIC_GROUP THEN
    ASM_SIMP_TAC[FINITE_FIELD_CYCLIC_UNIT_GROUP];
    MATCH_MP_TAC lemma THEN
    EXISTS_TAC `CARD(ring_carrier(quotient_ring b (Q:B->bool)))` THEN
    ASM_SIMP_TAC[RING_CHAR_DIVIDES_ORDER; CARD_EQ_0; RING_CARRIER_NONEMPTY]]);;

(* ------------------------------------------------------------------------- *)
(* The wild part: G_i / G_(i+1) in Q^i / Q^(i+1), G_1 a p-group.             *)
(* ------------------------------------------------------------------------- *)

let INERTIA_GROUP_WILD_MAP = prove
 (`!(h:A->B) k l b Q t i.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\
        t IN Q /\ ~(t IN ideal_pow b Q 2) /\ 1 <= i
        ==> ?theta.
              (!f. f IN group_carrier
                         (inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
                   ==> ?a. a IN ideal_pow b Q i /\
                           theta f = ring_coset b (ideal_pow b Q (i + 1)) a) /\
              (!f g. f IN group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
                     g IN group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
                     ==> theta(f o g) =
                         ring_add (quotient_ring b (ideal_pow b Q (i + 1)))
                                  (theta f) (theta g)) /\
              (!f a. f IN group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
                     a IN ideal_pow b Q i /\
                     ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
                     IN ideal_pow b Q (i + 2)
                     ==> theta f = ring_coset b (ideal_pow b Q (i + 1)) a) /\
              (!f. f IN group_carrier
                         (inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
                   ==> (theta f =
                        ring_0 (quotient_ring b (ideal_pow b Q (i + 1))) <=>
                        f IN group_carrier
                         (inertia_group(k,l) h b (ideal_pow b Q (i + 2)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the coefficients a_f with f(t) == (1 + a_f) t (mod Q^(i+2)) *)
  SUBGOAL_THEN
   `!f. f IN group_carrier
              (inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))
        ==> ?a. a IN ideal_pow b Q i /\
                ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
                IN ideal_pow b Q (i + 2)`
  MP_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                   `t:B`; `i:num`; `f:B->B`]
      INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(B->B)->B` (LABEL_TAC "C") o
    REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  SUBGOAL_THEN
   `ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
    ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
    ring_add l = ring_add b`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
             LABEL_TAC "lb" th) THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `!j. ideal_pow b Q j SUBSET ring_carrier (b:B ring)`
  ASSUME_TAC THENL
   [MESON_TAC[RING_IDEAL_IDEAL_POW; RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:B) IN ring_carrier b` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier
              (inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))
        ==> (C:(B->B)->B) f IN ring_carrier b /\ f t IN ring_carrier b`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    USE_THEN "C" (MP_TAC o SPEC `f:B->B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                   `i:num`; `f:B->B`] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`0:num`; `t:B`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IDEAL_POW_0];
    ALL_TAC] THEN
  (* a_f is unique modulo Q^(i+1) *)
  SUBGOAL_THEN
   `!f a. f IN group_carrier
                (inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))) /\
          a IN ring_carrier b /\
          ring_sub b (f t) (ring_mul b (ring_add b (ring_1 b) a) t)
          IN ideal_pow b Q (i + 2)
          ==> ring_sub b ((C:(B->B)->B) f) a IN ideal_pow b Q (i + 1)`
  (LABEL_TAC "uniq") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "C" (MP_TAC o SPEC `f:B->B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`; `t:B`; `(f:B->B) t`;
                   `ring_add b (ring_1 b) ((C:(B->B)->B) f)`;
                   `ring_add b (ring_1 b) (a:B)`; `i + 1:num`]
      DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE) THEN
    ASM_SIMP_TAC[RING_ADD; RING_1; ARITH_RULE `(i + 1) + 1 = i + 2`] THEN
    ASM_SIMP_TAC[RING_RULE
     `ring_sub r (ring_add r (ring_1 r) c) (ring_add r (ring_1 r) a) =
      ring_sub r c a:B`];
    ALL_TAC] THEN
  EXISTS_TAC
   `\f:B->B. ring_coset b (ideal_pow b Q (i + 1)) ((C:(B->B)->B) f)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the values *)
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    EXISTS_TAC `(C:(B->B)->B) f` THEN
    USE_THEN "C" (MP_TAC o SPEC `f:B->B`) THEN ASM_SIMP_TAC[];
    (* additivity *)
    MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
    MAP_EVERY (fun v -> USE_THEN "C" (MP_TAC o SPEC v) THEN
                        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
     [`f:B->B`; `g:B->B`] THEN
    SUBGOAL_THEN
     `(f:B->B) o g IN
      group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))`
        GROUP_MUL) THEN
      ASM_SIMP_TAC[CONJUNCT2 INERTIA_GROUP];
      ALL_TAC] THEN
    ASM_SIMP_TAC[QUOTIENT_RING_ADD; RING_IDEAL_IDEAL_POW; RING_COSET_EQ;
                 RING_ADD] THEN
    USE_THEN "uniq" MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_ADD] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                   `t:B`; `i:num`; `f:B->B`; `g:B->B`;
                   `(C:(B->B)->B) f`; `(C:(B->B)->B) g`]
      INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD) THEN
    USE_THEN "lb" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
    (* the defining congruence *)
    MAP_EVERY X_GEN_TAC [`f:B->B`; `a:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:B) IN ring_carrier b` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_COSET_EQ; RING_IDEAL_IDEAL_POW] THEN
    USE_THEN "uniq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* the kernel *)
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    USE_THEN "C" (MP_TAC o SPEC `f:B->B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_SIMP_TAC[QUOTIENT_RING_0; RING_IDEAL_IDEAL_POW;
                 RING_COSET_EQ_IDEAL] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                   `t:B`; `i:num`; `f:B->B`;
                   `ring_add b (ring_1 b) ((C:(B->B)->B) f)`]
      INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL) THEN
    USE_THEN "lb" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_ADD; RING_1]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[RING_RULE
     `ring_sub r (ring_add r (ring_1 r) x) (ring_1 r) = x:B`]]);;

let INERTIA_GROUP_WILD_HOMOMORPHISM = prove
 (`!(h:A->B) k l b Q t i.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\
        t IN Q /\ ~(t IN ideal_pow b Q 2) /\ 1 <= i
        ==> ?theta.
              group_homomorphism
               (inertia_group(k,l) h b (ideal_pow b Q (i + 1)),
                ring_additive_group(quotient_ring b (ideal_pow b Q (i + 1))))
               theta /\
              group_kernel
               (inertia_group(k,l) h b (ideal_pow b Q (i + 1)),
                ring_additive_group(quotient_ring b (ideal_pow b Q (i + 1))))
               theta =
              group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 2))) /\
              (!f. f IN group_carrier
                         (inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
                   ==> ?a. a IN ideal_pow b Q i /\
                           theta f = ring_coset b (ideal_pow b Q (i + 1)) a) /\
              (!f a. f IN group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
                     a IN ideal_pow b Q i /\
                     ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
                     IN ideal_pow b Q (i + 2)
                     ==> theta f = ring_coset b (ideal_pow b Q (i + 1)) a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INERTIA_GROUP_WILD_MAP) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `theta:(B->B)->(B->bool)` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `ring_ideal b (ideal_pow b Q (i + 1):B->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; PRIME_IMP_RING_IDEAL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GROUP_HOMOMORPHISM; RING_ADDITIVE_GROUP; INERTIA_GROUP] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:B->B` o check (fun th ->
      is_forall(concl th) && can (find_term is_exists) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN
    EXISTS_TAC `a:B` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`; `i:num`] RING_IDEAL_IDEAL_POW) THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN
    ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[group_kernel; RING_ADDITIVE_GROUP] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:B->B` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC
   `(f:B->B) IN
    group_carrier(inertia_group(k:A ring,l) h b (ideal_pow b Q (i + 1)))`
  THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `i:num`; `i + 1`] INERTIA_GROUP_IDEAL_POW_MONO) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(i:num) <= i + 1 /\ (i + 1) + 1 = i + 2`] THEN
  ASM SET_TAC[]);;

let INERTIA_GROUP_IDEAL_POW_CHAR_POW = prove
 (`!(h:A->B) k l b Q i f.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\ 1 <= i /\
        f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
        ==> group_pow (galois_group(k,l) h) f (ring_char(quotient_ring b Q))
            IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 2)))`,
REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_0 b = ring_0 (l:B ring)` ASSUME_TAC THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`]
    DEDEKIND_PRIME_IDEAL_UNIFORMIZER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                 `t:B`; `i:num`] INERTIA_GROUP_WILD_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `theta:(B->B)->(B->bool)` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `f:B->B` o check (fun th ->
    is_forall (concl th) &&
    can (find_term is_exists) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:B) IN ring_carrier b` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IDEAL_POW; RING_IDEAL_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. group_pow (galois_group(k,l) h) f n IN
        group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))) /\
        theta(group_pow (galois_group(k,l) h) f n) =
        ring_coset b (ideal_pow b Q (i + 1)) (ring_mul b (ring_of_num b n) a)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
     (fun th -> concl th = `ring_0 b = ring_0 (l:B ring)`)) THEN
    INDUCT_TAC THEN
    REWRITE_TAC[group_pow; CONJUNCT2 GALOIS_GROUP; ring_of_num] THENL
     [SUBGOAL_THEN
       `!j. (I:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b j)`
      ASSUME_TAC THENL
       [GEN_TAC THEN
        MP_TAC(ISPEC `inertia_group(k,l) (h:A->B) b j` GROUP_ID) THEN
        REWRITE_TAC[CONJUNCT1(CONJUNCT2 INERTIA_GROUP)];
        ALL_TAC] THEN
      ASM_SIMP_TAC[RING_MUL_LZERO; RING_COSET_0; RING_IDEAL_IDEAL_POW;
                   RING_IDEAL_IMP_SUBSET; GSYM QUOTIENT_RING_0] THEN
      MP_TAC(ISPECL [`b:B ring`; `ideal_pow b Q (i + 1):B->bool`]
        QUOTIENT_RING_0) THEN
      REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `f o group_pow (galois_group(k,l) (h:A->B)) f n IN
        group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))`
      ASSUME_TAC THENL
       [MP_TAC(ISPEC `inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))`
          GROUP_MUL) THEN
        ASM_SIMP_TAC[CONJUNCT2 INERTIA_GROUP];
        ASM_REWRITE_TAC[]] THEN
      FIRST_ASSUM(fun th -> W(fun (asl,w) ->
        MP_TAC(SPECL [`f:B->B`;
                      `group_pow (galois_group(k,l) (h:A->B)) (f:B->B) n`]
          (check (fun th -> can (find_term ((=) `g:B->B`)) (concl th))
                 th)))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[QUOTIENT_RING_ADD; RING_IDEAL_IDEAL_POW; RING_MUL;
                   RING_OF_NUM] THEN
      AP_TERM_TAC THEN
      ASM_SIMP_TAC[RING_OF_NUM; RING_RULE
       `ring_add r a (ring_mul r n a) =
        ring_mul r (ring_add r n (ring_1 r)) a:B`]];
    SUBGOAL_THEN `ring_of_num b (ring_char(quotient_ring b (Q:B->bool))) IN Q`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`]
        RING_HOMOMORPHISM_RING_COSET) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `ring_char(quotient_ring b (Q:B->bool))` o
        MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM) THEN
      MP_TAC(ISPECL [`quotient_ring b (Q:B->bool)`;
                     `ring_char(quotient_ring b (Q:B->bool))`]
        RING_OF_NUM_EQ_0) THEN
      REWRITE_TAC[DIVIDES_REFL] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; RING_OF_NUM];
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC
      `ring_char(quotient_ring b (Q:B->bool))`) THEN
    FIRST_ASSUM(MP_TAC o SPEC
      `group_pow (galois_group(k,l) (h:A->B)) (f:B->B)
         (ring_char(quotient_ring b (Q:B->bool)))` o check (fun th ->
      can (find_term ((=) `ring_0:(B->bool)ring->B->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[QUOTIENT_RING_0; RING_IDEAL_IDEAL_POW; RING_COSET_EQ_IDEAL;
                 RING_MUL; RING_OF_NUM] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `i + 1 = 1 + i:num`] THEN
    MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN
    ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET]]);;

let INERTIA_GROUP_WILD_PGROUP = prove
 (`!(h:A->B) k l b Q.
        finite_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ field_of_fractions(b,l) I /\
        prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q))
        ==> pgroup {ring_char(quotient_ring b Q)}
                   (inertia_group(k,l) h b (ideal_pow b Q 2))`,
REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `prime(ring_char(quotient_ring b (Q:B->bool)))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `quotient_ring b (Q:B->bool)` INTEGRAL_DOMAIN_CHAR) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FIELD_IMP_INTEGRAL_DOMAIN THEN
      ASM_SIMP_TAC[FIELD_QUOTIENT_RING; PRIME_IMP_RING_IDEAL] THEN
      MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
      ASM_REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED];
      ASM_MESON_TAC[RING_CHAR_FINITE]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PGROUP_SING] THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!m. group_pow (galois_group(k,l) (h:A->B)) f
          (ring_char(quotient_ring b (Q:B->bool)) EXP m) IN
        group_carrier(inertia_group(k,l) h b (ideal_pow b Q (m + 2)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
       `!g j. g IN group_carrier(inertia_group(k,l) (h:A->B) b j)
              ==> g IN group_carrier(galois_group(k,l) h)`
      ASSUME_TAC THENL
       [REWRITE_TAC[inertia_group] THEN
        MESON_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET; SUBSET];
        ALL_TAC] THEN
      INDUCT_TAC THENL
       [REWRITE_TAC[EXP; ADD_CLAUSES] THEN ASM_MESON_TAC[GROUP_POW_1];
        ALL_TAC] THEN
      REWRITE_TAC[EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
      SUBGOAL_THEN `(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[GROUP_POW_MUL] THEN
      REWRITE_TAC[ARITH_RULE `SUC m + 2 = (m + 1) + 2`] THEN
      MATCH_MP_TAC INERTIA_GROUP_IDEAL_POW_CHAR_POW THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= m + 1:num`;
                      ARITH_RULE `(m + 1) + 1 = m + 2:num`];
    ALL_TAC] THEN
MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`]
    INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N + 1:num`)) THEN
  REWRITE_TAC[ARITH_RULE `N <= N + 1:num`;
              ARITH_RULE `(N + 1) + 1 = N + 2:num`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
    can (find_term ((=) `(EXP)`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_SING] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `group_pow (inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2)) =
    group_pow (galois_group(k,l) h)`
  ASSUME_TAC THENL
   [REWRITE_TAC[inertia_group; GROUP_POW_SUBGROUP_GENERATED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2)`; `f:B->B`;
                 `ring_char(quotient_ring b (Q:B->bool)) EXP N`]
    GROUP_POW_EQ_ID) THEN
  ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2 INERTIA_GROUP)] THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW] THEN MESON_TAC[]);;

(* The wild inertia group G_1 lies in a subgroup c of the inertia group G_0  *)
(* iff the index of c in G_0 is prime to the residue characteristic.         *)
let INERTIA_GROUP_WILD_SUBSET = prove
 (`!(h:A->B) k l b Q c m.
        finite_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ field_of_fractions(b,l) I /\
        prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\
        c subgroup_of inertia_group(k,l) h b Q /\
        CARD(group_carrier(inertia_group(k,l) h b Q)) = m * CARD c
        ==> (group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2))
             SUBSET c <=>
             ~(ring_char(quotient_ring b Q) divides m))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p = ring_char(quotient_ring b (Q:B->bool))` THEN
  SUBGOAL_THEN `ring_0 b = ring_0 (l:B ring)` ASSUME_TAC THENL
   [UNDISCH_TAC `subring_generated l (ring_carrier b) = (b:B ring)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `prime p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_CHAR THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FIELD_IMP_INTEGRAL_DOMAIN THEN
    ASM_SIMP_TAC[FIELD_QUOTIENT_RING; PRIME_IMP_RING_IDEAL] THEN
    MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `G0 = inertia_group(k,l) (h:A->B) b Q` THEN
  ABBREV_TAC
   `N = group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2))` THEN
  SUBGOAL_THEN `FINITE(group_carrier(G0:(B->B)group)) /\ FINITE(N:(B->B)->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G0"; "N"] THEN
    CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `group_carrier(galois_group(k,l) (h:A->B))` THEN
    REWRITE_TAC[inertia_group; GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET] THEN
    ASM_SIMP_TAC[FINITE_GALOIS_GROUP];
    ALL_TAC] THEN
  (* N is normal in G0, a p-group, of index prime to p *)
  SUBGOAL_THEN `(N:(B->B)->bool) normal_subgroup_of G0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`b:B ring`; `Q:B->bool`]
      DEDEKIND_PRIME_IDEAL_UNIFORMIZER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`;
                   `t:B`] INERTIA_GROUP_TAME_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `theta:(B->B)->(B->bool)` (CONJUNCTS_THEN2
      (ASSUME_TAC o MATCH_MP NORMAL_SUBGROUP_GROUP_KERNEL)
      (SUBST_ALL_TAC o CONJUNCT2))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?j. CARD(N:(B->B)->bool) = p EXP j` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`]
      INERTIA_GROUP_WILD_PGROUP) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2)`; `p:num`]
     FINITE_PGROUP_SING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. coprime(d,p) /\ CARD(group_carrier(G0:(B->B)group)) =
        d * CARD(N:(B->B)->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`]
      INERTIA_GROUP_TAME_QUOTIENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
    MP_TAC(ISPECL [`G0:(B->B)group`; `N:(B->B)->bool`]
      LAGRANGE_THEOREM_RIGHT) THEN
    ASM_SIMP_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP; GSYM QUOTIENT_GROUP] THEN
    DISCH_TAC THEN
    EXISTS_TAC `CARD(group_carrier(quotient_group G0 (N:(B->B)->bool)))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC NORMAL_PGROUP_SUBSET_COPRIME_INDEX THEN
    MAP_EVERY EXISTS_TAC [`G0:(B->B)group`; `p:num`; `m:num`; `j:num`] THEN
    ASM_REWRITE_TAC[]] THEN
  (* if N SUBSET c then the index of c divides that of N *)
  SUBGOAL_THEN `CARD(N:(B->B)->bool) divides CARD(c:(B->B)->bool)` MP_TAC THENL
   [MP_TAC(ISPECL [`subgroup_generated G0 (c:(B->B)->bool)`; `N:(B->B)->bool`]
      LAGRANGE_THEOREM) THEN
    ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `group_carrier(G0:(B->B)group)` THEN
      ASM_SIMP_TAC[SUBGROUP_OF_IMP_SUBSET];
      ASM_SIMP_TAC[SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ] THEN
      ASM_SIMP_TAC[NORMAL_SUBGROUP_IMP_SUBGROUP]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e:num` o REWRITE_RULE[divides]) THEN
  SUBGOAL_THEN `~(p:num = 0) /\ ~(p = 1)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(N:(B->B)->bool) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXP_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `d:num = m * e` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:num`; `m * e:num`; `CARD(N:(B->B)->bool)`]
      EQ_MULT_RCANCEL) THEN
    REWRITE_TAC[ASSUME `~(CARD(N:(B->B)->bool) = 0)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `d * CARD(N:(B->B)->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[MULT_AC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(p:num) divides 1` MP_TAC THENL
   [UNDISCH_TAC `coprime(d:num,p)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `d:num`)) THEN
    UNDISCH_TAC `p divides (m:num)` THEN CONV_TAC NUMBER_RULE;
    ASM_REWRITE_TAC[DIVIDES_ONE]]);;

(* G_1 is trivial iff p does not divide |G_0| (the case c = {1} of           *)
(* INERTIA_GROUP_WILD_SUBSET).                                               *)
let INERTIA_GROUP_WILD_TRIVIAL = prove
 (`!(h:A->B) k l b Q.
        finite_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ field_of_fractions(b,l) I /\
        prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q))
        ==> (group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2)) = {I} <=>
             ~(ring_char(quotient_ring b Q) divides
               CARD(group_carrier(inertia_group(k,l) h b Q))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`; `b:B ring`; `Q:B->bool`; `{I:B->B}`;
    `CARD(group_carrier(inertia_group(k,l) (h:A->B) b Q))`]
   INERTIA_GROUP_WILD_SUBSET) THEN
  ASM_REWRITE_TAC[CARD_SING; MULT_CLAUSES] THEN ANTS_TAC THENL
   [MP_TAC(ISPEC `inertia_group(k,l) (h:A->B) b Q` TRIVIAL_SUBGROUP_OF) THEN
    REWRITE_TAC[CONJUNCT2 INERTIA_GROUP];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC(SET_RULE `(a:B->B) IN s ==> (s = {a} <=> s SUBSET {a})`) THEN
  MP_TAC(ISPEC `inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2)` GROUP_ID) THEN
  REWRITE_TAC[CONJUNCT2 INERTIA_GROUP]);;

let NUMBER_FIELD_WILD_INERTIA_TRIVIAL = prove
 (`!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> (group_carrier
              (inertia_group(k,l) h (ring_of_integers l)
                (ideal_pow (ring_of_integers l) Q 2)) = {I} <=>
             ~(ring_char(quotient_ring (ring_of_integers l) Q) divides
               ramification_index (ring_of_integers k,ring_of_integers l)
                                  h Q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field k /\ ring_homomorphism(k,l) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[GALOIS_IMP_FIELD_EXTENSION; field_extension;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_DECOMPOSITION_GROUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:A->bool`; `Q:B->bool`]
    NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC INERTIA_GROUP_WILD_TRIVIAL THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING; DEDEKIND_RING_OF_INTEGERS;
               GALOIS_GROUP_RING_OF_INTEGERS] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      NUMBER_FIELD_TOWER_LAW) THEN
    ASM_SIMP_TAC[];
    MESON_TAC[GALOIS_GROUP_RING_OF_INTEGERS];
    MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
    ASM_SIMP_TAC[]]);;
