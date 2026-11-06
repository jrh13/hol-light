(* ========================================================================= *)
(* The ideal norm: the index of an ideal j of a ring r, i.e. the number of   *)
(* elements of the quotient ring r/j (meaningful when r/j is finite).        *)
(*                                                                           *)
(*   ideal_norm r j = CARD(ring_carrier(quotient_ring r j))                  *)
(*                                                                           *)
(* Main results, in any ring: N(r) = 1, 1 < N(j) for proper j, and N(j) as   *)
(* an element of r lies in j (IDEAL_NORM_IN_IDEAL); along a chain of ideals  *)
(* j SUBSET k, |r/j| = |r/k| |k/j| (CARD_EQ_QUOTIENT_RING_CHAIN for          *)
(* cardinals, CARD_QUOTIENT_RING_CHAIN, FINITE_QUOTIENT_RING_CHAIN), so for  *)
(* j SUBSET k of finite index N(k) divides N(j) (IDEAL_NORM_SUBSET_DIVIDES)  *)
(* and N(k) = N(j) iff k = j (IDEAL_NORM_SUBSET_EQ); in a Noetherian ring    *)
(* r/jk is finite if r/j and r/k are (FINITE_QUOTIENT_RING_IDEAL_PROD). In a *)
(* Dedekind domain: |r/jk| = |r/j| |r/k| for nonzero ideals                  *)
(* (CARD_EQ_QUOTIENT_RING_IDEAL_PROD), the multiplicativity N(jk) = N(j)     *)
(* N(k) of the norm (IDEAL_NORM_MUL; it suffices that one of j, k is         *)
(* nonzero), N(j^n) = N(j)^n (IDEAL_NORM_IDEAL_POW), the norm of a finite    *)
(* product of nonzero ideals of finite index is the product of the norms     *)
(* (IDEAL_NORM_IDEAL_PRODUCT), and N(j) is the product of N(p)^v_p(j) over   *)
(* the nonzero primes p above j (IDEAL_NORM_FACTORIZATION); for a finite set *)
(* of nonzero primes of finite index the norm of the product of the p^e(p)   *)
(* is the product of the N(p)^e(p) (DEDEKIND_IDEAL_NORM_PRIME_POWERS). An    *)
(* ideal of finite index whose norm is a prime number is maximal, in any     *)
(* ring (IDEAL_NORM_PRIME_IMP_MAXIMAL).                                      *)
(*                                                                           *)
(* Multiplicativity uses one coset bijection: for nonzero ideals j and k     *)
(* choose a nonzero a in jk and b with j = (a,b) (strong two generators);    *)
(* then j SUBSET jk + (b), and x |-> x b + jk maps r onto j/jk with the      *)
(* fibres of r -> r/k, as {x | x b IN jk} = (jk:j) = k.                      *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (quotient rings, cosets; cardinal arithmetic  *)
(* of Library/card.ml), ANT/ideal_arith.ml (ideal_prod, ideal_pow,           *)
(* ideal_quotient, ideal_product), ANT/dedekind.ml (cancellation,            *)
(* factorization, ideal_valuation), ANT/dedekind_struct.ml                   *)
(* (DEDEKIND_TWO_GENERATORS_STRONG).                                         *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_struct.ml";;

(* ------------------------------------------------------------------------- *)
(* The ideal norm (the index of the ideal).                                  *)
(* ------------------------------------------------------------------------- *)

let ideal_norm = new_definition
 `ideal_norm (r:A ring) j = CARD(ring_carrier(quotient_ring r j))`;;

let IDEAL_NORM_CARRIER = prove
 (`!r:A ring. ideal_norm r (ring_carrier r) = 1`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `ring_carrier r:A->bool`]
    TRIVIAL_QUOTIENT_RING) THEN
  REWRITE_TAC[RING_IDEAL_CARRIER; PROPER_IDEAL_ALT] THEN
  SIMP_TAC[TRIVIAL_RING_HAS_SIZE_1; HAS_SIZE; ideal_norm]);;

let IDEAL_NORM_POS = prove
 (`!r j:A->bool.
        FINITE(ring_carrier(quotient_ring r j)) ==> 1 <= ideal_norm r j`,
  SIMP_TAC[ideal_norm; ARITH_RULE `1 <= n <=> ~(n = 0)`; CARD_EQ_0;
           RING_CARRIER_NONEMPTY]);;

let IDEAL_NORM_GT_1 = prove
 (`!r (j:A->bool).
     ring_ideal r j /\ ~(j = ring_carrier r) /\
     FINITE(ring_carrier(quotient_ring r j))
     ==> 1 < ideal_norm r j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] TRIVIAL_QUOTIENT_RING) THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] IDEAL_NORM_POS) THEN
  ASM_REWRITE_TAC[PROPER_IDEAL_ALT; TRIVIAL_RING_HAS_SIZE_1; HAS_SIZE] THEN
  REWRITE_TAC[ideal_norm] THEN ARITH_TAC);;

let IDEAL_NORM_IN_IDEAL = prove
 (`!r j:A->bool.
     ring_ideal r j /\ FINITE(ring_carrier(quotient_ring r j))
     ==> ring_of_num r (ideal_norm r j) IN j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `quotient_ring r (j:A->bool)` RING_CHAR_DIVIDES_ORDER) THEN
  ASM_REWRITE_TAC[GSYM RING_OF_NUM_EQ_0; GSYM ideal_norm] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_RING_COSET) THEN
  DISCH_THEN(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th)]) THEN
  ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; RING_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Finite quotients along a chain of ideals.                                 *)
(* ------------------------------------------------------------------------- *)

(* For j SUBSET k the induced epimorphism r/j -> r/k has kernel k/j, the     *)
(* image of k in r/j; so |r/j| = |r/k| |k/j| as cardinals.                   *)

let CARD_EQ_QUOTIENT_RING_CHAIN = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ j SUBSET k
        ==> ring_carrier(quotient_ring r j) =_c
            ring_carrier(quotient_ring r k) *_c IMAGE (ring_coset r j) k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `quotient_ring r (k:A->bool)`; `j:A->bool`;
                 `ring_coset r (k:A->bool)`]
    QUOTIENT_RING_UNIVERSAL_EPIMORPHISM) THEN
  ASM_SIMP_TAC[RING_EPIMORPHISM_RING_COSET; RING_KERNEL_RING_COSET] THEN
  REWRITE_TAC[RING_EPIMORPHISM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:(A->bool)->(A->bool)` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o ONCE_REWRITE_RULE[CARD_EQ_SYM] o
              MATCH_MP CARD_EQ_RING_IMAGE_KERNEL) THEN
  ASM_SIMP_TAC[ring_kernel; QUOTIENT_RING_CARRIER; QUOTIENT_RING_0] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!x:A. x IN ring_carrier r ==> (g(ring_coset r j x) = k <=> x IN k)`
  MP_TAC THENL [ASM_SIMP_TAC[RING_COSET_EQ_IDEAL]; ALL_TAC] THEN
  MP_TAC(MATCH_MP RING_IDEAL_IMP_SUBSET
   (ASSUME `ring_ideal r (k:A->bool)`)) THEN
  SET_TAC[]);;

let FINITE_QUOTIENT_RING_CHAIN = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ j SUBSET k
        ==> (FINITE(ring_carrier(quotient_ring r j)) <=>
             FINITE(ring_carrier(quotient_ring r k)) /\
             FINITE(IMAGE (ring_coset r j) k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`]
    CARD_EQ_QUOTIENT_RING_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o MATCH_MP CARD_FINITE_CONG) THEN
  REWRITE_TAC[CARD_MUL_FINITE_EQ; RING_CARRIER_NONEMPTY; IMAGE_EQ_EMPTY] THEN
  ASM_MESON_TAC[RING_IDEAL_IMP_NONEMPTY]);;

let FINITE_QUOTIENT_RING_MONO = prove
 (`!r (j:A->bool) k.
     ring_ideal r j /\ ring_ideal r k /\ j SUBSET k /\
     FINITE(ring_carrier(quotient_ring r j))
     ==> FINITE(ring_carrier(quotient_ring r k))`,
  MESON_TAC[FINITE_QUOTIENT_RING_CHAIN]);;

let CARD_QUOTIENT_RING_CHAIN = prove
 (`!r (j:A->bool) k.
     ring_ideal r j /\ ring_ideal r k /\ j SUBSET k /\
     FINITE(ring_carrier(quotient_ring r j))
     ==> CARD(ring_carrier(quotient_ring r j)) =
         CARD(ring_carrier(quotient_ring r k)) *
         CARD(IMAGE (ring_coset r j) k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`]
    FINITE_QUOTIENT_RING_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CARD_MUL_C] THEN MATCH_MP_TAC CARD_EQ_CARD_IMP THEN
  ASM_SIMP_TAC[CARD_MUL_FINITE; CARD_EQ_QUOTIENT_RING_CHAIN]);;

let IDEAL_NORM_SUBSET_EQ = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ j SUBSET k /\
        FINITE(ring_carrier(quotient_ring r j))
        ==> (ideal_norm r k = ideal_norm r j <=> k = j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`]
    FINITE_QUOTIENT_RING_CHAIN) THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`]
    CARD_QUOTIENT_RING_CHAIN) THEN
  ASM_REWRITE_TAC[GSYM ideal_norm] THEN DISCH_THEN SUBST1_TAC THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:A->bool`] IDEAL_NORM_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ARITH_RULE `n = n * 1`] THEN
  ASM_SIMP_TAC[EQ_MULT_LCANCEL; ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPEC `IMAGE (ring_coset r j) (k:A->bool)` CARD_LE_1) THEN
  ASM_REWRITE_TAC[LE_REFL; SUBSET; FORALL_IN_IMAGE; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:A->bool`) THEN
  SUBGOAL_THEN `!x:A. x IN k ==> x IN j` MP_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_coset r j (x:A) = ring_coset r j (ring_0 r)` MP_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN k`)]) THEN
      CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[IN_RING_IDEAL_0];
      ASM_SIMP_TAC[RING_COSET_EQ; RING_0; RING_SUB_RZERO]];
    ASM SET_TAC[]]);;

let IDEAL_NORM_SUBSET_DIVIDES = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ j SUBSET k /\
        FINITE(ring_carrier(quotient_ring r j))
        ==> ideal_norm r k divides ideal_norm r j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ideal_norm; divides] THEN
  EXISTS_TAC `CARD(IMAGE (ring_coset r j) (k:A->bool))` THEN
  MATCH_MP_TAC CARD_QUOTIENT_RING_CHAIN THEN ASM_REWRITE_TAC[]);;

(* In a Noetherian ring r/jk is finite if r/j and r/k are: with j = (t) for  *)
(* a finite t and a finite set u of representatives of r/k, every element of *)
(* j is congruent modulo jk to a combination of t with coefficients in u.    *)

let FINITE_QUOTIENT_RING_IDEAL_PROD = prove
 (`!r j k:A->bool.
        noetherian_ring r /\ ring_ideal r j /\ ring_ideal r k /\
        FINITE(ring_carrier(quotient_ring r j)) /\
        FINITE(ring_carrier(quotient_ring r k))
        ==> FINITE(ring_carrier(quotient_ring r (ideal_prod r j k)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_ideal r (ideal_prod r j k) /\ ideal_prod r j k SUBSET (j:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_PROD; IDEAL_PROD_SUBSET_LEFT;
                 RING_IDEAL_IMP_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_prod r j k:A->bool`; `j:A->bool`]
    FINITE_QUOTIENT_RING_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  (* d maps r to a finite set u of representatives of r/k *)
  MP_TAC(ISPECL [`ring_coset r (k:A->bool)`; `ring_carrier r:A->bool`;
                 `ring_carrier(quotient_ring r (k:A->bool))`]
    FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; SIMPLE_IMAGE; ETA_AX; SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!a:A. ?y. a IN ring_carrier r ==> y IN u /\ ring_sub r a y IN k`
  MP_TAC THENL
   [X_GEN_TAC `a:A` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_coset r k (a:A) IN IMAGE (ring_coset r k) u`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE];
      REWRITE_TAC[IN_IMAGE]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:A->bool`; `a:A`; `y:A`] RING_COSET_EQ) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `d:A->A` THEN DISCH_THEN(LABEL_TAC "d") THEN
  (* finitely many generators t of j *)
  FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool` o GEN_REWRITE_RULE I
    [noetherian_ring]) THEN
  ASM_REWRITE_TAC[finitely_generated_ideal; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a:A. a IN t ==> a IN j` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\e. ring_coset r (ideal_prod r j k)
                 (ring_sum r t (\a. ring_mul r (e a) a)))
          {e:A->A | (!a. a IN t ==> e a IN u) /\
                    (!a. ~(a IN t) ==> e a = ring_0 r)}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_FUNSPACE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(ASSUME
   `ideal_generated r t = (j:A->bool)`)] THEN
  SIMP_TAC[IDEAL_GENERATED_FINITE; ASSUME `FINITE(t:A->bool)`;
           ASSUME `(t:A->bool) SUBSET ring_carrier r`] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:A->A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC `\a:A. if a IN t then (d:A->A)(c a) else ring_0 r` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a:A. a IN t ==> a IN ring_carrier r /\ (d:A->A)(c a) IN ring_carrier r /\
                     (d:A->A)(c a) IN u /\ ring_sub r (c a) (d(c a)) IN k`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    USE_THEN "d" (MP_TAC o SPEC `(c:A->A) a`) THEN ASM_SIMP_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_prod r j k:A->bool`;
                 `ring_sum r t (\a. ring_mul r ((c:A->A) a) a)`;
                 `ring_sum r t (\a. ring_mul r
                    (if a IN t then (d:A->A)((c:A->A) a) else ring_0 r) a)`]
    RING_COSET_EQ) THEN
  ASM_REWRITE_TAC[RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_MUL; RING_0]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[GSYM RING_SUB_RDISTRIB] THEN
  SUBGOAL_THEN `ideal_prod r j k = ideal_prod r k (j:A->bool)` SUBST1_TAC
  THENL [ASM_SIMP_TAC[IDEAL_PROD_COMM; RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC[RING_SUB]);;

let FINITE_QUOTIENT_RING_IDEAL_POW = prove
 (`!(a:A ring) j n.
        noetherian_ring a /\ ring_ideal a j /\
        FINITE(ring_carrier(quotient_ring a j))
        ==> FINITE(ring_carrier(quotient_ring a (ideal_pow a j n)))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[IDEAL_POW_0] THEN MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN
    EXISTS_TAC `j:A->bool` THEN
    ASM_SIMP_TAC[RING_IDEAL_CARRIER; RING_IDEAL_IMP_SUBSET];
    REWRITE_TAC[IDEAL_POW_SUC] THEN MATCH_MP_TAC FINITE_QUOTIENT_RING_IDEAL_PROD
    THEN ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW]]);;

let IDEAL_NORM_PRIME_IMP_MAXIMAL = prove
 (`!r j:A->bool.
        ring_ideal r j /\ FINITE(ring_carrier(quotient_ring r j)) /\
        prime(ideal_norm r j)
        ==> maximal_ideal r j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[maximal_ideal; proper_ideal; PSUBSET] THEN
  ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `prime(ideal_norm r (ring_carrier r:A->bool))` THEN
    REWRITE_TAC[IDEAL_NORM_CARRIER; PRIME_1];
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `k:A->bool` THEN
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`]
    IDEAL_NORM_SUBSET_DIVIDES) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [prime]) THEN
  DISCH_THEN(fun th -> DISCH_THEN(DISJ_CASES_TAC o MATCH_MP th)) THENL
   [MP_TAC(ISPECL [`r:A ring`; `k:A->bool`] IDEAL_NORM_GT_1) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[FINITE_QUOTIENT_RING_MONO]; ASM_ARITH_TAC];
    MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`]
      IDEAL_NORM_SUBSET_EQ) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Multiplicativity in a Dedekind domain.                                    *)
(* ------------------------------------------------------------------------- *)

(* The coset bijection (any ring): if j SUBSET l + (b) with b IN j and       *)
(* x b IN l <=> x IN k, then x |-> x b + l maps the carrier onto j/l with    *)
(* the fibres of r -> r/k. In a Dedekind domain it applies to l = jk.        *)

let CARD_EQ_QUOTIENT_RING_IDEAL_PROD = prove
 (`!r j k:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ring_ideal r k /\
        ~(j = {ring_0 r}) /\ ~(k = {ring_0 r})
        ==> ring_carrier(quotient_ring r (ideal_prod r j k)) =_c
            ring_carrier(quotient_ring r j) *_c
            ring_carrier(quotient_ring r k)`,
  let lemma = prove
   (`!r j k l (b:A).
          ring_ideal r j /\ ring_ideal r k /\ ring_ideal r l /\ b IN j /\
          j SUBSET ring_setadd r l (ideal_generated r {b}) /\
          (!x. x IN ring_carrier r ==> (ring_mul r x b IN l <=> x IN k))
          ==> IMAGE (ring_coset r l) j =_c ring_carrier(quotient_ring r k)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(b:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (ring_coset r l) j =
      IMAGE (\x:A. ring_coset r l (ring_mul r x b)) (ring_carrier r)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FUN_IN_IMAGE;
                   IN_RING_IDEAL_LMUL] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_SIMP_TAC[ring_setadd; IDEAL_GENERATED_SING_ALT; IN_ELIM_THM] THEN
      REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                  LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
      MAP_EVERY X_GEN_TAC [`w:A`; `u:A`; `z:A`] THEN STRIP_TAC THEN
      EXISTS_TAC `z:A` THEN
      SUBGOAL_THEN `(w:A) IN ring_carrier r` ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[RING_COSET_EQ; RING_ADD; RING_MUL; RING_RULE
       `ring_sub r (ring_add r w (ring_mul r b z)) (ring_mul r z b):A = w`];
      ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; SIMPLE_IMAGE] THEN
      MATCH_MP_TAC CARD_EQ_IMAGES THEN
      ASM_SIMP_TAC[RING_COSET_EQ; RING_MUL; GSYM RING_SUB_RDISTRIB;
                   RING_SUB]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_ideal r (ideal_prod r j k) /\ ideal_prod r j k SUBSET (j:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_PROD; IDEAL_PROD_SUBSET_LEFT;
                 RING_IDEAL_IMP_SUBSET];
    ALL_TAC] THEN
  TRANS_TAC CARD_EQ_TRANS
   `ring_carrier(quotient_ring r j) *_c
    IMAGE (ring_coset r (ideal_prod r j k)) (j:A->bool)` THEN
  ASM_SIMP_TAC[CARD_EQ_QUOTIENT_RING_CHAIN] THEN
  MATCH_MP_TAC CARD_MUL_CONG THEN REWRITE_TAC[CARD_EQ_REFL] THEN
  MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?a:A. a IN ideal_prod r j k /\ ~(a = ring_0 r)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`]
      IDEAL_PROD_EQ_ZERO) THEN
    MP_TAC(ISPECL [`r:A ring`; `ideal_prod r j k:A->bool`]
      IN_RING_IDEAL_0) THEN
    ASM_SIMP_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `a:A`]
    DEDEKIND_TWO_GENERATORS_STRONG) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `b:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier r /\ b IN ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* j = (a) + (b) SUBSET jk + (b) since a IN jk *)
    GEN_REWRITE_TAC LAND_CONV [SYM(ASSUME `ideal_generated r {a:A,b} = j`)] THEN
    GEN_REWRITE_TAC LAND_CONV [IDEAL_GENERATED_INSERT] THEN
    MATCH_MP_TAC RING_SETADD_MONO THEN
    ASM_SIMP_TAC[SUBSET_REFL; IDEAL_GENERATED_MINIMAL; SING_SUBSET];
    ALL_TAC] THEN
  (* x b IN jk <=> x j SUBSET jk <=> x IN (jk:j) = k by cancellation *)
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ideal_quotient r (ideal_prod r j k) j = (k:A->bool)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THENL
   [MP_TAC(ISPECL [`r:A ring`; `k:A->bool`; `j:A->bool`]
      DEDEKIND_IDEAL_QUOTIENT_CANCEL) THEN
    MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`] IDEAL_PROD_COMM) THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET];
    ASM_REWRITE_TAC[ideal_quotient; IN_ELIM_THM]] THEN
  EQ_TAC THENL [DISCH_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(SET_RULE
   `!t. s SUBSET {y:A | y IN t /\ P y} ==> !y. y IN s ==> P y`) THEN
  EXISTS_TAC `ring_carrier r:A->bool` THEN
  GEN_REWRITE_TAC LAND_CONV [SYM(ASSUME `ideal_generated r {a:A,b} = j`)] THEN
  MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
  ASM_SIMP_TAC[RING_IDEAL_QUOTIENT_LMUL; INSERT_SUBSET; EMPTY_SUBSET;
               IN_ELIM_THM; IN_RING_IDEAL_LMUL]);;

let IDEAL_NORM_MUL = prove
 (`!r j k:A->bool.
     dedekind_domain r /\
     ring_ideal r j /\ ring_ideal r k /\
     (~(j = {ring_0 r}) \/ ~(k = {ring_0 r})) /\
     FINITE(ring_carrier(quotient_ring r j)) /\
     FINITE(ring_carrier(quotient_ring r k))
     ==> ideal_norm r (ideal_prod r j k) =
         ideal_norm r j * ideal_norm r k`,
  let lemma = prove
   (`!r k:A->bool.
        integral_domain r /\ ring_ideal r k /\ ~(k = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r {ring_0 r}))
        ==> k = ring_carrier r`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `field(r:A ring)` MP_TAC THENL
     [MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `FINITE(ring_carrier(quotient_ring r {ring_0 r:A}))` THEN
      SIMP_TAC[QUOTIENT_RING_CARRIER; RING_IDEAL_0; SIMPLE_IMAGE; ETA_AX] THEN
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
      SIMP_TAC[IMP_CONJ; RING_COSET_TRIVIAL] THEN SET_TAC[];
      REWRITE_TAC[FIELD_EQ_TRIVIAL_IDEALS] THEN ASM_MESON_TAC[]]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `j = {ring_0 r:A}` THEN ASM_CASES_TAC `k = {ring_0 r:A}` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `k = ring_carrier r:A->bool` SUBST1_TAC THENL
     [MATCH_MP_TAC lemma THEN ASM_SIMP_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN];
      SIMP_TAC[IDEAL_PROD_LZERO; SUBSET_REFL; IDEAL_NORM_CARRIER;
               MULT_CLAUSES]];
    SUBGOAL_THEN `j = ring_carrier r:A->bool` SUBST1_TAC THENL
     [MATCH_MP_TAC lemma THEN ASM_SIMP_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN];
      SIMP_TAC[IDEAL_PROD_CARRIER_LEFT; RING_IDEAL_0; IDEAL_NORM_CARRIER;
               MULT_CLAUSES]];
    ASM_SIMP_TAC[ideal_norm; GSYM CARD_MUL_C] THEN
    MATCH_MP_TAC CARD_EQ_CARD_IMP THEN
    ASM_SIMP_TAC[CARD_MUL_FINITE; CARD_EQ_QUOTIENT_RING_IDEAL_PROD]]);;

let IDEAL_NORM_IDEAL_POW = prove
 (`!r j:A->bool n.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r j))
        ==> FINITE(ring_carrier(quotient_ring r (ideal_pow r j n))) /\
            ideal_norm r (ideal_pow r j n) = ideal_norm r j EXP n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[IDEAL_POW_0; IDEAL_NORM_CARRIER; EXP] THEN
    MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC `j:A->bool` THEN
    ASM_SIMP_TAC[RING_IDEAL_CARRIER; RING_IDEAL_IMP_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_ideal r (ideal_pow r j n) /\ ~(ideal_pow r j n = {ring_0 r:A})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; IDEAL_POW_EQ_ZERO;
                 DEDEKIND_IMP_INTEGRAL_DOMAIN];
    ASM_SIMP_TAC[IDEAL_POW_SUC; EXP; FINITE_QUOTIENT_RING_IDEAL_PROD;
                 DEDEKIND_IMP_NOETHERIAN; IDEAL_NORM_MUL]]);;

let IDEAL_NORM_PRIME_POWER = prove
 (`!r (p:A->bool) n.
     dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
     FINITE(ring_carrier(quotient_ring r p))
     ==> FINITE(ring_carrier(quotient_ring r (ideal_pow r p (SUC n)))) /\
         ideal_norm r (ideal_pow r p (SUC n)) =
         ideal_norm r p EXP (SUC n)`,
  SIMP_TAC[IDEAL_NORM_IDEAL_POW; PRIME_IMP_RING_IDEAL]);;

let IDEAL_NORM_IDEAL_PRODUCT = prove
 (`!r s (f:K->A->bool).
        dedekind_domain r /\ FINITE s /\
        (!i. i IN s
             ==> ring_ideal r (f i) /\ ~(f i = {ring_0 r}) /\
                 FINITE(ring_carrier(quotient_ring r (f i))))
        ==> FINITE(ring_carrier(quotient_ring r (ideal_product r s f))) /\
            ideal_norm r (ideal_product r s f) =
            nproduct s (\i. ideal_norm r (f i))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IDEAL_PRODUCT_EMPTY; IDEAL_NORM_CARRIER; NPRODUCT_CLAUSES;
           FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `ring_carrier r:A->bool`]
      TRIVIAL_QUOTIENT_RING) THEN
    SIMP_TAC[RING_IDEAL_CARRIER; PROPER_IDEAL_ALT; TRIVIAL_IMP_FINITE_RING];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `f:K->A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:K->A->bool`) THEN
  ASM_SIMP_TAC[IDEAL_PRODUCT_INSERT] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_ideal r (ideal_product r t (f:K->A->bool)) /\
    ~(ideal_product r t f = {ring_0 r})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_PRODUCT; IDEAL_PRODUCT_EQ_ZERO;
                 DEDEKIND_IMP_INTEGRAL_DOMAIN; NOT_EXISTS_THM;
                 TAUT `~(p /\ q) <=> p ==> ~q`];
    ASM_SIMP_TAC[FINITE_QUOTIENT_RING_IDEAL_PROD; DEDEKIND_IMP_NOETHERIAN;
                 IDEAL_NORM_MUL]]);;

(* The norm of a finite product of nonzero ideals of finite index is the     *)
(* product of the norms; applied to the factorization of j.                  *)

let IDEAL_NORM_FACTORIZATION = prove
 (`!r j:A->bool.
     dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
     FINITE(ring_carrier(quotient_ring r j))
     ==> ideal_norm r j =
         nproduct {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ j SUBSET p}
                  (\p. ideal_norm r p EXP ideal_valuation r p j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] DEDEKIND_IDEAL_FACTORIZATION) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `s = {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ (j:A->bool) SUBSET p}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!p:A->bool. p IN s ==> prime_ideal r p /\ ~(p = {ring_0 r}) /\
                           FINITE(ring_carrier(quotient_ring r p))`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `p:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC `j:A->bool` THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`r:A ring`; `s:(A->bool)->bool`;
    `\p:A->bool. ideal_pow r p (ideal_valuation r p j)`]
   IDEAL_NORM_IDEAL_PRODUCT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; PRIME_IMP_RING_IDEAL; IDEAL_POW_EQ_ZERO;
                 DEDEKIND_IMP_INTEGRAL_DOMAIN; IDEAL_NORM_IDEAL_POW];
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[nproduct] THEN MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_MUL) THEN
  ASM_SIMP_TAC[IDEAL_NORM_IDEAL_POW; PRIME_IMP_RING_IDEAL]);;

let DEDEKIND_IDEAL_NORM_PRIME_POWERS = prove
 (`!r t (e:(A->bool)->num).
        dedekind_domain r /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        FINITE(ring_carrier(quotient_ring r P)))
        ==> FINITE(ring_carrier(quotient_ring r
                     (ideal_product r t (\P. ideal_pow r P (e P))))) /\
            ideal_norm r (ideal_product r t (\P. ideal_pow r P (e P))) =
            nproduct t (\P. ideal_norm r P EXP e P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  MP_TAC(ISPECL [`r:A ring`; `t:(A->bool)->bool`;
                 `\P:A->bool. ideal_pow r P (e P)`]
    IDEAL_NORM_IDEAL_PRODUCT) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; IDEAL_POW_EQ_ZERO; PRIME_IMP_RING_IDEAL;
               IDEAL_NORM_IDEAL_POW] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_MESON_TAC[IDEAL_NORM_IDEAL_POW; PRIME_IMP_RING_IDEAL]);;
