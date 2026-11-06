(* ========================================================================= *)
(* Ramification and the discriminant.                                        *)
(*                                                                           *)
(* A prime p ramifies in the number field k (some prime P of the ring of     *)
(* integers above p has ramification index > 1) iff p divides the            *)
(* discriminant d_K (NUMBER_FIELD_RAMIFIED_DISCRIMINANT); hence only         *)
(* finitely many primes ramify (NUMBER_FIELD_FINITE_RAMIFIED_PRIMES).        *)
(*                                                                           *)
(* Route (no different, no embeddings): for any ring r free over Z and any   *)
(* modulus m, the cosets of a Z-basis are a basis of r/mr over               *)
(* integer_mod_ring m, and traces and discriminants are those of r reduced   *)
(* mod m (FREE_BASIS_QUOTIENT_RING_INTEGER_MOD,                              *)
(* ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD,                                  *)
(* BASIS_DISCRIMINANT_QUOTIENT_RING_INTEGER_MOD); a free algebra over a      *)
(* finite field has nonzero discriminant iff it is reduced                   *)
(* (ANT/finite_field_trace.ml), so p divides d_K iff O/pO is not reduced     *)
(* (NUMBER_FIELD_DISCRIMINANT_DIVIDES); in a Dedekind domain r/j is reduced  *)
(* iff no prime occurs in j with exponent > 1                                *)
(* (DEDEKIND_QUOTIENT_RING_REDUCED of ANT/dedekind.ml). Two consequences for *)
(* traces, used by ANT/different.ml: in a ring free over Z the elements      *)
(* nilpotent modulo p have traces divisible by p                             *)
(* (ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD, from ALGEBRA_TRACE_NILPOTENT of     *)
(* Library/ring_det.ml), and if p r = P INTER Q with P maximal and P + Q =   *)
(* r, some element of Q has a trace prime to p                               *)
(* (ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL, from                                *)
(* ALGEBRA_TRACE_COMAXIMAL_NONZERO of ANT/finite_field_trace.ml).            *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (RING_HOMOMORPHISM_SUM_MUL),                  *)
(* Library/fieldtheory.ml, ANT/dedekind.ml                                   *)
(* (DEDEKIND_QUOTIENT_RING_REDUCED), Library/ring_det.ml                     *)
(* (ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE,                                    *)
(* BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE, ALGEBRA_TRACE_NILPOTENT),           *)
(* ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml,             *)
(* ANT/discriminant.ml and ANT/finite_field_trace.ml                         *)
(* (BASIS_DISCRIMINANT_EQ_0_FINITE,                                          *)
(* ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO).                                *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/dedekind.ml";;
needs "Library/ring_det.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/finite_field_trace.ml";;

(* ------------------------------------------------------------------------- *)
(* Rings free over Z, reduced modulo an integer m.                           *)
(* ------------------------------------------------------------------------- *)

(* In r/mr the integers act through integer_mod_ring m.                     *)
let RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING = prove
 (`!r:A ring m.
        ring_homomorphism
         (integer_mod_ring m,
          quotient_ring r (ideal_generated r {ring_of_num r m}))
         (ring_of_int(quotient_ring r (ideal_generated r {ring_of_num r m}))) /\
        !a. ring_coset r (ideal_generated r {ring_of_num r m})
                       (ring_of_int r a) =
            ring_of_int (quotient_ring r (ideal_generated r {ring_of_num r m}))
                        (a rem &m)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `j = ideal_generated r {ring_of_num r m:A}` THEN
  SUBGOAL_THEN `ring_ideal r (j:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_RING_COSET) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT;
                GSYM RING_OF_NUM_EQ_0] THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th)]) THEN
    ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; RING_OF_NUM] THEN
    EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN
    REWRITE_TAC[SING_SUBSET; IN_SING; RING_OF_NUM];
    DISCH_THEN(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_RING_OF_INT) THEN
    FIRST_X_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th]) THEN
    ASM_REWRITE_TAC[GSYM INTEGER_MOD_RING_OF_INT]]);;

(* In a ring free over Z, the multiples of m are the elements whose         *)
(* coordinates are all divisible by m.                                       *)
let FREE_BASIS_IDEAL_GENERATED_NUM = prove
 (`!r:A ring n w m x.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ x IN ring_carrier r
        ==> (x IN ideal_generated r {ring_of_num r m} <=>
             !i. i < n
                 ==> &m divides
                     basis_coordinates (integer_ring,r) (ring_of_int r)
                                       n w x i)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING; RING_OF_NUM; IN_ELIM_THM;
               ring_divides; GSYM RING_OF_INT_OF_NUM] THEN
  MP_TAC(ISPEC `r:A ring` RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    ASM_SIMP_TAC[BASIS_COORDINATES_LMUL; INTEGER_RING; IN_UNIV;
                 INTEGER_RULE `!m d:int. m divides m * d`];
    REWRITE_TAC[int_divides] THEN
    DISCH_THEN(X_CHOOSE_TAC `d:num->int` o
      REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    EXISTS_TAC `ring_sum r {i | i < n}
                  (\i. ring_mul r (ring_of_int r (d i)) ((w:num->A) i))` THEN
    REWRITE_TAC[RING_SUM] THEN
    MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`;
      `{i:num | i < n}`; `&m:int`; `d:num->int`; `w:num->A`]
      EXTENSION_LINCOMB_LMUL) THEN
    ASM_SIMP_TAC[INTEGER_RING; IN_UNIV; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`;
      `n:num`; `w:num->A`; `x:A`] BASIS_COORDINATES_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
      GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]]);;

let FREE_BASIS_QUOTIENT_RING_INTEGER_MOD = prove
 (`!r:A ring n w m.
        free_basis (integer_ring,r) (ring_of_int r) n w
        ==> free_basis
             (integer_mod_ring m,
              quotient_ring r (ideal_generated r {ring_of_num r m}))
             (ring_of_int
               (quotient_ring r (ideal_generated r {ring_of_num r m})))
             n (\i. ring_coset r (ideal_generated r {ring_of_num r m}) (w i))`,
  let lemma = prove
   (`!m c. c IN ring_carrier(integer_mod_ring m) /\ &m divides c ==> c = &0`,
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `&m:int = &0` THEN
    ASM_REWRITE_TAC[INTEGER_RULE `(&0:int) divides c <=> c = &0`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
    ASM_INT_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r:A ring`; `m:num`]
    RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING) THEN
  ABBREV_TAC `j = ideal_generated r {ring_of_num r m:A}` THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_RING_OF_INT o
    CONJUNCT1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTEGER_MOD_RING_OF_INT]) THEN
  SUBGOAL_THEN `ring_ideal r (j:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_RING_COSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN
   `!c. ring_coset r j
          (ring_sum r {i | i < n}
            (\i. ring_mul r (ring_of_int r (c i)) ((w:num->A) i))) =
        ring_sum (quotient_ring r j) {i | i < n}
          (\i. ring_mul (quotient_ring r j)
                 (ring_of_int (quotient_ring r j) (c i))
                 (ring_coset r j (w i)))`
  (LABEL_TAC "lin") THENL
   [GEN_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`r:A ring`; `quotient_ring r (j:A->bool)`;
      `ring_coset r (j:A->bool)`; `{i:num | i < n}`;
      `\i. ring_of_int r ((c:num->int) i):A`; `w:num->A`]
      RING_HOMOMORPHISM_SUM_MUL)) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_OF_INT] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th]);
    ALL_TAC] THEN
  REWRITE_TAC[free_basis] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `r:A ring` THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    EXISTS_TAC
     `\i. basis_coordinates (integer_ring,r) (ring_of_int r) n w (y:A) i
          rem &m` THEN
    ASM_REWRITE_TAC[INTEGER_MOD_RING_CARRIER_REM] THEN
    REMOVE_THEN "lin" (SUBST1_TAC o SYM o
      SPEC `basis_coordinates (integer_ring,r) (ring_of_int r) n w (y:A)`) THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c:num->int` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_sum r {i | i < n}
      (\i. ring_mul r (ring_of_int r ((c:num->int) i)) ((w:num->A) i)) IN j`
  MP_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) RING_COSET_EQ_IDEAL o snd) THEN
    ASM_REWRITE_TAC[RING_SUM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REMOVE_THEN "lin" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC QUOTIENT_RING_0 THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "lin" (K ALL_TAC)] THEN
  EXPAND_TAC "j" THEN
  ASM_SIMP_TAC[FREE_BASIS_IDEAL_GENERATED_NUM; RING_SUM;
               BASIS_COORDINATES_LINCOMB; RING_HOMOMORPHISM_INTEGER_RING_OF_INT;
               INTEGER_RING; IN_UNIV] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN ASM_MESON_TAC[lemma]);;

let ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD = prove
 (`!r:A ring n w m x.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ x IN ring_carrier r
        ==> algebra_trace
              (integer_mod_ring m,
               quotient_ring r (ideal_generated r {ring_of_num r m}))
              (ring_of_int
                (quotient_ring r (ideal_generated r {ring_of_num r m})))
              (ring_coset r (ideal_generated r {ring_of_num r m}) x) =
            algebra_trace (integer_ring,r) (ring_of_int r) x rem &m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r:A ring`; `m:num`]
    RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING) THEN
  FIRST_ASSUM(MP_TAC o SPEC `m:num` o
    MATCH_MP FREE_BASIS_QUOTIENT_RING_INTEGER_MOD) THEN
  ABBREV_TAC `j = ideal_generated r {ring_of_num r m:A}` THEN
  REWRITE_TAC[GSYM o_DEF; GSYM INTEGER_MOD_RING_OF_INT] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_ideal r (j:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_int r:int->A`;
                 `ring_of_int (quotient_ring r (j:A->bool))`;
                 `ring_of_int (integer_mod_ring m)`; `ring_coset r (j:A->bool)`;
                 `integer_ring`; `r:A ring`; `integer_mod_ring m`;
                 `quotient_ring r (j:A->bool)`; `n:num`; `w:num->A`; `x:A`]
    ALGEBRA_TRACE_NORM_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT;
               RING_HOMOMORPHISM_RING_COSET]);;

let BASIS_DISCRIMINANT_QUOTIENT_RING_INTEGER_MOD = prove
 (`!r:A ring n w m.
        free_basis (integer_ring,r) (ring_of_int r) n w
        ==> basis_discriminant
              (integer_mod_ring m,
               quotient_ring r (ideal_generated r {ring_of_num r m}))
              (ring_of_int
                (quotient_ring r (ideal_generated r {ring_of_num r m})))
              n (\i. ring_coset r (ideal_generated r {ring_of_num r m}) (w i)) =
            basis_discriminant (integer_ring,r) (ring_of_int r) n w rem &m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r:A ring`; `m:num`]
    RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING) THEN
  FIRST_ASSUM(MP_TAC o SPEC `m:num` o
    MATCH_MP FREE_BASIS_QUOTIENT_RING_INTEGER_MOD) THEN
  ABBREV_TAC `j = ideal_generated r {ring_of_num r m:A}` THEN
  REWRITE_TAC[GSYM o_DEF; GSYM INTEGER_MOD_RING_OF_INT] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BASIS_DISCRIMINANT_HOMOMORPHIC_IMAGE THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT;
                  INTEGER_MOD_RING_OF_INT] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_RING_COSET THEN
  EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]);;

(* In a ring free over Z, the elements nilpotent modulo p have traces        *)
(* divisible by p (the trace of a nilpotent of r/pr over the field Z/pZ      *)
(* vanishes).                                                                *)
let ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD = prove
 (`!r:A ring n w p x m.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ prime p /\
        x IN ring_carrier r /\ ~(m = 0) /\
        ring_pow r x m IN ideal_generated r {ring_of_num r p}
        ==> &p divides algebra_trace (integer_ring,r) (ring_of_int r) x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `j = ideal_generated r {ring_of_num r p:A}` THEN
  MP_TAC(ISPECL [`ring_of_int(quotient_ring r (j:A->bool))`;
                 `integer_mod_ring p`; `quotient_ring r (j:A->bool)`; `n:num`;
                 `\i. ring_coset r j ((w:num->A) i)`; `ring_coset r j (x:A)`]
    ALGEBRA_TRACE_NILPOTENT) THEN
  EXPAND_TAC "j" THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `p:num`; `x:A`]
    ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[FREE_BASIS_QUOTIENT_RING_INTEGER_MOD;
               RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING;
               FIELD_IMP_INTEGRAL_DOMAIN; FIELD_INTEGER_MOD_RING;
               INTEGER_MOD_RING_CLAUSES; INT_REM_EQ_0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[RING_NILPOTENT] THEN
  SUBGOAL_THEN `ring_ideal r (j:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_RING_COSET) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; EXISTS_TAC `m:num`] THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW th)]) THEN
  ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; RING_POW]);;

(* The same for r/pr when pr = P INTER Q with P maximal and P + Q = r: some  *)
(* element of Q has a trace prime to p (the case of the field Z/pZ of        *)
(* ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO).                                *)
let ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL = prove
 (`!r:A ring n w p P Q.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ prime p /\
        maximal_ideal r P /\ ring_ideal r Q /\
        ring_setadd r P Q = ring_carrier r /\
        P INTER Q = ideal_generated r {ring_of_num r p}
        ==> ?x. x IN Q /\
                ~(&p divides
                  algebra_trace (integer_ring,r) (ring_of_int r) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`integer_mod_ring p`; `r:A ring`;
                 `ring_of_int(quotient_ring r (P INTER Q:A->bool))`; `n:num`;
                 `\i. ring_coset r (P INTER Q:A->bool) ((w:num->A) i)`;
                 `P:A->bool`; `Q:A->bool`]
    ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO) THEN
  ASM_SIMP_TAC[FIELD_INTEGER_MOD_RING; FINITE_INTEGER_MOD_RING; PRIME_IMP_NZ;
               RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING;
               FREE_BASIS_QUOTIENT_RING_INTEGER_MOD] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `p:num`; `x:A`]
    ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; INT_REM_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Ramified primes are the prime divisors of the discriminant.               *)
(* ------------------------------------------------------------------------- *)

(* p divides d_K iff O/pO has a nonzero nilpotent element.                 *)
let NUMBER_FIELD_DISCRIMINANT_DIVIDES = prove
 (`!k:A ring p.
        number_field k /\ prime p
        ==> (&p divides number_field_discriminant k <=>
             ?x. ring_nilpotent
                   (quotient_ring (ring_of_integers k)
                      (ideal_generated (ring_of_integers k) {ring_of_num k p}))
                   x /\
                 ~(x = ring_0
                        (quotient_ring (ring_of_integers k)
                          (ideal_generated (ring_of_integers k)
                             {ring_of_num k p}))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I` THEN
  DISCH_THEN(X_CHOOSE_TAC `w:num->A`) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    NUMBER_FIELD_DISCRIMINANT_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`; `p:num`]
    BASIS_DISCRIMINANT_QUOTIENT_RING_INTEGER_MOD) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`; `p:num`]
    FREE_BASIS_QUOTIENT_RING_INTEGER_MOD) THEN
  MP_TAC(CONJUNCT1(ISPECL [`ring_of_integers k:A ring`; `p:num`]
    RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING)) THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `j = ideal_generated (ring_of_integers k) {ring_of_num k p:A}` THEN
  REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`integer_mod_ring p`;
    `quotient_ring (ring_of_integers k) (j:A->bool)`;
    `ring_of_int (quotient_ring (ring_of_integers k) (j:A->bool))`; `n:num`;
    `\i. ring_coset (ring_of_integers k) j ((w:num->A) i)`]
    BASIS_DISCRIMINANT_EQ_0_FINITE) THEN
  ASM_SIMP_TAC[FIELD_INTEGER_MOD_RING; FINITE_INTEGER_MOD_RING; PRIME_IMP_NZ;
               INTEGER_MOD_RING_CLAUSES]);;

let NUMBER_FIELD_RAMIFIED_DISCRIMINANT = prove
 (`!k:A ring p.
        number_field k /\ prime p
        ==> ((?P. prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P /\
                  1 < ramification_index (integer_ring,ring_of_integers k)
                        (ring_of_int k) P) <=>
             &p divides number_field_discriminant k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NUMBER_FIELD_DISCRIMINANT_DIVIDES] THEN
  ABBREV_TAC `j = ideal_generated (ring_of_integers k) {ring_of_num k p:A}` THEN
  SUBGOAL_THEN
   `ring_of_num k p IN ring_carrier(ring_of_integers k) /\
    ~(ring_of_num k p = ring_0 (k:A ring))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:num`] RING_OF_NUM) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[RING_OF_NUM_EQ_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[number_field]) THEN
    ASM_SIMP_TAC[DIVIDES_ZERO; PRIME_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_ideal (ring_of_integers k) (j:A->bool) /\ ~(j = {ring_0 k}) /\
    !P. prime_ideal (ring_of_integers k) P
        ==> (j SUBSET P <=> ring_of_num k p IN P)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_num k p:A`]
      IDEAL_GENERATED_EQ_0) THEN
    REWRITE_TAC[RING_OF_INTEGERS; ASSUME
     `ring_of_num k p IN ring_carrier(ring_of_integers (k:A ring))`;
     ASSUME `~(ring_of_num k p = ring_0 (k:A ring))`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REPEAT STRIP_TAC THEN EQ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `x IN s ==> s SUBSET t ==> (x:A) IN t`) THEN
      MATCH_MP_TAC IDEAL_GENERATED_INC THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
      DISCH_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
      ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; SING_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
    DEDEKIND_QUOTIENT_RING_REDUCED) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(~)`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_LE] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `prime_ideal (ring_of_integers k) (P:A->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ring_of_num k p IN (P:A->bool)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(P = {ring_0 k:A})` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `ring_of_num k p IN {ring_0 k:A}` THEN
      ASM_REWRITE_TAC[IN_SING];
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
        RAMIFICATION_INDEX_PRIME) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[]];
    ASM_CASES_TAC `P = {ring_0 k:A}` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `j:A->bool`]
      IDEAL_VALUATION_EQ_0) THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS] THEN
    ARITH_TAC]);;

let NUMBER_FIELD_FINITE_RAMIFIED_PRIMES = prove
 (`!k:A ring.
        number_field k
        ==> FINITE {p | prime p /\
                        ?P. prime_ideal (ring_of_integers k) P /\
                            ring_of_num k p IN P /\
                            1 < ramification_index
                                (integer_ring,ring_of_integers k) (ring_of_int
                                    k) P}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{p | p <= num_of_int(abs(number_field_discriminant (k:A ring)))}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`] NUMBER_FIELD_RAMIFIED_DISCRIMINANT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
  CONJ_TAC THENL [EXISTS_TAC `P:A->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
  ASM_SIMP_TAC[NUMBER_FIELD_DISCRIMINANT_NONZERO; INT_ABS_NUM] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS]);;
