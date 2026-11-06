(* ========================================================================= *)
(* Quadratic fields, abstractly (no complex numbers). A number field k of    *)
(* degree 2 contains a square root x of a unique squarefree integer d <> 1   *)
(* (QUADRATIC_FIELD_SQRT), every such d occurs (QUADRATIC_FIELD_EXISTS, via  *)
(* the Kronecker construction of Q[X]/(X^2 - d)), and d determines k up to   *)
(* isomorphism (QUADRATIC_FIELD_UNIQUE; QUADRATIC_FIELD_UNIQUE_EXPLICIT      *)
(* gives an isomorphism with x |-> y for square roots x and y of the same    *)
(* integer, x not in Q, by extending the homomorphism of the prime subfields *)
(* of Library/fieldtheory.ml along x |-> y: QUADRATIC_EXTEND_HOMOMORPHISM,   *)
(* from SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT with the minimal           *)
(* polynomial X^2 - x^2). For such x and d the ring of integers is Z + Z w   *)
(* with w = (1 + x) / 2 if d == 1 (mod 4) and w = x otherwise                *)
(* (QUADRATIC_FIELD_INTEGRAL_BASIS), and the discriminant is d or 4 d        *)
(* accordingly (QUADRATIC_FIELD_DISCRIMINANT). Squarefree is the library     *)
(* notion for num, applied to |d| (the integer forms of its facts are in     *)
(* Library/pocklington.ml, the bridges between integer and num divisibility  *)
(* in ANT/algmisc.ml). The decomposition of primes is in                     *)
(* ANT/quadratic_split.ml. Integer coordinates are unique: a + b x = c + d x *)
(* with integers a, b, c, d and x outside Q iff a = c and b = d              *)
(* (QUADRATIC_FIELD_INT_COORDINATES_EQ); the                                 *)
(* integer solutions of A^2 - d B^2 = 4 for d < 0, d <> -4, are A = +-2, B = *)
(* 0, or d = -1, A = 0, B = +-2, or d = -3, A = +-1, B = +-1                 *)
(* (INT_NORM_FORM_4_IMAGINARY).                                              *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml                       *)
(* (KRONECKER_SIMPLE_FIELD_EXTENSION, the simple algebraic extensions:       *)
(* RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN, _BASIS,                             *)
(* SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC,                                      *)
(* SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT;                                *)
(* PRIME_SUBFIELD_HOMOMORPHISM_EXISTS), Library/pocklington.ml               *)
(* (INT_SQUAREFREE_DECOMPOSITION, INT_SQUAREFREE_DIVPOW,                     *)
(* INT_SQUAREFREE_MUL_SQUARE), ANT/algmisc.ml (INT_DIVIDES_NUM_OF_INT_ABS,   *)
(* NUM_OF_INT_ABS_POW, FORALL_LT_2), Library/ring_det.ml, ANT/integral.ml,   *)
(* ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/discriminant.ml.            *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;
needs "ANT/integral.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/discriminant.ml";;

(* ------------------------------------------------------------------------- *)
(* The integers A, B with A^2 - d B^2 = 4 N, modulo 2.                       *)
(* ------------------------------------------------------------------------- *)

let INT_SQUARE_SUB_MUL_SQUARE_MOD_4 = prove
 (`!d A B N:int.
        ~(&4 divides d) /\ A pow 2 - d * B pow 2 = &4 * N
        ==> if (d == &1) (mod &4) then &2 divides (A - B)
            else &2 divides A /\ &2 divides B`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`A:int`; `&2:int`] INT_DIVISION) THEN
  MP_TAC(SPECL [`B:int`; `&2:int`] INT_DIVISION) THEN
  MP_TAC(SPECL [`d:int`; `&4:int`] INT_DIVISION) THEN
  REWRITE_TAC[INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_NUM] THEN
  SPEC_TAC(`d rem &4`,`e:int`) THEN SPEC_TAC(`d div &4`,`t:int`) THEN
  SPEC_TAC(`B rem &2`,`b:int`) THEN SPEC_TAC(`B div &2`,`s:int`) THEN
  SPEC_TAC(`A rem &2`,`a:int`) THEN SPEC_TAC(`A div &2`,`q:int`) THEN
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[INTEGER_RULE
   `!t e c n:int. (t * n + e == c) (mod n) <=> (e == c) (mod n)`;
              INTEGER_RULE
   `!t e n:int. n divides t * n + e <=> n divides e`;
              INTEGER_RULE
   `!q a s b n:int. n divides (q * n + a) - (s * n + b) <=>
                    n divides (a - b)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&4 divides ((a:int) pow 2 - e * b pow 2)` MP_TAC THENL
   [REWRITE_TAC[int_divides] THEN
    EXISTS_TAC `N - (q pow 2 + q * a - &4 * t * s pow 2 - &4 * t * s * b -
                     t * b pow 2 - e * s pow 2 - e * s * b):int` THEN
    ASM_INT_ARITH_TAC;
    UNDISCH_TAC `~(&4 divides (e:int))`] THEN
  SUBGOAL_THEN
   `((a:int) = &0 \/ a = &1) /\ ((b:int) = &0 \/ b = &1) /\
    ((e:int) = &0 \/ e = &1 \/ e = &2 \/ e = &3)`
  MP_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC)
   (CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC)
     (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC))) THEN
  REWRITE_TAC[GSYM INT_REM_EQ_0; GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

let INT_NORM_FORM_4_IMAGINARY = prove
 (`!A B d:int.
        d < &0 /\ ~(d = -- &4) /\ A pow 2 - d * B pow 2 = &4
        ==> B = &0 /\ (A = &2 \/ A = -- &2) \/
            d = -- &1 /\ A = &0 /\ (B = &2 \/ B = -- &2) \/
            d = -- &3 /\ (A = &1 \/ A = -- &1) /\ (B = &1 \/ B = -- &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:int. x pow 2 <= &4
                        ==> x = -- &2 \/ x = -- &1 \/ x = &0 \/ x = &1 \/
                            x = &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:int` THEN ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN
    DISCH_TAC THEN SUBGOAL_THEN `abs(x:int) <= &2` MP_TAC THENL
     [REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(&3:int) pow 2 <= abs x pow 2` MP_TAC THENL
       [MATCH_MP_TAC INT_POW_LE2 THEN ASM_INT_ARITH_TAC;
        ASM_INT_ARITH_TAC];
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:int) pow 2 <= &4 /\ (B:int) pow 2 <= &4`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `A:int` INT_LE_POW_2) THEN
    MP_TAC(SPEC `B:int` INT_LE_POW_2) THEN
    SUBGOAL_THEN `(B:int) pow 2 <= --d * B pow 2` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_LID] THEN
      MATCH_MP_TAC INT_LE_RMUL THEN REWRITE_TAC[INT_LE_POW_2] THEN
      ASM_INT_ARITH_TAC;
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(MATCH_MP th (ASSUME `(A:int) pow 2 <= &4`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `(B:int) pow 2 <= &4`))) THEN
  REPEAT(DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REDUCE_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Elements outside a subfield, and square roots of integers.                *)
(* ------------------------------------------------------------------------- *)

let IN_SUBFIELD_GENERATED_MUL_CANCEL = prove
 (`!k:A ring s a y.
        field k /\ a IN ring_carrier(subfield_generated k s) /\
        ~(a = ring_0 k) /\ y IN ring_carrier k /\
        ring_mul k a y IN ring_carrier(subfield_generated k s)
        ==> y IN ring_carrier(subfield_generated k s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `y = ring_mul k (ring_inv k a) (ring_mul k a y:A)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_ASSOC; RING_INV; FIELD_MUL_LINV; RING_MUL_LID];
    ASM_SIMP_TAC[RING_MUL_IN_SUBFIELD_GENERATED;
                 RING_INV_IN_SUBFIELD_GENERATED; FIELD_SUBFIELD_GENERATED]]);;

let SUBFIELD_GENERATED_ADD_MUL_EQ_0 = prove
 (`!k:A ring s a b x.
        field k /\ x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k s)) /\
        a IN ring_carrier(subfield_generated k s) /\
        b IN ring_carrier(subfield_generated k s)
        ==> (ring_add k a (ring_mul k b x) = ring_0 k <=>
             a = ring_0 k /\ b = ring_0 k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `s:A->bool`]
    RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `a:A` th) THEN MP_TAC(SPEC `b:A` th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_ADD_LZERO; RING_0] THEN
  MATCH_MP_TAC(TAUT `(~q ==> F) /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `~(x IN ring_carrier(subfield_generated k s:A ring))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC IN_SUBFIELD_GENERATED_MUL_CANCEL THEN
    EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ring_mul k b x = ring_neg k a:A` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `a:A`; `ring_mul k b x:A`] RING_ADD_EQ_0) THEN
      ASM_SIMP_TAC[RING_MUL] THEN MESON_TAC[];
      ASM_SIMP_TAC[RING_NEG_IN_SUBFIELD_GENERATED]];
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ring_add k a (ring_mul k (ring_0 k) x) = ring_0 k:A` THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_ADD_RZERO]]);;

let SUBFIELD_GENERATED_HALF_SUCC = prove
 (`!k:A ring s x.
        field k /\ ~(ring_of_num k 2 = ring_0 k) /\ x IN ring_carrier k
        ==> ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
              IN ring_carrier k /\
            ring_mul k (ring_of_num k 2)
              (ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)) =
            ring_add k (ring_1 k) x /\
            (ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
               IN ring_carrier(subfield_generated k s) <=>
             x IN ring_carrier(subfield_generated k s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A` THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "w" THEN ASM_SIMP_TAC[RING_DIV; RING_ADD; RING_1; RING_OF_NUM];
    DISCH_TAC THEN EXPAND_TAC "w" THEN REWRITE_TAC[ring_div] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_of_num k 2:A`] FIELD_MUL_RINV) THEN
    ASM_SIMP_TAC[RING_OF_NUM] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_add k (ring_1 k) x:A`;
                   `ring_inv k (ring_of_num k 2):A`]
     (RING_RULE
       `!k:A ring y h.
           ring_mul k (ring_of_num k 2) h = ring_1 k
           ==> ring_mul k (ring_of_num k 2) (ring_mul k y h) = y`)) THEN
    ASM_SIMP_TAC[RING_ADD; RING_1; RING_INV; RING_OF_NUM];
    STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN
       `x = ring_sub k (ring_mul k (ring_of_num k 2) w) (ring_1 k):A`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[RING_1; RING_RULE
         `ring_sub (r:A ring) (ring_add r (ring_1 r) x) (ring_1 r) = x`];
        ALL_TAC];
      EXPAND_TAC "w" THEN REWRITE_TAC[ring_div]] THEN
    REWRITE_TAC[ring_sub; GSYM RING_OF_INT_OF_NUM] THEN
    ASM_SIMP_TAC[RING_ADD_IN_SUBFIELD_GENERATED; RING_NEG_IN_SUBFIELD_GENERATED;
                 RING_MUL_IN_SUBFIELD_GENERATED; RING_1_IN_SUBFIELD_GENERATED;
                 RING_INV_IN_SUBFIELD_GENERATED; FIELD_SUBFIELD_GENERATED;
                 RING_OF_INT_IN_SUBFIELD_GENERATED]]);;

let FREE_BASIS_SUBFIELD_GENERATED_2 = prove
 (`!k:A ring s x.
        field k /\ x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k s)) /\
        (!z. z IN ring_carrier k
             ==> ?a b. a IN ring_carrier(subfield_generated k s) /\
                       b IN ring_carrier(subfield_generated k s) /\
                       z = ring_add k a (ring_mul k b x))
        ==> free_basis (subfield_generated k s,k) I 2
                       (\i. if i = 0 then ring_1 k else x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `s:A->bool`]
    RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN
  REWRITE_TAC[free_basis; FORALL_LT_2; ARITH_EQ; I_THM] THEN
  ASM_REWRITE_TAC[RING_1] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z:A) IN ring_carrier k`)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    EXISTS_TAC `\i. if i = 0 then a else b:A` THEN
    ASM_SIMP_TAC[FORALL_LT_2; ARITH_EQ; RING_SUM_LT_2; RING_MUL; RING_1;
                 RING_MUL_RID];
    X_GEN_TAC `c:num->A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `s:A->bool`; `(c:num->A) 0`; `(c:num->A) 1`;
                   `x:A`] SUBFIELD_GENERATED_ADD_MUL_EQ_0) THEN
    UNDISCH_TAC
     `ring_sum k {i | i < 2}
        (\i. ring_mul k (c i) (if i = 0 then ring_1 k else x)) =
      ring_0 k:A` THEN
    ASM_SIMP_TAC[RING_SUM_LT_2; RING_MUL; RING_1; ARITH_EQ; RING_MUL_RID;
                 CONJUNCT2 SUBFIELD_GENERATED]]);;

let INTEGRAL_ELEMENT_QUADRATIC = prove
 (`!k:A ring z b c.
        z IN ring_carrier k /\
        ring_add k (ring_pow k z 2)
                   (ring_add k (ring_mul k (ring_of_int k b) z)
                               (ring_of_int k c)) = ring_0 k
        ==> integral_element (integer_ring,k) (ring_of_int k) z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
  MAP_EVERY EXISTS_TAC [`2`; `\i. if i = 0 then c else b:int`] THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; INTEGER_RING; IN_UNIV;
               RING_SUM_LT_2; RING_MUL; RING_OF_INT; RING_POW; ARITH_EQ;
               RING_POW_0; RING_POW_1; RING_MUL_RID] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[RING_ADD_SYM; RING_MUL; RING_OF_INT]);;

let PRIME_SUBFIELD_SQRT_INTEGER = prove
 (`!k:A ring x m.
        field k /\ ring_char k = 0 /\
        x IN ring_carrier(subfield_generated k {ring_0 k}) /\
        ring_pow k x 2 = ring_of_int k m
        ==> ?n. x = ring_of_int k n /\ m = n pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] INTEGRAL_ELEMENT_PRIME_SUBFIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN
    MAP_EVERY EXISTS_TAC [`&0:int`; `--m:int`] THEN
    ASM_SIMP_TAC[RING_OF_INT_0; RING_OF_INT_NEG; RING_MUL_LZERO;
                 RING_ADD_LZERO; RING_NEG; RING_OF_INT; RING_ADD_RNEG];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:int` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ring_pow (k:A ring) (ring_of_int k n) 2 = ring_of_int k m` THEN
    ASM_SIMP_TAC[GSYM RING_OF_INT_POW; RING_OF_INT_EQ_CHAR_0] THEN
    MESON_TAC[]]);;

let PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE = prove
 (`!k:A ring b d m.
        field k /\ ring_char k = 0 /\
        b IN ring_carrier(subfield_generated k {ring_0 k}) /\
        squarefree(num_of_int(abs d)) /\
        ring_mul k (ring_of_int k d) (ring_pow k b 2) = ring_of_int k m
        ==> ?n. b = ring_of_int k n /\ m = d * n pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(b:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(d:int = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `squarefree(num_of_int(abs(&0:int)))` THEN
    REWRITE_TAC[INT_ABS_NUM; NUM_OF_INT_OF_NUM; SQUAREFREE_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `ring_mul k (ring_of_int k d) b:A`; `d * m:int`]
    PRIME_SUBFIELD_SQRT_INTEGER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_IN_SUBFIELD_GENERATED;
                 RING_OF_INT_IN_SUBFIELD_GENERATED; RING_OF_INT_MUL;
                 RING_OF_INT; RING_RULE
     `ring_pow (k:A ring) (ring_mul k d b) 2 =
      ring_mul k d (ring_mul k d (ring_pow k b 2))`];
    DISCH_THEN(X_CHOOSE_THEN `n:int` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(d:int) divides n` MP_TAC THENL
   [MATCH_MP_TAC INT_SQUAREFREE_DIVPOW THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    CONV_TAC INTEGER_RULE;
    REWRITE_TAC[int_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:int` SUBST_ALL_TAC)] THEN
  EXISTS_TAC `t:int` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_of_int k d:A`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_OF_INT;
                 RING_OF_INT_EQ_0_CHAR_0; GSYM RING_OF_INT_MUL];
    UNDISCH_TAC `d * m = (d * t:int) pow 2` THEN
    REWRITE_TAC[INT_ARITH `(d * t:int) pow 2 = d * d * t pow 2`] THEN
    ASM_REWRITE_TAC[INT_EQ_MUL_LCANCEL]]);;

let SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD = prove
 (`!k:A ring x d.
        field k /\ ring_char k = 0 /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1)
        ==> ~(x IN ring_carrier(subfield_generated k {ring_0 k}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`] PRIME_SUBFIELD_SQRT_INTEGER) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `n:int` THEN
  DISCH_THEN(SUBST_ALL_TAC o CONJUNCT2) THEN
  UNDISCH_TAC `squarefree(num_of_int(abs((n:int) pow 2)))` THEN
  REWRITE_TAC[INT_ABS_POW; NUM_OF_INT_ABS_POW; SQUAREFREE_EXP; ARITH_EQ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `int_of_num`) THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
  UNDISCH_TAC `~((n:int) pow 2 = &1)` THEN
  ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN MESON_TAC[INT_POW_ONE]);;

(* ------------------------------------------------------------------------- *)
(* Number fields of degree 2 and their square roots.                         *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_FREE_BASIS = prove
 (`!k:A ring y.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        y IN ring_carrier k /\
        ~(y IN ring_carrier(subfield_generated k {ring_0 k}))
        ==> free_basis (subfield_generated k {ring_0 k},k) I 2
                       (\i. if i = 0 then ring_1 k else y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `y:A`] NUMBER_FIELD_ALGEBRAIC) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [number_field]) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = subfield_generated (k:A ring) {ring_0 k}` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `field(q:A ring) /\ field_extension(q,k) (I:A->A)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg q (minimal_polynomial (q,k) (I:A->A) y) = 2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `y:A`]
      MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE) THEN
    MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `y:A`]
      MINIMAL_POLYNOMIAL_DEG_EQ_1) THEN
    MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `y:A`]
      MINIMAL_POLYNOMIAL_IRREDUCIBLE) THEN
    ASM_SIMP_TAC[IMAGE_I] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP IRREDUCIBLE_IMP_POLY_DEG_NZ o
      CONJ (ASSUME `field(q:A ring)`)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `y:A`]
    SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN STRIP_TAC THEN
  SUBGOAL_THEN `subfield_generated k ((y:A) INSERT ring_carrier q) = k`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`I:A->A`; `I:A->A`; `q:A ring`;
                   `subfield_generated k ((y:A) INSERT ring_carrier q)`;
                   `k:A ring`] EXTENSION_DEGREE_EQ_TOWER) THEN
    ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION; FIELD_EXTENSION_SUBFIELD_GENERATED;
                 I_O_ID; IMAGE_I; SUBFIELD_GENERATED_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `y:A`]
    RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS) THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN
  ASM_SIMP_TAC[FREE_BASIS_FIELD; FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) /\ r ==> p ==> q /\ r`) THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC IMAGE_EQ THEN
    REWRITE_TAC[IN_ELIM_THM; FORALL_LT_2; ARITH_EQ] THEN
    ASM_SIMP_TAC[RING_POW_0; RING_POW_1];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_LT_2; ARITH_EQ] THEN
    SUBGOAL_THEN `ring_1 k IN ring_carrier(q:A ring)` MP_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC[RING_1_IN_SUBFIELD_GENERATED];
      ASM_MESON_TAC[]]]);;

let QUADRATIC_FIELD_COORDINATES = prove
 (`!k:A ring x z.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        z IN ring_carrier k
        ==> ?a b. a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                  b IN ring_carrier(subfield_generated k {ring_0 k}) /\
                  z = ring_add k a (ring_mul k b x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] QUADRATIC_FIELD_FREE_BASIS) THEN
  ASM_REWRITE_TAC[free_basis] THEN
  DISCH_THEN(MP_TAC o SPEC `z:A` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_SIMP_TAC[FORALL_LT_2; ARITH_EQ; I_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:num->A` THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(c:num->A) 0`; `(c:num->A) 1`] THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
    RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `(c:num->A) 0` th) THEN MP_TAC(SPEC `(c:num->A) 1` th)) THEN
  ASM_SIMP_TAC[RING_SUM_LT_2; RING_MUL; RING_1; ARITH_EQ; RING_MUL_RID]);;

let QUADRATIC_FIELD_INT_COORDINATES_EQ = prove
 (`!k (x:A) a b a' b'.
        field k /\ ring_char k = 0 /\ x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k}))
        ==> (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x) =
             ring_add k (ring_of_int k a') (ring_mul k (ring_of_int k b') x) <=>
             a = a' /\ b = b')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`; `ring_of_int k (a - a'):A`;
                 `ring_of_int k (b - b'):A`; `x:A`]
    SUBFIELD_GENERATED_ADD_MUL_EQ_0) THEN
  ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
  ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0; INT_SUB_0] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[RING_OF_INT_SUB] THEN
  UNDISCH_TAC
   `ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x) =
    ring_add k (ring_of_int k a') (ring_mul k (ring_of_int k b') (x:A))` THEN
  MP_TAC(ISPECL [`k:A ring`; `a:int`] RING_OF_INT) THEN
  MP_TAC(ISPECL [`k:A ring`; `b:int`] RING_OF_INT) THEN
  MP_TAC(ISPECL [`k:A ring`; `a':int`] RING_OF_INT) THEN
  MP_TAC(ISPECL [`k:A ring`; `b':int`] RING_OF_INT) THEN
  UNDISCH_TAC `(x:A) IN ring_carrier k` THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t)))
   [`ring_of_int k a:A`; `ring_of_int k b:A`; `ring_of_int k a':A`;
    `ring_of_int k b':A`; `x:A`] THEN
  RING_TAC);;

let QUADRATIC_FIELD_INTEGER_SQUARE = prove
 (`!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2
        ==> ?w m. w IN ring_carrier k /\
                  ~(w IN ring_carrier(subfield_generated k {ring_0 k})) /\
                  ring_pow k w 2 = ring_of_int k m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  SUBGOAL_THEN
   `?y:A. y IN ring_carrier k /\
          ~(y IN ring_carrier(subfield_generated k {ring_0 k}))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DEGREE_EQ_1) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN
    MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
      RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `y:A`; `ring_pow k y 2:A`]
    QUADRATIC_FIELD_COORDINATES) THEN
  ASM_SIMP_TAC[RING_POW; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `{0,1}`; `\i. if i = 0 then a else b:A`]
    PRIME_SUBFIELD_COMMON_DENOMINATOR) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                  NOT_IN_EMPTY; ARITH_EQ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `D:int` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `m0:int`) (X_CHOOSE_TAC `m1:int`))) THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
    RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `a:A` th) THEN MP_TAC(SPEC `b:A` th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`ring_sub k (ring_mul k (ring_of_int k (&2 * D)) y) (ring_of_int k m1):A`;
    `(&4 * D * m0 + m1 pow 2):int`] THEN
  ASM_SIMP_TAC[RING_SUB; RING_MUL; RING_OF_INT] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(y IN ring_carrier(subfield_generated k {ring_0 k:A}))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC IN_SUBFIELD_GENERATED_MUL_CANCEL THEN
    EXISTS_TAC `ring_of_int k (&2 * D):A` THEN
    ASM_SIMP_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED; RING_OF_INT_EQ_0_CHAR_0;
                 INT_ENTIRE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    SUBGOAL_THEN
     `ring_mul k (ring_of_int k (&2 * D)) y =
      ring_add k
       (ring_sub k (ring_mul k (ring_of_int k (&2 * D)) y) (ring_of_int k m1))
       (ring_of_int k m1):A`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; RING_OF_INT;
                   RING_RULE `ring_add (r:A ring) (ring_sub r x y) y = x`];
      ASM_SIMP_TAC[RING_ADD_IN_SUBFIELD_GENERATED;
                   RING_OF_INT_IN_SUBFIELD_GENERATED]];
    MP_TAC(ISPECL
     [`k:A ring`; `y:A`; `a:A`; `b:A`; `ring_of_int k D:A`;
      `ring_of_int k m0:A`; `ring_of_int k m1:A`]
     (RING_RULE
       `!k:A ring y a b D m0 m1.
          ring_pow k y 2 = ring_add k a (ring_mul k b y) /\
          ring_mul k D a = m0 /\ ring_mul k D b = m1
          ==> ring_pow k (ring_sub k (ring_mul k (ring_mul k (ring_of_num k 2)
                                                             D) y) m1) 2 =
              ring_add k (ring_mul k (ring_of_num k 4) (ring_mul k D m0))
                         (ring_pow k m1 2)`)) THEN
    ASM_SIMP_TAC[RING_OF_INT; RING_OF_INT_MUL; RING_OF_INT_ADD;
                 RING_OF_INT_POW; RING_OF_INT_OF_NUM]]);;

let QUADRATIC_FIELD_SQRT_EXISTS = prove
 (`!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2
        ==> ?d x. squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
                  x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_INTEGER_SQUARE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:A`; `m:int`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(m:int = &0)` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(w IN ring_carrier(subfield_generated k {ring_0 k:A}))` THEN
    MP_TAC(ISPECL [`k:A ring`; `w:A`; `2`] INTEGRAL_DOMAIN_POW_EQ_0) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_OF_INT_0; ARITH_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[RING_0_IN_SUBFIELD_GENERATED];
    DISCH_THEN(MP_TAC o MATCH_MP INT_SQUAREFREE_DECOMPOSITION)] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:int`; `c:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~(ring_of_num k c:A = ring_0 k)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?x:A. x IN ring_carrier k /\ ring_mul k (ring_of_num k c) x = w`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `ring_mul k (ring_inv k (ring_of_num k c)) w:A` THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV; RING_MUL_ASSOC; RING_OF_NUM;
                 FIELD_MUL_RINV; RING_MUL_LID];
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
     (fun th -> rhs(concl th) = `w:A`))] THEN
  SUBGOAL_THEN `ring_pow k x 2 = ring_of_int k d:A` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_pow k (ring_of_num k c) 2:A`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_POW; RING_OF_NUM;
                 RING_OF_INT; INTEGRAL_DOMAIN_POW_EQ_0; ARITH_EQ] THEN
    UNDISCH_TAC
     `ring_pow k (ring_mul k (ring_of_num k c) x) 2 =
      ring_of_int k (d * &c pow 2):A` THEN
    REWRITE_TAC[RING_OF_INT_MUL; RING_OF_INT_POW; RING_OF_INT_OF_NUM] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_of_num k c:A`; `x:A`;
                   `ring_of_int k d:A`]
     (RING_RULE
       `!k:A ring c x d.
           ring_pow k (ring_mul k c x) 2 = ring_mul k d (ring_pow k c 2)
           ==> ring_mul k (ring_pow k c 2) (ring_pow k x 2) =
               ring_mul k (ring_pow k c 2) d`)) THEN
    ASM_SIMP_TAC[RING_OF_NUM; RING_OF_INT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d:int`; `x:A`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~(ring_mul k (ring_of_num k c) x IN
                 ring_carrier (subfield_generated k {ring_0 k:A}))` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RING_MUL_IN_SUBFIELD_GENERATED THEN
  REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] (INTEGRAL_DOMAIN_RULE
   `!r x:A. integral_domain r /\ x IN ring_carrier r /\
            ring_pow r x 2 = ring_1 r
            ==> x = ring_1 r \/ x = ring_neg r (ring_1 r)`)) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; GSYM RING_OF_INT_1] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[RING_OF_INT_1; RING_1_IN_SUBFIELD_GENERATED;
               RING_NEG_IN_SUBFIELD_GENERATED]);;

let QUADRATIC_FIELD_SQRT_UNIQUE = prove
 (`!k:A ring x y d e.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
        y IN ring_carrier k /\ ring_pow k y 2 = ring_of_int k e /\
        squarefree(num_of_int(abs e)) /\ ~(e = &1)
        ==> d = e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  MP_TAC(ISPECL [`k:A ring`; `y:A`; `e:int`]
    SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `y:A`] QUADRATIC_FIELD_COORDINATES) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
    RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `a:A` th) THEN MP_TAC(SPEC `b:A` th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `a = ring_0 k:A` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL
     [`k:A ring`; `{ring_0 k:A}`;
      `ring_sub k (ring_add k (ring_pow k a 2)
                              (ring_mul k (ring_pow k b 2) (ring_of_int k d)))
                  (ring_of_int k e):A`;
      `ring_mul k (ring_of_num k 2) (ring_mul k a b):A`; `x:A`]
     SUBFIELD_GENERATED_ADD_MUL_EQ_0) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ring_sub] THEN
      REPEAT(FIRST[CONJ_TAC; MATCH_MP_TAC RING_ADD_IN_SUBFIELD_GENERATED;
                   MATCH_MP_TAC RING_NEG_IN_SUBFIELD_GENERATED;
                   MATCH_MP_TAC RING_MUL_IN_SUBFIELD_GENERATED;
                   MATCH_MP_TAC RING_POW_IN_SUBFIELD_GENERATED]) THEN
      ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED;
                      GSYM RING_OF_INT_OF_NUM];
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE)] THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `x:A`; `a:A`; `b:A`; `ring_of_int k d:A`;
                     `ring_of_int k e:A`]
       (RING_RULE
         `!k:A ring x a b D E.
             ring_pow k x 2 = D /\
             ring_pow k (ring_add k a (ring_mul k b x)) 2 = E
             ==> ring_add k
                  (ring_sub k (ring_add k (ring_pow k a 2)
                                          (ring_mul k (ring_pow k b 2) D)) E)
                  (ring_mul k (ring_mul k (ring_of_num k 2) (ring_mul k a b))
                              x) = ring_0 k`)) THEN
      ASM_SIMP_TAC[RING_OF_INT];
      DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN;
                 RING_MUL; RING_OF_NUM; RING_OF_NUM_EQ_0; DIVIDES_ZERO;
                 ARITH_EQ] THEN
    ASM_CASES_TAC `b = ring_0 k:A` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(ring_add k a (ring_mul k b x) IN
                   ring_carrier(subfield_generated k {ring_0 k:A}))` THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_ADD_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `b:A`; `d:int`; `e:int`]
    PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `b:A`; `ring_of_int k d:A`;
                   `ring_of_int k e:A`]
     (RING_RULE
       `!k:A ring x b D E.
           ring_pow k x 2 = D /\
           ring_pow k (ring_add k (ring_0 k) (ring_mul k b x)) 2 = E
           ==> ring_mul k D (ring_pow k b 2) = E`)) THEN
    ASM_SIMP_TAC[RING_OF_INT];
    DISCH_THEN(X_CHOOSE_THEN `n:int` (SUBST_ALL_TAC o CONJUNCT2))] THEN
  MATCH_MP_TAC INT_SQUAREFREE_MUL_SQUARE THEN EXISTS_TAC `d * n:int` THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let QUADRATIC_FIELD_SQRT = prove
 (`!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2
        ==> ?!d. squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
                 ?x. x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_SQRT_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`d:int`; `e:int`] THEN STRIP_TAC THEN
    MATCH_MP_TAC QUADRATIC_FIELD_SQRT_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `x:A`; `x':A`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Existence: adjoining a square root (Kronecker).                           *)
(* ------------------------------------------------------------------------- *)

let FIELD_EXTENSION_SQRT = prove
 (`!k:A ring c.
        field k /\ c IN ring_carrier k /\
        ~(?y. y IN ring_carrier k /\ ring_pow k y 2 = c)
        ==> ?l h z:((1->num)->A)->bool.
               field_extension(k,l) h /\ z IN ring_carrier l /\
               ring_pow l z 2 = h c /\
               !y. y IN ring_carrier l
                   ==> ?a b. a IN ring_carrier k /\ b IN ring_carrier k /\
                             y = ring_add l (h a) (ring_mul l (h b) z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `2`; `c:A`] POLY_VAR_POW_SUB_CONST) THEN
  ASM_SIMP_TAC[FIELD_NONTRIVIAL; ARITH_EQ] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`;
    `poly_sub k (poly_pow k (poly_var k one) 2) (poly_const k (c:A))`]
    KRONECKER_SIMPLE_FIELD_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_EQ; NOT_EXISTS_THM] THEN X_GEN_TAC `y:A` THEN
    MP_TAC(ISPECL [`I:A->A`; `k:A ring`; `k:A ring`; `2`; `c:A`; `y:A`]
      POLY_EVAL_VAR_POW_SUB_CONST) THEN
    ASM_CASES_TAC `(y:A) IN ring_carrier k` THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_I; I_O_ID; I_THM; RING_SUB_EQ_0;
                 RING_POW] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`l:(((1->num)->A)->bool) ring`; `h:A->((1->num)->A)->bool`;
    `z:((1->num)->A)->bool`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`l:(((1->num)->A)->bool) ring`; `h:A->((1->num)->A)->bool`;
    `z:((1->num)->A)->bool`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
   [field_extension]) THEN
  SUBGOAL_THEN `(h:A->((1->num)->A)->bool) c IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->((1->num)->A)->bool`; `k:A ring`;
                 `l:(((1->num)->A)->bool) ring`; `2`; `c:A`;
                 `z:((1->num)->A)->bool`] POLY_EVAL_VAR_POW_SUB_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SYM) THEN
  ASM_SIMP_TAC[RING_SUB_EQ_0; RING_POW] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->((1->num)->A)->bool`; `k:A ring`;
                 `l:(((1->num)->A)->bool) ring`;
    `poly_sub k (poly_pow k (poly_var k one) 2) (poly_const k (c:A))`;
                 `z:((1->num)->A)->bool`]
    RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN) THEN
  ASM_SIMP_TAC[POLY_RING_CLAUSES; POLY_EXTEND_EVALUATE; GSYM poly_eval;
               RING_SUB_REFL] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `{ring_pow l z n | n < 2} =
                {ring_1 l} UNION {z:((1->num)->A)->bool}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; IN_SING; UNWIND_THM2;
                ARITH_RULE `n < 2 <=> n = 0 \/ n = 1`; RIGHT_OR_DISTRIB;
                EXISTS_OR_THM] THEN
    ASM_SIMP_TAC[RING_POW_0; RING_POW_1];
    ASM_SIMP_TAC[RING_SPAN_UNION; RING_SPAN_SING; RING_1; IN_ELIM_THM]] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[RING_MUL_RID; RING_HOMOMORPHISM_IN_CARRIER]);;

let QUADRATIC_FIELD_EXISTS = prove
 (`!d. squarefree(num_of_int(abs d)) /\ ~(d = &1)
       ==> ?k:(((1->num)->real)->bool) ring x.
               number_field k /\
               extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
               x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = subfield_generated real_ring {ring_0 real_ring}` THEN
  SUBGOAL_THEN `field(q:real ring) /\ ring_char q = 0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_REAL_RING;
             RING_CHAR_SUBFIELD_GENERATED; REAL_RING_CHAR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real ring`; `ring_of_int q d:real`]
    FIELD_EXTENSION_SQRT) THEN
  ASM_REWRITE_TAC[RING_OF_INT] THEN ANTS_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `y:real` THEN
    EXPAND_TAC "q" THEN
    REWRITE_TAC[RING_POW_SUBFIELD_GENERATED;
                RING_OF_INT_SUBFIELD_GENERATED] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`real_ring`; `y:real`; `d:int`]
      SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN
    ASM_REWRITE_TAC[FIELD_REAL_RING; REAL_RING_CHAR];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC
   [`l:(((1->num)->real)->bool) ring`; `h:real->((1->num)->real)->bool`;
    `z:((1->num)->real)->bool`] THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`l:(((1->num)->real)->bool) ring`; `z:((1->num)->real)->bool`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (ASSUME
   `ring_homomorphism(q,l) (h:real->((1->num)->real)->bool)`)]) THEN
  SUBGOAL_THEN `ring_char(l:(((1->num)->real)->bool) ring) = 0` ASSUME_TAC
  THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_CHAR_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real->((1->num)->real)->bool) (ring_carrier q) =
    ring_carrier(subfield_generated l {ring_0 l})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`q:real ring`; `l:(((1->num)->real)->bool) ring`;
                   `h:real->((1->num)->real)->bool`]
      PRIME_SUBFIELD_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[PRIME_SUBFIELD_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(z IN ring_carrier(subfield_generated l
                         {ring_0 l:((1->num)->real)->bool}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN
    EXISTS_TAC `d:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `free_basis (subfield_generated l {ring_0 l},l) I 2
      (\i. if i = 0 then ring_1 l else z:((1->num)->real)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FREE_BASIS_SUBFIELD_GENERATED_2 THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:((1->num)->real)->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP
     (ASSUME `(y:((1->num)->real)->bool) IN ring_carrier l`)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(h:real->((1->num)->real)->bool) a`;
      `(h:real->((1->num)->real)->bool) b`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> lhs(concl th) =
      `IMAGE (h:real->((1->num)->real)->bool) (ring_carrier q)`)) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[NUMBER_FIELD_ALT] THEN
    MAP_EVERY EXISTS_TAC
     [`2`; `\i. if i = 0 then ring_1 l else z:((1->num)->real)->bool`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUMBER_FIELD_FREE_BASIS_DEGREE THEN
    EXISTS_TAC `\i. if i = 0 then ring_1 l else z:((1->num)->real)->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness: quadratic fields are determined by d.                         *)
(* ------------------------------------------------------------------------- *)

(* A homomorphism h from a subfield K extends to k, with x |-> y, when every *)
(* element of k is a + b x with a, b in K and h maps x^2 to y^2: since x is  *)
(* not in K, the minimal polynomial of x over K is X^2 - x^2 (irreducible: a *)
(* root a in K would give x = a or x = -a), y is a root of its image under   *)
(* h, and SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT extends h to the ring    *)
(* generated by x and K, which is k.                                         *)

let QUADRATIC_EXTEND_HOMOMORPHISM = prove
 (`!k:A ring l:B ring s h x y.
        field k /\ ring_homomorphism(subfield_generated k s,l) h /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k s)) /\
        ring_pow k x 2 IN ring_carrier(subfield_generated k s) /\
        (!z. z IN ring_carrier k
             ==> ?a b. a IN ring_carrier(subfield_generated k s) /\
                       b IN ring_carrier(subfield_generated k s) /\
                       z = ring_add k a (ring_mul k b x)) /\
        y IN ring_carrier l /\ ring_pow l y 2 = h(ring_pow k x 2)
        ==> ?g. ring_homomorphism(k,l) g /\ g x = y /\
                !a. a IN ring_carrier(subfield_generated k s) ==> g a = h a`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `K = subfield_generated k (s:A->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `field(K:A ring) /\ field_extension(K,k) (I:A->A) /\
    (!a:A. a IN ring_carrier K
           ==> a IN ring_carrier k /\ ring_neg k a IN ring_carrier K /\
               ring_pow K a 2 = ring_pow k a 2) /\
    (h:A->B)(ring_pow k x 2) IN ring_carrier l`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_EXTENSION_SUBFIELD_GENERATED;
                 RING_NEG_IN_SUBFIELD_GENERATED;
                 RING_POW_SUBFIELD_GENERATED] THEN
    ASM_MESON_TAC[RING_POW; RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over (K,k) (I:A->A) x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`I:A->A`; `K:A ring`; `k:A ring`; `x:A`; `2`]
      ALGEBRAIC_OVER_POW_EQ) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[ALGEBRAIC_OVER_IMAGE; I_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:A ring`; `2`; `ring_pow k x 2:A`]
    POLY_VAR_POW_SUB_CONST) THEN
  ASM_SIMP_TAC[FIELD_NONTRIVIAL; ARITH_EQ] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:A ring`; `k:A ring`; `l:B ring`; `I:A->A`; `h:A->B`;
                 `x:A`; `y:B`] SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `minimal_polynomial (K,k) (I:A->A) x =
    poly_sub K (poly_pow K (poly_var K one) 2)
               (poly_const K (ring_pow k x 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MINIMAL_POLYNOMIAL_UNIQUE THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[monic; COEFF_POLY_SUB; COEFF_POLY_VARPOW;
                      COEFF_POLY_CONST; ARITH_EQ] THEN
      SIMP_TAC[RING_SUB_RZERO; RING_1];
      MATCH_MP_TAC POLY_DEG_2_IRREDUCIBLE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `a:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`I:A->A`; `K:A ring`; `K:A ring`; `2`;
                     `ring_pow k x 2:A`; `a:A`]
        POLY_EVAL_VAR_POW_SUB_CONST) THEN
      ASM_REWRITE_TAC[RING_HOMOMORPHISM_I; I_O_ID; I_THM] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[RING_SUB_EQ_0; RING_POW] THEN
      GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_SQUARE_EQ; FIELD_IMP_INTEGRAL_DOMAIN] THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[POLY_EXTEND_SUB; POLY_EXTEND_VARPOW; POLY_EXTEND_CONST;
                   RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR; I_THM;
                   RING_POLYNOMIAL_CONST; FIELD_EXTENSION_IMP_HOMOMORPHISM;
                   RING_SUB_REFL; RING_POW]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_EVAL_VAR_POW_SUB_CONST; RING_SUB_REFL; I_THM; IMAGE_I] THEN
  SUBGOAL_THEN `subring_generated k ((x:A) INSERT ring_carrier K) = k`
  SUBST1_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REWRITE_TAC[SUBRING_GENERATED_SUPERSET; SUBSET] THEN X_GEN_TAC `z:A` THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_ADD_IN_SUBRING_GENERATED THEN CONJ_TAC THEN
  TRY(MATCH_MP_TAC RING_MUL_IN_SUBRING_GENERATED THEN CONJ_TAC) THEN
  MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_SIMP_TAC[IN_INSERT]);;

let QUADRATIC_FIELD_UNIQUE_EXPLICIT = prove
 (`!k:A ring l:B ring x y d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        number_field l /\
        extension_degree (subfield_generated l {ring_0 l},l) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d /\
        y IN ring_carrier l /\ ring_pow l y 2 = ring_of_int l d
        ==> ?h. ring_isomorphism(k,l) h /\ h x = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `field(k:A ring) /\ field(l:B ring) /\
                ring_char k = 0 /\ ring_char l = 0`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NUMBER_FIELD_IMP_FIELD; number_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`]
    PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h0:A->B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `{ring_0 k:A}`; `h0:A->B`;
                 `x:A`; `y:B`] QUADRATIC_EXTEND_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[QUADRATIC_FIELD_COORDINATES] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED] THEN SIMP_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:A->B` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `ring_monomorphism(k:A ring,l:B ring) h` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_RING_HOMOMORPHISM_MONOMORPHISM;
                 FIELD_IMP_NONTRIVIAL_RING];
    ASM_REWRITE_TAC[RING_ISOMORPHISM_MONOMORPHISM_ALT]] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    PRIME_SUBFIELD_MONOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
    RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [ring_monomorphism]) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((y:B) IN ring_carrier(subfield_generated l {ring_0 l}))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `w:B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `y:B`; `w:B`] QUADRATIC_FIELD_COORDINATES) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:B`; `b:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?a' b'. a' IN ring_carrier(subfield_generated k {ring_0 k}) /\
            b' IN ring_carrier(subfield_generated k {ring_0 k}) /\
            (h:A->B) a' = a /\ h b' = b`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `ring_add k a' (ring_mul k b' x):A` THEN
  SUBGOAL_THEN `(a':A) IN ring_carrier k /\ (b':A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_ADD; RING_MUL;
    MATCH_MP RING_HOMOMORPHISM_ADD th; MATCH_MP RING_HOMOMORPHISM_MUL th]));;

let QUADRATIC_FIELD_UNIQUE = prove
 (`!k:A ring l:B ring d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        number_field l /\
        extension_degree (subfield_generated l {ring_0 l},l) I = 2 /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
        (?x. x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d) /\
        (?y. y IN ring_carrier l /\ ring_pow l y 2 = ring_of_int l d)
        ==> k isomorphic_ring l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_ring] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `x:A`; `y:B`; `d:int`]
    QUADRATIC_FIELD_UNIQUE_EXPLICIT) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN
  EXISTS_TAC `d:int` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NUMBER_FIELD_IMP_FIELD; number_field]);;

(* ------------------------------------------------------------------------- *)
(* The ring of integers.                                                     *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_TRACE = prove
 (`!k:A ring x a b.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 IN ring_carrier(subfield_generated k {ring_0 k}) /\
        a IN ring_carrier(subfield_generated k {ring_0 k}) /\
        b IN ring_carrier(subfield_generated k {ring_0 k})
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_add k a (ring_mul k b x)) =
            ring_mul k (ring_of_num k 2) a`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
    RING_HOMOMORPHISM_SUBFIELD_INCLUSION) THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
    RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] QUADRATIC_FIELD_FREE_BASIS) THEN
  ASM_REWRITE_TAC[SUBSET] THEN
  ABBREV_TAC `q = subfield_generated (k:A ring) {ring_0 k}` THEN
  ABBREV_TAC `g = \i. if i = 0 then ring_1 k else x:A` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(g:num->A) 0 = ring_1 k /\ g 1 = x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `algebra_trace (q,k) (I:A->A) x = ring_0 k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `2`; `g:num->A`; `x:A`]
      ALGEBRA_TRACE_FREE_BASIS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[mul_matrix] THEN
    SUBGOAL_THEN
     `basis_coordinates (q,k) (I:A->A) 2 g (ring_mul k x (g 0)) 0 = ring_0 k /\
      basis_coordinates (q,k) (I:A->A) 2 g (ring_mul k x (g 1)) 1 = ring_0 k`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `ring_mul k x ((g:num->A) 0) = g 1` SUBST1_TAC THENL
         [ASM_SIMP_TAC[RING_MUL_RID]; ALL_TAC] THEN
        ASM_SIMP_TAC[BASIS_COORDINATES_BASIS; ARITH] THEN EXPAND_TAC "q" THEN
        REWRITE_TAC[SUBFIELD_GENERATED];
        SUBGOAL_THEN
         `ring_mul k x ((g:num->A) 1) = ring_mul k (I(ring_pow k x 2)) (g 0)`
        SUBST1_TAC THENL
         [ASM_SIMP_TAC[RING_MUL_RID; I_THM; RING_POW_2; RING_POW; RING_MUL];
          ALL_TAC] THEN
        ASM_SIMP_TAC[BASIS_COORDINATES_LMUL; BASIS_COORDINATES_BASIS; ARITH;
                     RING_1] THEN
        EXPAND_TAC "q" THEN
        ASM_SIMP_TAC[SUBFIELD_GENERATED; RING_MUL_RZERO; RING_POW]];
      W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_LT_2 o lhand o snd) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "q" THEN
      REWRITE_TAC[RING_0_IN_SUBFIELD_GENERATED; SUBFIELD_GENERATED] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[RING_ADD_LZERO; RING_0]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `b:A`; `x:A`]
    ALGEBRA_TRACE_SCALAR) THEN
  MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `a:A`;
                 `ring_mul k b x:A`] ALGEBRA_TRACE_ADD) THEN
  ASM_SIMP_TAC[I_THM; RING_MUL] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `2`; `g:num->A`; `a:A`]
    ALGEBRA_TRACE_NORM_BASE_FREE_BASIS) THEN
  ASM_SIMP_TAC[I_THM] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  EXPAND_TAC "q" THEN
  REWRITE_TAC[SUBFIELD_GENERATED; RING_OF_NUM_SUBFIELD_GENERATED] THEN
  ASM_SIMP_TAC[RING_MUL_RZERO; RING_ADD_RZERO; RING_MUL; RING_OF_NUM]);;

let QUADRATIC_FIELD_INTEGRAL_COORDINATES = prove
 (`!k:A ring x d z.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
        z IN ring_carrier(ring_of_integers k)
        ==> ?A B N. ring_mul k (ring_of_num k 2) z =
                    ring_add k (ring_of_int k A)
                               (ring_mul k (ring_of_int k B) x) /\
                    A pow 2 - d * B pow 2 = &4 * N`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `z:A`] QUADRATIC_FIELD_COORDINATES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN ASM SET_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
    RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `a:A` th) THEN MP_TAC(SPEC `b:A` th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `ring_add k a (ring_mul k b x):A`]
    NUMBER_FIELD_TRACE_INTEGRAL_Q) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `a:A`; `b:A`] QUADRATIC_FIELD_TRACE) THEN
  ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(X_CHOOSE_TAC `A:int`) THEN
  SUBGOAL_THEN
   `?U. ring_sub k (ring_mul k (ring_pow k b 2) (ring_of_int k d))
                   (ring_pow k a 2) = ring_of_int k U:A`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_PRIME_SUBFIELD) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `x:A`; `a:A`; `b:A`; `ring_of_int k d:A`;
                     `ring_of_int k A:A`]
       (RING_RULE
         `!k:A ring x a b D c.
             ring_pow k x 2 = D /\ ring_mul k (ring_of_num k 2) a = c
             ==> ring_sub k (ring_mul k (ring_pow k b 2) D) (ring_pow k a 2) =
                 ring_sub k (ring_pow k (ring_add k a (ring_mul k b x)) 2)
                   (ring_mul k c (ring_add k a (ring_mul k b x)))`)) THEN
      ASM_SIMP_TAC[RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(CONJUNCT1 RING_OF_INTEGERS_SUBRING) THEN
      DISCH_THEN(ASSUME_TAC o SPEC `k:A ring`) THEN
      ASM_SIMP_TAC[IN_SUBRING_SUB; IN_SUBRING_MUL; IN_SUBRING_POW;
                   RING_OF_INT_IN_RING_OF_INTEGERS];
      REWRITE_TAC[ring_sub] THEN
      REPEAT(FIRST[MATCH_MP_TAC RING_ADD_IN_SUBFIELD_GENERATED;
                   MATCH_MP_TAC RING_NEG_IN_SUBFIELD_GENERATED;
                   MATCH_MP_TAC RING_MUL_IN_SUBFIELD_GENERATED;
                   MATCH_MP_TAC RING_POW_IN_SUBFIELD_GENERATED; CONJ_TAC]) THEN
      ASM_REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `ring_mul k (ring_of_num k 2) b:A`; `d:int`;
                 `(&4 * U + A pow 2):int`]
    PRIME_SUBFIELD_SQUAREFREE_MUL_SQUARE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_IN_SUBFIELD_GENERATED; GSYM RING_OF_INT_OF_NUM;
                 RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
    REWRITE_TAC[RING_OF_INT_ADD; RING_OF_INT_MUL; RING_OF_INT_POW;
                RING_OF_INT_OF_NUM] THEN
    MP_TAC(ISPECL [`k:A ring`; `a:A`; `b:A`; `ring_of_int k d:A`;
                   `ring_of_int k A:A`; `ring_of_int k U:A`]
     (RING_RULE
       `!k:A ring a b D A' U'.
           ring_mul k (ring_of_num k 2) a = A' /\
           ring_sub k (ring_mul k (ring_pow k b 2) D) (ring_pow k a 2) = U'
           ==> ring_mul k D (ring_pow k (ring_mul k (ring_of_num k 2) b) 2) =
               ring_add k (ring_mul k (ring_of_num k 4) U')
                          (ring_pow k A' 2)`)) THEN
    ASM_SIMP_TAC[RING_OF_INT];
    DISCH_THEN(X_CHOOSE_THEN `B:int` STRIP_ASSUME_TAC)] THEN
  MAP_EVERY EXISTS_TAC [`A:int`; `B:int`; `--U:int`] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `x:A`; `a:A`; `b:A`; `ring_of_int k A:A`;
                   `ring_of_int k B:A`]
     (RING_RULE
       `!k:A ring x a b A' B'.
           ring_mul k (ring_of_num k 2) a = A' /\
           ring_mul k (ring_of_num k 2) b = B'
           ==> ring_mul k (ring_of_num k 2) (ring_add k a (ring_mul k b x)) =
               ring_add k A' (ring_mul k B' x)`)) THEN
    ASM_SIMP_TAC[RING_OF_INT];
    UNDISCH_TAC `&4 * U + A pow 2 = (d:int) * B pow 2` THEN INT_ARITH_TAC]);;

let QUADRATIC_FIELD_INTEGRAL_FREE_BASIS = prove
 (`!k:A ring w.
        number_field k /\
        w IN ring_carrier(ring_of_integers k) /\
        ~(w IN ring_carrier(subfield_generated k {ring_0 k})) /\
        (!z. z IN ring_carrier(ring_of_integers k)
             ==> ?a b. z = ring_add k (ring_of_int k a)
                                      (ring_mul k (ring_of_int k b) w))
        ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) 2
                       (\i. if i = 0 then ring_1 k else w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  SUBGOAL_THEN `(w:A) IN ring_carrier k /\
                ring_1 k IN ring_carrier(ring_of_integers k)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers k:A ring` RING_1) THEN
    MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(CONJUNCT2 RING_OF_INTEGERS_SUBRING)] THEN
  SIMP_TAC[FREE_BASIS_INTEGER_RING_SUBRING_GENERATED;
           RING_OF_INTEGERS_SUBRING] THEN
  ASM_REWRITE_TAC[FORALL_LT_2; ARITH_EQ] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP
     (ASSUME `(z:A) IN ring_carrier(ring_of_integers k)`)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `\i. if i = 0 then a else b:int` THEN
    ASM_SIMP_TAC[RING_SUM_LT_2; RING_MUL; RING_OF_INT; RING_1; ARITH_EQ;
                 RING_MUL_RID];
    X_GEN_TAC `c:num->int` THEN
    ASM_SIMP_TAC[RING_SUM_LT_2; RING_MUL; RING_OF_INT; RING_1; ARITH_EQ;
                 RING_MUL_RID] THEN
    MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`; `ring_of_int k (c 0):A`;
                   `ring_of_int k (c 1):A`; `w:A`]
      SUBFIELD_GENERATED_ADD_MUL_EQ_0) THEN
    ASM_SIMP_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED; RING_OF_INT_EQ_0_CHAR_0]]);;

let QUADRATIC_FIELD_INTEGRAL_BASIS_SQRT = prove
 (`!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ ~((d == &1) (mod &4))
        ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) 2
              (\i. if i = 0 then ring_1 k else x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(ring_of_num k 2:A = ring_0 k) /\ ~(&4 divides (d:int))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO; ARITH_EQ] THEN
    UNDISCH_TAC `squarefree(num_of_int(abs d))` THEN
    REWRITE_TAC[squarefree; INT_DIVIDES_NUM_OF_INT_ABS; INT_ABS_NUM;
                NUM_OF_INT_OF_NUM] THEN
    DISCH_THEN(MP_TAC o SPEC `2`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC QUADRATIC_FIELD_INTEGRAL_FREE_BASIS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN
    MAP_EVERY EXISTS_TAC [`&0:int`; `--d:int`] THEN
    ASM_SIMP_TAC[RING_OF_INT_0; RING_OF_INT_NEG; RING_MUL_LZERO;
                 RING_ADD_LZERO; RING_NEG; RING_OF_INT; RING_ADD_RNEG];
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `z:A`]
      QUADRATIC_FIELD_INTEGRAL_COORDINATES) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`A:int`; `B:int`; `N:int`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`d:int`; `A:int`; `B:int`; `N:int`]
      INT_SQUARE_SUB_MUL_SQUARE_MOD_4) THEN
    ASM_REWRITE_TAC[int_divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:int` SUBST_ALL_TAC)
                               (X_CHOOSE_THEN `b:int` SUBST_ALL_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`a:int`; `b:int`] THEN
    SUBGOAL_THEN `(z:A) IN ring_carrier k` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET]
       (ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_of_num k 2:A`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_OF_NUM; RING_ADD; RING_MUL;
                 RING_OF_INT] THEN
    UNDISCH_TAC
     `ring_mul k (ring_of_num k 2) z =
      ring_add k (ring_of_int k (&2 * a))
                 (ring_mul k (ring_of_int k (&2 * b)) x):A` THEN
    REWRITE_TAC[RING_OF_INT_MUL; RING_OF_INT_OF_NUM] THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `x:A`; `ring_of_int k a:A`;
                   `ring_of_int k b:A`]
     (RING_RULE
       `!k:A ring z x a b.
           ring_mul k (ring_of_num k 2) z =
           ring_add k (ring_mul k (ring_of_num k 2) a)
                      (ring_mul k (ring_mul k (ring_of_num k 2) b) x)
           ==> ring_mul k (ring_of_num k 2) z =
               ring_mul k (ring_of_num k 2)
                 (ring_add k a (ring_mul k b x))`)) THEN
    ASM_SIMP_TAC[RING_OF_INT]]);;

let QUADRATIC_FIELD_INTEGRAL_BASIS_HALF = prove
 (`!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ (d == &1) (mod &4)
        ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) 2
              (\i. if i = 0 then ring_1 k
                   else ring_div k (ring_add k (ring_1 k) x)
                                   (ring_of_num k 2))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(ring_of_num k 2:A = ring_0 k) /\ ~(&4 divides (d:int))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO; ARITH_EQ] THEN
    UNDISCH_TAC `squarefree(num_of_int(abs d))` THEN
    REWRITE_TAC[squarefree; INT_DIVIDES_NUM_OF_INT_ABS; INT_ABS_NUM;
                NUM_OF_INT_OF_NUM] THEN
    DISCH_THEN(MP_TAC o SPEC `2`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC QUADRATIC_FIELD_INTEGRAL_FREE_BASIS THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`; `x:A`]
    SUBFIELD_GENERATED_HALF_SUCC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `((d:int) == &1) (mod &4)` THEN
    REWRITE_TAC[int_congruent] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:int` (SUBST_ALL_TAC o MATCH_MP
     (INT_ARITH `(d:int) - &1 = &4 * t ==> d = &1 + &4 * t`))) THEN
    REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN
    MAP_EVERY EXISTS_TAC [`--(&1):int`; `--t:int`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_of_num k 4:A`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_OF_NUM; RING_OF_NUM_EQ_0;
                 DIVIDES_ZERO; ARITH_EQ; RING_0; RING_ADD; RING_POW;
                 RING_MUL; RING_OF_INT] THEN
    UNDISCH_TAC `ring_pow k x 2 = ring_of_int k (&1 + &4 * t):A` THEN
    REWRITE_TAC[RING_OF_INT_NEG; RING_OF_INT_ADD; RING_OF_INT_MUL;
                RING_OF_INT_OF_NUM] THEN
    MP_TAC(ISPECL [`k:A ring`; `w:A`; `x:A`; `ring_of_int k t:A`]
     (RING_RULE
       `!k:A ring w x T.
           ring_mul k (ring_of_num k 2) w = ring_add k (ring_1 k) x
           ==> ring_pow k x 2 =
               ring_add k (ring_of_num k 1) (ring_mul k (ring_of_num k 4) T)
           ==> ring_mul k (ring_of_num k 4)
                (ring_add k (ring_pow k w 2)
                   (ring_add k (ring_mul k (ring_neg k (ring_of_num k 1)) w)
                               (ring_neg k T))) =
               ring_mul k (ring_of_num k 4) (ring_0 k)`)) THEN
    ASM_SIMP_TAC[RING_OF_INT];
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `z:A`]
      QUADRATIC_FIELD_INTEGRAL_COORDINATES) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`A:int`; `B:int`; `N:int`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`d:int`; `A:int`; `B:int`; `N:int`]
      INT_SQUARE_SUB_MUL_SQUARE_MOD_4) THEN
    ASM_REWRITE_TAC[int_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:int` (SUBST_ALL_TAC o MATCH_MP
     (INT_ARITH `A - B = &2 * c ==> A = &2 * c + B:int`))) THEN
    MAP_EVERY EXISTS_TAC [`c:int`; `B:int`] THEN
    SUBGOAL_THEN `(z:A) IN ring_carrier k` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET]
       (ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_of_num k 2:A`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_OF_NUM; RING_ADD; RING_MUL;
                 RING_OF_INT] THEN
    UNDISCH_TAC
     `ring_mul k (ring_of_num k 2) z =
      ring_add k (ring_of_int k (&2 * c + B))
                 (ring_mul k (ring_of_int k B) x):A` THEN
    REWRITE_TAC[RING_OF_INT_ADD; RING_OF_INT_MUL; RING_OF_INT_OF_NUM] THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `w:A`; `x:A`; `ring_of_int k c:A`;
                   `ring_of_int k B:A`]
     (RING_RULE
       `!k:A ring z w x C B.
           ring_mul k (ring_of_num k 2) w = ring_add k (ring_1 k) x
           ==> ring_mul k (ring_of_num k 2) z =
               ring_add k (ring_add k (ring_mul k (ring_of_num k 2) C) B)
                          (ring_mul k B x)
           ==> ring_mul k (ring_of_num k 2) z =
               ring_mul k (ring_of_num k 2)
                 (ring_add k C (ring_mul k B w))`)) THEN
    ASM_SIMP_TAC[RING_OF_INT]]);;

let QUADRATIC_FIELD_INTEGRAL_BASIS = prove
 (`!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1)
        ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) 2
              (\i. if i = 0 then ring_1 k
                   else if (d == &1) (mod &4)
                        then ring_div k (ring_add k (ring_1 k) x)
                                        (ring_of_num k 2)
                        else x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN
  FIRST[MATCH_MP_TAC QUADRATIC_FIELD_INTEGRAL_BASIS_HALF;
        MATCH_MP_TAC QUADRATIC_FIELD_INTEGRAL_BASIS_SQRT] THEN
  EXISTS_TAC `d:int` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The discriminant.                                                         *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_BASIS_DISCRIMINANT = prove
 (`!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d
        ==> basis_discriminant (subfield_generated k {ring_0 k},k) I 2
              (\i. if i = 0 then ring_1 k else x) =
            ring_of_int k (&4 * d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. a IN ring_carrier(subfield_generated k {ring_0 k}) /\
          b IN ring_carrier(subfield_generated k {ring_0 k})
          ==> algebra_trace (subfield_generated k {ring_0 k},k) (I:A->A)
                (ring_add k a (ring_mul k b x)) =
              ring_mul k (ring_of_num k 2) a`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`]
      RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th ->
      MP_TAC(SPEC `a:A` th) THEN MP_TAC(SPEC `b:A` th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `a:A`; `b:A`] QUADRATIC_FIELD_TRACE) THEN
    ASM_SIMP_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `algebra_trace (subfield_generated k {ring_0 k},k)
      (I:A->A) (ring_1 k) = ring_of_num k 2 /\
    algebra_trace (subfield_generated k {ring_0 k},k) (I:A->A) x = ring_0 k /\
    algebra_trace (subfield_generated k {ring_0 k},k)
      (I:A->A) (ring_of_int k d) =
    ring_mul k (ring_of_num k 2) (ring_of_int k d)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`ring_1 k:A`; `ring_0 k:A`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`ring_0 k:A`; `ring_1 k:A`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`ring_of_int k d:A`; `ring_0 k:A`])] THEN
    ASM_SIMP_TAC[RING_0_IN_SUBFIELD_GENERATED; RING_1_IN_SUBFIELD_GENERATED;
                 RING_OF_INT_IN_SUBFIELD_GENERATED; RING_MUL_LZERO;
                 RING_MUL_LID; RING_ADD_RZERO; RING_ADD_LZERO; RING_1;
                 RING_OF_INT; RING_MUL_RID; RING_OF_NUM; RING_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[basis_discriminant] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_DIAGONAL o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_LT_2; ARITH_EQ] THEN
  ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_RID; RING_1; SUBFIELD_GENERATED] THEN
  DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_LT_2 o lhand o snd) THEN
  REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RING_MUL_LID; RING_1; GSYM RING_POW_2; SUBFIELD_GENERATED;
               ARITH_EQ] THEN
  REWRITE_TAC[RING_OF_INT_MUL; RING_OF_INT_OF_NUM] THEN
  ASM_SIMP_TAC[RING_OF_INT; RING_RULE
   `ring_mul (k:A ring) (ring_of_num k 2) (ring_mul k (ring_of_num k 2) D) =
    ring_mul k (ring_of_num k 4) D`]);;

let QUADRATIC_FIELD_BASIS_DISCRIMINANT_HALF = prove
 (`!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d
        ==> basis_discriminant (subfield_generated k {ring_0 k},k) I 2
              (\i. if i = 0 then ring_1 k
                   else ring_div k (ring_add k (ring_1 k) x)
                                   (ring_of_num k 2)) =
            ring_of_int k d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  SUBGOAL_THEN `~(ring_of_num k 2:A = ring_0 k)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO; ARITH_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`; `x:A`]
    SUBFIELD_GENERATED_HALF_SUCC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A` THEN
  STRIP_TAC THEN
  ABBREV_TAC `h = ring_inv k (ring_of_num k 2):A` THEN
  SUBGOAL_THEN
   `h IN ring_carrier(subfield_generated k {ring_0 k}) /\
    h IN ring_carrier k /\ ring_mul k (ring_of_num k 2) h = ring_1 k:A`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[GSYM RING_OF_INT_OF_NUM] THEN
    ASM_SIMP_TAC[RING_INV_IN_SUBFIELD_GENERATED; FIELD_SUBFIELD_GENERATED;
                 RING_INV; RING_OF_INT; FIELD_MUL_RINV; RING_OF_INT_OF_NUM;
                 RING_OF_INT_IN_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`; `2`;
    `\i. if i = 0 then ring_1 k else x:A`;
    `\i. if i = 0 then ring_1 k else w:A`;
    `\i j. if i = 0 then (if j = 0 then ring_1 k else ring_0 k) else h:A`]
   BASIS_DISCRIMINANT_CHANGE_OF_BASIS) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
               QUADRATIC_FIELD_FREE_BASIS;
               QUADRATIC_FIELD_BASIS_DISCRIMINANT] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_LT_2; ARITH_EQ;
                I_THM] THEN
    ASM_SIMP_TAC[RING_SUM_LT_2; RING_0_IN_SUBFIELD_GENERATED;
                 RING_1_IN_SUBFIELD_GENERATED; RING_MUL; RING_1; RING_0;
                 ARITH_EQ; RING_MUL_LID; RING_MUL_LZERO; RING_ADD_RZERO] THEN
    MP_TAC(ISPECL [`k:A ring`; `h:A`; `w:A`]
     (RING_RULE
       `!k:A ring h w.
           ring_mul k (ring_of_num k 2) h = ring_1 k
           ==> w = ring_mul k h (ring_mul k (ring_of_num k 2) w)`)) THEN
    ASM_SIMP_TAC[RING_ADD_LDISTRIB; RING_1];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `ring_det (subfield_generated k {ring_0 k}) {i | i < 2}
      (\i j. if i = 0 then if j = 0 then ring_1 k else ring_0 k else h) =
    h:A`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_LOWERTRIANGULAR o
      lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ANTS_TAC THENL
     [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_LT_2; ARITH] THEN
      REWRITE_TAC[SUBFIELD_GENERATED];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_LT_2 o lhand o snd) THEN
    ASM_REWRITE_TAC[ARITH_EQ; RING_1_IN_SUBFIELD_GENERATED] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[SUBFIELD_GENERATED; RING_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[SUBFIELD_GENERATED; RING_POW_SUBFIELD_GENERATED;
              RING_OF_INT_MUL; RING_OF_INT_OF_NUM] THEN
  MP_TAC(ISPECL [`k:A ring`; `h:A`; `ring_of_int k d:A`]
   (RING_RULE
     `!k:A ring h D.
         ring_mul k (ring_of_num k 2) h = ring_1 k
         ==> ring_mul k (ring_pow k h 2) (ring_mul k (ring_of_num k 4) D) =
             D`)) THEN
  ASM_SIMP_TAC[RING_OF_INT]);;

let QUADRATIC_FIELD_DISCRIMINANT = prove
 (`!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1)
        ==> number_field_discriminant k =
            if (d == &1) (mod &4) then d else &4 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:A ring`; `x:A`; `d:int`] QUADRATIC_FIELD_INTEGRAL_BASIS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME `number_field(k:A ring)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[QUADRATIC_FIELD_BASIS_DISCRIMINANT;
               QUADRATIC_FIELD_BASIS_DISCRIMINANT_HALF;
               RING_OF_INT_EQ_CHAR_0]);;
