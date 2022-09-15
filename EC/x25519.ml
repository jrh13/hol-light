(* ========================================================================= *)
(* The x25519 function, and curve25519 over extensions of the prime field.   *)
(* ========================================================================= *)

needs "EC/curve25519.ml";;
needs "EC/xzprojective.ml";;

(* ------------------------------------------------------------------------- *)
(* The generalization of curve25519 to any field.                            *)
(* ------------------------------------------------------------------------- *)

let curve25519x = define
 `curve25519x (f:A ring) = (f,ring_of_num f A_25519,ring_of_num f 1)`;;

let curve25519x_curve25519 = prove
 (`curve25519x (integer_mod_ring p_25519) = curve25519`,
  REWRITE_TAC[curve25519; curve25519x; PAIR_EQ; p_25519; A_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Nonsingularity, in particular over extensions of curve25519 prime field.  *)
(* ------------------------------------------------------------------------- *)

let MONTGOMERY_NONSINGULAR_CURVE25519X_GEN = prove
 (`!f:A ring.
        field f /\
        ~(ring_char f divides 14802493890)
        ==> montgomery_nonsingular(curve25519x f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[montgomery_nonsingular; curve25519x] THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_OF_NUM; INTEGRAL_DOMAIN_RULE
   `ring_pow f x 2 = ring_of_num f 4 <=>
    x = ring_of_num f 2 \/ x = ring_neg f (ring_of_num f 2)`] THEN
  REWRITE_TAC[GSYM RING_OF_INT_NEG; GSYM RING_OF_INT_OF_NUM] THEN
  REWRITE_TAC[RING_OF_INT_EQ; RING_OF_INT_EQ_0] THEN REWRITE_TAC[INT_CONG] THEN
  REWRITE_TAC[A_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM num_divides; DIVIDES_ONE] THEN POP_ASSUM MP_TAC THEN
  POP_ASSUM(MP_TAC o MATCH_MP INTEGRAL_DOMAIN_CHAR o
        MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SPEC_TAC(`ring_char (f:A ring)`,`p:num`) THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  CONV_TAC(DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MESON[PRIME_1] `prime p ==> ~(p = 1)`] THEN
  REWRITE_TAC[ARITH_RULE `14802493890 = 2 * 3 * 5 * 127 * 479 * 8111`;
              ARITH_RULE `486660 = 2 EXP 2 * 3 * 5 * 8111`;
              ARITH_RULE `486664 = 2 EXP 3 * 127 * 479`] THEN
  ASM_SIMP_TAC[PRIME_DIVPROD_EQ; PRIME_DIVEXP_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN CONV_TAC TAUT);;

let MONTGOMERY_NONSINGULAR_CURVE25519X = prove
 (`!f:A ring.
        field f /\ ring_char f = p_25519
        ==> montgomery_nonsingular(curve25519x f)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MONTGOMERY_NONSINGULAR_CURVE25519X_GEN THEN
  ASM_REWRITE_TAC[p_25519] THEN
  CONV_TAC(DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* We don't have strong nonsingularity in general but we do have this        *)
(* analogous property for an X coordinate belonging to the prime (sub)field. *)
(* ------------------------------------------------------------------------- *)

let SPECIALLY_NONSINGULAR_CURVE25519X = prove
 (`!f X y:A.
        field f /\ ring_char f = p_25519 /\
        montgomery_curve (curve25519x f) (SOME(ring_of_num f X,y))
        ==> (y = ring_0 f <=> ring_of_num f X = ring_0 f)`,
  let lemma = prove
   (`!f:A ring.
          field f /\
          A IN ring_carrier f /\
          x IN ring_carrier f /\
          y IN ring_carrier f /\
          ~(ring_pow f (ring_add f (ring_mul f (ring_of_num f 2) x) A) 2 =
            ring_sub f (ring_pow f A 2) (ring_of_num f 4))
          ==> ring_mul f (ring_1 f) (ring_pow f y 2) =
              ring_add f (ring_pow f x 3)
              (ring_add f (ring_mul f A (ring_pow f x 2)) x)
          ==> (y = ring_0 f <=> x = ring_0 f)`,
    FIELD_TAC) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[montgomery_curve; curve25519x; RING_OF_NUM_1] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[RING_OF_NUM] THEN
  REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT_CLAUSES] THEN
  ASM_REWRITE_TAC[RING_OF_INT_EQ; A_25519; p_25519] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM num_congruent; INT_OF_NUM_CLAUSES] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `(z EXP 2 == a) (mod p) ==> ?x:num. (x EXP 2 == a) (mod p)`)) THEN
  SIMP_TAC[EULER_CRITERION; REWRITE_RULE[p_25519] PRIME_P25519] THEN
  CONV_TAC(DEPTH_CONV
   (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Definition of the curve group over the general field.                     *)
(* ------------------------------------------------------------------------- *)

let curve25519x_group = define
 `curve25519x_group (f:A ring) = montgomery_group(curve25519x f)`;;

let CURVE25519X_CURVE25519_GROUP = prove
 (`curve25519x_group (integer_mod_ring p_25519) = curve25519_group`,
  REWRITE_TAC[curve25519_group; curve25519x_group; curve25519x] THEN
  REWRITE_TAC[p_25519; A_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN REWRITE_TAC[]);;

let CURVE25519X_GROUP_GEN = prove
 (`!f:A ring.
        field f /\ ~(ring_char f divides 14802493890)
        ==> group_carrier (curve25519x_group f) =
              montgomery_curve (curve25519x f) /\
            group_id (curve25519x_group f) =
              NONE /\
            group_inv (curve25519x_group f) =
              montgomery_neg (curve25519x f) /\
            group_mul (curve25519x_group f) =
              montgomery_add (curve25519x f)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[curve25519x_group; curve25519x] THEN
  MATCH_MP_TAC MONTGOMERY_GROUP THEN ASM_REWRITE_TAC[RING_OF_NUM] THEN
  REWRITE_TAC[GSYM curve25519x] THEN
  ASM_SIMP_TAC[MONTGOMERY_NONSINGULAR_CURVE25519X_GEN] THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC[CONTRAPOS_THM] THEN
  CONV_TAC(DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[]);;

let CURVE25519X_GROUP = prove
 (`!f:A ring.
        field f /\ ring_char f = p_25519
        ==> group_carrier (curve25519x_group f) =
              montgomery_curve (curve25519x f) /\
            group_id (curve25519x_group f) =
              NONE /\
            group_inv (curve25519x_group f) =
              montgomery_neg (curve25519x f) /\
            group_mul (curve25519x_group f) =
              montgomery_add (curve25519x f)`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CURVE25519X_GROUP_GEN THEN
  ASM_REWRITE_TAC[p_25519] THEN
  CONV_TAC(DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[]);;

let GROUP_POW_CURVE25519X_TORSION = prove
 (`!(f:A ring) n.
        field f /\ ring_char f = p_25519
        ==> group_pow (curve25519x_group f) (SOME(ring_0 f,ring_0 f)) n =
            if EVEN n then NONE else SOME(ring_0 f,ring_0 f)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[group_pow; EVEN; CURVE25519X_GROUP; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[montgomery_add; curve25519x]);;

(* ------------------------------------------------------------------------- *)
(* Construction of quadratic extension (Z/p_25519)/sqrt(2) as used           *)
(* in Bernstein's original https://cr.yp.to/ecdh/curve25519-20060209.pdf;    *)
(* this proceeds via a slightly more general quadratic_extension (which      *)
(* could be further subsumed by a general algebraic extension construction). *)
(* ------------------------------------------------------------------------- *)

let quadratic_extension = new_definition
 `quadratic_extension (r:A ring) a =
        ring((ring_carrier r CROSS ring_carrier r),
             (ring_0 r,ring_0 r),
             (ring_1 r,ring_0 r),
             (\(x,y). ring_neg r x,ring_neg r y),
             (\(x1,y1) (x2,y2). ring_add r x1 x2,ring_add r y1 y2),
             (\(x1,y1) (x2,y2).
                ring_add r (ring_mul r x1 x2)
                           (ring_mul r (ring_of_num r a) (ring_mul r y1 y2)),
                ring_add r (ring_mul r x1 y2) (ring_mul r x2 y1)))`;;

let QUADRATIC_EXTENSION = prove
 (`(!(r:A ring) a. ring_carrier(quadratic_extension r a) =
                   ring_carrier r CROSS ring_carrier r) /\
   (!(r:A ring) a. ring_0 (quadratic_extension r a) =
                   (ring_0 r,ring_0 r)) /\
   (!(r:A ring) a. ring_1 (quadratic_extension r a) =
                   (ring_1 r,ring_0 r)) /\
   (!(r:A ring) a. ring_neg (quadratic_extension r a) =
                   \(x,y). ring_neg r x,ring_neg r y) /\
   (!(r:A ring) a. ring_add (quadratic_extension r a) =
                   \(x1,y1) (x2,y2). ring_add r x1 x2,ring_add r y1 y2) /\
   (!(r:A ring) a. ring_mul (quadratic_extension r a) =
                   \(x1,y1) (x2,y2).
                     ring_add r (ring_mul r x1 x2)
                                (ring_mul r (ring_of_num r a)
                                            (ring_mul r y1 y2)),
                     ring_add r (ring_mul r x1 y2) (ring_mul r x2 y1))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl quadratic_extension)))))
   (CONJUNCT2 ring_tybij)))) THEN
  REWRITE_TAC[GSYM quadratic_extension] THEN ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN RING_TAC;
    DISCH_TAC THEN
    ASM_REWRITE_TAC[ring_carrier; ring_0; ring_1; ring_neg;
                    ring_add; ring_mul]]);;

let RING_HOMOMORPHISM_INTO_QUADRATIC_EXTENSION = prove
 (`!(r:A ring) a.
    ring_homomorphism (r,quadratic_extension r a) (\x. (x,ring_0 r))`,
  REWRITE_TAC[RING_HOMOMORPHISM; QUADRATIC_EXTENSION; PAIR_EQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN RING_TAC);;

let RING_MONOMORPHISM_INTO_QUADRATIC_EXTENSION = prove
 (`!(r:A ring) a.
    ring_monomorphism (r,quadratic_extension r a) (\x. (x,ring_0 r))`,
  REWRITE_TAC[RING_MONOMORPHISM_ALT] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_INTO_QUADRATIC_EXTENSION] THEN
  SIMP_TAC[QUADRATIC_EXTENSION; PAIR_EQ]);;

let RING_OF_NUM_QUADRATIC_EXTENSION = prove
 (`!(r:A ring) a n.
        ring_of_num (quadratic_extension r a) n = (ring_of_num r n,ring_0 r)`,
  GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_of_num; QUADRATIC_EXTENSION] THEN
  REWRITE_TAC[PAIR_EQ] THEN RING_TAC);;

let RING_OF_INT_QUADRATIC_EXTENSION = prove
 (`!(r:A ring) a n.
        ring_of_int (quadratic_extension r a) n = (ring_of_int r n,ring_0 r)`,
  REWRITE_TAC[FORALL_INT_CASES; RING_OF_INT_NEG; RING_OF_INT_OF_NUM] THEN
  REWRITE_TAC[RING_OF_NUM_QUADRATIC_EXTENSION; QUADRATIC_EXTENSION] THEN
  REWRITE_TAC[RING_NEG_0]);;

let RING_CHAR_QUADRATIC_EXTENSION = prove
 (`!(r:A ring) a. ring_char (quadratic_extension r a) = ring_char r`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC RING_CHAR_MONOMORPHIC_IMAGE THEN
  MESON_TAC[RING_MONOMORPHISM_INTO_QUADRATIC_EXTENSION]);;

let FIELD_QUADRATIC_EXTENSION = prove
 (`!(r:A ring) a.
        field r /\
        (!d. d IN ring_carrier r ==> ~(ring_pow r d 2 = ring_of_num r a))
        ==> field(quadratic_extension r a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[field; QUADRATIC_EXTENSION] THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
  ASM_SIMP_TAC[FIELD_NONTRIVIAL] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  ABBREV_TAC `d:A = ring_sub r (ring_pow r x 2)
                               (ring_mul r (ring_of_num r a)
                                           (ring_pow r y 2))` THEN
  SUBGOAL_THEN `~(d:A = ring_0 r)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `ring_div r x y:A`) THEN
    ASM_SIMP_TAC[RING_DIV] THEN
    POP_ASSUM(SUBST_ALL_TAC o SYM) THEN FIELD_TAC;
    MAP_EVERY EXISTS_TAC
     [`ring_div r x d:A`; `ring_div r (ring_neg r y) d:A`] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
    FIRST_X_ASSUM(K ALL_TAC o SPEC `x:A`) THEN FIELD_TAC]);;

let sqintmod_field = new_definition
 `sqintmod_field = quadratic_extension (integer_mod_ring p_25519) 2`;;

let FIELD_SQINTMOD_FIELD = prove
 (`field sqintmod_field`,
  REWRITE_TAC[sqintmod_field] THEN MATCH_MP_TAC FIELD_QUADRATIC_EXTENSION THEN
  REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`; GSYM NOT_EXISTS_THM] THEN
  REWRITE_TAC[INTEGER_MOD_RING_ROOT_EXISTS] THEN
  REWRITE_TAC[el 9 (CONJUNCTS INTEGER_MOD_RING_CLAUSES)] THEN
  REWRITE_TAC[INT_OF_NUM_REM; INTEGER_MOD_RING_ROOT_EXISTS] THEN
  SIMP_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519; EULER_CRITERION] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SIMP_TAC[p_25519; MOD_LT; ARITH_LE; ARITH_LT] THEN
  CONV_TAC(DEPTH_CONV
   (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let RING_CHAR_SQINTMOD_FIELD = prove
 (`ring_char sqintmod_field = p_25519`,
  REWRITE_TAC[sqintmod_field; RING_CHAR_QUADRATIC_EXTENSION] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CHAR]);;

let SQUARE_ROOTS_SQINTMOD_FIELD = prove
 (`!n. ?x. x IN ring_carrier sqintmod_field /\
           ring_pow sqintmod_field x 2 = ring_of_num sqintmod_field n`,
  let lemma = prove
   (`!a. ?x. (x EXP 2 == a) (mod p_25519) \/ (x EXP 2 == 2 * a) (mod p_25519)`,
    SIMP_TAC[EXISTS_OR_THM; EULER_CRITERION;
             PRIME_P25519; PRIME_DIVPROD_EQ] THEN
    GEN_TAC THEN
    MP_TAC(SPECL [`p_25519`; `1`; `a EXP ((p_25519 - 1) DIV 2)`]
      CONG_SQUARE_1_PRIME_POWER) THEN
    MP_TAC(ONCE_REWRITE_RULE[COPRIME_SYM]
     (SPECL [`a:num`; `p_25519`] FERMAT_LITTLE_PRIME)) THEN
    MP_TAC(SPECL [`p_25519`; `a:num`] PRIME_COPRIME_EQ) THEN
    REWRITE_TAC[PRIME_P25519] THEN
    ASM_CASES_TAC `p_25519 divides a` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[EXP_1; EXP_EXP] THEN DISCH_TAC THEN
    ANTS_TAC THENL [REWRITE_TAC[p_25519; ARITH_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `(p_25519 - 1) DIV 2 * 2 = p_25519 - 1` SUBST1_TAC THENL
     [REWRITE_TAC[p_25519] THEN ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(TAUT `(q ==> q') ==> p \/ q ==> p \/ r \/ q'`) THEN
    REWRITE_TAC[MULT_EXP; CONG] THEN ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC(DEPTH_CONV
     (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV) in
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  SIMP_TAC[RING_POW_2] THEN REWRITE_TAC[NOT_IMP] THEN
  REWRITE_TAC[sqintmod_field; QUADRATIC_EXTENSION] THEN
  REWRITE_TAC[RING_OF_NUM_QUADRATIC_EXTENSION; EXISTS_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER; INTEGER_MOD_RING_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!p. (?x y. P (&x rem p) (&y rem p)) ==> (?x y. P x y)`) THEN
  EXISTS_TAC `&p_25519:int` THEN REWRITE_TAC[INT_LT_REM_EQ; PAIR_EQ] THEN
  SIMP_TAC[INT_ARITH `~(&p:int < &0)`; INT_POS; INT_REM_POS_EQ] THEN
  REWRITE_TAC[INT_ARITH `&p:int = &0 \/ &0:int < &p`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  MP_TAC(SPEC `n:num` lemma) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`m:num`; `0`];
    MAP_EVERY EXISTS_TAC [`0`; `m * inverse_mod p_25519 2`]] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; MOD_0] THEN
  ASM_REWRITE_TAC[GSYM EXP_2; GSYM CONG] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(m EXP 2 == t * n) (mod p) /\ (t * i == 1) (mod p)
    ==> (t * (m * i) EXP 2 == n) (mod p)`) THEN
  ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC COPRIME_CONV);;

(* ------------------------------------------------------------------------- *)
(* An explicitly computational definition of the pure x25519 function as     *)
(* "purex25519_def" and then an equivalent "purex25519" corresponding to the *)
(* way Bernstein defines it in https://cr.yp.to/ecdh/curve25519-20060209.pdf *)
(* Theorem 2.1. The "pure" means it does not prenormalize n and q, although  *)
(* it does automatically/implicitly reduce the q input modulo p_25519.       *)
(* ------------------------------------------------------------------------- *)

let x25519_ladderstep = define
 `x25519_ladderstep b P (P0,P1) =
        if b then (montgomery_xzdiffadd curve25519 P P1 P0,
                   montgomery_xzdouble curve25519 P1)
        else (montgomery_xzdouble curve25519 P0,
              montgomery_xzdiffadd curve25519 P P1 P0)`;;

let x25519_ladder = define
 `x25519_ladder n P =
    if n = 0 then ((&1,&0),P)
    else x25519_ladderstep (n MOD 2 = 1) P (x25519_ladder (n DIV 2) P)`;;

let purex25519_def = define
 `purex25519(n,q) =
        if q MOD p_25519 = 0 then 0 else
        let (X,Z) = FST(x25519_ladder n (&q,&1)) in
        let x = num_of_int(X rem &p_25519)
        and z = num_of_int(Z rem &p_25519) in
        if z = 0 then 0 else
        (x * inverse_mod p_25519 z) MOD p_25519`;;

let PUREX25519_LADDER = prove
 (`!(f:A ring) x y n.
        field f /\ ring_char f = p_25519 /\
        SOME(ring_of_num f x,y) IN group_carrier (curve25519x_group f) /\
        ~(ring_of_num f x = ring_0 f)
        ==> let (X,Z),(X',Z') = x25519_ladder n (&x,&1) in
            montgomery_xz f (group_pow (curve25519x_group f)
                                       (SOME(ring_of_num f x,y)) n)
                            (ring_of_int f X,ring_of_int f Z) /\
            montgomery_xz f (group_pow (curve25519x_group f)
                                       (SOME(ring_of_num f x,y)) (n+1))
                            (ring_of_int f X',ring_of_int f Z')`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[x25519_ladder] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[group_pow; GROUP_POW_1; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[CURVE25519X_GROUP] THEN
    CONV_TAC let_CONV THEN REWRITE_TAC[montgomery_xz] THEN
    REWRITE_TAC[RING_OF_INT] THEN
    REWRITE_TAC[GSYM RING_OF_INT_CLAUSES] THEN
    ASM_SIMP_TAC[FIELD_NONTRIVIAL; RING_DIV_1; RING_OF_INT] THEN
    REWRITE_TAC[RING_OF_INT_OF_NUM];
    FIRST_X_ASSUM(MP_TAC o SPEC `n DIV 2`)] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n DIV 2 < n <=> ~(n = 0)`] THEN
  ABBREV_TAC `P = x25519_ladder (n DIV 2) (&x,&1)` THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`P:(int#int)#(int#int)`,`P:(int#int)#(int#int)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`Xn:int`; `Zn:int`; `Xm:int`; `Zm:int`] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV let_CONV)) THEN
  ABBREV_TAC `m = n DIV 2` THEN
  ABBREV_TAC `b = n MOD 2` THEN
  SUBGOAL_THEN `n = 2 * m + b` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "b"] THEN ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN
   `montgomery_xz (f:A ring)
                  (SOME (ring_of_num f x,y)) (ring_of_num f x,ring_1 f)`
  ASSUME_TAC THENL
   [REWRITE_TAC[montgomery_xz] THEN
    ASM_SIMP_TAC[RING_DIV_1; RING_OF_NUM; RING_1; FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `n MOD 2 = b ==> b = 1 \/ b = 0`)) THEN
  REWRITE_TAC[ARITH_EQ; x25519_ladderstep] THEN LET_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:A ring`; `ring_of_num f A_25519:A`; `ring_of_num f 1:A`;
                   `SOME(ring_of_num f x,y):(A#A)option`; `m:num`;
                   `(ring_of_num f x:A,ring_1 f)`;
                   `ring_of_int f Xm:A,ring_of_int f Zm`;
                   `ring_of_int f Xn:A,ring_of_int f Zn`]
        MONTGOMERY_XZDIFFADD_GROUP);
    MP_TAC(ISPECL [`f:A ring`; `ring_of_num f A_25519:A`; `ring_of_num f 1:A`;
                   `SOME(ring_of_num f x,y):(A#A)option`; `m + 1`;
                   `ring_of_int f Xm:A,ring_of_int f Zm`]
        MONTGOMERY_XZDOUBLE_GROUP) THEN
    REWRITE_TAC[ARITH_RULE `2 * (m + 1) = (2 * m + 1) + 1`];
    MP_TAC(ISPECL [`f:A ring`; `ring_of_num f A_25519:A`; `ring_of_num f 1:A`;
                   `SOME(ring_of_num f x,y):(A#A)option`; `m:num`;
                   `ring_of_int f Xn:A,ring_of_int f Zn`]
        MONTGOMERY_XZDOUBLE_GROUP) THEN
    REWRITE_TAC[ADD_CLAUSES];
    MP_TAC(ISPECL [`f:A ring`; `ring_of_num f A_25519:A`; `ring_of_num f 1:A`;
                   `SOME(ring_of_num f x,y):(A#A)option`; `m:num`;
                   `(ring_of_num f x:A,ring_1 f)`;
                   `ring_of_int f Xm:A,ring_of_int f Zm`;
                   `ring_of_int f Xn:A,ring_of_int f Zn`]
        MONTGOMERY_XZDIFFADD_GROUP) THEN
    REWRITE_TAC[ADD_CLAUSES]] THEN
  ASM_REWRITE_TAC[GSYM curve25519x; GSYM curve25519x_group] THEN
  ASM_SIMP_TAC[MONTGOMERY_NONSINGULAR_CURVE25519X] THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[RING_OF_NUM; FIELD_NONTRIVIAL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PAIR_EQ]) THEN
  REWRITE_TAC[montgomery_xzdiffadd; montgomery_xzdouble;
              curve25519; curve25519x] THEN
  REWRITE_TAC[PAIR_EQ; GSYM curve25519; curve25519x] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[RING_OF_INT_CLAUSES; GSYM RING_OF_INT_OF_NUM] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; RING_OF_INT_EQ] THEN
  ASM_REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  ASM_REWRITE_TAC[]);;

let PUREX25519_BOUND = prove
 (`!n q. purex25519(n,q) < p_25519`,
  REPEAT GEN_TAC THEN REWRITE_TAC[purex25519_def] THEN LET_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ_LT; p_25519] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let PUREX25519 = prove
 (`!(f:A ring) n q Q.
        field f /\ ring_char f = p_25519 /\
        Q IN group_carrier(curve25519x_group f) /\
        montgomery_xmap f Q = ring_of_num f q
        ==> montgomery_xmap f (group_pow (curve25519x_group f) Q n) =
            ring_of_num f (purex25519(n,q))`,
  MAP_EVERY X_GEN_TAC [`f:A ring`; `n:num`; `q:num`] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN CONJ_TAC THENL
   [SIMP_TAC[GSYM CURVE25519X_GROUP; GROUP_POW_ID; IMP_CONJ] THEN
    SIMP_TAC[CURVE25519X_GROUP; purex25519_def; montgomery_xmap] THEN
    REPLICATE_TAC 3 DISCH_TAC THEN DISCH_THEN(MP_TAC o SYM) THEN
    ASM_SIMP_TAC[RING_OF_NUM_EQ_0; DIVIDES_MOD; RING_OF_NUM_0];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`]] THEN
  ASM_CASES_TAC `ring_of_num f q:A = ring_0 f` THENL
   [ASM_REWRITE_TAC[montgomery_xmap] THEN STRIP_TAC THEN
    UNDISCH_THEN `x:A = ring_0 f` SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`f:A ring`; `0`; `y:A`]
       SPECIALLY_NONSINGULAR_CURVE25519X) THEN
    ASM_REWRITE_TAC[RING_OF_NUM_0] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CURVE25519X_GROUP; IN]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`f:A ring`; `n:num`]
        GROUP_POW_CURVE25519X_TORSION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [RING_OF_NUM_EQ_0]) THEN
    ASM_SIMP_TAC[DIVIDES_MOD; purex25519_def; RING_OF_NUM_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[montgomery_xmap];
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [montgomery_xmap]) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [RING_OF_NUM_EQ_0]) THEN
  ASM_SIMP_TAC[DIVIDES_MOD; purex25519_def; RING_OF_NUM_0] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f:A ring`; `q:num`; `y:A`; `n:num`]
        PUREX25519_LADDER) THEN
  ASM_REWRITE_TAC[RING_OF_NUM_EQ_0; DIVIDES_MOD; RING_OF_NUM_0] THEN
  ABBREV_TAC `P = x25519_ladder n (&q,&1)` THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`P:(int#int)#(int#int)`,`P:(int#int)#(int#int)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`Xn:int`; `Zn:int`; `Xm:int`; `Zm:int`] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SPEC_TAC(`group_pow (curve25519x_group f) (SOME (ring_of_num f q,y:A)) n`,
           `Q:(A#A)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_xz; montgomery_xmap] THEN
  SUBGOAL_THEN
   `&(num_of_int(Xn rem &p_25519)) = Xn rem &p_25519 /\
    &(num_of_int(Zn rem &p_25519)) = Zn rem &p_25519`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    REWRITE_TAC[INT_REM_POS_EQ; p_25519; INT_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[RING_OF_INT_EQ_0; GSYM INT_REM_EQ_0; RING_OF_NUM_0] THEN
  GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `f:A ring` RING_OF_NUM_MOD) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[ring_div; RING_OF_NUM_MUL] THEN
  ASM_REWRITE_TAC[GSYM RING_OF_INT_OF_NUM] THEN
  MP_TAC(ISPEC `f:A ring` RING_OF_INT_REM) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RING_LINV_UNIQUE THEN
  REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT] THEN
  ASM_REWRITE_TAC[RING_OF_INT_CLAUSES; RING_OF_INT_EQ] THEN
  MATCH_MP_TAC INT_CONG_TRANS THEN
  EXISTS_TAC
   `&(inverse_mod p_25519 (num_of_int (Zn rem &p_25519))) *
    &(num_of_int (Zn rem &p_25519)):int` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_LMUL THEN
    ASM_REWRITE_TAC[INT_CONG_RREM; INT_CONG_REFL];
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
    REWRITE_TAC[INVERSE_MOD_LMUL_EQ]] THEN
  SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
  ASM_REWRITE_TAC[num_divides; GSYM INT_REM_EQ_0; INT_REM_REM]);;

let PUREX25519_UNIQUE = prove
 (`!n q s. purex25519(n,q) = s <=>
           s < p_25519 /\
           !Q. Q IN group_carrier(curve25519x_group sqintmod_field) /\
               montgomery_xmap sqintmod_field Q =
               ring_of_num sqintmod_field q
               ==> montgomery_xmap sqintmod_field
                     (group_pow (curve25519x_group sqintmod_field) Q n) =
                   ring_of_num sqintmod_field s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[PUREX25519_BOUND] THEN
    SIMP_TAC[PUREX25519; FIELD_SQINTMOD_FIELD; RING_CHAR_SQINTMOD_FIELD];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `ring_of_num sqintmod_field s =
    ring_of_num sqintmod_field (purex25519(n,q))`
  MP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[RING_OF_NUM_EQ; PUREX25519_BOUND; MOD_LT; CONG;
                 RING_CHAR_SQINTMOD_FIELD]] THEN
  SUBGOAL_THEN
   `?Q. Q IN group_carrier (curve25519x_group sqintmod_field) /\
        montgomery_xmap sqintmod_field Q = ring_of_num sqintmod_field q`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `Q:((int#int)#(int#int))option`) THEN
    MP_TAC(ISPECL [`sqintmod_field`; `n:num`; `q:num`;
                   `Q:((int#int)#(int#int))option`] PUREX25519) THEN
    ASM_SIMP_TAC[FIELD_SQINTMOD_FIELD; RING_CHAR_SQINTMOD_FIELD]] THEN
  ASM_SIMP_TAC[FIELD_SQINTMOD_FIELD; RING_CHAR_SQINTMOD_FIELD;
               CURVE25519X_GROUP] THEN
  REWRITE_TAC[IN] THEN REWRITE_TAC[EXISTS_OPTION_THM] THEN
  REWRITE_TAC[montgomery_curve; curve25519x] THEN
  ASM_CASES_TAC `ring_of_num sqintmod_field q = ring_0 sqintmod_field` THEN
  ASM_REWRITE_TAC[montgomery_xmap] THEN ONCE_REWRITE_TAC[EXISTS_PAIR_THM] THEN
  REWRITE_TAC[montgomery_curve] THEN
  EXISTS_TAC `ring_of_num sqintmod_field q` THEN
  ASM_REWRITE_TAC[montgomery_xmap; RING_OF_NUM] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  SIMP_TAC[RING_OF_NUM_1; RING_MUL_LID; RING_POW] THEN
  REWRITE_TAC[NOT_IMP; GSYM RING_OF_INT_OF_NUM] THEN
  REWRITE_TAC[RING_OF_INT_CLAUSES] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; RING_OF_INT_OF_NUM] THEN
  REWRITE_TAC[SQUARE_ROOTS_SQINTMOD_FIELD]);;

let purex25519 = prove
 (`!n q. purex25519(n,q) =
         @s. s < p_25519 /\
             !Q. Q IN group_carrier(curve25519x_group sqintmod_field) /\
                 montgomery_xmap sqintmod_field Q =
                 ring_of_num sqintmod_field q
                 ==> montgomery_xmap sqintmod_field
                       (group_pow (curve25519x_group sqintmod_field) Q n) =
                     ring_of_num sqintmod_field s`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[GSYM PUREX25519_UNIQUE] THEN MESON_TAC[]);;

let PUREX25519_MOD = prove
 (`!n q. purex25519(n,q MOD p_25519) = purex25519(n,q)`,
  REWRITE_TAC[purex25519; GSYM RING_CHAR_SQINTMOD_FIELD; RING_OF_NUM_MOD]);;

let PUREX25519_UNIQUE_IMP = prove
 (`!n q s. s < p_25519 /\
           (!(f:(int#int)ring) Q.
                field f /\ ring_char f = p_25519 /\
                Q IN group_carrier(curve25519x_group f) /\
                montgomery_xmap f Q = ring_of_num f q
                ==> montgomery_xmap f (group_pow (curve25519x_group f) Q n) =
                    ring_of_num f s)
           ==> purex25519(n,q) = s`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[PUREX25519_UNIQUE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[FIELD_SQINTMOD_FIELD; RING_CHAR_SQINTMOD_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The final version "rfcx25519" includes the prenormalization of n and q    *)
(* as in https://www.rfc-editor.org/rfc/rfc7748. Note that this includes     *)
(* an explicit masking of q to 255 bits *before* reduction modulo p_25519,   *)
(* so in that respect is slightly different from Bernstein's original paper  *)
(* which just reduces any q < 2^256 modulo p_25519.                          *)
(* ------------------------------------------------------------------------- *)

let rfcx25519 = define
 `rfcx25519(n,q) =
    purex25519(2 EXP 254 + (n MOD 2 EXP 254 - n MOD 8),
               q MOD 2 EXP 255)`;;

let RFCX25519_PUREX25519 = prove
 (`!n q. n IN {2 EXP 254 + 8 * i | i < 2 EXP 251} /\ q < 2 EXP 255
         ==> rfcx25519(n,q) = purex25519(n,q)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfcx25519] THEN
  AP_TERM_TAC THEN BINOP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a + 8 * i = 1 * a + 8 * i`] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SUB_0] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
