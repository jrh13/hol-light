(* ========================================================================= *)
(* The valuation subrings of Q-bar over a prime p are of rank one: the       *)
(* valuation rings of real non-archimedean absolute values. For k of         *)
(* characteristic 0 algebraic over its prime subfield (Q-bar, or any         *)
(* algebraic extension of Q), v a valuation subring with maximal ideal m of  *)
(* subring_generated k v lying over p (!n. ring_of_int k n IN m <=> &p       *)
(* divides n), and a number subfield L of k (l subfield_of k /\              *)
(* number_field(subfield_generated k l)) with O_L its ring of integers, Q_L  *)
(* = m INTER O_L and e(Q_L|p) = ramification_index (integer_ring,O_L)        *)
(* (ring_of_int O_L) Q_L:                                                    *)
(*                                                                           *)
(*   some w : A->real has w(xy) = w x + w y, min (w x) (w y) <= w(x + y),    *)
(*      x IN v <=> &0 <= w x (x nonzero), w(p) = &1, and                     *)
(*      w x = v_{Q_L}(x) / e(Q_L|p) for x nonzero in any L                   *)
(*      (ALGEBRAIC_VALUATION_SUBRING_RANK_ONE)                               *)
(*   some f : A->real is a nonarchimedean absolute value                     *)
(*      (nonarchimedean_absolute_value of ANT/dedekind_absolute.ml) with     *)
(*      unit ball v and f(p) = inv(&p), with                                 *)
(*      f x = &p rpow --(v_{Q_L}(x) / e(Q_L|p)) for x nonzero in any L       *)
(*      (ALGEBRAIC_VALUATION_SUBRING_ABSOLUTE_VALUE)                         *)
(*                                                                           *)
(* Finitely many algebraic elements generate a number field                  *)
(* (NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC); in a number subfield Q_L is  *)
(* nonzero with v_{Q_L}(p) = e(Q_L|p)                                        *)
(* (VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION) and x IN v <=>           *)
(* v_{Q_L}(x) >= 0 (VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION); for L      *)
(* SUBSET M, v_{Q_M} = e(Q_M|Q_L) v_{Q_L} on L                               *)
(* (VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER), so v_Q(x) / v_Q(p) does not    *)
(* depend on L (VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO).                    *)
(*                                                                           *)
(* Routes: w x is the ratio computed in L = subfield_generated k {x}         *)
(* (FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION,                           *)
(* SUBRING_EQ_SUBFIELD_GENERATED); the properties are checked in             *)
(* subfield_generated k {x,y}; the tower from                                *)
(* DEDEKIND_VALUATION_RAMIFICATION_INDEX of ANT/relative_split.ml for the    *)
(* inclusions, v_{Q_L}(p) from RAMIFICATION_INDEX_PRIME and                  *)
(* DEDEKIND_VALUATION_IMAGE, the unit ball from                              *)
(* VALUATION_SUBRING_NUMBER_SUBFIELD and DEDEKIND_VALUATION_POS; f = p rpow  *)
(* --w (RPOW_ADD, RPOW_MONO_LE_EQ).                                          *)
(*                                                                           *)
(* Uses: Library/fieldtheory.ml, ANT/dedekind_valuation.ml,                  *)
(* ANT/dedekind_absolute.ml (nonarchimedean_absolute_value),                 *)
(* ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/nf_valuation.ml,            *)
(* ANT/prime_split.ml, ANT/relative_split.ml, ANT/valuation_ring.ml,         *)
(* ANT/valuation_residue.ml and Multivariate/transcendentals.ml (rpow).      *)
(* ========================================================================= *)

needs "Library/fieldtheory.ml";;
needs "ANT/dedekind_valuation.ml";;
needs "ANT/dedekind_absolute.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/nf_valuation.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/valuation_ring.ml";;
needs "ANT/valuation_residue.ml";;
needs "Multivariate/transcendentals.ml";;

(* ------------------------------------------------------------------------- *)
(* A valuation subring over p at the finite levels.                          *)
(* ------------------------------------------------------------------------- *)

let VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION = prove
 (`!(k:A ring) v m p l.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        prime p /\ (!n. ring_of_int k n IN m <=> &p divides n) /\
        l subfield_of k /\ number_field(subfield_generated k l)
        ==> ~(m INTER ring_carrier(ring_of_integers(subfield_generated k l)) =
              {ring_0 k}) /\
            dedekind_valuation
             (ring_of_integers(subfield_generated k l),subfield_generated k l)
             I (m INTER ring_carrier(ring_of_integers(subfield_generated k l)))
             (ring_of_num k p) =
            &(ramification_index
               (integer_ring,ring_of_integers(subfield_generated k l))
               (ring_of_int(ring_of_integers(subfield_generated k l)))
               (m INTER
                ring_carrier(ring_of_integers(subfield_generated k l)))) /\
            ~(ramification_index
               (integer_ring,ring_of_integers(subfield_generated k l))
               (ring_of_int(ring_of_integers(subfield_generated k l)))
               (m INTER
                ring_carrier(ring_of_integers(subfield_generated k l))) = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `l:A->bool`]
    VALUATION_SUBRING_NUMBER_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o SPEC `&p:int` o CONJUNCT1)) THEN
  REWRITE_TAC[INTEGER_RULE `(x:int) divides x`] THEN
  REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED; RING_OF_INT_OF_NUM;
              RING_OF_NUM_SUBFIELD_GENERATED] THEN
  ABBREV_TAC `O = ring_of_integers(subfield_generated k (l:A->bool))` THEN
  ABBREV_TAC `Q = m INTER ring_carrier(O:A ring)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_of_num (O:A ring) p = ring_of_num k p` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    REWRITE_TAC[RING_OF_INTEGERS; RING_OF_NUM_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_of_num k p IN ring_carrier(O:A ring) /\
                ~(ring_of_num k p = ring_0(O:A ring))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_THEN `ring_of_num (O:A ring) p = ring_of_num k p`
     (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[RING_OF_NUM] THEN EXPAND_TAC "O" THEN
    REWRITE_TAC[RING_OF_INTEGERS; RING_OF_NUM_SUBFIELD_GENERATED;
                CONJUNCT2 SUBFIELD_GENERATED; RING_OF_NUM_EQ_0] THEN
    REWRITE_TAC[ring_of_integers; RING_CHAR_SUBRING_GENERATED] THEN
    UNDISCH_TAC `number_field(subfield_generated k (l:A->bool))` THEN
    SIMP_TAC[number_field] THEN DISCH_TAC THEN
    REWRITE_TAC[DIVIDES_ZERO] THEN ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Q = {ring_0 k:A})` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(ring_of_num k p = ring_0(O:A ring))` THEN
    EXPAND_TAC "O" THEN
    REWRITE_TAC[RING_OF_INTEGERS; CONJUNCT2 SUBFIELD_GENERATED] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:A ring`; `Q:A->bool`; `p:num`]
    RAMIFICATION_INDEX_PRIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`O:A ring`; `subfield_generated k (l:A->bool)`; `I:A->A`;
                 `Q:A->bool`; `ring_of_num k p:A`]
    DEDEKIND_VALUATION_PRIME_IDEAL) THEN
  MP_TAC(ISPECL [`O:A ring`; `subfield_generated k (l:A->bool)`; `I:A->A`;
                 `Q:A->bool`; `ring_of_num k p:A`]
    DEDEKIND_VALUATION_IMAGE) THEN
  ASM_REWRITE_TAC[I_THM] THEN
  SUBGOAL_THEN
   `dedekind_domain(O:A ring) /\
    ring_monomorphism(O,subfield_generated k (l:A->bool)) I /\
    ~(Q = {ring_0(O:A ring)})`
  (fun th -> REWRITE_TAC[th])
  THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "O" THEN ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS];
      EXPAND_TAC "O" THEN REWRITE_TAC[RING_OF_INTEGERS_FRACTION_FIELD];
      ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_EQ] THEN ARITH_TAC]);;

let VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER = prove
 (`!(k:A ring) v m p l l' x.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        prime p /\ (!n. ring_of_int k n IN m <=> &p divides n) /\
        l subfield_of k /\ number_field(subfield_generated k l) /\
        l' subfield_of k /\ number_field(subfield_generated k l') /\
        l SUBSET l' /\ x IN l /\ ~(x = ring_0 k)
        ==> dedekind_valuation
             (ring_of_integers(subfield_generated k l'),
              subfield_generated k l') I
             (m INTER
              ring_carrier(ring_of_integers(subfield_generated k l'))) x =
            &(ramification_index
               (ring_of_integers(subfield_generated k l),
                ring_of_integers(subfield_generated k l')) I
               (m INTER
                ring_carrier(ring_of_integers(subfield_generated k l')))) *
            dedekind_valuation
             (ring_of_integers(subfield_generated k l),subfield_generated k l)
             I (m INTER ring_carrier(ring_of_integers(subfield_generated k l)))
             x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `l:A->bool`]
    VALUATION_SUBRING_NUMBER_SUBFIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `l':A->bool`]
    VALUATION_SUBRING_NUMBER_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  SUBGOAL_THEN
   `ring_monomorphism(subfield_generated k l,subfield_generated k l')
                     (I:A->A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:A->bool`]
      SUBRING_GENERATED_BY_SUBFIELD_GENERATED) THEN
    MP_TAC(ISPECL [`k:A ring`; `l':A->bool`]
      SUBRING_GENERATED_BY_SUBFIELD_GENERATED) THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC RING_MONOMORPHISM_BETWEEN_SUBRINGS THEN
    ASM_REWRITE_TAC[RING_MONOMORPHISM_I; IMAGE_I];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_char(k:A ring) = 0` ASSUME_TAC THENL
   [UNDISCH_TAC `number_field(subfield_generated k (l:A->bool))` THEN
    SIMP_TAC[number_field; RING_CHAR_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{a | a IN ring_carrier(ring_of_integers(subfield_generated k l)) /\
         a IN m INTER
              ring_carrier(ring_of_integers(subfield_generated k l'))} =
    m INTER ring_carrier(ring_of_integers(subfield_generated k (l:A->bool)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_SUBFIELD_GENERATED] THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(m INTER ring_carrier(ring_of_integers(subfield_generated k l)) =
      {ring_0(ring_of_integers(subfield_generated k (l:A->bool)))})`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC
     `!n. ring_of_int (subfield_generated k (l:A->bool)) n IN
          m INTER ring_carrier (ring_of_integers (subfield_generated k l)) <=>
          &p divides n` THEN
    DISCH_THEN(MP_TAC o SPEC `&p:int`) THEN
    ASM_REWRITE_TAC[INTEGER_RULE `(x:int) divides x`; IN_SING;
                    RING_OF_INTEGERS; RING_OF_INT_SUBFIELD_GENERATED;
                    SUBFIELD_GENERATED; RING_OF_INT_EQ_0] THEN
    REWRITE_TAC[INTEGER_RULE `!x:int. &0 divides x <=> x = &0`;
                INT_OF_NUM_EQ] THEN
    ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ring_of_integers(subfield_generated k (l:A->bool))`;
    `ring_of_integers(subfield_generated k (l':A->bool))`;
    `subfield_generated k (l:A->bool)`; `subfield_generated k (l':A->bool)`;
    `I:A->A`; `I:A->A`; `I:A->A`; `I:A->A`;
    `m INTER
     ring_carrier(ring_of_integers(subfield_generated k (l':A->bool)))`;
    `x:A`] DEDEKIND_VALUATION_RAMIFICATION_INDEX) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD;
               RING_OF_INTEGERS_FRACTION_FIELD;
               RING_MONOMORPHISM_RING_OF_INTEGERS;
               RING_MONOMORPHISM_IMP_HOMOMORPHISM; I_THM;
               CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  MP_TAC(ISPEC `subfield_generated k (l:A->bool)`
    RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; RING_OF_INTEGERS;
               CONJUNCT2 SUBFIELD_GENERATED]);;

let VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO = prove
 (`!(k:A ring) v m p l l' x.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        prime p /\ (!n. ring_of_int k n IN m <=> &p divides n) /\
        l subfield_of k /\ number_field(subfield_generated k l) /\
        l' subfield_of k /\ number_field(subfield_generated k l') /\
        l SUBSET l' /\ x IN l /\ ~(x = ring_0 k)
        ==> real_of_int
             (dedekind_valuation
               (ring_of_integers(subfield_generated k l'),
                subfield_generated k l') I
               (m INTER
                ring_carrier(ring_of_integers(subfield_generated k l'))) x) /
            real_of_int
             (dedekind_valuation
               (ring_of_integers(subfield_generated k l'),
                subfield_generated k l') I
               (m INTER
                ring_carrier(ring_of_integers(subfield_generated k l')))
               (ring_of_num k p)) =
            real_of_int
             (dedekind_valuation
               (ring_of_integers(subfield_generated k l),
                subfield_generated k l) I
               (m INTER
                ring_carrier(ring_of_integers(subfield_generated k l))) x) /
            real_of_int
             (dedekind_valuation
               (ring_of_integers(subfield_generated k l),
                subfield_generated k l) I
               (m INTER
                ring_carrier(ring_of_integers(subfield_generated k l)))
               (ring_of_num k p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_of_num k p IN (l:A->bool) /\ ~(ring_of_num k p = ring_0 k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`subfield_generated k (l:A->bool)`; `p:num`]
        RING_OF_NUM) THEN
      ASM_SIMP_TAC[RING_OF_NUM_SUBFIELD_GENERATED;
                   CARRIER_SUBFIELD_GENERATED_SUBFIELD];
      REWRITE_TAC[RING_OF_NUM_EQ_0] THEN
      UNDISCH_TAC `number_field(subfield_generated k (l:A->bool))` THEN
      SIMP_TAC[number_field; RING_CHAR_SUBFIELD_GENERATED] THEN
      REWRITE_TAC[DIVIDES_ZERO] THEN ASM_MESON_TAC[PRIME_0]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `p:num`; `l':A->bool`]
    VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION) THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `p:num`; `l:A->bool`;
                 `l':A->bool`; `ring_of_num k p:A`]
    VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER) THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `p:num`; `l:A->bool`;
                 `l':A->bool`; `x:A`]
    VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(p /\ q /\ r ==> s) ==> p ==> q ==> t /\ r ==> s`) THEN
  MATCH_ACCEPT_TAC(prove
   (`!a b c d (n:num) (n':num).
        c = &n * a /\ d = &n * b /\ d = &n' /\ ~(n' = 0)
        ==> real_of_int c / real_of_int d = real_of_int a / real_of_int b`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[INT_MUL_LZERO] THEN MESON_TAC[INT_OF_NUM_EQ];
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC
       (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
      REWRITE_TAC[int_mul_th; int_of_num_th] THEN
      MATCH_MP_TAC(REAL_FIELD
       `!n a b:real. ~(n = &0) ==> (n * a) / (n * b) = a / b`) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_EQ]])));;

(* ------------------------------------------------------------------------- *)
(* Rank one: the real valuation and the absolute value.                      *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_VALUATION_SUBRING_RANK_ONE = prove
 (`!(k:A ring) v m p.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        prime p /\ (!n. ring_of_int k n IN m <=> &p divides n)
        ==> ?w:A->real.
             (!x y. x IN ring_carrier k /\ y IN ring_carrier k /\
                    ~(x = ring_0 k) /\ ~(y = ring_0 k)
                    ==> w(ring_mul k x y) = w x + w y) /\
             (!x y. x IN ring_carrier k /\ y IN ring_carrier k /\
                    ~(x = ring_0 k) /\ ~(y = ring_0 k) /\
                    ~(ring_add k x y = ring_0 k)
                    ==> min (w x) (w y) <= w(ring_add k x y)) /\
             (!x. x IN ring_carrier k /\ ~(x = ring_0 k)
                  ==> (x IN v <=> &0 <= w x)) /\
             w(ring_of_num k p) = &1 /\
             (!l x. l subfield_of k /\ number_field(subfield_generated k l) /\
                    x IN l /\ ~(x = ring_0 k)
                    ==> w x =
                        real_of_int
                         (dedekind_valuation
                           (ring_of_integers(subfield_generated k l),
                            subfield_generated k l) I
                           (m INTER ring_carrier
                              (ring_of_integers(subfield_generated k l)))
                           x) /
                        &(ramification_index
                           (integer_ring,
                            ring_of_integers(subfield_generated k l))
                           (ring_of_int
                             (ring_of_integers(subfield_generated k l)))
                           (m INTER ring_carrier
                              (ring_of_integers(subfield_generated k l)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  SUBGOAL_THEN
   `!s. FINITE s /\ s SUBSET ring_carrier k
        ==> ring_carrier(subfield_generated k s) subfield_of k /\
            number_field(subfield_generated k
                          (ring_carrier(subfield_generated k (s:A->bool))))`
  (LABEL_TAC "nf") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED;
                 SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `algebraic_extension(subfield_generated k {ring_0 k},k) (I:A->A)` THEN
    REWRITE_TAC[algebraic_extension] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l subfield_of k /\ number_field(subfield_generated k l)
        ==> ~(m INTER ring_carrier(ring_of_integers(subfield_generated k l)) =
              {ring_0 k}) /\
            &0 < real_of_int
                  (dedekind_valuation
                    (ring_of_integers(subfield_generated k l),
                     subfield_generated k l) I
                    (m INTER ring_carrier
                       (ring_of_integers(subfield_generated k (l:A->bool))))
                    (ring_of_num k p))`
  (LABEL_TAC "pos") THENL
   [X_GEN_TAC `l:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `p:num`;
                   `l:A->bool`]
      VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[int_of_num_th; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `R = \(l:A->bool) (x:A). real_of_int
                 (dedekind_valuation
                   (ring_of_integers(subfield_generated k l),
                    subfield_generated k l) I
                   (m INTER ring_carrier
                      (ring_of_integers(subfield_generated k l))) x) /
               real_of_int
                 (dedekind_valuation
                   (ring_of_integers(subfield_generated k l),
                    subfield_generated k l) I
                   (m INTER ring_carrier
                      (ring_of_integers(subfield_generated k l)))
                   (ring_of_num k p))` THEN
  SUBGOAL_THEN
   `!l l' x. l subfield_of k /\ number_field(subfield_generated k l) /\
             l' subfield_of k /\ number_field(subfield_generated k l') /\
             l SUBSET l' /\ x IN l /\ ~(x = ring_0 k)
             ==> (R:(A->bool)->A->real) l' x = R l x`
  (LABEL_TAC "rat") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "R" THEN
    MATCH_MP_TAC VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO THEN
    EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l x. l subfield_of k /\ number_field(subfield_generated k l) /\
          x IN l /\ ~(x = ring_0 k)
          ==> (R:(A->bool)->A->real) l x =
              R (ring_carrier(subfield_generated k {x})) x`
  (LABEL_TAC "K") THENL
   [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBFIELD_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
      USE_THEN "nf" (MP_TAC o SPEC `{x:A}`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[FINITE_SING; SING_SUBSET]; STRIP_TAC] THEN
      USE_THEN "rat" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
        ASM_REWRITE_TAC[SING_SUBSET];
        MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
        ASM_REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l x y. l subfield_of k /\ number_field(subfield_generated k l) /\
            x IN l /\ y IN l /\ ~(x = ring_0 k) /\ ~(y = ring_0 k)
            ==> (R:(A->bool)->A->real) l (ring_mul k x y) = R l x + R l y /\
                (~(ring_add k x y = ring_0 k)
                 ==> min (R l x) (R l y) <= R l (ring_add k x y))`
  (LABEL_TAC "hom") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "pos" (MP_TAC o SPEC `l:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `l:A->bool`]
      VALUATION_SUBRING_NUMBER_SUBFIELD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    EXPAND_TAC "R" THEN
    MP_TAC(ISPECL
     [`ring_of_integers(subfield_generated k (l:A->bool))`;
      `subfield_generated k (l:A->bool)`; `I:A->A`;
      `m INTER
       ring_carrier(ring_of_integers(subfield_generated k (l:A->bool)))`;
      `x:A`; `y:A`] DEDEKIND_VALUATION_MUL) THEN
    MP_TAC(ISPECL
     [`ring_of_integers(subfield_generated k (l:A->bool))`;
      `subfield_generated k (l:A->bool)`; `I:A->A`;
      `m INTER
       ring_carrier(ring_of_integers(subfield_generated k (l:A->bool)))`;
      `x:A`; `y:A`] DEDEKIND_VALUATION_ADD) THEN
    MP_TAC(ISPEC `subfield_generated k (l:A->bool)`
      RING_OF_INTEGERS_FRACTION_FIELD) THEN
    ASM_REWRITE_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; RING_OF_INTEGERS;
                    CONJUNCT2 SUBFIELD_GENERATED; I_THM] THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[int_add_th; real_div; REAL_ADD_RDISTRIB];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ASM_REWRITE_TAC[INT_MIN_LE; REAL_MIN_LE] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_INT_CLAUSES]];
    ALL_TAC] THEN
  EXISTS_TAC
   `\x:A. (R:(A->bool)->A->real)
          (ring_carrier(subfield_generated k {x})) x` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "nf" (MP_TAC o SPEC `{x:A,y}`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET;
                      EMPTY_SUBSET];
      STRIP_TAC] THEN
    SUBGOAL_THEN
     `(x:A) IN ring_carrier(subfield_generated k {x,y}) /\
      (y:A) IN ring_carrier(subfield_generated k {x,y}) /\
      ring_mul k x y IN ring_carrier(subfield_generated k {x,y}) /\
      ~(ring_mul k x y = ring_0 k)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT
       `p /\ q /\ (p /\ q ==> r) /\ s ==> p /\ q /\ r /\ s`) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
        ASM_REWRITE_TAC[IN_INSERT];
        MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
        ASM_REWRITE_TAC[IN_INSERT];
        ASM_MESON_TAC[IN_SUBFIELD_MUL];
        ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN]];
      ALL_TAC] THEN
    USE_THEN "K" (MP_TAC o SPECL
      [`ring_carrier(subfield_generated k {x:A,y})`; `ring_mul k x y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "K" (MP_TAC o SPECL
      [`ring_carrier(subfield_generated k {x:A,y})`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "K" (MP_TAC o SPECL
      [`ring_carrier(subfield_generated k {x:A,y})`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "hom" (MP_TAC o SPECL
      [`ring_carrier(subfield_generated k {x:A,y})`; `x:A`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "nf" (MP_TAC o SPEC `{x:A,y}`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET;
                      EMPTY_SUBSET];
      STRIP_TAC] THEN
    SUBGOAL_THEN
     `(x:A) IN ring_carrier(subfield_generated k {x,y}) /\
      (y:A) IN ring_carrier(subfield_generated k {x,y}) /\
      ring_add k x y IN ring_carrier(subfield_generated k {x,y})`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
        ASM_REWRITE_TAC[IN_INSERT];
        MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
        ASM_REWRITE_TAC[IN_INSERT];
        ASM_MESON_TAC[IN_SUBFIELD_ADD]];
      ALL_TAC] THEN
    USE_THEN "K" (MP_TAC o SPECL
      [`ring_carrier(subfield_generated k {x:A,y})`; `ring_add k x y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "K" (MP_TAC o SPECL
      [`ring_carrier(subfield_generated k {x:A,y})`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "K" (MP_TAC o SPECL
      [`ring_carrier(subfield_generated k {x:A,y})`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "hom" (MP_TAC o SPECL
      [`ring_carrier(subfield_generated k {x:A,y})`; `x:A`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    USE_THEN "nf" (MP_TAC o SPEC `{x:A}`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[FINITE_SING; SING_SUBSET]; STRIP_TAC] THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier(subfield_generated k {x})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_SING];
      ALL_TAC] THEN
    USE_THEN "pos"
     (MP_TAC o SPEC `ring_carrier(subfield_generated k {x:A})`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`;
                   `ring_carrier(subfield_generated k {x:A})`; `x:A`]
      VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "R" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN
    REWRITE_TAC[int_le; int_of_num_th];
    SUBGOAL_THEN `ring_of_num k p IN ring_carrier(k:A ring)` ASSUME_TAC THENL
     [REWRITE_TAC[RING_OF_NUM]; ALL_TAC] THEN
    USE_THEN "nf" (MP_TAC o SPEC `{ring_of_num k p:A}`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[FINITE_SING; SING_SUBSET]; STRIP_TAC] THEN
    USE_THEN "pos" (MP_TAC o SPEC
      `ring_carrier(subfield_generated k {ring_of_num k p:A})`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`l:A->bool`; `x:A`] THEN STRIP_TAC THEN
    USE_THEN "K" (MP_TAC o SPECL [`l:A->bool`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    EXPAND_TAC "R" THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `p:num`; `l:A->bool`]
      VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[int_of_num_th]]);;

let ALGEBRAIC_VALUATION_SUBRING_ABSOLUTE_VALUE = prove
 (`!(k:A ring) v m p.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        prime p /\ (!n. ring_of_int k n IN m <=> &p divides n)
        ==> ?f:A->real.
             nonarchimedean_absolute_value k f /\
             (!x. x IN ring_carrier k ==> (x IN v <=> f x <= &1)) /\
             f(ring_of_num k p) = inv(&p) /\
             (!l x. l subfield_of k /\ number_field(subfield_generated k l) /\
                    x IN l /\ ~(x = ring_0 k)
                    ==> f x =
                        &p rpow
                        --(real_of_int
                            (dedekind_valuation
                              (ring_of_integers(subfield_generated k l),
                               subfield_generated k l) I
                              (m INTER ring_carrier
                                (ring_of_integers(subfield_generated k l)))
                              x) /
                           &(ramification_index
                              (integer_ring,
                               ring_of_integers(subfield_generated k l))
                              (ring_of_int
                                (ring_of_integers(subfield_generated k l)))
                              (m INTER
                               ring_carrier
                                (ring_of_integers
                                  (subfield_generated k l))))))`,
  REWRITE_TAC[NONARCHIMEDEAN_ABSOLUTE_VALUE; GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ALGEBRAIC_VALUATION_SUBRING_RANK_ONE) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  SUBGOAL_THEN `&1 < (&p:real) /\ &0 < (&p:real)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\x:A. if x = ring_0 k then &0 else &p rpow --(w x)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL; RPOW_POS_LT; REAL_LT_IMP_LE; REAL_LT_IMP_NZ];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:A = ring_0 k` THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; REAL_MUL_LZERO] THEN
    ASM_CASES_TAC `y:A = ring_0 k` THEN
    ASM_SIMP_TAC[RING_MUL_RZERO; REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN] THEN
    ASM_SIMP_TAC[REAL_NEG_ADD; RPOW_ADD];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:A = ring_0 k` THENL
     [ASM_SIMP_TAC[RING_ADD_LZERO] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_MAX; REAL_LE_REFL];
      ALL_TAC] THEN
    ASM_CASES_TAC `y:A = ring_0 k` THENL
     [ASM_SIMP_TAC[RING_ADD_RZERO; REAL_LE_MAX; REAL_LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MAX; RPOW_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`] o check (fun th ->
      can (find_term ((=) `min:real->real->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MIN_LE; REAL_LE_MAX] THEN
    MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC RPOW_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:A = ring_0 k` THEN ASM_REWRITE_TAC[REAL_POS] THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP IN_SUBRING_0); ALL_TAC] THEN
    SUBGOAL_THEN `(x:A) IN v <=> &0 <= (w:A->real) x` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [GSYM(SPEC `&p:real` RPOW_0)] THEN
    ASM_SIMP_TAC[RPOW_MONO_LE_EQ] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `~(ring_of_num k p = ring_0 (k:A ring))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO] THEN
      ASM_MESON_TAC[PRIME_0];
      ASM_REWRITE_TAC[RPOW_NEG; RPOW_POW; REAL_POW_1]];
    MAP_EVERY X_GEN_TAC [`l:A->bool`; `x:A`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[]]);;
