(* ========================================================================= *)
(* A few extras to support proofs around elliptic curves.                    *)
(* ========================================================================= *)

needs "Library/pocklington.ml";;
needs "Library/primitive.ml";;
needs "Library/grouptheory.ml";;
needs "Library/ringtheory.ml";;

(* ------------------------------------------------------------------------- *)
(* Bounds on size of any curve of the form y^2 = f(x) over finite field.     *)
(* ------------------------------------------------------------------------- *)

let FINITE_QUADRATIC_CURVE = prove
 (`!(r:A ring) h.
        integral_domain r /\ FINITE(ring_carrier r)
        ==> FINITE {x,y | x IN ring_carrier r /\ y IN ring_carrier r /\
                          ring_pow r y 2 = h x} /\
            CARD {x,y | x IN ring_carrier r /\ y IN ring_carrier r /\
                        ring_pow r y 2 = h x}
            <= 2 * CARD(ring_carrier r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_MP_TAC FINITE_CARD_LE_SUBSET THEN
  EXISTS_TAC
   `UNIONS {{x,y | y | y IN ring_carrier r /\ ring_pow r y 2 = h x} |x|
            (x:A) IN ring_carrier r}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    SET_TAC[];
    MATCH_MP_TAC FINITE_CARD_LE_UNIONS THEN ASM_REWRITE_TAC[LE_REFL]] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC FINITE_CARD_LE_IMAGE THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> p /\ ~(p ==> ~q)`] THEN
  REWRITE_TAC[ARITH_RULE `~(n <= 2) <=> 3 <= n`; CHOOSE_SUBSET_EQ] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  MP_TAC(INTEGRAL_DOMAIN_RULE
   `!x y:A. integral_domain r
    ==> (ring_pow r x 2 = ring_pow r y 2 <=> x = y \/ x = ring_neg r y)`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM METIS_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Try to dispose of ring characteristic side-conditions. This in general    *)
(* requires external factorization tools for "multifactor" on large numbers. *)
(* ------------------------------------------------------------------------- *)

let NOT_RING_CHAR_DIVIDES_TAC =
  let bops = list_mk_binop `( * ):num->num->num`
  and patcheck = can (term_match [] `~(ring_char r divides NUMERAL n)`) in
  W(fun (asl,w) ->
        if not (patcheck w) then failwith "NOT_RING_CHAR_DIVIDES_TAC" else
        let n = dest_numeral(rand(rand w)) in
        let ns = multifactor n in
        let ntm = bops(map mk_numeral ns) in
        SUBST1_TAC(SYM(NUM_REDUCE_CONV ntm))) THEN
  ASM_SIMP_TAC[RING_CHAR_DIVIDES_MUL];;

(* ------------------------------------------------------------------------- *)
(* Ad-hoc rewrites for equality versus divisibility of characteristic.       *)
(* ------------------------------------------------------------------------- *)

let FIELD_CHAR_NOT2 = prove
 (`!(f:A ring) P.
        field f /\ ~(ring_char f = 2) /\ P <=>
        field f /\ ~(ring_char f divides 2) /\ P`,
  MESON_TAC[RING_CHAR_DIVIDES_PRIME; PRIME_2]);;

let FIELD_CHAR_NOT3 = prove
 (`!(f:A ring) P.
        field f /\ ~(ring_char f = 3) /\ P <=>
        field f /\ ~(ring_char f divides 3) /\ P`,
  MESON_TAC[RING_CHAR_DIVIDES_PRIME; PRIME_CONV `prime 3`]);;

let FIELD_CHAR_NOT23 = prove
 (`!(f:A ring) P.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\ P <=>
        field f /\ ~(ring_char f divides 2) /\ ~(ring_char f divides 3) /\ P`,
  MESON_TAC[RING_CHAR_DIVIDES_PRIME; PRIME_2; PRIME_CONV `prime 3`]);;

(* ------------------------------------------------------------------------- *)
(* An ad-hoc way of confirming the size of a group to be n when there is a   *)
(* crude bound of < 3 * n and we also know there are no points of order 2.   *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_GROUP_THEOREM_2 = prove
 (`!G:A group.
        FINITE(group_carrier G) /\ EVEN(CARD(group_carrier G))
        ==> ?x. x IN group_carrier G /\ group_element_order G x = 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_GROUP_THEOREM THEN
  ASM_REWRITE_TAC[PRIME_2; DIVIDES_2]);;

let GROUP_ADHOC_ORDER_UNIQUE_LEMMA = prove
 (`!G (a:A) p.
      FINITE(group_carrier G) /\ CARD(group_carrier G) < 3 * p /\
      (!x. x IN group_carrier G /\ group_inv G x = x ==> x = group_id G) /\
      a IN group_carrier G /\ group_element_order G a = p
      ==> (group_carrier G) HAS_SIZE p`,
  SIMP_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN MP_TAC
   (SPECL [`G:A group`; `a:A`] GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
  ASM_REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:num` THEN
  ASM_CASES_TAC `d = 0` THEN
  ASM_SIMP_TAC[CARD_EQ_0; MULT_CLAUSES; GROUP_CARRIER_NONEMPTY] THEN
  ASM_CASES_TAC `d = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  ASM_CASES_TAC `d = 2` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [MP_TAC(ISPEC `G:A group` CAUCHY_GROUP_THEOREM_2) THEN
    ASM_REWRITE_TAC[EVEN_MULT; ARITH; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_EQ_2_ALT] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `CARD(group_carrier(G:A group)) < 3 * p` THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN ASM_REWRITE_TAC[NOT_LT] THEN
    GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Use some symmetry to ease algebraic reduction of associativity            *)
(* ------------------------------------------------------------------------- *)

let SYMMETRY_LEMMA = prove
 (`!P eq add.
     (!x y. P x /\ P y /\ eq x y ==> eq y x) /\
     (!x y. P x /\ P y ==> P(add x y)) /\
     (!x y. P x /\ P y ==> add x y = add y x) /\
     (!x y z. P x /\ P y /\ P z /\ (eq x y \/ eq (add x y) z)
              ==> add x (add y z) = add (add x y) z) /\
     (!x y z. P x /\ P y /\ P z /\
              ~(eq x y) /\ ~(eq y z) /\ ~(eq x z) /\
              ~(eq (add x y) z) /\ ~(eq (add y z) x)
              ==> add x (add y z) = add (add x y) z)
     ==> !x y z:A. P x /\ P y /\ P z ==> add x (add y z) = add (add x y) z`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(eq:A->A->bool) x y` THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `(eq:A->A->bool) y z` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(eq:A->A->bool) x z` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(eq:A->A->bool) ((add:A->A->A) x y) z` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(eq:A->A->bool) ((add:A->A->A) y z) x` THEN
  ASM_MESON_TAC[]);;

let ASSOCIATIVITY_LEMMA = prove
(`!P add neg (id:A).
        P id /\
        (!x. P x ==> P(neg x)) /\
        (!x y. P x /\ P y ==> P(add x y)) /\
        (!x. P x ==> add id x = x) /\
        (!x. P x ==> add (neg x) x = id) /\
        (!x y. P x /\ P y ==> add x y = add y x) /\
        (!x. P x ==> neg(neg x) = x) /\
        (!x y. P x /\ P y ==> neg(add x y) = add (neg x) (neg y)) /\
        (!x y. P x /\ P y ==> add x (add x y) = add (add x x) y) /\
        (!x y. P x /\ P y ==> add (neg x) (add x y) = y) /\
        (!x y z u v.
            P x /\ P y /\ P z /\ P u /\ P v
            ==> ~(x = id) /\ ~(y = id) /\ ~(z = id) /\
                ~(u = id) /\ ~(v = id) /\
                ~(y = x \/ y = neg x) /\
                ~(z = y \/ z = neg y) /\
                ~(z = x \/ z = neg x) /\
                ~(z = u \/ z = neg u) /\
                ~(x = v \/ x = neg v)
                ==> add x y = u /\ add y z = v
                    ==> add x v = add u z)
     ==> !x y z. P x /\ P y /\ P z ==> add x (add y z) = add (add x y) z`,
  ONCE_REWRITE_TAC[TAUT
   `p ==> q ==> r /\ s ==> t <=> r ==> s ==> p /\ q ==> t`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SYMMETRY_LEMMA THEN
  EXISTS_TAC `\x y. y:A = x \/ y = neg x` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC;
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `z:A`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:A = id` THENL
     [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `y:A = id` THENL
     [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `z:A = id` THENL
     [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC;
    TRANS_TAC EQ_TRANS `id:A` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    TRANS_TAC EQ_TRANS `(add:A->A->A) x (neg x)` THEN
    CONJ_TAC THENL [AP_TERM_TAC; ASM_MESON_TAC[]] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]] THEN
  TRANS_TAC EQ_TRANS
   `add (x:A) (add (neg x) (add (add x y) (add x y)))` THEN
  CONJ_TAC THENL [AP_TERM_TAC; ASM_MESON_TAC[]] THEN
  TRANS_TAC EQ_TRANS `add (add (neg x) (add x y)) (add x y):A` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:A. P x /\ P y ==> add y (add x x) = add (add y x) x`
   (fun th -> ASM_SIMP_TAC[th]) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Formulate existence of roots in finite field as power residue over N.     *)
(* This is intuitively completely trivial but fiddly in the fine details,    *)
(* especially since we don't actually assume n is prime and so it's a field. *)
(* ------------------------------------------------------------------------- *)

let INTEGER_MOD_RING_ROOT_EXISTS = prove
 (`!n a k. (?b. b IN ring_carrier (integer_mod_ring n) /\
                ring_pow (integer_mod_ring n) b k = &a) <=>
           (n = 0 \/ a < n) /\
           (?b. (b EXP k == a) (mod n))`,
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_POW] THEN
  REWRITE_TAC[INT_EXISTS_POS] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[INTEGER_MOD_RING_CLAUSES; LE_1] THENL
   [REWRITE_TAC[IN_UNIV; INT_REM_0; INT_CONG_MOD_0] THEN
    EQ_TAC THENL [DISCH_THEN(X_CHOOSE_TAC `b:int`); MESON_TAC[]] THEN
    EXISTS_TAC `abs b:int` THEN
    ASM_REWRITE_TAC[INT_ABS_POS; GSYM INT_ABS_POW; INT_ABS_NUM];
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[GSYM INT_EXISTS_POS; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REWRITE_TAC[GSYM num_congruent; CONG] THEN
    ASM_MESON_TAC[MOD_LT; MOD_EXP_MOD; MOD_LT_EQ]]);;
