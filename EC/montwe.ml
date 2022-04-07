(* ========================================================================= *)
(* Isomorphic mappings from Montgomery to Weierstrass form and back again.   *)
(* ========================================================================= *)

needs "EC/montgomery.ml";;
needs "EC/weierstrass.ml";;

(* ------------------------------------------------------------------------- *)
(* Map from Montgomery to Weierstrass by (x,y) |-> ((x + A / 3) / B, y / B)  *)
(* and from Weierstrass to Montgomery by (x,y) |-> (B * x - A / 3, B * y)    *)
(* and thus Montgomery(A,B) curve gives Weierstrass(a,b) where               *)
(*                                                                           *)
(*     a = (1 - A^2 / 3) / B^2                                               *)
(*     b = A * (2 * A^2 - 9) / (27 * B^3)                                    *)
(* ------------------------------------------------------------------------- *)

let wcurve_of_mcurve = define
 `wcurve_of_mcurve(f,(a:A),b) =
   (f,
    ring_div f (ring_sub f (ring_of_num f 1)
                           (ring_div f (ring_pow f a 2) (ring_of_num f 3)))
               (ring_pow f b 2),
    ring_div f (ring_mul f a (ring_sub f (ring_mul f (ring_of_num f 2)
                                                     (ring_pow f a 2))
                                         (ring_of_num f 9)))
               (ring_mul f (ring_of_num f 27) (ring_pow f b 3)))`;;

let WCURVE_OF_MCURVE_NONSINGULAR_EQ = prove
 (`!f a b:A.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f)
        ==> (weierstrass_nonsingular(wcurve_of_mcurve(f,a,b)) <=>
             ~(ring_pow f a 2 = ring_of_num f 4))`,
  REWRITE_TAC[FIELD_CHAR_NOT23] THEN
  REWRITE_TAC[montgomery_nonsingular;
              weierstrass_nonsingular; wcurve_of_mcurve] THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let WCURVE_OF_MCURVE_NONSINGULAR = prove
 (`!f a b:A.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b)
        ==> weierstrass_nonsingular(wcurve_of_mcurve(f,a,b))`,
  SIMP_TAC[montgomery_nonsingular; DE_MORGAN_THM;
           WCURVE_OF_MCURVE_NONSINGULAR_EQ]);;

let weierstrass_of_montgomery = define
 `weierstrass_of_montgomery(f,a:A,b) NONE = NONE /\
  weierstrass_of_montgomery(f,a:A,b) (SOME(x,y)) =
  SOME(ring_div f (ring_add f x (ring_div f a (ring_of_num f 3))) b,
       ring_div f y b)`;;

let montgomery_of_weierstrass = define
 `montgomery_of_weierstrass(f,a:A,b) NONE = NONE /\
  montgomery_of_weierstrass(f,a:A,b) (SOME(x,y)) =
  SOME(ring_sub f (ring_mul f b x) (ring_div f a (ring_of_num f 3)),
       ring_mul f b y)`;;

let MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY = prove
 (`!f a (b:A) p.
        field f /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        montgomery_point f p
        ==> montgomery_of_weierstrass(f,a,b)
              (weierstrass_of_montgomery(f,a,b) p) = p`,
  REWRITE_TAC[FIELD_CHAR_NOT3] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_of_weierstrass; weierstrass_of_montgomery] THEN
  REWRITE_TAC[montgomery_point; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN FIELD_TAC);;

let WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS = prove
 (`!f a (b:A) p.
        field f /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        weierstrass_point f p
        ==> weierstrass_of_montgomery(f,a,b)
              (montgomery_of_weierstrass(f,a,b) p) = p`,
  REWRITE_TAC[FIELD_CHAR_NOT3] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_of_weierstrass; weierstrass_of_montgomery] THEN
  REWRITE_TAC[weierstrass_point; option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN FIELD_TAC);;

let WEIERSTRASS_OF_MONTGOMERY = prove
 (`!f (a:A) b p.
        field f /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p
        ==> weierstrass_curve (wcurve_of_mcurve(f,a,b))
                              (weierstrass_of_montgomery(f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_curve; weierstrass_curve;
              weierstrass_of_montgomery; wcurve_of_mcurve] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FIELD_CHAR_NOT3] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let MONTGOMERY_OF_WEIERSTRASS = prove
 (`!f (a:A) b p.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        weierstrass_curve (wcurve_of_mcurve(f,a,b)) p
        ==> montgomery_curve(f,a,b) (montgomery_of_weierstrass(f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_curve; weierstrass_curve;
              montgomery_of_weierstrass; wcurve_of_mcurve] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FIELD_CHAR_NOT23] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let WEIERSTRASS_OF_MONTGOMERY_NEG = prove
 (`!f (a:A) b p.
        field f /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        ~(b = ring_0 f) /\
        montgomery_curve(f,a,b) p
        ==> weierstrass_of_montgomery(f,a,b) (montgomery_neg(f,a,b) p) =
            weierstrass_neg (wcurve_of_mcurve(f,a,b))
                            (weierstrass_of_montgomery(f,a,b) p)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_curve; weierstrass_of_montgomery;
              montgomery_of_weierstrass;  wcurve_of_mcurve;
              montgomery_neg; weierstrass_neg] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ; FIELD_CHAR_NOT3] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let WEIERSTRASS_OF_MONTGOMERY_ADD = prove
 (`!f (a:A) b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        ~(b = ring_0 f) /\
        montgomery_curve(f,a,b) p /\ montgomery_curve(f,a,b) q
        ==> weierstrass_of_montgomery(f,a,b) (montgomery_add(f,a,b) p q) =
            weierstrass_add (wcurve_of_mcurve(f,a,b))
                            (weierstrass_of_montgomery(f,a,b) p)
                            (weierstrass_of_montgomery(f,a,b) q)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_curve; weierstrass_of_montgomery;
              montgomery_of_weierstrass;  wcurve_of_mcurve;
              montgomery_add; weierstrass_add] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[FIELD_CHAR_NOT23] THEN REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[weierstrass_of_montgomery]) THEN
  REPEAT LET_TAC THEN
  ASM_REWRITE_TAC[montgomery_of_weierstrass; weierstrass_of_montgomery] THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP = prove
 (`!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> group_isomorphisms
           (montgomery_group(f,a,b),weierstrass_group(wcurve_of_mcurve(f,a,b)))
           (weierstrass_of_montgomery(f,a,b),
            montgomery_of_weierstrass(f,a,b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (striplist dest_pair (rand(concl wcurve_of_mcurve)))
                WEIERSTRASS_GROUP) THEN
  REWRITE_TAC[GSYM wcurve_of_mcurve] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[WCURVE_OF_MCURVE_NONSINGULAR] THEN
    REPEAT CONJ_TAC THEN RING_CARRIER_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `b:A`] MONTGOMERY_GROUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[GROUP_ISOMORPHISMS; GROUP_HOMOMORPHISM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[IN] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[montgomery_nonsingular]) THEN
  SUBGOAL_THEN
   `(!x. weierstrass_curve (wcurve_of_mcurve (f,(a:A),b)) x
         ==> weierstrass_point f x) /\
    (!y. montgomery_curve (f,a,b) y ==> montgomery_point f y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; FORALL_OPTION_THM] THEN
    SIMP_TAC[weierstrass_curve; weierstrass_point; wcurve_of_mcurve;
                montgomery_curve; montgomery_point];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WEIERSTRASS_OF_MONTGOMERY; WEIERSTRASS_OF_MONTGOMERY_ADD;
               MONTGOMERY_OF_WEIERSTRASS;
               MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY;
               WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS]);;

let GROUP_ISOMORPHISMS_WEIERSTRASS_MONTGOMERY_GROUP = prove
 (`!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> group_isomorphisms
           (weierstrass_group(wcurve_of_mcurve(f,a,b)),montgomery_group(f,a,b))
           (montgomery_of_weierstrass(f,a,b),
            weierstrass_of_montgomery(f,a,b))`,
  ONCE_REWRITE_TAC[GROUP_ISOMORPHISMS_SYM] THEN
  ACCEPT_TAC GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP);;

let ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP = prove
 (`!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> (montgomery_group(f,a,b)) isomorphic_group
          (weierstrass_group(wcurve_of_mcurve(f,a,b)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o
    MATCH_MP GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP) THEN
  MESON_TAC[GROUP_ISOMORPHISMS_IMP_ISOMORPHISM; isomorphic_group]);;

let ISOMORPHIC_WEIERSTRASS_MONTGOMERY_GROUP = prove
 (`!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> (weierstrass_group(wcurve_of_mcurve(f,a,b))) isomorphic_group
          (montgomery_group(f,a,b))`,
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  ACCEPT_TAC ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP);;
