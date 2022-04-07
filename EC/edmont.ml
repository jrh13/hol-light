(* ========================================================================= *)
(* Mapping from Edwards to Montgomery form (and back as applicable).         *)
(* ========================================================================= *)

needs "EC/edwards.ml";;
needs "EC/montgomery.ml";;

(* ------------------------------------------------------------------------- *)
(* Map from Edwards(a,d) to Montgomery(A,B) where                            *)
(*                                                                           *)
(*         A = 2 * (a + d) / (a - d)                                         *)
(*         B = (4 / (a - d)) / c^2                                           *)
(*                                                                           *)
(* defined by                                                                *)
(*                                                                           *)
(*         (x,y) |-> ((1 + y) / (1 - y), c * (1 + y) / ((1 - y) * x))        *)
(*                                                                           *)
(* Here c is an arbitrary (nonzero) parameter giving a scaling factor.       *)
(* ------------------------------------------------------------------------- *)

let mcurve_of_ecurve = define
  `mcurve_of_ecurve (f,(a:A),d) c =
        (f,
         ring_div f (ring_mul f (ring_of_num f 2) (ring_add f a d))
                    (ring_sub f a d),
         ring_div f
          (ring_div f (ring_of_num f 4) (ring_sub f a d))
          (ring_pow f c 2))`;;

let montgomery_of_edwards = define
 `montgomery_of_edwards(f:A ring) c (x,y) =
        if (x,y) = (ring_0 f,ring_1 f) then
           NONE
        else if (x,y) = (ring_0 f,ring_neg f (ring_1 f)) then
           SOME(ring_0 f,ring_0 f)
        else
           SOME(ring_div f (ring_add f (ring_1 f) y) (ring_sub f (ring_1 f) y),
                ring_mul f c
                 (ring_div f (ring_add f (ring_1 f) y)
                             (ring_mul f x (ring_sub f (ring_1 f) y))))`;;

(* ------------------------------------------------------------------------- *)
(* Mapping from Montgomery(A,B) to Edwards(a,d) where                        *)
(*                                                                           *)
(*         a = ((A + 2) / B) / c^2                                           *)
(*         d = ((A - 2) / B) / c^2                                           *)
(*                                                                           *)
(* defined by                                                                *)
(*         (x,y) |-> (c * x / y, (x - 1) / (x + 1))                          *)
(*                                                                           *)
(* Here c is an arbitrary (nonzero) parameter giving a scaling factor.       *)
(* ------------------------------------------------------------------------- *)

let ecurve_of_mcurve = define
 `ecurve_of_mcurve (f,A:A,B) c =
        (f,
         ring_div f (ring_div f (ring_add f A (ring_of_num f 2)) B)
                    (ring_pow f c 2),
         ring_div f (ring_div f (ring_sub f A (ring_of_num f 2)) B)
                    (ring_pow f c 2))`;;

let edwards_of_montgomery = define
 `edwards_of_montgomery(f:A ring) c NONE =
    (ring_0 f,ring_1 f) /\
  edwards_of_montgomery(f:A ring) c (SOME(x,y)) =
    if (x,y) = (ring_0 f,ring_0 f) then (ring_0 f,ring_neg f (ring_1 f))
    else ring_mul f c (ring_div f x y),
         ring_div f (ring_sub f x (ring_of_num f 1))
                    (ring_add f x (ring_of_num f 1))`;;

(* ------------------------------------------------------------------------- *)
(* Curve mapping interactions, in particular with respect to singularity.    *)
(* ------------------------------------------------------------------------- *)

let ECURVE_OF_MCURVE_OF_ECURVE = prove
 (`!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f) /\
        ~(a = d)
        ==> ecurve_of_mcurve (mcurve_of_ecurve (f,a,d) c) c = (f,a,d)`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[mcurve_of_ecurve; ecurve_of_mcurve; PAIR_EQ] THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let MCURVE_OF_ECURVE_OF_MCURVE = prove
 (`!f A B c:A.
        field f /\ ~(ring_char f = 2) /\
        A IN ring_carrier f /\ B IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f) /\
        ~(B = ring_0 f)
        ==> mcurve_of_ecurve (ecurve_of_mcurve (f,A,B) c) c = (f,A,B)`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[mcurve_of_ecurve; ecurve_of_mcurve; PAIR_EQ] THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ = prove
 (`!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f)
        ==> (montgomery_strongly_nonsingular(mcurve_of_ecurve(f,a,d) c) <=>
             ~(?z. z IN ring_carrier f /\ ring_pow f z 2 = ring_mul f a d))`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[montgomery_strongly_nonsingular; mcurve_of_ecurve] THEN
  MATCH_MP_TAC(TAUT
   `!p'. (p' <=> p) /\ (p' ==> r) /\ (~p' ==> (q <=> r))
         ==> (~p /\ ~q <=> ~r)`) THEN
  EXISTS_TAC `a:A = d` THEN REPEAT CONJ_TAC THENL
   [FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC;
    ASM_MESON_TAC[RING_POW_2];
    DISCH_TAC] THEN
  EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC
     `ring_mul f (z:A) (ring_div f (ring_sub f a d) (ring_of_num f 4))`;
    EXISTS_TAC
     `ring_mul f (z:A) (ring_div f (ring_of_num f 4) (ring_sub f a d) )`] THEN
  REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let MCURVE_OF_ECURVE_NONSINGULAR_EQ = prove
 (`!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f)
        ==> (montgomery_nonsingular(mcurve_of_ecurve(f,a,d) c) <=>
             ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f))`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[montgomery_nonsingular; mcurve_of_ecurve] THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR = prove
 (`!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f) /\
        ~(a = ring_0 f) /\ ~(d = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> montgomery_strongly_nonsingular(mcurve_of_ecurve(f,a,d) c)`,
  SIMP_TAC[MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ] THEN
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[edwards_nonsingular; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b:A` THEN DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[CONTRAPOS_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN EXISTS_TAC `ring_div f z b:A` THEN
   REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let MCURVE_OF_ECURVE_NONSINGULAR = prove
 (`!f a d c:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        c IN ring_carrier f /\ ~(c = ring_0 f) /\
        ~(a = ring_0 f) /\ ~(d = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> montgomery_nonsingular(mcurve_of_ecurve(f,a,d) c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mcurve_of_ecurve] THEN
  MATCH_MP_TAC MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR THEN
  REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
  REWRITE_TAC[GSYM mcurve_of_ecurve] THEN
  MATCH_MP_TAC MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Interrelations of the mappings themselves.                                *)
(* ------------------------------------------------------------------------- *)

let MONTGOMERY_OF_EDWARDS = prove
 (`!f (a:A) d c p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(c = ring_0 f) /\
        edwards_curve(f,a,d) p
        ==> montgomery_curve (mcurve_of_ecurve(f,a,d) c)
                             (montgomery_of_edwards f c p)`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:A ring`; `a:A`; `d:A`; `c:A`; `x:A`; `y:A`] THEN
  REWRITE_TAC[edwards_curve; mcurve_of_ecurve; montgomery_of_edwards] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_CASES_TAC `x:A = ring_0 f` THEN
  ASM_REWRITE_TAC[montgomery_curve] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[montgomery_curve] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[montgomery_curve] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC;
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC]);;

let EDWARDS_OF_MONTGOMERY_OF_EDWARDS = prove
 (`!(f:A ring) a d c p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(c = ring_0 f) /\
        edwards_curve(f,a,d) p
        ==> edwards_of_montgomery f c (montgomery_of_edwards f c p) = p`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:A ring`;`a:A`; `d:A`; `c:A`; `x:A`; `y:A`] THEN
  REWRITE_TAC[edwards_curve; montgomery_of_edwards; PAIR_EQ] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `x:A = ring_0 f` THEN
  ASM_REWRITE_TAC[edwards_of_montgomery] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[edwards_of_montgomery] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[edwards_of_montgomery] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN FIELD_TAC;
    REWRITE_TAC[PAIR_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC]);;

let EDWARDS_OF_MONTGOMERY = prove
 (`!f (A:A) B c p.
        field f /\ ~(ring_char f = 2) /\
        A IN ring_carrier f /\ B IN ring_carrier f /\ c IN ring_carrier f /\
        ~(B = ring_0 f) /\ ~(c = ring_0 f) /\
        montgomery_strongly_nonsingular(f,A,B) /\
        edwards_nonsingular(ecurve_of_mcurve(f,A,B) c) /\
        montgomery_curve(f,A,B) p
        ==> edwards_curve (ecurve_of_mcurve(f,A,B) c)
                          (edwards_of_montgomery f c p)`,
  MAP_EVERY X_GEN_TAC [`f:A ring`; `A:A`; `B:A`; `c:A`] THEN
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[edwards_curve; ecurve_of_mcurve; edwards_of_montgomery] THEN
    REWRITE_TAC[montgomery_curve] THEN REPEAT STRIP_TAC THEN
    TRY RING_CARRIER_TAC THEN FIELD_TAC;
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`]] THEN
  REWRITE_TAC[montgomery_curve; edwards_of_montgomery; PAIR_EQ] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[edwards_curve; ecurve_of_mcurve] THENL
   [REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL [RING_CARRIER_TAC; ALL_TAC]) THEN
  ASM_CASES_TAC `y:A = ring_0 f` THENL
   [MP_TAC(ISPECL [`f:A ring`; `A:A`; `B:A`]
     MONTGOMERY_STRONGLY_NONSINGULAR) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[DIVIDES_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_REWRITE_TAC[montgomery_curve] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM])] THEN
  ASM_CASES_TAC `x:A = ring_neg f (ring_1 f)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`);
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[edwards_nonsingular; ecurve_of_mcurve]) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  CONJ_TAC THENL [FIELD_TAC; ALL_TAC] THEN
  EXISTS_TAC `ring_div f y c:A` THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
  NOT_RING_CHAR_DIVIDES_TAC);;

let MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY = prove
 (`!f (A:A) B c p.
        field f /\ ~(ring_char f = 2) /\
        A IN ring_carrier f /\ B IN ring_carrier f /\ c IN ring_carrier f /\
        ~(B = ring_0 f) /\ ~(c = ring_0 f) /\
        montgomery_strongly_nonsingular(f,A,B) /\
        edwards_nonsingular(ecurve_of_mcurve(f,A,B) c) /\
        montgomery_curve(f,A,B) p
        ==> montgomery_of_edwards f c (edwards_of_montgomery f c p) = p`,
  MAP_EVERY X_GEN_TAC [`f:A ring`; `A:A`; `B:A`; `c:A`] THEN
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; montgomery_curve] THEN
  REWRITE_TAC[edwards_of_montgomery; montgomery_of_edwards; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[montgomery_of_edwards; PAIR_EQ;
                         option_DISTINCT; option_INJ])
  THENL [FIELD_TAC; FIELD_TAC; FIELD_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `y:A = ring_0 f` THENL
   [MP_TAC(ISPECL [`f:A ring`; `A:A`; `B:A`]
     MONTGOMERY_STRONGLY_NONSINGULAR) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[DIVIDES_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_REWRITE_TAC[montgomery_curve] THEN FIELD_TAC;
    FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM])] THEN
  ASM_CASES_TAC `x:A = ring_neg f (ring_1 f)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`);
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[edwards_nonsingular; ecurve_of_mcurve]) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  CONJ_TAC THENL [FIELD_TAC; ALL_TAC] THEN
  EXISTS_TAC `ring_div f y c:A` THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
  NOT_RING_CHAR_DIVIDES_TAC);;

(* ------------------------------------------------------------------------- *)
(* Group isomorphisms                                                        *)
(* ------------------------------------------------------------------------- *)

let MONTGOMERY_OF_EDWARDS_NEG = prove
 (`!f (a:A) d c p.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        edwards_curve(f,a,d) p
        ==> montgomery_of_edwards f c (edwards_neg(f,a,d) p) =
            montgomery_neg (mcurve_of_ecurve(f,a,d) c)
                           (montgomery_of_edwards f c p)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:A ring`; `a:A`; `d:A`; `c:A`; `x:A`; `y:A`] THEN
  REWRITE_TAC[edwards_curve; mcurve_of_ecurve; montgomery_of_edwards] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_CASES_TAC `x:A = ring_0 f` THEN
  ASM_REWRITE_TAC[edwards_neg; montgomery_of_edwards] THEN
  ASM_SIMP_TAC[PAIR_EQ; RING_NEG_EQ_0; RING_0] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[montgomery_neg]) THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; montgomery_neg] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC);;

let GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP = prove
 (`!f (a:A) d c.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> group_isomorphisms (edwards_group(f,a,d),
                                montgomery_group(mcurve_of_ecurve(f,a,d) c))
                               (montgomery_of_edwards f c,
                                edwards_of_montgomery f c)`,
  let isolemma = prove
   (`!(G:A group) (H:B group) f g z.
          abelian_group G /\ abelian_group H /\
          z IN group_carrier G /\ ~(z = group_id G) /\
          (!x. x IN group_carrier G
               ==> f(x) IN group_carrier H /\ g(f x) = x) /\
          (!y. y IN group_carrier H
               ==> g(y) IN group_carrier G /\ f(g y) = y) /\
          f(group_id G) = group_id H /\
          (!x. x IN group_carrier G ==> f(group_inv G x) = group_inv H (f x)) /\
          (!x. x IN group_carrier G
               ==> f(group_mul G z x) = group_mul H (f z) (f x)) /\
          (!u v w. u IN group_carrier G /\ ~(u = group_id G) /\ ~(u = z) /\
                   v IN group_carrier G /\ ~(v = group_id G) /\ ~(v = z) /\
                   w IN group_carrier G /\ ~(w = group_id G) /\ ~(w = z) /\
                   group_mul G u v = w /\
                   ~(f v = f u) /\ ~(group_inv H (f v) = f u)
                   ==> group_mul H (f u) (f v) = f w)
          ==> group_isomorphisms (G,H) (f,g)`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GROUP_ISOMORPHISMS] THEN
    ASM_SIMP_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
    SUBGOAL_THEN
     `!x y. x IN group_carrier G /\ y IN group_carrier G /\ ~(x = y)
            ==> (f:A->B) (group_mul G x y) = group_mul H (f x) (f y)`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `x:A = group_id G` THENL
       [ASM_SIMP_TAC[GROUP_MUL_LID]; ALL_TAC] THEN
      ASM_CASES_TAC `x:A = z` THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `y:A = group_id G` THENL
       [ASM_SIMP_TAC[GROUP_MUL_RID]; ALL_TAC] THEN
      ASM_CASES_TAC `y:A = z` THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[abelian_group]) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `group_mul G x y:A = group_id G` THENL
       [ASM_REWRITE_TAC[] THEN  ASM_MESON_TAC[GROUP_RULE
         `group_id G = group_mul G a b <=> group_inv G b = a`];
        ALL_TAC] THEN
      ASM_CASES_TAC `group_mul G x y:A = z` THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN POP_ASSUM MP_TAC THEN
        ASM_SIMP_TAC[GROUP_INV; GROUP_RULE
          `group_mul G x y = z <=> x = group_mul G z (group_inv G y)`];
        ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[GROUP_MUL] THEN
      UNDISCH_TAC `~(group_mul G x y:A = group_id G)` THEN
      ASM_SIMP_TAC[GSYM GROUP_RINV_EQ] THEN ASM_MESON_TAC[GROUP_INV];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:A = y` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_THEN `x:A = y` (SUBST_ALL_TAC o SYM) THEN
    ASM_CASES_TAC `x:A = z` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `(f:A->B) (group_mul G (group_mul G z x) x) =
      group_mul H (f(group_mul G z x)) (f x)`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[GROUP_LID_EQ; GROUP_MUL];
      ASM_SIMP_TAC[GSYM GROUP_MUL_ASSOC; GROUP_MUL]] THEN
    ASM_SIMP_TAC[GROUP_MUL_LCANCEL; GROUP_MUL]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC isolemma THEN
  EXISTS_TAC `ring_0 f:A,ring_neg f (ring_1 f)` THEN
  ASM_SIMP_TAC[ABELIAN_EDWARDS_GROUP; EDWARDS_GROUP] THEN
  MP_TAC(ISPECL (striplist dest_pair (rand(concl mcurve_of_ecurve)))
                MONTGOMERY_GROUP) THEN
  MP_TAC(ISPECL (striplist dest_pair (rand(concl mcurve_of_ecurve)))
                ABELIAN_MONTGOMERY_GROUP) THEN
  ASM_REWRITE_TAC[GSYM mcurve_of_ecurve] THEN MATCH_MP_TAC(TAUT
   `p /\ (q /\ r ==> s) ==> (p ==> q) ==> (p ==> r) ==> s`) THEN
  CONJ_TAC THENL
   [REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
    MATCH_MP_TAC MCURVE_OF_ECURVE_NONSINGULAR THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  UNDISCH_TAC `~(ring_char(f:A ring) = 2)` THEN
  ASM_SIMP_TAC[GSYM RING_CHAR_DIVIDES_PRIME; PRIME_2] THEN DISCH_TAC THEN
  REWRITE_TAC[SET_RULE `x IN edwards_curve C <=> edwards_curve C x`] THEN
  REWRITE_TAC[SET_RULE `y IN montgomery_curve C <=> montgomery_curve C y`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[edwards_curve] THEN REPEAT CONJ_TAC THEN
    TRY RING_CARRIER_TAC THEN FIELD_TAC;
    REWRITE_TAC[edwards_0; PAIR_EQ] THEN FIELD_TAC;
    ASM_MESON_TAC[EDWARDS_OF_MONTGOMERY_OF_EDWARDS; MONTGOMERY_OF_EDWARDS;
                  RING_CHAR_DIVIDES_PRIME; PRIME_2];
    MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `c:A`]
        ECURVE_OF_MCURVE_OF_ECURVE) THEN
    ASM_SIMP_TAC[GSYM RING_CHAR_DIVIDES_PRIME; PRIME_2] THEN DISCH_TAC THEN
    GEN_TAC THEN REWRITE_TAC[mcurve_of_ecurve] THEN REPEAT STRIP_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        (REWRITE_RULE[CONJ_ASSOC] EDWARDS_OF_MONTGOMERY)));
      FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        (REWRITE_RULE[CONJ_ASSOC] MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY)))] THEN
    DISCH_THEN(MP_TAC o SPEC `c:A`) THEN
    ASM_REWRITE_TAC[GSYM mcurve_of_ecurve] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR;
                 GSYM RING_CHAR_DIVIDES_PRIME; PRIME_2] THEN
    REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
    FIRST_X_ASSUM(K ALL_TAC o SYM) THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC;
    REWRITE_TAC[montgomery_of_edwards; edwards_0];
    ASM_SIMP_TAC[MONTGOMERY_OF_EDWARDS_NEG];
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x2:A`; `y2:A`] THEN
    REWRITE_TAC[PAIR_EQ; edwards_curve] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[montgomery_of_edwards; PAIR_EQ] THEN
    ASM_CASES_TAC `ring_neg f (ring_1 f):A = ring_1 f` THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN FIELD_TAC;
      ASM_REWRITE_TAC[]] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[edwards_add; montgomery_add; montgomery_of_edwards;
                mcurve_of_ecurve] THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_0; RING_1; RING_NEG; RING_MUL_RZERO;
                 RING_ADD_LZERO; RING_ADD_RZERO; RING_MUL_LID; RING_MUL_RID;
                 RING_MUL; RING_DIV_1; RING_SUB_RZERO; PAIR_EQ;
                 FIELD_MUL_EQ_0; RING_NEG_EQ_0; RING_MUL_LNEG;
                 RING_MUL_RNEG; RING_NEG_NEG] THEN
    ASM_SIMP_TAC[RING_NEG_EQ; RING_1; RING_RULE
     `ring_neg f y = ring_1 f <=> y = ring_neg f (ring_1 f)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[montgomery_add] THEN
    COND_CASES_TAC THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN
      FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[RING_1; RING_RULE
     `ring_add f x (ring_neg f y) = ring_sub f x y /\
      ring_sub f x (ring_neg f y) = ring_add f x y`] THEN
    SUBGOAL_THEN
     `~(x2:A = ring_0 f) /\
      ~(ring_sub f (ring_1 f) y2 = ring_0 f) /\
      ~(ring_add f (ring_1 f) y2 = ring_0 f) /\
      ~(ring_sub f a d = ring_0 f)`
    STRIP_ASSUME_TAC THENL
     [FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC;
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o
         GEN_REWRITE_RULE I [DE_MORGAN_THM]))] THEN
    REPLICATE_TAC 3
     (RING_PULL_DIV_TAC THEN CONV_TAC(RAND_CONV let_CONV)) THEN
    REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    RING_PULL_DIV_TAC THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`; `x3:A`; `y3:A`] THEN
  REWRITE_TAC[edwards_curve; edwards_0; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC
   `x1:A = ring_0 f \/ y1 = ring_1 f \/ y1 = ring_neg f (ring_1 f)`
  THENL
   [MATCH_MP_TAC(TAUT `p \/ q ==> ~p /\ ~q /\ r ==> s`) THEN FIELD_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC o
      REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC
   `x2:A = ring_0 f \/ y2 = ring_1 f \/ y2 = ring_neg f (ring_1 f)`
  THENL
   [MATCH_MP_TAC(TAUT `p \/ q ==> ~p /\ ~q /\ r ==> s`) THEN FIELD_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC o
      REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC
   `x3:A = ring_0 f \/ y3 = ring_1 f \/ y3 = ring_neg f (ring_1 f)`
  THENL
   [MATCH_MP_TAC(TAUT `p \/ q ==> ~p /\ ~q /\ r ==> s`) THEN FIELD_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC o
      REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `p3 = montgomery_of_edwards f (c:A) (x3,y3)` THEN
  ABBREV_TAC `p2 = montgomery_of_edwards f (c:A) (x2,y2)` THEN
  ABBREV_TAC `p1 = montgomery_of_edwards f (c:A) (x1,y1)` THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `c:A`] MONTGOMERY_OF_EDWARDS) THEN
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    MP_TAC(end_itlist CONJ
        (map (fun t -> SPEC t th)
             [`x1:A,y1:A`; `x2:A,y2:A`; `x3:A,y3:A`]))) THEN
  ASM_REWRITE_TAC[edwards_curve] THEN
  REPLICATE_TAC 3 (POP_ASSUM MP_TAC) THEN
  REPLICATE_TAC 2 (ONCE_REWRITE_TAC[IMP_IMP]) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
    [`p3:(A#A)option`; `p2:(A#A)option`; `p1:(A#A)option`] THEN
  ASM_REWRITE_TAC[montgomery_of_edwards; PAIR_EQ] THEN
  REWRITE_TAC[FORALL_OPTION_THM; option_DISTINCT] THEN
  REWRITE_TAC[FORALL_PAIR_THM; option_INJ; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`u1:A`; `v1:A`; `u2:A`; `v2:A`; `u3:A`; `v3:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(u1:A) IN ring_carrier f /\ (v1:A) IN ring_carrier f /\
    (u2:A) IN ring_carrier f /\ (v2:A) IN ring_carrier f /\
    (u3:A) IN ring_carrier f /\ (v3:A) IN ring_carrier f`
  STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN RING_CARRIER_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul f (ring_div f c x1) u1:A = v1 /\
    ring_mul f (ring_div f c x2) u2:A = v2 /\
    ring_mul f (ring_div f c x3) u3:A = v3`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(fun th ->
       GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    ASM_SIMP_TAC[ring_div; RING_INV_MUL; RING_INV; RING_POW;
                 RING_MUL; RING_SUB; RING_1] THEN
    RING_TAC THEN REPEAT CONJ_TAC THEN RING_CARRIER_TAC;
    MAP_EVERY (fun t -> FIRST_X_ASSUM
     (K ALL_TAC o check (fun eq -> is_eq eq && rand eq = t) o concl))
     [`v1:A`; `v2:A`; `v3:A`] THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[montgomery_curve; mcurve_of_ecurve] THEN
  MAP_EVERY ABBREV_TAC
   [`A:A = ring_div f (ring_mul f (ring_of_num f 2) (ring_add f a d))
                      (ring_sub f a d)`;
    `B:A = ring_div f (ring_div f (ring_of_num f 4) (ring_sub f a d))
                      (ring_pow f c 2)`] THEN
  SUBGOAL_THEN `(A:A) IN ring_carrier f /\ B IN ring_carrier f`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RING_CARRIER_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  REWRITE_TAC[edwards_add; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPECL
   [`f:A ring`; `a:A`; `d:A`; `x1:A`; `y1:A`; `x2:A`; `y2:A`]
   EDWARDS_NONSINGULAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[edwards_curve; PAIR_EQ] THEN STRIP_TAC THEN
  REWRITE_TAC[montgomery_neg; option_INJ; PAIR_EQ] THEN
  ASM_CASES_TAC `u1:A = u2` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; INTEGRAL_DOMAIN_RULE
     `~(x = y) /\ ~(ring_neg f x = y) <=>
      ~(ring_pow f x 2 = ring_pow f y 2)`] THEN
    MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[IMP_IMP] (INTEGRAL_DOMAIN_RULE
     `~(a = ring_0 f) /\ ring_mul f a x = ring_mul f a y ==> x = y`))) THEN
    MAP_EVERY EXISTS_TAC [`f:A ring`; `B:A`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[ring_div] THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 8)
     [FIELD_MUL_EQ_0; FIELD_INV_EQ_0; FIELD_POW_EQ_0; RING_CLAUSES] THEN
    ASM_SIMP_TAC[RING_SUB_EQ_0; RING_OF_NUM_EQ_0] THEN
    NOT_RING_CHAR_DIVIDES_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[montgomery_add] THEN LET_TAC THEN
  SUBGOAL_THEN `(l:A) IN ring_carrier f` ASSUME_TAC THENL
   [RING_CARRIER_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ; option_INJ] THEN
  ASM_SIMP_TAC[RING_POW_2] THEN
  SUBGOAL_THEN `~(ring_sub f u2 u1:A = ring_0 f)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_SUB_EQ_0]; ALL_TAC] THEN
  EXPAND_TAC "l" THEN RING_PULL_DIV_TAC THEN
  SUBGOAL_THEN `~(ring_sub f a d:A = ring_0 f)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_SUB_EQ_0]; ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["A"; "B"] THEN RING_PULL_DIV_TAC THEN
  MAP_EVERY EXPAND_TAC ["v1"; "v2"; "v3"] THEN RING_PULL_DIV_TAC THEN
  SUBGOAL_THEN
   `~(ring_sub f (ring_1 f) y1:A = ring_0 f) /\
    ~(ring_sub f (ring_1 f) y2:A = ring_0 f) /\
    ~(ring_sub f (ring_1 f) y3:A = ring_0 f)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_SUB_EQ_0; RING_1]; ALL_TAC] THEN
  EXPAND_TAC "u1" THEN RING_PULL_DIV_TAC THEN
  EXPAND_TAC "u2" THEN RING_PULL_DIV_TAC THEN
  EXPAND_TAC "u3" THEN RING_PULL_DIV_TAC THEN
  EXPAND_TAC "x3" THEN RING_PULL_DIV_TAC THEN
  EXPAND_TAC "y3" THEN RING_PULL_DIV_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`ring_add f (ring_mul f a (ring_pow f x1 2)) (ring_pow f y1 2):A =
      ring_add f (ring_1 f)
      (ring_mul f d (ring_mul f (ring_pow f x1 2) (ring_pow f y1 2)))`;
    `ring_add f (ring_mul f a (ring_pow f x2 2)) (ring_pow f y2 2):A =
      ring_add f (ring_1 f)
      (ring_mul f d (ring_mul f (ring_pow f x2 2) (ring_pow f y2 2)))`] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o SYM)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o CONV_RULE(RAND_CONV SYM_CONV))) THEN
  RING_TAC);;

let MONTGOMERY_OF_EDWARDS_ADD = prove
 (`!f (a:A) d c p q.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) p /\
        edwards_curve(f,a,d) q
        ==> montgomery_of_edwards f c (edwards_add(f,a,d) p q) =
            montgomery_add (mcurve_of_ecurve(f,a,d) c)
                           (montgomery_of_edwards f c p)
                           (montgomery_of_edwards f c q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `c:A`]
    GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP) THEN
  ASM_REWRITE_TAC[GROUP_ISOMORPHISMS; GROUP_HOMOMORPHISM] THEN
  ASM_SIMP_TAC[EDWARDS_GROUP; IN] THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `d:A`; `c:A`]
    MCURVE_OF_ECURVE_NONSINGULAR) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[mcurve_of_ecurve] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   (REWRITE_RULE[CONJ_ASSOC] MONTGOMERY_GROUP))) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RING_CARRIER_TAC);;

let GROUP_ISOMORPHISMS_MONTGOMERY_EDWARDS_GROUP = prove
 (`!f (a:A) d c.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> group_isomorphisms (montgomery_group(mcurve_of_ecurve(f,a,d) c),
                                edwards_group(f,a,d))
                               (edwards_of_montgomery f c,
                                montgomery_of_edwards f c)`,
  ONCE_REWRITE_TAC[GROUP_ISOMORPHISMS_SYM] THEN
  ACCEPT_TAC GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP);;

let ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP = prove
 (`!f (a:A) d c.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> edwards_group(f,a,d) isomorphic_group
            montgomery_group(mcurve_of_ecurve(f,a,d) c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o
    MATCH_MP GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP) THEN
  MESON_TAC[GROUP_ISOMORPHISMS_IMP_ISOMORPHISM; isomorphic_group]);;

let ISOMORPHIC_MONTGOMERY_EDWARDS_GROUP = prove
 (`!f (a:A) d c.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\ c IN ring_carrier f /\
        ~(a = d) /\ ~(a = ring_0 f) /\ ~(d = ring_0 f) /\ ~(c = ring_0 f) /\
        edwards_nonsingular(f,a,d)
        ==> montgomery_group(mcurve_of_ecurve(f,a,d) c) isomorphic_group
            edwards_group(f,a,d)`,
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  MATCH_ACCEPT_TAC ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP);;
