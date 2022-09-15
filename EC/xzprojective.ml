(* ========================================================================= *)
(* Projective coordinates, x = X / Z without y for Montgomery curves.        *)
(* ========================================================================= *)

needs "EC/montgomery.ml";;

(* ------------------------------------------------------------------------- *)
(* The representation is only relational as we throw away the y coordinate.  *)
(* ------------------------------------------------------------------------- *)

let montgomery_xz = define
 `(montgomery_xz (f:A ring) NONE (X,Z) <=>
        X IN ring_carrier f /\ Z IN ring_carrier f /\
        ~(X = ring_0 f) /\ Z = ring_0 f) /\
  (montgomery_xz f (SOME(x,y:A)) (X,Z) <=>
        X IN ring_carrier f /\ Z IN ring_carrier f /\
        ~(Z = ring_0 f) /\ ring_div f X Z = x)`;;

let MONTGOMERY_XZ_IN_CARRIER = prove
 (`!P X Z.
        montgomery_xz f P (X,Z)
        ==> X IN ring_carrier f /\ Z IN ring_carrier f`,
  SIMP_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; montgomery_xz]);;

(* ------------------------------------------------------------------------- *)
(* However, doubling and *differential* addition are calculable.             *)
(* ------------------------------------------------------------------------- *)

let montgomery_xzdouble = define
  `montgomery_xzdouble (f,a:A,b:A) (X,Z) =
        ring_pow f (ring_sub f (ring_pow f X 2) (ring_pow f Z 2)) 2,
        ring_mul f (ring_mul f (ring_of_num f 4) (ring_mul f X Z))
                   (ring_add f (ring_pow f X 2)
                   (ring_add f (ring_mul f a
                         (ring_mul f X Z)) (ring_pow f Z 2)))`;;

let montgomery_xzdiffadd = define
  `montgomery_xzdiffadd (f:A ring,a:A,b:A) (X,Z) (Xm,Zm) (Xn,Zn) =
        ring_mul f (ring_mul f (ring_of_num f 4) Z)
                   (ring_pow f (ring_sub f (ring_mul f Xm Xn)
                                           (ring_mul f Zm Zn)) 2),
        ring_mul f (ring_mul f (ring_of_num f 4) X)
                   (ring_pow f (ring_sub f (ring_mul f Xm Zn)
                                           (ring_mul f Xn Zm)) 2)`;;

let MONTGOMERY_XZDOUBLE = prove
 (`!f (a:A) b p q.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b) /\
        montgomery_curve(f,a,b) p /\
        montgomery_xz f p q
        ==> montgomery_xz f (montgomery_add(f,a,b) p p)
                            (montgomery_xzdouble(f,a,b) q)`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_curve; montgomery_add; montgomery_xz;
    GSYM DE_MORGAN_THM; montgomery_xzdouble; montgomery_nonsingular] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[COND_SWAP] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; montgomery_xz] THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let MONTGOMERY_XZDIFFADD = prove
 (`!f (a:A) b p q pm qm pn qn.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b) /\
        montgomery_curve(f,a,b) p /\
        montgomery_curve(f,a,b) pm /\
        montgomery_curve(f,a,b) pn /\
        montgomery_xz f p q /\
        montgomery_xz f pm qm /\
        montgomery_xz f pn qn /\
        ~(FST q = ring_0 f) /\ ~(SND q = ring_0 f) /\
        montgomery_add (f,a,b) pm (montgomery_neg (f,a,b) pn) = p
        ==> montgomery_xz f (montgomery_add(f,a,b) pm pn)
                            (montgomery_xzdiffadd(f,a,b) q qm qn)`,
  REWRITE_TAC[FIELD_CHAR_NOT23] THEN REPEAT GEN_TAC THEN ASM_CASES_TAC
   `p = montgomery_add (f,a:A,b) pm (montgomery_neg (f,a,b) pn)` THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN
  W(fun (asl,w) -> MAP_EVERY (fun t -> SPEC_TAC(t,t)) (frees w)) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[montgomery_curve; montgomery_add; montgomery_xz; montgomery_neg;
    LET_DEF; LET_END_DEF; montgomery_xzdiffadd; montgomery_nonsingular] THEN
  REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN
  REWRITE_TAC[COND_SWAP; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ; montgomery_add;
                   LET_DEF; LET_END_DEF; montgomery_xz]) THEN
  REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;

let MONTGOMERY_XZDOUBLE_GROUP = prove
 (`!f (a:A) b p n q.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b) /\
        p IN group_carrier (montgomery_group(f,a,b)) /\
        montgomery_xz f (group_pow (montgomery_group(f,a,b)) p n) q
        ==> montgomery_xz f (group_pow (montgomery_group(f,a,b)) p (2 * n))
                            (montgomery_xzdouble(f,a,b) q)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MULT_2; GROUP_POW_ADD] THEN
  ASM_SIMP_TAC[MONTGOMERY_GROUP] THEN
  MATCH_MP_TAC MONTGOMERY_XZDOUBLE THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP GROUP_POW) THEN
  ASM_SIMP_TAC[MONTGOMERY_GROUP] THEN REWRITE_TAC[IN]);;

let MONTGOMERY_XZDIFFADD_GROUP = prove
 (`!f (a:A) b p n q qm qn.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b) /\
        ~(FST q = ring_0 f) /\ ~(SND q = ring_0 f) /\
        p IN group_carrier (montgomery_group(f,a,b)) /\
        montgomery_xz f p q /\
        montgomery_xz f (group_pow (montgomery_group(f,a,b)) p (n + 1)) qm /\
        montgomery_xz f (group_pow (montgomery_group(f,a,b)) p n) qn
        ==> montgomery_xz f (group_pow (montgomery_group(f,a,b)) p (2 * n + 1))
                            (montgomery_xzdiffadd(f,a,b) q qm qn)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `2 * n + 1 = SUC n + n`] THEN
  ASM_SIMP_TAC[GROUP_POW_ADD] THEN
  MP_TAC(SPECL [`f:A ring`; `a:A`; `b:A`] MONTGOMERY_GROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o last o CONJUNCTS) THEN
  MATCH_MP_TAC MONTGOMERY_XZDIFFADD THEN EXISTS_TAC `p:(A#A)option` THEN
  ASM_REWRITE_TAC[ADD1] THEN
  MP_TAC(SPECL [`f:A ring`; `a:A`; `b:A`] MONTGOMERY_GROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])THEN
  ONCE_REWRITE_TAC[SET_RULE `group_carrier G x <=> x IN group_carrier G`] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `n + 1 = 1 + n`] THEN
  ASM_SIMP_TAC[GROUP_POW; GROUP_POW_ADD; GROUP_POW_1] THEN
  MATCH_MP_TAC(GROUP_RULE
   `group_mul G (group_mul G x y) (group_inv G y) = x`) THEN
  ASM_SIMP_TAC[GROUP_POW]);;

(* ------------------------------------------------------------------------- *)
(* A functional X coordinate mapping as used in the x25519 functions.        *)
(* ------------------------------------------------------------------------- *)

let montgomery_xmap = define
 `montgomery_xmap (f:A ring) NONE = ring_0 f /\
  montgomery_xmap f (SOME(x:A,y:A)) = x`;;

let MONTGOMERY_XZ_XMAP = prove
 (`!(f:A ring) P X.
        field f /\ X IN ring_carrier f /\ ~(X = ring_0 f)
        ==> (montgomery_xz f P (X,ring_1 f) <=> montgomery_xmap f P = X)`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  SIMP_TAC[montgomery_xz; montgomery_xmap; FIELD_NONTRIVIAL; RING_1] THEN
  SIMP_TAC[ring_div; RING_INV_1; RING_MUL_RID] THEN MESON_TAC[]);;

let MONTGOMERY_XMAP_EQ_0 = prove
 (`!(f:A ring) a b P.
      field f /\ ~(ring_char f = 2) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular (f,a,b) /\
      P IN group_carrier(montgomery_group(f,a,b))
      ==> (montgomery_xmap f P = ring_0 f <=>
           P = NONE \/ P = SOME(ring_0 f,ring_0 f))`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM; montgomery_xmap] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  SIMP_TAC[IMP_CONJ; MONTGOMERY_GROUP] THEN
  MAP_EVERY X_GEN_TAC [`f:A ring`; `a:A`; `b:A`; `x:A`; `y:A`] THEN
  REPLICATE_TAC 5 DISCH_TAC THEN REWRITE_TAC[IN] THEN
  ASM_CASES_TAC `x:A = ring_0 f` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[montgomery_curve] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
    [montgomery_nonsingular]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_neg o concl)) THEN FIELD_TAC);;

let MONTGOMERY_XMAP_EQ_0_POW = prove
 (`!(f:A ring) a b P n.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular (f,a,b) /\
        P IN group_carrier(montgomery_group(f,a,b)) /\
        montgomery_xmap f P = ring_0 f
        ==> montgomery_xmap f (group_pow (montgomery_group(f,a,b)) P n) =
            ring_0 f`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`f:A ring`; `a:A`; `b:A`] MONTGOMERY_XMAP_EQ_0) THEN
  ASM_SIMP_TAC[GROUP_POW] THEN DISCH_THEN(K ALL_TAC) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GROUP_POW_MONTGOMERY_TORSION] THENL
   [DISJ1_TAC; MESON_TAC[]] THEN
  W(MP_TAC o PART_MATCH (rator o rator o lhand) GROUP_POW_ID o
    rator o rator o lhand o snd) THEN
  ASM_SIMP_TAC[MONTGOMERY_GROUP]);;

(* ------------------------------------------------------------------------- *)
(* The y coordinate can be recovered from any nondegenerate addition (e.g.   *)
(* differential) where we know the y coordinate of one of the addends. This  *)
(* formula is from Okeya and Sakurai's paper in CHES 2001 (LNCS 2162, p129). *)
(*                                                                           *)
(* Suppose (x1,y1) + (x,y) = (x2,y2). Then                                   *)
(* y1 = ((x1 * x + 1) * (x1 + x + 2 * A) - 2 * A - (x1 - x)^2 * x2) /        *)
(*      (2 * B * y)                                                          *)
(* ------------------------------------------------------------------------- *)

let MONTGOMERY_ADD_YRECOVERY = prove
 (`!f a (b:A) x y x1 y1 x2 y2.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        montgomery_curve (f,a,b) (SOME(x,y)) /\ ~(y = ring_0 f) /\
        montgomery_curve (f,a,b) (SOME(x1,y1)) /\
        montgomery_add(f,a,b) (SOME(x,y)) (SOME(x1,y1)) = SOME(x2,y2)
        ==> y1 = ring_div f
                  (ring_sub f
                   (ring_sub f
                    (ring_mul f (ring_add f (ring_mul f x1 x) (ring_1 f))
                    (ring_add f x1
                      (ring_add f x (ring_mul f (ring_of_num f 2) a))))
                      (ring_mul f (ring_of_num f 2) a))
                     (ring_mul f (ring_pow f (ring_sub f x1 x) 2) x2))
                  (ring_mul f (ring_of_num f 2) (ring_mul f b y))`,
  REWRITE_TAC[FIELD_CHAR_NOT2] THEN
  REWRITE_TAC[montgomery_nonsingular] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[montgomery_curve; montgomery_add; LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]) THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  REPLICATE_TAC 2 (FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC);;
