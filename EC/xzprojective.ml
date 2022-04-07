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
