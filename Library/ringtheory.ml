(* ========================================================================= *)
(* Simple formulation of rings (commutative, with 1) as type "(A)ring".      *)
(* ========================================================================= *)

needs "Library/binomial.ml";;
needs "Library/pocklington.ml";;
needs "Library/card.ml";;

(* ------------------------------------------------------------------------- *)
(* The basic type of rings.                                                  *)
(* ------------------------------------------------------------------------- *)

let ring_tybij =
  let eth = prove
   (`?s (z:A) w n a m.
          z IN s /\
          w IN s /\
          (!x. x IN s ==> n x IN s) /\
          (!x y. x IN s /\ y IN s ==> a x y IN s) /\
          (!x y. x IN s /\ y IN s ==> m x y IN s) /\
          (!x y. x IN s /\ y IN s ==> a x y = a y x) /\
          (!x y z. x IN s /\ y IN s /\ z IN s ==> a x (a y z) = a (a x y) z) /\
          (!x. x IN s ==> a z x = x) /\
          (!x. x IN s ==> a (n x) x = z) /\
          (!x y. x IN s /\ y IN s ==> m x y = m y x) /\
          (!x y z. x IN s /\ y IN s /\ z IN s ==> m x (m y z) = m (m x y) z) /\
          (!x. x IN s ==> m w x = x) /\
          (!x y z. x IN s /\ y IN s /\ z IN s
                   ==>  m x (a y z) = a (m x y) (m x z))`,
    MAP_EVERY EXISTS_TAC
     [`{ARB:A}`; `ARB:A`; `ARB:A`; `(\x. ARB):A->A`;
      `(\x y. ARB):A->A->A`; `(\x y. ARB):A->A->A`] THEN
    REWRITE_TAC[IN_SING] THEN MESON_TAC[]) in
  new_type_definition "ring" ("ring","ring_operations")
   (GEN_REWRITE_RULE DEPTH_CONV [EXISTS_UNPAIR_THM] eth);;

(* ------------------------------------------------------------------------- *)
(* The ring operations, primitive plus subtraction as a derived operation.   *)
(* ------------------------------------------------------------------------- *)

let ring_carrier = new_definition
 `(ring_carrier:(A)ring->A->bool) =
    \r. FST(ring_operations r)`;;

let ring_0 = new_definition
 `(ring_0:(A)ring->A) =
    \r. FST(SND(ring_operations r))`;;

let ring_1 = new_definition
 `(ring_1:(A)ring->A) =
    \r. FST(SND(SND(ring_operations r)))`;;

let ring_neg = new_definition
 `(ring_neg:(A)ring->A->A) =
    \r. FST(SND(SND(SND(ring_operations r))))`;;

let ring_add = new_definition
 `(ring_add:(A)ring->A->A->A) =
    \r. FST(SND(SND(SND(SND(ring_operations r)))))`;;

let ring_mul = new_definition
 `(ring_mul:(A)ring->A->A->A) =
    \r. SND(SND(SND(SND(SND(ring_operations r)))))`;;

let ring_sub = new_definition
 `ring_sub r x y = ring_add r x (ring_neg r y)`;;

let RINGS_EQ = prove
 (`!r r':A ring.
        r = r' <=>
        ring_carrier r = ring_carrier r' /\
        ring_0 r = ring_0 r' /\
        ring_1 r = ring_1 r' /\
        ring_neg r = ring_neg r' /\
        ring_add r = ring_add r' /\
        ring_mul r = ring_mul r'`,
  REWRITE_TAC[GSYM PAIR_EQ] THEN
  REWRITE_TAC[ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul] THEN
  MESON_TAC[CONJUNCT1 ring_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Ring properties and other elementary consequences.                        *)
(* ------------------------------------------------------------------------- *)

let RING_PROPERTIES = MATCH_MP
  (MESON[] `(!x. f(g x) = x) /\ (!y. P y <=> g(f y) = y) ==> !x. P(g x)`)
  ring_tybij;;

let RING_0 = prove
 (`!r:A ring. ring_0 r IN ring_carrier r`,
  REWRITE_TAC[ring_carrier; ring_0] THEN MESON_TAC[RING_PROPERTIES]);;

let RING_1 = prove
 (`!r:A ring. ring_1 r IN ring_carrier r`,
  REWRITE_TAC[ring_carrier; ring_1] THEN MESON_TAC[RING_PROPERTIES]);;

let RING_NEG = prove
 (`!r x:A. x IN ring_carrier r ==> ring_neg r x IN ring_carrier r`,
  REWRITE_TAC[ring_neg; ring_carrier] THEN MESON_TAC[RING_PROPERTIES]);;

let RING_ADD = prove
 (`!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
             ==> ring_add r x y IN ring_carrier r`,
  REWRITE_TAC[ring_add; ring_carrier] THEN MESON_TAC[RING_PROPERTIES]);;

let RING_SUB = prove
 (`!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
             ==> ring_sub r x y IN ring_carrier r`,
  SIMP_TAC[ring_sub; RING_ADD; RING_NEG]);;

let RING_MUL = prove
 (`!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
             ==> ring_mul r x y IN ring_carrier r`,
  REWRITE_TAC[ring_mul; ring_carrier] THEN MESON_TAC[RING_PROPERTIES]);;

let RING_ADD_SYM = prove
 (`!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
             ==> ring_add r x y = ring_add r y x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_add; ring_carrier] THEN
  MESON_TAC[RING_PROPERTIES]);;

let RING_MUL_SYM = prove
 (`!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
             ==> ring_mul r x y = ring_mul r y x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_mul; ring_carrier] THEN
  MESON_TAC[RING_PROPERTIES]);;

let RING_ADD_ASSOC = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> ring_add r x (ring_add r y z) = ring_add r (ring_add r x y) z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_add; ring_0; ring_carrier] THEN
  MESON_TAC[RING_PROPERTIES]);;

let RING_MUL_ASSOC = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> ring_mul r x (ring_mul r y z) = ring_mul r (ring_mul r x y) z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_mul; ring_carrier] THEN
  MESON_TAC[RING_PROPERTIES]);;

let RING_ADD_LDISTRIB = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==>  ring_mul r x (ring_add r y z) =
             ring_add r (ring_mul r x y) (ring_mul r x z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_add; ring_mul; ring_carrier] THEN
  MESON_TAC[RING_PROPERTIES]);;

let RING_ADD_RDISTRIB = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> ring_mul r (ring_add r x y) z =
            ring_add r (ring_mul r x z) (ring_mul r y z)`,
  MESON_TAC[RING_MUL_SYM; RING_ADD; RING_ADD_LDISTRIB]);;

let RING_ADD_LZERO = prove
 (`!r x:A. x IN ring_carrier r ==> ring_add r (ring_0 r) x = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_add; ring_0; ring_carrier] THEN
  MESON_TAC[RING_PROPERTIES]);;

let RING_ADD_RZERO = prove
 (`!r x:A. x IN ring_carrier r ==> ring_add r x (ring_0 r) = x`,
  MESON_TAC[RING_ADD_SYM; RING_0; RING_ADD_LZERO]);;

let RING_MUL_LID = prove
 (`!r x:A. x IN ring_carrier r ==> ring_mul r (ring_1 r) x = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_mul; ring_1; ring_carrier] THEN
  MESON_TAC[RING_PROPERTIES]);;

let RING_MUL_RID = prove
 (`!r x:A. x IN ring_carrier r ==> ring_mul r x (ring_1 r) = x`,
  MESON_TAC[RING_MUL_SYM; RING_1; RING_MUL_LID]);;

let RING_ADD_LNEG = prove
 (`!r x:A. x IN ring_carrier r ==> ring_add r (ring_neg r x) x = ring_0 r`,
  REWRITE_TAC[ring_add; ring_neg; ring_0; ring_carrier] THEN
  MESON_TAC[RING_PROPERTIES]);;

let RING_ADD_RNEG = prove
 (`!r x:A. x IN ring_carrier r ==> ring_add r x (ring_neg r x) = ring_0 r`,
  MESON_TAC[RING_ADD_SYM; RING_NEG; RING_ADD_LNEG]);;

let RING_ADD_AC = prove
 (`!r:A ring.
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r
               ==> ring_add r x y = ring_add r y x) /\
        (!x y z. x IN ring_carrier r /\ y IN ring_carrier r /\
                 z IN ring_carrier r
                 ==> ring_add r (ring_add r x y) z =
                     ring_add r x (ring_add r y z)) /\
        (!x y z. x IN ring_carrier r /\ y IN ring_carrier r /\
                 z IN ring_carrier r
                 ==> ring_add r x (ring_add r y z) =
                     ring_add r y (ring_add r x z))`,
  MESON_TAC[RING_ADD_SYM; RING_ADD_ASSOC; RING_ADD]);;

let RING_MUL_AC = prove
 (`!r:A ring.
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r
               ==> ring_mul r x y = ring_mul r y x) /\
        (!x y z. x IN ring_carrier r /\ y IN ring_carrier r /\
                 z IN ring_carrier r
                 ==> ring_mul r (ring_mul r x y) z =
                     ring_mul r x (ring_mul r y z)) /\
        (!x y z. x IN ring_carrier r /\ y IN ring_carrier r /\
                 z IN ring_carrier r
                 ==> ring_mul r x (ring_mul r y z) =
                     ring_mul r y (ring_mul r x z))`,
  MESON_TAC[RING_MUL_SYM; RING_MUL_ASSOC; RING_MUL]);;

let RING_ADD_LCANCEL = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> (ring_add r x y = ring_add r x z <=> y = z)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\y:A. ring_add r (ring_neg r x) y`) THEN
  ASM_SIMP_TAC[RING_ADD_ASSOC; RING_NEG; RING_ADD_LNEG; RING_ADD_LZERO]);;

let RING_ADD_RCANCEL = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> (ring_add r x z = ring_add r y z <=> x = y)`,
  MESON_TAC[RING_ADD_SYM; RING_ADD_LCANCEL]);;

let RING_ADD_LCANCEL_IMP = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r /\
        ring_add r x y = ring_add r x z
        ==> y = z`,
  MESON_TAC[RING_ADD_LCANCEL]);;

let RING_ADD_RCANCEL_IMP = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r /\
        ring_add r x z = ring_add r y z
        ==> x = y`,
  MESON_TAC[RING_ADD_RCANCEL]);;

let RING_ADD_EQ_RIGHT = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_add r x y = y <=> x = ring_0 r)`,
  MESON_TAC[RING_ADD_RCANCEL; RING_NEG; RING_0; RING_ADD_LZERO]);;

let RING_ADD_EQ_LEFT = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_add r x y = x <=> y = ring_0 r)`,
  MESON_TAC[RING_ADD_EQ_RIGHT; RING_ADD_SYM]);;

let RING_LZERO_UNIQUE = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ ring_add r x y = y
        ==> x = ring_0 r`,
  MESON_TAC[RING_ADD_EQ_RIGHT]);;

let RING_RZERO_UNIQUE = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ ring_add r x y = x
        ==> y = ring_0 r`,
  MESON_TAC[RING_ADD_EQ_LEFT]);;

let RING_ADD_EQ_0 = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_add r x y = ring_0 r <=> ring_neg r x = y)`,
  MESON_TAC[RING_ADD_LCANCEL; RING_NEG; RING_0; RING_ADD_RNEG]);;

let RING_LNEG_UNIQUE = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ ring_add r x y = ring_0 r
        ==> ring_neg r x = y`,
  MESON_TAC[RING_ADD_EQ_0]);;

let RING_RNEG_UNIQUE = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ ring_add r x y = ring_0 r
        ==> ring_neg r y = x`,
  MESON_TAC[RING_ADD_EQ_0; RING_ADD_SYM]);;

let RING_NEG_NEG = prove
 (`!r x:A. x IN ring_carrier r ==> ring_neg r (ring_neg r x) = x`,
  ASM_MESON_TAC[RING_LNEG_UNIQUE; RING_NEG; RING_ADD_LNEG]);;

let RING_NEG_EQ_SWAP = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_neg r x = y <=> ring_neg r y = x)`,
  MESON_TAC[RING_NEG_NEG]);;

let RING_NEG_EQ = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_neg r x = ring_neg r y <=> x = y)`,
  MESON_TAC[RING_NEG_NEG]);;

let RING_NEG_0 = prove
 (`!r:A ring. ring_neg r (ring_0 r) = ring_0 r`,
  MESON_TAC[RING_LNEG_UNIQUE; RING_0; RING_ADD_RZERO]);;

let RING_NEG_EQ_0 = prove
 (`!r x:A.
        x IN ring_carrier r
        ==> (ring_neg r x = ring_0 r <=> x = ring_0 r)`,
  MESON_TAC[RING_NEG_NEG; RING_NEG_0]);;

let RING_MUL_LZERO = prove
 (`!r x:A. x IN ring_carrier r ==> ring_mul r (ring_0 r) x = ring_0 r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[RING_LZERO_UNIQUE]
   `(x:A) IN ring_carrier r /\ ring_add r x x = x ==> x = ring_0 r`) THEN
  ASM_SIMP_TAC[GSYM RING_ADD_RDISTRIB; RING_0; RING_MUL; RING_ADD_LZERO]);;

let RING_MUL_RZERO = prove
 (`!r x:A. x IN ring_carrier r ==> ring_mul r x (ring_0 r) = ring_0 r`,
  MESON_TAC[RING_MUL_LZERO; RING_MUL_SYM; RING_0]);;

let RING_MUL_LNEG = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_mul r (ring_neg r x) y = ring_neg r (ring_mul r x y)`,
  REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_LNEG_UNIQUE THEN
  ASM_SIMP_TAC[GSYM RING_ADD_RDISTRIB; RING_NEG; RING_MUL; RING_ADD_RNEG;
               RING_MUL_LZERO]);;

let RING_MUL_RNEG = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_mul r x (ring_neg r y) = ring_neg r (ring_mul r x y)`,
  MESON_TAC[RING_MUL_LNEG; RING_MUL_SYM; RING_NEG]);;

let RING_NEG_ADD = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_neg r (ring_add r x y) =
            ring_add r (ring_neg r x) (ring_neg r y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_LNEG_UNIQUE THEN
  ASM_SIMP_TAC[RING_ADD; RING_NEG] THEN
  TRANS_TAC EQ_TRANS
   `ring_add r (ring_add r y
      (ring_add r x (ring_neg r x))) (ring_neg r y):A` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[RING_ADD_ASSOC; RING_ADD_SYM; RING_NEG; RING_ADD];
    ASM_SIMP_TAC[RING_ADD_RNEG; RING_ADD_RZERO]]);;

let RING_SUB_REFL = prove
 (`!r x:A. x IN ring_carrier r ==> ring_sub r x x = ring_0 r`,
  SIMP_TAC[ring_sub; RING_ADD_RNEG]);;

let RING_SUB_LZERO = prove
 (`!r x:A. x IN ring_carrier r ==> ring_sub r (ring_0 r) x = ring_neg r x`,
  MESON_TAC[ring_sub; RING_0; RING_NEG; RING_ADD_LZERO]);;

let RING_SUB_RZERO = prove
 (`!r x:A. x IN ring_carrier r ==> ring_sub r x (ring_0 r) = x`,
  MESON_TAC[ring_sub; RING_NEG_0; RING_ADD_RZERO]);;

let RING_SUB_EQ_0 = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_sub r x y = ring_0 r <=> x = y)`,
  SIMP_TAC[ring_sub; RING_ADD_EQ_0; RING_NEG; RING_NEG_EQ]);;

let RING_SUB_LDISTRIB = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> ring_mul r x (ring_sub r y z) =
            ring_sub r (ring_mul r x y) (ring_mul r x z)`,
  SIMP_TAC[ring_sub; RING_MUL_RNEG; RING_ADD_LDISTRIB; RING_NEG]);;

let RING_SUB_RDISTRIB = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> ring_mul r (ring_sub r x y) z =
            ring_sub r (ring_mul r x z) (ring_mul r y z)`,
  MESON_TAC[RING_SUB_LDISTRIB; RING_MUL_SYM; RING_MUL; RING_SUB]);;

let RING_EQ_SUB_LADD = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> (x = ring_sub r y z <=> ring_add r x z = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_SIMP_TAC[ring_sub; GSYM RING_ADD_ASSOC; RING_NEG; RING_NEG_ADD;
               RING_ADD; RING_ADD_LNEG; RING_ADD_RNEG; RING_ADD_RZERO]);;

let RING_EQ_SUB_RADD = prove
 (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r
        ==> (ring_sub r x y = z <=> x = ring_add r z y)`,
  MESON_TAC[RING_EQ_SUB_LADD]);;

let RING_CARRIER_NONEMPTY = prove
 (`!r:A ring. ~(ring_carrier r = {})`,
  MESON_TAC[MEMBER_NOT_EMPTY; RING_0]);;

(* ------------------------------------------------------------------------- *)
(* Charaterizing trivial (zero) rings.                                       *)
(* ------------------------------------------------------------------------- *)

let trivial_ring = new_definition
 `trivial_ring r <=> ring_carrier r = {ring_0 r}`;;

let TRIVIAL_IMP_FINITE_RING = prove
 (`!r:A ring. trivial_ring r ==> FINITE(ring_carrier r)`,
  SIMP_TAC[trivial_ring; FINITE_SING]);;

let TRIVIAL_RING_SUBSET = prove
 (`!r:A ring. trivial_ring r <=> ring_carrier r SUBSET {ring_0 r}`,
  SIMP_TAC[trivial_ring; GSYM SUBSET_ANTISYM_EQ; SING_SUBSET; RING_0]);;

let TRIVIAL_RING = prove
 (`!r:A ring. trivial_ring r <=> ?a. ring_carrier r = {a}`,
  GEN_TAC THEN REWRITE_TAC[trivial_ring] THEN MATCH_MP_TAC(SET_RULE
   `c IN s ==> (s = {c} <=> ?a. s = {a})`) THEN
  REWRITE_TAC[RING_0]);;

let TRIVIAL_RING_ALT = prove
 (`!r:A ring. trivial_ring r <=> ?a. ring_carrier r SUBSET {a}`,
  REWRITE_TAC[TRIVIAL_RING; RING_CARRIER_NONEMPTY; SET_RULE
   `(?a. s = {a}) <=> (?a. s SUBSET {a}) /\ ~(s = {})`]);;

let TRIVIAL_RING_10 = prove
 (`!r:A ring. trivial_ring r <=> ring_1 r = ring_0 r`,
  REWRITE_TAC[trivial_ring; EXTENSION; IN_SING] THEN
  MESON_TAC[RING_1; RING_0; RING_MUL_LID; RING_MUL_LZERO]);;

let RING_CARRIER_HAS_SIZE_1 = prove
 (`!r:A ring. ring_carrier r HAS_SIZE 1 <=> trivial_ring r`,
  GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[TRIVIAL_RING]);;

let TRIVIAL_RING_HAS_SIZE_1 = prove
 (`!G:A ring. trivial_ring G <=> ring_carrier(G) HAS_SIZE 1`,
  REWRITE_TAC[RING_CARRIER_HAS_SIZE_1]);;

let RING_CARRIER_HAS_SIZE_2 = prove
 (`!r:A ring.
        ring_carrier r HAS_SIZE 2 <=>
        ~(trivial_ring r) /\
        ring_carrier r = {ring_0 r,ring_1 r}`,
  GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM]; ASM_MESON_TAC[TRIVIAL_RING_10]] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[TRIVIAL_RING] THEN ASM SET_TAC[];
    REWRITE_TAC[TRIVIAL_RING_10] THEN MP_TAC(ISPEC `r:A ring` RING_1) THEN
    MP_TAC(ISPEC `r:A ring` RING_0) THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The singleton ring, the trivial ring containing a given object.           *)
(* ------------------------------------------------------------------------- *)

let singleton_ring = new_definition
 `singleton_ring (a:A) = ring({a},a,a,(\x. a),(\x y. a),(\x y. a))`;;

let SINGLETON_RING = prove
 (`(!a:A. ring_carrier(singleton_ring a) = {a}) /\
   (!a:A. ring_0(singleton_ring a) = a) /\
   (!a:A. ring_1(singleton_ring a) = a) /\
   (!a:A. ring_neg(singleton_ring a) = \x. a) /\
   (!a:A. ring_add(singleton_ring a) = \x y. a) /\
   (!a:A. ring_mul(singleton_ring a) = \x y. a)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl singleton_ring)))))
   (CONJUNCT2 ring_tybij)))) THEN
  REWRITE_TAC[GSYM singleton_ring] THEN SIMP_TAC[IN_SING] THEN
  SIMP_TAC[ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul]);;

let TRIVIAL_RING_SINGLETON_RING = prove
 (`!a:A. trivial_ring(singleton_ring a)`,
  REWRITE_TAC[trivial_ring; SINGLETON_RING]);;

let FINITE_SINGLETON_RING = prove
 (`!a:A. FINITE(ring_carrier(singleton_ring a))`,
  SIMP_TAC[TRIVIAL_IMP_FINITE_RING; TRIVIAL_RING_SINGLETON_RING]);;

(* ------------------------------------------------------------------------- *)
(* Mapping natural numbers and integers into a ring in the obvious way.      *)
(* ------------------------------------------------------------------------- *)

let ring_of_num = new_recursive_definition num_RECURSION
 `ring_of_num r 0 = ring_0 r /\
  ring_of_num r (SUC n) = ring_add r (ring_of_num r n) (ring_1 r)`;;

let ring_of_int = new_definition
 `ring_of_int (r:A ring) n =
        if &0 <= n then ring_of_num r (num_of_int n)
        else ring_neg r (ring_of_num r (num_of_int(--n)))`;;

let RING_OF_NUM = prove
 (`!(r:A ring) n. ring_of_num r n IN ring_carrier r`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_of_num; RING_0; RING_1; RING_ADD]);;

let RING_OF_INT = prove
 (`!(r:A ring) n. ring_of_int r n IN ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_of_int] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[RING_NEG; RING_OF_NUM]);;

let RING_OF_INT_OF_NUM = prove
 (`!(r:A ring) n. ring_of_int r (&n) = ring_of_num r n`,
  REWRITE_TAC[ring_of_int; INT_POS; NUM_OF_INT_OF_NUM]);;

let RING_OF_NUM_0 = prove
 (`!r:A ring. ring_of_num r 0 = ring_0 r`,
  REWRITE_TAC[ring_of_num]);;

let RING_OF_NUM_1 = prove
 (`!r:A ring. ring_of_num r 1 = ring_1 r`,
  SIMP_TAC[num_CONV `1`; ring_of_num; RING_ADD_LZERO; RING_1]);;

let RING_OF_NUM_ADD = prove
 (`!(r:A ring) m n.
      ring_of_num r (m + n) = ring_add r (ring_of_num r m) (ring_of_num r n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ADD_CLAUSES; ring_of_num; RING_ADD_LZERO; RING_OF_NUM] THEN
  ASM_SIMP_TAC[RING_ADD_AC; RING_OF_NUM; RING_ADD; RING_0; RING_1]);;

let RING_OF_NUM_MUL = prove
 (`!(r:A ring) m n.
      ring_of_num r (m * n) = ring_mul r (ring_of_num r m) (ring_of_num r n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[MULT_CLAUSES; RING_OF_NUM_0; RING_MUL_LZERO; RING_OF_NUM] THEN
  ASM_REWRITE_TAC[RING_OF_NUM_ADD; ring_of_num] THEN
  SIMP_TAC[RING_ADD_RDISTRIB; RING_1; RING_OF_NUM; RING_MUL_LID]);;

let RING_OF_INT_0 = prove
 (`!r:A ring. ring_of_int r (&0) = ring_0 r`,
  REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_0]);;

let RING_OF_INT_1 = prove
 (`!r:A ring. ring_of_int r (&1) = ring_1 r`,
  REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_1]);;

let RING_OF_INT_CLAUSES = prove
 (`(!(r:A ring) n. ring_of_int r (&n) = ring_of_num r n) /\
   (!(r:A ring) n. ring_of_int r (-- &n) = ring_neg r (ring_of_num r n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RING_OF_INT_OF_NUM] THEN
  REWRITE_TAC[ring_of_int; INT_ARITH `&0:int <= -- &n <=> &n:int = &0`] THEN
  SIMP_TAC[INT_NEG_NEG; INT_OF_NUM_EQ; INT_NEG_0; NUM_OF_INT_OF_NUM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ring_of_num; RING_NEG_0]);;

let RING_OF_INT_NEG = prove
 (`!(r:A ring) n. ring_of_int r (--n) = ring_neg r (ring_of_int r n)`,
  SIMP_TAC[FORALL_INT_CASES; RING_OF_INT_CLAUSES; INT_NEG_NEG;
           RING_NEG_NEG; RING_OF_NUM]);;

let RING_OF_INT_ADD = prove
 (`!(r:A ring) m n.
      ring_of_int r (m + n) = ring_add r (ring_of_int r m) (ring_of_int r n)`,
  SUBGOAL_THEN
   `!(r:A ring) m n p.
        m + n = p ==>
      ring_of_int r p = ring_add r (ring_of_int r m) (ring_of_int r n)`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[FORALL_INT_CASES; RING_OF_INT_CLAUSES] THEN
  ONCE_REWRITE_TAC[INT_ARITH `--b + a:int = a + --b`] THEN
  REWRITE_TAC[GSYM INT_NEG_ADD; INT_NEG_EQ; INT_NEG_NEG] THEN
  REWRITE_TAC[INT_ARITH
   `(&a + &b:int = -- &c <=> &a:int = &0 /\ &b:int = &0 /\ &c:int = &0) /\
    (!m n p. m + --n:int = &p <=> m = n + &p) /\
    (!m n p. m + --n:int = -- &p <=> m + &p = n)`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhand o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[RING_OF_NUM_ADD; RING_OF_NUM_0] THEN
  SIMP_TAC[RING_NEG_0; RING_ADD_LZERO; RING_ADD_RZERO; RING_0] THEN
  SIMP_TAC[GSYM RING_NEG_ADD; RING_OF_NUM] THEN SIMP_TAC
   [RING_ADD; RING_OF_NUM; MESON[RING_ADD_SYM; RING_NEG]
     `!x y. x IN ring_carrier r /\ y IN ring_carrier r
         ==> ring_add r (ring_neg r x) y = ring_add r y (ring_neg r x)`] THEN
  REWRITE_TAC[GSYM ring_sub] THEN
  SIMP_TAC[RING_EQ_SUB_LADD; RING_OF_NUM; RING_ADD; RING_NEG] THEN
  TRY(SIMP_TAC[RING_ADD_AC; RING_OF_NUM] THEN NO_TAC) THEN
  MATCH_MP_TAC(MESON[RING_ADD_SYM]
   `x IN ring_carrier r /\ y IN ring_carrier r /\ ring_add r x y = z
    ==> ring_add r y x = z`) THEN
  SIMP_TAC[RING_NEG; RING_OF_NUM; RING_ADD] THEN
  SIMP_TAC[GSYM RING_ADD_ASSOC; RING_ADD; RING_NEG; RING_OF_NUM;
           RING_ADD_RNEG; RING_ADD_RZERO]);;

let RING_OF_INT_MUL = prove
 (`!(r:A ring) m n.
      ring_of_int r (m * n) = ring_mul r (ring_of_int r m) (ring_of_int r n)`,
  REWRITE_TAC[FORALL_INT_CASES; INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG] THEN
  REWRITE_TAC[RING_OF_INT_CLAUSES; INT_OF_NUM_MUL; RING_OF_NUM_MUL] THEN
  SIMP_TAC[RING_MUL_LNEG; RING_MUL_RNEG; RING_OF_NUM; RING_NEG;
           RING_NEG_NEG; RING_MUL]);;

let RING_OF_INT_SUB = prove
 (`!(r:A ring) m n.
      ring_of_int r (m - n) = ring_sub r (ring_of_int r m) (ring_of_int r n)`,
  SIMP_TAC[INT_SUB; ring_sub; RING_OF_INT_ADD; RING_OF_INT_NEG;
           RING_NEG; RING_OF_INT]);;

(* ------------------------------------------------------------------------- *)
(* Characteristic of a ring, characterized by RING_OF_NUM_EQ_0.              *)
(* ------------------------------------------------------------------------- *)

let RING_OF_NUM_EQ_0 =
  let eth = prove
   (`!r:A ring. ?p. !n. ring_of_num r n = ring_0 r <=> p divides n`,
    GEN_TAC THEN MATCH_MP_TAC(MESON[]
     `(~P 0 ==> ?n. ~(n = 0) /\ P n) ==> ?n. P n`) THEN
    REWRITE_TAC[NUMBER_RULE `0 divides n <=> n = 0`] THEN
    SIMP_TAC[NOT_FORALL_THM; RING_OF_NUM_0; TAUT
     `~(p <=> q) <=> ~q /\ p \/ ~(q ==> p)`] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN
    REWRITE_TAC[TAUT `p ==> ~(q /\ r) <=> q /\ p ==> ~r`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN EQ_TAC THEN
    SIMP_TAC[divides; LEFT_IMP_EXISTS_THM; RING_OF_NUM_MUL] THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_OF_NUM] THEN
    SUBST1_TAC(SYM(SPECL [`m:num`; `p:num`] (CONJUNCT2 DIVISION_SIMP))) THEN
    ASM_SIMP_TAC[RING_OF_NUM_ADD; RING_OF_NUM_MUL; RING_MUL_LZERO;
                 RING_OF_NUM; RING_ADD_LZERO] THEN
    DISCH_TAC THEN EXISTS_TAC `m DIV p` THEN REWRITE_TAC[EQ_ADD_LCANCEL_0] THEN
    ASM_MESON_TAC[DIVISION]) in
  new_specification ["ring_char"] (REWRITE_RULE[SKOLEM_THM] eth);;

let RING_CHAR_EQ_0 = prove
 (`!r:A ring. ring_char r = 0 <=> !n. ring_of_num r n = ring_0 r <=> n = 0`,
  REWRITE_TAC[RING_OF_NUM_EQ_0] THEN MESON_TAC[NUMBER_RULE
   `(!n:num. n divides n) /\ (!n. 0 divides n <=> n = 0)`]);;

let RING_CHAR_EQ_1 = prove
 (`!r:A ring. ring_char r = 1 <=> trivial_ring r`,
  REWRITE_TAC[TRIVIAL_RING_10; GSYM RING_OF_NUM_1; RING_OF_NUM_EQ_0] THEN
  NUMBER_TAC);;

let RING_OF_INT_EQ_0 = prove
 (`!(r:A ring) n.
        ring_of_int r n = ring_0 r <=> &(ring_char r) divides n`,
  REWRITE_TAC[FORALL_INT_CASES; RING_OF_INT_CLAUSES] THEN
  SIMP_TAC[RING_NEG_EQ_0; RING_OF_NUM; RING_OF_NUM_EQ_0] THEN
  REWRITE_TAC[num_divides] THEN REPEAT STRIP_TAC THEN
  CONV_TAC INTEGER_RULE);;

let RING_OF_INT_EQ = prove
 (`!(r:A ring) m n.
        ring_of_int r m = ring_of_int r n <=> (m == n) (mod &(ring_char r))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUB_EQ_0 o lhand o snd) THEN
  REWRITE_TAC[RING_OF_INT; GSYM RING_OF_INT_SUB] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_OF_INT_EQ_0] THEN
  CONV_TAC INTEGER_RULE);;

let RING_OF_NUM_EQ = prove
 (`!(r:A ring) m n.
        ring_of_num r m = ring_of_num r n <=> (m == n) (mod (ring_char r))`,
  REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT_EQ; num_congruent]);;

let RING_CHAR_INFINITE = prove
 (`!r:A ring. ring_char r = 0 ==> INFINITE(ring_carrier r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `ring_of_num r:num->A` INFINITE_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[RING_OF_NUM_EQ] THEN ANTS_TAC THENL
   [CONV_TAC NUMBER_RULE; DISCH_THEN(MP_TAC o SPEC `(:num)`)] THEN
  REWRITE_TAC[num_INFINITE] THEN  MATCH_MP_TAC
   (REWRITE_RULE[IMP_CONJ_ALT] INFINITE_SUPERSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RING_OF_NUM]);;

let RING_CHAR_FINITE = prove
 (`!r:A ring. FINITE(ring_carrier r) ==> ~(ring_char r = 0)`,
  MESON_TAC[RING_CHAR_INFINITE; INFINITE]);;

let RING_CHAR_UNIQUE = prove
 (`!(r:A ring) p.
        ring_char r = p <=> !n. ring_of_num r n = ring_0 r <=> p divides n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RING_OF_NUM_EQ_0] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DIVIDES_ANTISYM] THEN
  MESON_TAC[NUMBER_RULE `!n:num. n divides n`;
   NUMBER_RULE `!m n p:num. m divides n /\ n divides p ==> m divides p`]);;

(* ------------------------------------------------------------------------- *)
(* Natural number powers of a ring element.                                  *)
(* ------------------------------------------------------------------------- *)

let ring_pow = new_recursive_definition num_RECURSION
 `ring_pow r x 0 = ring_1 r /\
  ring_pow r x (SUC n) = ring_mul r x (ring_pow r x n)`;;

let RING_POW = prove
 (`!r (x:A) n. x IN ring_carrier r ==> ring_pow r x n IN ring_carrier r`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ring_pow; RING_1; RING_MUL]);;

let RING_POW_ZERO = prove
 (`!r k. ring_pow r (ring_0 r) k = if k = 0 then ring_1 r else ring_0 r`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; NOT_SUC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL_LZERO; RING_0; RING_1]);;

let RING_POW_0 = prove
 (`!r (x:A). ring_pow r x 0 = ring_1 r`,
  REWRITE_TAC[ring_pow]);;

let RING_POW_1 = prove
 (`!r x:A. x IN ring_carrier r ==> ring_pow r x 1 = x`,
  SIMP_TAC[num_CONV `1`; ring_pow; RING_MUL_RID]);;

let RING_POW_2 = prove
 (`!r x:A. x IN ring_carrier r ==> ring_pow r x 2 = ring_mul r x x`,
  SIMP_TAC[num_CONV `2`; num_CONV `1`; ring_pow; RING_MUL_RID]);;

let RING_POW_ONE = prove
 (`!n. ring_pow r (ring_1 r) n = ring_1 r`,
  INDUCT_TAC THEN ASM_SIMP_TAC[ring_pow; RING_1; RING_MUL_LID]);;

let RING_POW_ADD = prove
 (`!r (x:A) m n.
        x IN ring_carrier r
        ==> ring_pow r x (m + n) =
            ring_mul r (ring_pow r x m) (ring_pow r x n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_pow; ADD_CLAUSES; RING_POW; RING_MUL_LID] THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_POW]);;

let RING_POW_MUL = prove
 (`!r (x:A) m n.
        x IN ring_carrier r
        ==> ring_pow r x (m * n) = ring_pow r (ring_pow r x m) n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[RING_POW_0; MULT_CLAUSES] THEN
  ASM_SIMP_TAC[RING_POW_ADD; CONJUNCT2 ring_pow]);;

let RING_POW_POW = prove
 (`!G (x:A) m n.
        x IN ring_carrier G
        ==> ring_pow G (ring_pow G x m) n = ring_pow G x (m * n)`,
  SIMP_TAC[RING_POW_MUL]);;

let RING_MUL_POW = prove
 (`!r (x:A) (y:A) n.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_pow r (ring_mul r x y) n =
            ring_mul r (ring_pow r x n) (ring_pow r y n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_pow; RING_MUL_LID; RING_1] THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_MUL; RING_POW] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 ring_pow)] THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_MUL; RING_POW] THEN
  ASM_SIMP_TAC[ring_pow; RING_MUL_AC; RING_POW; RING_MUL]);;

let RING_OF_NUM_EXP = prove
 (`!(r:A ring) m n.
        ring_of_num r (m EXP n) = ring_pow r (ring_of_num r m) n`,
  GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; EXP; RING_OF_NUM_1] THEN
  ASM_REWRITE_TAC[RING_OF_NUM_MUL]);;

let RING_OF_INT_POW = prove
 (`!(r:A ring) x n.
        ring_of_int r (x pow n) = ring_pow r (ring_of_int r x) n`,
  GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; INT_POW; RING_OF_INT_1] THEN
  ASM_REWRITE_TAC[RING_OF_INT_MUL]);;

let RING_POW_NEG = prove
 (`!r (x:A) n.
        x IN ring_carrier r
        ==> ring_pow r (ring_neg r x) n =
            if EVEN n then ring_pow r x n else ring_neg r (ring_pow r x n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN SIMP_TAC[EVEN; ring_pow; COND_SWAP] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[RING_MUL_LNEG; RING_MUL_RNEG; RING_POW; RING_NEG; RING_MUL;
               RING_NEG_NEG]);;

let RING_POW_IDEMPOTENT = prove
 (`!r (x:A) n.
        x IN ring_carrier r /\ ring_mul r x x = x
        ==> ring_pow r x n = if n = 0 then ring_1 r else x`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; NOT_SUC] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Sum in a ring. The instantiation required is a little ugly since all      *)
(* the ITSET/iterate stuff is really designed for total operators.           *)
(* ------------------------------------------------------------------------- *)

let ring_sum = new_definition
 `ring_sum r s (f:K->A) =
        iterate (\x y. if x IN ring_carrier r /\ y IN ring_carrier r
                       then ring_add r x y
                       else if x IN ring_carrier r then y
                       else if y IN ring_carrier r then x
                       else @z:A. ~(z IN ring_carrier r))
                {x | x IN s /\ f(x) IN ring_carrier r} f`;;

let NEUTRAL_RING_ADD = prove
 (`!r:A ring.
        neutral (\x y. if x IN ring_carrier r /\ y IN ring_carrier r
                       then ring_add r x y
                       else if x IN ring_carrier r then y
                       else if y IN ring_carrier r then x
                       else @z. ~(z IN ring_carrier r)) = ring_0 r`,
  GEN_TAC THEN REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `ring_0 r:A`); DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[RING_0; RING_ADD_LZERO; RING_ADD_RZERO; COND_ID]);;

let MONOIDAL_RING_ADD = prove
 (`!r:A ring.
        monoidal (\x y. if x IN ring_carrier r /\ y IN ring_carrier r
                        then ring_add r x y
                        else if x IN ring_carrier r then y
                         else if y IN ring_carrier r then x
                        else @z. ~(z IN ring_carrier r))`,
  REWRITE_TAC[monoidal; NEUTRAL_RING_ADD] THEN
  SIMP_TAC[RING_0; RING_ADD_LZERO; COND_ID] THEN
  GEN_TAC THEN CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  TRY(X_GEN_TAC `z:A`) THEN
  MAP_EVERY ASM_CASES_TAC
   [`(x:A) IN ring_carrier r`; `(y:A) IN ring_carrier r`;
    `(z:A) IN ring_carrier r`] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[RING_ADD] THEN
  ASM_SIMP_TAC[RING_ADD_AC; RING_ADD] THEN ASM_MESON_TAC[]);;

let RING_SUM = prove
 (`!r s (f:K->A). ring_sum r s f IN ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_sum] THEN
  MATCH_MP_TAC
   (SIMP_RULE[NEUTRAL_RING_ADD; RING_0; RING_ADD]
     (ISPEC `\x:B. x IN ring_carrier r`
     (MATCH_MP ITERATE_CLOSED (ISPEC `r:C ring` MONOIDAL_RING_ADD)))) THEN
  SIMP_TAC[IN_ELIM_THM]);;

let RING_SUM_RESTRICT = prove
 (`!s f. ring_sum r {a | a IN s /\ f a IN ring_carrier r} f = ring_sum r s f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_sum] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let RING_SUM_SUPPORT = prove
 (`!s (f:K->A).
        ring_sum r {a | a IN s /\ ~(f a = ring_0 r)} f = ring_sum r s f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_sum] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_RING_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let RING_SUM_TRIVIAL = prove
 (`!r k (f:K->A).
        INFINITE {i | i IN k /\ f i IN ring_carrier r /\ ~(f i = ring_0 r)}
        ==> ring_sum r k f = ring_0 r`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM RING_SUM_SUPPORT] THEN
  REWRITE_TAC[ring_sum] THEN ONCE_REWRITE_TAC[iterate] THEN
  REWRITE_TAC[NEUTRAL_RING_ADD; support] THEN
  ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN
  REWRITE_TAC[GSYM INFINITE; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[TAUT `((p /\ q) /\ r) /\ q <=> p /\ r /\ q`]);;

let RING_SUM_CLAUSES = prove
 (`(!r f:K->A. ring_sum r {} f = ring_0 r) /\
   (!r x (f:K->A) s.
          FINITE s
          ==> ring_sum r (x INSERT s) f =
              (if f(x) IN ring_carrier r ==> x IN s
               then ring_sum r s f else ring_add r (f x) (ring_sum r s f)))`,
  REWRITE_TAC[ring_sum; SET_RULE `{x | x IN {} /\ P x} = {}`] THEN
  REWRITE_TAC[INSERT_RESTRICT] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[MATCH_MP ITERATE_CLAUSES (ISPEC `r:A ring` MONOIDAL_RING_ADD);
               NOT_IN_EMPTY; EMPTY_GSPEC; FINITE_RESTRICT] THEN
  ASM_REWRITE_TAC[NEUTRAL_RING_ADD; GSYM ring_sum; IN_ELIM_THM; RING_SUM]);;

let RING_SUM_SING = prove
 (`!r (f:K->A) a.
        ring_sum r {a} f = if f a IN ring_carrier r then f a else ring_0 r`,
  SIMP_TAC[RING_SUM_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY; COND_SWAP] THEN
  MESON_TAC[RING_ADD_RZERO]);;

let RING_SUM_CLAUSES_NUMSEG_ALT = prove
 (`(!r m f:num->A.
        ring_sum r (m..0) f =
        if m = 0 /\ f 0 IN ring_carrier r then f 0 else ring_0 r) /\
   (!r m n f:num->A.
        ring_sum r (m..SUC n) f =
        if m <= SUC n /\ f(SUC n) IN ring_carrier r
        then ring_add r (f(SUC n)) (ring_sum r (m..n) f)
        else ring_sum r (m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `m = 0`; ASM_CASES_TAC `m <= SUC n`] THEN
  ASM_REWRITE_TAC[RING_SUM_SING; CONJUNCT1 RING_SUM_CLAUSES] THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG; ARITH_RULE `~(SUC n <= n)`; COND_SWAP]);;

let RING_SUM_CLAUSES_NUMSEG = prove
 (`(!r m f:num->A.
        ring_sum r (m..0) f =
        if m = 0 /\ f 0 IN ring_carrier r then f 0 else ring_0 r) /\
   (!r m n f:num->A.
        ring_sum r (m..SUC n) f =
        if m <= SUC n /\ f(SUC n) IN ring_carrier r
        then ring_add r (ring_sum r (m..n) f) (f(SUC n))
        else ring_sum r (m..n) f)`,
  REWRITE_TAC[RING_SUM_CLAUSES_NUMSEG_ALT] THEN
  MESON_TAC[RING_SUM; RING_ADD_SYM]);;

let RING_SUM_CLAUSES_LEFT = prove
 (`!r (f:num->A) m n.
        m <= n
        ==> ring_sum r (m..n) f =
            if f m IN ring_carrier r
            then ring_add r (f m) (ring_sum r (m+1..n) f)
            else ring_sum r (m+1..n) f`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM NUMSEG_LREC; RING_SUM_CLAUSES; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG; ARITH_RULE `~(n + 1 <= n)`; COND_SWAP]);;

let RING_SUM_UNION = prove
 (`!r (f:K->A) s t.
        FINITE s /\ FINITE t /\ DISJOINT s t
        ==> ring_sum r (s UNION t) f =
            ring_add r (ring_sum r s f) (ring_sum r t f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sum; UNION_RESTRICT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_UNION
    (ISPEC `r:C ring` MONOIDAL_RING_ADD)) o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM ring_sum; RING_SUM]);;

let RING_SUM_DIFF = prove
 (`!r (f:K->A) s t.
        FINITE s /\ t SUBSET s
        ==> ring_sum r (s DIFF t) f =
            ring_sub r (ring_sum r s f) (ring_sum r t f)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[RING_EQ_SUB_LADD; RING_SUM] THEN
  SIMP_TAC[ring_sum; DIFF_RESTRICT] THEN
  W(MP_TAC o PART_MATCH (lhand o lhand o rand) (MATCH_MP ITERATE_DIFF
    (ISPEC `r:C ring` MONOIDAL_RING_ADD)) o lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ring_sum; RING_SUM; GSYM DIFF_RESTRICT]);;

let RING_SUM_INCL_EXCL = prove
 (`!r (f:K->A) s t.
        FINITE s /\ FINITE t
        ==> ring_add r (ring_sum r s f) (ring_sum r t f) =
            ring_add r (ring_sum r (s UNION t) f)
                       (ring_sum r (s INTER t) f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ring_sum; INTER_RESTRICT; UNION_RESTRICT] THEN
  W(MP_TAC o PART_MATCH (funpow 3 rand) (MATCH_MP ITERATE_INCL_EXCL
    (ISPEC `r:C ring` MONOIDAL_RING_ADD)) o rand o rand o snd) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  REWRITE_TAC[GSYM INTER_RESTRICT; GSYM UNION_RESTRICT] THEN
  REWRITE_TAC[GSYM ring_sum; RING_SUM]);;

let RING_SUM_CLOSED = prove
 (`!r P (f:K->A) s.
        P(ring_0 r) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_add r x y)) /\
        (!a. a IN s ==> P(f a))
        ==> P(ring_sum r s f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sum] THEN
  MP_TAC(ISPECL
   [`\x:A. x IN ring_carrier r /\ P x`;
    `f:K->A`; `{a | a IN s /\ (f:K->A) a IN ring_carrier r}`]
   (MATCH_MP (REWRITE_RULE[RIGHT_IMP_FORALL_THM] ITERATE_CLOSED)
             (ISPEC `r:C ring` MONOIDAL_RING_ADD))) THEN
  ASM_SIMP_TAC[NEUTRAL_RING_ADD; IMP_IMP; RING_0; RING_ADD; IN_ELIM_THM]);;

let RING_SUM_RELATED = prove
 (`!r R (f:K->A) g s.
        R (ring_0 r) (ring_0 r)/\
        (!x y x' y'. x IN ring_carrier r /\ y IN ring_carrier r /\
                     x' IN ring_carrier r /\ y' IN ring_carrier r /\
                     R x y /\ R x' y'
                     ==> R (ring_add r x x') (ring_add r y y')) /\
        FINITE s /\
        (!a. a IN s
             ==> (f a IN ring_carrier r <=> g a IN ring_carrier r) /\
                 R (f a) (g a))
        ==> R (ring_sum r s f) (ring_sum r s g)`,
  REPLICATE_TAC 4 GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> p /\ q ==> r ==> s`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[FORALL_IN_INSERT; RING_SUM_CLAUSES] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[RING_SUM]);;

let RING_SUM_EQ_0 = prove
 (`!r (f:K->A) s.
        (!a. a IN s /\ f a IN ring_carrier r ==> f a = ring_0 r)
        ==> ring_sum r s f = ring_0 r`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM RING_SUM_RESTRICT] THEN
  ONCE_REWRITE_TAC[GSYM RING_SUM_SUPPORT] THEN
  MATCH_MP_TAC(MESON[RING_SUM_CLAUSES]
   `s = {} ==> ring_sum r s f = ring_0 r`) THEN
  ASM SET_TAC[]);;

let RING_SUM_0 = prove
 (`!r s. ring_sum r s (\i:K. ring_0 r):A = ring_0 r`,
  SIMP_TAC[RING_SUM_EQ_0]);;

let RING_SUM_DELETE = prove
 (`!r (f:K->A) s a.
        FINITE s /\ a IN s /\ f a IN ring_carrier r
        ==> ring_sum r (s DELETE a) f = ring_sub r (ring_sum r s f) (f a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:K) IN s` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `t = s DELETE (a:K)` THEN
  SUBGOAL_THEN `s = (a:K) INSERT t` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[FINITE_INSERT] THEN STRIP_TAC] THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES] THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[IN_DELETE] THEN
  ASM_SIMP_TAC[RING_EQ_SUB_LADD; RING_SUM; RING_ADD] THEN
  ASM_SIMP_TAC[RING_ADD_SYM; RING_SUM]);;

let RING_SUM_NEG = prove
 (`!r (f:K->A) s.
        FINITE s /\
        (!a. a IN s ==> f a IN ring_carrier r)
        ==> ring_sum r s (\x. ring_neg r (f x)) =
            ring_neg r (ring_sum r s f)`,
  REPLICATE_TAC 2 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES; FORALL_IN_INSERT; RING_NEG] THEN
  SIMP_TAC[RING_NEG_ADD; RING_SUM; RING_NEG_0]);;

let RING_SUM_ADD = prove
 (`!r (f:K->A) (g:K->A) s.
        FINITE s /\
        (!a. a IN s ==> f a IN ring_carrier r /\ g a IN ring_carrier r)
        ==> ring_sum r s (\x. ring_add r (f x) (g x)) =
            ring_add r (ring_sum r s f) (ring_sum r s g)`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES; FORALL_IN_INSERT; RING_ADD] THEN
  ASM_SIMP_TAC[RING_ADD_AC; RING_SUM; RING_ADD] THEN
  SIMP_TAC[RING_ADD_LZERO; RING_0]);;

let RING_SUM_EQ = prove
 (`!r (f:K->A) g s.
        (!a. a IN s ==> f a = g a) ==> ring_sum r s f = ring_sum r s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sum] THEN
  SUBGOAL_THEN
   `{a | a IN s /\ (g:K->A) a IN ring_carrier r} =
    {a | a IN s /\ (f:K->A) a IN ring_carrier r}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_EQ (ISPEC `r:C ring` MONOIDAL_RING_ADD)) THEN
  ASM SET_TAC[]);;

let RING_SUM_DELTA = prove
 (`!r s (i:K) (a:A).
        ring_sum r s (\j. if j = i then a else ring_0 r) =
        if i IN s /\ a IN ring_carrier r then a else ring_0 r`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM RING_SUM_SUPPORT] THEN
  ONCE_REWRITE_TAC[GSYM RING_SUM_RESTRICT] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RATOR] THEN
  REWRITE_TAC[RING_0; NOT_IMP; TAUT `(if p then q else T) <=> p ==> q`] THEN
  ASM_CASES_TAC `(i:K) IN s` THEN ASM_SIMP_TAC[RING_SUM_CLAUSES; SET_RULE
   `~(i IN s) ==> {j | (j IN s /\ j = i /\ P j) /\ Q j} = {}`] THEN
  ASM_CASES_TAC `a:A = ring_0 r` THEN
  ASM_REWRITE_TAC[COND_ID; EMPTY_GSPEC; RING_SUM_CLAUSES] THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN
  ASM_SIMP_TAC[TAUT `~((p /\ q) /\ ~q)`; EMPTY_GSPEC; RING_SUM_CLAUSES] THEN
  ASM_SIMP_TAC[SET_RULE `i IN s ==> {j | j IN s /\ j = i} = {i}`] THEN
  ASM_REWRITE_TAC[RING_SUM_SING]);;

let RING_SUM_LMUL = prove
 (`!r (f:K->A) c s.
        c IN ring_carrier r /\
        FINITE s /\
        (!a. a IN s ==> f a IN ring_carrier r)
        ==> ring_sum r s (\x. ring_mul r c (f x)) =
            ring_mul r c (ring_sum r s f)`,
  REPLICATE_TAC 3 GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES; FORALL_IN_INSERT; RING_MUL;
               RING_ADD_LDISTRIB; RING_MUL_RZERO; RING_SUM]);;

let RING_SUM_RMUL = prove
 (`!r (f:K->A) c s.
        c IN ring_carrier r /\
        FINITE s /\
        (!a. a IN s ==> f a IN ring_carrier r)
        ==> ring_sum r s (\x. ring_mul r (f x) c) =
            ring_mul r (ring_sum r s f) c`,
  REPLICATE_TAC 3 GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES; FORALL_IN_INSERT; RING_MUL;
               RING_ADD_RDISTRIB; RING_MUL_LZERO; RING_SUM]);;

let RING_SUM_SWAP = prove
 (`!r (f:K->L->A) s t.
        FINITE s /\ FINITE t /\
        (!i j. i IN s /\ j IN t ==> f i j IN ring_carrier r)
        ==> ring_sum r s (\i. ring_sum r t (f i)) =
            ring_sum r t (\j. ring_sum r s (\i. f i j))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[FORALL_IN_INSERT; RING_SUM_CLAUSES; RING_SUM; RING_SUM_0;
               GSYM RING_SUM_ADD] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[]);;

let RING_SUM_REFLECT = prove
 (`!r (x:num->A) m n.
        (!i. m <= i /\ i <= n ==> x i IN ring_carrier r)
        ==> ring_sum r (m..n) x =
            if n < m then ring_0 r
            else ring_sum r (0..n-m) (\i. x(n - i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `~(n < m)
    ==> !j. 0 <= j /\ j <= n - m ==> (x:num->A) (n - j) IN ring_carrier r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ring_sum; IN_NUMSEG] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x | P x /\ f x IN s} = {x | P x /\ (P x ==> f x IN s)}`] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM numseg] THEN
  MP_TAC(ISPECL [`x:num->A`; `m:num`; `n:num`]
   (MATCH_MP ITERATE_REFLECT (ISPEC `r:C ring` MONOIDAL_RING_ADD))) THEN
  ASM_REWRITE_TAC[NEUTRAL_RING_ADD]);;

let RING_SUM_SUM_PRODUCT = prove
 (`!r s t (x:K->L->A).
        FINITE s /\
        (!i. i IN s ==> FINITE(t i)) /\
        (!i j. i IN s /\ j IN t i ==> x i j IN ring_carrier r)
        ==> ring_sum r s (\i. ring_sum r (t i) (x i)) =
            ring_sum r {i,j | i IN s /\ j IN t i} (\(i,j). x i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sum] THEN
  MP_TAC(ISPECL [`s:K->bool`; `t:K->L->bool`; `x:K->L->A`]
  (MATCH_MP ITERATE_ITERATE_PRODUCT (ISPEC `r:D ring` MONOIDAL_RING_ADD))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `t' = t /\ s' = s ==> s = t ==> s' = t'`) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[ITERATE_EQ]
   `monoidal op /\ s = t /\ (!i. i IN s ==> f i = g i)
    ==> iterate op s f = iterate op t g`) THEN
  REWRITE_TAC[MONOIDAL_RING_ADD] THEN
  REWRITE_TAC[GSYM ring_sum; RING_SUM; IN_GSPEC] THEN
  X_GEN_TAC `i:K` THEN DISCH_TAC THEN REWRITE_TAC[ring_sum] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let RING_SUM_SUPERSET = prove
 (`!r (f:K->A) u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> f x = ring_0 r)
        ==> ring_sum r v f = ring_sum r u f`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM RING_SUM_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let RING_SUM_RESTRICT_SET = prove
 (`!P r s (f:K->A).
        ring_sum r {x | x IN s /\ P x} f =
        ring_sum r s (\x. if P x then f x else ring_0 r)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `ring_sum r s' f = ring_sum r s' f' /\
    ring_sum r s f' = ring_sum r s' f'
    ==> ring_sum r s' f = ring_sum r s f'`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN SET_TAC[];
    MATCH_MP_TAC RING_SUM_SUPERSET THEN
    SIMP_TAC[IN_ELIM_THM; SUBSET_RESTRICT] THEN MESON_TAC[]]);;

let RING_SUM_IMAGE = prove
 (`!r (f:K->L) (g:L->A) s.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ring_sum r (IMAGE f s) g = ring_sum r s (g o f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sum] THEN
  W(MP_TAC o PART_MATCH (rand o rand)
   (MATCH_MP ITERATE_IMAGE(ISPEC `r:C ring` MONOIDAL_RING_ADD)) o
    rand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[o_THM] THEN ASM SET_TAC[]);;

let RING_SUM_EQ_GENERAL_INVERSES = prove
 (`!r s t (f:K->A) (g:L->A) h k.
        (!y. y IN t ==> k y IN s /\ h (k y) = y) /\
        (!x. x IN s ==> h x IN t /\ k (h x) = x /\ g (h x) = f x)
        ==> ring_sum r s f = ring_sum r t g`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `ring_sum r s ((g:L->A) o (h:K->L))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[o_THM];
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

let RING_SUM_OFFSET = prove
 (`!p r (f:num->A) m n.
        ring_sum r (m+p..n+p) f = ring_sum r (m..n) (\i. f(i + p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NUMSEG_OFFSET_IMAGE] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] RING_SUM_IMAGE) THEN
  SIMP_TAC[EQ_ADD_RCANCEL]);;

let RING_SUM_IMAGE_GEN = prove
 (`!r (f:K->B) (g:K->A) s.
         FINITE s
         ==> ring_sum r s g =
             ring_sum r (IMAGE f s)
                        (\y. ring_sum r {x | x IN s /\ f x = y} g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sum] THEN
  MP_TAC(ISPECL
   [`f:K->B`; `g:K->A`; `{x | x IN s /\ (g:K->A) x IN ring_carrier r}`]
    (MATCH_MP ITERATE_IMAGE_GEN(ISPEC `r:C ring` MONOIDAL_RING_ADD))) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; TAUT
   `(x IN s /\ y IN t) /\ a = b <=> (x IN s /\ a = b) /\ y IN t`] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        ITERATE_SUPERSET) THEN
  REWRITE_TAC[MONOIDAL_RING_ADD] THEN
  REWRITE_TAC[SET_RULE `(x IN s /\ f x = a) /\ P x <=>
                        x IN {x | x IN s /\ f x = a} /\ P x`] THEN
  REWRITE_TAC[GSYM ring_sum; RING_SUM; NEUTRAL_RING_ADD] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
  SIMP_TAC[FUN_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ_0 THEN ASM SET_TAC[]);;

let RING_BINOMIAL_THEOREM = prove
 (`!r n x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_pow r (ring_add r x y) n =
            ring_sum r (0..n)
              (\k. ring_mul r (ring_of_num r (binom(n,k)))
                    (ring_mul r (ring_pow r x k) (ring_pow r y (n - k))))`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMSEG_SING; RING_SUM_SING; binom; SUB_REFL; ring_pow;
               RING_MUL_LID; RING_OF_NUM_1; RING_1] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [RING_SUM_CLAUSES_LEFT; ADD1; ARITH_RULE `0 <= n + 1`;
    RING_SUM_OFFSET; RING_POW; RING_MUL; RING_1; RING_OF_NUM] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [ring_pow; binom; GSYM ADD1; GSYM RING_SUM_LMUL; FINITE_NUMSEG;
    RING_POW; RING_MUL; RING_1; RING_OF_NUM; RING_ADD] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [RING_OF_NUM_ADD; RING_MUL_LID; SUB_0; RING_ADD_RDISTRIB; RING_SUM_ADD;
    RING_POW; RING_MUL; RING_1; RING_OF_NUM; RING_ADD; FINITE_NUMSEG;
    RING_OF_NUM_1] THEN
  MATCH_MP_TAC(MESON[RING_ADD_AC]
   `a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r /\
    d IN ring_carrier r /\ e IN ring_carrier r /\
    a = e /\ b = ring_add r c d
    ==> ring_add r a b = ring_add r c (ring_add r d e)`) THEN
  ASM_SIMP_TAC[RING_SUM; RING_MUL; RING_POW; RING_OF_NUM] THEN  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUB_SUC; RING_MUL_AC; RING_MUL; RING_OF_NUM; RING_POW];
    REWRITE_TAC[GSYM ring_pow]] THEN
  ASM_SIMP_TAC[ADD1; SYM(REWRITE_CONV
   [RING_SUM_OFFSET] `ring_sum r (m+1..n+1) (\i. f i)`)] THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES_NUMSEG; GSYM ADD1; LE_SUC; LE_0;
               RING_MUL; RING_POW; RING_OF_NUM] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [RING_SUM_CLAUSES_LEFT; LE_0; BINOM_LT; LT; RING_MUL_LID; SUB_0;
               RING_OF_NUM_1; ring_pow; binom; RING_MUL_LZERO; RING_ADD_RZERO;
               RING_OF_NUM_0; RING_ADD_LZERO; RING_SUM;
               RING_MUL; RING_POW; RING_OF_NUM] THEN
  REWRITE_TAC[ARITH] THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  SIMP_TAC[IN_NUMSEG; ARITH_RULE`k <= n ==> SUC n - k = SUC(n - k)`] THEN
  ASM_SIMP_TAC[ring_pow; RING_MUL_AC; RING_POW; RING_MUL; RING_OF_NUM]);;

let th = prove
 (`!r (f:K->A) g s.
    (!a. a IN s ==> f a = g a) ==> ring_sum r s (\i. f i) = ring_sum r s g`,
  REWRITE_TAC[ETA_AX; RING_SUM_EQ]) in
extend_basic_congs [SPEC_ALL th];;

(* ------------------------------------------------------------------------- *)
(* Very closely analogous: products in a ring.                               *)
(* ------------------------------------------------------------------------- *)

let ring_product = new_definition
 `ring_product r s (f:K->A) =
        iterate (\x y. if x IN ring_carrier r /\ y IN ring_carrier r
                       then ring_mul r x y
                       else if x IN ring_carrier r then y
                       else if y IN ring_carrier r then x
                       else @z:A. ~(z IN ring_carrier r))
                {x | x IN s /\ f(x) IN ring_carrier r} f`;;

let NEUTRAL_RING_MUL = prove
 (`!r:A ring.
        neutral (\x y. if x IN ring_carrier r /\ y IN ring_carrier r
                       then ring_mul r x y
                       else if x IN ring_carrier r then y
                       else if y IN ring_carrier r then x
                       else @z. ~(z IN ring_carrier r)) = ring_1 r`,
  GEN_TAC THEN REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `ring_1 r:A`); DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[RING_1; RING_MUL_LID; RING_MUL_RID; COND_ID]);;

let MONOIDAL_RING_MUL = prove
 (`!r:A ring.
        monoidal (\x y. if x IN ring_carrier r /\ y IN ring_carrier r
                        then ring_mul r x y
                        else if x IN ring_carrier r then y
                         else if y IN ring_carrier r then x
                        else @z. ~(z IN ring_carrier r))`,
  REWRITE_TAC[monoidal; NEUTRAL_RING_MUL] THEN
  SIMP_TAC[RING_1; RING_MUL_LID; COND_ID] THEN
  GEN_TAC THEN CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  TRY(X_GEN_TAC `z:A`) THEN
  MAP_EVERY ASM_CASES_TAC
   [`(x:A) IN ring_carrier r`; `(y:A) IN ring_carrier r`;
    `(z:A) IN ring_carrier r`] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[RING_MUL] THEN
  ASM_SIMP_TAC[RING_MUL_AC; RING_MUL] THEN ASM_MESON_TAC[]);;

let RING_PRODUCT = prove
 (`!r s (f:K->A). ring_product r s f IN ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_product] THEN
  MATCH_MP_TAC
   (SIMP_RULE[NEUTRAL_RING_MUL; RING_1; RING_MUL]
     (ISPEC `\x:B. x IN ring_carrier r`
     (MATCH_MP ITERATE_CLOSED (ISPEC `r:C ring` MONOIDAL_RING_MUL)))) THEN
  SIMP_TAC[IN_ELIM_THM]);;

let RING_PRODUCT_RESTRICT = prove
 (`!s f. ring_product r {a | a IN s /\ f a IN ring_carrier r} f =
         ring_product r s f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_product] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let RING_PRODUCT_SUPPORT = prove
 (`!s (f:K->A).
        ring_product r {a | a IN s /\ ~(f a = ring_1 r)} f =
        ring_product r s f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_product] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_RING_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let RING_PRODUCT_TRIVIAL = prove
 (`!r k (f:K->A).
        INFINITE {i | i IN k /\ f i IN ring_carrier r /\ ~(f i = ring_1 r)}
        ==> ring_product r k f = ring_1 r`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM RING_PRODUCT_SUPPORT] THEN
  REWRITE_TAC[ring_product] THEN ONCE_REWRITE_TAC[iterate] THEN
  REWRITE_TAC[NEUTRAL_RING_MUL; support] THEN
  ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN
  REWRITE_TAC[GSYM INFINITE; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[TAUT `((p /\ q) /\ r) /\ q <=> p /\ r /\ q`]);;

let RING_PRODUCT_CLAUSES = prove
 (`(!r f:K->A. ring_product r {} f = ring_1 r) /\
   (!r x (f:K->A) s.
          FINITE s
          ==> ring_product r (x INSERT s) f =
              (if f(x) IN ring_carrier r ==> x IN s
               then ring_product r s f
               else ring_mul r (f x) (ring_product r s f)))`,
  REWRITE_TAC[ring_product; SET_RULE `{x | x IN {} /\ P x} = {}`] THEN
  REWRITE_TAC[INSERT_RESTRICT] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[MATCH_MP ITERATE_CLAUSES (ISPEC `r:A ring` MONOIDAL_RING_MUL);
               NOT_IN_EMPTY; EMPTY_GSPEC; FINITE_RESTRICT] THEN
  ASM_REWRITE_TAC[NEUTRAL_RING_MUL; GSYM ring_product;
    IN_ELIM_THM; RING_PRODUCT]);;

let RING_PRODUCT_SING = prove
 (`!r (f:K->A) a.
       ring_product r {a} f = if f a IN ring_carrier r then f a else ring_1 r`,
  SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY; COND_SWAP] THEN
  MESON_TAC[RING_MUL_RID]);;

let RING_PRODUCT_CLAUSES_NUMSEG_ALT = prove
 (`(!r m f:num->A.
        ring_product r (m..0) f =
        if m = 0 /\ f 0 IN ring_carrier r then f 0 else ring_1 r) /\
   (!r m n f:num->A.
        ring_product r (m..SUC n) f =
        if m <= SUC n /\ f(SUC n) IN ring_carrier r
        then ring_mul r (f(SUC n)) (ring_product r (m..n) f)
        else ring_product r (m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `m = 0`; ASM_CASES_TAC `m <= SUC n`] THEN
  ASM_REWRITE_TAC[RING_PRODUCT_SING; CONJUNCT1 RING_PRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG; ARITH_RULE `~(SUC n <= n)`; COND_SWAP]);;

let RING_PRODUCT_CLAUSES_NUMSEG = prove
 (`(!r m f:num->A.
        ring_product r (m..0) f =
        if m = 0 /\ f 0 IN ring_carrier r then f 0 else ring_1 r) /\
   (!r m n f:num->A.
        ring_product r (m..SUC n) f =
        if m <= SUC n /\ f(SUC n) IN ring_carrier r
        then ring_mul r (ring_product r (m..n) f) (f(SUC n))
        else ring_product r (m..n) f)`,
  REWRITE_TAC[RING_PRODUCT_CLAUSES_NUMSEG_ALT] THEN
  MESON_TAC[RING_MUL_SYM; RING_PRODUCT]);;

let RING_PRODUCT_CLAUSES_LEFT = prove
 (`!r (f:num->A) m n.
        m <= n
        ==> ring_product r (m..n) f =
            if f m IN ring_carrier r
            then ring_mul r (f m) (ring_product r (m+1..n) f)
            else ring_product r (m+1..n) f`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM NUMSEG_LREC; RING_PRODUCT_CLAUSES; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG; ARITH_RULE `~(n + 1 <= n)`; COND_SWAP]);;

let RING_PRODUCT_UNION = prove
 (`!r (f:K->A) s t.
        FINITE s /\ FINITE t /\ DISJOINT s t
        ==> ring_product r (s UNION t) f =
            ring_mul r (ring_product r s f) (ring_product r t f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_product; UNION_RESTRICT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_UNION
    (ISPEC `r:C ring` MONOIDAL_RING_MUL)) o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM ring_product; RING_PRODUCT]);;

let RING_PRODUCT_INCL_EXCL = prove
 (`!r (f:K->A) s t.
        FINITE s /\ FINITE t
        ==> ring_mul r (ring_product r s f) (ring_product r t f) =
            ring_mul r (ring_product r (s UNION t) f)
                       (ring_product r (s INTER t) f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ring_product; INTER_RESTRICT; UNION_RESTRICT] THEN
  W(MP_TAC o PART_MATCH (funpow 3 rand) (MATCH_MP ITERATE_INCL_EXCL
    (ISPEC `r:C ring` MONOIDAL_RING_MUL)) o rand o rand o snd) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  REWRITE_TAC[GSYM INTER_RESTRICT; GSYM UNION_RESTRICT] THEN
  REWRITE_TAC[GSYM ring_product; RING_PRODUCT]);;

let RING_PRODUCT_CLOSED = prove
 (`!r P (f:K->A) s.
        P(ring_1 r) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_mul r x y)) /\
        (!a. a IN s ==> P(f a))
        ==> P(ring_product r s f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_product] THEN
  MP_TAC(ISPECL
   [`\x:A. x IN ring_carrier r /\ P x`;
    `f:K->A`; `{a | a IN s /\ (f:K->A) a IN ring_carrier r}`]
   (MATCH_MP (REWRITE_RULE[RIGHT_IMP_FORALL_THM] ITERATE_CLOSED)
             (ISPEC `r:C ring` MONOIDAL_RING_MUL))) THEN
  ASM_SIMP_TAC[NEUTRAL_RING_MUL; IMP_IMP; RING_1; RING_MUL; IN_ELIM_THM]);;

let RING_PRODUCT_RELATED = prove
 (`!r R (f:K->A) g s.
        R (ring_1 r) (ring_1 r)/\
        (!x y x' y'. x IN ring_carrier r /\ y IN ring_carrier r /\
                     x' IN ring_carrier r /\ y' IN ring_carrier r /\
                     R x y /\ R x' y'
                     ==> R (ring_mul r x x') (ring_mul r y y')) /\
        FINITE s /\
        (!a. a IN s
             ==> (f a IN ring_carrier r <=> g a IN ring_carrier r) /\
                 R (f a) (g a))
        ==> R (ring_product r s f) (ring_product r s g)`,
  REPLICATE_TAC 4 GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> p /\ q ==> r ==> s`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[FORALL_IN_INSERT; RING_PRODUCT_CLAUSES] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[RING_PRODUCT]);;

let RING_PRODUCT_EQ_1 = prove
 (`!r (f:K->A) s.
        (!a. a IN s /\ f a IN ring_carrier r ==> f a = ring_1 r)
        ==> ring_product r s f = ring_1 r`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM RING_PRODUCT_RESTRICT] THEN
  ONCE_REWRITE_TAC[GSYM RING_PRODUCT_SUPPORT] THEN
  MATCH_MP_TAC(MESON[RING_PRODUCT_CLAUSES]
   `s = {} ==> ring_product r s f = ring_1 r`) THEN
  ASM SET_TAC[]);;

let RING_PRODUCT_1 = prove
 (`!r s. ring_product r s (\i:K. ring_1 r):A = ring_1 r`,
  SIMP_TAC[RING_PRODUCT_EQ_1]);;

let RING_PRODUCT_MUL = prove
 (`!r (f:K->A) (g:K->A) s.
        FINITE s /\
        (!a. a IN s ==> f a IN ring_carrier r /\ g a IN ring_carrier r)
        ==> ring_product r s (\x. ring_mul r (f x) (g x)) =
            ring_mul r (ring_product r s f) (ring_product r s g)`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; FORALL_IN_INSERT; RING_MUL] THEN
  ASM_SIMP_TAC[RING_MUL_AC; RING_PRODUCT; RING_MUL] THEN
  SIMP_TAC[RING_MUL_LID; RING_1]);;

let RING_PRODUCT_EQ = prove
 (`!r (f:K->A) g s.
       (!a. a IN s ==> f a = g a) ==> ring_product r s f = ring_product r s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_product] THEN
  SUBGOAL_THEN
   `{a | a IN s /\ (g:K->A) a IN ring_carrier r} =
    {a | a IN s /\ (f:K->A) a IN ring_carrier r}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_EQ (ISPEC `r:C ring` MONOIDAL_RING_MUL)) THEN
  ASM SET_TAC[]);;

let RING_PRODUCT_DELTA = prove
 (`!r s (i:K) (a:A).
        ring_product r s (\j. if j = i then a else ring_1 r) =
        if i IN s /\ a IN ring_carrier r then a else ring_1 r`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM RING_PRODUCT_SUPPORT] THEN
  ONCE_REWRITE_TAC[GSYM RING_PRODUCT_RESTRICT] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RATOR] THEN
  REWRITE_TAC[RING_1; NOT_IMP; TAUT `(if p then q else T) <=> p ==> q`] THEN
  ASM_CASES_TAC `(i:K) IN s` THEN ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; SET_RULE
   `~(i IN s) ==> {j | (j IN s /\ j = i /\ P j) /\ Q j} = {}`] THEN
  ASM_CASES_TAC `a:A = ring_1 r` THEN
  ASM_REWRITE_TAC[COND_ID; EMPTY_GSPEC; RING_PRODUCT_CLAUSES] THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN
  ASM_SIMP_TAC[TAUT
    `~((p /\ q) /\ ~q)`; EMPTY_GSPEC; RING_PRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[SET_RULE `i IN s ==> {j | j IN s /\ j = i} = {i}`] THEN
  ASM_REWRITE_TAC[RING_PRODUCT_SING]);;

let RING_PRODUCT_SWAP = prove
 (`!r (f:K->L->A) s t.
        FINITE s /\ FINITE t /\
        (!i j. i IN s /\ j IN t ==> f i j IN ring_carrier r)
        ==> ring_product r s (\i. ring_product r t (f i)) =
            ring_product r t (\j. ring_product r s (\i. f i j))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[FORALL_IN_INSERT; RING_PRODUCT_CLAUSES; RING_PRODUCT;
               RING_PRODUCT_1; GSYM RING_PRODUCT_MUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC[]);;

let RING_PRODUCT_REFLECT = prove
 (`!r (x:num->A) m n.
        (!i. m <= i /\ i <= n ==> x i IN ring_carrier r)
        ==> ring_product r (m..n) x =
            if n < m then ring_1 r
            else ring_product r (0..n-m) (\i. x(n - i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `~(n < m)
    ==> !j. 0 <= j /\ j <= n - m ==> (x:num->A) (n - j) IN ring_carrier r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ring_product; IN_NUMSEG] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x | P x /\ f x IN s} = {x | P x /\ (P x ==> f x IN s)}`] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM numseg] THEN
  MP_TAC(ISPECL [`x:num->A`; `m:num`; `n:num`]
   (MATCH_MP ITERATE_REFLECT (ISPEC `r:C ring` MONOIDAL_RING_MUL))) THEN
  ASM_REWRITE_TAC[NEUTRAL_RING_MUL]);;

let RING_PRODUCT_SUPERSET = prove
 (`!r (f:K->A) u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> f x = ring_1 r)
        ==> ring_product r v f = ring_product r u f`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM RING_PRODUCT_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let RING_PRODUCT_RESTRICT_SET = prove
 (`!P r s (f:K->A).
        ring_product r {x | x IN s /\ P x} f =
        ring_product r s (\x. if P x then f x else ring_1 r)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `ring_product r s' f = ring_product r s' f' /\
    ring_product r s f' = ring_product r s' f'
    ==> ring_product r s' f = ring_product r s f'`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ THEN SET_TAC[];
    MATCH_MP_TAC RING_PRODUCT_SUPERSET THEN
    SIMP_TAC[IN_ELIM_THM; SUBSET_RESTRICT] THEN MESON_TAC[]]);;

let RING_PRODUCT_IMAGE = prove
 (`!r (f:K->L) (g:L->A) s.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ring_product r (IMAGE f s) g = ring_product r s (g o f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_product] THEN
  W(MP_TAC o PART_MATCH (rand o rand)
   (MATCH_MP ITERATE_IMAGE(ISPEC `r:C ring` MONOIDAL_RING_MUL)) o
    rand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[o_THM] THEN ASM SET_TAC[]);;

let RING_PRODUCT_EQ_GENERAL_INVERSES = prove
 (`!r s t (f:K->A) (g:L->A) h k.
        (!y. y IN t ==> k y IN s /\ h (k y) = y) /\
        (!x. x IN s ==> h x IN t /\ k (h x) = x /\ g (h x) = f x)
        ==> ring_product r s f = ring_product r t g`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `ring_product r s ((g:L->A) o (h:K->L))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC[o_THM];
    W(MP_TAC o PART_MATCH (rand o rand) RING_PRODUCT_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

let RING_PRODUCT_OFFSET = prove
 (`!p r (f:num->A) m n.
        ring_product r (m+p..n+p) f = ring_product r (m..n) (\i. f(i + p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NUMSEG_OFFSET_IMAGE] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] RING_PRODUCT_IMAGE) THEN
  SIMP_TAC[EQ_ADD_RCANCEL]);;

let RING_PRODUCT_IMAGE_GEN = prove
 (`!r (f:K->B) (g:K->A) s.
         FINITE s
         ==> ring_product r s g =
             ring_product r (IMAGE f s)
                            (\y. ring_product r {x | x IN s /\ f x = y} g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_product] THEN
  MP_TAC(ISPECL
   [`f:K->B`; `g:K->A`; `{x | x IN s /\ (g:K->A) x IN ring_carrier r}`]
    (MATCH_MP ITERATE_IMAGE_GEN(ISPEC `r:C ring` MONOIDAL_RING_MUL))) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; TAUT
   `(x IN s /\ y IN t) /\ a = b <=> (x IN s /\ a = b) /\ y IN t`] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        ITERATE_SUPERSET) THEN
  REWRITE_TAC[MONOIDAL_RING_MUL] THEN
  REWRITE_TAC[SET_RULE `(x IN s /\ f x = a) /\ P x <=>
                        x IN {x | x IN s /\ f x = a} /\ P x`] THEN
  REWRITE_TAC[GSYM ring_product; RING_PRODUCT; NEUTRAL_RING_MUL] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
  SIMP_TAC[FUN_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RING_PRODUCT_EQ_1 THEN ASM SET_TAC[]);;

let th = prove
 (`!r (f:K->A) g s.
    (!a. a IN s ==> f a = g a)
    ==> ring_product r s (\i. f i) = ring_product r s g`,
  REWRITE_TAC[ETA_AX; RING_PRODUCT_EQ]) in
extend_basic_congs [SPEC_ALL th];;

(* ------------------------------------------------------------------------- *)
(* Divisibility, zerodivisors, units etc.                                    *)
(*                                                                           *)
(* The standard texts and references are a bit divided over how to define    *)
(* associates, but the two versions are equivalent for integral domains:     *)
(* See INTEGRAL_DOMAIN_ASSOCIATES for this other possible definition.        *)
(* ------------------------------------------------------------------------- *)

let ring_divides = new_definition
 `ring_divides r (a:A) b <=>
        a IN ring_carrier r /\ b IN ring_carrier r /\
        ?x. x IN ring_carrier r /\ b = ring_mul r a x`;;

let ring_zerodivisor = new_definition
 `ring_zerodivisor r (a:A) <=>
        a IN ring_carrier r /\
        ?x. x IN ring_carrier r /\ ~(x = ring_0 r) /\
            ring_mul r a x = ring_0 r`;;

let ring_regular = new_definition
 `ring_regular r (a:A) <=> a IN ring_carrier r /\ ~(ring_zerodivisor r a)`;;

let ring_nilpotent = new_definition
 `ring_nilpotent r (a:A) <=>
        a IN ring_carrier r /\ ?n. ~(n = 0) /\ ring_pow r a n = ring_0 r`;;

let ring_unit = new_definition
 `ring_unit r (a:A) <=>
        a IN ring_carrier r /\
        ?x. x IN ring_carrier r /\ ring_mul r a x = ring_1 r`;;

let ring_associates = new_definition
 `ring_associates r (a:A) b <=> ring_divides r a b /\ ring_divides r b a`;;

let ring_coprime = new_definition
 `ring_coprime r (a:A,b) <=>
        a IN ring_carrier r /\ b IN ring_carrier r /\
        !d. ring_divides r d a /\ ring_divides r d b ==> ring_unit r d`;;

let ring_inv = new_definition
 `ring_inv r (a:A) =
        if ring_unit r a
        then @x. x IN ring_carrier r /\ ring_mul r a x = ring_1 r
        else ring_0 r`;;

let ring_div = new_definition
 `ring_div r (a:A) b = ring_mul r a (ring_inv r b)`;;

let RING_DIVIDES_IN_CARRIER = prove
 (`!r a b:A.
        ring_divides r a b
        ==> a IN ring_carrier r /\ b IN ring_carrier r`,
  SIMP_TAC[ring_divides]);;

let RING_ZERODIVISOR_IN_CARRIER = prove
 (`!r a:A. ring_zerodivisor r a ==> a IN ring_carrier r`,
  SIMP_TAC[ring_zerodivisor]);;

let RING_REGULAR_IN_CARRIER = prove
 (`!r a:A. ring_regular r a ==> a IN ring_carrier r`,
  SIMP_TAC[ring_regular]);;

let RING_NILPOTENT_IN_CARRIER = prove
 (`!r a:A. ring_nilpotent r a ==> a IN ring_carrier r`,
  SIMP_TAC[ring_nilpotent]);;

let RING_UNIT_IN_CARRIER = prove
 (`!r a:A. ring_unit r a ==> a IN ring_carrier r`,
  SIMP_TAC[ring_unit]);;

let RING_ASSOCIATES_IN_CARRIER = prove
 (`!r a a':A. ring_associates r a a'
              ==> a IN ring_carrier r /\ a' IN ring_carrier r`,
  SIMP_TAC[ring_associates; ring_divides]);;

let RING_COPRIME_IN_CARRIER = prove
 (`!r a b:A.
        ring_coprime r (a,b)
        ==> a IN ring_carrier r /\ b IN ring_carrier r`,
  SIMP_TAC[ring_coprime]);;

let RING_INV,RING_MUL_RINV = (CONJ_PAIR o prove)
 (`(!r a:A. a IN ring_carrier r ==> (ring_inv r a) IN ring_carrier r) /\
   (!r a:A. ring_unit r a ==> ring_mul r a (ring_inv r a) = ring_1 r)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `ring_unit r (a:A)` THEN ASM_REWRITE_TAC[ring_inv] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ring_unit] THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[RING_0] THEN
  CONV_TAC(RAND_CONV SELECT_CONV) THEN REWRITE_TAC[]);;

let RING_MUL_LINV = prove
 (`!r a:A. ring_unit r a ==> ring_mul r (ring_inv r a) a = ring_1 r`,
  MESON_TAC[RING_MUL_RINV; RING_INV; RING_MUL_SYM; ring_unit]);;

let RING_DIV = prove
 (`!r a b:A. a IN ring_carrier r /\ b IN ring_carrier r
             ==> ring_div r a b IN ring_carrier r`,
  SIMP_TAC[ring_div; RING_MUL; RING_INV]);;

let RING_CLAUSES = prove
 (`(!(r:A ring). ring_0 r IN ring_carrier r) /\
   (!(r:A ring). ring_1 r IN ring_carrier r) /\
   (!(r:A ring) n. ring_of_num r n IN ring_carrier r) /\
   (!(r:A ring) x. x IN ring_carrier r ==> ring_neg r x IN ring_carrier r) /\
   (!(r:A ring) x. x IN ring_carrier r ==> ring_inv r x IN ring_carrier r) /\
   (!(r:A ring) x y.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_add r x y IN ring_carrier r) /\
   (!(r:A ring) x y.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_sub r x y IN ring_carrier r) /\
   (!(r:A ring) x y.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_mul r x y IN ring_carrier r) /\
   (!(r:A ring) x y.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_div r x y IN ring_carrier r) /\
   (!(r:A ring) x n. x IN ring_carrier r
                     ==> ring_pow r x n IN ring_carrier r)`,
  REWRITE_TAC[RING_0; RING_1; RING_OF_NUM; RING_NEG; RING_INV;
              RING_ADD; RING_SUB; RING_MUL; RING_DIV;RING_POW]);;

let RING_RINV_UNIQUE = prove
 (`!r a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\
        ring_mul r a b = ring_1 r
        ==> ring_inv r a = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_inv] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[ring_unit]] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `c:A` THEN REWRITE_TAC[] THEN
  EQ_TAC THENL [STRIP_TAC; ASM_MESON_TAC[]] THEN
  TRANS_TAC EQ_TRANS `ring_mul r (ring_mul r a b) c:A` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_LID]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `ring_mul r (ring_mul r a c) b:A` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_AC; RING_MUL]; ASM_SIMP_TAC[RING_MUL_LID]]);;

let RING_LINV_UNIQUE = prove
 (`!r a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\
        ring_mul r a b = ring_1 r
        ==> ring_inv r b = a`,
  MESON_TAC[RING_RINV_UNIQUE; RING_MUL_SYM]);;

let RING_INV_1 = prove
 (`!r:A ring. ring_inv r (ring_1 r) = ring_1 r`,
  GEN_TAC THEN MATCH_MP_TAC RING_RINV_UNIQUE THEN
  SIMP_TAC[RING_MUL_LID; RING_1]);;

let RING_DIV_1 = prove
 (`!r x:A. x IN ring_carrier r ==> ring_div r x (ring_1 r) = x`,
  SIMP_TAC[ring_div; RING_INV_1; RING_MUL_RID]);;

let RING_1_DIV = prove
 (`!(r:A ring) x.
        x IN ring_carrier r ==> ring_div r (ring_1 r) x = ring_inv r x`,
  SIMP_TAC[ring_div; RING_INV; RING_MUL_LID]);;

let RING_INV_ZERO = prove
 (`!r x:A. ~ring_unit r x ==> ring_inv r x = ring_0 r`,
  SIMP_TAC[ring_inv]);;

let RING_INV_MUL = prove
 (`!r a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> ring_inv r (ring_mul r a b) =
            ring_mul r (ring_inv r a) (ring_inv r b)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `ring_unit r (a:A)` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[RING_INV_ZERO; RING_INV; RING_MUL_LZERO] THEN
    MATCH_MP_TAC RING_INV_ZERO THEN UNDISCH_TAC `~ring_unit r (a:A)` THEN
    REWRITE_TAC[ring_unit; CONTRAPOS_THM] THEN
    ASM_MESON_TAC[RING_MUL_AC; RING_MUL]] THEN
  ASM_CASES_TAC `ring_unit r (b:A)` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[RING_INV_ZERO; RING_INV; RING_MUL_RZERO] THEN
    MATCH_MP_TAC RING_INV_ZERO THEN UNDISCH_TAC `~ring_unit r (b:A)` THEN
    REWRITE_TAC[ring_unit; CONTRAPOS_THM] THEN
    ASM_MESON_TAC[RING_MUL_AC; RING_MUL]] THEN
  MATCH_MP_TAC RING_RINV_UNIQUE THEN
  ASM_SIMP_TAC[RING_MUL; RING_INV; RING_UNIT_IN_CARRIER] THEN
  TRANS_TAC EQ_TRANS
   `ring_mul r (ring_mul r a (ring_inv r a))
               (ring_mul r b (ring_inv r b)):A` THEN
  CONJ_TAC THENL
   [ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
        [RING_MUL; RING_INV; RING_MUL_AC; RING_UNIT_IN_CARRIER];
    ASM_SIMP_TAC[RING_MUL_RINV; RING_MUL_LID; RING_1; RING_UNIT_IN_CARRIER]]);;

let RING_INV_POW = prove
 (`!r (x:A) n.
        x IN ring_carrier r
        ==> ring_inv r (ring_pow r x n) = ring_pow r (ring_inv r x) n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ring_pow; RING_INV_1] THEN
  ASM_SIMP_TAC[RING_INV_MUL; RING_POW]);;

let RING_POW_INV = prove
 (`!r (x:A) n.
        x IN ring_carrier r
        ==> ring_pow r (ring_inv r x) n = ring_inv r (ring_pow r x n)`,
  SIMP_TAC[RING_INV_POW]);;

let RING_INV_INV = prove
 (`!r a:A. ring_unit r a ==> ring_inv r (ring_inv r a) = a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_RINV_UNIQUE THEN
  ASM_SIMP_TAC[RING_INV; RING_UNIT_IN_CARRIER; RING_MUL_LINV]);;

let RING_MUL_RINV_EQ = prove
 (`!r x:A.
        x IN ring_carrier r
        ==> (ring_mul r x (ring_inv r x) = ring_1 r <=> ring_unit r x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[RING_MUL_RINV] THEN
  REWRITE_TAC[ring_unit] THEN ASM_MESON_TAC[RING_INV]);;

let RING_MUL_LINV_EQ = prove
 (`!r x:A.
        x IN ring_carrier r
        ==> (ring_mul r (ring_inv r x) x = ring_1 r <=> ring_unit r x)`,
  MESON_TAC[RING_MUL_RINV_EQ; RING_MUL_SYM; RING_INV]);;

let RING_UNIT_DIVIDES = prove
 (`!r a:A. ring_unit r a <=> ring_divides r a (ring_1 r)`,
  REWRITE_TAC[ring_unit; ring_divides] THEN MESON_TAC[RING_1]);;

let RING_UNIT_0 = prove
 (`!r:A ring. ring_unit r (ring_0 r) <=> trivial_ring r`,
  REWRITE_TAC[ring_unit; RING_0; TRIVIAL_RING_10] THEN
  MESON_TAC[RING_MUL_LZERO; RING_0]);;

let RING_INV_0 = prove
 (`!r:A ring. ring_inv r (ring_0 r) = ring_0 r`,
  GEN_TAC THEN REWRITE_TAC[ring_inv; RING_UNIT_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `x:A` THEN
  EQ_TAC THEN SIMP_TAC[RING_0; RING_MUL_LZERO; IMP_CONJ] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[trivial_ring]) THEN ASM SET_TAC[];
    ASM_MESON_TAC[TRIVIAL_RING_10]]);;

let RING_UNIT_1 = prove
 (`!r:A ring. ring_unit r (ring_1 r)`,
  GEN_TAC THEN REWRITE_TAC[ring_unit; RING_1] THEN
  EXISTS_TAC `ring_1 r:A` THEN SIMP_TAC[RING_1; RING_MUL_LID]);;

let RING_UNIT_NEG = prove
 (`!r x:A. ring_unit r x ==> ring_unit r (ring_neg r x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_unit] THEN DISCH_THEN
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[RING_NEG] THEN EXISTS_TAC `ring_neg r x':A` THEN
  ASM_SIMP_TAC[RING_NEG; RING_MUL_LNEG; RING_MUL_RNEG; RING_NEG_NEG; RING_1]);;

let RING_UNIT_NEG_EQ = prove
 (`!r x:A.
        x IN ring_carrier r
        ==> (ring_unit r (ring_neg r x) <=> ring_unit r x)`,
  MESON_TAC[RING_UNIT_NEG; RING_UNIT_IN_CARRIER; RING_NEG_NEG]);;

let RING_UNIT_INV = prove
 (`!r x:A. ring_unit r x ==> ring_unit r (ring_inv r x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_unit] THEN DISCH_THEN
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[RING_INV] THEN EXISTS_TAC `ring_inv r (x':A)` THEN
  ASM_SIMP_TAC[RING_INV] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_INV_MUL o lhand o snd) THEN
  ASM_REWRITE_TAC[RING_INV_1; ring_unit] THEN ASM_MESON_TAC[RING_MUL_SYM]);;

let RING_UNIT_MUL = prove
 (`!r x y:A. ring_unit r x /\ ring_unit r y ==> ring_unit r (ring_mul r x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_unit] THEN DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y':A` STRIP_ASSUME_TAC))) THEN
  ASM_SIMP_TAC[RING_MUL] THEN
  EXISTS_TAC `ring_mul r x' y':A` THEN ASM_SIMP_TAC[RING_MUL] THEN
  TRANS_TAC EQ_TRANS `ring_mul r (ring_mul r x x') (ring_mul r y y'):A` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RING_MUL_LID; RING_1]] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o SYM)) THEN
  ASM_SIMP_TAC[RING_MUL_AC; RING_MUL]);;

let RING_UNIT_DIV = prove
 (`!r x y:A. ring_unit r x /\ ring_unit r y ==> ring_unit r (ring_div r x y)`,
  SIMP_TAC[ring_div; RING_UNIT_MUL; RING_UNIT_INV]);;

let RING_MUL_IMP_UNITS = prove
 (`!r a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\
        ring_mul r a b = ring_1 r
        ==> ring_unit r a /\ ring_unit r b`,
  REWRITE_TAC[ring_unit] THEN
  MESON_TAC[RING_MUL_SYM]);;

let RING_UNIT_MUL_EQ = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_unit r (ring_mul r x y) <=> ring_unit r x /\ ring_unit r y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[RING_UNIT_MUL] THEN
  REWRITE_TAC[ring_unit] THEN ASM_MESON_TAC[RING_MUL; RING_MUL_AC]);;

let RING_UNIT_POW = prove
 (`!r (a:A) n. ring_unit r a ==> ring_unit r (ring_pow r a n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ring_pow; RING_UNIT_1; RING_UNIT_MUL]);;

let RING_UNIT_POW_EQ = prove
 (`!r (a:A) n.
        a IN ring_carrier r
        ==> (ring_unit r (ring_pow r a n) <=> n = 0 \/ ring_unit r a)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_pow; RING_UNIT_1; RING_UNIT_MUL_EQ; RING_POW; NOT_SUC] THEN
  CONV_TAC TAUT);;

let RING_UNIT_DIVIDES_ANY = prove
 (`!r a b:A. ring_unit r a /\ b IN ring_carrier r ==> ring_divides r a b`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ring_unit; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[ring_divides] THEN
  EXISTS_TAC `ring_mul r c b:A` THEN
  ASM_SIMP_TAC[RING_MUL; RING_MUL_ASSOC; RING_MUL_LID]);;

let RING_UNIT_DIVISOR = prove
 (`!r u v:A. ring_unit r u /\ ring_divides r v u ==> ring_unit r v`,
  REWRITE_TAC[ring_divides] THEN MESON_TAC[ring_unit; RING_UNIT_MUL_EQ]);;

let RING_UNIT_PRODUCT = prove
 (`!r k (f:K->A).
        FINITE k
        ==> (ring_unit r (ring_product r k f) <=>
             !i. i IN k /\ f i IN ring_carrier r ==> ring_unit r (f i))`,
  GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; RING_UNIT_1; COND_SWAP] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[RING_UNIT_MUL_EQ; RING_PRODUCT]);;

let RING_DIVIDES_REFL = prove
 (`!r a:A. ring_divides r a a <=> a IN ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_divides] THEN
  MESON_TAC[RING_1; RING_MUL_RID]);;

let RING_DIVIDES_TRANS = prove
 (`!r a b c:A.
        ring_divides r a b /\ ring_divides r b c ==> ring_divides r a c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_divides] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `ring_mul r x y:A` THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_MUL]);;

let RING_DIVIDES_MORE_DIVISORS = prove
 (`!r a b:A.
        ring_divides r a b <=>
        a IN ring_carrier r /\ b IN ring_carrier r /\
        !d. d IN ring_carrier r /\ ring_divides r d a ==> ring_divides r d b`,
  MESON_TAC[ring_divides; RING_DIVIDES_REFL; RING_DIVIDES_TRANS]);;

let RING_DIVIDES_ANTISYM = prove
 (`!r a b:A.
    ring_divides r a b /\ ring_divides r b a <=> ring_associates r a b`,
  REWRITE_TAC[ring_associates]);;

let RING_DIVIDES_ASSOCIATES = prove
 (`!r a b:A. ring_associates r a b ==> ring_divides r a b`,
  SIMP_TAC[ring_associates]);;

let RING_DIVIDES_0 = prove
 (`!r a:A. ring_divides r a (ring_0 r) <=> a IN ring_carrier r`,
  REWRITE_TAC[ring_divides] THEN MESON_TAC[RING_0; RING_MUL_RZERO]);;

let RING_DIVIDES_ZERO = prove
 (`!r a:A. ring_divides r (ring_0 r) a <=> a = ring_0 r`,
  REWRITE_TAC[ring_divides] THEN MESON_TAC[RING_0; RING_MUL_LZERO]);;

let RING_DIVIDES_1 = prove
 (`!r a:A. ring_divides r (ring_1 r) a <=> a IN ring_carrier r`,
  REWRITE_TAC[ring_divides] THEN MESON_TAC[RING_1; RING_MUL_LID]);;

let RING_DIVIDES_ONE = prove
 (`!r a:A. ring_divides r a (ring_1 r) <=> ring_unit r a`,
  REWRITE_TAC[ring_divides; ring_unit; RING_1] THEN MESON_TAC[]);;

let RING_UNIT_DIVIDES_ALL = prove
 (`!r a:A. ring_unit r a <=> !b. b IN ring_carrier r ==> ring_divides r a b`,
  MESON_TAC[RING_UNIT_DIVIDES_ANY; RING_DIVIDES_ONE; RING_1]);;

let RING_DIVIDES_ADD = prove
 (`!r a b d:A.
        ring_divides r d a /\ ring_divides r d b
        ==> ring_divides r d (ring_add r a b)`,
  SIMP_TAC[ring_divides; RING_ADD] THEN
  MESON_TAC[RING_ADD_LDISTRIB; RING_ADD]);;

let RING_DIVIDES_SUB = prove
 (`!r a b d:A.
        ring_divides r d a /\ ring_divides r d b
        ==> ring_divides r d (ring_sub r a b)`,
  SIMP_TAC[ring_divides; RING_SUB] THEN
  MESON_TAC[RING_SUB_LDISTRIB; RING_SUB]);;

let RING_DIVIDES_LNEG = prove
 (`!r a d:A. ring_divides r d a ==> ring_divides r (ring_neg r d) a`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_divides; RING_NEG] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ring_neg r x:A` THEN
  ASM_SIMP_TAC[RING_NEG; RING_MUL_LNEG; RING_MUL_RNEG] THEN
  ASM_SIMP_TAC[RING_MUL; RING_NEG_NEG]);;

let RING_DIVIDES_NEG = prove
 (`!r a d:A. ring_divides r d a ==> ring_divides r d (ring_neg r a)`,
  MESON_TAC[RING_SUB_LZERO; RING_DIVIDES_SUB; ring_divides; RING_0;
            RING_DIVIDES_0]);;

let RING_DIVIDES_NEG_EQ = prove
 (`(!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
              ==> (ring_divides r (ring_neg r x) y <=> ring_divides r x y)) /\
   (!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
              ==> (ring_divides r x (ring_neg r y) <=> ring_divides r x y))`,
  MESON_TAC[RING_DIVIDES_NEG; RING_DIVIDES_LNEG;
    RING_DIVIDES_IN_CARRIER; RING_NEG_NEG]);;

let RING_DIVIDES_RMUL = prove
 (`!r a b d:A.
        ring_divides r d a /\ b IN ring_carrier r
        ==> ring_divides r d (ring_mul r a b)`,
  SIMP_TAC[ring_divides; RING_MUL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM RING_MUL_ASSOC] THEN
  ASM_MESON_TAC[RING_MUL]);;

let RING_DIVIDES_LMUL = prove
 (`!r a b d:A.
        a IN ring_carrier r /\ ring_divides r d b
        ==> ring_divides r d (ring_mul r a b)`,
  MESON_TAC[RING_DIVIDES_RMUL; ring_divides; RING_MUL_SYM]);;

let RING_DIVIDES_LMUL_REV = prove
 (`!r d a x:A.
        x IN ring_carrier r /\ d IN ring_carrier r /\
        ring_divides r (ring_mul r x d) a
        ==> ring_divides r d a`,
  REWRITE_TAC[ring_divides] THEN MESON_TAC[RING_MUL_AC; RING_MUL]);;

let RING_DIVIDES_RMUL_REV = prove
 (`!r d a x:A.
        x IN ring_carrier r /\ d IN ring_carrier r /\
        ring_divides r (ring_mul r d x) a
        ==> ring_divides r d a`,
  REWRITE_TAC[ring_divides] THEN MESON_TAC[RING_MUL_AC; RING_MUL]);;

let RING_DIVIDES_MUL2 = prove
 (`!r a b c d:A.
        ring_divides r a b /\ ring_divides r c d
        ==> ring_divides r (ring_mul r a c) (ring_mul r b d)`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_divides; RING_MUL] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN STRIP_TAC THEN
  EXISTS_TAC `ring_mul r u v:A` THEN ASM_SIMP_TAC[RING_MUL] THEN
  ASM_SIMP_TAC[RING_MUL_AC; RING_MUL]);;

let RING_DIVIDES_LMUL2 = prove
 (`!r a b c:A.
        a IN ring_carrier r /\ ring_divides r b c
        ==> ring_divides r (ring_mul r a b) (ring_mul r a c)`,
  SIMP_TAC[RING_DIVIDES_MUL2; RING_DIVIDES_REFL]);;

let RING_DIVIDES_RMUL2 = prove
 (`!r a b c:A.
        ring_divides r a b /\ c IN ring_carrier r
        ==> ring_divides r (ring_mul r a c) (ring_mul r b c)`,
  SIMP_TAC[RING_DIVIDES_MUL2; RING_DIVIDES_REFL]);;

let RING_DIVIDES_PRODUCT_SUBSET = prove
 (`!r (f:K->A) s t.
        FINITE t /\ s SUBSET t
        ==> ring_divides r (ring_product r s f) (ring_product r t f)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `u:K->bool = t DIFF s` THEN
  SUBGOAL_THEN `t:K->bool = s UNION u` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_DIFF]; ASM SET_TAC[]];
    MESON_TAC[RING_DIVIDES_RMUL; RING_PRODUCT; RING_DIVIDES_REFL]]);;

let RING_ASSOCIATES_REFL = prove
 (`!r a:A. ring_associates r a a <=> a IN ring_carrier r`,
  REWRITE_TAC[ring_associates; RING_DIVIDES_REFL]);;

let RING_ASSOCIATES_SYM = prove
 (`!r a b:A. ring_associates r a b <=> ring_associates r b a`,
  REWRITE_TAC[ring_associates] THEN MESON_TAC[]);;

let RING_ASSOCIATES_TRANS = prove
 (`!r a b c:A.
    ring_associates r a b /\ ring_associates r b c ==> ring_associates r a c`,
  REWRITE_TAC[ring_associates] THEN MESON_TAC[RING_DIVIDES_TRANS]);;

let RING_ASSOCIATES_SAME_DIVISORS = prove
 (`!r a b:A.
        ring_associates r a b <=>
        a IN ring_carrier r /\ b IN ring_carrier r /\
        !d. d IN ring_carrier r
            ==> (ring_divides r d a <=> ring_divides r d b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_associates] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [RING_DIVIDES_MORE_DIVISORS] THEN
  MESON_TAC[]);;

let RING_ASSOCIATES_0 = prove
 (`(!r a:A. ring_associates r a (ring_0 r) <=> a = ring_0 r) /\
   (!r a:A. ring_associates r (ring_0 r) a <=> a = ring_0 r)`,
  REWRITE_TAC[ring_associates; RING_DIVIDES_0; RING_DIVIDES_ZERO] THEN
  MESON_TAC[RING_0]);;

let RING_ASSOCIATES_1 = prove
 (`(!r a:A. ring_associates r a (ring_1 r) <=> ring_unit r a) /\
   (!r a:A. ring_associates r (ring_1 r) a <=> ring_unit r a)`,
  REWRITE_TAC[ring_associates; RING_DIVIDES_1; RING_DIVIDES_ONE] THEN
  MESON_TAC[ring_unit]);;

let RING_ASSOCIATES_LNEG = prove
 (`!r a d:A. ring_associates r d a ==> ring_associates r (ring_neg r d) a`,
  SIMP_TAC[ring_associates; RING_DIVIDES_NEG; RING_DIVIDES_LNEG]);;

let RING_ASSOCIATES_NEG = prove
 (`!r a d:A. ring_associates r d a ==> ring_associates r d (ring_neg r a)`,
  SIMP_TAC[ring_associates; RING_DIVIDES_NEG; RING_DIVIDES_LNEG]);;

let RING_ASSOCIATES_NEG_EQ = prove
 (`(!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_associates r (ring_neg r x) y <=> ring_associates r x y)) /\
   (!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_associates r x (ring_neg r y) <=> ring_associates r x y))`,
  MESON_TAC[RING_ASSOCIATES_NEG; RING_ASSOCIATES_LNEG;
    RING_ASSOCIATES_IN_CARRIER; RING_NEG_NEG]);;

let RING_ASSOCIATES_MUL = prove
 (`!r a a' b b'.
        ring_associates r a a' /\ ring_associates r b b'
        ==> ring_associates r (ring_mul r a b) (ring_mul r a' b')`,
  SIMP_TAC[ring_associates; RING_DIVIDES_MUL2]);;

let RING_ASSOCIATES_POW = prove
 (`!r a (a':A) n.
        ring_associates r a a'
        ==> ring_associates r (ring_pow r a n) (ring_pow r a' n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_pow; RING_ASSOCIATES_REFL; RING_1; RING_ASSOCIATES_MUL;
                RING_MUL]);;

let RING_ASSOCIATES_PRODUCT = prove
 (`!r k (f:K->A) g.
        FINITE k /\
        (!i. i IN k ==> ring_associates r (f i) (g i))
        ==> ring_associates r (ring_product r k f) (ring_product r k g)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; RING_ASSOCIATES_REFL; RING_1; COND_SWAP] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[RING_ASSOCIATES_MUL]) THEN
  ASM_MESON_TAC[RING_ASSOCIATES_IN_CARRIER]);;

let RING_ZERODIVISOR_0 = prove
 (`!r:A ring. ring_zerodivisor r (ring_0 r) <=> ~trivial_ring r`,
  REWRITE_TAC[ring_zerodivisor; TRIVIAL_RING_SUBSET; RING_0] THEN
  REWRITE_TAC[SUBSET; IN_SING] THEN MESON_TAC[RING_MUL_LZERO]);;

let RING_REGULAR_0 = prove
 (`!r:A ring. ring_regular r (ring_0 r) <=> trivial_ring r`,
  REWRITE_TAC[ring_regular; RING_ZERODIVISOR_0; RING_0]);;

let RING_ZERODIVISOR_1 = prove
 (`!r:A ring. ~(ring_zerodivisor r (ring_1 r))`,
  REWRITE_TAC[ring_zerodivisor; RING_1] THEN MESON_TAC[RING_MUL_LID]);;

let RING_REGULAR_1 = prove
 (`!r:A ring. ring_regular r (ring_1 r)`,
  REWRITE_TAC[ring_regular; RING_1; RING_ZERODIVISOR_1]);;

let RING_ZERODIVISOR_LMUL = prove
 (`!r a x:A.
        a IN ring_carrier r /\ ring_zerodivisor r x
        ==> ring_zerodivisor r (ring_mul r a x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_zerodivisor; IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[RING_MUL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_MUL_RZERO]);;

let RING_ZERODIVISOR_RMUL = prove
 (`!r x a:A.
        ring_zerodivisor r x /\ a IN ring_carrier r
        ==> ring_zerodivisor r (ring_mul r x a)`,
  MESON_TAC[RING_ZERODIVISOR_LMUL; RING_ZERODIVISOR_IN_CARRIER;
            RING_MUL_SYM]);;

let RING_ZERODIVISOR_MUL = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_zerodivisor r (ring_mul r x y) <=>
             ring_zerodivisor r x \/ ring_zerodivisor r y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[RING_ZERODIVISOR_LMUL; RING_ZERODIVISOR_RMUL]] THEN
  ASM_SIMP_TAC[ring_zerodivisor; RING_MUL] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `ring_mul r x z:A = ring_0 r` THENL
   [ASM_MESON_TAC[]; DISJ2_TAC] THEN
  EXISTS_TAC `ring_mul r x z:A` THEN ASM_SIMP_TAC[RING_MUL] THEN
  ASM_MESON_TAC[RING_MUL_AC]);;

let RING_ZERODIVISOR_POW = prove
 (`!r (x:A) n.
        x IN ring_carrier r
        ==> (ring_zerodivisor r (ring_pow r x n) <=>
             ~(n = 0) /\ ring_zerodivisor r x)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ring_pow; RING_ZERODIVISOR_1] THEN
  ASM_SIMP_TAC[NOT_SUC; RING_POW; RING_ZERODIVISOR_MUL] THEN
  CONV_TAC TAUT);;

let RING_REGULAR_MUL_EQ = prove
 (`!r x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_regular r (ring_mul r x y) <=>
             ring_regular r x /\ ring_regular r y)`,
  SIMP_TAC[ring_regular; RING_MUL; RING_ZERODIVISOR_MUL] THEN MESON_TAC[]);;

let RING_REGULAR_POW = prove
 (`!r (x:A) n.
        x IN ring_carrier r
        ==> (ring_regular r (ring_pow r x n) <=> n = 0 \/ ring_regular r x)`,
  SIMP_TAC[ring_regular; RING_POW; RING_ZERODIVISOR_POW] THEN MESON_TAC[]);;

let RING_REGULAR_MUL = prove
 (`!r x y:A.
        ring_regular r x /\ ring_regular r y
        ==> ring_regular r (ring_mul r x y)`,
  SIMP_TAC[RING_REGULAR_MUL_EQ; RING_REGULAR_IN_CARRIER]);;

let RING_ZERODIVISOR_NEG = prove
 (`!r x:A. ring_zerodivisor r x ==> ring_zerodivisor r (ring_neg r x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_ZERODIVISOR_IN_CARRIER) THEN
  SUBGOAL_THEN `ring_neg r x:A = ring_mul r (ring_neg r (ring_1 r)) x`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_LNEG; RING_MUL_LID; RING_1];
    ASM_SIMP_TAC[RING_ZERODIVISOR_MUL; RING_1; RING_NEG]]);;

let RING_ZERODIVISOR_NEG_EQ = prove
 (`!r x:A.
        x IN ring_carrier r
        ==> (ring_zerodivisor r (ring_neg r x) <=> ring_zerodivisor r x)`,
  MESON_TAC[RING_ZERODIVISOR_NEG; RING_ZERODIVISOR_IN_CARRIER; RING_NEG_NEG]);;

let RING_REGULAR_NEG = prove
 (`!r x:A. ring_regular r x ==> ring_regular r (ring_neg r x)`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_regular; IMP_CONJ; RING_NEG] THEN
  SIMP_TAC[RING_ZERODIVISOR_NEG_EQ]);;

let RING_REGULAR_NEG_EQ = prove
 (`!r x:A.
        x IN ring_carrier r
        ==> (ring_regular r (ring_neg r x) <=> ring_regular r x)`,
  MESON_TAC[RING_REGULAR_NEG; RING_REGULAR_IN_CARRIER; RING_NEG_NEG]);;

let RING_ZERODIVISOR_IMP_NONUNIT = prove
 (`!r x:A. ring_zerodivisor r x ==> ~(ring_unit r x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_ZERODIVISOR_IN_CARRIER) THEN
  ASM_REWRITE_TAC[ring_unit] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `ring_zerodivisor (r:A ring)`) THEN
  ASM_SIMP_TAC[RING_ZERODIVISOR_MUL; RING_ZERODIVISOR_1]);;

let RING_UNIT_IMP_REGULAR = prove
 (`!r a:A. ring_unit r a ==> ring_regular r a`,
  MESON_TAC[RING_ZERODIVISOR_IMP_NONUNIT; ring_unit; ring_regular]);;

let RING_DIVIDES_UNIT = prove
 (`!r u v:A. ring_unit r u ==> (ring_divides r v u <=> ring_unit r v)`,
  MESON_TAC[RING_UNIT_DIVISOR; RING_UNIT_DIVIDES_ALL; ring_unit]);;

let RING_COPRIME_REFL = prove
 (`!r a:A. ring_coprime r (a,a) <=> ring_unit r a`,
  REWRITE_TAC[ring_coprime] THEN
  MESON_TAC[RING_DIVIDES_UNIT; RING_DIVIDES_REFL]);;

let RING_COPRIME_SYM = prove
 (`!r a b:A. ring_coprime r (a,b) <=> ring_coprime r (b,a)`,
  REWRITE_TAC[ring_coprime] THEN MESON_TAC[]);;

let RING_COPRIME_0 = prove
 (`(!r a:A. ring_coprime r (ring_0 r,a) <=> ring_unit r a) /\
   (!r a:A. ring_coprime r (a,ring_0 r) <=> ring_unit r a)`,
  REWRITE_TAC[ring_coprime; RING_DIVIDES_0; RING_0] THEN
  MESON_TAC[RING_UNIT_DIVISOR; ring_unit; RING_DIVIDES_REFL]);;

let RING_COPRIME_00 = prove
 (`!r:A ring. ring_coprime r (ring_0 r,ring_0 r) <=> trivial_ring r`,
  REWRITE_TAC[RING_COPRIME_0; RING_UNIT_0]);;

let RING_ASSOCIATES_RMUL = prove
 (`!r a u:A.
        a IN ring_carrier r /\ ring_unit r u
        ==> ring_associates r a (ring_mul r a u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_unit; ring_associates] THEN
  SIMP_TAC[RING_DIVIDES_RMUL; RING_DIVIDES_REFL] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[ring_divides; RING_MUL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_MUL_RID]);;

let RING_ASSOCIATES_LMUL = prove
 (`!r a u:A.
        ring_unit r u /\ a IN ring_carrier r
        ==> ring_associates r a (ring_mul r u a)`,
  MESON_TAC[RING_ASSOCIATES_RMUL; RING_MUL_SYM; ring_unit]);;

let RING_ASSOCIATES_DIVIDES = prove
 (`!r a b a' b':A.
        ring_associates r a a' /\ ring_associates r b b'
        ==> (ring_divides r a b <=> ring_divides r a' b')`,
  REWRITE_TAC[ring_associates] THEN
  MESON_TAC[RING_DIVIDES_TRANS]);;

let RING_ASSOCIATES_ASSOCIATES = prove
 (`!r a b a' b':A.
        ring_associates r a a' /\ ring_associates r b b'
        ==> (ring_associates r a b <=> ring_associates r a' b')`,
  ASM_MESON_TAC[RING_ASSOCIATES_SYM; ring_associates; RING_DIVIDES_TRANS]);;

let RING_ASSOCIATES_UNIT = prove
 (`!r a a':A.
        ring_associates r a a' ==> (ring_unit r a <=> ring_unit r a')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RING_DIVIDES_ONE] THEN
  ASM_MESON_TAC[RING_ASSOCIATES_DIVIDES; RING_ASSOCIATES_REFL; RING_1]);;

let RING_ASSOCIATES_EQ_0 = prove
 (`!r a a':A.
        ring_associates r a a' ==> (a = ring_0 r <=> a' = ring_0 r)`,
  MESON_TAC[RING_ASSOCIATES_0; RING_ASSOCIATES_TRANS; RING_0]);;

let RING_ASSOCIATES_COPRIME = prove
 (`!r a b a' b':A.
        ring_associates r a a' /\ ring_associates r b b'
        ==> (ring_coprime r (a,b) <=> ring_coprime r (a',b'))`,
  REWRITE_TAC[ring_coprime] THEN
  MESON_TAC[RING_ASSOCIATES_DIVIDES; RING_ASSOCIATES_REFL;
            RING_ASSOCIATES_IN_CARRIER; ring_divides]);;

let RING_ASSOCIATES_ZERODIVISOR = prove
 (`!r a a':A.
        ring_associates r a a'
        ==> (ring_zerodivisor r a <=> ring_zerodivisor r a')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_ASSOCIATES_IN_CARRIER) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_associates]) THEN EQ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1); FIRST_X_ASSUM(MP_TAC o CONJUNCT2)] THEN
  ASM_REWRITE_TAC[ring_divides; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_SIMP_TAC[ring_zerodivisor; RING_MUL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[RING_MUL; RING_MUL_AC; RING_MUL_LZERO]);;

let RING_ASSOCIATES_REGULAR = prove
 (`!r a a':A.
        ring_associates r a a'
        ==> (ring_regular r a <=> ring_regular r a')`,
  REWRITE_TAC[ring_regular] THEN
  MESON_TAC[RING_ASSOCIATES_IN_CARRIER; RING_ASSOCIATES_ZERODIVISOR]);;

let RING_ASSOCIATES_NILPOTENT = prove
 (`!r a a':A.
        ring_associates r a a'
        ==> (ring_nilpotent r a <=> ring_nilpotent r a')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_nilpotent] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[RING_ASSOCIATES_IN_CARRIER]; ALL_TAC] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[RING_ASSOCIATES_EQ_0; RING_ASSOCIATES_POW]);;

let RING_NILPOTENT_0 = prove
 (`!r. ring_nilpotent r (ring_0 r)`,
  REWRITE_TAC[ring_nilpotent] THEN
  MESON_TAC[RING_0; RING_POW_1; ARITH_RULE `~(1 = 0)`]);;

let RING_NILPOTENT_1 = prove
 (`!r:A ring. ring_nilpotent r (ring_1 r) <=> trivial_ring r`,
  SIMP_TAC[ring_nilpotent; RING_POW_ONE; RING_1; TRIVIAL_RING_10] THEN
  MESON_TAC[ARITH_RULE `~(1 = 0)`]);;

let RING_NILPOTENT = prove
 (`!r a:A.
        ring_nilpotent r a <=>
        a IN ring_carrier r /\ ?n. ring_pow r a n = ring_0 r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_nilpotent] THEN
  EQ_TAC THENL [MESON_TAC[]; REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM]] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_REWRITE_TAC[ring_pow; GSYM TRIVIAL_RING_10] THEN
  REWRITE_TAC[trivial_ring] THEN DISCH_TAC THEN EXISTS_TAC `1` THEN
  ASM_SIMP_TAC[ARITH_EQ; RING_POW_1] THEN
  MP_TAC(ISPEC `r:A ring` RING_0) THEN ASM SET_TAC[]);;

let RING_NILPOTENT_POW = prove
 (`!r (x:A) n.
        x IN ring_carrier r /\ ~(n = 0)
        ==> (ring_nilpotent r (ring_pow r x n) <=> ring_nilpotent r x)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RING_NILPOTENT; RING_POW] THEN
  ASM_SIMP_TAC[GSYM RING_POW_MUL] THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[RING_POW_MUL; RING_POW_ZERO]);;

let RING_NILPOTENT_IMP_ZERODIVISOR = prove
 (`!r a:A. ~trivial_ring r /\ ring_nilpotent r a ==> ring_zerodivisor r a`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN
  ASM_SIMP_TAC[ring_nilpotent; ring_zerodivisor; LEFT_IMP_EXISTS_THM] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[ring_pow; NOT_SUC] THEN
  X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `ring_pow r (a:A) n = ring_0 r` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[RING_POW]] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_MESON_TAC[TRIVIAL_RING_10; ring_pow]; ASM_SIMP_TAC[]]);;

let RING_NILPOTENT_NEG = prove
 (`!r x:A. ring_nilpotent r x ==> ring_nilpotent r (ring_neg r x)`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_nilpotent; RING_NEG; IMP_CONJ] THEN
  DISCH_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[RING_POW_NEG; RING_NEG_0; COND_ID]);;

let RING_NILPOTENT_NEG_EQ = prove
 (`!r x:A.
        x IN ring_carrier r
        ==> (ring_nilpotent r (ring_neg r x) <=> ring_nilpotent r x)`,
  MESON_TAC[RING_NILPOTENT_NEG; RING_NILPOTENT_IN_CARRIER; RING_NEG_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Subrings. We treat them as *sets* which seems to be a common convention.  *)
(* And "subring_generated" can be used in the degenerate case where the set  *)
(* is closed under the operations to cast from "subset" to "ring".           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("subring_of",(12,"right"));;

let subring_of = new_definition
  `(s:A->bool) subring_of (r:A ring) <=>
        s SUBSET ring_carrier r /\
        ring_0 r IN s /\
        ring_1 r IN s /\
        (!x. x IN s ==> ring_neg r x IN s) /\
        (!x y. x IN s /\ y IN s ==> ring_add r x y IN s) /\
        (!x y. x IN s /\ y IN s ==> ring_mul r x y IN s)`;;

let subring_generated = new_definition
 `subring_generated r (s:A->bool) =
      ring(INTERS {h | h subring_of r /\ (ring_carrier r INTER s) SUBSET h},
           ring_0 r,ring_1 r,ring_neg r,ring_add r,ring_mul r)`;;

let IN_SUBRING_0 = prove
 (`!r h:A->bool. h subring_of r ==> ring_0 r IN h`,
  SIMP_TAC[subring_of]);;

let IN_SUBRING_1 = prove
 (`!r h:A->bool. h subring_of r ==> ring_1 r IN h`,
  SIMP_TAC[subring_of]);;

let IN_SUBRING_NEG = prove
 (`!r h x:A. h subring_of r /\ x IN h ==> ring_neg r x IN h`,
  SIMP_TAC[subring_of]);;

let IN_SUBRING_ADD = prove
 (`!r h x y:A. h subring_of r /\ x IN h /\ y IN h ==> ring_add r x y IN h`,
  SIMP_TAC[subring_of]);;

let IN_SUBRING_MUL = prove
 (`!r h x y:A. h subring_of r /\ x IN h /\ y IN h ==> ring_mul r x y IN h`,
  SIMP_TAC[subring_of]);;

let IN_SUBRING_SUB = prove
 (`!r h x y:A. h subring_of r /\ x IN h /\ y IN h ==> ring_sub r x y IN h`,
  SIMP_TAC[ring_sub; IN_SUBRING_ADD; IN_SUBRING_NEG]);;

let IN_SUBRING_POW = prove
 (`!r h (x:A) n. h subring_of r /\ x IN h ==> ring_pow r x n IN h`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_pow; IN_SUBRING_1; IN_SUBRING_MUL]);;

let SUBRING_OF_INTERS = prove
 (`!r (gs:(A->bool)->bool).
        (!g. g IN gs ==> g subring_of r) /\ ~(gs = {})
        ==> (INTERS gs) subring_of r`,
  REWRITE_TAC[subring_of; SUBSET; IN_INTERS] THEN SET_TAC[]);;

let SUBRING_OF_INTER = prove
 (`!r g h:A->bool.
        g subring_of r /\ h subring_of r ==> (g INTER h) subring_of r`,
  REWRITE_TAC[subring_of; SUBSET; IN_INTER] THEN SET_TAC[]);;

let SUBRING_OF_UNIONS = prove
 (`!r (u:(A->bool)->bool).
        ~(u = {}) /\
        (!h. h IN u ==> h subring_of r) /\
        (!g h. g IN u /\ h IN u ==> g SUBSET h \/ h SUBSET g)
        ==> (UNIONS u) subring_of r`,
  REWRITE_TAC[subring_of] THEN SET_TAC[]);;

let SUBRING_OF_IMP_SUBSET = prove
 (`!r s:A->bool. s subring_of r ==> s SUBSET ring_carrier r`,
  SIMP_TAC[subring_of]);;

let SUBRING_OF_IMP_NONEMPTY = prove
 (`!r s:A->bool. s subring_of r ==> ~(s = {})`,
  REWRITE_TAC[subring_of] THEN SET_TAC[]);;

let CARRIER_SUBRING_OF = prove
 (`!r:A ring. (ring_carrier r) subring_of r`,
  REWRITE_TAC[subring_of; SUBSET_REFL] THEN
  REWRITE_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let SUBRING_GENERATED = prove
 (`(!r s:A->bool.
        ring_carrier (subring_generated r s) =
          INTERS {h | h subring_of r /\ (ring_carrier r INTER s) SUBSET h}) /\
   (!r s:A->bool. ring_0 (subring_generated r s) = ring_0 r) /\
   (!r s:A->bool. ring_1 (subring_generated r s) = ring_1 r) /\
   (!r s:A->bool. ring_neg (subring_generated r s) = ring_neg r) /\
   (!r s:A->bool. ring_add (subring_generated r s) = ring_add r) /\
   (!r s:A->bool. ring_mul (subring_generated r s) = ring_mul r)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl subring_generated)))))
   (CONJUNCT2 ring_tybij)))) THEN
  REWRITE_TAC[GSYM subring_generated] THEN ANTS_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
    REPLICATE_TAC 4 (GEN_REWRITE_TAC I [CONJ_ASSOC]) THEN CONJ_TAC THENL
     [MESON_TAC[subring_of]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `ring_carrier r:A->bool`)) THEN
    REWRITE_TAC[INTER_SUBSET; SUBSET_REFL; CARRIER_SUBRING_OF] THEN
    ASM_SIMP_TAC[RING_ADD_LZERO; RING_ADD_LNEG; RING_MUL_LID] THEN
    ASM_SIMP_TAC[RING_ADD_LDISTRIB] THEN
    ASM_SIMP_TAC[RING_ADD_AC; RING_MUL_AC; RING_ADD; RING_MUL];
    DISCH_TAC THEN
    ASM_REWRITE_TAC[ring_carrier; ring_0; ring_1; ring_neg;
                    ring_add; ring_mul]]);;

let SUBRING_GENERATED_EQ = prove
 (`!G s:A->bool.
        subring_generated G s = G <=>
        ring_carrier(subring_generated G s) = ring_carrier G`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [RINGS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED]);;

let RING_SUB_SUBRING_GENERATED = prove
 (`!r s:A->bool. ring_sub (subring_generated r s) = ring_sub r`,
  REWRITE_TAC[FUN_EQ_THM; ring_sub; SUBRING_GENERATED]);;

let RING_POW_SUBRING_GENERATED = prove
 (`!r s:A->bool. ring_pow (subring_generated r s) = ring_pow r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; SUBRING_GENERATED]);;

let RING_OF_NUM_SUBRING_GENERATED = prove
 (`!r s:A->bool. ring_of_num (subring_generated r s) = ring_of_num r`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_of_num; SUBRING_GENERATED]);;

let RING_OF_INT_SUBRING_GENERATED = prove
 (`!r s:A->bool. ring_of_int (subring_generated r s) = ring_of_int r`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[ring_of_int; RING_OF_NUM_SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBRING_GENERATED]);;

let SUBRING_GENERATED_RESTRICT = prove
 (`!r s:A->bool.
        subring_generated r s =
        subring_generated r (ring_carrier r INTER s)`,
  REWRITE_TAC[subring_generated; SET_RULE `g INTER g INTER s = g INTER s`]);;

let SUBRING_SUBRING_GENERATED = prove
 (`!r s:A->bool. ring_carrier(subring_generated r s) subring_of r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBRING_GENERATED] THEN
  MATCH_MP_TAC SUBRING_OF_INTERS THEN
  SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `ring_carrier r:A->bool` THEN
  REWRITE_TAC[CARRIER_SUBRING_OF; INTER_SUBSET]);;

let SUBRING_GENERATED_MONO = prove
 (`!r s t:A->bool.
        s SUBSET t
        ==> ring_carrier(subring_generated r s) SUBSET
            ring_carrier(subring_generated r t)`,
  REWRITE_TAC[SUBRING_GENERATED] THEN SET_TAC[]);;

let SUBRING_GENERATED_MINIMAL = prove
 (`!r h s:A->bool.
        s SUBSET h /\ h subring_of r
        ==> ring_carrier(subring_generated r s) SUBSET h`,
  REWRITE_TAC[SUBRING_GENERATED; INTERS_GSPEC] THEN SET_TAC[]);;

let SUBRINGS_GENERATED_EQ = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier(subring_generated r t) /\
        t SUBSET ring_carrier(subring_generated r s)
        ==> subring_generated r s = subring_generated r t`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [RINGS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[SUBRING_GENERATED_MINIMAL; SUBRING_SUBRING_GENERATED]);;

let SUBRING_GENERATED_INDUCT = prove
 (`!r P s:A->bool.
        (!x. x IN ring_carrier r /\ x IN s ==> P x) /\
        P(ring_0 r) /\
        P(ring_1 r) /\
        (!x. P x ==> P(ring_neg r x)) /\
        (!x y. P x /\ P y ==> P(ring_add r x y)) /\
        (!x y. P x /\ P y ==> P(ring_mul r x y))
        ==> !x. x IN ring_carrier(subring_generated r s) ==> P x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IN_INTER] THEN
  ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT] THEN MP_TAC(SET_RULE
    `ring_carrier r INTER (s:A->bool) SUBSET ring_carrier r`) THEN
  SPEC_TAC(`ring_carrier r INTER (s:A->bool)`,`s:A->bool`) THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `{x:A | x IN ring_carrier r /\ P x}`;
                 `s:A->bool`] SUBRING_GENERATED_MINIMAL) THEN
  ANTS_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[subring_of; IN_ELIM_THM; SUBSET; RING_ADD; RING_NEG;
               RING_0; RING_1; RING_MUL]);;

let SUBRING_GENERATED_INDUCT_STRONG = prove
 (`!r P s:A->bool.
        (!x. x IN ring_carrier r /\ x IN s ==> P x) /\
        P(ring_0 r) /\
        P(ring_1 r) /\
        (!x. x IN ring_carrier r /\ P x ==> P(ring_neg r x)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_add r x y)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_mul r x y))
        ==> !x. x IN ring_carrier(subring_generated r s) ==> P x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN ring_carrier (subring_generated r s)
        ==> (x:A) IN ring_carrier r /\ P x`
  MP_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC SUBRING_GENERATED_INDUCT THEN
  ASM_SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let RING_CARRIER_SUBRING_GENERATED_SUBSET = prove
 (`!r h:A->bool.
        ring_carrier (subring_generated r h) SUBSET ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBRING_GENERATED] THEN
  MATCH_MP_TAC(SET_RULE `a IN s ==> INTERS s SUBSET a`) THEN
  REWRITE_TAC[IN_ELIM_THM; CARRIER_SUBRING_OF; INTER_SUBSET]);;

let SUBRING_OF_SUBRING_GENERATED_EQ = prove
 (`!r h k:A->bool.
        h subring_of (subring_generated r k) <=>
        h subring_of r /\ h SUBSET ring_carrier(subring_generated r k)`,
  REWRITE_TAC[subring_of; CONJUNCT2 SUBRING_GENERATED] THEN
  MESON_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET; SUBSET_TRANS]);;

let SUBRING_GENERATED_SUPERSET = prove
 (`!r s:A->bool.
    subring_generated r s = r <=>
    ring_carrier r SUBSET ring_carrier(subring_generated r s)`,
  REWRITE_TAC[SUBRING_GENERATED_EQ; GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET]);;

let FINITE_SUBRING_GENERATED = prove
 (`!r s:A->bool.
        FINITE(ring_carrier r)
        ==> FINITE(ring_carrier(subring_generated r s))`,
  MESON_TAC[FINITE_SUBSET; RING_CARRIER_SUBRING_GENERATED_SUBSET]);;

let SUBRING_GENERATED_SUBSET_CARRIER = prove
 (`!r h:A->bool.
     ring_carrier r INTER h SUBSET ring_carrier(subring_generated r h)`,
  REWRITE_TAC[subring_of; SUBRING_GENERATED; SUBSET_INTERS] THEN SET_TAC[]);;

let SUBSET_CARRIER_SUBRING_GENERATED = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier r /\ s SUBSET t
        ==> s SUBSET ring_carrier(subring_generated r t)`,
  MESON_TAC[SUBSET_TRANS; SUBSET_INTER; SUBRING_GENERATED_SUBSET_CARRIER]);;

let CARRIER_SUBRING_GENERATED_SUBRING = prove
 (`!r h:A->bool.
        h subring_of r ==> ring_carrier (subring_generated r h) = h`,
  REWRITE_TAC[subring_of; SUBRING_GENERATED; INTERS_GSPEC] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[SET_RULE `h SUBSET g ==> g INTER h = h`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL [GEN_REWRITE_TAC I [SUBSET]; ASM SET_TAC[]] THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `h:A->bool`) THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let SUBRING_GENERATED_MINIMAL_EQ = prove
 (`!r h s:A->bool.
        h subring_of r
        ==> (ring_carrier(subring_generated r s) SUBSET h <=>
             ring_carrier r INTER s SUBSET h)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
    REWRITE_TAC[SUBRING_GENERATED_SUBSET_CARRIER];
    ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT] THEN
    ASM_SIMP_TAC[SUBRING_GENERATED_MINIMAL]]);;

let SUBRING_OF_SUBRING_GENERATED_SUBRING_EQ = prove
 (`!r h k:A->bool.
        k subring_of r
        ==> (h subring_of (subring_generated r k) <=>
             h subring_of r /\ h SUBSET k)`,
  REWRITE_TAC[SUBRING_OF_SUBRING_GENERATED_EQ] THEN
  SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING]);;

let SUBRING_GENERATED_RING_CARRIER = prove
 (`!r:A ring. subring_generated r (ring_carrier r) = r`,
  GEN_TAC THEN REWRITE_TAC[RINGS_EQ] THEN
  SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; CARRIER_SUBRING_OF] THEN
  REWRITE_TAC[SUBRING_GENERATED]);;

let SUBRING_OF_SUBRING_GENERATED = prove
 (`!r g h:A->bool.
        g subring_of r /\ g SUBSET h
        ==> g subring_of (subring_generated r h)`,
  SIMP_TAC[subring_of; SUBRING_GENERATED; SUBSET_INTERS] THEN SET_TAC[]);;

let SUBRING_GENERATED_SUBSET_CARRIER_SUBSET = prove
 (`!r s:A->bool.
        s SUBSET ring_carrier r
        ==> s SUBSET ring_carrier(subring_generated r s)`,
  MESON_TAC[SUBRING_GENERATED_SUBSET_CARRIER;
            SET_RULE `s SUBSET t <=> t INTER s = s`]);;

let SUBRING_GENERATED_REFL = prove
 (`!r s:A->bool. ring_carrier r SUBSET s ==> subring_generated r s = r`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT] THEN
  ASM_SIMP_TAC[SET_RULE `u SUBSET s ==> u INTER s = u`] THEN
  REWRITE_TAC[SUBRING_GENERATED_RING_CARRIER]);;

let SUBRING_GENERATED_INC = prove
 (`!r s x:A.
        s SUBSET ring_carrier r /\ x IN s
        ==> x IN ring_carrier(subring_generated r s)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; GSYM SUBSET] THEN
  REWRITE_TAC[SUBRING_GENERATED_SUBSET_CARRIER_SUBSET]);;

let SUBRING_OF_SUBRING_GENERATED_REV = prove
 (`!r g h:A->bool.
        g subring_of (subring_generated r h)
        ==> g subring_of r`,
  SIMP_TAC[subring_of; CONJUNCT2 SUBRING_GENERATED] THEN
  MESON_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET; SUBSET_TRANS]);;

let TRIVIAL_RING_SUBRING_GENERATED = prove
 (`!r s:A->bool.
        trivial_ring(subring_generated r s) <=> trivial_ring r`,
  REWRITE_TAC[TRIVIAL_RING_10; CONJUNCT2 SUBRING_GENERATED]);;

let SUBRING_GENERATED_BY_SUBRING_GENERATED = prove
 (`!r s:A->bool.
        subring_generated r (ring_carrier(subring_generated r s)) =
        subring_generated r s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBRING_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    REWRITE_TAC[SUBRING_SUBRING_GENERATED; SUBSET_REFL];
    MATCH_MP_TAC SUBRING_GENERATED_SUBSET_CARRIER_SUBSET THEN
    REWRITE_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET]]);;

let SUBRING_GENERATED_INSERT_ZERO = prove
 (`!r s:A->bool.
        subring_generated r (ring_0 r INSERT s) = subring_generated r s`,
  REWRITE_TAC[RINGS_EQ; SUBRING_GENERATED] THEN
  REWRITE_TAC[EXTENSION; INTERS_GSPEC; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; TAUT
   `p /\ (q \/ r) ==> s <=> (q ==> p ==> s) /\ (p /\ r ==> s)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2; RING_0] THEN
  MESON_TAC[subring_of]);;

let RING_CARRIER_SUBRING_GENERATED_MONO = prove
 (`!r s t:A->bool.
        ring_carrier(subring_generated (subring_generated r s) t) SUBSET
        ring_carrier(subring_generated r t)`,
  ONCE_REWRITE_TAC[SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBRING_OF_SUBRING_GENERATED_EQ] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC INTERS_ANTIMONO_GEN THEN
  X_GEN_TAC `h:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `h INTER ring_carrier (subring_generated r s):A->bool` THEN
  REWRITE_TAC[INTER_SUBSET; SUBSET_INTER] THEN
  ASM_SIMP_TAC[SUBRING_OF_INTER; SUBRING_SUBRING_GENERATED] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
    RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN
  ASM SET_TAC[]);;

let SUBRING_GENERATED_IDEMPOT_GEN = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier(subring_generated r t)
        ==> subring_generated (subring_generated r t) s =
            subring_generated r s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBRING_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[RING_CARRIER_SUBRING_GENERATED_MONO] THEN
  MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
  ASM_SIMP_TAC[SUBRING_GENERATED_SUBSET_CARRIER_SUBSET] THEN
  MESON_TAC[SUBRING_OF_SUBRING_GENERATED_REV; SUBRING_SUBRING_GENERATED]);;

let SUBRING_GENERATED_IDEMPOT = prove
 (`!r s t:A->bool.
        s SUBSET t
        ==> subring_generated (subring_generated r t) s =
            subring_generated r s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBRING_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[RING_CARRIER_SUBRING_GENERATED_MONO] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [SUBRING_GENERATED_RESTRICT] THEN
  MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH rand SUBRING_GENERATED_SUBSET_CARRIER o
      rand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
    REWRITE_TAC[INTER_SUBSET; SUBSET_INTER] THEN
    MP_TAC(ISPECL [`r:A ring`; `t:A->bool`]
        SUBRING_GENERATED_SUBSET_CARRIER) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC SUBRING_OF_SUBRING_GENERATED_REV THEN
    EXISTS_TAC `t:A->bool` THEN REWRITE_TAC[SUBRING_SUBRING_GENERATED]]);;

let SUBRING_GENERATED_SUBRING_GENERATED = prove
 (`!r s t:A->bool.
        s subring_of r /\ t subring_of r
        ==> subring_generated (subring_generated r s) t =
            subring_generated r (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBRING_GENERATED] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SUBRING_GENERATED_RESTRICT] THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; SUBRING_OF_INTER] THEN
  MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN
  ASM_SIMP_TAC[SUBRING_OF_SUBRING_GENERATED_SUBRING_EQ] THEN
  ASM_SIMP_TAC[INTER_SUBSET; SUBRING_OF_INTER]);;

let SUBRING_GENERATED_BY_SUBRING_GENERATED_IDEMPOT = prove
 (`!r s t:A->bool.
        s SUBSET t
        ==> subring_generated (subring_generated r t)
                               (ring_carrier (subring_generated r s)) =
            subring_generated r s`,
  MESON_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED;
            SUBRING_GENERATED_IDEMPOT; SUBRING_GENERATED_MONO]);;

let SUBRING_GENERATED_UNION_LEFT = prove
 (`!r s t:A->bool.
        subring_generated r (ring_carrier(subring_generated r s) UNION t) =
        subring_generated r (s UNION t)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [RINGS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBRING_GENERATED_MINIMAL_EQ; SUBRING_SUBRING_GENERATED] THEN
  REWRITE_TAC[UNION_OVER_INTER; UNION_SUBSET] THEN
  SIMP_TAC[GSYM SUBRING_GENERATED_MINIMAL_EQ;
           SUBRING_SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC; ALL_TAC;
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [GSYM SUBRING_GENERATED_BY_SUBRING_GENERATED];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBRING_GENERATED_MONO THEN SET_TAC[]);;

let SUBRING_GENERATED_UNION_RIGHT = prove
 (`!r s t:A->bool.
        subring_generated r (s UNION ring_carrier(subring_generated r t)) =
        subring_generated r (s UNION t)`,
  ONCE_REWRITE_TAC[UNION_COMM] THEN
  REWRITE_TAC[SUBRING_GENERATED_UNION_LEFT]);;

let SUBRING_GENERATED_UNION = prove
 (`!r s t:A->bool.
        subring_generated r (ring_carrier(subring_generated r s) UNION
                              ring_carrier(subring_generated r t)) =
        subring_generated r (s UNION t)`,
  REWRITE_TAC[SUBRING_GENERATED_UNION_LEFT;
              SUBRING_GENERATED_UNION_RIGHT]);;

let RING_CHAR_SUBRING_GENERATED = prove
 (`!r s:A->bool. ring_char(subring_generated r s) = ring_char r`,
  REWRITE_TAC[RING_CHAR_UNIQUE] THEN
  REWRITE_TAC[SUBRING_GENERATED; RING_OF_NUM_SUBRING_GENERATED] THEN
  REWRITE_TAC[RING_OF_NUM_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Ideals, with some quite analogous properties to subrings in many cases.   *)
(* ------------------------------------------------------------------------- *)

let ring_ideal = new_definition
 `ring_ideal (r:A ring) j <=>
        j SUBSET ring_carrier r /\
        ring_0 r IN j /\
        (!x. x IN j ==> ring_neg r x IN j) /\
        (!x y. x IN j /\ y IN j ==> ring_add r x y IN j) /\
        (!x y. x IN ring_carrier r /\ y IN j ==> ring_mul r x y IN j)`;;

let RING_IDEAL_IMP_SUBSET = prove
 (`!r s:A->bool. ring_ideal r s ==> s SUBSET ring_carrier r`,
  SIMP_TAC[ring_ideal]);;

let RING_IDEAL_IMP_NONEMPTY = prove
 (`!r s:A->bool. ring_ideal r s ==> ~(s = {})`,
  REWRITE_TAC[ring_ideal] THEN SET_TAC[]);;

let RING_IDEAL_0 = prove
 (`!r:A ring. ring_ideal r {ring_0 r}`,
  REWRITE_TAC[ring_ideal; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2; SING_SUBSET] THEN
  SIMP_TAC[RING_MUL_RZERO; RING_NEG_0; RING_0; RING_ADD_LZERO]);;

let IN_RING_IDEAL_0 = prove
 (`!r h:A->bool. ring_ideal r h ==> ring_0 r IN h`,
  SIMP_TAC[ring_ideal]);;

let IN_RING_IDEAL_NEG = prove
 (`!r h x:A. ring_ideal r h /\ x IN h ==> ring_neg r x IN h`,
  SIMP_TAC[ring_ideal]);;

let IN_RING_IDEAL_ADD = prove
 (`!r h x y:A. ring_ideal r h /\ x IN h /\ y IN h ==> ring_add r x y IN h`,
  SIMP_TAC[ring_ideal]);;

let IN_RING_IDEAL_SUB = prove
 (`!r h x y:A. ring_ideal r h /\ x IN h /\ y IN h ==> ring_sub r x y IN h`,
  SIMP_TAC[ring_sub; IN_RING_IDEAL_ADD; IN_RING_IDEAL_NEG]);;

let IN_RING_IDEAL_MUL = prove
 (`!r h x y:A. ring_ideal r h /\ x IN h /\ y IN h ==> ring_mul r x y IN h`,
  SIMP_TAC[ring_ideal; SUBSET]);;

let IN_RING_IDEAL_LMUL = prove
 (`!r h x y:A.
     ring_ideal r h /\ x IN ring_carrier r /\ y IN h ==> ring_mul r x y IN h`,
  REWRITE_TAC[ring_ideal; SUBSET] THEN MESON_TAC[RING_MUL_SYM]);;

let IN_RING_IDEAL_RMUL = prove
 (`!r h x y:A.
     ring_ideal r h /\ x IN h /\ y IN ring_carrier r ==> ring_mul r x y IN h`,
  REWRITE_TAC[ring_ideal; SUBSET] THEN MESON_TAC[RING_MUL_SYM]);;

let RING_MULTIPLE_IN_IDEAL = prove
 (`!r j a b:A. ring_ideal r j /\ a IN j /\ ring_divides r a b ==> b IN j`,
  REWRITE_TAC[ring_divides] THEN MESON_TAC[IN_RING_IDEAL_RMUL]);;

let RING_POW_IN_IDEAL = prove
 (`!r j (x:A) n.
        ring_ideal r j /\ x IN j /\ ~(n = 0) ==> ring_pow r x n IN j`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[NOT_SUC] THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[ring_pow; RING_MUL_RID; IN_RING_IDEAL_LMUL]);;

let IN_RING_IDEAL_SUM = prove
 (`!r j s (f:K->A).
        ring_ideal r j /\ (!i. i IN s ==> f i IN j) ==> ring_sum r s f IN j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[]
        (ISPECL [`r:A ring`; `\x:A. x IN j`] RING_SUM_CLOSED)) THEN
  ASM_MESON_TAC[ring_ideal; SUBSET]);;

let RING_ASSOCIATES_IN_IDEAL = prove
 (`!r j a a'.
        ring_ideal r j /\ ring_associates r a a'
        ==> (a IN j <=> a' IN j)`,
  REWRITE_TAC[ring_associates] THEN MESON_TAC[RING_MULTIPLE_IN_IDEAL]);;

let RING_IDEAL_INTERS = prove
 (`!r (gs:(A->bool)->bool).
        (!g. g IN gs ==> ring_ideal r g) /\ ~(gs = {})
        ==> ring_ideal r (INTERS gs)`,
  REWRITE_TAC[ring_ideal; SUBSET; IN_INTERS] THEN SET_TAC[]);;

let RING_IDEAL_INTER = prove
 (`!r g h:A->bool.
        ring_ideal r g /\ ring_ideal r h ==> ring_ideal r (g INTER h)`,
  REWRITE_TAC[ring_ideal; SUBSET; IN_INTER] THEN SET_TAC[]);;

let RING_IDEAL_UNIONS = prove
 (`!r (u:(A->bool)->bool).
        ~(u = {}) /\
        (!h. h IN u ==> ring_ideal r h) /\
        (!g h. g IN u /\ h IN u ==> g SUBSET h \/ h SUBSET g)
        ==> ring_ideal r (UNIONS u)`,
  REWRITE_TAC[ring_ideal] THEN SET_TAC[]);;

let RING_IDEAL_EQ_CARRIER = prove
 (`!(r:A ring) j.
        ring_ideal r j ==> (j = ring_carrier r <=> ring_1 r IN j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [MESON_TAC[RING_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[IN_RING_IDEAL_RMUL; RING_MUL_LID]);;

let RING_IDEAL_EQ_CARRIER_UNIT = prove
 (`!(r:A ring) j.
        ring_ideal r j
        ==> (j = ring_carrier r <=> ?u. ring_unit r u /\ u IN j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RING_IDEAL_EQ_CARRIER] THEN
  EQ_TAC THENL [MESON_TAC[RING_UNIT_1]; ALL_TAC] THEN
  REWRITE_TAC[ring_unit] THEN ASM_MESON_TAC[IN_RING_IDEAL_RMUL]);;

let TRIVIAL_RING_IDEAL = prove
 (`!r:A ring. ring_ideal r {ring_0 r}`,
  SIMP_TAC[ring_ideal; IN_SING; SING_SUBSET] THEN
  SIMP_TAC[RING_ADD_LZERO; RING_0; RING_MUL_RZERO; RING_NEG_0]);;

let RING_IDEAL_CARRIER = prove
 (`!r:A ring. ring_ideal r (ring_carrier r)`,
  REWRITE_TAC[ring_ideal; SUBSET_REFL] THEN
  SIMP_TAC[RING_0; RING_NEG; RING_ADD; RING_MUL]);;

let RING_IDEAL_SUBRING_GENERATED_EQ = prove
 (`!r s j:A->bool.
        s subring_of r /\ ring_ideal r j
        ==> (ring_ideal (subring_generated r s) j <=> j SUBSET s)`,
  SIMP_TAC[ring_ideal; CARRIER_SUBRING_GENERATED_SUBRING] THEN
  SIMP_TAC[SUBRING_GENERATED] THEN
  REWRITE_TAC[subring_of] THEN SET_TAC[]);;

let RING_IDEAL_SUBRING_GENERATED = prove
 (`!r s j:A->bool.
        s subring_of r /\ ring_ideal r j /\ j SUBSET s
        ==> ring_ideal (subring_generated r s) j`,
  SIMP_TAC[RING_IDEAL_SUBRING_GENERATED_EQ]);;

let RING_SUBRING_INTER_IDEAL = prove
 (`!r s j:A->bool.
        s subring_of r /\ ring_ideal r j
        ==> ring_ideal (subring_generated r s) (s INTER j)`,
  SIMP_TAC[ring_ideal; CARRIER_SUBRING_GENERATED_SUBRING] THEN
  SIMP_TAC[SUBRING_GENERATED; IN_INTER; subring_of] THEN
  SET_TAC[]);;

let RING_IDEAL_INTER_SUBRING = prove
 (`!r s j:A->bool.
        s subring_of r /\ ring_ideal r j
        ==> ring_ideal (subring_generated r s) (j INTER s)`,
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  REWRITE_TAC[RING_SUBRING_INTER_IDEAL]);;

(* ------------------------------------------------------------------------- *)
(* Setwise operations.                                                       *)
(* ------------------------------------------------------------------------- *)

let ring_setneg = new_definition
  `ring_setneg (r:A ring) s = {ring_neg r x | x IN s}`;;

let ring_setadd = new_definition
   `ring_setadd (r:A ring) s t = {ring_add r x y | x IN s /\ y IN t}`;;

let ring_setmul = new_definition
   `ring_setmul (r:A ring) s t = {ring_mul r x y | x IN s /\ y IN t}`;;

let RING_NEG_IN_SETNEG = prove
 (`!r s x:A. x IN s ==> ring_neg r x IN ring_setneg r s`,
  REWRITE_TAC[ring_setneg; IN_ELIM_THM] THEN MESON_TAC[]);;

let RING_ADD_IN_SETADD = prove
 (`!r s t x y:A.
        x IN s /\ y IN t ==> ring_add r x y IN ring_setadd r s t`,
  REWRITE_TAC[ring_setadd; IN_ELIM_THM] THEN MESON_TAC[]);;

let RING_MUL_IN_SETMUL = prove
 (`!r s t x y:A.
        x IN s /\ y IN t ==> ring_mul r x y IN ring_setmul r s t`,
  REWRITE_TAC[ring_setmul; IN_ELIM_THM] THEN MESON_TAC[]);;

let RING_SETNEG_MONO = prove
 (`!r s s':A->bool.
        s SUBSET s' ==> ring_setneg r s SUBSET ring_setneg r s'`,
  REWRITE_TAC[ring_setneg] THEN SET_TAC[]);;

let RING_SETADD_MONO = prove
 (`!r s t s' t':A->bool.
        s SUBSET s' /\ t SUBSET t'
        ==> ring_setadd r s t SUBSET ring_setadd r s' t'`,
  REWRITE_TAC[ring_setadd] THEN SET_TAC[]);;

let RING_SETMUL_MONO = prove
 (`!r s t s' t':A->bool.
        s SUBSET s' /\ t SUBSET t'
        ==> ring_setmul r s t SUBSET ring_setmul r s' t'`,
  REWRITE_TAC[ring_setmul] THEN SET_TAC[]);;

let SUBRING_OF_SETWISE = prove
 (`!r s:A->bool.
        s subring_of r <=>
        s SUBSET ring_carrier r /\
        ring_0 r IN s /\
        ring_1 r IN s /\
        ring_setneg r s SUBSET s /\
        ring_setadd r s s SUBSET s /\
        ring_setmul r s s SUBSET s`,
  REWRITE_TAC[subring_of; ring_setneg; ring_setadd; ring_setmul] THEN
  SET_TAC[]);;

let RING_IDEAL_SETWISE = prove
 (`!r j:A->bool.
        ring_ideal r j <=>
        j SUBSET ring_carrier r /\
        ring_0 r IN j /\
        ring_setneg r j SUBSET j /\
        ring_setadd r j j SUBSET j /\
        ring_setmul r (ring_carrier r) j SUBSET j`,
  REWRITE_TAC[ring_ideal; ring_setneg; ring_setadd; ring_setmul] THEN
  SET_TAC[]);;

let RING_SETNEG_EQ_EMPTY = prove
 (`!r s:A->bool. ring_setneg r s = {} <=> s = {}`,
  REWRITE_TAC[ring_setneg] THEN SET_TAC[]);;

let RING_SETADD_EQ_EMPTY = prove
 (`!r s t:A->bool. ring_setadd r s t = {} <=> s = {} \/ t = {}`,
  REWRITE_TAC[ring_setadd] THEN SET_TAC[]);;

let RING_SETMUL_EQ_EMPTY = prove
 (`!r s t:A->bool. ring_setmul r s t = {} <=> s = {} \/ t = {}`,
  REWRITE_TAC[ring_setmul] THEN SET_TAC[]);;

let RING_SETNEG_SING = prove
 (`!r x:A. ring_setneg r {x} = {ring_neg r x}`,
  REWRITE_TAC[ring_setneg] THEN SET_TAC[]);;

let RING_SETADD_SING = prove
 (`!r x y:A. ring_setadd r {x} {y} = {ring_add r x y}`,
  REWRITE_TAC[ring_setadd] THEN SET_TAC[]);;

let RING_SETMUL_SING = prove
 (`!r x y:A. ring_setmul r {x} {y} = {ring_mul r x y}`,
  REWRITE_TAC[ring_setmul] THEN SET_TAC[]);;

let RING_SETNEG = prove
 (`!r s:A->bool.
        s SUBSET ring_carrier r ==> ring_setneg r s SUBSET ring_carrier r`,
  SIMP_TAC[ring_setneg; SUBSET; FORALL_IN_GSPEC; RING_NEG]);;

let RING_SETADD = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==>  ring_setadd r s t SUBSET ring_carrier r`,
  SIMP_TAC[ring_setadd; SUBSET; FORALL_IN_GSPEC; RING_ADD]);;

let RING_SETMUL = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==>  ring_setmul r s t SUBSET ring_carrier r`,
  SIMP_TAC[ring_setmul; SUBSET; FORALL_IN_GSPEC; RING_MUL]);;

let RING_SETADD_SYM = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ring_setadd r s t = ring_setadd r t s`,
  REWRITE_TAC[SUBSET; EXTENSION; IN_ELIM_THM; ring_setadd] THEN
  MESON_TAC[RING_ADD_SYM]);;

let RING_SETMUL_SYM = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ring_setmul r s t = ring_setmul r t s`,
  REWRITE_TAC[SUBSET; EXTENSION; IN_ELIM_THM; ring_setmul] THEN
  MESON_TAC[RING_MUL_SYM]);;

let RING_SETADD_LZERO = prove
 (`!r s:A->bool.
        s SUBSET ring_carrier r ==> ring_setadd r {ring_0 r} s = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_setadd] THEN MATCH_MP_TAC(SET_RULE
   `(!y. y IN s ==> f a y = y) ==> {f x y | x IN {a} /\ y IN s} = s`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_SIMP_TAC[RING_ADD_LZERO]);;

let RING_SETADD_RZERO = prove
 (`!r s:A->bool.
        s SUBSET ring_carrier r ==> ring_setadd r s {ring_0 r} = s`,
  MESON_TAC[RING_SETADD_SYM; RING_SETADD_LZERO; RING_0; SING_SUBSET]);;

let RING_SETMUL_LID = prove
 (`!r s:A->bool.
        s SUBSET ring_carrier r ==> ring_setmul r {ring_1 r} s = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_setmul] THEN MATCH_MP_TAC(SET_RULE
   `(!y. y IN s ==> f a y = y) ==> {f x y | x IN {a} /\ y IN s} = s`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_SIMP_TAC[RING_MUL_LID]);;

let RING_SETMUL_RID = prove
 (`!r s:A->bool.
        s SUBSET ring_carrier r ==> ring_setmul r s {ring_1 r} = s`,
  MESON_TAC[RING_SETMUL_SYM; RING_SETMUL_LID; RING_1; SING_SUBSET]);;

let RING_SETADD_ASSOC = prove
 (`!r s t u:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r /\
        u SUBSET ring_carrier r
        ==> ring_setadd r s (ring_setadd r t u) =
            ring_setadd r (ring_setadd r s t) u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_setadd] THEN
  REWRITE_TAC[SET_RULE
   `{f x y |x,y| x IN s /\ y IN {g w z | w IN t /\ z IN u}} =
    {f x (g y z) | x IN s /\ y IN t /\ z IN u}`] THEN
  REWRITE_TAC[SET_RULE
   `{f x y |x,y| x IN {g w z | w IN s /\ z IN t} /\ y IN u} =
    {f (g x y) z | x IN s /\ y IN t /\ z IN u}`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y z. P x y z ==> f x y z = g x y z)
    ==> {f x y z | P x y z} = {g x y z | P x y z}`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_ADD_ASSOC THEN
  ASM SET_TAC[]);;

let RING_SETMUL_ASSOC = prove
 (`!r s t u:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r /\
        u SUBSET ring_carrier r
        ==> ring_setmul r s (ring_setmul r t u) =
            ring_setmul r (ring_setmul r s t) u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_setmul] THEN
  REWRITE_TAC[SET_RULE
   `{f x y |x,y| x IN s /\ y IN {g w z | w IN t /\ z IN u}} =
    {f x (g y z) | x IN s /\ y IN t /\ z IN u}`] THEN
  REWRITE_TAC[SET_RULE
   `{f x y |x,y| x IN {g w z | w IN s /\ z IN t} /\ y IN u} =
    {f (g x y) z | x IN s /\ y IN t /\ z IN u}`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y z. P x y z ==> f x y z = g x y z)
    ==> {f x y z | P x y z} = {g x y z | P x y z}`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_ASSOC THEN
  ASM SET_TAC[]);;

let RING_SETADD_AC = prove
 (`!r:A ring.
        (!s t. s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
               ==> ring_setadd r s t = ring_setadd r t s) /\
        (!s t u. s SUBSET ring_carrier r /\ t SUBSET ring_carrier r /\
                 u SUBSET ring_carrier r
                 ==> ring_setadd r (ring_setadd r s t) u =
                     ring_setadd r s (ring_setadd r t u)) /\
        (!s t u. s SUBSET ring_carrier r /\ t SUBSET ring_carrier r /\
                 u SUBSET ring_carrier r
                 ==> ring_setadd r s (ring_setadd r t u) =
                     ring_setadd r t (ring_setadd r s u))`,
  MESON_TAC[RING_SETADD_SYM; RING_SETADD_ASSOC; RING_SETADD]);;

let RING_SETMUL_AC = prove
 (`!r:A ring.
        (!s t. s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
               ==> ring_setmul r s t = ring_setmul r t s) /\
        (!s t u. s SUBSET ring_carrier r /\ t SUBSET ring_carrier r /\
                 u SUBSET ring_carrier r
                 ==> ring_setmul r (ring_setmul r s t) u =
                     ring_setmul r s (ring_setmul r t u)) /\
        (!s t u. s SUBSET ring_carrier r /\ t SUBSET ring_carrier r /\
                 u SUBSET ring_carrier r
                 ==> ring_setmul r s (ring_setmul r t u) =
                     ring_setmul r t (ring_setmul r s u))`,
  MESON_TAC[RING_SETMUL_SYM; RING_SETMUL_ASSOC; RING_SETMUL]);;

let RING_SETADD_SUPERSET_LEFT = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier r /\ ring_0 r IN t
        ==> s SUBSET ring_setadd r s t`,
  REWRITE_TAC[SUBSET; ring_setadd; IN_ELIM_THM] THEN
  MESON_TAC[RING_ADD_RZERO]);;

let RING_SETADD_SUPERSET_RIGHT = prove
 (`!r s t:A->bool.
        ring_0 r IN s /\ t SUBSET ring_carrier r
        ==> t SUBSET ring_setadd r s t`,
  REWRITE_TAC[SUBSET; ring_setadd; IN_ELIM_THM] THEN
  MESON_TAC[RING_ADD_LZERO]);;

let RING_SETNEG_SETADD = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ring_setneg r (ring_setadd r s t) =
            ring_setadd r (ring_setneg r s) (ring_setneg r t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; ring_setneg; ring_setadd; IN_ELIM_THM] THEN
  ASM_MESON_TAC[SUBSET; RING_NEG_ADD; RING_NEG; RING_ADD]);;

let RING_SETADD_LDISTRIB = prove
 (`!r s t u:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r /\
        u SUBSET ring_carrier r
        ==> ring_setmul r s (ring_setadd r t u) SUBSET
            ring_setadd r (ring_setmul r s t) (ring_setmul r s u)`,
  REWRITE_TAC[SUBSET; ring_setadd; ring_setmul; IN_ELIM_THM] THEN
  MESON_TAC[RING_ADD_LDISTRIB; RING_MUL; RING_ADD]);;

let RING_SETADD_RDISTRIB = prove
 (`!r s t u:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r /\
        u SUBSET ring_carrier r
        ==> ring_setmul r (ring_setadd r s t) u SUBSET
            ring_setadd r (ring_setmul r s u) (ring_setmul r t u)`,
  REWRITE_TAC[SUBSET; ring_setadd; ring_setmul; IN_ELIM_THM] THEN
  MESON_TAC[RING_ADD_RDISTRIB; RING_MUL; RING_ADD]);;

let RING_SETNEG_IDEAL = prove
 (`!r j:A->bool. ring_ideal r j ==> ring_setneg r j = j`,
  REWRITE_TAC[ring_setneg; ring_ideal; SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x IN s /\ f(f x) = x) ==> {f x | x IN s} = s`) THEN
  ASM_SIMP_TAC[RING_NEG_NEG]);;

let RING_SETNEG_SUBRING = prove
 (`!r s:A->bool. s subring_of r ==> ring_setneg r s = s`,
  REWRITE_TAC[ring_setneg; subring_of; SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x IN s /\ f(f x) = x) ==> {f x | x IN s} = s`) THEN
  ASM_SIMP_TAC[RING_NEG_NEG]);;

let RING_SETADD_LSUBSET = prove
 (`!r j s:A->bool.
        (ring_ideal r j \/ j subring_of r) /\
        s SUBSET j /\ ~(s = {}) ==> ring_setadd r s j = j`,
  REWRITE_TAC[ring_setadd; ring_ideal; subring_of; SUBSET] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; RING_ADD; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MAP_EVERY EXISTS_TAC [`y:A`; `ring_add r (ring_neg r y) x:A`] THEN
  ASM_SIMP_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_ADD_ASSOC o rand o snd) THEN
  ASM_SIMP_TAC[RING_ADD; RING_NEG; RING_ADD_RNEG; RING_ADD_LZERO]);;

let RING_SETADD_RSUBSET = prove
 (`!r j s:A->bool.
        (ring_ideal r j \/ j subring_of r) /\
        s SUBSET j /\ ~(s = {}) ==> ring_setadd r j s = j`,
  MESON_TAC[RING_SETADD_LSUBSET; RING_SETADD_SYM;
            ring_ideal; subring_of; SUBSET_TRANS]);;

let RING_SETADD_LSUBSET_EQ = prove
 (`!r j s:A->bool.
        (ring_ideal r j \/ j subring_of r) /\ s SUBSET ring_carrier r
        ==> (ring_setadd r s j = j <=> s SUBSET j /\ ~(s = {}))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
   [ASM_MESON_TAC[RING_SETADD_EQ_EMPTY; RING_IDEAL_IMP_NONEMPTY;
                  SUBRING_OF_IMP_NONEMPTY];
    ASM_REWRITE_TAC[]] THEN
  EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RING_SETADD_LSUBSET]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ring_setadd; IN_ELIM_THM; SUBSET] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:A`; `ring_0 r:A`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_ideal; subring_of; SUBSET]) THEN
  ASM_MESON_TAC[RING_ADD_RZERO]);;

let RING_SETADD_RSUBSET_EQ = prove
 (`!r j s:A->bool.
        (ring_ideal r j \/ j subring_of r) /\
        s SUBSET ring_carrier r
        ==> (ring_setadd r j s = j <=> s SUBSET j /\ ~(s = {}))`,
  MESON_TAC[RING_SETADD_LSUBSET_EQ; RING_SETADD_SYM;
            ring_ideal; subring_of; SUBSET_TRANS]);;

let RING_SETADD_SUBRING = prove
 (`!r j:A->bool.
        (ring_ideal r j \/ j subring_of r) ==> ring_setadd r j j = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SETADD_LSUBSET THEN
  ASM_MESON_TAC[SUBRING_OF_IMP_NONEMPTY; RING_IDEAL_IMP_NONEMPTY;
                SUBSET_REFL]);;

let RING_SETMUL_SUBRING = prove
 (`!r s:A->bool.
        s subring_of r ==> ring_setmul r s s = s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBRING_OF_SETWISE]; ALL_TAC] THEN
  REWRITE_TAC[ring_setmul; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `ring_1 r:A`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[subring_of; SUBSET]) THEN
  ASM_MESON_TAC[RING_MUL_RID; RING_1]);;

let RING_SETADD_SUBSET_IDEAL = prove
 (`!r j s t:A->bool.
        ring_ideal r j /\ s SUBSET j /\ t SUBSET j
        ==> ring_setadd r s t SUBSET j`,
  SIMP_TAC[ring_setadd; SUBSET; FORALL_IN_GSPEC; ring_ideal] THEN SET_TAC[]);;

let RING_SETADD_IDEAL_LEFT = prove
 (`!r j s t:A->bool.
        (ring_ideal r j \/ j subring_of r) /\
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ring_setadd r (ring_setadd r j s) (ring_setadd r j t) =
            ring_setadd r j (ring_setadd r s t)`,
  REPEAT STRIP_TAC THEN
  (TRANS_TAC EQ_TRANS
    `ring_setadd r (ring_setadd r j j) (ring_setadd r s t):A->bool` THEN
   CONJ_TAC THENL
    [ASM_SIMP_TAC[RING_SETADD_AC; RING_SETADD; RING_IDEAL_IMP_SUBSET;
                  SUBRING_OF_IMP_SUBSET];
     ASM_SIMP_TAC[RING_SETADD_SUBRING]]));;

let RING_SETADD_IDEAL_RIGHT = prove
 (`!r j s t:A->bool.
        (ring_ideal r j \/ j subring_of r) /\
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ring_setadd r (ring_setadd r s j) (ring_setadd r t j) =
            ring_setadd r (ring_setadd r s t) j`,
  REPEAT STRIP_TAC THEN
  (TRANS_TAC EQ_TRANS
    `ring_setadd r (ring_setadd r s t) (ring_setadd r j j) :A->bool` THEN
   CONJ_TAC THENL
    [ASM_SIMP_TAC[RING_SETADD_AC; RING_SETADD; RING_IDEAL_IMP_SUBSET;
                  SUBRING_OF_IMP_SUBSET];
     ASM_SIMP_TAC[RING_SETADD_SUBRING]]));;

let RING_SETMUL_IDEAL_LEFT = prove
 (`!r j s t:A->bool.
        ring_ideal r j /\
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ring_setmul r (ring_setadd r j s) (ring_setadd r j t) SUBSET
            ring_setadd r j (ring_setmul r s t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ring_setmul; ring_setadd; SUBSET; FORALL_IN_GSPEC;
              IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `a:A`; `y:A`; `b:A`] THEN STRIP_TAC THEN
  REWRITE_TAC[SET_RULE
   `{f x y |x,y| x IN s /\ y IN {g w z | w IN t /\ z IN u}} =
    {f x (g y z) | x IN s /\ y IN t /\ z IN u}`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC
   [`ring_add r (ring_mul r x y)
                (ring_add r (ring_mul r a y) (ring_mul r x b)):A`;
    `a:A`; `b:A`] THEN
 FIRST_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
 RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
 ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
  [SUBSET; IN_RING_IDEAL_ADD; IN_RING_IDEAL_LMUL; RING_ADD_LDISTRIB;
   IN_RING_IDEAL_RMUL; RING_ADD; RING_MUL] THEN
 ASM_SIMP_TAC[RING_ADD; RING_ADD_RDISTRIB] THEN
 ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
  [GSYM RING_ADD_ASSOC; RING_MUL; RING_ADD]);;

let RING_SETMUL_IDEAL_RIGHT = prove
 (`!r j s t:A->bool.
        ring_ideal r j /\
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ring_setmul r (ring_setadd r s j) (ring_setadd r t j) SUBSET
            ring_setadd r (ring_setmul r s t) j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_SETMUL_IDEAL_LEFT) THEN
  ASM_SIMP_TAC[RING_SETADD_AC; RING_SETMUL; RING_IDEAL_IMP_SUBSET]);;

let RING_SETMUL_SUBSET_IDEAL = prove
 (`!r j s t:A->bool.
        ring_ideal r j /\
        (s SUBSET j /\ t SUBSET ring_carrier r \/
         s SUBSET ring_carrier r /\ t SUBSET j)
        ==> ring_setmul r s t SUBSET j`,
  SIMP_TAC[ring_setmul; SUBSET; FORALL_IN_GSPEC; ring_ideal] THEN
  MESON_TAC[RING_MUL_SYM]);;

let RING_SETADD_LCANCEL = prove
 (`!r s t x:A.
        x IN ring_carrier r /\
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> (ring_setadd r {x} s = ring_setadd r {x} t <=> s = t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `ring_setadd r {ring_neg r x:A}`) THEN
  ASM_SIMP_TAC[RING_SETADD_ASSOC; SING_SUBSET; RING_NEG] THEN
  ASM_SIMP_TAC[RING_SETADD_SING; RING_ADD_LNEG; RING_SETADD_LZERO]);;

let RING_SETADD_RCANCEL = prove
 (`!r s t x:A.
        x IN ring_carrier r /\ s SUBSET ring_carrier r /\
        t SUBSET ring_carrier r
        ==> (ring_setadd r s {x} = ring_setadd r t {x} <=> s = t)`,
  MESON_TAC[RING_SETADD_LCANCEL; RING_SETADD_SYM; SING_SUBSET]);;

let RING_SETADD_LCANCEL_SET = prove
 (`!r j x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\
        (ring_ideal r j \/ j subring_of r)
        ==> (ring_setadd r j {x} = ring_setadd r j {y} <=>
             ring_sub r x y IN j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(j:A->bool) SUBSET ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBRING_OF_IMP_SUBSET; RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ring_setadd r (ring_setadd r j {x}) {ring_neg r y}  =
    ring_setadd r (ring_setadd r j {y:A}) {ring_neg r y}` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SETADD_RCANCEL THEN
    ASM_SIMP_TAC[RING_NEG; RING_SETADD; SING_SUBSET];
    ASM_SIMP_TAC[GSYM RING_SETADD_ASSOC; RING_NEG; SING_SUBSET] THEN
    ASM_SIMP_TAC[RING_SETADD_SING; RING_ADD_RNEG; RING_SETADD_RZERO] THEN
    ASM_SIMP_TAC[RING_SETADD_RSUBSET_EQ; SING_SUBSET; ring_sub;
                 RING_NEG; RING_ADD; NOT_INSERT_EMPTY]]);;

let RING_SETADD_RCANCEL_SET = prove
 (`!r j x y:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\
        (ring_ideal r j \/ j subring_of r)
        ==> (ring_setadd r {x} j = ring_setadd r {y} j <=>
             ring_sub r x y IN j)`,
  MESON_TAC[RING_SETADD_LCANCEL_SET; RING_SETADD_SYM; SING_SUBSET;
            SUBRING_OF_IMP_SUBSET; RING_IDEAL_IMP_SUBSET]);;

let RING_IDEAL_SETADD = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k
        ==> ring_ideal r (ring_setadd r j k)`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_ideal; RING_SETADD] THEN
  REWRITE_TAC[SUBSET; ring_setadd] THEN STRIP_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(EXISTS_TAC `ring_0 r:A`) THEN ASM_SIMP_TAC[RING_ADD_LZERO; RING_0];
    ASM_SIMP_TAC[RING_NEG_ADD] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x1:A`; `y1:A`; `x2:A`; `y2:A`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ring_add r x1 x2:A`; `ring_add r y1 y2:A`] THEN
    ASM_SIMP_TAC[RING_ADD_AC; RING_ADD];
    ASM_SIMP_TAC[RING_ADD_LDISTRIB] THEN ASM_MESON_TAC[RING_MUL]]);;

let SUBRING_SETADD_LEFT = prove
 (`!r j s:A->bool.
        ring_ideal r j /\ s subring_of r
        ==> (ring_setadd r j s) subring_of r`,
  REWRITE_TAC[ring_ideal; subring_of; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[ring_setadd; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_ADD]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_0; RING_ADD_LZERO]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_1; RING_ADD_LZERO]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`a:A`; `x:A`] THENL
   [ASM_MESON_TAC[RING_NEG_ADD; RING_ADD; RING_NEG]; DISCH_TAC; DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `y:A`] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`ring_add r a b:A`; `ring_add r x y:A`] THEN
    ASM_SIMP_TAC[RING_ADD; RING_ADD_AC];
    EXISTS_TAC `ring_add r (ring_mul r a b)
                       (ring_add r (ring_mul r y a) (ring_mul r x b)):A` THEN
    EXISTS_TAC `ring_mul r x y:A` THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [RING_ADD_LDISTRIB; RING_ADD_RDISTRIB; RING_ADD; RING_MUL;
      RING_MUL_SYM; RING_ADD_AC]]);;

let SUBRING_SETADD_RIGHT = prove
 (`!r j s:A->bool.
        ring_ideal r j /\ s subring_of r
        ==> (ring_setadd r s j) subring_of r`,
  MESON_TAC[RING_SETADD_SYM; SUBRING_SETADD_LEFT;
            SUBRING_OF_IMP_SUBSET; RING_IDEAL_IMP_SUBSET]);;

let RING_IDEAL_QUOTIENT = prove
 (`!r i j:A->bool.
        ring_ideal r i /\ ring_ideal r j
        ==> ring_ideal r {x | x IN ring_carrier r /\
                              ring_setmul r {x} j SUBSET i}`,
  REWRITE_TAC[ring_ideal; SUBSET; ring_setmul; FORALL_IN_GSPEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_SING; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[RING_0; RING_MUL_LZERO] THEN
  ASM_SIMP_TAC[RING_MUL_LNEG; RING_NEG] THEN
  ASM_SIMP_TAC[RING_ADD; RING_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[RING_MUL; GSYM RING_MUL_ASSOC]);;

let RING_IDEAL_QUOTIENT_RMUL = prove
 (`!r j a:A.
        ring_ideal r j /\ a IN ring_carrier r
        ==> ring_ideal r {x | x IN ring_carrier r /\ ring_mul r x a IN j}`,
  REWRITE_TAC[ring_ideal; SUBSET; ring_setmul; FORALL_IN_GSPEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_SING; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[RING_0; RING_MUL_LZERO] THEN
  ASM_SIMP_TAC[RING_MUL_LNEG; RING_NEG] THEN
  ASM_SIMP_TAC[RING_ADD; RING_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[RING_MUL; GSYM RING_MUL_ASSOC]);;

let RING_IDEAL_QUOTIENT_LMUL = prove
 (`!r (a:A) j.
        a IN ring_carrier r /\ ring_ideal r j
        ==> ring_ideal r {x | x IN ring_carrier r /\ ring_mul r a x IN j}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_QUOTIENT_RMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[RING_MUL_SYM]);;

let RING_COMAXIMAL = prove
 (`!r j k. ring_ideal r j /\ ring_ideal r k
           ==> (ring_setadd r j k = ring_carrier r <=>
                ?a b. a IN j /\ b IN k /\ ring_add r a b = ring_1 r)`,
  SIMP_TAC[RING_IDEAL_EQ_CARRIER; RING_IDEAL_SETADD] THEN
  REWRITE_TAC[ring_setadd] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Ideal generated by a subset.                                              *)
(* ------------------------------------------------------------------------- *)

let ideal_generated = new_definition
 `ideal_generated r (s:A->bool) =
     INTERS {j | ring_ideal r j /\ (ring_carrier r INTER s) SUBSET j}`;;

let IDEAL_GENERATED_RESTRICT = prove
 (`!r s:A->bool.
        ideal_generated r s =
        ideal_generated r (ring_carrier r INTER s)`,
  REWRITE_TAC[ideal_generated; SET_RULE `g INTER g INTER s = g INTER s`]);;

let RING_IDEAL_IDEAL_GENERATED = prove
 (`!r s:A->bool. ring_ideal r (ideal_generated r s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ideal_generated] THEN
  MATCH_MP_TAC RING_IDEAL_INTERS THEN
  SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `ring_carrier r:A->bool` THEN
  REWRITE_TAC[RING_IDEAL_CARRIER; INTER_SUBSET]);;

let IDEAL_GENERATED_NONEMPTY = prove
 (`!r s:A->bool. ~(ideal_generated r s = {})`,
  MESON_TAC[RING_IDEAL_IDEAL_GENERATED; RING_IDEAL_IMP_NONEMPTY]);;

let IDEAL_GENERATED_MONO = prove
 (`!r s t:A->bool.
        s SUBSET t
        ==> ideal_generated r s SUBSET ideal_generated r t`,
  REWRITE_TAC[ideal_generated] THEN SET_TAC[]);;

let IDEAL_GENERATED_MINIMAL = prove
 (`!r h s:A->bool.
        s SUBSET h /\ ring_ideal r h ==> ideal_generated r s SUBSET h`,
  REWRITE_TAC[ideal_generated; INTERS_GSPEC] THEN SET_TAC[]);;

let IDEAL_GENERATED_INDUCT = prove
 (`!r P s:A->bool.
        (!x. x IN ring_carrier r /\ x IN s ==> P x) /\
        P(ring_0 r) /\
        (!x. P x ==> P(ring_neg r x)) /\
        (!x y. P x /\ P y ==> P(ring_add r x y)) /\
        (!x y. x IN ring_carrier r /\ P y ==> P(ring_mul r x y))
        ==> !x. x IN ideal_generated r s ==> P x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IN_INTER] THEN
  ONCE_REWRITE_TAC[IDEAL_GENERATED_RESTRICT] THEN MP_TAC(SET_RULE
    `ring_carrier r INTER (s:A->bool) SUBSET ring_carrier r`) THEN
  SPEC_TAC(`ring_carrier r INTER (s:A->bool)`,`s:A->bool`) THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `{x:A | x IN ring_carrier r /\ P x}`;
                 `s:A->bool`] IDEAL_GENERATED_MINIMAL) THEN
  ANTS_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[ring_ideal; IN_ELIM_THM; SUBSET; RING_ADD; RING_NEG;
               RING_0; RING_1; RING_MUL]);;

let IDEAL_GENERATED_INDUCT_STRONG = prove
 (`!r P s:A->bool.
        (!x. x IN ring_carrier r /\ x IN s ==> P x) /\
        P(ring_0 r) /\
        (!x. x IN ring_carrier r /\ P x ==> P(ring_neg r x)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_add r x y)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P y
               ==> P(ring_mul r x y))
        ==> !x. x IN ideal_generated r s ==> P x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN ideal_generated r s ==> (x:A) IN ring_carrier r /\ P x`
  MP_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC IDEAL_GENERATED_INDUCT THEN
  ASM_SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let IDEAL_GENERATED_SUBSET = prove
 (`!r h:A->bool.
         ideal_generated r h SUBSET ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ideal_generated] THEN
  MATCH_MP_TAC(SET_RULE `a IN s ==> INTERS s SUBSET a`) THEN
  REWRITE_TAC[IN_ELIM_THM; RING_IDEAL_CARRIER; INTER_SUBSET]);;

let FINITE_IDEAL_GENERATED = prove
 (`!r s:A->bool.
        FINITE(ring_carrier r)
        ==> FINITE(ideal_generated r s)`,
  MESON_TAC[FINITE_SUBSET; IDEAL_GENERATED_SUBSET]);;

let IDEAL_GENERATED_SUBSET_CARRIER = prove
 (`!r h:A->bool.
     ring_carrier r INTER h SUBSET (ideal_generated r h)`,
  REWRITE_TAC[ring_ideal; ideal_generated; SUBSET_INTERS] THEN SET_TAC[]);;

let IDEAL_GENERATED_MINIMAL_EQ = prove
 (`!r h s:A->bool.
        ring_ideal r h
        ==> (ideal_generated r s SUBSET h <=>
             ring_carrier r INTER s SUBSET h)`,
  MESON_TAC[IDEAL_GENERATED_SUBSET_CARRIER; SUBSET_TRANS;
            IDEAL_GENERATED_MINIMAL; IDEAL_GENERATED_RESTRICT]);;

let IDEALS_GENERATED_SUBSET = prove
 (`!r s t:A->bool.
        ideal_generated r s SUBSET ideal_generated r t <=>
        ring_carrier r INTER s SUBSET ideal_generated r t`,
  SIMP_TAC[IDEAL_GENERATED_MINIMAL_EQ; RING_IDEAL_IDEAL_GENERATED]);;

let IDEAL_GENERATED_RING_IDEAL = prove
 (`!r h:A->bool.
        ring_ideal r h ==> ideal_generated r h = h`,
  REWRITE_TAC[ring_ideal; ideal_generated; INTERS_GSPEC] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[SET_RULE `h SUBSET g ==> g INTER h = h`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL [GEN_REWRITE_TAC I [SUBSET]; ASM SET_TAC[]] THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `h:A->bool`) THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let IDEAL_GENERATED_RING_IDEAL_EQ = prove
 (`!r h:A->bool. ideal_generated r h = h <=> ring_ideal r h`,
  MESON_TAC[IDEAL_GENERATED_RING_IDEAL; RING_IDEAL_IDEAL_GENERATED]);;

let IDEAL_GENERATED_RING_CARRIER = prove
 (`!r:A ring. ideal_generated r (ring_carrier r) = ring_carrier r`,
  GEN_TAC THEN REWRITE_TAC[RINGS_EQ] THEN
  SIMP_TAC[IDEAL_GENERATED_RING_IDEAL; RING_IDEAL_CARRIER] THEN
  REWRITE_TAC[ideal_generated]);;

let IDEAL_GENERATED_SUBSET_CARRIER_SUBSET = prove
 (`!r s:A->bool. s SUBSET ring_carrier r ==> s SUBSET (ideal_generated r s)`,
  MESON_TAC[IDEAL_GENERATED_SUBSET_CARRIER;
            SET_RULE `s SUBSET t <=> t INTER s = s`]);;

let IDEAL_GENERATED_REFL = prove
 (`!r s:A->bool.
        ring_carrier r SUBSET s ==> ideal_generated r s = ring_carrier r`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[IDEAL_GENERATED_RESTRICT] THEN
  ASM_SIMP_TAC[SET_RULE `u SUBSET s ==> u INTER s = u`] THEN
  REWRITE_TAC[IDEAL_GENERATED_RING_CARRIER]);;

let IDEAL_GENERATED_INC = prove
 (`!r s x:A.
        s SUBSET ring_carrier r /\ x IN s
        ==> x IN ideal_generated r s`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; GSYM SUBSET] THEN
  REWRITE_TAC[IDEAL_GENERATED_SUBSET_CARRIER_SUBSET]);;

let IDEAL_GENERATED_INC_GEN = prove
 (`!r s x:A.
        x IN ring_carrier r /\ x IN s
        ==> x IN ideal_generated r s`,
  ONCE_REWRITE_TAC[IDEAL_GENERATED_RESTRICT] THEN
  SIMP_TAC[IDEAL_GENERATED_INC; INTER_SUBSET; IN_INTER]);;

let IDEAL_GENERATED_BY_IDEAL_GENERATED = prove
 (`!r s:A->bool.
        ideal_generated r (ideal_generated r s) =
        ideal_generated r s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RINGS_EQ] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; SUBSET_REFL];
    MATCH_MP_TAC IDEAL_GENERATED_SUBSET_CARRIER_SUBSET THEN
    REWRITE_TAC[IDEAL_GENERATED_SUBSET]]);;

let IDEAL_GENERATED_INSERT_ZERO = prove
 (`!r s:A->bool.
        ideal_generated r (ring_0 r INSERT s) = ideal_generated r s`,
  REWRITE_TAC[RINGS_EQ; ideal_generated] THEN
  REWRITE_TAC[EXTENSION; INTERS_GSPEC; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; TAUT
   `p /\ (q \/ r) ==> s <=> (q ==> p ==> s) /\ (p /\ r ==> s)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2; RING_0] THEN
  MESON_TAC[ring_ideal]);;

let IDEAL_GENERATED_0 = prove
 (`!r:A ring. ideal_generated r {ring_0 r} = {ring_0 r}`,
  REWRITE_TAC[IDEAL_GENERATED_RING_IDEAL_EQ; RING_IDEAL_0]);;

let IDEAL_GENERATED_EMPTY = prove
 (`!r:A ring. ideal_generated r {} = {ring_0 r}`,
  MESON_TAC[IDEAL_GENERATED_0; IDEAL_GENERATED_INSERT_ZERO]);;

let IDEAL_GENERATED_SING = prove
 (`!r a:A.
        a IN ring_carrier r
        ==> ideal_generated r {a} = {x | ring_divides r a x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_INDUCT THEN
    ASM_SIMP_TAC[IN_SING; RING_DIVIDES_REFL; RING_DIVIDES_0;
                 RING_DIVIDES_NEG; RING_DIVIDES_ADD; RING_DIVIDES_LMUL];
    REWRITE_TAC[ring_divides] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC THEN
    ASM_REWRITE_TAC[SING_SUBSET; IN_SING]]);;

let IDEAL_GENERATED_SING_ALT = prove
 (`!r a:A.
      a IN ring_carrier r
      ==> ideal_generated r {a} = {ring_mul r a x | x | x IN ring_carrier r}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[IDEAL_GENERATED_SING] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; ring_divides] THEN
  ASM_MESON_TAC[RING_MUL]);;

let IDEAL_GENERATED_SING_EQ_CARRIER = prove
 (`!r a:A.
        a IN ring_carrier r
        ==> (ideal_generated r {a} = ring_carrier r <=> ring_unit r a)`,
  SIMP_TAC[RING_IDEAL_EQ_CARRIER; RING_IDEAL_IDEAL_GENERATED] THEN
  SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM; RING_DIVIDES_ONE]);;

let SUBSET_IDEALS_GENERATED_SING = prove
 (`!r a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ideal_generated r {a} SUBSET ideal_generated r {b} <=>
             ring_divides r b a)`,
  SIMP_TAC[IDEALS_GENERATED_SUBSET] THEN
  SIMP_TAC[SET_RULE `x IN s ==> s INTER {x} = {x}`; SING_SUBSET] THEN
  SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM]);;

let IDEALS_GENERATED_SING_EQ = prove
 (`!r a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ideal_generated r {a} = ideal_generated r {b} <=>
             ring_associates r b a)`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; ring_associates] THEN
  SIMP_TAC[SUBSET_IDEALS_GENERATED_SING]);;

let PSUBSET_IDEALS_GENERATED_SING = prove
 (`!r a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ideal_generated r {a} PSUBSET ideal_generated r {b} <=>
             ring_divides r b a /\ ~(ring_divides r a b))`,
  REWRITE_TAC[SET_RULE `s PSUBSET t <=> s SUBSET t /\ ~(t SUBSET s)`] THEN
  SIMP_TAC[SUBSET_IDEALS_GENERATED_SING]);;

let IDEAL_GENERATED_EQ_0 = prove
 (`!r a:A. ideal_generated r {a} = {ring_0 r} <=>
           a IN ring_carrier r ==> a = ring_0 r`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THENL
   [ONCE_REWRITE_TAC[GSYM IDEAL_GENERATED_0] THEN
    ASM_SIMP_TAC[IDEALS_GENERATED_SING_EQ; RING_0; RING_ASSOCIATES_0];
    ONCE_REWRITE_TAC[IDEAL_GENERATED_RESTRICT] THEN
    ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> s INTER {a} = {}`] THEN
    REWRITE_TAC[IDEAL_GENERATED_EMPTY]]);;

let IDEAL_GENERATED_SING_SETMUL_RIGHT = prove
 (`!r a:A. a IN ring_carrier r
           ==> ideal_generated r {a} = ring_setmul r {a} (ring_carrier r)`,
  SIMP_TAC[IDEAL_GENERATED_SING_ALT; ring_setmul] THEN SET_TAC[]);;

let IDEAL_GENERATED_SING_SETMUL_LEFT = prove
 (`!r a:A. a IN ring_carrier r
           ==> ideal_generated r {a} = ring_setmul r (ring_carrier r) {a}`,
  MESON_TAC[IDEAL_GENERATED_SING_SETMUL_RIGHT; RING_SETMUL_SYM;
            SING_SUBSET; SUBSET_REFL]);;

let RING_SETMUL_IDEAL_GENERATED_SING = prove
 (`!r a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> ring_setmul r (ideal_generated r {a}) (ideal_generated r {b}) =
            ideal_generated r {ring_mul r a b}`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING_SETMUL_LEFT; RING_MUL] THEN
  TRANS_TAC EQ_TRANS
   `ring_setmul r (ring_setmul r (ring_carrier r) (ring_carrier r))
                  {ring_mul r a b}:A->bool` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_SETMUL_SING; RING_SETMUL_AC; SING_SUBSET;
                 SUBSET_REFL; RING_SETMUL];
    ASM_SIMP_TAC[RING_SETMUL_SUBRING; CARRIER_SUBRING_OF]]);;

let IDEAL_GENERATED_UNION = prove
 (`!r s t:A->bool.
        ideal_generated r (s UNION t) =
        ring_setadd r (ideal_generated r s) (ideal_generated r t)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [IDEAL_GENERATED_RESTRICT] THEN
    MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
    SIMP_TAC[RING_IDEAL_SETADD; RING_IDEAL_IDEAL_GENERATED] THEN
    REWRITE_TAC[UNION_OVER_INTER; UNION_SUBSET; ring_setadd] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `z:A` THEN DISCH_TAC THENL
     [MAP_EVERY EXISTS_TAC [`z:A`; `ring_0 r:A`];
      MAP_EVERY EXISTS_TAC [`ring_0 r:A`; `z:A`]] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; RING_ADD_RZERO; RING_ADD_LZERO;
                 IN_RING_IDEAL_0; RING_IDEAL_IDEAL_GENERATED];
    REWRITE_TAC[ring_setadd; SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC IN_RING_IDEAL_ADD THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `z IN u ==> u SUBSET v ==> z IN v`)) THEN
    MATCH_MP_TAC IDEAL_GENERATED_MONO THEN SET_TAC[]]);;

let IDEAL_GENERATED_INSERT = prove
 (`!r s a:A.
        ideal_generated r (a INSERT s) =
        ring_setadd r (ideal_generated r {a}) (ideal_generated r s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IDEAL_GENERATED_UNION] THEN
  AP_TERM_TAC THEN SET_TAC[]);;

let IDEAL_GENERATED_2 = prove
 (`!r a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> ideal_generated r {a,b} =
            { ring_add r (ring_mul r a x) (ring_mul r b y) | x,y |
              x IN ring_carrier r /\ y IN ring_carrier r}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[IDEAL_GENERATED_INSERT] THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING_ALT] THEN
  REWRITE_TAC[ring_setadd] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integral domain and field.                                                *)
(* ------------------------------------------------------------------------- *)

let integral_domain = new_definition
 `integral_domain (r:A ring) <=>
        ~(ring_1 r = ring_0 r) /\
        (!x y. x IN ring_carrier r /\
               y IN ring_carrier r /\
               ring_mul r x y = ring_0 r
               ==> x = ring_0 r \/ y = ring_0 r)`;;

let field = new_definition
 `field (r:A ring) <=>
        ~(ring_1 r = ring_0 r) /\
        !x. x IN ring_carrier r /\ ~(x = ring_0 r)
            ==> ?y. y IN ring_carrier r /\
                    ring_mul r x y = ring_1 r`;;

let INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING = prove
 (`!r:A ring. integral_domain r ==> ~(trivial_ring r)`,
  SIMP_TAC[integral_domain; TRIVIAL_RING_10]);;

let FIELD_IMP_NONTRIVIAL_RING = prove
 (`!r:A ring. field r ==> ~(trivial_ring r)`,
  SIMP_TAC[field; TRIVIAL_RING_10]);;

let INTEGRAL_DOMAIN_EQ_NO_ZERODIVISORS = prove
 (`!r:A ring.
        integral_domain r <=>
        ~(ring_1 r = ring_0 r) /\
        !x. ring_zerodivisor r x ==> x = ring_0 r`,
  REWRITE_TAC[integral_domain; ring_zerodivisor] THEN MESON_TAC[]);;

let INTEGRAL_DOMAIN_EQ_ALL_REGULAR = prove
 (`!r:A ring.
        integral_domain r <=>
        ~(ring_1 r = ring_0 r) /\
        !x. ring_regular r x <=> x IN ring_carrier r /\ ~(x = ring_0 r)`,
  REWRITE_TAC[ring_regular; INTEGRAL_DOMAIN_EQ_NO_ZERODIVISORS] THEN
  MESON_TAC[ring_zerodivisor; RING_ZERODIVISOR_0; TRIVIAL_RING_10]);;

let INTEGRAL_DOMAIN_ZERODIVISOR = prove
 (`!r a:A.
        integral_domain r
        ==> (ring_zerodivisor r a <=> a = ring_0 r)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[INTEGRAL_DOMAIN_EQ_NO_ZERODIVISORS];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ring_zerodivisor; RING_0] THEN
    ASM_MESON_TAC[integral_domain; RING_1; RING_MUL_LZERO]]);;

let INTEGRAL_DOMAIN_REGULAR = prove
 (`!r a:A. integral_domain r
           ==> (ring_regular r a <=> a IN ring_carrier r /\ ~(a = ring_0 r))`,
  SIMP_TAC[ring_regular; INTEGRAL_DOMAIN_ZERODIVISOR]);;

let INTEGRAL_DOMAIN_MUL_EQ_0 = prove
 (`!r a b:A.
        integral_domain r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_mul r a b = ring_0 r <=> a = ring_0 r \/ b = ring_0 r)`,
  REWRITE_TAC[integral_domain] THEN
  MESON_TAC[RING_MUL_LZERO; RING_MUL_RZERO]);;

let INTEGRAL_DOMAIN_POW_EQ_0 = prove
 (`!r (a:A) n.
        integral_domain r /\ a IN ring_carrier r
        ==> (ring_pow r a n = ring_0 r <=> a = ring_0 r /\ ~(n = 0))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; ring_pow; RING_POW; NOT_SUC] THEN
  ASM_MESON_TAC[integral_domain]);;

let INTEGRAL_DOMAIN_NILPOTENT = prove
 (`!r a:A. integral_domain r ==> (ring_nilpotent r a <=> a = ring_0 r)`,
  REWRITE_TAC[ring_nilpotent] THEN
  MESON_TAC[INTEGRAL_DOMAIN_POW_EQ_0; NOT_SUC; RING_0]);;

let INTEGRAL_DOMAIN_PRODUCT_EQ_0 = prove
 (`!r k (f:K->A).
        integral_domain r /\ FINITE k
        ==> (ring_product r k f = ring_0 r <=> ?i. i IN k /\ f i = ring_0 r)`,
  GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[RING_PRODUCT_CLAUSES; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[integral_domain]; ALL_TAC] THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; COND_SWAP] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; RING_PRODUCT] THEN
  ASM_MESON_TAC[RING_0]);;

let INTEGRAL_DOMAIN_MUL_LCANCEL = prove
 (`!r a x y:A.
        integral_domain r /\
        a IN ring_carrier r /\ ~(a = ring_0 r) /\
        x IN ring_carrier r /\ y IN ring_carrier r /\
        ring_mul r a x = ring_mul r a y
        ==> x = y`,
  REWRITE_TAC[integral_domain] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `ring_sub r x y:A`]) THEN
  ASM_SIMP_TAC[RING_SUB_LDISTRIB; RING_SUB; RING_SUB_EQ_0; RING_MUL]);;

let INTEGRAL_DOMAIN_MUL_LCANCEL_EQ = prove
 (`!r a x y:A.
        integral_domain r /\
        a IN ring_carrier r /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_mul r a x = ring_mul r a y <=>
             a = ring_0 r \/ x = y)`,
  MESON_TAC[RING_MUL_LZERO; INTEGRAL_DOMAIN_MUL_LCANCEL]);;

let INTEGRAL_DOMAIN_MUL_RCANCEL = prove
 (`!r a x y:A.
        integral_domain r /\
        a IN ring_carrier r /\ ~(a = ring_0 r) /\
        x IN ring_carrier r /\ y IN ring_carrier r /\
        ring_mul r x a = ring_mul r y a
        ==> x = y`,
  MESON_TAC[INTEGRAL_DOMAIN_MUL_LCANCEL; RING_MUL_SYM]);;

let INTEGRAL_DOMAIN_MUL_RCANCEL_EQ = prove
 (`!r a x y:A.
        integral_domain r /\
        a IN ring_carrier r /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_mul r x a = ring_mul r y a <=>
             x = y \/ a = ring_0 r)`,
  MESON_TAC[INTEGRAL_DOMAIN_MUL_LCANCEL_EQ; RING_MUL_SYM]);;

let INTEGRAL_DOMAIN_DIVIDES_LMUL2 = prove
 (`!r a b c:A.
        integral_domain r /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> (ring_divides r (ring_mul r a b) (ring_mul r a c) <=>
             a = ring_0 r \/ ring_divides r b c)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a:A = ring_0 r` THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_DIVIDES_REFL; RING_0] THEN
  EQ_TAC THEN ASM_SIMP_TAC[RING_DIVIDES_LMUL2] THEN
  ASM_SIMP_TAC[RING_MUL; ring_divides] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:A` THEN ASM_CASES_TAC `(d:A) IN ring_carrier r` THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; INTEGRAL_DOMAIN_MUL_LCANCEL_EQ;
               RING_MUL]);;

let INTEGRAL_DOMAIN_DIVIDES_RMUL2 = prove
 (`!r a b c:A.
        integral_domain r /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> (ring_divides r (ring_mul r a c) (ring_mul r b c) <=>
             ring_divides r a b \/ c = ring_0 r)`,
  MESON_TAC[INTEGRAL_DOMAIN_DIVIDES_LMUL2; RING_MUL_SYM]);;

let INTEGRAL_DOMAIN_ASSOCIATES_LMUL2 = prove
 (`!r a b c:A.
        integral_domain r /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> (ring_associates r (ring_mul r a b) (ring_mul r a c) <=>
             a = ring_0 r \/ ring_associates r b c)`,
  SIMP_TAC[ring_associates; INTEGRAL_DOMAIN_DIVIDES_LMUL2] THEN
  CONV_TAC TAUT);;

let INTEGRAL_DOMAIN_ASSOCIATES_RMUL2 = prove
 (`!r a b c:A.
        integral_domain r /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> (ring_associates r (ring_mul r a c) (ring_mul r b c) <=>
             ring_associates r a b \/ c = ring_0 r)`,
  SIMP_TAC[ring_associates; INTEGRAL_DOMAIN_DIVIDES_RMUL2] THEN
  CONV_TAC TAUT);;

let INTEGRAL_DOMAIN_MUL_EQ_SELF = prove
 (`(!r a b:A.
        integral_domain r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_mul r a b = b <=> a = ring_1 r \/ b = ring_0 r)) /\
   (!r a b:A.
        integral_domain r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_mul r a b = a <=> a = ring_0 r \/ b = ring_1 r))`,
  MESON_TAC[INTEGRAL_DOMAIN_MUL_RCANCEL_EQ; INTEGRAL_DOMAIN_MUL_LCANCEL_EQ;
                RING_1; RING_0; RING_MUL_LID; RING_MUL_RID]);;

let INTEGRAL_DOMAIN_DIVIDES_MUL_SELF = prove
 (`(!r a b:A.
        integral_domain r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_divides r (ring_mul r a b) b <=>
             ring_unit r a \/ b = ring_0 r)) /\
   (!r a b:A.
        integral_domain r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_divides r (ring_mul r a b) a <=>
             a = ring_0 r \/ ring_unit r b))`,
  REWRITE_TAC[GSYM RING_DIVIDES_ONE] THEN
  SIMP_TAC[GSYM INTEGRAL_DOMAIN_DIVIDES_LMUL2; RING_1; RING_MUL_RID;
           GSYM INTEGRAL_DOMAIN_DIVIDES_RMUL2; RING_MUL_LID]);;

let INTEGRAL_DOMAIN_DIVIDES_ASSOCIATES_MUL_SELF = prove
 (`(!r a b:A.
        integral_domain r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_associates r (ring_mul r a b) b <=>
             ring_unit r a \/ b = ring_0 r)) /\
   (!r a b:A.
        integral_domain r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_associates r (ring_mul r a b) a <=>
             a = ring_0 r \/ ring_unit r b)) /\
   (!r a b:A.
        integral_domain r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_associates r b (ring_mul r a b) <=>
             ring_unit r a \/ b = ring_0 r)) /\
   (!r a b:A.
        integral_domain r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_associates r a (ring_mul r a b) <=>
             a = ring_0 r \/ ring_unit r b))`,
  REWRITE_TAC[ring_associates] THEN
  SIMP_TAC[RING_DIVIDES_LMUL; RING_DIVIDES_RMUL; RING_DIVIDES_REFL] THEN
  SIMP_TAC[INTEGRAL_DOMAIN_DIVIDES_MUL_SELF]);;

let FIELD_EQ_ALL_UNITS = prove
 (`!r:A ring.
        field r <=>
        ~(ring_1 r = ring_0 r) /\
        !x. x IN ring_carrier r /\ ~(x = ring_0 r) ==> ring_unit r x`,
  REWRITE_TAC[field; ring_unit] THEN MESON_TAC[]);;

let FIELD_EQ_ALL_DIVIDE_1 = prove
 (`!r:A ring.
        field r <=>
        ~(ring_1 r = ring_0 r) /\
        !a. a IN ring_carrier r /\ ~(a = ring_0 r)
            ==> ring_divides r a (ring_1 r)`,
  REWRITE_TAC[field; ring_divides] THEN MESON_TAC[RING_1]);;

let FIELD_UNIT = prove
 (`!r a:A.
      field r ==> (ring_unit r a <=> a IN ring_carrier r /\ ~(a = ring_0 r))`,
  REWRITE_TAC[field; GSYM TRIVIAL_RING_10] THEN
  MESON_TAC[FIELD_EQ_ALL_UNITS; RING_UNIT_0; ring_unit]);;

let FIELD_MUL_LINV = prove
 (`!r a:A. field r /\ a IN ring_carrier r /\ ~(a = ring_0 r)
           ==> ring_mul r (ring_inv r a) a = ring_1 r`,
  SIMP_TAC[FIELD_UNIT; RING_MUL_LINV]);;

let FIELD_MUL_RINV = prove
 (`!r a:A. field r /\ a IN ring_carrier r /\ ~(a = ring_0 r)
           ==> ring_mul r a (ring_inv r a) = ring_1 r`,
  SIMP_TAC[FIELD_UNIT; RING_MUL_RINV]);;

let FIELD_DIVIDES = prove
 (`!r a b:A.
        field r
        ==> (ring_divides r a b <=>
             a IN ring_carrier r /\ b IN ring_carrier r /\
             (a = ring_0 r ==> b = ring_0 r))`,
  MESON_TAC[RING_UNIT_DIVIDES_ALL; FIELD_UNIT;
            RING_DIVIDES_ZERO; ring_divides]);;

let FIELD_ASSOCIATES = prove
 (`!r a b:A.
        field r
        ==> (ring_associates r a b <=>
             a IN ring_carrier r /\ b IN ring_carrier r /\
             (a = ring_0 r <=> b = ring_0 r))`,
  SIMP_TAC[ring_associates; FIELD_DIVIDES] THEN MESON_TAC[]);;

let FIELD_COPRIME = prove
 (`!r a b:A.
        field r
        ==> (ring_coprime r (a,b) <=>
             a IN ring_carrier r /\ b IN ring_carrier r /\
             ~(a = ring_0 r /\ b = ring_0 r))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ring_coprime; FIELD_DIVIDES; FIELD_UNIT] THEN
  MESON_TAC[RING_0]);;

let FIELD_IMP_INTEGRAL_DOMAIN = prove
 (`!r:A ring. field r ==> integral_domain r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[field; integral_domain] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN
  ASM_CASES_TAC `y:A = ring_0 r` THEN ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `y':A` THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `ring_mul r x (ring_mul r y y'):A` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[RING_MUL_RID]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_MUL; RING_MUL_LZERO]);;

let FIELD_ZERODIVISOR = prove
 (`!r a:A. field r ==> (ring_zerodivisor r a <=> a = ring_0 r)`,
  SIMP_TAC[INTEGRAL_DOMAIN_ZERODIVISOR; FIELD_IMP_INTEGRAL_DOMAIN]);;

let FIELD_REGULAR = prove
 (`!r a:A. field r
           ==> (ring_regular r a <=> a IN ring_carrier r /\ ~(a = ring_0 r))`,
  SIMP_TAC[ring_regular; FIELD_ZERODIVISOR]);;

let FIELD_NILPOTENT = prove
 (`!r a:A. field r ==> (ring_nilpotent r a <=> a = ring_0 r)`,
  SIMP_TAC[INTEGRAL_DOMAIN_NILPOTENT; FIELD_IMP_INTEGRAL_DOMAIN]);;

let FIELD_MUL_EQ_0 = prove
 (`!r a b:A.
        field r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_mul r a b = ring_0 r <=> a = ring_0 r \/ b = ring_0 r)`,
  SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN]);;

let FIELD_POW_EQ_0 = prove
 (`!r (a:A) n.
        field r /\ a IN ring_carrier r
        ==> (ring_pow r a n = ring_0 r <=> a = ring_0 r /\ ~(n = 0))`,
  SIMP_TAC[INTEGRAL_DOMAIN_POW_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN]);;

let FIELD_PRODUCT_EQ_0 = prove
 (`!r k (f:K->A).
        field r /\ FINITE k
        ==> (ring_product r k f = ring_0 r <=> ?i. i IN k /\ f i = ring_0 r)`,
  SIMP_TAC[INTEGRAL_DOMAIN_PRODUCT_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN]);;

let FINITE_INTEGRAL_DOMAIN_IMP_FIELD = prove
 (`!r:A ring. FINITE(ring_carrier r) /\ integral_domain r ==> field r`,
  GEN_TAC THEN REWRITE_TAC[integral_domain; field] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`ring_carrier r:A->bool`;
    `\x:A. ring_mul r a x`] SURJECTIVE_IFF_INJECTIVE) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; RING_MUL] THEN
  DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[RING_1]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
  EXISTS_TAC `r:A ring` THEN ASM_REWRITE_TAC[integral_domain] THEN
  ASM_MESON_TAC[]);;

let FINITE_INTEGRAL_DOMAIN_EQ_FIELD = prove
 (`!r:A ring.
        FINITE(ring_carrier r) ==> (integral_domain r <=> field r)`,
  MESON_TAC[FINITE_INTEGRAL_DOMAIN_IMP_FIELD; FIELD_IMP_INTEGRAL_DOMAIN]);;

let INTEGRAL_DOMAIN_CHAR = prove
 (`!r:A ring.
        integral_domain r ==> ring_char r = 0 \/ prime(ring_char r)`,
  REWRITE_TAC[integral_domain; GSYM TRIVIAL_RING_10] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[prime; RING_CHAR_EQ_1] THEN
  ASM_CASES_TAC `ring_char(r:A ring) = 0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ring_of_num r m:A`; `ring_of_num r n:A`]) THEN
  ASM_REWRITE_TAC[RING_OF_NUM; GSYM RING_OF_NUM_MUL] THEN
  REWRITE_TAC[RING_OF_NUM_EQ_0; NUMBER_RULE `!n:num. n divides n`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  ASM_REWRITE_TAC[divides; GSYM MULT_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `n:num = m * n * d <=> n = n * m * d`] THEN
  REWRITE_TAC[ARITH_RULE `m = m * n <=> m * n = m * 1`] THEN
  ASM_REWRITE_TAC[EQ_MULT_LCANCEL; MULT_EQ_1] THEN MESON_TAC[]);;

let RING_CHAR_DIVIDES_MUL = prove
 (`!(r:A ring) m n.
        integral_domain r \/ field r
        ==> (ring_char r divides m * n <=>
             ring_char r divides m \/ ring_char r divides n)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (p ==> r) ==> (p \/ q ==> r)`) THEN
  REWRITE_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP INTEGRAL_DOMAIN_CHAR) THEN
  ASM_MESON_TAC[ZERO_ONE_OR_PRIME_DIVPROD]);;

let RING_CHAR_DIVIDES_PRIME = prove
 (`!(r:A ring) p.
        (integral_domain r \/ field r) /\ prime p
        ==> (ring_char r divides p <=> ring_char r = p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (p ==> r) ==> (p \/ q ==> r)`) THEN
  REWRITE_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP INTEGRAL_DOMAIN_CHAR) THEN
  ASM_MESON_TAC[prime; NUMBER_RULE `(n:num) divides n`;
                NUMBER_RULE `0 divides n <=> n = 0`]);;

let FINITE_INTEGRAL_DOMAIN_CHAR = prove
 (`!r:A ring.
        integral_domain r /\ FINITE(ring_carrier r) ==> prime(ring_char r)`,
  MESON_TAC[RING_CHAR_FINITE; INTEGRAL_DOMAIN_CHAR]);;

let INTEGRAL_DOMAIN_SUBRING_GENERATED = prove
 (`!r s:A->bool.
        integral_domain r ==> integral_domain (subring_generated r s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integral_domain; GSYM TRIVIAL_RING_10] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[TRIVIAL_RING_SUBRING_GENERATED] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
        RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN
  ASM SET_TAC[]);;

let INTEGRAL_DOMAIN_ASSOCIATES = prove
 (`!r a b:A.
        integral_domain r
        ==> (ring_associates r a b <=>
             a IN ring_carrier r /\ b IN ring_carrier r /\
             ?u. ring_unit r u /\ ring_mul r a u = b)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a:A = ring_0 r` THENL
   [ASM_REWRITE_TAC[RING_0; RING_ASSOCIATES_0] THEN
    ASM_MESON_TAC[RING_MUL_LZERO; RING_UNIT_1; RING_0; ring_unit];
    ALL_TAC] THEN
  REWRITE_TAC[ring_associates; ring_divides] THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(b:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; ring_unit] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:A` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:A` THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`r:A ring`; `a:A`] THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC; RING_1; RING_MUL; RING_MUL_RID];
    UNDISCH_THEN `ring_mul r a u:A = b` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_MUL_RID]]);;

let INTEGRAL_DOMAIN_10 = prove
 (`!r:A ring.
        ring_carrier r = {ring_0 r,ring_1 r}
        ==> (integral_domain r <=> ~(ring_1 r = ring_0 r))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[integral_domain; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[RING_1; RING_MUL_LID]);;

let FIELD_10 = prove
 (`!r:A ring.
        ring_carrier r = {ring_0 r,ring_1 r}
        ==> (field r <=> ~(ring_1 r = ring_0 r))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[field; IMP_CONJ] THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[RING_1; RING_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Rule and tactic methods of proving carrier membership by backchaining.    *)
(* The tactic also tries expanding ABBREV_TAC-style definitions and using    *)
(* existing assumptions.                                                     *)
(* ------------------------------------------------------------------------- *)

let RING_CARRIER_RULE =
  let rule_0 = PART_MATCH I RING_0
  and rule_1 = PART_MATCH I RING_1
  and rule_n = PART_MATCH I RING_OF_NUM
  and rule_z = PART_MATCH I RING_OF_INT
  and rule_neg = PART_MATCH rand RING_NEG
  and rule_inv = PART_MATCH rand RING_INV
  and rule_pow = PART_MATCH rand RING_POW
  and rule_add = PART_MATCH rand RING_ADD
  and rule_sub = PART_MATCH rand RING_SUB
  and rule_mul = PART_MATCH rand RING_MUL
  and rule_div = PART_MATCH rand RING_DIV in
  fun asm ->
    let rule_nullary tm =
      try find (fun a -> concl a = tm) asm
      with Failure _ -> try
          rule_0 tm
      with Failure _ -> try
          rule_1 tm
      with Failure _ -> try
          rule_n tm
      with Failure _ ->
          rule_z tm
    and rule_unary tm =
      try rule_neg tm
      with Failure _ -> try
          rule_inv tm
      with Failure _ ->
          rule_pow tm
    and rule_binary tm =
      try rule_add tm
      with Failure _ -> try
          rule_sub tm
      with Failure _ -> try
          rule_mul tm
      with Failure _ ->
          rule_div tm in
    let rec rule tm =
     try rule_nullary tm
     with Failure _ -> try
         let th = rule_unary tm in
         MP th (rule(lhand(concl th)))
     with Failure _ -> try
         let th = rule_binary tm in
         MP th (CONJ (rule(lhand(lhand(concl th))))
                     (rule(rand(lhand(concl th)))))
     with Failure _ ->
         ASSUME tm in
    fun tm ->
      match tm with
        Comb(Comb(Const("IN",_),t),Comb(Const("ring_carrier",_),r)) -> rule tm
    | _ -> failwith "RING_CARRIER_RULE";;

let RING_CARRIER_TAC =
  let tac_0 = MATCH_ACCEPT_TAC RING_0
  and tac_1 = MATCH_ACCEPT_TAC RING_1
  and tac_n = MATCH_ACCEPT_TAC RING_OF_NUM
  and tac_z = MATCH_ACCEPT_TAC RING_OF_INT
  and tac_neg = MATCH_MP_TAC RING_NEG
  and tac_inv = MATCH_MP_TAC RING_INV
  and tac_pow = MATCH_MP_TAC RING_POW
  and tac_add = MATCH_MP_TAC RING_ADD
  and tac_sub = MATCH_MP_TAC RING_SUB
  and tac_mul = MATCH_MP_TAC RING_MUL
  and tac_div = MATCH_MP_TAC RING_DIV in
  let tac_nullary = tac_0 ORELSE tac_1 ORELSE tac_n ORELSE tac_z
  and tac_unary = tac_neg ORELSE tac_inv ORELSE tac_pow
  and tac_binary = tac_add ORELSE tac_sub ORELSE tac_mul ORELSE tac_div in
  let base_tac =
    FIRST_ASSUM ACCEPT_TAC ORELSE
    tac_nullary ORELSE tac_unary ORELSE (tac_binary THEN CONJ_TAC)
  and checker =
   can (term_match [] `(x:A) IN ring_carrier r`) in
  W(fun (asl,w) -> if checker w then ALL_TAC else NO_TAC) THEN
  REPEAT(base_tac ORELSE
         (FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
          base_tac));;

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer and ring procedure for the case of a ring      *)
(* "r:A ring" with the whole type A as the carrier. Since all the machinery  *)
(* of the normalizer is designed for such "universal" rings, this is the     *)
(* best we can do, but below we use this to define a general procedure.      *)
(* The RING instantiation is called RING_INTEGRAL_DOMAIN_UNIVERSAL since     *)
(* it in general assumes "integral_domain r" and may also assume that        *)
(* "ring_char r = 0". Later we use the other cofactors function to give      *)
(* a better decision procedure for general rings, but the integral           *)
(* domain one may be independently useful for proofs involving cancellation  *)
(* in such domains.                                                          *)
(* ------------------------------------------------------------------------- *)

let RING_POLY_UNIVERSAL_CONV =
  let pth = (UNDISCH o SPEC_ALL o prove)
   (`!r. ring_carrier r = (:A)
          ==> (!x y z. ring_add r x (ring_add r y z) =
                       ring_add r (ring_add r x y) z) /\
              (!x y. ring_add r x y = ring_add r y x) /\
              (!x. ring_add r (ring_of_int r (&0)) x = x) /\
              (!x y z. ring_mul r x (ring_mul r y z) =
                       ring_mul r (ring_mul r x y) z) /\
              (!x y. ring_mul r x y = ring_mul r y x) /\
              (!x. ring_mul r (ring_of_int r (&1)) x = x) /\
              (!x. ring_mul r (ring_of_int r (&0)) x = ring_of_int r (&0)) /\
              (!x y z. ring_mul r x (ring_add r y z) =
                       ring_add r (ring_mul r x y) (ring_mul r x z)) /\
              (!x. ring_pow r x 0 = ring_of_int r (&1)) /\
              (!x n. ring_pow r x (SUC n) = ring_mul r x (ring_pow r x n))`,
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_1; CONJUNCT1 ring_of_num] THEN
    SIMP_TAC[RING_ADD_LZERO; RING_MUL_LID; RING_MUL_LZERO; IN_UNIV] THEN
    SIMP_TAC[ring_pow; RING_ADD_LDISTRIB; IN_UNIV] THEN
    SIMP_TAC[RING_ADD_AC; RING_MUL_AC; IN_UNIV])
  and sth = (UNDISCH o SPEC_ALL o prove)
   (`!r. ring_carrier r = (:A)
          ==> (!x. ring_neg r x = ring_mul r (ring_of_int r (-- &1)) x) /\
              (!x y. ring_sub r x y =
                     ring_add r x (ring_mul r (ring_of_int r (-- &1)) y))`,
    SIMP_TAC[RING_OF_INT_NEG; RING_MUL_LNEG; IN_UNIV; ring_sub] THEN
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_1; CONJUNCT1 ring_of_num] THEN
    SIMP_TAC[ring_sub; RING_MUL_LNEG; RING_MUL_LID; IN_UNIV])
  and RING_INT_ADD_CONV =
      GEN_REWRITE_CONV I [GSYM RING_OF_INT_ADD] THENC
      RAND_CONV INT_ADD_CONV
  and RING_INT_MUL_CONV =
    GEN_REWRITE_CONV I [GSYM RING_OF_INT_MUL] THENC
    RAND_CONV INT_MUL_CONV
  and RING_INT_POW_CONV =
    GEN_REWRITE_CONV I [GSYM RING_OF_INT_POW] THENC
    RAND_CONV INT_POW_CONV
  and is_ringconst tm =
    match tm with
      Comb(Comb(Const("ring_of_int",_),_),n) -> is_intconst n
    | _ -> false
  and ith = prove
   (`ring_0 r = ring_of_int r (&0) /\
     ring_1 r = ring_of_int r (&1)`,
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_1; CONJUNCT1 ring_of_num]) in
  let _,_,_,_,_,RING_POLY_CONV =
    SEMIRING_NORMALIZERS_CONV pth sth
     (is_ringconst,
      RING_INT_ADD_CONV,RING_INT_MUL_CONV,RING_INT_POW_CONV)
     (<) in
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [ith; GSYM RING_OF_INT_OF_NUM] THENC
  RING_POLY_CONV;;

let RING_INTEGRAL_DOMAIN_UNIVERSAL,ring_ring_cofactors_universal =
  let RING_INTEGRAL = (repeat UNDISCH o prove)
   (`integral_domain r
     ==> ring_carrier r = (:A)
         ==> (!x. ring_mul r (ring_of_int r (&0)) x = ring_of_int r (&0)) /\
             (!x y z. ring_add r x y = ring_add r x z <=> y = z) /\
             (!w x y z.
                      ring_add r (ring_mul r w y) (ring_mul r x z) =
                      ring_add r (ring_mul r w z) (ring_mul r x y) <=>
                      w = x \/ y = z)`,
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_0] THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_ADD_LCANCEL; IN_UNIV] THEN
    REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `r:A ring` RING_SUB_EQ_0) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          INTEGRAL_DOMAIN_MUL_EQ_0)) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[ring_sub; IN_UNIV; RING_ADD_LDISTRIB; RING_ADD_RDISTRIB;
                 RING_NEG_NEG; RING_NEG_ADD; RING_MUL_LNEG; RING_MUL_RNEG] THEN
    ASM_SIMP_TAC[RING_MUL_AC; IN_UNIV] THEN
    ASM_SIMP_TAC[RING_ADD_AC; IN_UNIV])
  and neth_b = prove
   (`ring_of_int r n :A = ring_of_int r n <=> T`,
    REWRITE_TAC[])
  and neth_l = (UNDISCH o prove)
   (`integral_domain (r:A ring)
     ==> (ring_of_int r (&1) = ring_of_int r (&0) <=> F)`,
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_0; RING_OF_NUM_1] THEN
    SIMP_TAC[integral_domain])
  and neth_r = (UNDISCH o prove)
   (`integral_domain (r:A ring)
     ==> (ring_of_int r (&0) = ring_of_int r (&1) <=> F)`,
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_0; RING_OF_NUM_1] THEN
    SIMP_TAC[integral_domain])
  and neth_g = prove
   (`(ring_of_int r m :A = ring_of_int r n <=> F) <=>
     ~(&(ring_char r) divides (m - n))`,
    REWRITE_TAC[RING_OF_INT_EQ] THEN CONV_TAC INTEGER_RULE)
  and neth_h = prove
   (`(&(ring_char(r:A ring)) divides --(&n) <=> ring_char r divides n) /\
     (&(ring_char(r:A ring)) divides &n <=> ring_char r divides n)`,
    REWRITE_TAC[num_divides] THEN CONV_TAC INTEGER_RULE) in
  let rule1 = PART_MATCH (lhand o lhand) neth_g
  and conv1 =
    RAND_CONV INT_SUB_CONV THENC
    GEN_REWRITE_CONV TRY_CONV [neth_h] in
  let RING_EQ_CONV tm =
    try PART_MATCH lhand neth_b tm
    with Failure _ -> try
        PART_MATCH lhand neth_l tm
    with Failure _ -> try
        PART_MATCH lhand neth_r tm
    with Failure _ -> try
        let th1 = rule1 tm in
        let th2 = CONV_RULE(RAND_CONV(RAND_CONV conv1)) th1 in
        UNDISCH(snd(EQ_IMP_RULE th2))
    with Failure _ -> failwith "RING_EQ_CONV"
  and dest_ringconst tm =
    match tm with
      Comb(Comb(Const("ring_of_int",_),_),n) -> dest_intconst n
    | _ -> failwith "dest_ringconst"
  and mk_ringconst =
    let ptm = `ring_of_int (r:A ring)` in
    fun n -> mk_comb(ptm,mk_intconst n) in
  let cth = prove
   (`ring_0 r:A = ring_of_int r (&0) /\
     ring_1 r:A = ring_of_int r (&1)`,
    REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_0; RING_OF_NUM_1]) in
  let decorule =
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [cth; GSYM RING_OF_INT_OF_NUM] in
  let basic_rule,idealconv =
    RING_AND_IDEAL_CONV
     (dest_ringconst,
      mk_ringconst,
      RING_EQ_CONV,
      `ring_neg(r:A ring)`,
      `ring_add(r:A ring)`,
      `ring_sub(r:A ring)`,
      `ring_inv(r:A ring)`,
      `ring_mul(r:A ring)`,
      `ring_div(r:A ring)`,
      `ring_pow(r:A ring)`,
      RING_INTEGRAL,TRUTH,RING_POLY_UNIVERSAL_CONV) in
  let rule tm =
    let th = decorule tm in
    EQ_MP (SYM th) (basic_rule(rand(concl th))) in
  rule,idealconv;;

(* ------------------------------------------------------------------------- *)
(* Homomorphisms etc.                                                        *)
(* ------------------------------------------------------------------------- *)

let ring_homomorphism = new_definition
 `ring_homomorphism (r,r') (f:A->B) <=>
        IMAGE f (ring_carrier r) SUBSET ring_carrier r' /\
        f (ring_0 r) = ring_0 r' /\
        f (ring_1 r) = ring_1 r' /\
        (!x. x IN ring_carrier r
             ==> f(ring_neg r x) = ring_neg r' (f x)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r
               ==> f(ring_add r x y) = ring_add r' (f x) (f y)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r
               ==> f(ring_mul r x y) = ring_mul r' (f x) (f y))`;;

let ring_monomorphism = new_definition
 `ring_monomorphism (r,r') (f:A->B) <=>
        ring_homomorphism (r,r') f /\
        !x y. x IN ring_carrier r /\ y IN ring_carrier r /\ f x = f y
             ==> x = y`;;

let ring_epimorphism = new_definition
 `ring_epimorphism (r,r') (f:A->B) <=>
        ring_homomorphism (r,r') f /\
        IMAGE f (ring_carrier r) = ring_carrier r'`;;

let ring_endomorphism = new_definition
 `ring_endomorphism r (f:A->A) <=> ring_homomorphism (r,r) f`;;

let ring_isomorphisms = new_definition
 `ring_isomorphisms (r,r') ((f:A->B),g) <=>
        ring_homomorphism (r,r') f /\
        ring_homomorphism (r',r) g /\
        (!x. x IN ring_carrier r ==> g(f x) = x) /\
        (!y. y IN ring_carrier r' ==> f(g y) = y)`;;

let ring_isomorphism = new_definition
 `ring_isomorphism (r,r') (f:A->B) <=> ?g. ring_isomorphisms (r,r') (f,g)`;;

let ring_automorphism = new_definition
 `ring_automorphism r (f:A->A) <=> ring_isomorphism (r,r) f`;;

let RING_HOMOMORPHISM_EQ = prove
 (`!r r' (f:A->B) f'.
        ring_homomorphism(r,r') f /\
        (!x. x IN ring_carrier r ==> f' x = f x)
        ==> ring_homomorphism (r,r') f'`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let RING_MONOMORPHISM_EQ = prove
 (`!r r' (f:A->B) f'.
        ring_monomorphism(r,r') f /\
        (!x. x IN ring_carrier r ==> f' x = f x)
        ==> ring_monomorphism (r,r') f'`,
  REWRITE_TAC[ring_monomorphism; ring_homomorphism; SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
  MESON_TAC[]);;

let RING_EPIMORPHISM_EQ = prove
 (`!r r' (f:A->B) f'.
        ring_epimorphism(r,r') f /\
        (!x. x IN ring_carrier r ==> f' x = f x)
        ==> ring_epimorphism (r,r') f'`,
  REWRITE_TAC[ring_epimorphism; ring_homomorphism; SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN SET_TAC[]);;

let RING_ENDOMORPHISM_EQ = prove
 (`!r (f:A->A) f'.
        ring_endomorphism r f /\
        (!x. x IN ring_carrier r ==> f' x = f x)
        ==> ring_endomorphism r f'`,
  REWRITE_TAC[ring_endomorphism; RING_HOMOMORPHISM_EQ]);;

let RING_ISOMORPHISMS_EQ = prove
 (`!r r' (f:A->B) g.
        ring_isomorphisms(r,r') (f,g) /\
        (!x. x IN ring_carrier r ==> f' x = f x) /\
        (!y. y IN ring_carrier r' ==> g' y = g y)
        ==> ring_isomorphisms(r,r') (f',g')`,
  SIMP_TAC[ring_isomorphisms; ring_homomorphism; SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN SET_TAC[]);;

let RING_ISOMORPHISM_EQ = prove
 (`!r r' (f:A->B) f'.
        ring_isomorphism(r,r') f /\
        (!x. x IN ring_carrier r ==> f' x = f x)
        ==> ring_isomorphism (r,r') f'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ring_isomorphism] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[RING_ISOMORPHISMS_EQ]);;

let RING_AUTOMORPHISM_EQ = prove
 (`!r (f:A->A) f'.
        ring_automorphism r f /\
        (!x. x IN ring_carrier r ==> f' x = f x)
        ==> ring_automorphism r f'`,
  REWRITE_TAC[ring_automorphism; RING_ISOMORPHISM_EQ]);;

let RING_ISOMORPHISMS_SYM = prove
 (`!r r' (f:A->B) g.
        ring_isomorphisms (r,r') (f,g) <=> ring_isomorphisms(r',r) (g,f)`,
  REWRITE_TAC[ring_isomorphisms] THEN MESON_TAC[]);;

let RING_ISOMORPHISMS_IMP_ISOMORPHISM = prove
 (`!(f:A->B) g r r'.
        ring_isomorphisms (r,r') (f,g) ==> ring_isomorphism (r,r') f`,
  REWRITE_TAC[ring_isomorphism] THEN MESON_TAC[]);;

let RING_ISOMORPHISMS_IMP_ISOMORPHISM_ALT = prove
 (`!(f:A->B) g r r'.
        ring_isomorphisms (r,r') (f,g) ==> ring_isomorphism (r',r) g`,
  MESON_TAC[RING_ISOMORPHISMS_SYM; RING_ISOMORPHISMS_IMP_ISOMORPHISM]);;

let RING_HOMOMORPHISM = prove
 (`!r r' f:A->B.
        ring_homomorphism (r,r') (f:A->B) <=>
        IMAGE f (ring_carrier r) SUBSET ring_carrier r' /\
        f(ring_1 r) = ring_1 r' /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r
               ==> f(ring_add r x y) = ring_add r' (f x) (f y)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r
               ==> f(ring_mul r x y) = ring_mul r' (f x) (f y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_homomorphism] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`ring_0 r:A`; `ring_0 r:A`])) THEN
    SIMP_TAC[RING_0; RING_ADD_LZERO] THEN
    ASM_MESON_TAC[RING_LZERO_UNIQUE; RING_0];
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_LNEG_UNIQUE THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `ring_neg r x:A`])) THEN
    ASM_SIMP_TAC[RING_NEG; RING_ADD_RNEG]]);;

let RING_ISOMORPHISMS = prove
 (`!r r' (f:A->B) g.
        ring_isomorphisms(r,r') (f,g) <=>
        ring_homomorphism(r,r') f /\
        (!x. x IN ring_carrier r ==> g(f x) = x) /\
        (!y. y IN ring_carrier r' ==> g y IN ring_carrier r /\ f(g y) = y)`,
  REWRITE_TAC[ring_isomorphisms; ring_homomorphism] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let RING_HOMOMORPHISM_0 = prove
 (`!r r' (f:A->B). ring_homomorphism(r,r') f ==> f(ring_0 r) = ring_0 r'`,
  SIMP_TAC[ring_homomorphism]);;

let RING_HOMOMORPHISM_1 = prove
 (`!r r' (f:A->B). ring_homomorphism(r,r') f ==> f(ring_1 r) = ring_1 r'`,
  SIMP_TAC[ring_homomorphism]);;

let RING_HOMOMORPHISM_NEG = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> !x. x IN ring_carrier r
                ==> f(ring_neg r x) = ring_neg r' (f x)`,
  SIMP_TAC[ring_homomorphism]);;

let RING_HOMOMORPHISM_ADD = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r
                  ==> f(ring_add r x y) = ring_add r' (f x) (f y)`,
  SIMP_TAC[ring_homomorphism]);;

let RING_HOMOMORPHISM_MUL = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r
                  ==> f(ring_mul r x y) = ring_mul r' (f x) (f y)`,
  SIMP_TAC[ring_homomorphism]);;

let RING_HOMOMORPHISM_SUB = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r
                  ==> f(ring_sub r x y) = ring_sub r' (f x) (f y)`,
  REWRITE_TAC[ring_homomorphism; ring_sub] THEN
  MESON_TAC[RING_ADD; RING_NEG]);;

let RING_HOMOMORPHISM_POW = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> !x n. x IN ring_carrier r
                  ==> f(ring_pow r x n) = ring_pow r' (f x) n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_homomorphism] THEN DISCH_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ring_pow; RING_POW]);;

let RING_HOMOMORPHISM_RING_OF_NUM = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> !n. f(ring_of_num r n) = ring_of_num r' n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[ring_of_num] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC
   [MATCH_MP RING_HOMOMORPHISM_ADD th; RING_OF_NUM; RING_1]) THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_1]);;

let RING_HOMOMORPHISM_RING_OF_INT = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> !n. f(ring_of_int r n) = ring_of_int r' n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[FORALL_INT_CASES; RING_OF_INT_CLAUSES] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC
   [RING_NEG; RING_OF_NUM; MATCH_MP RING_HOMOMORPHISM_NEG th]) THEN
  FIRST_ASSUM(fun th ->
   ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th]));;

let RING_HOMOMORPHISM_SUM = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> !(h:K->A) k.
                FINITE k /\ (!i. i IN k ==> h i IN ring_carrier r)
                ==> f(ring_sum r k h) = ring_sum r' k (f o h)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; FINITE_INSERT] THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES; o_THM; RING_SUM]);;

let RING_HOMOMORPHISM_PRODUCT = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> !(h:K->A) k.
                FINITE k /\ (!i. i IN k ==> h i IN ring_carrier r)
                ==> f(ring_product r k h) = ring_product r' k (f o h)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; FINITE_INSERT] THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; o_THM; RING_PRODUCT]);;

let RING_MONOMORPHISM_SUM = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f
        ==> !(h:K->A) k.
                (!i. i IN k ==> h i IN ring_carrier r)
                ==> f(ring_sum r k h) = ring_sum r' k (f o h)`,
  REWRITE_TAC[ring_monomorphism; INJECTIVE_ON_ALT] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM RING_SUM_SUPPORT] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_HOMOMORPHISM_0) THEN
  ASM_SIMP_TAC[o_THM; RING_0; TAUT `p /\ ~q <=> ~(p ==> q)`] THEN
  REWRITE_TAC[NOT_IMP] THEN
  ASM_CASES_TAC `FINITE {a | a IN k /\ ~((h:K->A) a = ring_0 r)}` THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_SUM; IN_ELIM_THM] THEN
  MATCH_MP_TAC(MESON[RING_HOMOMORPHISM_0]
   `ring_homomorphism(r,r') f /\ x = ring_0 r /\ y = ring_0 r'
    ==> f x = y`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RING_SUM_TRIVIAL THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INFINITE]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN
  MP_TAC(ISPEC `r:A ring` RING_0) THEN ASM SET_TAC[]);;

let RING_MONOMORPHISM_PRODUCT = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f
        ==> !(h:K->A) k.
                (!i. i IN k ==> h i IN ring_carrier r)
                ==> f(ring_product r k h) = ring_product r' k (f o h)`,
  REWRITE_TAC[ring_monomorphism; INJECTIVE_ON_ALT] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM RING_PRODUCT_SUPPORT] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_HOMOMORPHISM_1) THEN
  ASM_SIMP_TAC[o_THM; RING_1; TAUT `p /\ ~q <=> ~(p ==> q)`] THEN
  REWRITE_TAC[NOT_IMP] THEN
  ASM_CASES_TAC `FINITE {a | a IN k /\ ~((h:K->A) a = ring_1 r)}` THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_PRODUCT; IN_ELIM_THM] THEN
  MATCH_MP_TAC(MESON[RING_HOMOMORPHISM_1]
   `ring_homomorphism(r,r') f /\ x = ring_1 r /\ y = ring_1 r'
    ==> f x = y`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RING_PRODUCT_TRIVIAL THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INFINITE]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN
  MP_TAC(ISPEC `r:A ring` RING_1) THEN ASM SET_TAC[]);;

let RING_MONOMORPHISM_SUM_GEN = prove
 (`!r r' (f:A->B) (h:K->A) k.
        ring_monomorphism(r,r') f
        ==> f(ring_sum r k h) =
            ring_sum r' {i | i IN k /\ h i IN ring_carrier r} (f o h)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM RING_SUM_RESTRICT] THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_SUM; IN_ELIM_THM]);;

let RING_MONOMORPHISM_PRODUCT_GEN = prove
 (`!r r' (f:A->B) (h:K->A) k.
        ring_monomorphism(r,r') f
        ==> f(ring_product r k h) =
            ring_product r' {i | i IN k /\ h i IN ring_carrier r} (f o h)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM RING_PRODUCT_RESTRICT] THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_PRODUCT; IN_ELIM_THM]);;

let RING_MONOMORPHISM_IMP_HOMOMORPHISM = prove
 (`!(f:A->B) r r'. ring_monomorphism(r,r') f ==> ring_homomorphism(r,r') f`,
  SIMP_TAC[ring_monomorphism]);;

let RING_EPIMORPHISM_IMP_HOMOMORPHISM = prove
 (`!(f:A->B) r r'. ring_epimorphism(r,r') f ==> ring_homomorphism(r,r') f`,
  SIMP_TAC[ring_epimorphism]);;

let RING_MONOMORPHISM_INJECTIVE_EQ = prove
 (`!r r' (f:A->B) x y.
        ring_monomorphism(r,r') f /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (f x = f y <=> x = y)`,
  REWRITE_TAC[ring_monomorphism] THEN MESON_TAC[]);;

let RING_MONOMORPHISM_EQ_0 = prove
 (`!r r' (f:A->B) x.
        ring_monomorphism(r,r') f /\
        x IN ring_carrier r
        ==> (f x = ring_0 r' <=> x = ring_0 r)`,
  MESON_TAC[RING_MONOMORPHISM_INJECTIVE_EQ; RING_HOMOMORPHISM_0; RING_0;
            RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let RING_HOMOMORPHISM_ID = prove
 (`!r:A ring. ring_homomorphism (r,r) (\x. x)`,
  REWRITE_TAC[ring_homomorphism; IMAGE_ID; SUBSET_REFL]);;

let RING_MONOMORPHISM_ID = prove
 (`!r:A ring. ring_monomorphism (r,r) (\x. x)`,
  SIMP_TAC[ring_monomorphism; RING_HOMOMORPHISM_ID]);;

let RING_EPIMORPHISM_ID = prove
 (`!r:A ring. ring_epimorphism (r,r) (\x. x)`,
  SIMP_TAC[ring_epimorphism; RING_HOMOMORPHISM_ID; IMAGE_ID]);;

let RING_ISOMORPHISMS_ID = prove
 (`!r:A ring. ring_isomorphisms (r,r) ((\x. x),(\x. x))`,
  REWRITE_TAC[ring_isomorphisms; RING_HOMOMORPHISM_ID]);;

let RING_ISOMORPHISM_ID = prove
 (`!r:A ring. ring_isomorphism (r,r) (\x. x)`,
  REWRITE_TAC[ring_isomorphism] THEN MESON_TAC[RING_ISOMORPHISMS_ID]);;

let RING_HOMOMORPHISM_COMPOSE = prove
 (`!r1 r2 r3 (f:A->B) (g:B->C).
        ring_homomorphism(r1,r2) f /\ ring_homomorphism(r2,r3) g
        ==> ring_homomorphism(r1,r3) (g o f)`,
  SIMP_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM]);;

let RING_MONOMORPHISM_COMPOSE = prove
 (`!r1 r2 r3 (f:A->B) (g:B->C).
        ring_monomorphism(r1,r2) f /\ ring_monomorphism(r2,r3) g
        ==> ring_monomorphism(r1,r3) (g o f)`,
  REWRITE_TAC[ring_monomorphism; ring_homomorphism; INJECTIVE_ON_ALT] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM]);;

let RING_MONOMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        ring_homomorphism(A,B) f /\ ring_homomorphism(B,C) g /\
        ring_monomorphism(A,C) (g o f)
        ==> ring_monomorphism(A,B) f`,
  REWRITE_TAC[ring_monomorphism; o_THM] THEN MESON_TAC[]);;

let RING_EPIMORPHISM_COMPOSE = prove
 (`!r1 r2 r3 (f:A->B) (g:B->C).
        ring_epimorphism(r1,r2) f /\ ring_epimorphism(r2,r3) g
        ==> ring_epimorphism(r1,r3) (g o f)`,
  SIMP_TAC[ring_epimorphism; IMAGE_o] THEN
  MESON_TAC[RING_HOMOMORPHISM_COMPOSE]);;

let RING_EPIMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        ring_homomorphism(A,B) f /\ ring_homomorphism(B,C) g /\
        ring_epimorphism(A,C) (g o f)
        ==> ring_epimorphism(B,C) g`,
  REWRITE_TAC[ring_epimorphism; ring_homomorphism; o_THM; IMAGE_o] THEN
  SET_TAC[]);;

let RING_MONOMORPHISM_LEFT_INVERTIBLE = prove
 (`!r r' (f:A->B) g.
        ring_homomorphism(r,r') f /\
        (!x. x IN ring_carrier r ==> g(f x) = x)
        ==> ring_monomorphism (r,r') f`,
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; ring_monomorphism] THEN
  MESON_TAC[]);;

let RING_EPIMORPHISM_RIGHT_INVERTIBLE = prove
 (`!r r' (f:A->B) g.
        ring_homomorphism(r,r') f /\
        ring_homomorphism(r',r) g /\
        (!x. x IN ring_carrier r ==> g(f x) = x)
        ==> ring_epimorphism (r',r) g`,
  SIMP_TAC[ring_epimorphism] THEN REWRITE_TAC[ring_homomorphism] THEN
  SET_TAC[]);;

let RING_HOMOMORPHISM_INTO_SUBRING = prove
 (`!r r' h (f:A->B).
        ring_homomorphism (r,r') f /\ IMAGE f (ring_carrier r) SUBSET h
        ==> ring_homomorphism (r,subring_generated r' h) f`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_homomorphism; SUBRING_GENERATED] THEN
  REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[]);;

let RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN = prove
 (`!(f:A->B) r r' s.
      ring_homomorphism(r,subring_generated r' s) f <=>
      ring_homomorphism(r,r') f /\
      IMAGE f (ring_carrier r) SUBSET ring_carrier(subring_generated r' s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_homomorphism] THEN
  MP_TAC(ISPECL [`r':B ring`; `s:B->bool`]
    RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN
  REWRITE_TAC[SUBRING_GENERATED] THEN SET_TAC[]);;

let RING_HOMOMORPHISM_INTO_SUBRING_EQ = prove
 (`!r r' h (f:A->B).
        h subring_of r'
        ==> (ring_homomorphism (r,subring_generated r' h) f <=>
             ring_homomorphism (r,r') f /\
             IMAGE f (ring_carrier r) SUBSET h)`,
  SIMP_TAC[RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN;
           CARRIER_SUBRING_GENERATED_SUBRING]);;

let RING_HOMOMORPHISM_FROM_SUBRING_GENERATED = prove
 (`!(f:A->B) r r' s.
        ring_homomorphism (r,r') f
        ==> ring_homomorphism(subring_generated r s,r') f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_homomorphism] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
        RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN
  SIMP_TAC[SUBSET; SUBRING_GENERATED; INTERS_GSPEC; FORALL_IN_IMAGE] THEN
  SET_TAC[]);;

let RING_MONOMORPHISM_FROM_SUBRING_GENERATED = prove
 (`!(f:A->B) r r' s.
        ring_monomorphism (r,r') f
        ==> ring_monomorphism(subring_generated r s,r') f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_monomorphism] THEN
  MATCH_MP_TAC MONO_AND THEN
  REWRITE_TAC[RING_HOMOMORPHISM_FROM_SUBRING_GENERATED] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
    RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN
  SET_TAC[]);;

let RING_HOMOMORPHISM_INCLUSION = prove
 (`!r s:A->bool. ring_homomorphism(subring_generated r s,r) (\x. x)`,
  SIMP_TAC[RING_HOMOMORPHISM_FROM_SUBRING_GENERATED;
           RING_HOMOMORPHISM_ID]);;

let RING_MONOMORPHISM_INCLUSION = prove
 (`!r s:A->bool. ring_monomorphism(subring_generated r s,r) (\x. x)`,
  SIMP_TAC[RING_MONOMORPHISM_FROM_SUBRING_GENERATED;
           RING_MONOMORPHISM_ID]);;

let RING_HOMOMORPHISM_BETWEEN_SUBRINGS = prove
 (`!r r' s t (f:A->B).
      ring_homomorphism(r,r') f /\ IMAGE f s SUBSET t
      ==> ring_homomorphism(subring_generated r s,subring_generated r' t) f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN] THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_FROM_SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p /\ q`] THEN
  MATCH_MP_TAC SUBRING_GENERATED_INDUCT THEN RULE_ASSUM_TAC
   (REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  MP_TAC(REWRITE_RULE[SUBSET] (ISPECL [`r:A ring`; `s:A->bool`]
        RING_CARRIER_SUBRING_GENERATED_SUBSET)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] SUBRING_GENERATED_SUBSET_CARRIER) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_0; SUBRING_GENERATED]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_1; SUBRING_GENERATED]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_NEG; SUBRING_GENERATED]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_ADD; SUBRING_GENERATED]; ALL_TAC] THEN
  ASM_MESON_TAC[RING_MUL; SUBRING_GENERATED]);;

let RING_HOMOMORPHISM_BETWEEN_SUBRINGS_ALT = prove
 (`!r s g h (f:A->B).
      ring_homomorphism(r,s) f /\ IMAGE f (ring_carrier r INTER g) SUBSET h
      ==> ring_homomorphism(subring_generated r g,subring_generated s h) f`,
  MESON_TAC[SUBRING_GENERATED_RESTRICT;
            RING_HOMOMORPHISM_BETWEEN_SUBRINGS]);;

let RING_MONOMORPHISM_BETWEEN_SUBRINGS = prove
 (`!r r' s t (f:A->B).
      ring_monomorphism(r,r') f /\ IMAGE f s SUBSET t
      ==> ring_monomorphism(subring_generated r s,subring_generated r' t) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_monomorphism] THEN
  SIMP_TAC[RING_HOMOMORPHISM_BETWEEN_SUBRINGS] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
    RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN
  SET_TAC[]);;

let RING_MONOMORPHISM_INTO_SUPERRING = prove
 (`!r r' t (f:A->B).
        ring_monomorphism(r,subring_generated r' t) f
        ==> ring_monomorphism(r,r') f`,
  REWRITE_TAC[ring_monomorphism; RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN] THEN
  MESON_TAC[]);;

let RING_SUM_SUBRING_GENERATED_GEN = prove
 (`!r s k (f:K->A).
      ring_sum (subring_generated r s) k f =
      ring_sum r {x | x IN k /\ f x IN ring_carrier(subring_generated r s)} f`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC
   (REWRITE_RULE[o_DEF; ETA_AX] (MATCH_MP RING_MONOMORPHISM_SUM_GEN
        (SPEC_ALL RING_MONOMORPHISM_INCLUSION))));;

let RING_SUM_SUBRING_GENERATED = prove
 (`!r s k (f:K->A).
        s subring_of r
        ==> ring_sum (subring_generated r s) k f =
            ring_sum r {x | x IN k /\ f x IN s} f`,
  REWRITE_TAC[RING_SUM_SUBRING_GENERATED_GEN] THEN
  SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING]);;

let SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) s.
        ring_homomorphism(r,r') f /\ s SUBSET ring_carrier r
        ==> ring_carrier (subring_generated r' (IMAGE f s)) =
            IMAGE f (ring_carrier(subring_generated r s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC SUBRING_GENERATED_INDUCT THEN
    REWRITE_TAC[FORALL_IN_IMAGE_2] THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    MP_TAC(REWRITE_RULE[SUBSET] (ISPECL [`r:A ring`; `s:A->bool`]
        RING_CARRIER_SUBRING_GENERATED_SUBSET)) THEN
    FIRST_X_ASSUM(MP_TAC o GSYM o GEN_REWRITE_RULE I [ring_homomorphism]) THEN
    ASM_SIMP_TAC[SUBRING_GENERATED_INC; FUN_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_MESON_TAC[SUBRING_GENERATED; RING_0; RING_NEG; RING_ADD;
                  RING_1; RING_MUL];
    FIRST_ASSUM(MP_TAC o ISPECL [`s:A->bool`; `IMAGE (f:A->B) s`] o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_BETWEEN_SUBRINGS)) THEN
    SIMP_TAC[ring_homomorphism; SUBSET_REFL]]);;

let RING_EPIMORPHISM_BETWEEN_SUBRINGS = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f /\ s SUBSET ring_carrier r
        ==> ring_epimorphism(subring_generated r s,
                             subring_generated r' (IMAGE f s)) f`,
  REWRITE_TAC[ring_epimorphism; RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN] THEN
  SIMP_TAC[RING_HOMOMORPHISM_FROM_SUBRING_GENERATED] THEN
  ASM_SIMP_TAC[SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE; SUBSET_REFL]);;

let RING_ISOMORPHISM = prove
 (`!r r' f:A->B.
      ring_isomorphism (r,r') (f:A->B) <=>
      ring_homomorphism (r,r') f /\
      IMAGE f (ring_carrier r) = ring_carrier r' /\
      (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ f x = f y
             ==> x = y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ring_isomorphism; ring_isomorphisms; ring_homomorphism] THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; RIGHT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME
    `IMAGE (f:A->B) (ring_carrier r) = ring_carrier r'`)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_IMAGE_2] THEN
  ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[RING_0; RING_ADD; RING_MUL; RING_1; RING_NEG]);;

let RING_ISOMORPHISM_SUBSET = prove
 (`!r r' f:A->B.
      ring_isomorphism (r,r') (f:A->B) <=>
      ring_homomorphism (r,r') f /\
      ring_carrier r' SUBSET IMAGE f (ring_carrier r) /\
      (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ f x = f y
             ==> x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RING_ISOMORPHISM; ring_homomorphism] THEN
  SET_TAC[]);;

let SUBRING_OF_HOMOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) h.
        ring_homomorphism (r,r') f /\ h subring_of r
        ==> IMAGE f h subring_of r'`,
  REWRITE_TAC[ring_homomorphism; subring_of] THEN SET_TAC[]);;

let RING_IDEAL_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) j.
        ring_epimorphism (r,r') f /\ ring_ideal r j
        ==> ring_ideal r' (IMAGE f j)`,
  REWRITE_TAC[ring_epimorphism; ring_homomorphism; ring_ideal] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  ASM SET_TAC[]);;

let SUBRING_OF_HOMOMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B) h.
        ring_homomorphism(r,r') f /\ h subring_of r'
        ==> {x | x IN ring_carrier r /\ f x IN h} subring_of r`,
  REWRITE_TAC[ring_homomorphism; subring_of; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let SUBRING_OF_EPIMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B) h.
        ring_epimorphism(r,r') f /\ h subring_of r'
        ==> {x | x IN ring_carrier r /\ f x IN h} subring_of r /\
            IMAGE f {x | x IN ring_carrier r /\ f x IN h} = h`,
  REWRITE_TAC[ring_epimorphism] THEN
  REWRITE_TAC[ring_homomorphism; subring_of; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  MESON_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let RING_IDEAL_HOMOMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B) j.
        ring_homomorphism(r,r') f /\ ring_ideal r' j
        ==> ring_ideal r {x | x IN ring_carrier r /\ f x IN j}`,
  REWRITE_TAC[ring_homomorphism; ring_ideal; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) s.
        ring_epimorphism(r,r') f /\ s SUBSET ring_carrier r
        ==> ideal_generated r' (IMAGE f s) = IMAGE f (ideal_generated r s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_SUBSET_CARRIER_SUBSET; IMAGE_SUBSET] THEN
    ASM_MESON_TAC[RING_IDEAL_IDEAL_GENERATED; RING_IDEAL_EPIMORPHIC_IMAGE];
    MATCH_MP_TAC(SET_RULE
     `u SUBSET {x | x IN ring_carrier r  /\ f x IN t}
      ==> IMAGE f u SUBSET t`) THEN
    MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s SUBSET u /\ IMAGE f s SUBSET t
        ==> s SUBSET {x | x IN u /\ f x IN t}`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IDEAL_GENERATED_SUBSET_CARRIER_SUBSET THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ring_epimorphism]) THEN ASM SET_TAC[];
      MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN
      ASM_MESON_TAC[RING_IDEAL_IDEAL_GENERATED; ring_epimorphism]]]);;

let RING_MONOMORPHISM_EPIMORPHISM = prove
 (`!r r' f:A->B.
        ring_monomorphism (r,r') f /\ ring_epimorphism (r,r') f <=>
        ring_isomorphism (r,r') f`,
  REWRITE_TAC[RING_ISOMORPHISM; ring_monomorphism; ring_epimorphism] THEN
  MESON_TAC[]);;

let SUBRING_MONOMORPHISM_EPIMORPHISM = prove
 (`!r r' s (f:A->B).
        ring_monomorphism(r,r') f /\
        ring_epimorphism(r,subring_generated r' s) f <=>
        ring_isomorphism(r,subring_generated r' s) f`,
  MESON_TAC[RING_MONOMORPHISM_EPIMORPHISM; RING_MONOMORPHISM_INTO_SUPERRING;
            RING_HOMOMORPHISM_INTO_SUBRING; ring_monomorphism;
            ring_epimorphism]);;

let RING_ISOMORPHISM_EPIMORPHISM = prove
 (`!r r' (f:A->B).
        ring_isomorphism (r,r') f <=>
        ring_epimorphism (r,r') f /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ f x = f y
               ==> x = y)`,
  REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM;
              ring_monomorphism; ring_epimorphism] THEN
  MESON_TAC[]);;

let RING_ISOMORPHISM_MONOMORPHISM = prove
 (`!r r' f:A->B.
        ring_isomorphism (r,r') f <=>
        ring_monomorphism (r,r') f /\
        IMAGE f (ring_carrier r) = ring_carrier r'`,
  REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[ring_monomorphism; ring_epimorphism] THEN
  MESON_TAC[]);;

let RING_ISOMORPHISM_MONOMORPHISM_ALT = prove
 (`!r r' f:A->B.
        ring_isomorphism (r,r') f <=>
        ring_monomorphism (r,r') f /\
        ring_carrier r' SUBSET IMAGE f (ring_carrier r)`,
  REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[ring_monomorphism; ring_epimorphism] THEN
  REWRITE_TAC[ring_homomorphism] THEN SET_TAC[]);;

let RING_ISOMORPHISM_IMP_MONOMORPHISM = prove
 (`!r r' (f:A->B).
        ring_isomorphism (r,r') f ==> ring_monomorphism (r,r') f`,
  SIMP_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM]);;

let RING_ISOMORPHISM_IMP_EPIMORPHISM = prove
 (`!r r' (f:A->B).
        ring_isomorphism (r,r') f ==> ring_epimorphism (r,r') f`,
  SIMP_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM]);;

let RING_ISOMORPHISM_IMP_HOMOMORPHISM = prove
 (`!(f:A->B) r r'. ring_isomorphism(r,r') f ==> ring_homomorphism(r,r') f`,
  SIMP_TAC[RING_ISOMORPHISM]);;

let RING_AUTOMORPHISM_IMP_ENDOMORPHISM = prove
 (`!r (f:A->A). ring_automorphism r f ==> ring_endomorphism r f`,
  REWRITE_TAC[ring_automorphism; ring_endomorphism] THEN
  REWRITE_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM]);;

let RING_ISOMORPHISMS_ISOMORPHISM = prove
 (`!r r' (f:A->B) g.
        ring_isomorphisms (r,r') (f,g) <=>
        ring_isomorphism (r,r') f /\
        ring_isomorphism (r',r) g /\
        (!x. x IN ring_carrier r ==> g (f x) = x) /\
        (!y. y IN ring_carrier r' ==> f (g y) = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[ring_isomorphisms; RING_ISOMORPHISMS_IMP_ISOMORPHISM;
              RING_ISOMORPHISMS_IMP_ISOMORPHISM_ALT];
    SIMP_TAC[ring_isomorphisms] THEN
    MESON_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM]]);;

let RING_ISOMORPHISM_EQ_MONOMORPHISM_FINITE = prove
 (`!G H (f:A->B).
        FINITE(ring_carrier G) /\ FINITE(ring_carrier H) /\
        CARD(ring_carrier G) = CARD(ring_carrier H)
        ==> (ring_isomorphism(G,H) f <=> ring_monomorphism(G,H) f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[RING_ISOMORPHISM_IMP_MONOMORPHISM] THEN
  SIMP_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[ring_monomorphism; ring_epimorphism] THEN
  REWRITE_TAC[ring_homomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MP_TAC(ISPECL
   [`ring_carrier G:A->bool`; `ring_carrier H:B->bool`; `f:A->B`]
        SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let RING_ISOMORPHISM_EQ_EPIMORPHISM_FINITE = prove
 (`!G H (f:A->B).
        FINITE(ring_carrier G) /\ FINITE(ring_carrier H) /\
        CARD(ring_carrier G) = CARD(ring_carrier H)
        ==> (ring_isomorphism(G,H) f <=> ring_epimorphism(G,H) f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[RING_ISOMORPHISM_IMP_EPIMORPHISM] THEN
  SIMP_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[ring_monomorphism; ring_epimorphism] THEN
  REWRITE_TAC[ring_homomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MP_TAC(ISPECL
   [`ring_carrier G:A->bool`; `ring_carrier H:B->bool`; `f:A->B`]
        SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let RING_ISOMORPHISMS_BETWEEN_SUBRINGS = prove
 (`!r r' g h (f:A->B) f'.
      ring_isomorphisms(r,r') (f,f') /\
      IMAGE f g SUBSET h /\ IMAGE f' h SUBSET g
      ==> ring_isomorphisms (subring_generated r g,subring_generated r' h)
                             (f,f')`,
  SIMP_TAC[ring_isomorphisms; RING_HOMOMORPHISM_BETWEEN_SUBRINGS] THEN
  MESON_TAC[SUBSET; RING_CARRIER_SUBRING_GENERATED_SUBSET]);;

let RING_ISOMORPHISMS_BETWEEN_SUBRINGS_ALT = prove
 (`!r s g h (f:A->B) f'.
      ring_isomorphisms(r,s) (f,f') /\
      IMAGE f (ring_carrier r INTER g) SUBSET h /\
      IMAGE f' (ring_carrier s INTER h) SUBSET g
      ==> ring_isomorphisms (subring_generated r g,subring_generated s h)
                             (f,f')`,
  SIMP_TAC[ring_isomorphisms; RING_HOMOMORPHISM_BETWEEN_SUBRINGS_ALT] THEN
  MESON_TAC[SUBSET; RING_CARRIER_SUBRING_GENERATED_SUBSET]);;

let RING_ISOMORPHISM_BETWEEN_SUBRINGS = prove
 (`!r r' g h (f:A->B).
      ring_isomorphism(r,r') f /\ g SUBSET ring_carrier r /\ IMAGE f g = h
      ==> ring_isomorphism(subring_generated r g,subring_generated r' h) f`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ring_isomorphism] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f':B->A` THEN
  REWRITE_TAC[ring_isomorphisms] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[RING_HOMOMORPHISM_BETWEEN_SUBRINGS; SUBSET_REFL];
    ALL_TAC;
    ASM_MESON_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET; SUBSET];
    ASM_MESON_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET; SUBSET]] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SUBRING_GENERATED_RESTRICT] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_BETWEEN_SUBRINGS THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN
  ASM SET_TAC[]);;

let RING_ISOMORPHISMS_COMPOSE = prove
 (`!r1 r2 r3 (f1:A->B) (f2:B->C) g1 g2.
        ring_isomorphisms(r1,r2) (f1,g1) /\ ring_isomorphisms(r2,r3) (f2,g2)
        ==> ring_isomorphisms(r1,r3) (f2 o f1,g1 o g2)`,
  SIMP_TAC[ring_isomorphisms; ring_homomorphism;
           SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM]);;

let RING_ISOMORPHISM_COMPOSE = prove
 (`!r1 r2 r3 (f:A->B) (g:B->C).
        ring_isomorphism(r1,r2) f /\ ring_isomorphism(r2,r3) g
        ==> ring_isomorphism(r1,r3) (g o f)`,
  REWRITE_TAC[ring_isomorphism] THEN MESON_TAC[RING_ISOMORPHISMS_COMPOSE]);;

let RING_ISOMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        ring_homomorphism(A,B) f /\ ring_homomorphism(B,C) g /\
        ring_isomorphism(A,C) (g o f)
        ==> ring_monomorphism(A,B) f /\ ring_epimorphism(B,C) g`,
  REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  MESON_TAC[RING_MONOMORPHISM_COMPOSE_REV; RING_EPIMORPHISM_COMPOSE_REV]);;

let RING_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        ring_epimorphism (A,B) f /\
        ring_homomorphism (B,C) g /\
        ring_isomorphism (A,C) (g o f)
        ==> ring_isomorphism (A,B) f /\ ring_isomorphism (B,C) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RING_ISOMORPHISM_COMPOSE_REV; ring_epimorphism;
                  RING_MONOMORPHISM_EPIMORPHISM];
    REWRITE_TAC[ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f':B->A` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM ring_isomorphism] THEN
    MATCH_MP_TAC RING_ISOMORPHISM_EQ THEN
    EXISTS_TAC `(g:B->C) o f o (f':B->A)` THEN CONJ_TAC THENL
     [REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC RING_ISOMORPHISM_COMPOSE THEN
      ASM_MESON_TAC[RING_ISOMORPHISMS_SYM; ring_isomorphism];
      RULE_ASSUM_TAC(REWRITE_RULE
       [ring_isomorphisms; ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC[o_THM]]]);;

let RING_MONOMORPHISM_ISOMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        ring_homomorphism (A,B) f /\
        ring_monomorphism (B,C) g /\
        ring_isomorphism (A,C) (g o f)
        ==> ring_isomorphism (A,B) f /\ ring_isomorphism (B,C) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RING_ISOMORPHISM_COMPOSE_REV; ring_monomorphism;
                  RING_MONOMORPHISM_EPIMORPHISM];
    REWRITE_TAC[ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g':C->B` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM ring_isomorphism] THEN
    MATCH_MP_TAC RING_ISOMORPHISM_EQ THEN
    EXISTS_TAC `(g':C->B) o g o (f:A->B)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_ISOMORPHISM_COMPOSE THEN
      ASM_MESON_TAC[RING_ISOMORPHISMS_SYM; ring_isomorphism];
      RULE_ASSUM_TAC(REWRITE_RULE
       [ring_isomorphisms; ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC[o_THM]]]);;

let RING_ISOMORPHISM_INVERSE = prove
 (`!(f:A->B) g r r'.
        ring_isomorphism(r,r') f /\
        (!x. x IN ring_carrier r ==> g(f x) = x)
        ==> ring_isomorphism(r',r) g`,
  REWRITE_TAC[ring_isomorphism; ring_isomorphisms; ring_homomorphism] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `f:A->B` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier r' ==> (g:B->A) y IN ring_carrier r`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier r' ==> (f:A->B)(g y) = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let RING_HOMOMORPHISM_FROM_TRIVIAL_RING = prove
 (`!(f:A->B) r r'.
        trivial_ring r
        ==> (ring_homomorphism(r,r') f <=>
             trivial_ring r' /\ IMAGE f (ring_carrier r) = {ring_0 r'})`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [trivial_ring] THEN DISCH_TAC THEN EQ_TAC THENL
   [ASM_SIMP_TAC[ring_homomorphism; TRIVIAL_RING_10] THEN
    MP_TAC(ISPEC `r:A ring` RING_1) THEN ASM SET_TAC[];
    SIMP_TAC[trivial_ring; RING_HOMOMORPHISM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP
     (SET_RULE `IMAGE f s = {a} ==> !x. x IN s ==> f x = a`)) THEN
    ASM_SIMP_TAC[RING_0; RING_1; RING_ADD; RING_MUL;
                 RING_ADD_LZERO; RING_MUL_LZERO] THEN
    MP_TAC(ISPEC `r':B ring` RING_0) THEN
    MP_TAC(ISPEC `r':B ring` RING_1) THEN ASM SET_TAC[]]);;

let RING_MONOMORPHISM_FROM_TRIVIAL_RING = prove
 (`!(f:A->B) r r'.
        trivial_ring r
        ==> (ring_monomorphism (r,r') f <=> ring_homomorphism (r,r') f)`,
  REWRITE_TAC[ring_monomorphism; trivial_ring] THEN SET_TAC[]);;

let RING_MONOMORPHISM_TO_TRIVIAL_RING = prove
 (`!(f:A->B) r r'.
        trivial_ring r'
        ==> (ring_monomorphism (r,r') f <=>
             ring_homomorphism (r,r') f /\ trivial_ring r)`,
  SIMP_TAC[ring_monomorphism; trivial_ring; ring_homomorphism] THEN
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `r:A ring` RING_0) THEN SET_TAC[]);;

let RING_EPIMORPHISM_FROM_TRIVIAL_RING = prove
 (`!(f:A->B) r r'.
        trivial_ring r
        ==> (ring_epimorphism (r,r') f <=>
             ring_homomorphism (r,r') f /\ trivial_ring r')`,
  SIMP_TAC[ring_epimorphism; trivial_ring; ring_homomorphism] THEN
  SET_TAC[]);;

let RING_EPIMORPHISM_TO_TRIVIAL_RING = prove
 (`!(f:A->B) r r'.
        trivial_ring r'
        ==> (ring_epimorphism (r,r') f <=>
             ring_homomorphism (r,r') f)`,
  REWRITE_TAC[ring_epimorphism; trivial_ring; ring_homomorphism] THEN
  REPEAT GEN_TAC THEN
  MAP_EVERY(MP_TAC o C ISPEC RING_0) [`r:A ring`; `r':B ring`] THEN
  SET_TAC[]);;

let TRIVIAL_RING_MONOMORPHIC_PREIMAGE = prove
 (`!r r' f:A->B.
        ring_monomorphism (r,r') f /\ trivial_ring r' ==> trivial_ring r`,
  MESON_TAC[RING_MONOMORPHISM_TO_TRIVIAL_RING]);;

let TRIVIAL_RING_HOMOMORPHIC_IMAGE = prove
 (`!r r' f:A->B.
        ring_homomorphism(r,r') f /\ trivial_ring r ==> trivial_ring r'`,
  REWRITE_TAC[ring_homomorphism; TRIVIAL_RING_10] THEN MESON_TAC[]);;

let TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ = prove
 (`!r r' f:A->B.
        ring_monomorphism (r,r') f
        ==> (trivial_ring r <=> trivial_ring r')`,
  MESON_TAC[TRIVIAL_RING_MONOMORPHIC_PREIMAGE;
            TRIVIAL_RING_HOMOMORPHIC_IMAGE;
            RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let RING_NILPOTENT_HOMOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) a.
        ring_homomorphism (r,r') f /\ ring_nilpotent r a
        ==> ring_nilpotent r' (f a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ring_nilpotent; RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[];
    ASM_MESON_TAC[RING_HOMOMORPHISM_POW; RING_HOMOMORPHISM_0]]);;

let RING_NILPOTENT_MONOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) a.
        ring_monomorphism(r,r') f /\ a IN ring_carrier r
        ==> (ring_nilpotent r' (f a) <=> ring_nilpotent r a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_nilpotent] THEN BINOP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[];
    FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
          (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM th))]) THEN
    ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; RING_POW]]);;

let RING_CHAR_MONOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f ==> ring_char r = ring_char r'`,
  REWRITE_TAC[RING_CHAR_UNIQUE; GSYM RING_OF_NUM_EQ_0] THEN
  MESON_TAC[RING_MONOMORPHISM_EQ_0; RING_HOMOMORPHISM_RING_OF_NUM;
            RING_OF_NUM; ring_monomorphism]);;

(* ------------------------------------------------------------------------- *)
(* Relation of isomorphism.                                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("isomorphic_ring",(12, "right"));;

let isomorphic_ring = new_definition
 `r isomorphic_ring r' <=> ?f:A->B. ring_isomorphism (r,r') f`;;

let RING_ISOMORPHISM_IMP_ISOMORPHIC = prove
 (`!r r' f:A->B. ring_isomorphism (r,r') f ==> r isomorphic_ring r'`,
  REWRITE_TAC[isomorphic_ring] THEN MESON_TAC[]);;

let ISOMORPHIC_RING_REFL = prove
 (`!r:A ring. r isomorphic_ring r`,
  GEN_TAC THEN REWRITE_TAC[isomorphic_ring] THEN EXISTS_TAC `\x:A. x` THEN
  REWRITE_TAC[RING_ISOMORPHISM_ID]);;

let ISOMORPHIC_RING_SYM = prove
 (`!(r:A ring) (r':B ring). r isomorphic_ring r' <=> r' isomorphic_ring r`,
  REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  MESON_TAC[RING_ISOMORPHISMS_SYM]);;

let ISOMORPHIC_RING_TRANS = prove
 (`!(r1:A ring) (r2:B ring) (r3:C ring).
        r1 isomorphic_ring r2 /\ r2 isomorphic_ring r3
        ==> r1 isomorphic_ring r3`,
  REWRITE_TAC[isomorphic_ring] THEN MESON_TAC[RING_ISOMORPHISM_COMPOSE]);;

let ISOMORPHIC_RING_TRIVIALITY = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> (trivial_ring r <=> trivial_ring r')`,
  REWRITE_TAC[isomorphic_ring; TRIVIAL_RING; ring_isomorphism;
              ring_isomorphisms; ring_homomorphism] THEN
  SET_TAC[]);;

let ISOMORPHIC_TO_TRIVIAL_RING = prove
 (`(!(r:A ring) (r':B ring).
        trivial_ring r ==> (r isomorphic_ring r' <=> trivial_ring r')) /\
   (!(r:A ring) (r':B ring).
        trivial_ring r' ==> (r isomorphic_ring r' <=> trivial_ring r))`,
  let lemma = prove
   (`!(r:A ring) (r':B ring).
        trivial_ring r ==> (r isomorphic_ring r' <=> trivial_ring r')`,
    REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ASM_MESON_TAC[ISOMORPHIC_RING_TRIVIALITY]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[TRIVIAL_RING; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    X_GEN_TAC `b:B` THEN DISCH_TAC THEN
    REWRITE_TAC[isomorphic_ring; RING_ISOMORPHISM] THEN
    EXISTS_TAC `(\x. b):A->B` THEN
    ASM_REWRITE_TAC[ring_homomorphism] THEN
    SIMP_TAC[IN_SING; IMAGE_CLAUSES; SUBSET_REFL] THEN
    ASM_MESON_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL; IN_SING]) in
  REWRITE_TAC[lemma] THEN ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  REWRITE_TAC[lemma]);;

let ISOMORPHIC_TRIVIAL_RINGS = prove
 (`!(G:A ring) (H:B ring).
        trivial_ring G /\ trivial_ring H
        ==> G isomorphic_ring H`,
  MESON_TAC[ISOMORPHIC_TO_TRIVIAL_RING]);;

let ISOMORPHIC_RING_SINGLETON_RING = prove
 (`(!(r:A ring) (b:B).
        r isomorphic_ring singleton_ring b <=> trivial_ring r) /\
   (!a:A (r:B ring).
        singleton_ring a isomorphic_ring r <=> trivial_ring r)`,
  MESON_TAC[ISOMORPHIC_TO_TRIVIAL_RING; TRIVIAL_RING_SINGLETON_RING]);;

let CARD_LE_RING_MONOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f ==> ring_carrier r <=_c ring_carrier r'`,
  REWRITE_TAC[ring_monomorphism; le_c; ring_homomorphism] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `f:A->B` THEN ASM SET_TAC[]);;

let CARD_LE_RING_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f ==> ring_carrier r' <=_c ring_carrier r`,
  REWRITE_TAC[ring_epimorphism; LE_C; ring_homomorphism] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `f:A->B` THEN ASM SET_TAC[]);;

let CARD_EQ_RING_ISOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_isomorphism(r,r') f ==> ring_carrier r =_c ring_carrier r'`,
  REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM; GSYM CARD_LE_ANTISYM] THEN
  MESON_TAC[CARD_LE_RING_MONOMORPHIC_IMAGE; CARD_LE_RING_EPIMORPHIC_IMAGE]);;

let ISOMORPHIC_RING_CARD_EQ = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> ring_carrier r =_c ring_carrier r'`,
  REWRITE_TAC[isomorphic_ring; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[CARD_EQ_RING_ISOMORPHIC_IMAGE]);;

let ISOMORPHIC_RING_FINITENESS = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r'
        ==> (FINITE(ring_carrier r) <=> FINITE(ring_carrier r'))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHIC_RING_CARD_EQ) THEN
  REWRITE_TAC[CARD_FINITE_CONG]);;

let ISOMORPHIC_RING_INFINITENESS = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r'
        ==> (INFINITE(ring_carrier r) <=> INFINITE(ring_carrier r'))`,
  REWRITE_TAC[INFINITE; TAUT `(~p <=> ~q) <=> (p <=> q)`] THEN
  REWRITE_TAC[ISOMORPHIC_RING_FINITENESS]);;

let FINITE_RING_MONOMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f /\ FINITE(ring_carrier r')
        ==> FINITE(ring_carrier r)`,
  MESON_TAC[CARD_LE_FINITE; CARD_LE_RING_MONOMORPHIC_IMAGE]);;

let FINITE_RING_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f /\ FINITE(ring_carrier r)
        ==> FINITE(ring_carrier r')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_FINITE) THEN
  ASM_MESON_TAC[CARD_LE_RING_EPIMORPHIC_IMAGE]);;

let CARD_EQ_RING_MONOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f
        ==> IMAGE f (ring_carrier r) =_c ring_carrier r`,
  REWRITE_TAC[ring_monomorphism] THEN MESON_TAC[CARD_EQ_IMAGE]);;

let ISOMORPHIC_RING_SIZE = prove
 (`!(r:A ring) (r':B ring) n.
        r isomorphic_ring r'
        ==> (ring_carrier r HAS_SIZE n <=> ring_carrier r' HAS_SIZE n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHIC_RING_CARD_EQ) THEN
  REWRITE_TAC[CARD_HAS_SIZE_CONG]);;

let ISOMORPHIC_RING_CARD = prove
 (`!(G:A ring) (H:B ring).
        G isomorphic_ring H /\
        (FINITE(ring_carrier G) \/ FINITE(ring_carrier H))
        ==> CARD(ring_carrier G) = CARD(ring_carrier H)`,
  MESON_TAC[ISOMORPHIC_RING_SIZE; HAS_SIZE;
            ISOMORPHIC_RING_FINITENESS]);;

let ISOMORPHIC_RING_CHAR = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> ring_char r = ring_char r'`,
  REWRITE_TAC[isomorphic_ring] THEN
  MESON_TAC[RING_ISOMORPHISM_IMP_MONOMORPHISM; RING_CHAR_MONOMORPHIC_IMAGE]);;

let ISOMORPHIC_COPY_OF_RING = prove
 (`!(r:A ring) (s:B->bool).
        (?r'. ring_carrier r' = s /\ r isomorphic_ring r') <=>
        ring_carrier r =_c s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[ISOMORPHIC_RING_CARD_EQ; CARD_EQ_TRANS];
    REWRITE_TAC[EQ_C_BIJECTIONS; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`f:A->B`; `g:B->A`] THEN STRIP_TAC THEN
  ABBREV_TAC
   `r' = ring(s:B->bool,
              f (ring_0 r:A),
              f (ring_1 r),
              (\x. f(ring_neg r (g x))),
              (\x1 x2. f(ring_add r (g x1) (g x2))),
              (\x1 x2. f(ring_mul r (g x1) (g x2))))` THEN
  SUBGOAL_THEN
   `ring_carrier r' = s /\
    ring_0 r' = (f:A->B) (ring_0 r) /\
    ring_1 r' = f (ring_1 r) /\
    ring_neg r' = (\x. f(ring_neg r (g x))) /\
    ring_add r' = (\x1 x2. f(ring_add r (g x1) (g x2))) /\
    ring_mul r' = (\x1 x2. f(ring_mul r (g x1) (g x2)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r'" THEN PURE_REWRITE_TAC
     [GSYM PAIR_EQ; ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul;
      BETA_THM; PAIR] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 ring_tybij)] THEN
    REWRITE_TAC(map (GSYM o REWRITE_RULE[FUN_EQ_THM])
     [ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul]) THEN
    SUBGOAL_THEN `s = IMAGE (f:A->B) (ring_carrier r)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; RING_0; RING_1;
                 RING_NEG; RING_ADD; RING_MUL] THEN
    MESON_TAC[RING_ADD_SYM; RING_ADD_ASSOC; RING_ADD_LZERO;
              RING_ADD_LNEG; RING_MUL_SYM; RING_MUL_ASSOC;
              RING_MUL_LID; RING_ADD_LDISTRIB];
    EXISTS_TAC `r':B ring` THEN ASM_REWRITE_TAC[isomorphic_ring] THEN
    EXISTS_TAC `f:A->B` THEN REWRITE_TAC[ring_isomorphism] THEN
    EXISTS_TAC `g:B->A` THEN REWRITE_TAC[ring_isomorphisms] THEN
    ASM_SIMP_TAC[ring_homomorphism; RING_0; RING_1; SUBSET; FORALL_IN_IMAGE;
                 RING_NEG; RING_ADD; RING_MUL]]);;

(* ------------------------------------------------------------------------- *)
(* Kernels and images of homomorphisms.                                      *)
(* ------------------------------------------------------------------------- *)

let ring_kernel = new_definition
 `ring_kernel (r,r') (f:A->B) =
    {x | x IN ring_carrier r /\ f x = ring_0 r'}`;;

let ring_image = new_definition
 `ring_image (r:A ring,r':B ring) (f:A->B) = IMAGE f (ring_carrier r)`;;

let RING_KERNEL_0 = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> ring_0 r IN ring_kernel (r,r') f`,
  SIMP_TAC[ring_homomorphism; ring_kernel; IN_ELIM_THM; RING_0]);;

let RING_KERNEL_NONEMPTY = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f ==> ~(ring_kernel (r,r') f = {})`,
  MESON_TAC[RING_KERNEL_0; NOT_IN_EMPTY]);;

let RING_KERNEL_SUBSET_CARRIER = prove
 (`!r r' (f:A->B). ring_kernel (r,r') f SUBSET ring_carrier r`,
  REWRITE_TAC[ring_kernel; SUBSET_RESTRICT]);;

let RING_MONOMORPHISM = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f <=>
        ring_homomorphism(r,r') f /\
        ring_kernel (r,r') f = {ring_0 r}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_monomorphism] THEN
  REWRITE_TAC[TAUT `(p /\ q <=> p /\ r) <=> p ==> (q <=> r)`] THEN
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SING_SUBSET] THEN
  ASM_REWRITE_TAC[SUBSET; IN_SING; ring_kernel; IN_ELIM_THM; RING_0] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `ring_0 r:A`]) THEN
    ASM_SIMP_TAC[RING_0];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ring_sub r x y:A`) THEN
    ASM_SIMP_TAC[ring_sub; RING_ADD; RING_NEG] THEN
    REWRITE_TAC[GSYM ring_sub] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUB_EQ_0 o
      rand o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUB_EQ_0 o snd) THEN
    ASM_SIMP_TAC[]]);;

let RING_MONOMORPHISM_ALT = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f <=>
        ring_homomorphism(r,r') f /\
        !x. x IN ring_carrier r /\ f x = ring_0 r' ==> x = ring_0 r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RING_MONOMORPHISM; ring_kernel] THEN
  MP_TAC(ISPEC `r:A ring` RING_0) THEN
  REWRITE_TAC[ring_homomorphism] THEN SET_TAC[]);;

let RING_MONOMORPHISM_ALT_EQ = prove
 (`!r r' f:A->B.
        ring_monomorphism (r,r') f <=>
        ring_homomorphism (r,r') f /\
        !x. x IN ring_carrier r ==> (f x = ring_0 r' <=> x = ring_0 r)`,
  MESON_TAC[RING_MONOMORPHISM_ALT; ring_homomorphism]);;

let RING_EPIMORPHISM = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f <=>
        ring_homomorphism(r,r') f /\
        ring_image (r,r') f = ring_carrier r'`,
  REWRITE_TAC[ring_epimorphism; ring_image] THEN MESON_TAC[]);;

let RING_EPIMORPHISM_ALT = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f <=>
        ring_homomorphism(r,r') f /\
        ring_carrier r' SUBSET ring_image (r,r') f`,
  REWRITE_TAC[RING_EPIMORPHISM; ring_homomorphism; ring_image] THEN
  MESON_TAC[SUBSET_ANTISYM_EQ]);;

let RING_ISOMORPHISM_RING_KERNEL_RING_IMAGE = prove
 (`!r r' (f:A->B).
        ring_isomorphism (r,r') f <=>
        ring_homomorphism(r,r') f /\
        ring_kernel (r,r') f = {ring_0 r} /\
        ring_image (r,r') f = ring_carrier r'`,
  REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[RING_MONOMORPHISM; RING_EPIMORPHISM] THEN MESON_TAC[]);;

let RING_ISOMORPHISM_ALT = prove
 (`!r r' (f:A->B).
      ring_isomorphism (r,r') f <=>
      IMAGE f (ring_carrier r) = ring_carrier r' /\
      f (ring_1 r) = ring_1 r' /\
      (!x y. x IN ring_carrier r /\ y IN ring_carrier r
             ==> f(ring_add r x y) = ring_add r' (f x) (f y)) /\
      (!x y. x IN ring_carrier r /\ y IN ring_carrier r
             ==> f(ring_mul r x y) = ring_mul r' (f x) (f y)) /\
      (!x. x IN ring_carrier r /\ f x = ring_0 r' ==> x = ring_0 r)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `ring_homomorphism (r,r') (f:A->B)` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[RING_ISOMORPHISM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [RING_HOMOMORPHISM]) THEN
    MESON_TAC[SUBSET_REFL]] THEN
  ASM_REWRITE_TAC[RING_ISOMORPHISM_RING_KERNEL_RING_IMAGE;
                  ring_kernel; ring_image] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN
  MP_TAC(ISPEC `r:A ring` RING_0) THEN ASM SET_TAC[]);;

let CARD_EQ_RING_IMAGE_KERNEL = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> ring_image(r,r') f *_c ring_kernel(r,r') f =_c ring_carrier r`,
  REWRITE_TAC[ring_homomorphism; ring_image; SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_EQ_IMAGE_MUL_FIBRES THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN TRANS_TAC CARD_EQ_TRANS
   `IMAGE (ring_add r x) (ring_kernel(r,r') (f:A->B))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_REFL_IMP;
    MATCH_MP_TAC CARD_EQ_IMAGE THEN REWRITE_TAC[ring_kernel; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_ADD_LCANCEL_IMP]] THEN
  MATCH_MP_TAC(SET_RULE
   `!g. IMAGE f s SUBSET t /\ IMAGE g t SUBSET s /\ (!y. y IN t ==> f(g y) = y)
        ==> t = IMAGE f s`) THEN
  EXISTS_TAC `ring_add r (ring_neg r x:A)` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; ring_kernel] THEN
  ASM_SIMP_TAC[RING_ADD; RING_NEG; RING_ADD_RZERO; RING_ADD_LZERO;
               RING_ADD_LNEG; RING_ADD_ASSOC; RING_ADD_RNEG]);;

let RING_IDEAL_RING_KERNEL = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f ==> ring_ideal r (ring_kernel (r,r') f)`,
  SIMP_TAC[ring_homomorphism; ring_ideal; ring_kernel; IN_ELIM_THM; SUBSET;
           FORALL_IN_IMAGE; RING_ADD_LZERO; RING_0; RING_ADD;
           RING_NEG_0; RING_NEG; RING_MUL_RZERO; RING_MUL]);;

let SUBRING_RING_IMAGE = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f ==> (ring_image (r,r') f) subring_of r'`,
  SIMP_TAC[ring_homomorphism; subring_of; ring_image; SUBSET;
           FORALL_IN_IMAGE; FORALL_IN_IMAGE_2; IN_IMAGE] THEN
  MESON_TAC[RING_ADD; RING_NEG; RING_0; RING_1; RING_MUL]);;

let RING_KERNEL_TO_SUBRING_GENERATED = prove
 (`!r r' s (f:A->B).
        ring_kernel (r,subring_generated r' s) f = ring_kernel(r,r') f`,
  REWRITE_TAC[ring_kernel; SUBRING_GENERATED]);;

let RING_IMAGE_TO_SUBRING_GENERATED = prove
 (`!r r' s (f:A->B).
        ring_image (r,subring_generated r' s) f = ring_image(r,r') f`,
  REWRITE_TAC[ring_image]);;

let RING_KERNEL_FROM_SUBRING_GENERATED = prove
 (`!r r' s f:A->B.
        s subring_of r
        ==> ring_kernel(subring_generated r s,r') f =
            ring_kernel(r,r') f INTER s`,
  SIMP_TAC[ring_kernel; CARRIER_SUBRING_GENERATED_SUBRING] THEN
  REWRITE_TAC[subring_of] THEN SET_TAC[]);;

let RING_IMAGE_FROM_SUBRING_GENERATED = prove
 (`!r r' s f:A->B.
        s subring_of r
        ==> ring_image(subring_generated r s,r') f =
            ring_image(r,r') f INTER IMAGE f s`,
  SIMP_TAC[ring_image; CARRIER_SUBRING_GENERATED_SUBRING] THEN
  REWRITE_TAC[subring_of] THEN SET_TAC[]);;

let RING_ISOMORPHISM_ONTO_IMAGE = prove
 (`!(f:A->B) r r'.
        ring_isomorphism(r,subring_generated r' (ring_image (r,r') f)) f <=>
        ring_monomorphism(r,r') f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[ring_monomorphism; ring_epimorphism] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN] THEN
  ASM_CASES_TAC `ring_homomorphism (r,r') (f:A->B)` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; SUBRING_RING_IMAGE] THEN
  REWRITE_TAC[ring_image; SUBSET_REFL]);;

let SUBRING_IMP_MONOMORPHIC_PROPERTY = prove
 (`!P Q.
        (!r r'. r isomorphic_ring r' ==> (P r <=> Q r')) /\
        (!r s. Q r ==> Q(subring_generated r s))
        ==> !r r' (f:A->B). ring_monomorphism(r,r') f /\ Q r' ==> P r`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [GSYM RING_ISOMORPHISM_ONTO_IMAGE]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_ISOMORPHIC) THEN
  DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RING_KERNEL_FROM_TRIVIAL_RING = prove
 (`!r r' (f:A->B).
        ring_homomorphism (r,r') f /\ trivial_ring r
        ==> ring_kernel (r,r') f = ring_carrier r`,
  REWRITE_TAC[trivial_ring; ring_kernel; ring_homomorphism] THEN
  SET_TAC[]);;

let RING_IMAGE_FROM_TRIVIAL_RING = prove
 (`!r r' (f:A->B).
        ring_homomorphism (r,r') f /\ trivial_ring r
        ==> ring_image (r,r') f = {ring_0 r'}`,
  REWRITE_TAC[trivial_ring; ring_image; ring_homomorphism] THEN
  SET_TAC[]);;

let RING_KERNEL_TO_TRIVIAL_RING = prove
 (`!r r' (f:A->B).
        ring_homomorphism (r,r') f /\ trivial_ring r'
        ==> ring_kernel (r,r') f = ring_carrier r`,
  REWRITE_TAC[trivial_ring; ring_kernel; ring_homomorphism] THEN
  SET_TAC[]);;

let RING_IMAGE_TO_TRIVIAL_RING = prove
 (`!r r' (f:A->B).
        ring_homomorphism (r,r') f /\ trivial_ring r'
        ==> ring_image (r,r') f = ring_carrier r'`,
  REWRITE_TAC[trivial_ring; ring_image; ring_homomorphism] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SING_SUBSET; IN_IMAGE] THEN
  ASM_MESON_TAC[RING_0]);;

let RING_HOMOMORPHISM_PREIMAGE_IMAGE_GEN = prove
 (`!r r' (f:A->B) s.
        ring_homomorphism(r,r') f /\ s SUBSET ring_carrier r
        ==> {x | x IN ring_carrier r /\ f x IN IMAGE f s} =
            ring_setadd r s (ring_kernel(r,r') f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; ring_kernel; IN_ELIM_THM; ring_setadd] THEN
  X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    EXISTS_TAC `ring_sub r z x:A` THEN ASM_SIMP_TAC[RING_SUB] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_SUB) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUB_REFL THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[];
      TRANS_TAC EQ_TRANS `ring_add r (ring_sub r z x) x:A` THEN CONJ_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[RING_ADD_SYM; RING_SUB]] THEN
      ASM_SIMP_TAC[ring_sub; GSYM RING_ADD_ASSOC; RING_NEG] THEN
      ASM_SIMP_TAC[RING_ADD_LNEG; RING_ADD_RZERO]];
    REWRITE_TAC[IN_IMAGE; RIGHT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[RING_ADD]] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_ADD) THEN
    DISCH_THEN(K ALL_TAC) THEN RULE_ASSUM_TAC
     (REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[RING_ADD_RZERO]]);;

let RING_HOMOMORPHISM_IMAGE_PREIMAGE = prove
 (`!r r' (f:A->B) t.
        ring_homomorphism(r,r') f
        ==> IMAGE f {x | x IN ring_carrier r /\ f x IN t} =
            t INTER (ring_image(r,r') f)`,
  REWRITE_TAC[ring_homomorphism; ring_image] THEN SET_TAC[]);;

let RING_HOMOMORPHISM_PREIMAGE_IMAGE = prove
 (`!r r' (f:A->B) s.
        ring_homomorphism(r,r') f /\
        ring_kernel(r,r') f SUBSET s /\
        (ring_ideal r s \/ s subring_of r)
        ==> {x | x IN ring_carrier r /\ f x IN IMAGE f s} = s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    RING_HOMOMORPHISM_PREIMAGE_IMAGE_GEN o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ring_ideal; subring_of]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[RING_SETADD_RSUBSET_EQ; RING_KERNEL_NONEMPTY;
               RING_KERNEL_SUBSET_CARRIER]);;

let RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ = prove
 (`!r r' (f:A->B) t.
        ring_homomorphism(r,r') f /\ t SUBSET ring_image(r,r') f
        ==> IMAGE f {x | x IN ring_carrier r /\ f x IN t} = t`,
  SIMP_TAC[RING_HOMOMORPHISM_IMAGE_PREIMAGE] THEN SET_TAC[]);;

let RING_EPIMORPHISM_IDEAL_CORRESPONDENCE = prove
 (`!r r' (f:A->B) k.
        ring_epimorphism(r,r') f
        ==> (ring_ideal r' k <=>
             ?j. ring_ideal r j /\
                 ring_kernel(r,r') f SUBSET j /\
                 {x | x IN ring_carrier r /\ f x IN k} = j /\
                 IMAGE f j = k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_EPIMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[RING_IDEAL_EPIMORPHIC_IMAGE]] THEN
  EXISTS_TAC `{x | x IN ring_carrier r /\ (f:A->B) x IN k}` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[ring_kernel; SUBSET; IN_ELIM_THM; IN_RING_IDEAL_0];
    RULE_ASSUM_TAC(REWRITE_RULE
     [RING_EPIMORPHISM; ring_image; ring_ideal]) THEN ASM SET_TAC[]]);;

let RING_EPIMORPHISM_SUBRING_CORRESPONDENCE = prove
 (`!r r' (f:A->B) t.
        ring_epimorphism(r,r') f
        ==> (t subring_of r' <=>
             ?s. s subring_of r /\
                 ring_kernel(r,r') f SUBSET s /\
                 {x | x IN ring_carrier r /\ f x IN t} = s /\
                 IMAGE f s = t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_EPIMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SUBRING_OF_HOMOMORPHIC_IMAGE]] THEN
  EXISTS_TAC `{x | x IN ring_carrier r /\ (f:A->B) x IN t}` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC SUBRING_OF_HOMOMORPHIC_PREIMAGE THEN ASM_MESON_TAC[];
   ASM_SIMP_TAC[ring_kernel; SUBSET; IN_ELIM_THM; IN_SUBRING_0];
   RULE_ASSUM_TAC(REWRITE_RULE
    [RING_EPIMORPHISM; ring_image; subring_of]) THEN ASM SET_TAC[]]);;

let RING_EPIMORPHISM_IDEAL_CORRESPONDENCE_ALT = prove
 (`!r r' (f:A->B) j.
        ring_epimorphism(r,r') f
        ==> (ring_ideal r j /\ ring_kernel(r,r') f SUBSET j <=>
             ?k. ring_ideal r' k /\
                 {x | x IN ring_carrier r /\ f x IN k} = j /\
                 IMAGE f j = k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_EPIMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `IMAGE (f:A->B) j` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_EPIMORPHIC_IMAGE]; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `j SUBSET s /\ (!x y. x IN j /\ y IN s /\ f x = f y ==> y IN j)
      ==> {x | x IN s /\ f x IN IMAGE f j} = j`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y:A = ring_add r (ring_sub r y x) x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[ring_sub; GSYM RING_ADD_ASSOC; RING_NEG;
                   RING_ADD_LNEG; RING_ADD_RZERO];
      MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[ring_kernel; IN_ELIM_THM; RING_SUB] THEN
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUB th]) THEN
      W(MP_TAC o PART_MATCH (lhand o rand) RING_SUB_EQ_0 o snd) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `k:B->bool` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "j" THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; ring_kernel; IN_ELIM_THM] THEN
      ASM_MESON_TAC[IN_RING_IDEAL_0]]]);;

let RING_EPIMORPHISM_SUBRING_CORRESPONDENCE_ALT = prove
 (`!r r' (f:A->B) j.
        ring_epimorphism(r,r') f
        ==> (j subring_of r /\ ring_kernel(r,r') f SUBSET j <=>
             ?k. k subring_of r' /\
                 {x | x IN ring_carrier r /\ f x IN k} = j /\
                 IMAGE f j = k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_EPIMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `IMAGE (f:A->B) j` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBRING_OF_HOMOMORPHIC_IMAGE]; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `j SUBSET s /\ (!x y. x IN j /\ y IN s /\ f x = f y ==> y IN j)
      ==> {x | x IN s /\ f x IN IMAGE f j} = j`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBRING_OF_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y:A = ring_add r (ring_sub r y x) x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[ring_sub; GSYM RING_ADD_ASSOC; RING_NEG;
                   RING_ADD_LNEG; RING_ADD_RZERO];
      MATCH_MP_TAC IN_SUBRING_ADD THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[ring_kernel; IN_ELIM_THM; RING_SUB] THEN
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUB th]) THEN
      W(MP_TAC o PART_MATCH (lhand o rand) RING_SUB_EQ_0 o snd) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `k:B->bool` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "j" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBRING_OF_HOMOMORPHIC_PREIMAGE THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; ring_kernel; IN_ELIM_THM] THEN
      ASM_MESON_TAC[IN_SUBRING_0]]]);;

let RING_IDEAL_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) j.
        ring_isomorphism(r,r') f /\ j SUBSET ring_carrier r
        ==> (ring_ideal r' (IMAGE f j) <=> ring_ideal r j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC;
    ASM_MESON_TAC[RING_ISOMORPHISM_IMP_EPIMORPHISM;
                  RING_IDEAL_EPIMORPHIC_IMAGE]] THEN
  SUBGOAL_THEN
   `j = {x | x IN ring_carrier r /\ (f:A->B) x IN IMAGE f j}`
  SUBST1_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ring_isomorphism; ring_isomorphisms]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN
    ASM_MESON_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM]]);;

let RING_DIVIDES_HOMOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) x y.
        ring_homomorphism(r,r') f /\ ring_divides r x y
        ==> ring_divides r' (f x) (f y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_divides] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_MESON_TAC[]);;

let RING_ASSOCIATES_HOMOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) x y.
        ring_homomorphism(r,r') f /\ ring_associates r x y
        ==> ring_associates r' (f x) (f y)`,
  REWRITE_TAC[ring_associates] THEN
  MESON_TAC[RING_DIVIDES_HOMOMORPHIC_IMAGE]);;

let RING_UNIT_HOMOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) u.
        ring_homomorphism(r,r') f /\ ring_unit r u ==> ring_unit r' (f u)`,
  REWRITE_TAC[RING_UNIT_DIVIDES] THEN
  MESON_TAC[RING_DIVIDES_HOMOMORPHIC_IMAGE; ring_homomorphism]);;

let RING_DIVIDES_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) x y.
        ring_isomorphism(r,r') f /\ x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_divides r' (f x) (f y) <=> ring_divides r x y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN
  ASM_MESON_TAC[RING_DIVIDES_HOMOMORPHIC_IMAGE;
                RING_ISOMORPHISM_IMP_HOMOMORPHISM]);;

let RING_ASSOCIATES_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) x y.
        ring_isomorphism(r,r') f /\ x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_associates r' (f x) (f y) <=> ring_associates r x y)`,
  REWRITE_TAC[ring_associates] THEN
  MESON_TAC[RING_DIVIDES_ISOMORPHIC_IMAGE_EQ]);;

let RING_UNIT_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) u.
        ring_isomorphism(r,r') f /\ u IN ring_carrier r
        ==> (ring_unit r' (f u) <=> ring_unit r u)`,
  REWRITE_TAC[RING_UNIT_DIVIDES] THEN
  MESON_TAC[RING_DIVIDES_ISOMORPHIC_IMAGE_EQ; ring_homomorphism;
            RING_1; RING_ISOMORPHISM_IMP_HOMOMORPHISM]);;

let RING_ZERODIVISOR_MONOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) a.
        ring_monomorphism(r,r') f /\ ring_zerodivisor r a
        ==> ring_zerodivisor r' (f a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RING_MONOMORPHISM_ALT_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ring_zerodivisor] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  EXISTS_TAC `(f:A->B) b` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[ring_homomorphism]);;

let RING_ZERODIVISOR_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) a.
        ring_isomorphism(r,r') f /\ a IN ring_carrier r
        ==> (ring_zerodivisor r' (f a) <=> ring_zerodivisor r a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN
  ASM_MESON_TAC[RING_ZERODIVISOR_MONOMORPHIC_IMAGE;
                RING_ISOMORPHISM_IMP_MONOMORPHISM]);;

let RING_REGULAR_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) a.
        ring_isomorphism(r,r') f /\ a IN ring_carrier r
        ==> (ring_regular r' (f a) <=> ring_regular r a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_regular] THEN BINOP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
    REWRITE_TAC[ring_homomorphism] THEN ASM SET_TAC[];
    ASM_MESON_TAC[RING_ZERODIVISOR_ISOMORPHIC_IMAGE_EQ]]);;

let ISOMORPHIC_RING_INTEGRAL_DOMAINNESS = prove
 (`!(r:A ring) (r':B ring).
         r isomorphic_ring r' ==> (integral_domain r <=> integral_domain r')`,
  let lemma = prove
   (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> integral_domain r ==> integral_domain r'`,
    REPEAT GEN_TAC THEN REWRITE_TAC[integral_domain; GSYM TRIVIAL_RING_10] THEN
    DISCH_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ISOMORPHIC_RING_TRIVIALITY]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `f:A->B` o REWRITE_RULE[isomorphic_ring]) THEN
    SUBGOAL_THEN `ring_carrier r' = IMAGE (f:A->B) (ring_carrier r)`
    SUBST1_TAC THENL [ASM_MESON_TAC[RING_ISOMORPHISM]; ALL_TAC] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_MONOMORPHISM) THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_ALT_EQ; ring_homomorphism;
                 SUBSET; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[RING_MUL]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  ASM_REWRITE_TAC[]);;

let INTEGRAL_DOMAIN_MONOMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f /\ integral_domain r' ==> integral_domain r`,
  MATCH_MP_TAC SUBRING_IMP_MONOMORPHIC_PROPERTY THEN
  REWRITE_TAC[INTEGRAL_DOMAIN_SUBRING_GENERATED] THEN
  REWRITE_TAC[ISOMORPHIC_RING_INTEGRAL_DOMAINNESS]);;

let FIELD_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
      ring_epimorphism(r,r') f /\ field r /\ ~(trivial_ring r') ==> field r'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FIELD_EQ_ALL_UNITS; GSYM TRIVIAL_RING_10] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_ASSUM
   (SUBST1_TAC o SYM o CONJUNCT2 o REWRITE_RULE[ring_epimorphism]) THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RING_UNIT_HOMOMORPHIC_IMAGE THEN EXISTS_TAC `r:A ring` THEN
  ASM_SIMP_TAC[RING_EPIMORPHISM_IMP_HOMOMORPHISM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_0; RING_EPIMORPHISM_IMP_HOMOMORPHISM]);;

let ISOMORPHIC_RING_FIELDNESS = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> (field r <=> field r')`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `~(trivial_ring(r:A ring)) /\ ~(trivial_ring(r':B ring))` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [isomorphic_ring]);
    ASM_MESON_TAC[ISOMORPHIC_RING_TRIVIALITY; FIELD_IMP_NONTRIVIAL_RING]] THEN
  REWRITE_TAC[ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[FIELD_EPIMORPHIC_IMAGE; RING_ISOMORPHISM_IMP_EPIMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* Direct products of rings, binary and general.                             *)
(* ------------------------------------------------------------------------- *)

let prod_ring = new_definition
 `prod_ring (r:A ring) (r':B ring) =
        ring((ring_carrier r) CROSS (ring_carrier r'),
              (ring_0 r,ring_0 r'),
              (ring_1 r,ring_1 r'),
              (\(x,x'). ring_neg r x,ring_neg r' x'),
              (\(x,x') (y,y'). ring_add r x y,ring_add r' x' y'),
              (\(x,x') (y,y'). ring_mul r x y,ring_mul r' x' y'))`;;

let PROD_RING = prove
 (`(!(r:A ring) (r':B ring).
        ring_carrier (prod_ring r r') =
        (ring_carrier r) CROSS (ring_carrier r')) /\
   (!(r:A ring) (r':B ring).
        ring_0 (prod_ring r r') = (ring_0 r,ring_0 r')) /\
   (!(r:A ring) (r':B ring).
        ring_1 (prod_ring r r') = (ring_1 r,ring_1 r')) /\
   (!(r:A ring) (r':B ring).
        ring_neg (prod_ring r r') =
          \(x,x'). ring_neg r x,ring_neg r' x') /\
   (!(r:A ring) (r':B ring).
        ring_add (prod_ring r r') =
          \(x,x') (y,y'). ring_add r x y,ring_add r' x' y') /\
   (!(r:A ring) (r':B ring).
        ring_mul (prod_ring r r') =
          \(x,x') (y,y'). ring_mul r x y,ring_mul r' x' y')`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl prod_ring)))))
   (CONJUNCT2 ring_tybij)))) THEN
  REWRITE_TAC[GSYM prod_ring] THEN ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    SIMP_TAC[RING_ADD_LDISTRIB; RING_ADD_LZERO; RING_ADD_LNEG; RING_MUL_LID;
             RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
    SIMP_TAC[RING_MUL_AC; RING_ADD_AC; RING_ADD; RING_MUL];
    DISCH_TAC THEN
    ASM_REWRITE_TAC[ring_carrier; ring_0; ring_1; ring_neg;
                    ring_add; ring_mul]]);;

let RING_HOMOMORPHISM_PAIRWISE = prove
 (`!(f:A->B#C) r r' K.
        ring_homomorphism(r,prod_ring r' K) f <=>
        ring_homomorphism(r,r') (FST o f) /\
        ring_homomorphism(r,K) (SND o f)`,
  REWRITE_TAC[ring_homomorphism; PROD_RING] THEN
  REWRITE_TAC[FORALL_PAIR_FUN_THM; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF; IN_CROSS; PAIR_EQ] THEN MESON_TAC[]);;

let RING_HOMOMORPHISM_PAIRED = prove
 (`!(f:A->B) (g:A->C) r r' K.
        ring_homomorphism(r,prod_ring r' K) (\x. f x,g x) <=>
        ring_homomorphism(r,r') f /\
        ring_homomorphism(r,K) g`,
  REWRITE_TAC[RING_HOMOMORPHISM_PAIRWISE; o_DEF; ETA_AX]);;

let RING_HOMOMORPHISM_DIAG = prove
 (`!r:A ring.
        ring_homomorphism(r,prod_ring r r) (\x. x,x)`,
  REWRITE_TAC[RING_HOMOMORPHISM_PAIRED; RING_HOMOMORPHISM_ID]);;

let RING_MONOMORPHISM_DIAG = prove
 (`!r:A ring.
        ring_monomorphism(r,prod_ring r r) (\x. x,x)`,
  REWRITE_TAC[ring_monomorphism; RING_HOMOMORPHISM_DIAG] THEN
  SIMP_TAC[PAIR_EQ]);;

let RING_HOMOMORPHISM_PAIRED2 = prove
 (`!(f:A->B) (g:C->D) r r' r'' r'''.
        ring_homomorphism(prod_ring r r'',prod_ring r' r''')
                (\(x,y). f x,g y) <=>
        ring_homomorphism(r,r') f /\ ring_homomorphism(r'',r''') g`,
  REWRITE_TAC[ring_homomorphism; PROD_RING; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[PROD_RING; FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
  MESON_TAC[RING_0]);;

let RING_ISOMORPHISMS_PAIRED2 = prove
 (`!(f:A->B) (g:C->D) f' g' r r' r'' r'''.
        ring_isomorphisms(prod_ring r r'',prod_ring r' r''')
                ((\(x,y). f x,g y),(\(x,y). f' x,g' y)) <=>
        ring_isomorphisms(r,r') (f,f') /\
        ring_isomorphisms(r'',r''') (g,g')`,
  REWRITE_TAC[ring_isomorphisms; RING_HOMOMORPHISM_PAIRED2] THEN
  REWRITE_TAC[PROD_RING; FORALL_IN_CROSS; PAIR_EQ] THEN
  MESON_TAC[RING_0]);;

let RING_ISOMORPHISM_PAIRED2 = prove
 (`!(f:A->B) (g:C->D) r r' r'' r'''.
        ring_isomorphism(prod_ring r r'',prod_ring r' r''')
                (\(x,y). f x,g y) <=>
        ring_isomorphism(r,r') f /\ ring_isomorphism(r'',r''') g`,
  REWRITE_TAC[RING_ISOMORPHISM; RING_HOMOMORPHISM_PAIRED2] THEN
  REWRITE_TAC[PROD_RING; FORALL_PAIR_THM; IN_CROSS; IMAGE_PAIRED_CROSS] THEN
  REWRITE_TAC[CROSS_EQ; IMAGE_EQ_EMPTY; RING_CARRIER_NONEMPTY; PAIR_EQ] THEN
  MESON_TAC[RING_0]);;

let ISOMORPHIC_RING_PROD_RINGS = prove
 (`!(r:A ring) (r':B ring) (s:C ring) (s':D ring).
        r isomorphic_ring r' /\ s isomorphic_ring s'
        ==> (prod_ring r s) isomorphic_ring (prod_ring r' s')`,
  REWRITE_TAC[isomorphic_ring; ring_isomorphism; RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM RING_ISOMORPHISMS_PAIRED2] THEN MESON_TAC[]);;

let RING_HOMOMORPHISM_OF_FST = prove
 (`!(f:A->C) A (B:B ring) C.
        ring_homomorphism (prod_ring A B,C) (f o FST) <=>
        ring_homomorphism (A,C) f`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE; PROD_RING] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; o_DEF] THEN MESON_TAC[RING_0]);;

let RING_HOMOMORPHISM_OF_SND = prove
 (`!(f:B->C) (A:A ring) B C.
        ring_homomorphism (prod_ring A B,C) (f o SND) <=>
        ring_homomorphism (B,C) f`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE; PROD_RING] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; o_DEF] THEN MESON_TAC[RING_0]);;

let RING_EPIMORPHISM_OF_FST = prove
 (`!(f:A->C) A (B:B ring) C.
        ring_epimorphism (prod_ring A B,C) (f o FST) <=>
        ring_epimorphism (A,C) f`,
  REWRITE_TAC[ring_epimorphism; RING_HOMOMORPHISM_OF_FST] THEN
  REWRITE_TAC[PROD_RING; IMAGE_o; IMAGE_FST_CROSS; RING_CARRIER_NONEMPTY]);;

let RING_EPIMORPHISM_OF_SND = prove
 (`!(f:B->C) A (B:B ring) C.
        ring_epimorphism (prod_ring A B,C) (f o SND) <=>
        ring_epimorphism (B,C) f`,
  REWRITE_TAC[ring_epimorphism; RING_HOMOMORPHISM_OF_SND] THEN
  REWRITE_TAC[PROD_RING; IMAGE_o; IMAGE_SND_CROSS; RING_CARRIER_NONEMPTY]);;

let RING_HOMOMORPHISM_FST = prove
 (`!(A:A ring) (B:B ring). ring_homomorphism (prod_ring A B,A) FST`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE; PROD_RING] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; o_DEF] THEN MESON_TAC[RING_0]);;

let RING_HOMOMORPHISM_SND = prove
 (`!(A:A ring) (B:B ring). ring_homomorphism (prod_ring A B,B) SND`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE; PROD_RING] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; o_DEF] THEN MESON_TAC[RING_0]);;

let RING_EPIMORPHISM_FST = prove
 (`!(A:A ring) (B:B ring). ring_epimorphism (prod_ring A B,A) FST`,
  REWRITE_TAC[ring_epimorphism; RING_HOMOMORPHISM_FST] THEN
  REWRITE_TAC[PROD_RING; IMAGE_o; IMAGE_FST_CROSS; RING_CARRIER_NONEMPTY]);;

let RING_EPIMORPHISM_SND = prove
 (`!(A:A ring) (B:B ring). ring_epimorphism (prod_ring A B,B) SND`,
  REWRITE_TAC[ring_epimorphism; RING_HOMOMORPHISM_SND] THEN
  REWRITE_TAC[PROD_RING; IMAGE_o; IMAGE_SND_CROSS; RING_CARRIER_NONEMPTY]);;

let RING_ISOMORPHISM_FST = prove
 (`!(G:A ring) (H:B ring).
        ring_isomorphism (prod_ring G H,G) FST <=> trivial_ring H`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[RING_EPIMORPHISM_FST] THEN
  REWRITE_TAC[ring_monomorphism; RING_HOMOMORPHISM_FST] THEN
  SIMP_TAC[FORALL_PAIR_THM; PROD_RING; IN_CROSS; PAIR_EQ] THEN
  REWRITE_TAC[TRIVIAL_RING_ALT] THEN
  MP_TAC(ISPEC `G:A ring` RING_CARRIER_NONEMPTY) THEN SET_TAC[]);;

let RING_ISOMORPHISM_SND = prove
 (`!(G:A ring) (H:B ring).
        ring_isomorphism (prod_ring G H,H) SND <=> trivial_ring G`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[RING_EPIMORPHISM_SND] THEN
  REWRITE_TAC[ring_monomorphism; RING_HOMOMORPHISM_SND] THEN
  SIMP_TAC[FORALL_PAIR_THM; PROD_RING; IN_CROSS; PAIR_EQ] THEN
  REWRITE_TAC[TRIVIAL_RING_ALT] THEN
  MP_TAC(ISPEC `H:B ring` RING_CARRIER_NONEMPTY) THEN SET_TAC[]);;

let RING_ISOMORPHISMS_PROD_RING_SWAP = prove
 (`!(r:A ring) (r':B ring).
        ring_isomorphisms (prod_ring r r',prod_ring r' r)
                           ((\(x,y). y,x),(\(y,x). x,y))`,
  REWRITE_TAC[ring_isomorphisms; FORALL_PAIR_THM] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_PAIRWISE; o_DEF; LAMBDA_PAIR] THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] RING_HOMOMORPHISM_OF_FST;
              REWRITE_RULE[o_DEF] RING_HOMOMORPHISM_OF_SND] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_ID]);;

let ISOMORPHIC_RING_PROD_RING_SYM = prove
 (`!(r:A ring) (r':B ring).
        prod_ring r r' isomorphic_ring prod_ring r' r`,
  REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  MESON_TAC[RING_ISOMORPHISMS_PROD_RING_SWAP]);;

let ISOMORPHIC_RING_PROD_RING_SWAP_LEFT = prove
 (`!(r:A ring) (r':B ring) (K:C ring).
        prod_ring r r' isomorphic_ring K <=>
        prod_ring r' r isomorphic_ring K`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ISOMORPHIC_RING_TRANS) THEN
  REWRITE_TAC[ISOMORPHIC_RING_PROD_RING_SYM]);;

let ISOMORPHIC_RING_PROD_RING_SWAP_RIGHT = prove
 (`!(r:A ring) (r':B ring) (K:C ring).
        r isomorphic_ring prod_ring r' K <=>
        r isomorphic_ring prod_ring K r'`,
  ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  REWRITE_TAC[ISOMORPHIC_RING_PROD_RING_SWAP_LEFT]);;

let ISOMORPHIC_PROD_TRIVIAL_RING = prove
 (`(!(G:A ring) (H:B ring).
        trivial_ring G ==> (prod_ring G H isomorphic_ring H)) /\
   (!(G:A ring) (H:B ring).
        trivial_ring H ==> (prod_ring G H isomorphic_ring G)) /\
   (!(G:A ring) (H:B ring).
        trivial_ring G ==> (H isomorphic_ring prod_ring G H)) /\
   (!(G:A ring) (H:B ring).
        trivial_ring H ==> (G isomorphic_ring prod_ring G H))`,
  let lemma = prove
   (`!(G:A ring) (H:B ring).
        trivial_ring G ==> (prod_ring G H isomorphic_ring H)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_ring] THEN
    EXISTS_TAC `SND:A#B->B` THEN ASM_REWRITE_TAC[RING_ISOMORPHISM_SND]) in
  GEN_REWRITE_TAC I [CONJ_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ISOMORPHIC_RING_SYM] THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [ISOMORPHIC_RING_PROD_RING_SWAP_LEFT] THEN
  REWRITE_TAC[lemma]);;

let TRIVIAL_PROD_RING = prove
 (`!(r:A ring) (r':B ring).
        trivial_ring(prod_ring r r') <=>
        trivial_ring r /\ trivial_ring r'`,
  REWRITE_TAC[TRIVIAL_RING_SUBSET; PROD_RING; GSYM CROSS_SING] THEN
  REWRITE_TAC[SUBSET_CROSS; RING_CARRIER_NONEMPTY]);;

let FINITE_PROD_RING = prove
 (`!(r:A ring) (r':B ring).
        FINITE(ring_carrier(prod_ring r r')) <=>
        FINITE(ring_carrier r) /\ FINITE(ring_carrier r')`,
  REWRITE_TAC[PROD_RING; FINITE_CROSS_EQ; RING_CARRIER_NONEMPTY]);;

let CROSS_SUBRING_OF_PROD_RING = prove
 (`!(r1:A ring) (r2:B ring) s1 s2.
        (s1 CROSS s2) subring_of (prod_ring r1 r2) <=>
        s1 subring_of r1 /\ s2 subring_of r2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[subring_of; FORALL_PAIR_THM; PROD_RING; IN_CROSS] THEN
  REWRITE_TAC[SUBSET_CROSS] THEN SET_TAC[]);;

let PROD_RING_SUBRING_GENERATED = prove
 (`!(r1:A ring) (r2:B ring) s1 s2.
        s1 subring_of r1 /\ s2 subring_of r2
        ==> (prod_ring (subring_generated r1 s1) (subring_generated r2 s2) =
             subring_generated (prod_ring r1 r2) (s1 CROSS s2))`,
  SIMP_TAC[RINGS_EQ; CONJUNCT2 PROD_RING; CONJUNCT2 SUBRING_GENERATED] THEN
  SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING;
           CROSS_SUBRING_OF_PROD_RING; PROD_RING]);;

let RING_IDEAL_CROSS = prove
 (`!(r1:A ring) (r2:B ring) s1 s2.
        ring_ideal (prod_ring r1 r2) (s1 CROSS s2) <=>
        ring_ideal r1 s1 /\ ring_ideal r2 s2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ring_ideal; FORALL_PAIR_THM; PROD_RING; IN_CROSS] THEN
  REWRITE_TAC[SUBSET_CROSS] THEN SET_TAC[]);;

let RING_IDEAL_PROD_RING = prove
 (`!r1 r2 (k:A#B->bool).
        ring_ideal (prod_ring r1 r2) k <=>
        ?j1 j2. ring_ideal r1 j1 /\ ring_ideal r2 j2 /\
                j1 CROSS j2 = k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  EQ_TAC THENL [DISCH_TAC; MESON_TAC[RING_IDEAL_CROSS]] THEN
  EXISTS_TAC `IMAGE FST (k:A#B->bool)` THEN
  EXISTS_TAC `IMAGE SND (k:A#B->bool)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_EPIMORPHIC_IMAGE; RING_EPIMORPHISM_FST;
                  RING_EPIMORPHISM_SND];
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_PAIR_THM; UNWIND_THM1; RIGHT_EXISTS_AND_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:B`] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `y:B`) (X_CHOOSE_TAC `x:A`)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_ideal]) THEN
  REWRITE_TAC[SUBSET; PROD_RING; FORALL_PAIR_THM; IN_CROSS] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(a:A),(b:B) =
    ring_add r1 (ring_mul r1 (ring_1 r1) a) (ring_mul r1 (ring_0 r1) x),
    ring_add r2 (ring_mul r2 (ring_0 r2) y) (ring_mul r2 (ring_1 r2) b)`
  SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  ASM_MESON_TAC[RING_ADD_RZERO; RING_ADD_LZERO; RING_MUL_LID; RING_MUL_RID;
                RING_MUL_LZERO; RING_MUL_RZERO; RING_0; RING_1]);;

let IDEAL_GENERATED_PAIRWISE = prove
 (`!(r1:A ring) (r2:B ring) t.
        t SUBSET ring_carrier(prod_ring r1 r2)
        ==> ideal_generated (prod_ring r1 r2) t =
             (ideal_generated r1 (IMAGE FST t)) CROSS
             (ideal_generated r2 (IMAGE SND t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r1:A ring`; `r2:B ring`;
                 `ideal_generated (prod_ring r1 r2) (t:A#B->bool)`]
        RING_IDEAL_PROD_RING) THEN
  REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`j1:A->bool`; `j2:B->bool`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[CROSS_EQ; IDEAL_GENERATED_NONEMPTY] THEN
  CONJ_TAC THEN CONV_TAC SYM_CONV THENL
   [MP_TAC(SPECL [`r1:A ring`; `r2:B ring`] RING_EPIMORPHISM_FST);
    MP_TAC(SPECL [`r1:A ring`; `r2:B ring`] RING_EPIMORPHISM_SND)] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE)) THEN
  DISCH_THEN(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ASM_REWRITE_TAC[IMAGE_FST_CROSS; IMAGE_SND_CROSS] THEN
  ASM_MESON_TAC[RING_IDEAL_IMP_NONEMPTY]);;

let IDEAL_GENERATED_CROSS = prove
 (`!(r1:A ring) (r2:B ring) s1 s2.
        s1 SUBSET ring_carrier r1 /\ s2 SUBSET ring_carrier r2
        ==> ideal_generated (prod_ring r1 r2) (s1 CROSS s2) =
            if s1 = {} \/ s2 = {} then {ring_0(prod_ring r1 r2)}
            else (ideal_generated r1 s1) CROSS (ideal_generated r2 s2)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[IDEAL_GENERATED_PAIRWISE; SUBSET_CROSS; PROD_RING] THEN
  REWRITE_TAC[PROD_RING; INTER_CROSS; IMAGE_FST_CROSS; IMAGE_SND_CROSS] THEN
  MAP_EVERY ASM_CASES_TAC [`s1:A->bool = {}`; `s2:B->bool = {}`] THEN
  ASM_REWRITE_TAC[IDEAL_GENERATED_EMPTY; CROSS_SING]);;

let RING_POW_PROD_RING = prove
 (`!r1 r2 (a:A) (b:B) n.
        ring_pow (prod_ring r1 r2) (a,b) n =
        (ring_pow r1 a n,ring_pow r2 b n)`,
  REPLICATE_TAC 4 GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; PROD_RING]);;

let RING_DIVIDES_PROD_RING = prove
 (`!r1 r2 (a:A) (b:B) c d.
        ring_divides (prod_ring r1 r2) (a,b) (c,d) <=>
        ring_divides r1 a c /\ ring_divides r2 b d`,
  REWRITE_TAC[ring_divides; EXISTS_PAIR_THM; PROD_RING; IN_CROSS; PAIR_EQ] THEN
  MESON_TAC[]);;

let RING_ASSOCIATES_PROD_RING = prove
 (`!r1 r2 (a:A) (b:B) c d.
        ring_associates (prod_ring r1 r2) (a,b) (c,d) <=>
        ring_associates r1 a c /\ ring_associates r2 b d`,
  REWRITE_TAC[ring_associates; RING_DIVIDES_PROD_RING] THEN MESON_TAC[]);;

let RING_ZERODIVISOR_PROD_RING = prove
 (`!r1 r2 (a:A) (b:B).
        ring_zerodivisor (prod_ring r1 r2) (a,b) <=>
        ring_zerodivisor r1 a /\ b IN ring_carrier r2 \/
        a IN ring_carrier r1 /\ ring_zerodivisor r2 b`,
  REWRITE_TAC[ring_zerodivisor; EXISTS_PAIR_THM; PROD_RING;
              IN_CROSS; PAIR_EQ] THEN
  MESON_TAC[RING_0; RING_MUL_RZERO]);;

let RING_REGULAR_PROD_RING = prove
 (`!r1 r2 (a:A) (b:B).
        ring_regular (prod_ring r1 r2) (a,b) <=>
        ring_regular r1 a /\ ring_regular r2 b`,
  REWRITE_TAC[ring_regular; PROD_RING; IN_CROSS;
              RING_ZERODIVISOR_PROD_RING] THEN
  MESON_TAC[]);;

let RING_NILPOTENT_PROD_RING = prove
 (`!r1 r2 (a:A) (b:B).
        ring_nilpotent (prod_ring r1 r2) (a,b) <=>
        ring_nilpotent r1 a /\ ring_nilpotent r2 b`,
  REWRITE_TAC[ring_nilpotent; EXISTS_PAIR_THM; PROD_RING;
              IN_CROSS; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(b:B) IN ring_carrier r2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RING_POW_PROD_RING; PAIR_EQ] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `m + n:num` THEN
  ASM_SIMP_TAC[RING_POW_ADD; ADD_EQ_0; RING_MUL_LZERO; RING_MUL_RZERO;
               RING_POW]);;

let product_ring = new_definition
 `product_ring k (r:K->A ring) =
        ring(cartesian_product k (\i. ring_carrier(r i)),
              RESTRICTION k (\i. ring_0 (r i)),
              RESTRICTION k (\i. ring_1 (r i)),
              (\x. RESTRICTION k (\i. ring_neg (r i) (x i))),
              (\x y. RESTRICTION k (\i. ring_add (r i) (x i) (y i))),
              (\x y. RESTRICTION k (\i. ring_mul (r i) (x i) (y i))))`;;

let PRODUCT_RING = prove
 (`(!k (r:K->A ring).
        ring_carrier(product_ring k r) =
          cartesian_product k (\i. ring_carrier(r i))) /\
   (!k (r:K->A ring).
        ring_0 (product_ring k r) =
          RESTRICTION k (\i. ring_0 (r i))) /\
   (!k (r:K->A ring).
        ring_1 (product_ring k r) =
          RESTRICTION k (\i. ring_1 (r i))) /\
   (!k (r:K->A ring).
        ring_neg (product_ring k r) =
          \x. RESTRICTION k (\i. ring_neg (r i) (x i))) /\
   (!k (r:K->A ring).
        ring_add (product_ring k r) =
          (\x y. RESTRICTION k (\i. ring_add (r i) (x i) (y i)))) /\
   (!k (r:K->A ring).
        ring_mul (product_ring k r) =
          (\x y. RESTRICTION k (\i. ring_mul (r i) (x i) (y i))))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl product_ring)))))
   (CONJUNCT2 ring_tybij)))) THEN
  REWRITE_TAC[GSYM product_ring] THEN ANTS_TAC THENL
   [REWRITE_TAC[cartesian_product; RESTRICTION; EXTENSIONAL; IN_ELIM_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_SIMP_TAC[RING_ADD_LDISTRIB; RING_ADD_LZERO; RING_ADD_LNEG;
      RING_MUL_LID; RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
    ASM_SIMP_TAC[RING_MUL_AC; RING_ADD_AC; RING_ADD; RING_MUL];
    DISCH_TAC THEN
    ASM_REWRITE_TAC[ring_carrier; ring_0; ring_1;
                    ring_neg; ring_add; ring_mul]]);;

let TRIVIAL_PRODUCT_RING = prove
 (`!k (r:K->A ring).
        trivial_ring(product_ring k r) <=>
        !i. i IN k ==> trivial_ring(r i)`,
  REWRITE_TAC[TRIVIAL_RING_SUBSET; PRODUCT_RING] THEN
  REWRITE_TAC[GSYM CARTESIAN_PRODUCT_SINGS_GEN] THEN
  REWRITE_TAC[SUBSET_CARTESIAN_PRODUCT] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_EQ_EMPTY; RING_CARRIER_NONEMPTY]);;

let ISOMORPHIC_RING_PRODUCT_RING = prove
 (`!(r:K->A ring) (r':K->B ring) k.
        (!i. i IN k ==> (r i) isomorphic_ring (r' i))
        ==> (product_ring k r) isomorphic_ring (product_ring k r')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; ring_isomorphisms] THEN
  MAP_EVERY X_GEN_TAC [`f:K->A->B`; `g:K->B->A`] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x. RESTRICTION k (\i. (f:K->A->B) i (x i))`;
    `\y. RESTRICTION k (\i. (g:K->B->A) i (y i))`] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [REWRITE_TAC[RING_HOMOMORPHISM; PRODUCT_RING;
                cartesian_product; IN_ELIM_THM; EXTENSIONAL;
                SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN SIMP_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [RING_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[PRODUCT_RING; IN_CARTESIAN_PRODUCT; FUN_EQ_THM] THEN
    ASM_SIMP_TAC[RESTRICTION; EXTENSIONAL] THEN SET_TAC[]]);;

let RING_HOMOMORPHISM_COMPONENTWISE = prove
 (`!r k s (f:A->K->B).
        ring_homomorphism(r,product_ring k s) f <=>
        IMAGE f (ring_carrier r) SUBSET EXTENSIONAL k /\
        !i. i IN k ==> ring_homomorphism (r,s i) (\x. f x i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[PRODUCT_RING; IN_CARTESIAN_PRODUCT] THEN
  REWRITE_TAC[RESTRICTION_UNIQUE_ALT] THEN
  REWRITE_TAC[SET_RULE `f IN EXTENSIONAL s <=> EXTENSIONAL s f`] THEN
  ASM_CASES_TAC
   `!x. x IN ring_carrier r ==> EXTENSIONAL k ((f:A->K->B) x)`
  THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
  MESON_TAC[]);;

let RING_HOMOMORPHISM_COMPONENTWISE_UNIV = prove
 (`!r s (f:A->K->B).
        ring_homomorphism(r,product_ring (:K) s) f <=>
        !i. ring_homomorphism (r,s i) (\x. f x i)`,
  REWRITE_TAC[RING_HOMOMORPHISM_COMPONENTWISE; IN_UNIV] THEN
  REWRITE_TAC[SET_RULE `s SUBSET P <=> !x. x IN s ==> P x`] THEN
  REWRITE_TAC[EXTENSIONAL_UNIV]);;

let RING_PRODUCT_INJECTION = prove
 (`!k (r:K->A ring) a i.
        RESTRICTION k (\j. if j = i then a else ring_0 (r j)) IN
        ring_carrier(product_ring k r) <=>
        i IN k ==> a IN ring_carrier(r i)`,
  SIMP_TAC[PRODUCT_RING; RESTRICTION_IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
  MESON_TAC[RING_0]);;

let RING_HOMOMORPHISM_DIAGONAL = prove
 (`!(k:K->bool) (r:A ring).
     ring_homomorphism (r,product_ring k (\i. r)) (\x. RESTRICTION k (\i. x))`,
  REWRITE_TAC[RING_HOMOMORPHISM_COMPONENTWISE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION; RING_HOMOMORPHISM_ID]);;

let RING_HOMOMORPHISM_DIAGONAL_UNIV = prove
 (`!(r:A ring).
        ring_homomorphism (r,product_ring (:K) (\i. r)) (\x i. x)`,
  REWRITE_TAC[RING_HOMOMORPHISM_COMPONENTWISE_UNIV] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_ID]);;

let RING_MONOMORPHISM_DIAGONAL = prove
 (`!(k:K->bool) (r:A ring).
     ring_monomorphism (r,product_ring k (\i. r))
                       (\x. RESTRICTION k (\i. x)) <=>
     k = {} ==> trivial_ring r`,
  REWRITE_TAC[ring_monomorphism; RING_HOMOMORPHISM_DIAGONAL] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[RESTRICTION_EXTENSION] THEN
  ASM_CASES_TAC `k:K->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY]; ASM SET_TAC[]] THEN
  REWRITE_TAC[TRIVIAL_RING_ALT] THEN SET_TAC[]);;

let RING_MONOMORPHISM_DIAGONAL_UNIV = prove
 (`!(r:A ring).
        ring_monomorphism (r,product_ring (:K) (\i. r)) (\x i. x)`,
  REWRITE_TAC[ring_monomorphism; RING_HOMOMORPHISM_DIAGONAL_UNIV] THEN
  REWRITE_TAC[RESTRICTION_EXTENSION] THEN SET_TAC[]);;

let RING_HOMOMORPHISM_PRODUCT_PROJECTION = prove
 (`!(r:K->A ring) k i.
        i IN k ==> ring_homomorphism (product_ring k r,r i) (\x. x i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`product_ring k (r:K->A ring)`; `k:K->bool`; `r:K->A ring`;
                 `\x:K->A. x`]
        RING_HOMOMORPHISM_COMPONENTWISE) THEN
  REWRITE_TAC[RING_HOMOMORPHISM_ID] THEN
 ASM_SIMP_TAC[RING_HOMOMORPHISM_COMPONENTWISE]);;

let RING_EPIMORPHISM_PRODUCT_PROJECTION = prove
 (`!(r:K->A ring) k i.
        i IN k ==> ring_epimorphism (product_ring k r,r i) (\x. x i)`,
  SIMP_TAC[ring_epimorphism; RING_HOMOMORPHISM_PRODUCT_PROJECTION] THEN
  SIMP_TAC[IMAGE_PROJECTION_CARTESIAN_PRODUCT; PRODUCT_RING;
           CARTESIAN_PRODUCT_EQ_EMPTY; RING_CARRIER_NONEMPTY]);;

let RING_ISOMORPHISM_PRODUCT_PROJECTION = prove
 (`!r k. ring_isomorphism (product_ring {k} r,r k) (\x. x k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RING_ISOMORPHISM_EPIMORPHISM] THEN
  SIMP_TAC[RING_EPIMORPHISM_PRODUCT_PROJECTION; IN_SING] THEN
  REWRITE_TAC[PRODUCT_RING; CARTESIAN_PRODUCT_AS_RESTRICTIONS] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[RESTRICTION_EXTENSION; RESTRICTION; IN_SING] THEN MESON_TAC[]);;

let CARTESIAN_PRODUCT_SUBRING_OF_PRODUCT_RING = prove
 (`!k h r:K->A ring.
        (cartesian_product k h) subring_of (product_ring k r) <=>
        !i. i IN k ==> (h i) subring_of (r i)`,
  REWRITE_TAC[subring_of; PRODUCT_RING; RESTRICTION_IN_CARTESIAN_PRODUCT;
              SUBSET_CARTESIAN_PRODUCT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_CASES_TAC `cartesian_product k (h:K->A->bool) = {}` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
    SET_TAC[];
    ASM_REWRITE_TAC[REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
          FORALL_CARTESIAN_PRODUCT_ELEMENTS] THEN
    MESON_TAC[]]);;

let PRODUCT_RING_SUBRING_GENERATED = prove
 (`!k r (h:K->A->bool).
        (!i. i IN k ==> (h i) subring_of (r i))
        ==> product_ring k (\i. subring_generated (r i) (h i)) =
            subring_generated (product_ring k r) (cartesian_product k h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RINGS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 PRODUCT_RING; CONJUNCT2 SUBRING_GENERATED] THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; PRODUCT_RING;
               CARTESIAN_PRODUCT_SUBRING_OF_PRODUCT_RING] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_EQ] THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING]);;

let FINITE_PRODUCT_RING = prove
 (`!k (r:K->A ring).
        FINITE(ring_carrier(product_ring k r)) <=>
        FINITE {i | i IN k /\ ~trivial_ring(r i)} /\
        !i. i IN k ==> FINITE(ring_carrier(r i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PRODUCT_RING] THEN
  REWRITE_TAC[FINITE_CARTESIAN_PRODUCT; CARTESIAN_PRODUCT_EQ_EMPTY] THEN
  REWRITE_TAC[TRIVIAL_RING_ALT; RING_CARRIER_NONEMPTY]);;

let RING_IDEAL_CARTESIAN_PRODUCT = prove
 (`!k h r:K->A ring.
        ring_ideal (product_ring k r) (cartesian_product k h) <=>
        !i. i IN k ==> ring_ideal (r i) (h i)`,
  REWRITE_TAC[ring_ideal; PRODUCT_RING; RESTRICTION_IN_CARTESIAN_PRODUCT;
              SUBSET_CARTESIAN_PRODUCT] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_CASES_TAC `cartesian_product k (h:K->A->bool) = {}` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
    SET_TAC[];
    ASM_REWRITE_TAC[REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
          FORALL_CARTESIAN_PRODUCT_ELEMENTS] THEN
    REWRITE_TAC[CARTESIAN_PRODUCT_EQ_EMPTY; RING_CARRIER_NONEMPTY] THEN
    MESON_TAC[]]);;

let RING_SUM_PRODUCT_RING = prove
 (`!k r t (f:L->K->A).
        FINITE t /\
        (!a. a IN t ==> (f a) IN ring_carrier(product_ring k r))
        ==> ring_sum (product_ring k r) t f =
            RESTRICTION k (\i. ring_sum (r i) t (\a. f a i))`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; FORALL_IN_INSERT] THEN
  SIMP_TAC[PRODUCT_RING; IN_CARTESIAN_PRODUCT; RESTRICTION_EXTENSION] THEN
  SIMP_TAC[RESTRICTION]);;

let RING_IDEAL_PRODUCT_RING = prove
 (`!(r:K->A ring) k t.
        FINITE {i | i IN k /\ ~trivial_ring(r i)}
        ==> (ring_ideal (product_ring k r) t <=>
             ?j. (!i. i IN k ==> ring_ideal (r i) (j i)) /\
                 cartesian_product k j = t)`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[RING_IDEAL_CARTESIAN_PRODUCT]] THEN
  DISCH_TAC THEN
  EXISTS_TAC `\i. IMAGE (\x. x i) (t:(K->A)->bool)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_IDEAL_EPIMORPHIC_IMAGE THEN
    ASM_MESON_TAC[RING_EPIMORPHISM_PRODUCT_PROJECTION];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:K->A` THEN
  REWRITE_TAC[IN_CARTESIAN_PRODUCT] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC);
    DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
    REWRITE_TAC[SUBSET; PRODUCT_RING; IN_CARTESIAN_PRODUCT] THEN
    DISCH_THEN(MP_TAC o SPEC `f:K->A`) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]] THEN
  REWRITE_TAC[IN_IMAGE; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:K->K->A` (STRIP_ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN
   `!i j. i IN k /\ j IN k ==> (g:K->K->A) i j IN ring_carrier(r j)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
    REWRITE_TAC[SUBSET; PRODUCT_RING; IN_CARTESIAN_PRODUCT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f = ring_sum (product_ring k (r:K->A ring))
                 {i | i IN k /\ ~trivial_ring(r i)}
                 (\i. ring_mul (product_ring k r) (g i)
                               (RESTRICTION k (\j. if j = i then ring_1 (r i)
                                                   else ring_0 (r j))))`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[PRODUCT_RING] THEN
    REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
    ASM_MESON_TAC[RING_0; RING_1]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_PRODUCT_RING o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `a:K` THEN DISCH_TAC THEN MATCH_MP_TAC RING_MUL THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
      ASM SET_TAC[];
      REWRITE_TAC[PRODUCT_RING; RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
      MESON_TAC[RING_0; RING_1]];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[RESTRICTION_UNIQUE_ALT] THEN
  X_GEN_TAC `a:K` THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS
   `ring_sum ((r:K->A ring) a)
             {i | i IN k /\ ~trivial_ring (r i)}
             (\i:K. if i = a then f a else ring_0(r a))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM] THEN
    ASM_CASES_TAC `trivial_ring((r:K->A ring) a)` THEN
    ASM_REWRITE_TAC[] THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[trivial_ring]) THEN ASM SET_TAC[];
      ASM_MESON_TAC[RING_MUL_RZERO]];
    MATCH_MP_TAC RING_SUM_EQ THEN
    X_GEN_TAC `b:K` THEN ASM_SIMP_TAC[PRODUCT_RING; RESTRICTION] THEN
    ASM_CASES_TAC `b:K = a` THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_MUL_RID; RING_MUL_RZERO]]);;

let IDEAL_GENERATED_COMPONENTWISE = prove
 (`!(r:K->A ring) k t.
      FINITE {i | i IN k /\ ~trivial_ring(r i)} /\
      t SUBSET ring_carrier(product_ring k r)
      ==> ideal_generated (product_ring k r) t =
          cartesian_product k (\i. ideal_generated (r i) (IMAGE (\x. x i) t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:K->A ring`; `k:K->bool`;
                 `ideal_generated (product_ring k r) (t:(K->A)->bool)`]
        RING_IDEAL_PRODUCT_RING) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `j:K->A->bool` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[CARTESIAN_PRODUCT_EQ; IDEAL_GENERATED_NONEMPTY] THEN
  DISJ2_TAC THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`r:K->A ring`; `k:K->bool`; `i:K`]
        RING_EPIMORPHISM_PRODUCT_PROJECTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE)) THEN
  DISCH_THEN(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ASM_SIMP_TAC[IMAGE_PROJECTION_CARTESIAN_PRODUCT] THEN
  ASM_REWRITE_TAC[CARTESIAN_PRODUCT_EQ_EMPTY] THEN
  ASM_MESON_TAC[IDEAL_GENERATED_NONEMPTY]);;

let IDEAL_GENERATED_CARTESIAN_PRODUCT = prove
 (`!(r:K->A ring) k s.
        FINITE {i | i IN k /\ ~trivial_ring(r i)} /\
        (!i. i IN k ==> (s i) SUBSET ring_carrier(r i))
        ==> ideal_generated (product_ring k r) (cartesian_product k s) =
            if cartesian_product k s = {} then {ring_0(product_ring k r)}
            else cartesian_product k (\i. ideal_generated (r i) (s i))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_COMPONENTWISE; PRODUCT_RING;
                SUBSET_CARTESIAN_PRODUCT] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[IMAGE_PROJECTION_CARTESIAN_PRODUCT; CARTESIAN_PRODUCT_EQ] THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; IDEAL_GENERATED_EMPTY; PRODUCT_RING] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_SINGS_GEN]);;

let RING_POW_PRODUCT_RING = prove
 (`!k (r:K->A ring) x n.
        ring_pow (product_ring k r) x n =
        RESTRICTION k (\i. ring_pow (r i) (x i) n)`,
  REPLICATE_TAC 3 GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; PRODUCT_RING] THEN
  REWRITE_TAC[RESTRICTION_EXTENSION] THEN SIMP_TAC[RESTRICTION]);;

let RING_DIVIDES_PRODUCT_RING = prove
 (`!k (r:K->A ring) x y.
        ring_divides (product_ring k r) x y <=>
        EXTENSIONAL k x /\ EXTENSIONAL k y /\
        !i. i IN k ==> ring_divides (r i) (x i) (y i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_divides; PRODUCT_RING; CONJ_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [IN_CARTESIAN_PRODUCT] THEN
  ASM_CASES_TAC `EXTENSIONAL k (x:K->A)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `EXTENSIONAL k (y:K->A)` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RESTRICTION_UNIQUE_ALT; EXISTS_CARTESIAN_PRODUCT_ELEMENT] THEN
  MESON_TAC[]);;

let RING_ASSOCIATES_PRODUCT_RING = prove
 (`!k (r:K->A ring) x y.
        ring_associates (product_ring k r) x y <=>
        EXTENSIONAL k x /\ EXTENSIONAL k y /\
        !i. i IN k ==> ring_associates (r i) (x i) (y i)`,
  REWRITE_TAC[ring_associates; RING_DIVIDES_PRODUCT_RING] THEN
  MESON_TAC[]);;

let RING_ZERODIVISOR_PRODUCT_RING = prove
 (`!k (r:K->A ring) x.
        ring_zerodivisor (product_ring k r) x <=>
        x IN ring_carrier (product_ring k r) /\
        ?i. i IN k /\ ring_zerodivisor (r i) (x i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_zerodivisor] THEN
  ASM_CASES_TAC `(x:K->A) IN ring_carrier (product_ring k r)` THEN
  ASM_REWRITE_TAC[PRODUCT_RING; RESTRICTION_EXTENSION] THEN
  REWRITE_TAC[RESTRICTION_UNIQUE_ALT] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:K->A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PRODUCT_RING; IN_CARTESIAN_PRODUCT]) THEN
    ASM SET_TAC[];
    REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `i:K` THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC `x:A` THEN REPEAT DISCH_TAC THEN EXISTS_TAC
     `RESTRICTION k (\j:K. if j = i then (x:A) else ring_0 (r j))` THEN
    REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
    REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PRODUCT_RING; IN_CARTESIAN_PRODUCT]) THEN
    ASM_SIMP_TAC[RESTRICTION] THEN
    ASM_MESON_TAC[RING_0; RING_MUL_RZERO]]);;

let RING_REGULAR_PRODUCT_RING = prove
 (`!k (r:K->A ring) x.
        ring_regular (product_ring k r) x <=>
        EXTENSIONAL k x /\
        !i. i IN k ==> ring_regular (r i) (x i)`,
  REWRITE_TAC[ring_regular; RING_ZERODIVISOR_PRODUCT_RING] THEN
  REWRITE_TAC[PRODUCT_RING; IN_CARTESIAN_PRODUCT] THEN MESON_TAC[]);;

let RING_NILPOTENT_PRODUCT_RING_GEN = prove
 (`!k (r:K->A ring) x.
        ring_nilpotent (product_ring k r) x <=>
        EXTENSIONAL k x /\
        (!i. i IN k ==> ring_nilpotent (r i) (x i)) /\
        (?n. ~(n = 0) /\ !i. i IN k ==> ring_pow (r i) (x i) n = ring_0(r i))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `!q'. (p ==> q') /\ (q' ==> q) /\ (q' /\ s ==> r) /\
         (q /\ r ==> q') /\ (p <=> q' /\ s)
         ==> (p <=> q /\ r /\ s)`) THEN
  EXISTS_TAC `(x:K->A) IN ring_carrier(product_ring k r)` THEN
  REWRITE_TAC[RING_NILPOTENT_IN_CARRIER] THEN
  SIMP_TAC[ring_nilpotent; PRODUCT_RING; IN_CARTESIAN_PRODUCT;
           RING_POW_PRODUCT_RING; RESTRICTION_EXTENSION] THEN
  MESON_TAC[]);;

let RING_NILPOTENT_PRODUCT_RING = prove
 (`!k (r:K->A ring) x.
        FINITE k
        ==> (ring_nilpotent (product_ring k r) x <=>
             EXTENSIONAL k x /\
             !i. i IN k ==> ring_nilpotent (r i) (x i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RING_NILPOTENT_PRODUCT_RING_GEN] THEN
  EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ring_nilpotent] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_AND_EXISTS_THM; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:K->num`) THEN
  MP_TAC(ISPEC `IMAGE (m:K->num) k` FINITE_SUBSET_NUMSEG) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; IN_NUMSEG; LE_0; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `SUC n` THEN
  REWRITE_TAC[NOT_SUC] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:K`)) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[ARITH_RULE `SUC(m + d) = m + SUC d`] THEN
  ASM_SIMP_TAC[RING_POW_ADD; RING_MUL_LZERO; RING_POW]);;

let ISOMORPHIC_PRODUCT_RING_DISJOINT_UNION = prove
 (`!(f:K->A ring) k l.
        DISJOINT k l
        ==> product_ring (k UNION l) f isomorphic_ring
            prod_ring (product_ring k f) (product_ring l f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  REWRITE_TAC[RING_ISOMORPHISMS] THEN
  EXISTS_TAC `\(f:K->A). RESTRICTION k f,RESTRICTION l f` THEN
  EXISTS_TAC `\((f:K->A),g) x. if x IN k then f x else g x` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[RING_HOMOMORPHISM_PAIRED;
                RING_HOMOMORPHISM_COMPONENTWISE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
    SIMP_TAC[RESTRICTION; RING_HOMOMORPHISM_PRODUCT_PROJECTION; IN_UNION];
    REWRITE_TAC[PROD_RING; FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    SIMP_TAC[RESTRICTION_UNIQUE; IN_CARTESIAN_PRODUCT; PRODUCT_RING] THEN
    REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN ASM SET_TAC[]]);;


let ISOMORPHIC_PRODUCT_RING_SING = prove
 (`!(r:K->A ring) k. product_ring {k} r isomorphic_ring r k`,
  REWRITE_TAC[isomorphic_ring] THEN
  MESON_TAC[RING_ISOMORPHISM_PRODUCT_PROJECTION]);;

let ISOMORPHIC_PRODUCT_RING_SUPPORT = prove
 (`!k (r:K->A ring).
        product_ring {i | i IN k /\ ~trivial_ring(r i)} r isomorphic_ring
        product_ring k r`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  REWRITE_TAC[isomorphic_ring; ring_isomorphism; RING_ISOMORPHISMS] THEN
  MAP_EVERY EXISTS_TAC
   [`\x:K->A. RESTRICTION {i | i IN k /\ ~trivial_ring((r:K->A ring) i)} x`;
    `\x. RESTRICTION k (\i. if trivial_ring((r:K->A ring) i)
                            then ring_0(r i) else x i)`] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_COMPONENTWISE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
  REWRITE_TAC[PRODUCT_RING; RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_CARTESIAN_PRODUCT] THEN
  REWRITE_TAC[RESTRICTION_UNIQUE] THEN SIMP_TAC[IN_ELIM_THM] THEN
  SIMP_TAC[RESTRICTION; IN_ELIM_THM; EXTENSIONAL] THEN
  SIMP_TAC[RING_HOMOMORPHISM_PRODUCT_PROJECTION] THEN
  MESON_TAC[RING_0; trivial_ring; IN_SING]);;

let ISOMORPHIC_PRODUCT_RING_SYMDIFF = prove
 (`!k l (r:K->A ring).
        (!i. i IN (k DIFF l) UNION (l DIFF k) ==> trivial_ring(r i))
        ==> product_ring k r isomorphic_ring product_ring l r`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH rand ISOMORPHIC_PRODUCT_RING_SUPPORT o
    lhand o snd) THEN
  GEN_REWRITE_TAC LAND_CONV [ISOMORPHIC_RING_SYM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] ISOMORPHIC_RING_TRANS) THEN
  W(MP_TAC o PART_MATCH rand ISOMORPHIC_PRODUCT_RING_SUPPORT o
    rand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ISOMORPHIC_RING_TRANS) THEN
  MATCH_MP_TAC(MESON[ISOMORPHIC_RING_REFL]
   `r = s ==> r isomorphic_ring s`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let ISOMORPHIC_PRODUCT_RING_BIJECTIONS = prove
 (`!s (r:K->A ring) t (r':L->B ring) f g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y) /\
        (!i. i IN s ==> (r i) isomorphic_ring r'(f i))
        ==> product_ring s r isomorphic_ring product_ring t r'`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:K->A->B`; `k:K->B->A`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [ring_isomorphisms; FORALL_AND_THM;
    TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\(x:K->A). RESTRICTION t (\j:L. (h:K->A->B) (g j) (x (g j)))`;
    `\(y:L->B). RESTRICTION s (\i:K. (k:K->B->A) i (y (f i)))`] THEN
  REWRITE_TAC[ring_isomorphisms] THEN
  REWRITE_TAC[RESTRICTION_EXTENSION; PRODUCT_RING; FORALL_IN_GSPEC;
    IMP_CONJ; CARTESIAN_PRODUCT_AS_RESTRICTIONS] THEN
  ASM_SIMP_TAC[RESTRICTION] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_COMPONENTWISE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PRODUCT_RING] THEN
  REWRITE_TAC[RESTRICTION_IN_EXTENSIONAL] THEN SIMP_TAC[RESTRICTION] THEN
  CONJ_TAC THENL [X_GEN_TAC `j:L`; X_GEN_TAC `i:K`] THEN
  DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THENL
   [EXISTS_TAC `(r:K->A ring) (g(j:L))`;
    EXISTS_TAC `(r':L->B ring) (f(i:K))`] THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_PRODUCT_PROJECTION] THEN
  ASM_MESON_TAC[]);;

let RING_ISOMORPHISMS_PRODUCT_RING_DISJOINT_UNION = prove
 (`!(f:K->A ring) k l.
        DISJOINT k l
        ==> ring_isomorphisms
                (product_ring (k UNION l) f,
                 prod_ring (product_ring k f) (product_ring l f))
                ((\f. RESTRICTION k f,RESTRICTION l f),
                 (\(f,g) x. if x IN k then f x else g x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RING_ISOMORPHISMS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[RING_HOMOMORPHISM_PAIRED;
                RING_HOMOMORPHISM_COMPONENTWISE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
    SIMP_TAC[RESTRICTION; RING_HOMOMORPHISM_PRODUCT_PROJECTION; IN_UNION];
    REWRITE_TAC[PROD_RING; FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    SIMP_TAC[RESTRICTION_UNIQUE; IN_CARTESIAN_PRODUCT; PRODUCT_RING] THEN
    REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN ASM SET_TAC[]]);;

let RING_ISOMORPHISM_PRODUCT_RING_DISJOINT_UNION = prove
 (`!(f:K->A ring) k l.
        DISJOINT k l
        ==> ring_isomorphism
                (product_ring (k UNION l) f,
                 prod_ring (product_ring k f) (product_ring l f))
                (\f. RESTRICTION k f,RESTRICTION l f)`,
  REWRITE_TAC[ring_isomorphism] THEN
  MESON_TAC[RING_ISOMORPHISMS_PRODUCT_RING_DISJOINT_UNION]);;

let ISOMORPHIC_PRODUCT_RING_INSERT = prove
 (`!(f:K->A ring) i k.
        ~(i IN k)
        ==> product_ring (i INSERT k) f isomorphic_ring
            prod_ring (f i) (product_ring k f)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC ISOMORPHIC_RING_TRANS
   `prod_ring (product_ring {i} f) (product_ring k (f:K->A ring))` THEN
  SUBST1_TAC(SET_RULE `(i:K) INSERT k = {i} UNION k`) THEN
  ASM_SIMP_TAC[ISOMORPHIC_PRODUCT_RING_DISJOINT_UNION; DISJOINT_SING] THEN
  MATCH_MP_TAC ISOMORPHIC_RING_PROD_RINGS THEN
  REWRITE_TAC[ISOMORPHIC_RING_REFL; ISOMORPHIC_PRODUCT_RING_SING]);;

(* ------------------------------------------------------------------------- *)
(* Derived rule to take a theorem asserting a monomorphism between r and r'  *)
(* and a term that is some Boolean combination of equations in the ring r    *)
(* and prove it equivalent to a "transferred" version in r' where all the    *)
(* variables x (in r) in the original map to "f x" (in r').                  *)
(* ------------------------------------------------------------------------- *)

let RING_MONOMORPHIC_IMAGE_RULE =
  let pth = prove
   (`!r r' (f:A->B).
          ring_monomorphism(r,r') f
          ==> (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> (x = y <=> x' = y')) /\
              (!x. x IN ring_carrier r
                   ==> x IN ring_carrier r /\ f x = f x) /\
              (ring_0 r IN ring_carrier r /\ f(ring_0 r) = ring_0 r') /\
              (ring_1 r IN ring_carrier r /\ f(ring_1 r) = ring_1 r') /\
              (!n. ring_of_num r n IN ring_carrier r /\
                   f(ring_of_num r n) = ring_of_num r' n) /\
              (!n. ring_of_int r n IN ring_carrier r /\
                   f(ring_of_int r n) = ring_of_int r' n) /\
              (!x x'. x IN ring_carrier r /\ f x = x'
                      ==> ring_neg r x IN ring_carrier r /\
                          f(ring_neg r x) = ring_neg r' x') /\
              (!n x x'.
                  x IN ring_carrier r /\ f x = x'
                  ==> ring_pow r x n IN ring_carrier r /\
                      f(ring_pow r x n) = ring_pow r' x' n) /\
              (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> ring_add r x y IN ring_carrier r /\
                      f(ring_add r x y) = ring_add r' x' y') /\
              (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> ring_sub r x y IN ring_carrier r /\
                      f(ring_sub r x y) = ring_sub r' x' y') /\
              (!x x' y y'.
                  (x IN ring_carrier r /\ f x = x') /\
                  (y IN ring_carrier r /\ f y = y')
                  ==> ring_mul r x y IN ring_carrier r /\
                      f(ring_mul r x y) = ring_mul r' x' y')`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ring_monomorphism] THEN
    GEN_REWRITE_TAC LAND_CONV [CONJ_SYM] THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[RING_0; RING_1; RING_OF_NUM; RING_OF_INT; RING_NEG;
              RING_POW; RING_ADD; RING_SUB; RING_MUL;
              RING_HOMOMORPHISM_0; RING_HOMOMORPHISM_1;
              RING_HOMOMORPHISM_RING_OF_NUM; RING_HOMOMORPHISM_RING_OF_INT;
              RING_HOMOMORPHISM_NEG; RING_HOMOMORPHISM_POW;
              RING_HOMOMORPHISM_ADD; RING_HOMOMORPHISM_SUB;
              RING_HOMOMORPHISM_MUL]) in
  fun hth ->
    let [pth_eq; pth_asm;
         pth_0; pth_1; pth_num; pth_int;
         pth_neg; pth_pow;
         pth_add; pth_sub],pth_mul =
      splitlist CONJ_PAIR (MATCH_MP pth hth)
    and htm = rand(concl hth) in
    let rec mterm tm =
      match tm with
        Comb(Const("ring_0",_),_) ->
          pth_0
      | Comb(Const("ring_1",_),_) ->
          pth_1
      | Comb(Comb(Const("ring_of_num",_),_),n) ->
          SPEC n pth_num
      | Comb(Comb(Const("ring_of_int",_),_),n) ->
          SPEC n pth_int
      | Comb(Comb(Const("ring_neg",_),_),s) ->
          let sth = mterm s in
          MATCH_MP pth_neg sth
      | Comb(Comb(Comb(Const("ring_pow",_),_),s),n) ->
          let sth = mterm s in
          MATCH_MP (SPEC n pth_pow) sth
      | Comb(Comb(Comb(Const("ring_add",_),_),s),t) ->
          let sth = mterm s and tth = mterm t in
          MATCH_MP pth_add (CONJ sth tth)
      | Comb(Comb(Comb(Const("ring_sub",_),_),s),t) ->
          let sth = mterm s and tth = mterm t in
          MATCH_MP pth_sub (CONJ sth tth)
      | Comb(Comb(Comb(Const("ring_mul",_),_),s),t) ->
          let sth = mterm s and tth = mterm t in
          MATCH_MP pth_mul (CONJ sth tth)
      | _ -> UNDISCH(SPEC tm pth_asm) in
    let rec mform tm =
      if is_neg tm then
         RAND_CONV mform tm
      else if is_iff tm || is_imp tm || is_conj tm || is_disj tm then
         BINOP_CONV mform tm
      else if is_eq tm then
        let s,t = dest_eq tm in
        let sth = mterm s and tth = mterm t in
        MATCH_MP pth_eq (CONJ sth tth)
      else failwith "RING_MONOMORPHIC_IMAGE_RULE: unhandled formula" in
    mform;;

(* ------------------------------------------------------------------------- *)
(* A decision procedure for the universal theory of rings, mapping           *)
(* momomorphically into a "total" ring to leverage earlier stuff.            *)
(* It will prove either the exact thing you request, or if you omit some     *)
(* carrier membership hypotheses, will add those as an antecedent.           *)
(* ------------------------------------------------------------------------- *)

let RING_RULE =
  let RING_TOTALIZATION = prove
   (`!r:A ring.
          (?r' f. ring_carrier r' = (:1) /\
                  ring_monomorphism(r,r') f) \/
          (?r' f. ring_carrier r' = (:num#A->bool) /\
                  ring_monomorphism(r,r') f)`,
    let lemma = prove
     (`!r:A ring.
            ~(trivial_ring r) /\ INFINITE(:B) /\ (:A) <=_c (:B)
            ==> ring_carrier(product_ring (:B) (\i. r)) =_c (:B->bool)`,
      REPEAT STRIP_TAC THEN REWRITE_TAC[PRODUCT_RING] THEN
      REWRITE_TAC[CARTESIAN_PRODUCT_CONST; GSYM CARD_EXP_UNIV] THEN
      MATCH_MP_TAC CARD_EXP_ABSORB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [TRANS_TAC CARD_LE_TRANS `{ring_0 r:A,ring_1 r:A}` THEN
        CONJ_TAC THENL
         [SIMP_TAC[CARD_LE_CARD; FINITE_INSERT; FINITE_EMPTY; FINITE_BOOL;
                   CARD_BOOL; CARD_CLAUSES] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[TRIVIAL_RING_10]) THEN
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
          CONV_TAC NUM_REDUCE_CONV;
          MATCH_MP_TAC CARD_LE_SUBSET THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; RING_0; RING_1]];
        TRANS_TAC CARD_LE_TRANS `(:A)` THEN
        ASM_SIMP_TAC[CARD_LE_SUBSET; SUBSET_UNIV] THEN
        TRANS_TAC CARD_LE_TRANS `(:B)` THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[CARD_EXP_CANTOR; CARD_LT_IMP_LE]]) in
    GEN_TAC THEN ASM_CASES_TAC `trivial_ring(r:A ring)` THENL
     [DISJ1_TAC THEN EXISTS_TAC `singleton_ring one` THEN
      EXISTS_TAC `(\x. one):A->1` THEN
      ASM_SIMP_TAC[RING_MONOMORPHISM_FROM_TRIVIAL_RING;
                   RING_HOMOMORPHISM_FROM_TRIVIAL_RING] THEN
      ASM_SIMP_TAC[TRIVIAL_RING_SINGLETON_RING; SINGLETON_RING] THEN
      REWRITE_TAC[IMAGE_CONST; RING_CARRIER_NONEMPTY] THEN
      REWRITE_TAC[EXTENSION; IN_UNIV; IN_SING; FORALL_ONE_THM];
      DISJ2_TAC] THEN
    MP_TAC(snd(EQ_IMP_RULE(ISPECL
     [`product_ring (:num#A) (\i. (r:A ring))`; `(:num#A->bool)`]
     ISOMORPHIC_COPY_OF_RING))) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC lemma THEN
      ASM_REWRITE_TAC[GSYM MUL_C_UNIV; INFINITE; CARD_MUL_FINITE_EQ] THEN
      REWRITE_TAC[UNIV_NOT_EMPTY; DE_MORGAN_THM; GSYM INFINITE] THEN
      REWRITE_TAC[num_INFINITE; MUL_C_UNIV] THEN
      REWRITE_TAC[le_c] THEN EXISTS_TAC `\x:A. 0,x` THEN
      REWRITE_TAC[IN_UNIV; PAIR_EQ];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r':(num#A->bool)ring` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [isomorphic_ring]) THEN
    DISCH_THEN(X_CHOOSE_TAC `f:(num#A->A)->num#A->bool`) THEN
    EXISTS_TAC `(f:(num#A->A)->num#A->bool) o (\x i. x)` THEN
    MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN
    EXISTS_TAC `product_ring (:num#A) (\i. (r:A ring))` THEN
    REWRITE_TAC[RING_MONOMORPHISM_DIAGONAL_UNIV] THEN
    ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_MONOMORPHISM]) in
  let RING_WORD_UNIVERSAL =
    let cth = prove
     (`ring_0 r = ring_of_int r (&0) /\
       ring_1 r = ring_of_int r (&1)`,
      REWRITE_TAC[RING_OF_INT_OF_NUM; RING_OF_NUM_0; RING_OF_NUM_1])
    and pth = (UNDISCH o prove)
     (`ring_carrier r = (:A)
       ==> (x = y <=> ring_sub r x y = ring_of_int r (&0))`,
      SIMP_TAC[RING_SUB_EQ_0; IN_UNIV; RING_OF_INT_OF_NUM; RING_OF_NUM_0])
    and bth = REFL `ring_of_int r (&0):A`
    and mth = (UNDISCH o prove)
     (`ring_carrier r = (:A)
       ==> p = ring_of_int r (&0) ==> !c. ring_mul r c p = ring_of_int r (&0)`,
      SIMP_TAC[RING_MUL_RZERO; RING_OF_INT_OF_NUM; RING_OF_NUM_0; IN_UNIV])
    and dth = (UNDISCH o prove)
     (`ring_carrier r = (:A)
       ==> p = ring_of_int r (&0) /\ q = ring_of_int r (&0)
           ==> ring_add r p q = ring_of_int r (&0)`,
      SIMP_TAC[RING_ADD_RZERO; RING_OF_INT_OF_NUM; RING_OF_NUM_0; IN_UNIV]) in
    let decorule =
      GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV)
       [cth; GSYM RING_OF_INT_OF_NUM] o
      PART_MATCH lhand pth in
    fun tm ->
      let avs,bod = strip_forall tm in
      if is_imp bod then
        let ant,con = dest_imp bod in
        let aths =
          mapfilter (CONV_RULE decorule) (CONJUNCTS(ASSUME ant))
        and cth = decorule con in
        let atms = map (lhand o concl) aths
        and ctm = lhand(rand(concl cth)) in
        let ctms = ring_ring_cofactors_universal atms ctm in
        let zths = map2 (fun c th -> SPEC c (MATCH_MP mth th)) ctms aths in
        let zth =
          end_itlist (fun th1 th2 -> MATCH_MP dth (CONJ th1 th2)) zths in
        let eth =
          TRANS (RING_POLY_UNIVERSAL_CONV ctm)
          (SYM(RING_POLY_UNIVERSAL_CONV (lhand(concl zth)))) in
        GENL avs (DISCH ant (EQ_MP (SYM cth) (TRANS eth zth)))
      else
        let th1 = decorule tm in
        let th2 = CONV_RULE
          (RAND_CONV (LAND_CONV RING_POLY_UNIVERSAL_CONV)) th1 in
        EQ_MP (SYM th2) bth in
  let RING_RING_WORD =
    let imp_imp_rule = GEN_REWRITE_RULE I [IMP_IMP]
    and left_exists_rule = GEN_REWRITE_RULE I [LEFT_FORALL_IMP_THM]
    and or_elim_rule =
      GEN_REWRITE_RULE I [TAUT `(p ==> q) /\ (p' ==> q) <=> p \/ p' ==> q`] in
    fun ths tm ->
      let dty = type_of(rand tm) in
      let rty = mk_type("ring",[dty]) in
      let rtms = filter ((=) rty o type_of) (freesl(tm::map concl ths)) in
      if length rtms <> 1
      then failwith "RING_RULE: can't deduce which ring" else
      let rtm = hd rtms in
      let tvs =
        itlist (union o type_vars_in_term o concl) ths
               (type_vars_in_term tm) in
      let dty' = mk_vartype("Z"^itlist ((^) o dest_vartype) tvs "") in
      let rty' = mk_type("ring",[dty']) in
      let avvers = itlist (union o variables o concl) ths (variables tm) in
      let rtm' = variant avvers (mk_var("r'",rty'))
      and htm = variant avvers (mk_var("h",mk_fun_ty dty dty')) in
      let hasm = list_mk_icomb "ring_monomorphism" [mk_pair(rtm,rtm'); htm] in
      let hth = ASSUME hasm in
      let ths' = mapfilter (CONV_RULE(RING_MONOMORPHIC_IMAGE_RULE hth)) ths
      and th' = RING_MONOMORPHIC_IMAGE_RULE hth tm in
      let utm =
        if ths' = [] then rand(concl th')
        else mk_imp(list_mk_conj (map concl ths'),rand(concl th')) in
      let hvs = find_terms
       (fun t -> is_comb t && rator t = htm && is_var(rand t)) utm in
      let gvs = map (genvar o type_of) hvs in
      let vtm = subst (zip gvs hvs) utm in
      let arty = mk_type("ring",[aty]) in
      let atm =
        vsubst [mk_var("r",arty),mk_var(fst(dest_var rtm'),arty)]
               (inst[aty,dty'] vtm) in
      let th1 = RING_WORD_UNIVERSAL atm in
      let th2 = INST_TYPE [dty',aty] th1 in
      let th3 = INST [rtm',mk_var("r",rty')] th2 in
      let th4 = INST (zip hvs gvs) th3 in
      let th5 =
        if ths' = [] then th4 else
        MP th4 (end_itlist CONJ ths') in
      let th6 = itlist PROVE_HYP ths (EQ_MP (SYM th') th5) in
      let ueq = mk_eq(list_mk_icomb "ring_carrier" [rtm'],
                      mk_const("UNIV",[dty',aty])) in
      let th7 = imp_imp_rule (DISCH ueq (DISCH hasm th6)) in
      let th8 = left_exists_rule(GEN htm th7) in
      let th9 = left_exists_rule(GEN rtm' th8) in
      let th10 = ISPEC rtm RING_TOTALIZATION in
      let th11 = CONJ (PART_MATCH lhand th9 (lhand(concl th10)))
                      (PART_MATCH lhand th9 (rand(concl th10))) in
      MP (or_elim_rule th11) th10 in
  let RING_RING_HORN =
    let ddj_conv =
      GEN_REWRITE_CONV (RAND_CONV o DEPTH_CONV)
        [TAUT `~p \/ ~q <=> ~(p /\ q)`] THENC
      GEN_REWRITE_CONV I [TAUT `p \/ ~q <=> q ==> p`] in
    fun tm ->
      if not(is_disj tm) then RING_RING_WORD [] tm else
      let th0 = ddj_conv tm in
      let tm' = rand(concl th0) in
      let abod = lhand tm' in
      let ths = CONJUNCTS(ASSUME abod) in
      let th1 = RING_RING_WORD ths (rand tm') in
      EQ_MP (SYM th0) (DISCH abod (itlist PROVE_HYP ths th1)) in
  let RING_RING_CORE =
    let pth = TAUT `p ==> q <=> (p \/ q <=> q)`
    and ptm = `p:bool` and qtm = `q:bool` in
    fun tm ->
      let negdjs,posdjs = partition is_neg (disjuncts tm) in
      let th = tryfind
       (fun p -> RING_RING_HORN (list_mk_disj(p::negdjs))) posdjs in
      let th1 = INST[concl th,ptm; tm,qtm] pth in
      MP (EQ_MP (SYM th1) (DISJ_ACI_RULE(rand(concl th1)))) th in
  let init_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    CONDS_ELIM_CONV THENC
    NNFC_CONV THENC CNF_CONV THENC
    SKOLEM_CONV THENC PRENEX_CONV THENC
    GEN_REWRITE_CONV REDEPTH_CONV
     [RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM DISJ_ASSOC] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM CONJ_ASSOC] in
  let RING_RULE_BASIC tm =
    let avs,bod = strip_forall tm in
    let th1 = init_conv bod in
    let tm' = rand(concl th1) in
    let avs',bod' = strip_forall tm' in
    let th2 = end_itlist CONJ (map RING_RING_CORE (conjuncts bod')) in
    let th3 = EQ_MP (SYM th1) (GENL avs' th2) in
    let imps = hyp th3 in
    let th4 =
      if imps = [] then th3
      else DISCH_ALL
             (itlist PROVE_HYP (CONJUNCTS(ASSUME(list_mk_conj imps))) th3) in
    GENL avs th4 in
  fun tm ->
    let tvs = type_vars_in_term tm in
    let ty = mk_vartype("Y"^itlist ((^) o dest_vartype) tvs "") in
    let tm' = inst[ty,aty] tm in
    INST_TYPE [aty,ty] (RING_RULE_BASIC tm');;

(* ------------------------------------------------------------------------- *)
(* A naive tactic form, pulling in equations in the assumptions and          *)
(* either solving outright or leaving some ring carrier membership           *)
(* ------------------------------------------------------------------------- *)

let RING_TAC =
  REPEAT GEN_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
  W(fun (asl,w) ->
        let th = RING_RULE w in
        (MATCH_ACCEPT_TAC th ORELSE
         (MATCH_MP_TAC th THEN ASM_REWRITE_TAC[])));;

(* ------------------------------------------------------------------------- *)
(* Cosets in a ring.                                                         *)
(* ------------------------------------------------------------------------- *)

let ring_coset = new_definition
 `ring_coset (r:A ring) j = \a. {ring_add r a x | x IN j}`;;

let RING_COSET_SETADD = prove
 (`!r s a:A. ring_coset r s a = ring_setadd r {a} s`,
  REWRITE_TAC[ring_setadd; ring_coset] THEN SET_TAC[]);;

let RING_COSET = prove
 (`!r t x:A.
        x IN ring_carrier r /\ t SUBSET ring_carrier r
        ==> ring_coset r t x SUBSET ring_carrier r`,
  SIMP_TAC[RING_COSET_SETADD; RING_SETADD; SING_SUBSET]);;

let RING_COSET_0 = prove
 (`!r t:A->bool.
        t SUBSET ring_carrier r ==> ring_coset r t (ring_0 r) = t`,
  SIMP_TAC[RING_COSET_SETADD; RING_SETADD_LZERO]);;

let RING_COSET_TRIVIAL = prove
 (`!r x:A. x IN ring_carrier r ==> ring_coset r {ring_0 r} x = {x}`,
  SIMP_TAC[RING_COSET_SETADD; RING_SETADD_SING; RING_0; RING_ADD_RZERO]);;

let RING_COSET_CARRIER = prove
 (`!r x:A. x IN ring_carrier r
           ==> ring_coset r (ring_carrier r) x = ring_carrier r`,
  SIMP_TAC[RING_COSET_SETADD; RING_SETADD_LSUBSET; SING_SUBSET;
           NOT_INSERT_EMPTY; RING_IDEAL_CARRIER]);;

let RING_COSET_EQ = prove
 (`!r j x y:A.
        (ring_ideal r j \/ j subring_of r) /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_coset r j x = ring_coset r j y <=> ring_sub r x y IN j)`,
  SIMP_TAC[RING_SETADD_RCANCEL_SET; RING_COSET_SETADD]);;

let RING_COSET_EQ_IDEAL = prove
 (`!r j x:A.
        (ring_ideal r j \/ j subring_of r) /\ x IN ring_carrier r
        ==> (ring_coset r j x = j <=> x IN j)`,
  SIMP_TAC[RING_COSET_SETADD; RING_SETADD_LSUBSET_EQ; SING_SUBSET] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY]);;

let RING_COSET_EQ_EMPTY = prove
 (`!r j x:A. ring_coset r j x = {} <=> j = {}`,
  REWRITE_TAC[RING_COSET_SETADD; RING_SETADD_EQ_EMPTY; NOT_INSERT_EMPTY]);;

let RING_COSET_NONEMPTY = prove
 (`!r j x:A. ring_ideal r j \/ j subring_of r ==> ~(ring_coset r j x = {})`,
  MESON_TAC[RING_COSET_EQ_EMPTY; SUBRING_OF_IMP_NONEMPTY;
            RING_IDEAL_IMP_NONEMPTY]);;

let IN_RING_COSET_SELF = prove
 (`!r j x:A.
      (ring_ideal r j \/ j subring_of r) /\ x IN ring_carrier r
      ==> x IN ring_coset r j x`,
  REWRITE_TAC[ring_ideal; subring_of; RING_COSET_SETADD; ring_setadd;
              IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[RING_ADD_RZERO]);;

let UNIONS_RING_COSETS = prove
 (`!r j:A->bool.
        ring_ideal r j \/ j subring_of r
        ==> UNIONS {ring_coset r j x |x| x IN ring_carrier r} =
            ring_carrier r`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[RING_COSET; RING_IDEAL_IMP_SUBSET; SUBRING_OF_IMP_SUBSET] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; SUBSET] THEN
  ASM_MESON_TAC[IN_RING_COSET_SELF]);;

let RING_COSETS_EQ = prove
 (`!r j x y:A.
        (ring_ideal r j \/ j subring_of r) /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_coset r j x = ring_coset r j y <=>
             ~(DISJOINT (ring_coset r j x) (ring_coset r j y)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[GSYM DISJOINT_EMPTY_REFL; RING_COSET_NONEMPTY] THEN
  ASM_SIMP_TAC[RING_COSET_EQ; LEFT_IMP_EXISTS_THM; IMP_CONJ; SET_RULE
   `~DISJOINT s t <=> ?x. x IN s /\ ?y. y IN t /\ x = y`] THEN
  REWRITE_TAC[RING_COSET_SETADD; ring_setadd; FORALL_IN_GSPEC; IN_SING] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  X_GEN_TAC `u:A` THEN DISCH_TAC THEN X_GEN_TAC `v:A` THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:A. ring_sub r x u`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_ideal; subring_of; SUBSET]) THEN
  REWRITE_TAC[ring_sub] THEN
  ASM_SIMP_TAC[GSYM RING_ADD_ASSOC; RING_ADD_RNEG; RING_ADD_RZERO] THEN
  DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_ADD_SYM o lhand o snd) THEN
  (ANTS_TAC THENL
   [ASM_MESON_TAC[RING_ADD; RING_NEG]; DISCH_THEN SUBST1_TAC]) THEN
  ASM_SIMP_TAC[RING_ADD_ASSOC; RING_SUB; RING_ADD; RING_NEG; RING_ADD_LNEG]);;

let DISJOINT_RING_COSETS = prove
 (`!r j x y:A.
        (ring_ideal r j \/ j subring_of r) /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (DISJOINT (ring_coset r j x) (ring_coset r j y) <=>
             ~(ring_coset r j x = ring_coset r j y))`,
  SIMP_TAC[RING_COSETS_EQ]);;

let PAIRWISE_DISJOINT_RING_COSETS = prove
 (`!r j:A->bool.
        ring_ideal r j \/ j subring_of r
        ==> pairwise DISJOINT {ring_coset r j x |x| x IN ring_carrier r}`,
  REWRITE_TAC[SIMPLE_IMAGE; PAIRWISE_IMAGE] THEN
  SIMP_TAC[pairwise; DISJOINT_RING_COSETS]);;

let IMAGE_RING_COSET_SWITCH = prove
 (`!r j x y:A.
        (ring_ideal r j \/ j subring_of r) /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> IMAGE (\a. ring_add r (ring_sub r y x) a)
                  (ring_coset r j x) =
            ring_coset r j y`,
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
   `ring_setadd r {ring_sub r y x:A} (ring_coset r j x)` THEN
  (CONJ_TAC THENL [REWRITE_TAC[ring_setadd] THEN SET_TAC[]; ALL_TAC]) THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET);
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBRING_OF_IMP_SUBSET)] THEN
  REWRITE_TAC[RING_COSET_SETADD; ring_sub] THEN
  ASM_SIMP_TAC[RING_SETADD_ASSOC; RING_SETADD; SING_SUBSET;
               RING_ADD; RING_NEG; RING_SETADD_SING; GSYM RING_ADD_ASSOC;
               RING_ADD_LNEG; RING_ADD_RZERO]);;

let CARD_EQ_RING_COSETS = prove
 (`!r j x y:A.
        (ring_ideal r j \/ j subring_of r) /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> ring_coset r j x =_c ring_coset r j y`,
  let lemma = prove
   (`!f g. (IMAGE f s = t /\ IMAGE g t = s) /\
           (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
     ==> s =_c t`,
    REWRITE_TAC[eq_c; LEFT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  EXISTS_TAC `\a:A. ring_add r (ring_sub r y x) a` THEN
  EXISTS_TAC `\a:A. ring_add r (ring_sub r x y) a` THEN
  ASM_SIMP_TAC[IMAGE_RING_COSET_SWITCH; INJECTIVE_ON_ALT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_ADD_LCANCEL THEN
  ASM_MESON_TAC[RING_SUB; SUBSET; RING_COSET;
                SUBRING_OF_IMP_SUBSET; RING_IDEAL_IMP_SUBSET]);;

let CARD_EQ_RING_COSET_IDEAL = prove
 (`!r j x:A.
        (ring_ideal r j \/ j subring_of r) /\
        x IN ring_carrier r
        ==> ring_coset r j x =_c j`,
 MESON_TAC[CARD_EQ_RING_COSETS; RING_0; RING_COSET_0;
           SUBRING_OF_IMP_SUBSET; RING_IDEAL_IMP_SUBSET]);;

let LAGRANGE_THEOREM_RING_EXPLICIT = prove
 (`!r j:A->bool.
        FINITE(ring_carrier r) /\
        (ring_ideal r j \/ j subring_of r)
        ==> CARD {ring_coset r j x |x| x IN ring_carrier r} * CARD j =
            CARD(ring_carrier r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE(j:A->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; ring_ideal; subring_of]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [SYM(MATCH_MP UNIONS_RING_COSETS th)]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNIONS o rand o snd) THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE] THEN
  ASM_SIMP_TAC[GSYM DISJOINT; DISJOINT_RING_COSETS] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; RING_COSET; ring_ideal; subring_of];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[GSYM NSUM_CONST; FINITE_IMAGE] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CARD_EQ_CARD_IMP THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CARD_EQ_RING_COSET_IDEAL]);;

let LAGRANGE_THEOREM_RING = prove
 (`!r j:A->bool.
        FINITE(ring_carrier r) /\
        (ring_ideal r j \/ j subring_of r)
        ==> (CARD j) divides CARD(ring_carrier r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP LAGRANGE_THEOREM_RING_EXPLICIT) THEN
  NUMBER_TAC);;

let CARD_DIVIDES_RING_MONOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f /\ FINITE(ring_carrier r')
        ==> CARD(ring_carrier r) divides CARD(ring_carrier r')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD(ring_carrier r) = CARD(ring_image (r,r') (f:A->B))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_EQ_CARD_IMP THEN
    REWRITE_TAC[ring_image] THEN
    ASM_MESON_TAC[CARD_EQ_RING_MONOMORPHIC_IMAGE;
                  FINITE_RING_MONOMORPHIC_PREIMAGE];
    MATCH_MP_TAC LAGRANGE_THEOREM_RING THEN
    ASM_MESON_TAC[SUBRING_RING_IMAGE; ring_monomorphism]]);;

let CARD_DIVIDES_RING_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f /\ FINITE(ring_carrier r)
        ==> CARD(ring_carrier r') divides CARD(ring_carrier r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RING_EPIMORPHISM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CARD_EQ_RING_IMAGE_KERNEL) THEN DISCH_THEN
   (MP_TAC o (MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_CARD_IMP))) THEN
  ASM_REWRITE_TAC[ring_image; mul_c; GSYM CROSS; ring_kernel] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[FINITE_CROSS; CARD_CROSS; FINITE_IMAGE; FINITE_RESTRICT] THEN
  CONV_TAC NUMBER_RULE);;

let CARD_RING_COSETS_DIVIDES = prove
 (`!r j:A->bool.
        FINITE(ring_carrier r) /\
        (ring_ideal r j \/ j subring_of r)
        ==> CARD {ring_coset r j x | x | x IN ring_carrier r} divides
            CARD(ring_carrier r)`,
  MESON_TAC[divides; LAGRANGE_THEOREM_RING_EXPLICIT]);;

let RING_SETADD_PROD_RING = prove
 (`!(r1:A ring) (r2:B ring) s1 s2 t1 t2.
        ring_setadd (prod_ring r1 r2) (s1 CROSS s2) (t1 CROSS t2) =
        (ring_setadd r1 s1 t1) CROSS (ring_setadd r2 s2 t2)`,
  REWRITE_TAC[ring_setadd; CROSS; PROD_RING; SET_RULE
   `{f x y | x IN {s a b | P a b} /\ y IN {t c d | Q c d}} =
    {f (s a b) (t c d) | P a b /\ Q c d}`] THEN
  SET_TAC[]);;

let RING_COSET_PROD_RING = prove
 (`!r1 r2 s1 s2 (x1:A) (x2:B).
        ring_coset (prod_ring r1 r2) (s1 CROSS s2) (x1,x2) =
        (ring_coset r1 s1 x1) CROSS (ring_coset r2 s2 x2)`,
  REWRITE_TAC[RING_COSET_SETADD; GSYM CROSS_SING; RING_SETADD_PROD_RING]);;

let RING_SETADD_PRODUCT_RING = prove
 (`!(r:K->A ring) k s t.
        ring_setadd (product_ring k r)
                     (cartesian_product k s) (cartesian_product k t) =
        cartesian_product k (\i. ring_setadd (r i) (s i) (t i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ring_setadd; CARTESIAN_PRODUCT_AS_RESTRICTIONS;
              PRODUCT_RING] THEN
  REWRITE_TAC[IN_ELIM_THM; SET_RULE
   `{f x y | x,y | x IN {s x | P x} /\ y IN {s f | Q f}} =
    {f (s x) (s y) | P x /\ Q y}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; TAUT
   `p ==> (q /\ r) /\ s <=> (p ==> s) /\ (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[GSYM RESTRICTION_EXTENSION; SET_RULE
   `{RESTRICTION k f | f | ?x y. RESTRICTION k f = RESTRICTION k (s x y) /\
                                 R x y} =
    {RESTRICTION k (s x y) | R x y}`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y. R x y ==> f x y = s x y)
    ==> {f x y | R x y} = {s x y | R x y}`) THEN
  REWRITE_TAC[RESTRICTION_EXTENSION] THEN SIMP_TAC[RESTRICTION]);;

let RING_COSET_PRODUCT_RING = prove
 (`!(r:K->A ring) j x k.
        ring_coset (product_ring k r) (cartesian_product k j) x =
        cartesian_product k (\i. ring_coset (r i) (j i) (x i))`,
  REWRITE_TAC[RING_COSET_SETADD; GSYM RING_SETADD_PRODUCT_RING] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[CARTESIAN_PRODUCT_SINGS_GEN] THEN
  REWRITE_TAC[ring_setadd; PRODUCT_RING; SET_RULE
   `{f x y | x,y | x IN {a} /\ P y} = {f a x | P x}`] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = g x) ==> {f x | x IN s} = {g x | x IN s}`) THEN
  REWRITE_TAC[RESTRICTION_EXTENSION] THEN SIMP_TAC[RESTRICTION]);;

let RING_SETNEG_SUBRING_GENERATED = prove
 (`!r s:A->bool.
        ring_setneg (subring_generated r s) = ring_setneg r`,
  REWRITE_TAC[ring_setneg; FUN_EQ_THM; SUBRING_GENERATED]);;

let RING_SETADD_SUBRING_GENERATED = prove
 (`!r s:A->bool.
        ring_setadd (subring_generated r s) = ring_setadd r`,
  REWRITE_TAC[ring_setadd; FUN_EQ_THM; SUBRING_GENERATED]);;

let RING_SETNEG_COSET = prove
 (`!r j a:A.
        a IN ring_carrier r /\ (ring_ideal r j \/ j subring_of r)
        ==> ring_setneg r (ring_coset r j a) = ring_coset r j (ring_neg r a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_coset] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; ring_setneg; FORALL_IN_GSPEC; IMP_CONJ;
              RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[SET_RULE `{f x | x IN {g a | P a}} = {f (g a) | P a}`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `ring_neg r x:A` THEN
  ASM_SIMP_TAC[IN_RING_IDEAL_NEG; IN_SUBRING_NEG] THEN
  (FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) ORELSE
   FIRST_X_ASSUM(MP_TAC o MATCH_MP SUBRING_OF_IMP_SUBSET)) THEN
  ASM_SIMP_TAC[SUBSET; RING_NEG_ADD; RING_NEG_NEG; RING_NEG]);;

let RING_SETADD_COSETS = prove
 (`!r j a b:A.
        (ring_ideal r j \/ j subring_of r) /\
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> ring_setadd r (ring_coset r j a) (ring_coset r j b) =
            ring_coset r j (ring_add r a b)`,
  REWRITE_TAC[RING_COSET_SETADD] THEN
  ASM_SIMP_TAC[RING_SETADD_IDEAL_RIGHT; SING_SUBSET; IN_SING] THEN
  REWRITE_TAC[RING_SETADD_SING]);;

let RING_SETMUL_COSETS = prove
 (`!r j a b:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\ ring_ideal r j
        ==> ring_setmul r (ring_coset r j a) (ring_coset r j b)
            SUBSET ring_coset r j (ring_mul r a b)`,
  REWRITE_TAC[RING_COSET_SETADD] THEN
  ASM_SIMP_TAC[RING_SETMUL_IDEAL_RIGHT; GSYM RING_SETMUL_SING; SING_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Quotient rings.                                                           *)
(* ------------------------------------------------------------------------- *)

let quotient_ring = new_definition
 `quotient_ring (r:A ring) j =
        ring({ring_coset r j a | a | a IN ring_carrier r},
             ring_coset r j (ring_0 r:A),
             ring_coset r j (ring_1 r),
             ring_setneg r,
             ring_setadd r,
             (\s t. ring_setadd r (ring_setmul r s t) j))`;;

let RING_HOMOMORPHISM_RING_COSET,QUOTIENT_RING = (CONJ_PAIR o prove)
 (`(!r j:A->bool.
        ring_ideal r j
        ==> ring_homomorphism (r,quotient_ring r j) (ring_coset r j)) /\
   (!r j:A->bool.
        ring_ideal r j
        ==> ring_carrier (quotient_ring r j) =
            {ring_coset r j a | a | a IN ring_carrier r}) /\
   (!r j:A->bool.
        ring_ideal r j
        ==> ring_0 (quotient_ring r j) = ring_coset r j (ring_0 r)) /\
   (!r j:A->bool.
        ring_ideal r j
        ==> ring_1 (quotient_ring r j) = ring_coset r j (ring_1 r)) /\
   (!r j:A->bool.
        ring_ideal r j ==> ring_neg (quotient_ring r j) = ring_setneg r) /\
   (!r j:A->bool.
        ring_ideal r j ==> ring_add (quotient_ring r j) = ring_setadd r) /\
   (!r j:A->bool.
        ring_ideal r j
        ==> ring_mul (quotient_ring r j) =
            (\s t. ring_setadd r (ring_setmul r s t) j))`,
  let lemma = prove
   (`!r j a b:A.
          ring_ideal r j /\ a IN ring_carrier r /\ b IN ring_carrier r
          ==> ring_setadd r
                (ring_setmul r (ring_coset r j a) (ring_coset r j b)) j =
              ring_coset r j (ring_mul r a b)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[ring_coset] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; ring_setmul; ring_setadd; FORALL_IN_GSPEC; IMP_CONJ;
                RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[SET_RULE
     `{f x y | x IN {g a | P a} /\ y IN {h b | Q b}} =
      {f (g a) (h b) | P a /\ Q b}`] THEN
    REWRITE_TAC[SET_RULE
      `{f x y | x IN {g a b | P a b} /\ y IN t} =
       {f (g a b) y | P a b /\ y IN t}`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `z:A`] THEN STRIP_TAC THEN
      EXISTS_TAC `ring_add r (ring_mul r x b)
       (ring_add r (ring_mul r a y) (ring_add r (ring_mul r x y) z)):A` THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
      ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [SUBSET; IN_RING_IDEAL_ADD; IN_RING_IDEAL_LMUL; RING_ADD_LDISTRIB;
        IN_RING_IDEAL_RMUL; RING_ADD; RING_MUL] THEN
      ASM_SIMP_TAC[RING_ADD; RING_ADD_RDISTRIB] THEN
      ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [GSYM RING_ADD_ASSOC; RING_MUL; RING_ADD];
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`ring_0 r:A`; `ring_0 r:A`; `z:A`] THEN
      ASM_SIMP_TAC[RING_0; RING_ADD_RZERO; IN_RING_IDEAL_0]]) in
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `ring_ideal r (j:A->bool)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[ring_homomorphism; RING_SETNEG_COSET;
                 RING_SETADD_COSETS; lemma] THEN
    SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (DEPTH_BINOP_CONV `/\` o LAND_CONV o ONCE_DEPTH_CONV)
   [ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul] THEN
  PURE_REWRITE_TAC[GSYM PAIR_EQ; BETA_THM; PAIR] THEN
  PURE_REWRITE_TAC[quotient_ring; GSYM(CONJUNCT2 ring_tybij)] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[RING_SETNEG_COSET; RING_SETADD_COSETS; lemma;
               RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
   [MESON_TAC[RING_0];
    MESON_TAC[RING_1];
    ASM_MESON_TAC[RING_NEG];
    ASM_MESON_TAC[RING_ADD];
    ASM_MESON_TAC[RING_MUL];
    ASM_SIMP_TAC[RING_ADD_SYM];
    ASM_SIMP_TAC[RING_ADD_ASSOC];
    ASM_SIMP_TAC[RING_ADD_LZERO];
    ASM_SIMP_TAC[RING_ADD_LNEG];
    ASM_SIMP_TAC[RING_MUL_SYM];
    ASM_SIMP_TAC[RING_MUL_ASSOC];
    ASM_SIMP_TAC[RING_MUL_LID];
    ASM_SIMP_TAC[RING_ADD_LDISTRIB]]);;

let RING_EPIMORPHISM_RING_COSET = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> ring_epimorphism (r,quotient_ring r j) (ring_coset r j)`,
  SIMP_TAC[ring_epimorphism; RING_HOMOMORPHISM_RING_COSET] THEN
  SIMP_TAC[QUOTIENT_RING] THEN SET_TAC[]);;

let QUOTIENT_RING_CARRIER = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> ring_carrier (quotient_ring r j) =
            {ring_coset r j a | a | a IN ring_carrier r}`,
  REWRITE_TAC[QUOTIENT_RING]);;

let QUOTIENT_RING_0 = prove
 (`!r j:A->bool.
        ring_ideal r j ==> ring_0(quotient_ring r j) = j`,
  SIMP_TAC[QUOTIENT_RING; RING_COSET_0; RING_IDEAL_IMP_SUBSET]);;

let QUOTIENT_RING_1 = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> ring_1(quotient_ring r j) = ring_coset r j (ring_1 r)`,
  REWRITE_TAC[QUOTIENT_RING]);;

let QUOTIENT_RING_NEG = prove
 (`!r j a:A.
        ring_ideal r j /\ a IN ring_carrier r
        ==>  ring_neg (quotient_ring r j) (ring_coset r j a) =
             ring_coset r j (ring_neg r a)`,
  SIMP_TAC[REWRITE_RULE[ring_homomorphism] RING_HOMOMORPHISM_RING_COSET]);;

let QUOTIENT_RING_ADD = prove
 (`!r j a b:A.
        ring_ideal r j /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==>  ring_add (quotient_ring r j)
                      (ring_coset r j a) (ring_coset r j b) =
             ring_coset r j (ring_add r a b)`,
  SIMP_TAC[REWRITE_RULE[ring_homomorphism] RING_HOMOMORPHISM_RING_COSET]);;

let QUOTIENT_RING_MUL = prove
 (`!r j a b:A.
        ring_ideal r j /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==>  ring_mul (quotient_ring r j)
                      (ring_coset r j a) (ring_coset r j b) =
             ring_coset r j (ring_mul r a b)`,
  SIMP_TAC[REWRITE_RULE[ring_homomorphism] RING_HOMOMORPHISM_RING_COSET]);;

let RING_KERNEL_RING_COSET = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> ring_kernel(r,quotient_ring r j) (ring_coset r j) = j`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ring_kernel; QUOTIENT_RING_0] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[RING_COSET_EQ_IDEAL; RING_IDEAL_IMP_SUBSET; SUBSET]);;

let CARD_LE_QUOTIENT_RING = prove
 (`!r j:A->bool.
    ring_ideal r j ==> ring_carrier(quotient_ring r j) <=_c ring_carrier r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_EPIMORPHISM_RING_COSET) THEN
  REWRITE_TAC[CARD_LE_RING_EPIMORPHIC_IMAGE]);;

let CARD_QUOTIENT_RING_DIVIDES = prove
 (`!r j:A->bool.
        FINITE(ring_carrier r) /\ ring_ideal r j
        ==> CARD(ring_carrier(quotient_ring r j)) divides
            CARD(ring_carrier r)`,
  SIMP_TAC[QUOTIENT_RING; CARD_RING_COSETS_DIVIDES]);;

let QUOTIENT_RING_UNIVERSAL_EXPLICIT = prove
 (`!r r' j (f:A->B).
        ring_homomorphism (r,r') f /\ ring_ideal r j /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\
               ring_coset r j x = ring_coset r j y
               ==> f x = f y)
        ==> ?g. ring_homomorphism(quotient_ring r j,r') g /\
                !x. x IN ring_carrier r ==> g(ring_coset r j x) = f x`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GSYM o GEN_REWRITE_RULE I [FUNCTION_FACTORS_LEFT_GEN]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:(A->bool)->B` THEN
  DISCH_TAC THEN ASM_SIMP_TAC[CONJUNCT1 QUOTIENT_RING] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[RING_ADD; QUOTIENT_RING_ADD; RING_MUL; QUOTIENT_RING_MUL;
               RING_NEG; QUOTIENT_RING_NEG; RING_1; QUOTIENT_RING_1] THEN
  ASM_SIMP_TAC[QUOTIENT_RING; RING_0]);;

let QUOTIENT_RING_UNIVERSAL = prove
 (`!r r' j (f:A->B).
        ring_homomorphism (r,r') f /\
        ring_ideal r j /\
        j SUBSET ring_kernel(r,r') f
        ==> ?g. ring_homomorphism(quotient_ring r j,r') g /\
                !x. x IN ring_carrier r ==> g(ring_coset r j x) = f x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC QUOTIENT_RING_UNIVERSAL_EXPLICIT THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ring_sub r x y:A` o REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[GSYM RING_COSET_EQ; ring_kernel; IN_ELIM_THM; RING_SUB] THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_SUB] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC RING_SUB_EQ_0 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[]);;

let QUOTIENT_RING_UNIVERSAL_EPIMORPHISM = prove
 (`!r r' j (f:A->B).
        ring_epimorphism (r,r') f /\
        ring_ideal r j /\
        j SUBSET ring_kernel(r,r') f
        ==> ?g. ring_epimorphism(quotient_ring r j,r') g /\
                !x. x IN ring_carrier r ==> g(ring_coset r j x) = f x`,
  REWRITE_TAC[ring_epimorphism] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `j:A->bool`; `f:A->B`]
        QUOTIENT_RING_UNIVERSAL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[QUOTIENT_RING] THEN ASM SET_TAC[]);;

let FIRST_RING_ISOMORPHISM_THEOREM = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f
        ==> (quotient_ring r (ring_kernel (r,r') f)) isomorphic_ring
            (subring_generated r' (ring_image (r,r') f))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_ring; RING_ISOMORPHISM] THEN
  FIRST_ASSUM(MP_TAC o SPEC `ring_kernel (r,r') (f:A->B)` o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] QUOTIENT_RING_UNIVERSAL_EXPLICIT)) THEN
  ASM_SIMP_TAC[RING_IDEAL_RING_KERNEL] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[IMP_CONJ; RING_COSET_EQ; RING_IDEAL_RING_KERNEL];
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `g:(A->bool)->B` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_INTO_SUBRING_EQ; SUBRING_RING_IMAGE;
                 CARRIER_SUBRING_GENERATED_SUBRING] THEN
    ASM_SIMP_TAC[QUOTIENT_RING; RING_IDEAL_RING_KERNEL] THEN
    REWRITE_TAC[ring_image] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC[RING_COSET_EQ; RING_IDEAL_RING_KERNEL]] THEN
  ASM_SIMP_TAC[ring_kernel; IN_ELIM_THM; RING_HOMOMORPHISM_SUB] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[RING_SUB; RING_SUB_EQ_0]);;

let FIRST_RING_EPIMORPHISM_THEOREM = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f
        ==> (quotient_ring r (ring_kernel(r,r') f)) isomorphic_ring r'`,
  REWRITE_TAC[ring_epimorphism] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FIRST_RING_ISOMORPHISM_THEOREM) THEN
  ASM_REWRITE_TAC[ring_image; SUBRING_GENERATED_RING_CARRIER]);;

let SECOND_RING_ISOMORPHISM_THEOREM = prove
 (`!r s j:A->bool.
        s subring_of r /\ ring_ideal r j
        ==> ring_ideal (subring_generated r (ring_setadd r s j)) j /\
            ring_ideal (subring_generated r s) (s INTER j) /\
            quotient_ring (subring_generated r (ring_setadd r s j)) j
            isomorphic_ring
            quotient_ring (subring_generated r s) (s INTER j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RING_IDEAL_SUBRING_GENERATED THEN
    ASM_SIMP_TAC[SUBRING_SETADD_RIGHT] THEN
    MATCH_MP_TAC RING_SETADD_SUPERSET_RIGHT THEN
    ASM_MESON_TAC[subring_of; ring_ideal];
    ASM_SIMP_TAC[RING_SUBRING_INTER_IDEAL];
    STRIP_TAC] THEN
  ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  MP_TAC(ISPECL [`subring_generated r s:A ring`;
   `quotient_ring (subring_generated r (ring_setadd r s (j:A->bool))) j`;
   `ring_coset r (j:A->bool)`]
    FIRST_RING_EPIMORPHISM_THEOREM) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[RING_KERNEL_FROM_SUBRING_GENERATED] THEN
    ASM_SIMP_TAC[ring_kernel; QUOTIENT_RING] THEN
    ASM_SIMP_TAC[RING_COSET_0; RING_IDEAL_IMP_SUBSET] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
    ASM_MESON_TAC[RING_COSET_EQ_IDEAL; RING_IDEAL_IMP_SUBSET; SUBSET]] THEN
  SUBGOAL_THEN
   `subring_generated r s =
    subring_generated (subring_generated r (ring_setadd r s j)) (s:A->bool)`
   (fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th))
  THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUBRING_GENERATED_IDEMPOT THEN
    MATCH_MP_TAC RING_SETADD_SUPERSET_LEFT THEN
    ASM_MESON_TAC[subring_of; ring_ideal];
    ALL_TAC] THEN
  REWRITE_TAC[RING_EPIMORPHISM_ALT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_FROM_SUBRING_GENERATED THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_HOMOMORPHISM_RING_COSET o lhand o
      snd) THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[ring_coset; SUBRING_GENERATED];
    ASM_SIMP_TAC[QUOTIENT_RING; ring_image] THEN
    ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; SUBRING_SETADD_RIGHT] THEN
    REWRITE_TAC[ring_coset; SUBRING_GENERATED] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; ring_setadd] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN REWRITE_TAC[GSYM(REWRITE_RULE[]
     (ONCE_REWRITE_RULE[FUN_EQ_THM] ring_coset))] THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier r /\ y IN ring_carrier r`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ring_ideal; subring_of; SUBSET];
      EXISTS_TAC `x:A` THEN     ASM_SIMP_TAC[RING_COSET_EQ; RING_ADD]] THEN
    SUBGOAL_THEN `ring_add r x y:A = ring_add r y x` SUBST1_TAC THENL
     [ASM_MESON_TAC[RING_ADD_SYM]; REWRITE_TAC[ring_sub]] THEN
    ASM_SIMP_TAC[GSYM RING_ADD_ASSOC; RING_NEG;
                 RING_ADD_RNEG; RING_ADD_RZERO]]);;

let THIRD_RING_ISOMORPHISM_THEOREM = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\ j SUBSET k
        ==> quotient_ring (quotient_ring r j) (IMAGE (ring_coset r j) k)
             isomorphic_ring quotient_ring r k`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`r:A ring`; `quotient_ring r (k:A->bool)`; `j:A->bool`;
    `ring_coset r (k:A->bool)`] QUOTIENT_RING_UNIVERSAL_EPIMORPHISM) THEN
  ASM_SIMP_TAC[RING_EPIMORPHISM_RING_COSET; RING_KERNEL_RING_COSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->(A->bool)` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FIRST_RING_EPIMORPHISM_THEOREM) THEN
    ASM_SIMP_TAC[ring_kernel; QUOTIENT_RING] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ISOMORPHIC_RING_TRANS) THEN
  MATCH_MP_TAC(MESON[ISOMORPHIC_RING_REFL]`s = t ==> s isomorphic_ring t`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[SET_RULE
   `{y | y IN {f x | P x} /\ Q y} = IMAGE f {x | P x /\ Q(f x)}`] THEN
  REWRITE_TAC[ETA_AX] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  ASM_SIMP_TAC[RING_COSET_EQ; RING_0; RING_SUB_RZERO] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN
  SET_TAC[]);;

let QUOTIENT_RING_SUBRING_CORRESPONDENCE = prove
 (`!(r:A ring) j t.
        ring_ideal r j
        ==> (t subring_of (quotient_ring r j) <=>
             ?s. s subring_of r /\ j SUBSET s /\
                 {x | x IN ring_carrier r /\ ring_coset r j x IN t} = s /\
                 IMAGE (ring_coset r j) s = t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_EPIMORPHISM_RING_COSET) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_EPIMORPHISM_SUBRING_CORRESPONDENCE) THEN
  ASM_SIMP_TAC[RING_KERNEL_RING_COSET]);;

let QUOTIENT_RING_IDEAL_CORRESPONDENCE = prove
 (`!(r:A ring) j k.
        ring_ideal r j
        ==> (ring_ideal (quotient_ring r j) k <=>
             ?i. ring_ideal r i /\ j SUBSET i /\
                 {x | x IN ring_carrier r /\ ring_coset r j x IN k} = i /\
                 IMAGE (ring_coset r j) i = k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_EPIMORPHISM_RING_COSET) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_EPIMORPHISM_IDEAL_CORRESPONDENCE) THEN
  ASM_SIMP_TAC[RING_KERNEL_RING_COSET]);;

let FIRST_RING_ISOMORPHISM_THEOREM_GEN = prove
 (`!r r' (f:A->B) j k.
        ring_epimorphism(r,r') f /\
        ring_ideal r' k /\ {x | x IN ring_carrier r /\ f x IN k} = j
        ==> quotient_ring r j isomorphic_ring quotient_ring r' k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `quotient_ring r' (k:B->bool)`;
                 `ring_coset r' k o (f:A->B)`]
        FIRST_RING_EPIMORPHISM_THEOREM) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC RING_EPIMORPHISM_COMPOSE THEN EXISTS_TAC `r':B ring` THEN
    ASM_SIMP_TAC[RING_EPIMORPHISM_RING_COSET];
    MATCH_MP_TAC EQ_IMP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[ring_kernel; QUOTIENT_RING_0; o_THM] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN EXPAND_TAC "j" THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_COSET_EQ_IDEAL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_epimorphism]) THEN ASM SET_TAC[]);;

let FIRST_RING_ISOMORPHISM_THEOREM_GEN_ALT = prove
 (`!r r' (f:A->B) j k.
        ring_epimorphism(r,r') f /\
        ring_ideal r j /\ ring_kernel (r,r') f SUBSET j /\ IMAGE f j = k
        ==> quotient_ring r j isomorphic_ring quotient_ring r' k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FIRST_RING_ISOMORPHISM_THEOREM_GEN THEN
  EXISTS_TAC `f:A->B` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[RING_EPIMORPHISM_IDEAL_CORRESPONDENCE_ALT]);;

(* ------------------------------------------------------------------------- *)
(* Prime and irreducible elements.                                           *)
(* ------------------------------------------------------------------------- *)

let ring_prime = new_definition
 `ring_prime r (p:A) <=>
        p IN ring_carrier r /\ ~(p = ring_0 r) /\ ~(ring_unit r p) /\
        !a b. a IN ring_carrier r /\
              b IN ring_carrier r /\
              ring_divides r p (ring_mul r a b)
              ==> ring_divides r p a \/ ring_divides r p b`;;

let ring_irreducible = new_definition
 `ring_irreducible r (p:A) <=>
        p IN ring_carrier r /\ ~(p = ring_0 r) /\ ~(ring_unit r p) /\
        !a b. a IN ring_carrier r /\
              b IN ring_carrier r /\
              ring_mul r a b = p
              ==> ring_unit r a \/ ring_unit r b`;;

let RING_PRIME_IN_CARRIER = prove
 (`!r a:A. ring_prime r a ==> a IN ring_carrier r`,
  SIMP_TAC[ring_prime]);;

let RING_IRREDUCIBLE_IN_CARRIER = prove
 (`!r a:A. ring_irreducible r a ==> a IN ring_carrier r`,
  SIMP_TAC[ring_irreducible]);;

let FIELD_PRIME = prove
 (`!r a:A. field r ==> ~(ring_prime r a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ring_prime; FIELD_DIVIDES; FIELD_UNIT] THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:A = ring_0 r` THEN ASM_REWRITE_TAC[]);;

let FIELD_IRREDUCIBLE = prove
 (`!r a:A. field r ==> ~(ring_irreducible r a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ring_irreducible; FIELD_DIVIDES; FIELD_UNIT] THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:A = ring_0 r` THEN ASM_REWRITE_TAC[]);;

let RING_ASSOCIATES_PRIME = prove
 (`!r a a':A.
        ring_associates r a a' ==> (ring_prime r a <=> ring_prime r a')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_prime] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_ASSOCIATES_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[RING_ASSOCIATES_EQ_0]; ALL_TAC] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[RING_ASSOCIATES_UNIT]; ALL_TAC] THEN
  ASM_MESON_TAC[RING_MUL; RING_ASSOCIATES_DIVIDES; RING_ASSOCIATES_REFL]);;

let RING_NONUNIT_DIVIDES_IRREDUCIBLE = prove
 (`!r p q:A.
        ~(ring_unit r p) /\
        ring_irreducible r q /\
        ring_divides r p q
        ==> ring_associates r p q`,
  SIMP_TAC[ring_irreducible; ring_associates] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:A`; `x:A`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC RING_DIVIDES_ASSOCIATES THEN
  ONCE_REWRITE_TAC[RING_ASSOCIATES_SYM] THEN
  ASM_SIMP_TAC[RING_ASSOCIATES_RMUL]);;

let RING_PRIME_DIVIDES_IRREDUCIBLE = prove
 (`!r p q:A.
        ring_prime r p /\
        ring_irreducible r q /\
        ring_divides r p q
        ==> ring_prime r q`,
  MESON_TAC[ring_prime; RING_ASSOCIATES_PRIME;
            RING_NONUNIT_DIVIDES_IRREDUCIBLE]);;

let RING_PRIME_DIVIDES_MUL = prove
 (`!r p a b:A.
        ring_prime r p /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_divides r p (ring_mul r a b) <=>
             ring_divides r p a \/ ring_divides r p b)`,
  MESON_TAC[ring_prime; RING_DIVIDES_RMUL; RING_DIVIDES_LMUL]);;

let RING_PRIME_DIVIDES_PRODUCT = prove
 (`!r p k (f:K->A).
        ring_prime r p /\ FINITE k /\ (!i. i IN k ==> f i IN ring_carrier r)
        ==> (ring_divides r p (ring_product r k f) <=>
             ?i. i IN k /\ ring_divides r p (f i))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT; EXISTS_IN_INSERT] THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; RING_DIVIDES_ONE] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ring_prime]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_PRIME_DIVIDES_MUL; RING_PRODUCT]);;

let INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE = prove
 (`!r p:A. integral_domain r /\ ring_prime r p ==> ring_irreducible r p`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_prime; ring_irreducible] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [DISJ_SYM] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`]) THEN
  ASM_REWRITE_TAC[RING_DIVIDES_REFL] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
  ASM_REWRITE_TAC[ring_divides; ring_unit] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
  EXISTS_TAC `r:A ring` THEN EXISTS_TAC `p:A` THEN
  ASM_SIMP_TAC[RING_MUL; RING_1; RING_MUL_RID] THEN
  ASM_MESON_TAC[RING_MUL_AC]);;

let INTEGRAL_DOMAIN_IRREDUCIBLE = prove
 (`!r a:A.
        integral_domain r
        ==> (ring_irreducible r a <=>
             a IN ring_carrier r /\
             ~(a = ring_0 r) /\
             ~ring_unit r a /\
             !d. ring_divides r d a
                 ==> ring_unit r d \/ ring_divides r a d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_irreducible] THEN
  REPEAT(MATCH_MP_TAC(TAUT `(p ==> (q <=> q')) ==> (p /\ q <=> p /\ q')`) THEN
         DISCH_TAC) THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV) [ring_divides] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN EQ_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:A` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:A` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
  ASM_CASES_TAC `ring_unit r (x:A)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THENL
   [ASM_MESON_TAC[RING_ASSOCIATES_RMUL; RING_DIVIDES_REFL;
                  RING_ASSOCIATES_DIVIDES; RING_ASSOCIATES_REFL];
    ASM_REWRITE_TAC[ring_divides; ring_unit] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `u:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SYM)) THEN
    ASM_SIMP_TAC[GSYM RING_MUL_ASSOC] THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`r:A ring`; `x:A`] THEN
    ASM_SIMP_TAC[RING_1; RING_MUL_RID; RING_MUL] THEN
    ASM_MESON_TAC[RING_MUL_LZERO]]);;

let INTEGRAL_DOMAIN_IRREDUCIBLE_ALT = prove
 (`!r a:A.
        integral_domain r
        ==> (ring_irreducible r a <=>
             a IN ring_carrier r /\
             ~(a = ring_0 r) /\
             ~ring_unit r a /\
             !d. ring_divides r d a
                 ==> ring_unit r d \/ ring_associates r d a)`,
  SIMP_TAC[ring_associates; INTEGRAL_DOMAIN_IRREDUCIBLE]);;

let INTEGRAL_DOMAIN_IRREDUCIBLE_DIVISORS = prove
 (`!r a:A.
         integral_domain r
         ==> (ring_irreducible r a <=>
              a IN ring_carrier r /\
              ~(a = ring_0 r) /\
              ~ring_unit r a /\
              !b c. b IN ring_carrier r /\ c IN ring_carrier r /\
                    ring_mul r b c = a
                    ==> ring_divides r a b \/ ring_divides r a c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral_domain; ring_irreducible] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `c:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:A`; `c:A`]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_DIVIDES_MUL_SELF] THEN
  ASM_MESON_TAC[RING_MUL_LZERO; RING_MUL_RZERO]);;

let RING_ASSOCIATES_IRREDUCIBLE = prove
 (`!r a a':A.
        integral_domain r /\ ring_associates r a a'
        ==> (ring_irreducible r a <=> ring_irreducible r a')`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTEGRAL_DOMAIN_IRREDUCIBLE_ALT] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_ASSOCIATES_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[RING_ASSOCIATES_EQ_0]; ALL_TAC] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[RING_ASSOCIATES_UNIT]; ALL_TAC] THEN
  ASM_MESON_TAC[ring_divides; RING_ASSOCIATES_DIVIDES; RING_ASSOCIATES_REFL;
                RING_ASSOCIATES_ASSOCIATES]);;

let INTEGRAL_DOMAIN_DIVIDES_PRIME_LMUL = prove
 (`!r p a b:A.
        integral_domain r /\ ring_prime r p /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ ~(ring_divides r p a)
        ==> (ring_divides r a (ring_mul r p b) <=> ring_divides r a b)`,
  REWRITE_TAC[ring_prime] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN ASM_SIMP_TAC[RING_DIVIDES_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [ring_divides] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `x:A`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[RING_DIVIDES_RMUL; RING_DIVIDES_REFL]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [ring_divides] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `y:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[ring_divides] THEN EXISTS_TAC `y:A` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
  MAP_EVERY EXISTS_TAC [`r:A ring`; `p:A`] THEN
  ASM_SIMP_TAC[RING_MUL] THEN ASM_SIMP_TAC[RING_MUL_AC]);;

let INTEGRAL_DOMAIN_DIVIDES_PRIME_RMUL = prove
 (`!r p a b:A.
        integral_domain r /\ ring_prime r p /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ ~(ring_divides r p a)
        ==> (ring_divides r a (ring_mul r b p) <=> ring_divides r a b)`,
  MESON_TAC[INTEGRAL_DOMAIN_DIVIDES_PRIME_LMUL; RING_MUL_SYM;
            RING_PRIME_IN_CARRIER]);;

let RING_IRREDUCIBLE_DIVIDES_OR_COPRIME = prove
 (`!r p a:A.
        ring_irreducible r p /\ a IN ring_carrier r
        ==> ring_divides r p a \/ ring_coprime r (p,a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ring_coprime; RING_IRREDUCIBLE_IN_CARRIER] THEN
  ASM_MESON_TAC[RING_NONUNIT_DIVIDES_IRREDUCIBLE; RING_ASSOCIATES_DIVIDES;
                RING_ASSOCIATES_REFL]);;

let RING_IRREDUCIBLE_COPRIME_EQ = prove
 (`!r p a:A.
        ring_irreducible r p
        ==> (ring_coprime r (p,a) <=>
             a IN ring_carrier r /\ ~(ring_divides r p a))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:A) IN ring_carrier r` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[RING_COPRIME_IN_CARRIER]] THEN
  EQ_TAC THENL
   [GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN DISCH_TAC;
    ASM_MESON_TAC[RING_IRREDUCIBLE_DIVIDES_OR_COPRIME]] THEN
  ASM_REWRITE_TAC[ring_coprime] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `p:A`)) THEN
  ASM_MESON_TAC[RING_DIVIDES_REFL; ring_irreducible]);;
let INTEGRAL_DOMAIN_PRIME_DIVIDES_OR_COPRIME = prove
 (`!r p a:A.
        integral_domain r /\ ring_prime r p /\ a IN ring_carrier r
        ==> ring_divides r p a \/ ring_coprime r (p,a)`,
  MESON_TAC[RING_IRREDUCIBLE_DIVIDES_OR_COPRIME;
            INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE]);;

let INTEGRAL_DOMAIN_PRIME_COPRIME_EQ = prove
 (`!r p a:A.
        integral_domain r /\ ring_prime r p
        ==> (ring_coprime r (p,a) <=>
             a IN ring_carrier r /\ ~(ring_divides r p a))`,
  MESON_TAC[RING_IRREDUCIBLE_COPRIME_EQ;
            INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE]);;

let RING_PRIME_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) a.
        ring_isomorphism(r,r') f /\ a IN ring_carrier r
        ==> (ring_prime r' (f a) <=> ring_prime r a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_prime] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o el 1 o CONJUNCTS o
    REWRITE_RULE[RING_ISOMORPHISM]) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_MUL
        (MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM th))]) THEN
  FIRST_ASSUM(fun th ->
   ASM_SIMP_TAC[RING_MUL; MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        RING_DIVIDES_ISOMORPHIC_IMAGE_EQ) th]) THEN
  BINOP_TAC THENL [ALL_TAC; ASM_MESON_TAC[RING_UNIT_ISOMORPHIC_IMAGE_EQ]] THEN
  ASM_MESON_TAC[RING_MONOMORPHISM_ALT_EQ;
                RING_ISOMORPHISM_IMP_MONOMORPHISM]);;

let RING_IRREDUCIBLE_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) a.
        ring_isomorphism(r,r') f /\ a IN ring_carrier r
        ==> (ring_irreducible r' (f a) <=> ring_irreducible r a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_irreducible] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o el 1 o CONJUNCTS o
    REWRITE_RULE[RING_ISOMORPHISM]) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_MUL
        (MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM th))]) THEN
  FIRST_ASSUM(fun th ->
   ASM_SIMP_TAC[MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        RING_UNIT_ISOMORPHIC_IMAGE_EQ) th]) THEN
  BINOP_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_ALT_EQ; RING_ISOMORPHISM_IMP_MONOMORPHISM];
    ALL_TAC] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[RING_UNIT_ISOMORPHIC_IMAGE_EQ]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
   ASM_SIMP_TAC[RING_MUL; MATCH_MP
    (ONCE_REWRITE_RULE[IMP_CONJ] RING_MONOMORPHISM_INJECTIVE_EQ)
       (MATCH_MP RING_ISOMORPHISM_IMP_MONOMORPHISM th)]));;

(* ------------------------------------------------------------------------- *)
(* Prime (not in general irreducible) factorizations are automatically       *)
(* unique, up to permutation and associates. Here we have several forms of   *)
(* that observation here, including one-way variants for divisibility, and   *)
(* with the refinement of only assuming irreducibility for one side.         *)
(* ------------------------------------------------------------------------- *)

let RING_DIVIDES_PRIMEFACTS_INJECTION = prove
 (`!r s (f:K->A) t (g:L->A).
        integral_domain r /\
        FINITE s /\ (!i. i IN s ==> ring_prime r (f i)) /\
        FINITE t /\ (!j. j IN t ==> ring_irreducible r (g j)) /\
        ring_divides r (ring_product r s f) (ring_product r t g)
        ==> ?h. IMAGE h s SUBSET t /\
                (!i j. i IN s /\ j IN s /\ h i = h j ==> i = j) /\
                (!i. i IN s ==> ring_associates r (f i) (g(h i)))`,
  REWRITE_TAC[INJECTIVE_ON_ALT; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; CARD_CLAUSES; LE_0] THEN
  MAP_EVERY X_GEN_TAC [`i:K`; `s:K->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `f:K->A` THEN STRIP_TAC THEN
  X_GEN_TAC `t:L->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `g:L->A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:K->A`) THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; RING_PRIME_IN_CARRIER] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   (REWRITE_RULE[CONJ_ASSOC] RING_DIVIDES_RMUL_REV))) THEN
  ASM_SIMP_TAC[RING_PRODUCT; RING_PRIME_IN_CARRIER] THEN
  ASM_SIMP_TAC[RING_PRIME_DIVIDES_PRODUCT; RING_IRREDUCIBLE_IN_CARRIER] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:L` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t DELETE (j:L)`; `g:L->A`]) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; CARD_DELETE; CARD_CLAUSES] THEN
  SUBGOAL_THEN `ring_associates r ((f:K->A) i) ((g:L->A) j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_NONUNIT_DIVIDES_IRREDUCIBLE; ring_prime]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `h:K->L` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\k. if k = i then j else (h:K->L) k` THEN
    ASM SET_TAC[]] THEN
  SUBGOAL_THEN
   `ring_divides r (ring_mul r (f i) (ring_product r s (f:K->A)))
                   (ring_mul r (f i) (ring_product r (t DELETE (j:L)) g))`
  MP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_DIVIDES_LMUL2;
                 RING_PRIME_IN_CARRIER; RING_PRODUCT] THEN
    ASM_MESON_TAC[ring_prime]] THEN
  TRANS_TAC RING_DIVIDES_TRANS
   `ring_mul r ((g:L->A) j) (ring_product r (t DELETE j) g)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        RING_DIVIDES_TRANS)) THEN
    MATCH_MP_TAC(MESON[RING_DIVIDES_REFL]
     `a IN ring_carrier r /\ b = a ==> ring_divides r a b`) THEN
    REWRITE_TAC[RING_PRODUCT] THEN
    ABBREV_TAC `u = t DELETE (j:L)` THEN
    SUBGOAL_THEN `t = (j:L) INSERT u` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "u" THEN
    ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_DELETE] THEN
    EXPAND_TAC "u" THEN REWRITE_TAC[IN_DELETE] THEN
    ASM_SIMP_TAC[RING_IRREDUCIBLE_IN_CARRIER];
    MATCH_MP_TAC RING_DIVIDES_RMUL2 THEN REWRITE_TAC[RING_PRODUCT] THEN
    MATCH_MP_TAC RING_DIVIDES_ASSOCIATES THEN
    ONCE_REWRITE_TAC[RING_ASSOCIATES_SYM] THEN
    ASM_REWRITE_TAC[]]);;

let RING_DIVIDES_PRIMEFACTS_INJECTION_EQ = prove
 (`!r s (f:K->A) t (g:L->A).
        integral_domain r /\
        FINITE s /\ (!i. i IN s ==> ring_prime r (f i)) /\
        FINITE t /\ (!j. j IN t ==> ring_irreducible r (g j))
        ==> (ring_divides r (ring_product r s f) (ring_product r t g) <=>
             ?h. IMAGE h s SUBSET t /\
                 (!i j. i IN s /\ j IN s /\ h i = h j ==> i = j) /\
                 (!i. i IN s ==> ring_associates r (f i) (g(h i))))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC RING_DIVIDES_PRIMEFACTS_INJECTION THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[INJECTIVE_ON_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:K->L` STRIP_ASSUME_TAC)] THEN
  TRANS_TAC RING_DIVIDES_TRANS
   `ring_product r (IMAGE (h:K->L) s) (g:L->A)` THEN
  ASM_SIMP_TAC[RING_DIVIDES_PRODUCT_SUBSET] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_IMAGE o rand o snd) THEN
  ASM_REWRITE_TAC[INJECTIVE_ON_ALT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_PRODUCT_RELATED THEN
  ASM_REWRITE_TAC[RING_DIVIDES_REFL; RING_1; o_THM] THEN
  SIMP_TAC[RING_DIVIDES_MUL2] THEN RULE_ASSUM_TAC
   (REWRITE_RULE[ring_associates; ring_prime; ring_irreducible]) THEN
  ASM SET_TAC[]);;

let RING_DIVIDES_PRIMEFACTS_LE = prove
 (`!r s (f:K->A) t (g:L->A).
        integral_domain r /\
        FINITE s /\ (!i. i IN s ==> ring_prime r (f i)) /\
        FINITE t /\ (!j. j IN t ==> ring_irreducible r (g j)) /\
        ring_divides r (ring_product r s f) (ring_product r t g)
        ==> CARD s <= CARD t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_DIVIDES_PRIMEFACTS_INJECTION) THEN
  REWRITE_TAC[INJECTIVE_ON_ALT; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h:K->L` THEN DISCH_TAC THEN
  TRANS_TAC LE_TRANS `CARD(IMAGE (h:K->L) s)` THEN
  ASM_SIMP_TAC[CARD_SUBSET] THEN MATCH_MP_TAC EQ_IMP_LE THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_REWRITE_TAC[INJECTIVE_ON_ALT]);;

let RING_ASSOCIATES_PRIMEFACTS_BIJECTION = prove
 (`!r s (f:K->A) t (g:L->A).
        integral_domain r /\
        FINITE s /\ (!i. i IN s ==> ring_prime r (f i)) /\
        FINITE t /\ (!j. j IN t ==> ring_irreducible r (g j)) /\
        ring_associates r (ring_product r s f) (ring_product r t g)
        ==> ?h. IMAGE h s = t /\
                (!i j. i IN s /\ j IN s /\ h i = h j ==> i = j) /\
                (!i. i IN s ==> ring_associates r (f i) (g(h i)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:K->bool`; `f:K->A`; `t:L->bool`; `g:L->A`]
        RING_DIVIDES_PRIMEFACTS_INJECTION) THEN
  REWRITE_TAC[INJECTIVE_ON_ALT] THEN
  ASM_SIMP_TAC[RING_DIVIDES_ASSOCIATES] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:K->L` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC
   (SET_RULE `s SUBSET t /\ (~(t DIFF s = {}) ==> F) ==> s = t`) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `ring_associates r
        (ring_product r s (f:K->A))
        (ring_mul r (ring_product r s f)
                    (ring_product r (t DIFF IMAGE (h:K->L) s) g))`
  MP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_DIVIDES_ASSOCIATES_MUL_SELF; RING_PRODUCT;
       RING_UNIT_PRODUCT; FINITE_DIFF; INTEGRAL_DOMAIN_PRODUCT_EQ_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_prime; ring_irreducible]) THEN
    ASM SET_TAC[]] THEN
  TRANS_TAC RING_ASSOCIATES_TRANS
   `ring_mul r (ring_product r (IMAGE h s) g)
               (ring_product r (t DIFF IMAGE (h:K->L) s) g):A` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_PRODUCT_UNION; FINITE_DIFF; FINITE_IMAGE;
                 SET_RULE `DISJOINT s (t DIFF s)`] THEN
    ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s UNION (t DIFF s) = t`];
    MATCH_MP_TAC RING_ASSOCIATES_MUL THEN
    REWRITE_TAC[RING_ASSOCIATES_REFL; RING_PRODUCT] THEN
    ASM_SIMP_TAC[RING_PRODUCT_IMAGE; INJECTIVE_ON_ALT] THEN
    MATCH_MP_TAC RING_ASSOCIATES_PRODUCT THEN
    ASM_REWRITE_TAC[o_DEF] THEN ASM_MESON_TAC[RING_ASSOCIATES_SYM]]);;

let RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS = prove
 (`!r s (f:K->A) t (g:L->A).
        integral_domain r /\
        FINITE s /\ (!i. i IN s ==> ring_prime r (f i)) /\
        FINITE t /\ (!j. j IN t ==> ring_irreducible r (g j)) /\
        ring_associates r (ring_product r s f) (ring_product r t g)
        ==> ?h k. IMAGE h s = t /\ IMAGE k t = s /\
                  (!i. i IN s ==> k(h i) = i) /\
                  (!j. j IN t ==> h(k j) = j) /\
                  (!i. i IN s ==> ring_associates r (f i) (g(h i))) /\
                  (!j. j IN t ==> ring_associates r (g j) (f(k j)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_ASSOCIATES_PRIMEFACTS_BIJECTION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:K->L` THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `k:L->K` THEN
  GEN_REWRITE_TAC (funpow 6 RAND_CONV o ONCE_DEPTH_CONV)
   [RING_ASSOCIATES_SYM] THEN
  SET_TAC[]);;

let RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS_EQ = prove
 (`!r s (f:K->A) t (g:L->A).
        integral_domain r /\
        FINITE s /\ (!i. i IN s ==> ring_prime r (f i)) /\
        FINITE t /\ (!j. j IN t ==> ring_irreducible r (g j))
        ==> (ring_associates r (ring_product r s f) (ring_product r t g) <=>
             ?h k. IMAGE h s = t /\ IMAGE k t = s /\
                   (!i. i IN s ==> k(h i) = i) /\
                   (!j. j IN t ==> h(k j) = j) /\
                   (!i. i IN s ==> ring_associates r (f i) (g(h i))) /\
                   (!j. j IN t ==> ring_associates r (g j) (f(k j))))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS] THEN STRIP_TAC THEN
  UNDISCH_THEN `IMAGE (h:K->L) s = t` (SUBST1_TAC o SYM) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_IMAGE o rand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_ASSOCIATES_PRODUCT THEN ASM_REWRITE_TAC[o_THM]);;

let RING_ASSOCIATES_PRIMEFACTS_BIJECTION_EQ = prove
 (`!r s (f:K->A) t (g:L->A).
        integral_domain r /\
        FINITE s /\ (!i. i IN s ==> ring_prime r (f i)) /\
        FINITE t /\ (!j. j IN t ==> ring_irreducible r (g j))
        ==> (ring_associates r (ring_product r s f) (ring_product r t g) <=>
             ?h. IMAGE h s = t /\
                 (!i j. i IN s /\ j IN s /\ h i = h j ==> i = j) /\
                 (!i. i IN s ==> ring_associates r (f i) (g(h i))))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_ASSOCIATES_PRIMEFACTS_BIJECTIONS_EQ] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 5 RAND_CONV o ONCE_DEPTH_CONV)
   [RING_ASSOCIATES_SYM] THEN
  ASM SET_TAC[]);;

let RING_ASSOCIATES_PRIMEFACTS_EQ = prove
 (`!r s (f:K->A) t (g:L->A).
        integral_domain r /\
        FINITE s /\ (!i. i IN s ==> ring_prime r (f i)) /\
        FINITE t /\ (!j. j IN t ==> ring_irreducible r (g j)) /\
        ring_associates r (ring_product r s f) (ring_product r t g)
        ==> CARD s = CARD t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_ASSOCIATES_PRIMEFACTS_BIJECTION) THEN
  REWRITE_TAC[INJECTIVE_ON_ALT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[]);;

let RING_DIVIDES_PRIMEFACTS_LT = prove
 (`!r s (f:K->A) t (g:L->A).
        integral_domain r /\
        FINITE s /\ (!i. i IN s ==> ring_prime r (f i)) /\
        FINITE t /\ (!j. j IN t ==> ring_irreducible r (g j)) /\
        ring_divides r (ring_product r s f) (ring_product r t g) /\
        ~(ring_divides r (ring_product r t g) (ring_product r s f))
        ==> CARD s < CARD t`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 5 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[MESON[ring_associates]
   `ring_divides r x y /\ ~(ring_divides r y x) <=>
    ring_divides r x y /\ ~(ring_associates r x y)`] THEN
  ASM_SIMP_TAC[RING_DIVIDES_PRIMEFACTS_INJECTION_EQ;
               RING_ASSOCIATES_PRIMEFACTS_BIJECTION_EQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `(?x. P x) /\ ~(?x. Q x) ==> ?x. P x /\ ~Q x`)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; INJECTIVE_ON_ALT] THEN
  X_GEN_TAC `h:K->L` THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TRANS_TAC LET_TRANS `CARD(IMAGE (h:K->L) s)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Multiplicative system in a ring.                                          *)
(* ------------------------------------------------------------------------- *)

let ring_multsys = new_definition
 `ring_multsys (r:A ring) s <=>
        s SUBSET ring_carrier r /\
        ring_1 r IN s /\
        (!x y. x IN s /\ y IN s ==> ring_mul r x y IN s)`;;

let RING_MULTSYS_IMP_SUBSET = prove
 (`!r s:A->bool. ring_multsys r s ==> s SUBSET ring_carrier r`,
  SIMP_TAC[ring_multsys]);;

let RING_MULTSYS_IMP_NONEMPTY = prove
 (`!r s:A->bool. ring_multsys r s ==> ~(s = {})`,
  MESON_TAC[ring_multsys; NOT_IN_EMPTY]);;

let RING_MULYSYS_1 = prove
 (`!r:A ring. ring_multsys r {ring_1 r}`,
  GEN_TAC THEN REWRITE_TAC[ring_multsys; SING_SUBSET; IN_SING] THEN
  SIMP_TAC[RING_1; RING_MUL_LID]);;

let RING_MULYSYS_CARRIER = prove
 (`!r:A ring. ring_multsys r (ring_carrier r)`,
  GEN_TAC THEN REWRITE_TAC[ring_multsys; SUBSET_REFL] THEN
  SIMP_TAC[RING_1; RING_MUL]);;

let RING_MULTSYS_REGULAR = prove
 (`!r:A ring.
        ring_multsys r {a | ring_regular r a}`,
  GEN_TAC THEN REWRITE_TAC[ring_multsys; IN_ELIM_THM] THEN
  REWRITE_TAC[RING_REGULAR_MUL; RING_REGULAR_1] THEN
  REWRITE_TAC[ring_regular] THEN SET_TAC[]);;

let RING_MULTSYS_NONZERO = prove
 (`!r:A ring.
        ring_multsys r (ring_carrier r DIFF {ring_0 r}) <=>
        integral_domain r`,
  REWRITE_TAC[ring_multsys; IN_DIFF; IN_SING; integral_domain] THEN
  GEN_TAC THEN SIMP_TAC[RING_MUL; RING_1] THEN SET_TAC[]);;

let RING_MULTSYS_POWERS = prove
 (`!r x:A. x IN ring_carrier r
           ==> ring_multsys r {ring_pow r x n | n IN (:num)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_multsys] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[GSYM RING_POW_ADD] THEN
  ASM_MESON_TAC[RING_POW; ring_pow]);;

let RING_MULTSYS_UNITS = prove
 (`!r:A ring. ring_multsys r {u | ring_unit r u}`,
  SIMP_TAC[ring_multsys; IN_ELIM_THM; SUBSET; RING_UNIT_MUL; RING_UNIT_1] THEN
  SIMP_TAC[ring_unit]);;

let RING_MULTSYS_IDEMPOT = prove
 (`!r x:A.
        x IN ring_carrier r /\ ring_mul r x x = x
        ==> ring_multsys r {ring_1 r,x}`,
  REWRITE_TAC[ring_multsys; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IMP_IMP] THEN
  SIMP_TAC[IN_INSERT; NOT_IN_EMPTY; INSERT_SUBSET; EMPTY_SUBSET] THEN
  SIMP_TAC[RING_1; RING_MUL_LID; RING_MUL_RID]);;

let RING_MULTSYS_INTERS = prove
 (`!r gs.
         (!g. g IN gs ==> ring_multsys r g) /\ ~(gs = {})
         ==> ring_multsys r (INTERS gs)`,
  REWRITE_TAC[ring_multsys; SUBSET; IN_INTERS] THEN SET_TAC[]);;

let RING_MULTSYS_INTER = prove
 (`!r s t:A->bool.
        ring_multsys r s /\ ring_multsys r t ==> ring_multsys r (s INTER t)`,
  REWRITE_TAC[ring_multsys] THEN SET_TAC[]);;

let RING_POW_IN_MULTSYS = prove
 (`!r s (x:A) n.
        ring_multsys r s /\ x IN s ==> ring_pow r x n IN s`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; ring_multsys] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ring_pow]);;

let RING_MULTSYS_NILPOTENT_EXISTS = prove
 (`!r s:A->bool.
        ring_multsys r s
        ==> ((?x. ring_nilpotent r x /\ x IN s) <=> ring_0 r IN s)`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[RING_NILPOTENT_0]] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_nilpotent]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num`
   (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
  ASM_SIMP_TAC[RING_POW_IN_MULTSYS]);;

(* ------------------------------------------------------------------------- *)
(* Localization, special case of total ring or field of fractions.           *)
(* ------------------------------------------------------------------------- *)

let ring_localequiv = new_definition
 `ring_localequiv r s (a,b) (a',b') <=>
        a IN ring_carrier r /\ a' IN ring_carrier r /\ b IN s /\ b' IN s /\
        ?u. u IN s /\
            ring_mul r u (ring_sub r (ring_mul r a b') (ring_mul r a' b)) =
            ring_0 r`;;

let RING_LOCALEQUIV = prove
 (`!r s a b a' b':A.
      ring_multsys r s
      ==> (ring_localequiv r s (a,b) (a',b') <=>
           a IN ring_carrier r /\ a' IN ring_carrier r /\
           b IN ring_carrier r /\ b' IN ring_carrier r /\
           b IN s /\ b' IN s /\
           ?u. u IN s /\
               ring_mul r u (ring_sub r (ring_mul r a b') (ring_mul r a' b)) =
               ring_0 r)`,
  REWRITE_TAC[ring_multsys; ring_localequiv; SUBSET] THEN MESON_TAC[]);;

let RING_LOCALEQUIV_REFL = prove
 (`!r s a b:A.
        ring_multsys r s
        ==> (ring_localequiv r s (a,b) (a,b) <=>
             a IN ring_carrier r /\ b IN s)`,
  REWRITE_TAC[ring_multsys; SUBSET] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[ring_localequiv] THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN
  ASM_CASES_TAC `(b:A) IN s` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RING_MUL; RING_SUB_REFL] THEN
  ASM_MESON_TAC[RING_MUL_RZERO]);;

let RING_LOCALEQUIV_SYM = prove
 (`!r s a b a' b':A.
        ring_multsys r s
        ==> (ring_localequiv r s (a,b) (a',b') <=>
             ring_localequiv r s (a',b') (a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_multsys; SUBSET] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REWRITE_TAC[ring_localequiv; RIGHT_AND_EXISTS_THM] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN RING_TAC THEN ASM SET_TAC[]);;

let RING_LOCALEQUIV_TRANS = prove
 (`!r s a b a' b' a'' b'':A.
        ring_multsys r s /\
        ring_localequiv r s (a,b) (a',b') /\
        ring_localequiv r s (a',b') (a'',b'')
        ==> ring_localequiv r s (a,b) (a'',b'')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_multsys] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ring_localequiv; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `u:A` THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `v:A` THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `ring_mul r b' (ring_mul r u v):A` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; RING_TAC THEN ASM SET_TAC[]]);;

let RING_LOCALEQUIV_EQUIV = prove
 (`!r s a b a' b'.
        ring_multsys r s /\
        a IN ring_carrier r /\ a' IN ring_carrier r /\ b IN s /\ b' IN s
        ==> (ring_localequiv r s (a,b) (a',b') <=>
             ring_localequiv r s (a,b) = ring_localequiv r s (a',b'))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[RING_LOCALEQUIV_REFL; RING_LOCALEQUIV_SYM;
                RING_LOCALEQUIV_TRANS]);;

let RING_LOCALEQUIV_NEG = prove
 (`!r s a b a' b':A.
        ring_multsys r s /\
        ring_localequiv r s (a,b) (a',b')
        ==> ring_localequiv r s (ring_neg r a,b) (ring_neg r a',b')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_multsys] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ring_localequiv; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `u:A` THEN
  REPEAT DISCH_TAC THEN ASM_SIMP_TAC[RING_NEG] THEN
  EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[] THEN
  RING_TAC THEN ASM SET_TAC[]);;

let RING_LOCALEQUIV_ADD = prove
 (`!r s a1 b1 a1' b1' a2 b2 a2' b2':A.
        ring_multsys r s /\
        ring_localequiv r s (a1,b1) (a1',b1') /\
        ring_localequiv r s (a2,b2) (a2',b2')
        ==> ring_localequiv r s
             (ring_add r (ring_mul r a1 b2) (ring_mul r a2 b1),
              ring_mul r b1 b2)
             (ring_add r (ring_mul r a1' b2') (ring_mul r a2' b1'),
              ring_mul r b1' b2')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_multsys; SUBSET] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ring_localequiv; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `u:A` THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `v:A` THEN
  REPEAT DISCH_TAC THEN ASM_SIMP_TAC[RING_MUL; RING_ADD] THEN
  EXISTS_TAC `ring_mul r u v:A` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; RING_TAC THEN ASM SET_TAC[]]);;

let RING_LOCALEQUIV_MUL = prove
 (`!r s a1 b1 a1' b1' a2 b2 a2' b2':A.
        ring_multsys r s /\
        ring_localequiv r s (a1,b1) (a1',b1') /\
        ring_localequiv r s (a2,b2) (a2',b2')
        ==> ring_localequiv r s
             (ring_mul r a1 a2,ring_mul r b1 b2)
             (ring_mul r a1' a2',ring_mul r b1' b2')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_multsys] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[ring_localequiv; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `u:A` THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `v:A` THEN
  REPEAT DISCH_TAC THEN ASM_SIMP_TAC[RING_MUL] THEN
  EXISTS_TAC `ring_mul r u v:A` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; RING_TAC THEN ASM SET_TAC[]]);;

let ring_localization = new_definition
 `ring_localization (r:A ring) s =
        ring({ring_localequiv r s (a,b) |a,b| a IN ring_carrier r /\ b IN s},
             ring_localequiv r s (ring_0 r,ring_1 r),
             ring_localequiv r s (ring_1 r,ring_1 r),
             (@f. !a b. a IN ring_carrier r /\ b IN s
                      ==> f (ring_localequiv r s (a,b)) =
                          ring_localequiv r s (ring_neg r a,b)),
             (@f. !a1 b1 a2 b2.
                        a1 IN ring_carrier r /\ b1 IN s /\
                        a2 IN ring_carrier r /\ b2 IN s
                        ==> f (ring_localequiv r s (a1,b1))
                              (ring_localequiv r s (a2,b2)) =
                            ring_localequiv r s
                             (ring_add r (ring_mul r a1 b2) (ring_mul r a2 b1),
                              ring_mul r b1 b2)),
             (@f. !a1 b1 a2 b2.
                        a1 IN ring_carrier r /\ b1 IN s /\
                        a2 IN ring_carrier r /\ b2 IN s
                        ==> f (ring_localequiv r s (a1,b1))
                              (ring_localequiv r s (a2,b2)) =
                            ring_localequiv r s
                              (ring_mul r a1 a2,ring_mul r b1 b2)))`;;

let [RING_LOCALIZATION; RING_LOCALIZATION_NEG; RING_LOCALIZATION_ADD],
    RING_LOCALIZATION_MUL =
  let lemma = prove
   (`!(r:A->B) P.
     (!x x' y y'.
          P x y /\ P x' y' /\ r x = r x' /\ r y = r y'
          ==> r (f x y) = r (f x' y'))
      ==> ?g. !x y. P x y ==> g (r x) (r y) = r (f x y)`,
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[MESON[]
     `(!x y. P x y ==> g (r x) (r y) = r (f x y)) <=>
      (!w z x y. P x y /\ r x = w /\ r y = z ==> g w z = r (f x y))`] THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN ASM_METIS_TAC[]) in
  let localization_neg_exists = prove
   (`!r s:A->bool.
          ring_multsys r s
          ==> ?f. !a b. a IN ring_carrier r /\ b IN s
                        ==> f (ring_localequiv r s (a,b)) =
                            ring_localequiv r s (ring_neg r a,b)`,
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC BINDER_CONV [FORALL_UNPAIR_THM] THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [EQ_SYM_EQ] THEN
    REWRITE_TAC[GSYM FUNCTION_FACTORS_LEFT_GEN] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
    REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[GSYM RING_LOCALEQUIV_EQUIV; RING_NEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC RING_LOCALEQUIV_NEG THEN ASM_REWRITE_TAC[])
  and localization_mul_exists = prove
   (`!r s:A->bool.
          ring_multsys r s
          ==> ?f. !a1 b1 a2 b2.
                        a1 IN ring_carrier r /\ b1 IN s /\
                        a2 IN ring_carrier r /\ b2 IN s
                        ==> f (ring_localequiv r s (a1,b1))
                              (ring_localequiv r s (a2,b2)) =
                            ring_localequiv r s
                              (ring_mul r a1 a2,ring_mul r b1 b2)`,
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC BINDER_CONV [FORALL_UNPAIR_THM] THEN
    GEN_REWRITE_TAC (BINDER_CONV o BINDER_CONV) [FORALL_UNPAIR_THM] THEN
    REWRITE_TAC[PAIR] THEN
    MATCH_MP_TAC(ISPEC `ring_localequiv (r:A ring) s` lemma) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
    REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_multsys]) THEN
    ASM_SIMP_TAC[GSYM RING_LOCALEQUIV_EQUIV; RING_MUL] THEN STRIP_TAC THEN
    MATCH_MP_TAC RING_LOCALEQUIV_MUL THEN ASM_REWRITE_TAC[])
  and localization_add_exists = prove
   (`!r s:A->bool.
          ring_multsys r s
          ==> ?f. !a1 b1 a2 b2.
                        a1 IN ring_carrier r /\ b1 IN s /\
                        a2 IN ring_carrier r /\ b2 IN s
                        ==> f (ring_localequiv r s (a1,b1))
                              (ring_localequiv r s (a2,b2)) =
                            ring_localequiv r s
                             (ring_add r (ring_mul r a1 b2) (ring_mul r a2 b1),
                              ring_mul r b1 b2)`,
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC BINDER_CONV [FORALL_UNPAIR_THM] THEN
    GEN_REWRITE_TAC (BINDER_CONV o BINDER_CONV) [FORALL_UNPAIR_THM] THEN
    REWRITE_TAC[PAIR] THEN
    MATCH_MP_TAC(ISPEC `ring_localequiv (r:A ring) s` lemma) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
    REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_multsys]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
      [GSYM RING_LOCALEQUIV_EQUIV; RING_MUL; RING_ADD] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC RING_LOCALEQUIV_ADD THEN ASM_REWRITE_TAC[]) in
 (splitlist CONJ_PAIR o prove)
 (`((!r s:A->bool.
         ring_multsys r s
         ==> ring_carrier (ring_localization r s) =
             { ring_localequiv r s (a,b) |a,b|
               a IN ring_carrier r /\ b IN s}) /\
    (!r s:A->bool.
         ring_multsys r s
         ==> ring_0 (ring_localization r s) =
             ring_localequiv r s (ring_0 r,ring_1 r)) /\
    (!r s:A->bool.
         ring_multsys r s
         ==> ring_1 (ring_localization r s) =
             ring_localequiv r s (ring_1 r,ring_1 r)) /\
    (!r s:A->bool.
         ring_multsys r s
         ==> ring_neg (ring_localization r s) =
             @f. !a b. a IN ring_carrier r /\ b IN s
                       ==> f (ring_localequiv r s (a,b)) =
                           ring_localequiv r s (ring_neg r a,b)) /\
    (!r s:A->bool.
         ring_multsys r s
         ==> ring_add (ring_localization r s) =
             @f. !a1 b1 a2 b2.
                        a1 IN ring_carrier r /\ b1 IN s /\
                        a2 IN ring_carrier r /\ b2 IN s
                        ==> f (ring_localequiv r s (a1,b1))
                              (ring_localequiv r s (a2,b2)) =
                            ring_localequiv r s
                             (ring_add r (ring_mul r a1 b2) (ring_mul r a2 b1),
                              ring_mul r b1 b2)) /\
     (!r s:A->bool.
         ring_multsys r s
         ==> ring_mul (ring_localization r s) =
             @f. !a1 b1 a2 b2.
                        a1 IN ring_carrier r /\ b1 IN s /\
                        a2 IN ring_carrier r /\ b2 IN s
                        ==> f (ring_localequiv r s (a1,b1))
                              (ring_localequiv r s (a2,b2)) =
                            ring_localequiv r s
                              (ring_mul r a1 a2,ring_mul r b1 b2))) /\
   ((!r s a b:A.
        ring_multsys r s /\ a IN ring_carrier r /\ b IN s
        ==> ring_neg (ring_localization r s) (ring_localequiv r s (a,b)) =
            ring_localequiv r s (ring_neg r a,b)) /\
    (!r s a1 b1 a2 b2:A.
        ring_multsys r s /\
        a1 IN ring_carrier r /\ b1 IN s /\
        a2 IN ring_carrier r /\ b2 IN s
        ==> ring_add (ring_localization r s)
             (ring_localequiv r s (a1,b1)) (ring_localequiv r s (a2,b2)) =
            ring_localequiv r s
             (ring_add r (ring_mul r a1 b2) (ring_mul r a2 b1),
              ring_mul r b1 b2)) /\
    (!r s a1 b1 a2 b2:A.
        ring_multsys r s /\
        a1 IN ring_carrier r /\ b1 IN s /\
        a2 IN ring_carrier r /\ b2 IN s
        ==> ring_mul (ring_localization r s)
             (ring_localequiv r s (a1,b1)) (ring_localequiv r s (a2,b2)) =
            ring_localequiv r s (ring_mul r a1 a2, ring_mul r b1 b2)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM AND_FORALL_THM] THEN
  ASM_CASES_TAC `ring_multsys r (s:A->bool)` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
   [`lneg = @f. !a b:A. a IN ring_carrier r /\ b IN s
                        ==> f (ring_localequiv r s (a,b)) =
                            ring_localequiv r s (ring_neg r a,b)`;
    `ladd =  @f. !a1 b1 a2 b2:A.
                        a1 IN ring_carrier r /\ b1 IN s /\
                        a2 IN ring_carrier r /\ b2 IN s
                        ==> f (ring_localequiv r s (a1,b1))
                              (ring_localequiv r s (a2,b2)) =
                            ring_localequiv r s
                             (ring_add r (ring_mul r a1 b2) (ring_mul r a2 b1),
                              ring_mul r b1 b2)`;
    `lmul =  @f. !a1 b1 a2 b2:A.
                        a1 IN ring_carrier r /\ b1 IN s /\
                        a2 IN ring_carrier r /\ b2 IN s
                        ==> f (ring_localequiv r s (a1,b1))
                              (ring_localequiv r s (a2,b2)) =
                            ring_localequiv r s
                             (ring_mul r a1 a2,ring_mul r b1 b2)`] THEN
  FIRST_ASSUM(MP_TAC o SELECT_RULE o MATCH_MP localization_neg_exists) THEN
  FIRST_ASSUM(MP_TAC o SELECT_RULE o MATCH_MP localization_add_exists) THEN
  FIRST_ASSUM(MP_TAC o SELECT_RULE o MATCH_MP localization_mul_exists) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [DISCH_THEN(fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
  GEN_REWRITE_TAC (DEPTH_BINOP_CONV `/\` o LAND_CONV o ONCE_DEPTH_CONV)
   [ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul] THEN
  PURE_REWRITE_TAC[GSYM PAIR_EQ; BETA_THM; PAIR] THEN
  ASM_REWRITE_TAC[ring_localization; GSYM(CONJUNCT2 ring_tybij)] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_multsys; SUBSET]) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
  REPLICATE_TAC 3
   (CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[RING_0; RING_1; RING_NEG];
      ALL_TAC]) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a1:A`; `b1:A`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`a2:A`; `b2:A`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `ring_add r (ring_mul r a1 b2) (ring_mul r a2 b1):A` THEN
    EXISTS_TAC `ring_mul r b1 b2:A` THEN
    ASM_MESON_TAC[RING_ADD; RING_MUL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[RING_MUL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  MP_TAC(GSYM(ISPECL [`r:A ring`; `s:A->bool`] RING_LOCALEQUIV_EQUIV)) THEN
  ASM_REWRITE_TAC[ring_multsys; SUBSET] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 6)
   [RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
  DISCH_THEN(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[ring_localequiv] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
  EXISTS_TAC `ring_1 r:A` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN RING_TAC THEN ASM SET_TAC[]);;

let RING_LOCALIZATION_CARRIER = prove
 (`!r s:A->bool.
        ring_multsys r s
        ==> ring_carrier (ring_localization r s) =
             { ring_localequiv r s (a,b) |a,b|
               a IN ring_carrier r /\ b IN s}`,
  REWRITE_TAC[RING_LOCALIZATION]);;

let RING_LOCALIZATION_0 = prove
 (`!r s:A->bool.
        ring_multsys r s
        ==> ring_0 (ring_localization r s) =
             ring_localequiv r s (ring_0 r,ring_1 r)`,
  REWRITE_TAC[RING_LOCALIZATION]);;

let RING_LOCALIZATION_1 = prove
 (`!r s:A->bool.
        ring_multsys r s
        ==> ring_1 (ring_localization r s) =
             ring_localequiv r s (ring_1 r,ring_1 r)`,
  REWRITE_TAC[RING_LOCALIZATION]);;

let TRIVIAL_RING_LOCALIZATION = prove
 (`!r s:A->bool.
        ring_multsys r s
        ==> (trivial_ring(ring_localization r s) <=> ring_0 r IN s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [ring_multsys]) THEN
  ASM_SIMP_TAC[TRIVIAL_RING_10; RING_LOCALIZATION_1; RING_LOCALIZATION_0;
    GSYM RING_LOCALEQUIV_EQUIV; RING_0; RING_1; ring_localequiv] THEN
  SIMP_TAC[RING_1; RING_0; RING_MUL_RID; RING_SUB_RZERO] THEN
  ASM_MESON_TAC[RING_MUL_RID; RING_MUL_LID; SUBSET]);;

let RING_LOCALEQUIV_IN_CARRIER = prove
 (`!r s a b:A.
        ring_multsys r s /\ a IN ring_carrier r /\ b IN s
        ==> ring_localequiv r s (a,b) IN ring_carrier(ring_localization r s)`,
  SIMP_TAC[RING_LOCALIZATION_CARRIER] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let RING_UNIT_LOCALEQUIV = prove
 (`!r s a b:A.
        ring_multsys r s /\ a IN s /\ b IN s
        ==> ring_unit (ring_localization r s) (ring_localequiv r s (a,b))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_multsys]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[ring_unit; RING_LOCALEQUIV_IN_CARRIER] THEN
  EXISTS_TAC `ring_localequiv r s (b:A,a)` THEN
  ASM_SIMP_TAC[RING_LOCALEQUIV_IN_CARRIER] THEN
  ASM_SIMP_TAC[RING_LOCALIZATION_MUL; RING_LOCALIZATION_1] THEN
  ASM_SIMP_TAC[GSYM RING_LOCALEQUIV_EQUIV; RING_MUL_LID; RING_MUL_RID] THEN
  ASM_SIMP_TAC[ring_localequiv; RING_1] THEN
  EXISTS_TAC `ring_1 r:A` THEN ASM_REWRITE_TAC[] THEN
  RING_TAC THEN ASM_SIMP_TAC[]);;

let RING_LOCALEQUIV_EQ_0_GEN = prove
 (`!r s a b:A.
        ring_multsys r s /\ a IN ring_carrier r /\ b IN s
        ==> (ring_localequiv r s (a,b) = ring_0(ring_localization r s) <=>
             ?c. c IN s /\ ring_mul r c a = ring_0 r)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_multsys]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[RING_LOCALIZATION_0; GSYM RING_LOCALEQUIV_EQUIV; RING_0] THEN
  ASM_SIMP_TAC[ring_localequiv; RING_0; RING_MUL_RID; RING_MUL_LZERO] THEN
  ASM_SIMP_TAC[RING_SUB_RZERO]);;

let ring_fractionate = new_definition
 `ring_fractionate r s = \x:A. ring_localequiv r s (x,ring_1 r)`;;

let RING_FRACTIONATE_IN_CARRIER = prove
 (`!r s a:A.
        ring_multsys r s /\ a IN ring_carrier r
        ==> ring_fractionate r s a IN ring_carrier (ring_localization r s)`,
  SIMP_TAC[RING_LOCALIZATION_CARRIER; ring_fractionate] THEN
  REWRITE_TAC[IN_ELIM_THM; ring_multsys] THEN MESON_TAC[]);;

let RING_UNIT_FRACTIONATE = prove
 (`!r s a:A.
        ring_multsys r s /\ a IN s
        ==> ring_unit (ring_localization r s) (ring_fractionate r s a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_fractionate] THEN
  MATCH_MP_TAC RING_UNIT_LOCALEQUIV THEN ASM_MESON_TAC[ring_multsys]);;

let RING_FRACTIONATE_EQ_0_GEN = prove
 (`!r s a:A.
        ring_multsys r s /\ a IN ring_carrier r
        ==> (ring_fractionate r s a = ring_0(ring_localization r s) <=>
             ?c. c IN s /\ ring_mul r c a = ring_0 r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_fractionate] THEN
  MATCH_MP_TAC RING_LOCALEQUIV_EQ_0_GEN THEN ASM_MESON_TAC[ring_multsys]);;

let RING_HOMOMORPHISM_FRACTIONATE = prove
 (`!r s:A->bool.
      ring_multsys r s
      ==> ring_homomorphism (r,ring_localization r s) (ring_fractionate r s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_fractionate] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ring_multsys; SUBSET]) THEN
  ASM_SIMP_TAC[ring_homomorphism; RING_LOCALIZATION_CARRIER] THEN
  ASM_SIMP_TAC[RING_LOCALIZATION_0; RING_LOCALIZATION_1] THEN
  ASM_SIMP_TAC[RING_LOCALIZATION_NEG; SUBSET; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[RING_LOCALIZATION_ADD; RING_LOCALIZATION_MUL] THEN
  SIMP_TAC[RING_MUL_RID; RING_1] THEN ASM SET_TAC[]);;

let RING_MONOMORPHISM_FRACTIONATE_GEN = prove
 (`!r s:A->bool.
      ring_multsys r s
      ==> (ring_monomorphism (r,ring_localization r s)
                             (ring_fractionate r s) <=>
           s SUBSET {a | ring_regular r a})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ring_multsys; SUBSET]) THEN
  ASM_SIMP_TAC[ring_monomorphism; RING_HOMOMORPHISM_FRACTIONATE] THEN
  REWRITE_TAC[ring_fractionate; IMP_CONJ] THEN
  ASM_SIMP_TAC[GSYM RING_LOCALEQUIV_EQUIV; ring_localequiv] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[ring_regular; ring_zerodivisor] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `a:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `ring_0 r:A`; `a:A`]) THEN
    ASM_SIMP_TAC[RING_0; RING_MUL_RID; RING_SUB_RZERO];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `a:A`] THEN
    SIMP_TAC[IMP_CONJ; RING_MUL_RID] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `ring_sub r x y:A`) THEN
    ASM_SIMP_TAC[RING_SUB_EQ_0; RING_SUB]]);;

let RING_ISOMORPHISM_FRACTIONATE_GEN = prove
 (`!r s:A->bool.
      ring_multsys r s
      ==> (ring_isomorphism (r,ring_localization r s)
                            (ring_fractionate r s) <=>
           s SUBSET {a | ring_unit r a})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ring_multsys; SUBSET]) THEN
  ASM_SIMP_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM; RING_EPIMORPHISM_ALT;
               RING_MONOMORPHISM_FRACTIONATE_GEN;
               RING_HOMOMORPHISM_FRACTIONATE; SUBSET; IN_ELIM_THM] THEN
  MATCH_MP_TAC(TAUT
   `(r ==> p) /\ (r ==> q) /\ (p ==> q ==> r) ==> (p /\ q <=> r)`) THEN
  CONJ_TAC THENL [MESON_TAC[RING_UNIT_IMP_REGULAR]; ALL_TAC] THEN
  ASM_SIMP_TAC[ring_image; ring_fractionate; RING_LOCALIZATION_CARRIER] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. Q x ==> ~P x)`] THEN
  ASM_SIMP_TAC[GSYM RING_LOCALEQUIV_EQUIV] THEN
  ASM_SIMP_TAC[ring_localequiv; RING_MUL_RID] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN CONJ_TAC THENL
   [DISCH_THEN(fun th -> MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
                         MP_TAC(SPEC `b:A` th)) THEN
    ASM_SIMP_TAC[ring_unit] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ring_mul r a x:A` THEN ASM_SIMP_TAC[RING_MUL] THEN
    EXISTS_TAC `ring_1 r:A` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SYM) THEN RING_TAC THEN ASM_SIMP_TAC[];
    DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `ring_1 r:A`) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:A` THEN
    ASM_CASES_TAC `(y:A) IN s` THEN ASM_SIMP_TAC[RING_1] THEN
    ASM_SIMP_TAC[ring_unit] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ring_regular r (u:A)` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[ring_regular]] THEN
    ASM_SIMP_TAC[ring_zerodivisor; IMP_CONJ; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `ring_sub r (ring_1 r) (ring_mul r z y):A`) THEN
    ASM_SIMP_TAC[RING_1; RING_SUB; RING_MUL] THEN
    RING_TAC THEN ASM SET_TAC[]]);;

let RING_LOCALIZATION_UNCHANGED = prove
 (`!r s:A->bool.
        ring_multsys r s /\ s SUBSET {x | ring_unit r x}
        ==> (ring_localization r s) isomorphic_ring r`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  REWRITE_TAC[isomorphic_ring] THEN
  EXISTS_TAC `ring_fractionate r (s:A->bool)` THEN
  ASM_SIMP_TAC[RING_ISOMORPHISM_FRACTIONATE_GEN]);;

let RING_LOCALIZATION_UNIVERSAL = prove
 (`!r s r' (f:A->B).
      ring_multsys r s /\
      ring_homomorphism (r,r') f /\
      (!x. x IN s ==> ring_unit r' (f x))
      ==> ?g. ring_homomorphism(ring_localization r s,r') g /\
              !x. x IN ring_carrier r ==> g (ring_fractionate r s x) = f x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_multsys]) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[ring_homomorphism]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?g. !a b. a IN ring_carrier r /\ b IN s
              ==> g (ring_localequiv r s (a,b)) =
                  ring_mul r' ((f:A->B) a) (ring_inv r' (f b))`
  MP_TAC THENL
   [GEN_REWRITE_TAC BINDER_CONV [FORALL_UNPAIR_THM] THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [EQ_SYM_EQ] THEN
    REWRITE_TAC[GSYM FUNCTION_FACTORS_LEFT_GEN] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a1:A`; `b1:A`; `a2:A`; `b2:A`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[GSYM RING_LOCALEQUIV_EQUIV] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
     `ring_mul r y1 (ring_inv r y1) = ring_1 r /\
      ring_mul r y2 (ring_inv r y2) = ring_1 r /\
      ring_mul r x1 y2 = ring_mul r x2 y1
      ==> ring_mul r x1 (ring_inv r y1) = ring_mul r x2 (ring_inv r y2)`)) THEN
   STRIP_TAC THEN ASM_SIMP_TAC[RING_INV; RING_MUL_RINV] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_localequiv]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `u:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM
     `ring_mul r' (ring_inv r' ((f:A->B) u)) o f`) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_SUB) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_MUL) THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [o_THM; RING_SUB; RING_MUL; RING_MUL_ASSOC; RING_MUL_RZERO;
      RING_INV; RING_MUL_LINV; RING_MUL_LID; RING_SUB_EQ_0];
    MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `g:(A#A->bool)->B` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ring_fractionate] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP RING_HOMOMORPHISM_1) THEN
  ASM_SIMP_TAC[RING_MUL_RID; RING_INV_1] THEN
  REWRITE_TAC[ring_homomorphism] THEN
  ASM_SIMP_TAC[RING_LOCALIZATION_CARRIER; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; SUBSET; FORALL_IN_IMAGE] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [RING_LOCALIZATION_0; RING_LOCALIZATION_1; RING_0; RING_1;
    RING_LOCALIZATION_NEG; RING_LOCALIZATION_ADD; RING_NEG; RING_ADD;
    RING_LOCALIZATION_MUL; RING_MUL; RING_MUL_LZERO; RING_MUL_LID;
    RING_INV_1; RING_INV; RING_MUL_LNEG; RING_INV_MUL] THEN
  DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`a1:A`; `b1:A`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a2:A`; `b2:A`] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `ring_unit r' ((f:A->B) b1) /\ ring_unit r' ((f:A->B) b2)`
   MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP RING_MUL_RINV)) THEN
  RING_TAC THEN ASM_SIMP_TAC[RING_INV]);;

let fraction_ring = new_definition
 `fraction_ring (r:A ring) = ring_localization r {a | ring_regular r a}`;;

let RING_LOCALEQUIV_EQ_0 = prove
 (`!r a b:A.
        a IN ring_carrier r /\ ring_regular r b
        ==> (ring_localequiv r {x | ring_regular r x} (a,b) =
             ring_0(fraction_ring r) <=>
             a = ring_0 r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fraction_ring] THEN
  ASM_SIMP_TAC[RING_LOCALEQUIV_EQ_0_GEN; RING_MULTSYS_REGULAR;
               IN_ELIM_THM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [REWRITE_TAC[ring_regular; ring_zerodivisor] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[RING_MUL_RZERO; RING_REGULAR_IN_CARRIER]]);;

let RING_FRACTIONATE_EQ_0 = prove
 (`!r a:A.
        a IN ring_carrier r
        ==> (ring_fractionate r {x | ring_regular r x} a =
             ring_0(fraction_ring r) <=>
             a = ring_0 r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_fractionate] THEN
  MATCH_MP_TAC RING_LOCALEQUIV_EQ_0 THEN
  ASM_REWRITE_TAC[RING_REGULAR_1]);;

let RING_MONOMORPHISM_FRACTIONATE = prove
 (`!r:A ring.
      ring_monomorphism (r,fraction_ring r)
                        (ring_fractionate r {a | ring_regular r a})`,
  SIMP_TAC[fraction_ring; RING_MONOMORPHISM_FRACTIONATE_GEN;
           RING_MULTSYS_REGULAR; SUBSET_REFL]);;

let FRACTION_RING_UNIVERSAL = prove
 (`!r r' (f:A->B).
      ring_homomorphism (r,r') f /\
      (!x. ring_regular r x ==> ring_unit r' (f x))
      ==> ?g. ring_homomorphism(fraction_ring r,r') g /\
              !x. x IN ring_carrier r
                  ==> g (ring_fractionate r {a | ring_regular r a} x) = f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fraction_ring] THEN
  MATCH_MP_TAC RING_LOCALIZATION_UNIVERSAL THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; RING_MULTSYS_REGULAR]);;

let RING_UNIT_FRACTION_RING,RING_ZERODIVISOR_FRACTION_RING =
 (CONJ_PAIR o prove)
 (`(!r a b:A.
        a IN ring_carrier r /\ ring_regular r b
        ==> (ring_unit (fraction_ring r)
                       (ring_localequiv r {x | ring_regular r x} (a,b)) <=>
             ring_regular r a)) /\
   (!r a b:A.
        a IN ring_carrier r /\ ring_regular r b
        ==> (ring_zerodivisor (fraction_ring r)
                       (ring_localequiv r {x | ring_regular r x} (a,b)) <=>
             ring_zerodivisor r a))`,
  REWRITE_TAC[ring_regular; AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(~r ==> p) /\ (r ==> q) /\ (q ==> ~p)
    ==> (p <=> ~r) /\ (q <=> r)`) THEN
  REWRITE_TAC[RING_ZERODIVISOR_IMP_NONUNIT] THEN CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[fraction_ring; GSYM ring_regular] THEN
    MATCH_MP_TAC RING_UNIT_LOCALEQUIV THEN
    REWRITE_TAC[RING_MULTSYS_REGULAR; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[ring_regular];
    REWRITE_TAC[GSYM ring_regular] THEN ASM_REWRITE_TAC[ring_zerodivisor] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ring_regular r (b:A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ring_regular]; ALL_TAC] THEN
    ASM_SIMP_TAC[fraction_ring; RING_LOCALEQUIV_IN_CARRIER;
                 RING_MULTSYS_REGULAR; IN_ELIM_THM] THEN
    EXISTS_TAC `ring_fractionate r {x | ring_regular r x} (c:A)` THEN
    REWRITE_TAC[ring_fractionate] THEN
    ASM_SIMP_TAC[RING_LOCALEQUIV_IN_CARRIER; RING_MULTSYS_REGULAR; RING_0;
                 IN_ELIM_THM; RING_REGULAR_1; RING_LOCALEQUIV_EQ_0_GEN;
                 RING_LOCALIZATION_MUL; RING_REGULAR_MUL] THEN
    ASM_MESON_TAC[ring_regular; ring_zerodivisor;
                  RING_REGULAR_1; RING_MUL_RZERO]]);;

let FRACTION_RING_UNIT_EQ_REGULAR = prove
 (`!(r:A ring) a.
        ring_unit (fraction_ring r) a <=> ring_regular (fraction_ring r) a`,
  GEN_TAC THEN MATCH_MP_TAC
   (MESON[RING_UNIT_IN_CARRIER; RING_REGULAR_IN_CARRIER]
     `(!a. a IN ring_carrier r ==> (ring_unit r a <=> ring_regular r a))
      ==> !a. ring_unit r a <=> ring_regular r a`) THEN
  SIMP_TAC[fraction_ring; RING_LOCALIZATION_CARRIER; RING_MULTSYS_REGULAR] THEN
  REWRITE_TAC[GSYM fraction_ring; FORALL_IN_GSPEC] THEN
  SIMP_TAC[IN_ELIM_THM; RING_UNIT_FRACTION_RING] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [ring_regular] THEN
  ASM_SIMP_TAC[RING_ZERODIVISOR_FRACTION_RING] THEN
  ASM_SIMP_TAC[RING_LOCALEQUIV_IN_CARRIER; fraction_ring;
               RING_MULTSYS_REGULAR; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[ring_regular]);;

let FRACTION_RING_UNIT_OR_ZERODIVISOR = prove
 (`!(r:A ring) a.
        a IN ring_carrier(fraction_ring r)
        ==> ring_unit (fraction_ring r) a \/
            ring_zerodivisor (fraction_ring r) a`,
  SIMP_TAC[FRACTION_RING_UNIT_EQ_REGULAR; ring_regular] THEN
  CONV_TAC TAUT);;

let TRIVIAL_FRACTION_RING = prove
 (`!r:A ring. trivial_ring(fraction_ring r) <=> trivial_ring r`,
  SIMP_TAC[fraction_ring; TRIVIAL_RING_LOCALIZATION; RING_MULTSYS_REGULAR] THEN
  REWRITE_TAC[IN_ELIM_THM; RING_REGULAR_0]);;

let FRACTION_FIELD = prove
 (`!r:A ring. field(fraction_ring r) <=> integral_domain r`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MP_TAC(ISPEC `r:A ring` RING_MONOMORPHISM_FRACTIONATE) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        INTEGRAL_DOMAIN_MONOMORPHIC_PREIMAGE)) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN];
    DISCH_TAC THEN REWRITE_TAC[FIELD_EQ_ALL_UNITS; GSYM TRIVIAL_RING_10] THEN
    REWRITE_TAC[TRIVIAL_FRACTION_RING] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING] THEN
    SIMP_TAC[fraction_ring; RING_LOCALIZATION_CARRIER;
             RING_MULTSYS_REGULAR; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; GSYM fraction_ring] THEN
    SIMP_TAC[RING_LOCALEQUIV_EQ_0; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[fraction_ring] THEN
    MATCH_MP_TAC RING_UNIT_LOCALEQUIV THEN
    ASM_REWRITE_TAC[RING_MULTSYS_REGULAR; IN_ELIM_THM] THEN
    ASM_MESON_TAC[INTEGRAL_DOMAIN_REGULAR]]);;

let FRACTION_DOMAIN = prove
 (`!r:A ring. integral_domain(fraction_ring r) <=> integral_domain r`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MP_TAC(ISPEC `r:A ring` RING_MONOMORPHISM_FRACTIONATE) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        INTEGRAL_DOMAIN_MONOMORPHIC_PREIMAGE)) THEN
    ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC LAND_CONV [GSYM FRACTION_FIELD] THEN
    REWRITE_TAC[FIELD_IMP_INTEGRAL_DOMAIN]]);;

(* ------------------------------------------------------------------------- *)
(* Special types of ideal, hence PID and Noetherian rings.                   *)
(* ------------------------------------------------------------------------- *)

let proper_ideal = new_definition
 `proper_ideal (r:A ring) j <=>
        ring_ideal r j /\ j PSUBSET ring_carrier r`;;

let principal_ideal = new_definition
 `principal_ideal (r:A ring) j <=>
        ?a. a IN ring_carrier r /\ ideal_generated r {a} = j`;;

let finitely_generated_ideal = new_definition
 `finitely_generated_ideal (r:A ring) j <=>
        ?s. FINITE s /\ s SUBSET ring_carrier r /\ ideal_generated r s = j`;;

let prime_ideal = new_definition
 `prime_ideal (r:A ring) j <=>
        proper_ideal r j /\
        !x y. x IN ring_carrier r /\
              y IN ring_carrier r /\
              (ring_mul r x y) IN j
              ==> x IN j \/ y IN j`;;

let maximal_ideal = new_definition
 `maximal_ideal (r:A ring) j <=>
        proper_ideal r j /\ ~(?j'. proper_ideal r j' /\ j PSUBSET j')`;;

let PID = new_definition
 `PID (r:A ring) <=>
        integral_domain r /\
        !j. ring_ideal r j ==> principal_ideal r j`;;

let noetherian_ring = new_definition
 `noetherian_ring (r:A ring) <=>
        !j. ring_ideal r j ==> finitely_generated_ideal r j`;;

let PROPER_IMP_RING_IDEAL = prove
 (`!r j:A->bool. proper_ideal r j ==> ring_ideal r j`,
  SIMP_TAC[proper_ideal]);;

let PROPER_IDEAL_IMP_SUBSET = prove
 (`!r s:A->bool. proper_ideal r s ==> s SUBSET ring_carrier r`,
  SIMP_TAC[ring_ideal; proper_ideal]);;

let PROPER_IDEAL_IMP_PSUBSET = prove
 (`!r s:A->bool. proper_ideal r s ==> s PSUBSET ring_carrier r`,
  SIMP_TAC[proper_ideal]);;

let PRINCIPAL_IMP_RING_IDEAL = prove
 (`!r j:A->bool. principal_ideal r j ==> ring_ideal r j`,
  REWRITE_TAC[principal_ideal] THEN MESON_TAC[RING_IDEAL_IDEAL_GENERATED]);;

let PRINCIPAL_IDEAL_IMP_SUBSET = prove
 (`!r s:A->bool. principal_ideal r s ==> s SUBSET ring_carrier r`,
  MESON_TAC[principal_ideal; IDEAL_GENERATED_SUBSET]);;

let FINITELY_GENERATED_IMP_RING_IDEAL = prove
 (`!r j:A->bool. finitely_generated_ideal r j ==> ring_ideal r j`,
  REWRITE_TAC[finitely_generated_ideal] THEN
  MESON_TAC[RING_IDEAL_IDEAL_GENERATED]);;

let FINITELY_GENERATED_IDEAL_IMP_SUBSET = prove
 (`!r s:A->bool. finitely_generated_ideal r s ==> s SUBSET ring_carrier r`,
  MESON_TAC[finitely_generated_ideal; IDEAL_GENERATED_SUBSET]);;

let PRIME_IMP_PROPER_IDEAL = prove
 (`!r j:A->bool. prime_ideal r j ==> proper_ideal r j`,
  SIMP_TAC[prime_ideal]);;

let PRIME_IMP_RING_IDEAL = prove
 (`!r j:A->bool. prime_ideal r j ==> ring_ideal r j`,
  SIMP_TAC[prime_ideal; proper_ideal]);;

let PRIME_IDEAL_IMP_SUBSET = prove
 (`!r j:A->bool. prime_ideal r j ==> j SUBSET ring_carrier r`,
  SIMP_TAC[RING_IDEAL_IMP_SUBSET; PRIME_IMP_RING_IDEAL]);;

let PRIME_IDEAL_IMP_PSUBSET = prove
 (`!r j:A->bool. prime_ideal r j ==> j PSUBSET ring_carrier r`,
  SIMP_TAC[PROPER_IDEAL_IMP_PSUBSET; PRIME_IMP_PROPER_IDEAL]);;

let MAXIMAL_IMP_PROPER_IDEAL = prove
 (`!r j:A->bool. maximal_ideal r j ==> proper_ideal r j`,
  SIMP_TAC[maximal_ideal]);;

let MAXIMAL_IMP_RING_IDEAL = prove
 (`!r j:A->bool. maximal_ideal r j ==> ring_ideal r j`,
  SIMP_TAC[maximal_ideal; proper_ideal]);;

let MAXIMAL_IDEAL_IMP_SUBSET = prove
 (`!r j:A->bool. maximal_ideal r j ==> j SUBSET ring_carrier r`,
  SIMP_TAC[RING_IDEAL_IMP_SUBSET; MAXIMAL_IMP_RING_IDEAL]);;

let MAXIMAL_IDEAL_IMP_PSUBSET = prove
 (`!r j:A->bool. maximal_ideal r j ==> j PSUBSET ring_carrier r`,
  SIMP_TAC[PROPER_IDEAL_IMP_PSUBSET; MAXIMAL_IMP_PROPER_IDEAL]);;

let PROPER_IDEAL_0 = prove
 (`!r:A ring. proper_ideal r {ring_0 r} <=> ~trivial_ring r`,
  GEN_TAC THEN REWRITE_TAC[proper_ideal; RING_IDEAL_0; trivial_ring] THEN
  MP_TAC(ISPEC `r:A ring` RING_0) THEN SET_TAC[]);;

let PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL = prove
 (`!r j:A->bool. principal_ideal r j ==> finitely_generated_ideal r j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[principal_ideal; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  REWRITE_TAC[finitely_generated_ideal] THEN
  EXISTS_TAC `{a:A}` THEN ASM_REWRITE_TAC[SING_SUBSET; FINITE_SING]);;

let PID_IMP_INTEGRAL_DOMAIN = prove
 (`!r:A ring. PID r ==> integral_domain r`,
  SIMP_TAC[PID]);;

let PID_IMP_NOETHERIAN_RING = prove
 (`!r:A ring. PID r ==> noetherian_ring r`,
  REWRITE_TAC[PID; noetherian_ring] THEN
  MESON_TAC[PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL]);;

let PRINCIPAL_IDEAL_ALT = prove
 (`!(r:A ring) j.
        principal_ideal (r:A ring) j <=> ?a. ideal_generated r {a} = j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[principal_ideal] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` MP_TAC) THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IDEAL_GENERATED_RESTRICT] THEN
  ASM_SIMP_TAC[SET_RULE `~(x IN s) ==> s INTER {x} = {}`] THEN
  REWRITE_TAC[IDEAL_GENERATED_EMPTY] THEN
  MESON_TAC[IDEAL_GENERATED_0; RING_0]);;

let PRINCIPAL_IDEAL_IDEAL_GENERATED_SING = prove
 (`!r a:A. principal_ideal r (ideal_generated r {a})`,
  MESON_TAC[PRINCIPAL_IDEAL_ALT]);;

let PRINCIPAL_IDEAL_0 = prove
 (`!r:A ring. principal_ideal r {ring_0 r}`,
  REWRITE_TAC[principal_ideal] THEN
  MESON_TAC[IDEAL_GENERATED_0; RING_0]);;

let FINITELY_GENERATED_IDEAL_0 = prove
 (`!r:A ring. finitely_generated_ideal r {ring_0 r}`,
  MESON_TAC[PRINCIPAL_IDEAL_0; PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL]);;

let PRINCIPAL_IDEAL_CARRIER = prove
 (`!r:A ring. principal_ideal r (ring_carrier r)`,
  GEN_TAC THEN REWRITE_TAC[principal_ideal] THEN
  EXISTS_TAC `ring_1 r:A` THEN
  SIMP_TAC[RING_IDEAL_EQ_CARRIER; RING_IDEAL_IDEAL_GENERATED; RING_1;
           IDEAL_GENERATED_INC_GEN; IN_SING]);;

let FINITELY_GENERATED_IDEAL_CARRIER = prove
 (`!r:A ring. finitely_generated_ideal r (ring_carrier r)`,
  MESON_TAC[PRINCIPAL_IDEAL_CARRIER; PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL]);;

let PROPER_IDEAL_ALT = prove
 (`!(r:A ring) j.
        proper_ideal r j <=> ring_ideal r j /\ ~(j = ring_carrier r)`,
  REWRITE_TAC[proper_ideal; PSUBSET] THEN
  MESON_TAC[RING_IDEAL_IMP_SUBSET]);;

let NONPRINCIPAL_IMP_PROPER_IDEAL = prove
 (`!r:A ring. ring_ideal r j /\ ~(principal_ideal r j) ==> proper_ideal r j`,
  SIMP_TAC[PROPER_IDEAL_ALT] THEN
  MESON_TAC[PRINCIPAL_IDEAL_CARRIER; SET_RULE `~(s PSUBSET s)`]);;

let NONFINITELY_GENERATED_IMP_PROPER_IDEAL = prove
 (`!r:A ring.
      ring_ideal r j /\ ~(finitely_generated_ideal r j) ==> proper_ideal r j`,
  MESON_TAC[NONPRINCIPAL_IMP_PROPER_IDEAL;
            PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL]);;

let FINITELY_GENERATED_IDEAL_ALT = prove
 (`!(r:A ring) j.
        finitely_generated_ideal (r:A ring) j <=>
        ?s. FINITE s /\ ideal_generated r s = j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[finitely_generated_ideal] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(ring_carrier r INTER s):A->bool` THEN
  ASM_REWRITE_TAC[INTER_SUBSET; GSYM IDEAL_GENERATED_RESTRICT] THEN
  ASM_SIMP_TAC[FINITE_INTER]);;

let FINITELY_GENERATED_IDEAL_GENERATED = prove
 (`!(r:A ring) s.
        FINITE s ==> finitely_generated_ideal r (ideal_generated r s)`,
  REWRITE_TAC[FINITELY_GENERATED_IDEAL_ALT] THEN MESON_TAC[]);;

let FINITELY_GENERATED_IDEAL_SETADD = prove
 (`!r j k:A->bool.
        finitely_generated_ideal r j /\ finitely_generated_ideal r k
        ==> finitely_generated_ideal r (ring_setadd r j k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[finitely_generated_ideal] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s UNION t:A->bool` THEN
  ASM_REWRITE_TAC[FINITE_UNION; UNION_SUBSET; IDEAL_GENERATED_UNION]);;

let PROPER_IDEAL = prove
 (`!(r:A ring) j. proper_ideal r j <=> ring_ideal r j /\ ~(ring_1 r IN j)`,
  SIMP_TAC[proper_ideal; PSUBSET] THEN
  MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_EQ_CARRIER]);;

let PROPER_IDEAL_UNIT = prove
 (`!(r:A ring) j.
        proper_ideal r j <=> ring_ideal r j /\ DISJOINT j {u | ring_unit r u}`,
  REWRITE_TAC[SET_RULE `DISJOINT u {x | P x} <=> ~(?x. P x /\ x IN u)`] THEN
  SIMP_TAC[proper_ideal; PSUBSET] THEN
  MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_EQ_CARRIER_UNIT]);;

let PROPER_IDEAL_UNIONS = prove
 (`!r (u:(A->bool)->bool).
        ~(u = {}) /\
        (!h. h IN u ==> proper_ideal r h) /\
        (!g h. g IN u /\ h IN u ==> g SUBSET h \/ h SUBSET g)
        ==> proper_ideal r (UNIONS u)`,
  SIMP_TAC[PROPER_IDEAL; RING_IDEAL_UNIONS] THEN SET_TAC[]);;

let PROPER_IDEAL_EXISTS = prove
 (`!(r:A ring). (?j. proper_ideal r j) <=> ~(trivial_ring r)`,
  GEN_TAC THEN REWRITE_TAC[proper_ideal; TRIVIAL_RING_SUBSET] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `j:A->bool` THEN
    MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] IN_RING_IDEAL_0) THEN SET_TAC[];
    DISCH_TAC THEN EXISTS_TAC `{ring_0 r:A}` THEN
    REWRITE_TAC[RING_IDEAL_0] THEN
    MP_TAC(ISPEC `r:A ring` RING_0) THEN ASM SET_TAC[]]);;

let FINITELY_GENERATED_IDEAL_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) j.
         ring_epimorphism (r,r') f /\ finitely_generated_ideal r j
         ==> finitely_generated_ideal r' (IMAGE f j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[finitely_generated_ideal] THEN FIRST_ASSUM
   (SUBST1_TAC o SYM o CONJUNCT2 o REWRITE_RULE[ring_epimorphism]) THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE]);;

let PRINCIPAL_IDEAL_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) j.
         ring_epimorphism (r,r') f /\ principal_ideal r j
         ==> principal_ideal r' (IMAGE f j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[principal_ideal] THEN FIRST_ASSUM
   (SUBST1_TAC o SYM o CONJUNCT2 o REWRITE_RULE[ring_epimorphism]) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[IMAGE_CLAUSES; SING_SUBSET;
                IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE]);;

let PROPER_IDEAL_HOMOMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B) j.
        ring_homomorphism(r,r') f /\ proper_ideal r' j
        ==> proper_ideal r {x | x IN ring_carrier r /\ f x IN j}`,
  REWRITE_TAC[PROPER_IDEAL; IN_ELIM_THM; RING_1] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN ASM SET_TAC[];
    ASM_MESON_TAC[RING_HOMOMORPHISM_1]]);;

let PROPER_IDEAL_CORRESPONDENCE = prove
 (`!r r' (f:A->B) j k.
         ring_homomorphism (r,r') f /\
         ring_ideal r' k /\
         {x | x IN ring_carrier r /\ f x IN k} = j
         ==> (proper_ideal r j <=> proper_ideal r' k)`,
  SIMP_TAC[PROPER_IDEAL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; RING_1] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP RING_HOMOMORPHISM_1) THEN
  ASM_CASES_TAC `(ring_1 r':B) IN k` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN ASM_MESON_TAC[]);;

let PROPER_IDEAL_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) j.
        ring_isomorphism(r,r') f /\ j SUBSET ring_carrier r
        ==> (proper_ideal r' (IMAGE f j) <=> proper_ideal r j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_ISOMORPHIC_IMAGE_EQ) THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (q' ==> p') /\ (p' ==> (q' <=> q))
    ==> (p' <=> p) ==> (q' <=> q)`) THEN
  REWRITE_TAC[PROPER_IMP_RING_IDEAL] THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC PROPER_IDEAL_CORRESPONDENCE THEN
  EXISTS_TAC `f:A->B` THEN ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_isomorphism; ring_isomorphisms]) THEN
  ASM SET_TAC[]);;

let PRIME_IDEAL_HOMOMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B) j.
        ring_homomorphism(r,r') f /\ prime_ideal r' j
        ==> prime_ideal r {x | x IN ring_carrier r /\ f x IN j}`,
  REWRITE_TAC[prime_ideal; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC PROPER_IDEAL_HOMOMORPHIC_PREIMAGE THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[]]);;

let RING_1_NOT_IN_PRIME_IDEAL = prove
 (`!r j:A->bool.
        prime_ideal r j ==> ~(ring_1 r IN j)`,
  MESON_TAC[PROPER_IDEAL; prime_ideal]);;

let RING_UNIT_NOT_IN_PRIME_IDEAL = prove
 (`!r j x:A.
        prime_ideal r j /\ ring_unit r x ==> ~(x IN j)`,
  REWRITE_TAC[prime_ideal; PROPER_IDEAL_UNIT] THEN SET_TAC[]);;

let RING_MUL_IN_PRIME_IDEAL = prove
 (`!r j x y:A.
        prime_ideal r j /\ x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_mul r x y IN j <=> x IN j \/ y IN j)`,
  ASM_MESON_TAC[prime_ideal; proper_ideal; ring_ideal; RING_MUL_SYM; SUBSET]);;

let RING_POW_IN_PRIME_IDEAL = prove
 (`!r j (x:A) n.
        prime_ideal r j /\ x IN ring_carrier r
        ==> (ring_pow r x n IN j <=> ~(n = 0) /\ x IN j)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ring_pow; RING_1_NOT_IN_PRIME_IDEAL] THEN
  ASM_SIMP_TAC[RING_MUL_IN_PRIME_IDEAL; RING_POW; NOT_SUC] THEN
  CONV_TAC TAUT);;

let MAXIMAL_SUPERIDEAL_EXISTS = prove
 (`!(r:A ring) j.
        proper_ideal r j ==> ?j'. maximal_ideal r j' /\ j SUBSET j'`,
  REWRITE_TAC[PROPER_IDEAL] THEN REPEAT STRIP_TAC THEN MP_TAC(ISPEC
   `\j'. proper_ideal (r:A ring) j' /\ j SUBSET j'`
   ZL_SUBSETS_UNIONS_NONEMPTY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY; PROPER_IDEAL] THEN
    SIMP_TAC[RING_IDEAL_UNIONS] THEN ASM SET_TAC[];
    REWRITE_TAC[maximal_ideal; PROPER_IDEAL] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]]);;

let MAXIMAL_IDEAL_EXISTS = prove
 (`!r:A ring. (?j. maximal_ideal r j) <=> ~(trivial_ring r)`,
  GEN_TAC THEN REWRITE_TAC[GSYM PROPER_IDEAL_EXISTS] THEN
  MESON_TAC[MAXIMAL_IMP_PROPER_IDEAL; MAXIMAL_SUPERIDEAL_EXISTS]);;

let RING_MULTSYS_NONPRIME = prove
 (`!r j:A->bool.
        prime_ideal r j ==> ring_multsys r (ring_carrier r DIFF j)`,
  REWRITE_TAC[ring_multsys; IN_DIFF; prime_ideal; PROPER_IDEAL] THEN
  GEN_TAC THEN SIMP_TAC[RING_MUL; RING_1] THEN SET_TAC[]);;

let RING_MULTSYS_NONPRIME_EQ = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> (ring_multsys r (ring_carrier r DIFF j) <=> prime_ideal r j)`,
  REWRITE_TAC[ring_multsys; IN_DIFF; prime_ideal; PROPER_IDEAL] THEN
  GEN_TAC THEN SIMP_TAC[RING_MUL; RING_1] THEN SET_TAC[]);;

let MAXIMAL_EXCLUDING_IMP_PRIME_IDEAL = prove
 (`!r s j:A->bool.
        ring_multsys r s /\
        ring_ideal r j /\ DISJOINT j s /\
        (!j'. ring_ideal r j' /\ j PSUBSET j' ==> ~DISJOINT j' s)
        ==> prime_ideal r j`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[prime_ideal; proper_ideal] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `DISJOINT j s
      ==> j SUBSET c /\ s SUBSET c /\ ~(s = {}) ==> j PSUBSET c`)) THEN
    ASM_MESON_TAC[RING_MULTSYS_IMP_SUBSET; RING_MULTSYS_IMP_NONEMPTY;
                  RING_IDEAL_IMP_SUBSET];
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `ring_setadd r j (ideal_generated r {b:A})` th) THEN
      MP_TAC(SPEC `ring_setadd r j (ideal_generated r {a:A})` th)) THEN
   MATCH_MP_TAC(TAUT
    `(p /\ p') /\ (q /\ q' ==> r) ==> (p ==> q) ==> (p' ==> q') ==> r`) THEN
   CONJ_TAC THENL
    [ASM_SIMP_TAC[RING_IDEAL_SETADD; RING_IDEAL_IDEAL_GENERATED] THEN
     CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
      `!a. a IN s /\ ~(a IN j) /\
           j SUBSET ring_setadd r j s /\ s SUBSET ring_setadd r j s
           ==> j PSUBSET ring_setadd r j s`)
     THENL [EXISTS_TAC `a:A`; EXISTS_TAC `b:A`] THEN
     ASM_SIMP_TAC[IDEAL_GENERATED_INC; IN_SING; SING_SUBSET] THEN
     ASM_SIMP_TAC[RING_SETADD_SUPERSET_LEFT; IN_RING_IDEAL_0; SING_SUBSET;
                  RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_GENERATED;
                  RING_SETADD_SUPERSET_RIGHT];
     REWRITE_TAC[SET_RULE `~DISJOINT t s /\ ~DISJOINT u s ==> P <=>
         !x y. x IN s /\ y IN s ==> x IN t /\ y IN u ==> P`] THEN
     MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
     DISCH_THEN(MP_TAC o ISPEC `r:A ring` o MATCH_MP RING_MUL_IN_SETMUL) THEN
     W(MP_TAC o PART_MATCH (lhand o rand) RING_SETMUL_IDEAL_LEFT o
        rand o lhand o snd) THEN
     ASM_REWRITE_TAC[IDEAL_GENERATED_SUBSET] THEN MATCH_MP_TAC(SET_RULE
      `(P ==> a IN t ==> F) ==> (s SUBSET t ==> a IN s ==> ~P)`) THEN
     DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `DISJOINT j s ==> z IN s /\ j' SUBSET j ==> z IN j' ==> F`)) THEN
     CONJ_TAC THENL [ASM_MESON_TAC[ring_multsys]; ALL_TAC] THEN
     ASM_SIMP_TAC[RING_SETMUL_IDEAL_GENERATED_SING] THEN
     MATCH_MP_TAC RING_SETADD_SUBSET_IDEAL THEN
     ASM_SIMP_TAC[SUBSET_REFL; IDEAL_GENERATED_MINIMAL; SING_SUBSET]]]);;

let MAXIMAL_IMP_PRIME_IDEAL = prove
 (`!r j:A->bool. maximal_ideal r j ==> prime_ideal r j`,
  REWRITE_TAC[maximal_ideal; PROPER_IDEAL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MAXIMAL_EXCLUDING_IMP_PRIME_IDEAL THEN
  EXISTS_TAC `{ring_1 r:A}` THEN ASM_REWRITE_TAC[RING_MULYSYS_1] THEN
  ASM SET_TAC[]);;

let MAXIMAL_AMONG_PRIME_IDEALS = prove
 (`!r j:A->bool.
        maximal_ideal r j <=>
        prime_ideal r j /\ ~(?j'. prime_ideal r j' /\ j PSUBSET j')`,
  ASM_MESON_TAC[MAXIMAL_SUPERIDEAL_EXISTS; PRIME_IMP_PROPER_IDEAL;
                MAXIMAL_IMP_PRIME_IDEAL; maximal_ideal;
                SET_RULE `s PSUBSET t /\ t SUBSET u ==> s PSUBSET u`]);;

let PRIME_IDEAL_0 = prove
 (`!r:A ring. prime_ideal r {ring_0 r} <=> integral_domain r`,
  GEN_TAC THEN REWRITE_TAC[prime_ideal; PROPER_IDEAL; RING_IDEAL_0] THEN
  REWRITE_TAC[IN_SING; integral_domain]);;

let MAXIMAL_IDEAL_0 = prove
 (`!r:A ring. maximal_ideal r {ring_0 r} <=> field r`,
  REWRITE_TAC[maximal_ideal; PROPER_IDEAL; RING_IDEAL_IDEAL_GENERATED] THEN
  REWRITE_TAC[RING_IDEAL_0; IN_SING; field] THEN
  GEN_TAC THEN ASM_CASES_TAC `ring_1 r:A = ring_0 r` THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ideal_generated r {a:A}`) THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    MATCH_MP_TAC(SET_RULE
      `!x. x IN a /\ ring_0 r IN a /\ ~(x = ring_0 r) /\ (P ==> Q)
            ==> ~(~P /\ {ring_0 r} PSUBSET a) ==> Q`) THEN
    EXISTS_TAC `a:A` THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_SING] THEN
    SIMP_TAC[IN_RING_IDEAL_0; RING_IDEAL_IDEAL_GENERATED] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM; ring_divides] THEN
    MESON_TAC[RING_1];
    X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC o MATCH_MP (SET_RULE
     `{z} PSUBSET s ==> ?a. z IN s /\ a IN s /\ ~(a = z)`)) THEN
    SUBGOAL_THEN `(a:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
      ASM_MESON_TAC[IN_RING_IDEAL_RMUL]]]);;

let PRIME_SUPERIDEAL_EXISTS = prove
 (`!(r:A ring) j.
        proper_ideal r j ==> ?j'. prime_ideal r j' /\ j SUBSET j'`,
  MESON_TAC[MAXIMAL_IMP_PRIME_IDEAL; MAXIMAL_SUPERIDEAL_EXISTS]);;

let PRIME_IDEAL_EXISTS = prove
 (`!r:A ring. (?j. prime_ideal r j) <=> ~trivial_ring r`,
  MESON_TAC[PRIME_SUPERIDEAL_EXISTS; PROPER_IDEAL_EXISTS;
            PRIME_IMP_PROPER_IDEAL]);;

let PRIME_SUPERIDEAL_EXCLUDING_EXISTS = prove
 (`!r s j:A->bool.
        ring_ideal r j /\ ring_multsys r s /\ DISJOINT j s
        ==> ?j'. prime_ideal r j' /\ j SUBSET j' /\ DISJOINT j' s`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC
   `\j'. ring_ideal (r:A ring) j' /\ j SUBSET j' /\ DISJOINT j' s`
   ZL_SUBSETS_UNIONS_NONEMPTY) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RING_IDEAL_UNIONS] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_REFL]; SET_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:A->bool` THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MAXIMAL_EXCLUDING_IMP_PRIME_IDEAL THEN
    EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let PRIME_IDEAL_EXCLUDING_EXISTS = prove
 (`!r s:A->bool.
           ring_multsys r s /\ ~(ring_0 r IN s)
           ==> ?j. prime_ideal r j /\ DISJOINT j s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `{ring_0 r:A}`]
        PRIME_SUPERIDEAL_EXCLUDING_EXISTS) THEN
  ASM_REWRITE_TAC[RING_IDEAL_0; DISJOINT_SING] THEN MESON_TAC[]);;

let PRIME_IDEAL_SING = prove
 (`!r a:A. prime_ideal r (ideal_generated r {a}) <=>
           if ~(a IN ring_carrier r) \/ a = ring_0 r then integral_domain r
           else ring_prime r a`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IDEAL_GENERATED_0; PRIME_IDEAL_0] THEN
    ASM_SIMP_TAC[prime_ideal; PROPER_IDEAL; RING_IDEAL_IDEAL_GENERATED] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM; RING_DIVIDES_ONE] THEN
    ASM_REWRITE_TAC[ring_prime];
    ONCE_REWRITE_TAC[IDEAL_GENERATED_RESTRICT] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_EMPTY; SET_RULE
      `~(a IN s) ==> s INTER {a} = {}`] THEN
    REWRITE_TAC[PRIME_IDEAL_0]]);;

let RING_PRIME_IDEAL = prove
 (`!r a:A.
        ring_prime r a <=>
        a IN ring_carrier r /\ ~(a = ring_0 r) /\
        prime_ideal r (ideal_generated r {a})`,
  MESON_TAC[ring_prime; PRIME_IDEAL_SING]);;

let PROPER_IDEAL_IDEAL_GENERATED_SING = prove
 (`!r a:A.
        a IN ring_carrier r
        ==> (proper_ideal r (ideal_generated r {a}) <=> ~(ring_unit r a))`,
  SIMP_TAC[PROPER_IDEAL_ALT; RING_IDEAL_IDEAL_GENERATED] THEN
  SIMP_TAC[IDEAL_GENERATED_SING_EQ_CARRIER]);;

let UNIONS_MAXIMAL_IDEALS = prove
 (`!r:A ring.
        UNIONS {j | maximal_ideal r j} =
        {x | x IN ring_carrier r /\ ~(ring_unit r x)}`,
  GEN_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNIONS_SUBSET] THEN
  REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[maximal_ideal; PROPER_IDEAL_UNIT; ring_ideal] THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN SET_TAC[];
    SIMP_TAC[GSYM PROPER_IDEAL_IDEAL_GENERATED_SING; IMP_CONJ] THEN
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP MAXIMAL_SUPERIDEAL_EXISTS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SUBSET] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_SING]]);;

let RING_IRREDUCIBLE_IMP_MAXIMAL_PRINCIPAL_IDEAL = prove
 (`!r p:A.
        ring_irreducible r p
        ==> proper_ideal r (ideal_generated r {p}) /\
            ~(?j. principal_ideal r j /\
                  proper_ideal r j /\
                  ideal_generated r {p} PSUBSET j)`,
  REWRITE_TAC[ring_irreducible] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[PROPER_IDEAL_IDEAL_GENERATED_SING] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [principal_ideal]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A`
   (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PSUBSET]) THEN
  ASM_SIMP_TAC[SUBSET_IDEALS_GENERATED_SING; IDEALS_GENERATED_SING_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `u:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[RING_ASSOCIATES_RMUL; PROPER_IDEAL_IDEAL_GENERATED_SING]);;

let RING_IRREDUCIBLE_EQ_MAXIMAL_PRINCIPAL_IDEAL = prove
 (`!r p:A.
        integral_domain r
        ==> (ring_irreducible r p <=>
             p IN ring_carrier r /\ ~(p = ring_0 r) /\
             proper_ideal r (ideal_generated r {p}) /\
             ~(?j. principal_ideal r j /\
                   proper_ideal r j /\
                   ideal_generated r {p} PSUBSET j))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(p:A) IN ring_carrier r` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[ring_irreducible]] THEN
  ASM_CASES_TAC `p:A = ring_0 r` THENL
   [ASM_MESON_TAC[ring_irreducible]; ASM_REWRITE_TAC[]] THEN
  EQ_TAC THEN REWRITE_TAC[RING_IRREDUCIBLE_IMP_MAXIMAL_PRINCIPAL_IDEAL] THEN
  ASM_SIMP_TAC[PROPER_IDEAL_IDEAL_GENERATED_SING; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[INTEGRAL_DOMAIN_IRREDUCIBLE_ALT] THEN
  X_GEN_TAC `d:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ideal_generated r {d:A}`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_DIVIDES_IN_CARRIER) THEN
  REWRITE_TAC[PRINCIPAL_IDEAL_IDEAL_GENERATED_SING] THEN
  ASM_SIMP_TAC[PROPER_IDEAL_IDEAL_GENERATED_SING; DE_MORGAN_THM] THEN
  ASM_SIMP_TAC[PSUBSET; SUBSET_IDEALS_GENERATED_SING] THEN
  ASM_SIMP_TAC[IDEALS_GENERATED_SING_EQ]);;

let MAXIMAL_IDEAL_SING_IMP_IRREDUCIBLE = prove
 (`!r p:A.
        integral_domain r /\
        p IN ring_carrier r /\ ~(p = ring_0 r) /\
        maximal_ideal r (ideal_generated r {p})
        ==> ring_irreducible r p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MAXIMAL_IMP_PRIME_IDEAL) THEN
  ASM_SIMP_TAC[PRIME_IDEAL_SING]);;

let RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL = prove
 (`!r p:A.
        PID r
        ==> (ring_irreducible r p <=>
             p IN ring_carrier r /\ ~(p = ring_0 r) /\
             maximal_ideal r (ideal_generated r {p}))`,
  SIMP_TAC[PID; RING_IRREDUCIBLE_EQ_MAXIMAL_PRINCIPAL_IDEAL] THEN
  REWRITE_TAC[maximal_ideal] THEN MESON_TAC[proper_ideal]);;

let MAXIMAL_IDEAL_SING = prove
 (`!r p:A.
        PID r
        ==> (maximal_ideal r (ideal_generated r {p}) <=>
             if ~(p IN ring_carrier r) \/ p = ring_0 r then field r
             else ring_irreducible r p)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(p:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IDEAL_GENERATED_0; MAXIMAL_IDEAL_0] THEN
    ASM_SIMP_TAC[RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL];
    ONCE_REWRITE_TAC[IDEAL_GENERATED_RESTRICT] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_EMPTY; SET_RULE
      `~(p IN s) ==> s INTER {p} = {}`] THEN
    REWRITE_TAC[MAXIMAL_IDEAL_0]]);;

let PID_IRREDUCIBLE_EQ_PRIME = prove
 (`!r p:A. PID r ==> (ring_irreducible r p <=> ring_prime r p)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[PID; INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE]] THEN
  ASM_SIMP_TAC[RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL; RING_PRIME_IDEAL] THEN
  SIMP_TAC[MAXIMAL_IMP_PRIME_IDEAL]);;

let FIELD_EQ_TRIVIAL_IDEALS = prove
 (`!r:A ring.
        field r <=>
        ~(trivial_ring r) /\
        !j. ring_ideal r j ==> j = {ring_0 r} \/ j = ring_carrier r`,
  GEN_TAC THEN REWRITE_TAC[GSYM MAXIMAL_IDEAL_0; maximal_ideal] THEN
  REWRITE_TAC[PROPER_IDEAL_0; NOT_EXISTS_THM] THEN AP_TERM_TAC THEN
  REWRITE_TAC[proper_ideal; TAUT `~((p /\ q) /\ r) <=> p ==> ~r \/ ~q`] THEN
  SIMP_TAC[PSUBSET; RING_IDEAL_IMP_SUBSET; SING_SUBSET; IN_RING_IDEAL_0] THEN
  MESON_TAC[]);;

let FIELD_EQ_TRIVIAL_IDEALS_EQ = prove
 (`!r:A ring.
        field r <=>
        ~(trivial_ring r) /\
        !j. ring_ideal r j <=> j = {ring_0 r} \/ j = ring_carrier r`,
  REWRITE_TAC[FIELD_EQ_TRIVIAL_IDEALS] THEN
  MESON_TAC[RING_IDEAL_CARRIER; RING_IDEAL_0]);;

let FIELD_EQ_NO_PROPER_IDEALS = prove
 (`!r:A ring. field r <=>
               ~(trivial_ring r) /\
               !j. proper_ideal r j ==> j = {ring_0 r}`,
  REWRITE_TAC[proper_ideal; FIELD_EQ_TRIVIAL_IDEALS; PSUBSET] THEN
  MESON_TAC[RING_IDEAL_IMP_SUBSET]);;

let FIELD_EQ_NO_PROPER_IDEALS_EQ = prove
 (`!r:A ring. field r <=>
               ~(trivial_ring r) /\
               !j. proper_ideal r j <=> j = {ring_0 r}`,
  REWRITE_TAC[FIELD_EQ_NO_PROPER_IDEALS] THEN MESON_TAC[PROPER_IDEAL_0]);;

let FIELD_EQ_PROPER_IMP_MAXIMAL_IDEAL = prove
 (`!r:A ring. field r <=>
               ~(trivial_ring r) /\
               !j. proper_ideal r j ==> maximal_ideal r j`,
  MESON_TAC[FIELD_EQ_NO_PROPER_IDEALS; PROPER_IDEAL_0; MAXIMAL_IDEAL_0]);;

let FIELD_EQ_PROPER_IMP_PRIME_IDEAL = prove
 (`!r:A ring. field r <=>
               ~(trivial_ring r) /\
               !j. proper_ideal r j ==> prime_ideal r j`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[FIELD_EQ_PROPER_IMP_MAXIMAL_IDEAL; MAXIMAL_IMP_PRIME_IDEAL];
    STRIP_TAC THEN ASM_SIMP_TAC[FIELD_EQ_ALL_UNITS; GSYM TRIVIAL_RING_10]] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `ideal_generated r {ring_pow r (a:A) 2}`) THEN
  REWRITE_TAC[TAUT `(p ==> q) ==> r <=> (~p ==> r) /\ (q ==> r)`] THEN
  ASM_SIMP_TAC[PROPER_IDEAL_IDEAL_GENERATED_SING; RING_POW] THEN
  ASM_SIMP_TAC[RING_UNIT_POW_EQ; ARITH_EQ] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`r:A ring`; `ideal_generated r {ring_pow r (a:A) 2}`; `a:A`; `2`]
   RING_POW_IN_PRIME_IDEAL) THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_SING; RING_POW; ARITH_EQ] THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING_ALT; RING_POW; IN_ELIM_THM; ring_unit] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:A` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
  MAP_EVERY EXISTS_TAC [`r:A ring`; `a:A`] THEN ASM_REWRITE_TAC[RING_1] THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_MUL; GSYM RING_POW_2; RING_MUL_RID] THEN
  ASM_MESON_TAC[PRIME_IDEAL_0; PROPER_IDEAL_0]);;

let FIELD_IMP_PID = prove
 (`!r:A ring. field r ==> PID r`,
  GEN_TAC THEN SIMP_TAC[PID; FIELD_IMP_INTEGRAL_DOMAIN] THEN
  REWRITE_TAC[FIELD_EQ_TRIVIAL_IDEALS] THEN
  MESON_TAC[PRINCIPAL_IDEAL_0; PRINCIPAL_IDEAL_CARRIER]);;

let FIELD_IMP_NOETHERIAN_RING = prove
 (`!r:A ring. field r ==> noetherian_ring r`,
  SIMP_TAC[FIELD_IMP_PID; PID_IMP_NOETHERIAN_RING]);;

let PID_MAXIMAL_EQ_PRIME_IDEAL = prove
 (`!r j:A->bool.
        PID r /\ ~(j = {ring_0 r})
        ==> (maximal_ideal r j <=> prime_ideal r j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `principal_ideal r (j:A->bool)` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [principal_ideal]);
    ASM_MESON_TAC[PID; maximal_ideal; prime_ideal; proper_ideal]] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `a:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  ASM_REWRITE_TAC[IDEAL_GENERATED_EQ_0] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MAXIMAL_IDEAL_SING; PRIME_IDEAL_SING;
               PID_IMP_INTEGRAL_DOMAIN] THEN
  ASM_SIMP_TAC[PID_IRREDUCIBLE_EQ_PRIME]);;

let PID_EQ_INTEGRAL_DOMAIN_PRIME_PRINCIPAL = prove
 (`!r:A ring. PID r <=>
              integral_domain r /\
              (!j. prime_ideal r j ==> principal_ideal r j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[PID; PRIME_IMP_RING_IDEAL];
    STRIP_TAC THEN ASM_REWRITE_TAC[PID]] THEN
  GEN_REWRITE_TAC I [MESON[] `(!x. P x ==> Q x) <=> ~(?x. P x /\ ~Q x)`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `\j:A->bool. ring_ideal r j /\ ~principal_ideal r j`
   ZL_SUBSETS_UNIONS_NONEMPTY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY; PROPER_IDEAL] THEN
    SIMP_TAC[RING_IDEAL_UNIONS] THEN
    X_GEN_TAC `c:(A->bool)->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[principal_ideal] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `a:A` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_SING; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ideal_generated r {a:A} = i` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM; ASM_MESON_TAC[principal_ideal]] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_MINIMAL_EQ] THEN ASM SET_TAC[];
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `k:A->bool` THEN
    FIRST_X_ASSUM(K ALL_TAC o check (is_exists o concl))] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A->bool`) THEN
  ASM_REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[prime_ideal; NONPRINCIPAL_IMP_PROPER_IDEAL] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p \/ q <=> ~(~p /\ ~q)`] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAUT
   `(p /\ ~q) /\ r ==> s <=> p /\ r /\ ~s ==> q`]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `ideal_generated r ((a:A) INSERT k)`) THEN
  REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [TRANS_TAC SUBSET_TRANS `(a:A) INSERT k` THEN
    REWRITE_TAC[SET_RULE `s SUBSET a INSERT s`] THEN
    MATCH_MP_TAC IDEAL_GENERATED_SUBSET_CARRIER_SUBSET THEN
    ASM_SIMP_TAC[INSERT_SUBSET; RING_IDEAL_IMP_SUBSET];
    GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[IN_INSERT];
    REWRITE_TAC[principal_ideal] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` (STRIP_ASSUME_TAC o GSYM))] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `{x:A | x IN ring_carrier r /\ ring_mul r x a IN k}`) THEN
  ASM_SIMP_TAC[RING_IDEAL_QUOTIENT_RMUL; NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[IN_RING_IDEAL_RMUL; SUBSET; RING_IDEAL_IMP_SUBSET];
    GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `b:A`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_MUL_SYM];
    REWRITE_TAC[principal_ideal] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:A` (STRIP_ASSUME_TAC o GSYM))] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [principal_ideal]) THEN
  REWRITE_TAC[] THEN EXISTS_TAC `ring_mul r c d:A` THEN
  ASM_SIMP_TAC[RING_MUL; GSYM SUBSET_ANTISYM_EQ; IDEAL_GENERATED_MINIMAL_EQ;
               SING_SUBSET; SET_RULE `a IN s ==> s INTER {a} = {a}`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE LAND_CONV [IDEAL_GENERATED_INSERT]) THEN
    REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `c:A`) THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_SING] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_RING_IDEAL; IDEAL_GENERATED_SING_ALT] THEN
    SPEC_TAC(`c:A`,`c:A`) THEN
    UNDISCH_THEN `(c:A) IN ring_carrier r` (K ALL_TAC) THEN
    REWRITE_TAC[ring_setadd; FORALL_IN_GSPEC; IMP_CONJ;
                RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_ADD_RDISTRIB; RING_MUL] THEN
    MATCH_MP_TAC IN_RING_IDEAL_ADD THEN
    ASM_SIMP_TAC[IN_RING_IDEAL_RMUL] THEN
    SUBGOAL_THEN
     `ring_mul r (ring_mul r a x) d:A = ring_mul r x (ring_mul r d a)`
    SUBST1_TAC THENL [ASM_SIMP_TAC[RING_MUL_AC]; ALL_TAC] THEN
    MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `{x | P x /\ f x IN k} = s ==> d IN s ==> f d IN k`)) THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_SING];
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `ideal_generated r (a INSERT k) = s
      ==> (a INSERT k) SUBSET ideal_generated r (a INSERT k) /\
          s INTER k SUBSET t
          ==> k SUBSET t`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IDEAL_GENERATED_SUBSET_CARRIER_SUBSET THEN
      ASM_SIMP_TAC[INSERT_SUBSET; RING_IDEAL_IMP_SUBSET];
      ASM_SIMP_TAC[IDEAL_GENERATED_SING_ALT]] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `u:A` THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC[GSYM RING_SETMUL_IDEAL_GENERATED_SING] THEN
    MATCH_MP_TAC RING_MUL_IN_SETMUL THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_SING] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC RING_MULTIPLE_IN_IDEAL THEN
    MAP_EVERY EXISTS_TAC [`r:A ring`; `ring_mul r u c:A`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[RING_MUL_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC RING_DIVIDES_MUL2 THEN ASM_REWRITE_TAC[RING_DIVIDES_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_INSERT] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM]]);;

let TRIVIAL_QUOTIENT_RING = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> (trivial_ring (quotient_ring r j) <=> ~proper_ideal r j)`,
  SIMP_TAC[TRIVIAL_RING_10; QUOTIENT_RING] THEN
  SIMP_TAC[RING_COSET_EQ; RING_0; RING_1; PROPER_IDEAL] THEN
  SIMP_TAC[RING_SUB_RZERO; RING_1]);;

let INTEGRAL_DOMAIN_QUOTIENT_RING = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> (integral_domain(quotient_ring r j) <=> prime_ideal r j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral_domain] THEN
  ASM_SIMP_TAC[CONJUNCT1 QUOTIENT_RING] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[QUOTIENT_RING_0] THEN
  ASM_SIMP_TAC[el 2 (CONJUNCTS QUOTIENT_RING)] THEN
  ASM_SIMP_TAC[RING_COSET_EQ_IDEAL; QUOTIENT_RING_MUL; RING_MUL; RING_1] THEN
  ASM_REWRITE_TAC[prime_ideal; PROPER_IDEAL] THEN MESON_TAC[]);;

let FIELD_QUOTIENT_RING = prove
 (`!r j:A->bool.
        ring_ideal r j ==> (field(quotient_ring r j) <=> maximal_ideal r j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[field] THEN
  ASM_SIMP_TAC[CONJUNCT1 QUOTIENT_RING] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
  ASM_SIMP_TAC[QUOTIENT_RING_0] THEN
  ONCE_REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  ASM_SIMP_TAC[el 2 (CONJUNCTS QUOTIENT_RING)] THEN
  ASM_SIMP_TAC[RING_COSET_EQ_IDEAL; QUOTIENT_RING_MUL; RING_MUL; RING_1;
               RING_COSET_EQ] THEN
  ASM_CASES_TAC `(ring_1 r:A) IN j` THEN
  ASM_REWRITE_TAC[maximal_ideal; PROPER_IDEAL; NOT_FORALL_THM; NOT_IMP;
                  NOT_EXISTS_THM; IMP_IMP] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `k:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o
        GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN
    SUBGOAL_THEN `(a:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; RING_IDEAL_IMP_SUBSET];
      ASM_REWRITE_TAC[NOT_EXISTS_THM]] THEN
    X_GEN_TAC `b:A` THEN STRIP_TAC THEN
     UNDISCH_TAC `~((ring_1 r:A) IN k)` THEN
    SUBGOAL_THEN
     `ring_1 r:A =
      ring_sub r (ring_mul r a b) (ring_sub r (ring_mul r a b) (ring_1 r))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[ring_sub; RING_NEG_ADD; RING_NEG_NEG; RING_1; RING_MUL;
        RING_ADD; RING_NEG; RING_ADD_ASSOC; RING_ADD_RNEG; RING_ADD_LZERO];
      REWRITE_TAC[] THEN MATCH_MP_TAC IN_RING_IDEAL_SUB THEN
      ASM_MESON_TAC[SUBSET; ring_ideal; RING_MUL_SYM]];
    X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `ring_setadd r j (ideal_generated r {a:A})`) THEN
    ASM_SIMP_TAC[RING_IDEAL_SETADD; RING_IDEAL_IDEAL_GENERATED;
                 SING_SUBSET] THEN
    MATCH_MP_TAC(TAUT `q /\ (~p ==> r) ==> ~(p /\ q) ==> r`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[PSUBSET; RING_SETADD_SUPERSET_LEFT; IN_RING_IDEAL_0;
                   RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_GENERATED] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `~(a IN j) ==> a IN s ==> ~(j = s)`)) THEN
      W(MP_TAC o PART_MATCH (rand o rand) RING_SETADD_SUPERSET_RIGHT o
        rand o snd) THEN
      ASM_SIMP_TAC[IN_RING_IDEAL_0; IDEAL_GENERATED_SUBSET; SING_SUBSET] THEN
      MATCH_MP_TAC(SET_RULE `x IN s ==> s SUBSET t ==> x IN t`) THEN
      ASM_SIMP_TAC[IDEAL_GENERATED_INC; IN_SING; SING_SUBSET];
      ASM_SIMP_TAC[ring_setadd; IDEAL_GENERATED_SING_ALT] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `z:A`] THEN
      STRIP_TAC THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
       [ASM_MESON_TAC[ring_ideal; SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[ring_sub; RING_NEG_ADD; RING_MUL] THEN
      MATCH_MP_TAC(MESON[]
       `x IN j /\
        ring_add r a (ring_add r x (ring_neg r a)) = x
        ==> (ring_add r a (ring_add r x (ring_neg r a))) IN j`) THEN
      ASM_SIMP_TAC[IN_RING_IDEAL_NEG] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC RING_LNEG_UNIQUE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[RING_ADD; RING_NEG; RING_MUL]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM RING_NEG_ADD; RING_MUL;
                   RING_ADD; RING_MUL; RING_NEG] THEN
      ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
       [RING_ADD_ASSOC; RING_MUL; RING_NEG; RING_ADD; RING_ADD_RNEG]]]);;

let PRIME_IDEAL_CORRESPONDENCE = prove
 (`!r r' (f:A->B) j k.
           ring_epimorphism (r,r') f /\
           ring_ideal r' k /\
           {x | x IN ring_carrier r /\ f x IN k} = j
        ==> (prime_ideal r j <=> prime_ideal r' k)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `f:A->B`]
    RING_IDEAL_HOMOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_DOMAIN_QUOTIENT_RING;
                RING_EPIMORPHISM_IMP_HOMOMORPHISM] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC ISOMORPHIC_RING_INTEGRAL_DOMAINNESS THEN
  MATCH_MP_TAC FIRST_RING_ISOMORPHISM_THEOREM_GEN THEN
  EXISTS_TAC `f:A->B` THEN ASM_REWRITE_TAC[]);;

let PRIME_IDEAL_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) j.
        ring_isomorphism(r,r') f /\ j SUBSET ring_carrier r
        ==> (prime_ideal r' (IMAGE f j) <=> prime_ideal r j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_ISOMORPHIC_IMAGE_EQ) THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (q' ==> p') /\ (p' ==> (q' <=> q))
    ==> (p' <=> p) ==> (q' <=> q)`) THEN
  REWRITE_TAC[PRIME_IMP_RING_IDEAL] THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRIME_IDEAL_CORRESPONDENCE THEN
  EXISTS_TAC `f:A->B` THEN ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_EPIMORPHISM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_isomorphism; ring_isomorphisms]) THEN
  ASM SET_TAC[]);;

let MAXIMAL_IDEAL_CORRESPONDENCE = prove
 (`!r r' (f:A->B) j k.
           ring_epimorphism (r,r') f /\
           ring_ideal r' k /\
           {x | x IN ring_carrier r /\ f x IN k} = j
        ==> (maximal_ideal r j <=> maximal_ideal r' k)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `f:A->B`]
    RING_IDEAL_HOMOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[GSYM FIELD_QUOTIENT_RING;
                RING_EPIMORPHISM_IMP_HOMOMORPHISM] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC ISOMORPHIC_RING_FIELDNESS THEN
  MATCH_MP_TAC FIRST_RING_ISOMORPHISM_THEOREM_GEN THEN
  EXISTS_TAC `f:A->B` THEN ASM_REWRITE_TAC[]);;

let MAXIMAL_IDEAL_EPIMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B) j.
        ring_epimorphism(r,r') f /\ maximal_ideal r' j
        ==> maximal_ideal r {x | x IN ring_carrier r /\ f x IN j}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  UNDISCH_TAC `maximal_ideal r' (j:B->bool)` THEN
  MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MAXIMAL_IDEAL_CORRESPONDENCE THEN
  EXISTS_TAC `f:A->B` THEN ASM_REWRITE_TAC[]);;

let MAXIMAL_IDEAL_ISOMORPHIC_IMAGE_EQ = prove
 (`!r r' (f:A->B) j.
        ring_isomorphism(r,r') f /\ j SUBSET ring_carrier r
        ==> (maximal_ideal r' (IMAGE f j) <=> maximal_ideal r j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_ISOMORPHIC_IMAGE_EQ) THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (q' ==> p') /\ (p' ==> (q' <=> q))
    ==> (p' <=> p) ==> (q' <=> q)`) THEN
  REWRITE_TAC[MAXIMAL_IMP_RING_IDEAL] THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MAXIMAL_IDEAL_CORRESPONDENCE THEN
  EXISTS_TAC `f:A->B` THEN ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_EPIMORPHISM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_isomorphism; ring_isomorphisms]) THEN
  ASM SET_TAC[]);;

let ISOMORPHIC_RING_PIDNESS = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> (PID r <=> PID r')`,
  let lemma = prove
   (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> PID r ==> PID r'`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[PID] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ISOMORPHIC_RING_INTEGRAL_DOMAINNESS]; ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `k:B->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `f:A->B` MP_TAC o
      REWRITE_RULE[isomorphic_ring]) THEN
    REWRITE_TAC[ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `g:B->A` THEN REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (g:B->A) k`) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_EPIMORPHIC_IMAGE;
                    RING_ISOMORPHISM_IMP_EPIMORPHISM];
      REWRITE_TAC[principal_ideal]] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(f:A->B) a` THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[RING_ISOMORPHISM]) THEN ASM SET_TAC[];
      ONCE_REWRITE_TAC[SET_RULE `{f a} = IMAGE f {a}`]] THEN
    MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `f:A->B`]
        IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[SING_SUBSET; RING_ISOMORPHISM_IMP_EPIMORPHISM] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN ASM SET_TAC[]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  ASM_REWRITE_TAC[]);;

let FIELD_HOMOMORPHISM_IMP_MONOMORPHISM = prove
 (`!r r' (f:A->B).
        ring_homomorphism(r,r') f /\ field r
        ==> (!x. x IN ring_carrier r ==> f x = ring_0 r') \/
            ring_monomorphism(r,r') f`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[RING_MONOMORPHISM] THEN
  FIRST_ASSUM(MP_TAC o SPEC `ring_kernel(r,r') (f:A->B)` o
    CONJUNCT2 o GEN_REWRITE_RULE I [FIELD_EQ_TRIVIAL_IDEALS]) THEN
  ASM_SIMP_TAC[RING_IDEAL_RING_KERNEL] THEN
  REWRITE_TAC[ring_kernel] THEN SET_TAC[]);;

let FIELD_EPIMORPHISM_IMP_ISOMORPHISM = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f /\ field r
        ==> (!x. x IN ring_carrier r ==> f x = ring_0 r') \/
            ring_isomorphism(r,r') f`,
  SIMP_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  MESON_TAC[FIELD_HOMOMORPHISM_IMP_MONOMORPHISM;
            RING_EPIMORPHISM_IMP_HOMOMORPHISM]);;

let RING_EPIMORPHISM_ONTO_FIELD_EXISTS = prove
 (`!r:A ring.
        ~(trivial_ring r)
        ==> ?s (f:A->A->bool). ring_epimorphism(r,s) f /\ field s`,
  GEN_TAC THEN REWRITE_TAC[GSYM MAXIMAL_IDEAL_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:A->bool`) THEN
  EXISTS_TAC `quotient_ring r (j:A->bool)` THEN
  EXISTS_TAC `ring_coset r (j:A->bool)` THEN
  ASM_SIMP_TAC[FIELD_QUOTIENT_RING; MAXIMAL_IMP_RING_IDEAL;
               RING_EPIMORPHISM_RING_COSET]);;

(* ------------------------------------------------------------------------- *)
(* The radical ideal and in particular the nilradical                        *)
(* ------------------------------------------------------------------------- *)

let radical = new_definition
 `radical r j = {x:A | x IN ring_carrier r /\
                       ?n. ~(n = 0) /\ ring_pow r x n IN j}`;;

let RADICAL_SUBSET = prove
 (`!r j:A->bool. j SUBSET radical r j <=> j SUBSET ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[radical] THEN
  EQ_TAC THENL [SET_TAC[]; REWRITE_TAC[SUBSET; IN_ELIM_THM]] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN EXISTS_TAC `1` THEN
  ASM_SIMP_TAC[RING_POW_1] THEN CONV_TAC NUM_REDUCE_CONV);;

let RADICAL_MONO = prove
 (`!r j k:A->bool. j SUBSET k ==> radical r j SUBSET radical r k`,
  REWRITE_TAC[radical] THEN SET_TAC[]);;

let RING_IDEAL_RADICAL = prove
 (`!r j:A->bool. ring_ideal r j ==> ring_ideal r (radical r j)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ring_ideal; radical; SUBSET] THEN
  SIMP_TAC[IN_ELIM_THM; RING_0] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `1` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[RING_POW_1; RING_0; IN_RING_IDEAL_0];
    X_GEN_TAC `x:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[RING_NEG] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_SIMP_TAC[RING_POW_NEG] THEN ASM_MESON_TAC[IN_RING_IDEAL_NEG];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    DISCH_THEN(CONJUNCTS_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_ADD] THEN EXISTS_TAC `m + n:num` THEN
    ASM_SIMP_TAC[RING_BINOMIAL_THEOREM; ADD_EQ_0] THEN
    MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN
    ASM_REWRITE_TAC[RING_OF_NUM] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (ARITH_RULE
     `k:num <= m + n ==> k = m + (k - m) \/ (m + n) - k = n + (m - k)`))
    THENL
     [MATCH_MP_TAC IN_RING_IDEAL_RMUL; MATCH_MP_TAC IN_RING_IDEAL_LMUL] THEN
    ASM_SIMP_TAC[RING_POW] THEN ASM_SIMP_TAC[RING_POW_ADD] THEN
    MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC[RING_POW];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[RING_MUL] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_SIMP_TAC[RING_MUL_POW] THEN
    ASM_MESON_TAC[IN_RING_IDEAL_LMUL; RING_POW]]);;

let RADICAL_0 = prove
 (`!r:A ring. radical r {ring_0 r} = {x | ring_nilpotent r x}`,
  GEN_TAC THEN REWRITE_TAC[radical; ring_nilpotent; IN_SING]);;

let RADICAL_RING_CARRIER = prove
 (`!r:A ring. radical r (ring_carrier r) = ring_carrier r`,
  REWRITE_TAC[radical; EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[ARITH_RULE `~(1 = 0)`; RING_POW]);;

let RADICAL_ALT = prove
 (`!r j:A->bool.
      ring_ideal r j
      ==> radical r j = {x | x IN ring_carrier r /\ ?n. ring_pow r x n IN j}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `j:A->bool = ring_carrier r` THENL
   [ASM_REWRITE_TAC[RADICAL_RING_CARRIER; EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[RING_POW];
    REWRITE_TAC[radical]] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `~P 0 ==> ((?n. ~(n = 0) /\ P n) <=> (?n. P n))`) THEN
  REWRITE_TAC[ring_pow] THEN ASM_MESON_TAC[PROPER_IDEAL; PROPER_IDEAL_ALT]);;

let RING_POW_IN_RADICAL = prove
 (`!r j (x:A) n.
        ring_ideal r j /\ x IN ring_carrier r /\ ~(n = 0)
        ==> (ring_pow r x n IN radical r j <=> x IN radical r j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RADICAL_ALT; IN_ELIM_THM; RING_POW] THEN
  ASM_SIMP_TAC[GSYM RING_POW_MUL] THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[RING_POW_MUL] THEN
  ASM_SIMP_TAC[RING_POW_IN_IDEAL]);;

let INTEGRAL_DOMAIN_NILRADICAL = prove
 (`!r:A ring. integral_domain r ==> radical r {ring_0 r} = {ring_0 r}`,
  SIMP_TAC[INTEGRAL_DOMAIN_NILPOTENT; RADICAL_0; SING_GSPEC]);;

let FIELD_NILRADICAL = prove
 (`!r:A ring. field r ==> radical r {ring_0 r} = {ring_0 r}`,
  SIMP_TAC[INTEGRAL_DOMAIN_NILRADICAL; FIELD_IMP_INTEGRAL_DOMAIN]);;

let RADICAL = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> radical r j = if j = ring_carrier r then ring_carrier r
                          else INTERS {k | prime_ideal r k /\ j SUBSET k}`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[RADICAL_RING_CARRIER] THEN
  ASM_SIMP_TAC[RADICAL_ALT; EXTENSION; IN_ELIM_THM; INTERS_GSPEC] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [ASM_MESON_TAC[RING_POW_IN_PRIME_IDEAL; SUBSET]; DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] PRIME_SUPERIDEAL_EXISTS) THEN
    ASM_REWRITE_TAC[PROPER_IDEAL_ALT] THEN
    ASM_MESON_TAC[PRIME_IDEAL_IMP_SUBSET; SUBSET];
    DISCH_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `{ring_pow r (x:A) n | n IN (:num)}`;
                 `j:A->bool`] PRIME_SUPERIDEAL_EXCLUDING_EXISTS) THEN
  ASM_SIMP_TAC[RING_MULTSYS_POWERS] THEN
  MATCH_MP_TAC(TAUT `(~p ==> r) /\ ~q ==> (p ==> q) ==> r`) THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `DISJOINT k {f n | n IN (:num)} ==> ~(f 1 IN k)`)) THEN
  ASM_SIMP_TAC[RING_POW_1]);;

let RING_NILRADICAL = prove
 (`!r:A ring.
        radical r {ring_0 r} =
        if trivial_ring r then {ring_0 r}
        else INTERS {j | prime_ideal r j}`,
  GEN_TAC THEN SIMP_TAC[RADICAL; RING_IDEAL_0] THEN
  ASM_CASES_TAC `trivial_ring(r:A ring)` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[trivial_ring]) THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; SING_SUBSET] THEN
  MESON_TAC[IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL]);;

let INTERS_PRIME_IDEALS = prove
 (`!r:A ring.
    ~(trivial_ring r) ==> INTERS {j | prime_ideal r j} = radical r {ring_0 r}`,
  SIMP_TAC[RING_NILRADICAL]);;

let RADICAL_RADICAL = prove
 (`!r j:A->bool. radical r (radical r j) = radical r j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; radical; IN_ELIM_THM] THEN
  X_GEN_TAC `a:A` THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN ASM_SIMP_TAC[RING_POW] THEN
  ASM_SIMP_TAC[RIGHT_AND_EXISTS_THM; GSYM RING_POW_MUL] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `n * m:num` THEN ASM_SIMP_TAC[MULT_EQ_0];
    MAP_EVERY EXISTS_TAC [`1`; `n:num`] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ARITH]]);;

let RADICAL_EQ_CARRIER = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> (radical r j = ring_carrier r <=> j = ring_carrier r)`,
  SIMP_TAC[RING_IDEAL_EQ_CARRIER; RING_IDEAL_RADICAL] THEN
  SIMP_TAC[RADICAL_ALT; IN_ELIM_THM; RING_POW_ONE; RING_1]);;

let PROPER_RADICAL = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> (proper_ideal r (radical r j) <=> proper_ideal r j)`,
  SIMP_TAC[PROPER_IDEAL_ALT; RADICAL_EQ_CARRIER;
           RING_IDEAL_RADICAL]);;

let RADICAL_UNIONS = prove
 (`!r u:(A->bool)->bool.
        radical r (UNIONS u) = UNIONS {radical r j | j IN u}`,
  REWRITE_TAC[radical; UNIONS_GSPEC] THEN SET_TAC[]);;

let RADICAL_UNION = prove
 (`!r j k:A->bool.
        radical r (j UNION k) = radical r j UNION radical r k`,
  REWRITE_TAC[radical] THEN SET_TAC[]);;

let RADICAL_INTER = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k
        ==> radical r (j INTER k) = radical r j INTER radical r k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[RADICAL_ALT; RING_IDEAL_INTER] THEN
  CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER]] THEN
  X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN ring_carrier r` THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `m:num`) (X_CHOOSE_TAC `n:num`)) THEN
  EXISTS_TAC `m + n:num` THEN
  ASM_SIMP_TAC[RING_POW_ADD; IN_RING_IDEAL_LMUL; IN_RING_IDEAL_RMUL;
               RING_POW]);;

let RADICAL_SETADD = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k
        ==> radical r (ring_setadd r (radical r j) (radical r k)) =
            radical r (ring_setadd r j k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM RADICAL_RADICAL] THEN
    MATCH_MP_TAC RADICAL_MONO THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SETADD_SUBRING o rand o snd) THEN
    ASM_SIMP_TAC[RING_IDEAL_RADICAL; RING_IDEAL_SETADD] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SETADD_MONO THEN
    CONJ_TAC THEN MATCH_MP_TAC RADICAL_MONO THENL
     [MATCH_MP_TAC RING_SETADD_SUPERSET_LEFT;
      MATCH_MP_TAC RING_SETADD_SUPERSET_RIGHT] THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; IN_RING_IDEAL_0];
    MATCH_MP_TAC RADICAL_MONO THEN
    MATCH_MP_TAC RING_SETADD_MONO THEN
    ASM_SIMP_TAC[RADICAL_SUBSET; RING_IDEAL_IMP_SUBSET]]);;

let COMAXIMAL_RADICALS = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k
        ==> (ring_setadd r (radical r j) (radical r k) = ring_carrier r <=>
             ring_setadd r j k = ring_carrier r)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) RADICAL_EQ_CARRIER o
    rand o snd) THEN
  ASM_SIMP_TAC[RING_IDEAL_SETADD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  W(MP_TAC o PART_MATCH (rand o rand) RADICAL_EQ_CARRIER o
    lhand o snd) THEN
  ASM_SIMP_TAC[RING_IDEAL_SETADD; RING_IDEAL_RADICAL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[RADICAL_SETADD]);;

let RADICAL_PRIME_IDEAL = prove
 (`!r j:A->bool. prime_ideal r j ==> radical r j = j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IDEAL_IMP_SUBSET) THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; RADICAL_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; radical] THEN
  ASM_SIMP_TAC[IMP_CONJ; RING_POW_IN_PRIME_IDEAL] THEN MESON_TAC[]);;

let RADICAL_SUBSET_PRIME_IDEAL_EQ = prove
 (`!r j k:A->bool.
        j SUBSET ring_carrier r /\ prime_ideal r k
        ==> (radical r j SUBSET k <=> j SUBSET k)`,
  MESON_TAC[RADICAL_PRIME_IDEAL; RADICAL_SUBSET; SUBSET_TRANS; RADICAL_MONO]);;

let RADICAL_IDEAL_PRIME_IDEAL_EQ = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ prime_ideal r k
        ==> (radical r j SUBSET k <=> j SUBSET k)`,
  SIMP_TAC[RADICAL_SUBSET_PRIME_IDEAL_EQ; RING_IDEAL_IMP_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* More closure properties for nilpotents etc. (could be put earlier but     *)
(* the proofs would sometimes be a bit longer).                              *)
(* ------------------------------------------------------------------------- *)

let RING_NILPOTENT_ADD = prove
 (`!r x y:A.
        ring_nilpotent r x /\ ring_nilpotent r y
        ==> ring_nilpotent r (ring_add r x y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(MATCH_MP RING_IDEAL_RADICAL (SPEC `r:A ring` RING_IDEAL_0)) THEN
  REWRITE_TAC[RADICAL_0; ring_ideal] THEN SET_TAC[]);;

let RING_NILPOTENT_LMUL = prove
 (`!r x y:A.
        x IN ring_carrier r /\ ring_nilpotent r y
        ==> ring_nilpotent r (ring_mul r x y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(MATCH_MP RING_IDEAL_RADICAL (SPEC `r:A ring` RING_IDEAL_0)) THEN
  REWRITE_TAC[RADICAL_0; ring_ideal] THEN SET_TAC[]);;

let RING_NILPOTENT_RMUL = prove
 (`!r x y:A.
        ring_nilpotent r x /\ y IN ring_carrier r
        ==> ring_nilpotent r (ring_mul r x y)`,
  MESON_TAC[RING_NILPOTENT_LMUL; RING_MUL_SYM; RING_NILPOTENT_IN_CARRIER]);;

let RING_NILPOTENT_SUB = prove
 (`!r x y:A.
        ring_nilpotent r x /\ ring_nilpotent r y
        ==> ring_nilpotent r (ring_sub r x y)`,
  SIMP_TAC[ring_sub; RING_NILPOTENT_ADD; RING_NILPOTENT_NEG]);;

let RING_ZERODIVISOR_NILPOTENT_CLAUSES = prove
 (`(!r w z:A.
        ring_zerodivisor r w /\ ring_nilpotent r z
        ==> ring_zerodivisor r (ring_add r w z)) /\
   (!r w z:A.
        ring_nilpotent r z /\ ring_zerodivisor r w
        ==> ring_zerodivisor r (ring_add r z w)) /\
   (!r w z:A.
        ring_zerodivisor r w /\ ring_nilpotent r z
        ==> ring_zerodivisor r (ring_sub r w z)) /\
   (!r w z:A.
        ring_nilpotent r z /\ ring_zerodivisor r w
        ==> ring_zerodivisor r (ring_sub r z w))`,
  MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (p /\ q ==> r /\ s) /\ p ==> p /\ q /\ r /\ s`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[RING_ADD_SYM; RING_NILPOTENT_IN_CARRIER;
              RING_ZERODIVISOR_IN_CARRIER];
    SIMP_TAC[ring_sub; RING_ZERODIVISOR_NEG; RING_NILPOTENT_NEG];
    MAP_EVERY X_GEN_TAC [`r:A ring`; `x:A`; `z:A`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_ZERODIVISOR_IN_CARRIER) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_NILPOTENT_IN_CARRIER)] THEN
  ASM_SIMP_TAC[ring_zerodivisor; RING_ADD] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~p ==> F`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_zerodivisor]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. ~(ring_mul r (ring_pow r z n) w:A = ring_0 r)`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN ASM_SIMP_TAC[ring_pow; RING_MUL_LID] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ring_mul r w (ring_pow r z n):A` o
                  REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_SIMP_TAC[RING_MUL; RING_POW] THEN
    FIRST_ASSUM(MP_TAC o SYM) THEN RING_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_nilpotent]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_SIMP_TAC[RING_MUL_LZERO]]);;

let RING_REGULAR_NILPOTENT_CLAUSES = prove
 (`(!r w z:A.
        ring_regular r w /\ ring_nilpotent r z
        ==> ring_regular r (ring_add r w z)) /\
   (!r w z:A.
        ring_nilpotent r z /\ ring_regular r w
        ==> ring_regular r (ring_add r z w)) /\
   (!r w z:A.
        ring_regular r w /\ ring_nilpotent r z
        ==> ring_regular r (ring_sub r w z)) /\
   (!r w z:A.
        ring_nilpotent r z /\ ring_regular r w
        ==> ring_regular r (ring_sub r z w))`,
  MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (p /\ q ==> r /\ s) /\ p ==> p /\ q /\ r /\ s`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[RING_ADD_SYM; RING_NILPOTENT_IN_CARRIER;
              RING_REGULAR_IN_CARRIER];
    SIMP_TAC[ring_sub; RING_REGULAR_NEG; RING_NILPOTENT_NEG];
    MAP_EVERY X_GEN_TAC [`r:A ring`; `x:A`; `z:A`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_REGULAR_IN_CARRIER) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_NILPOTENT_IN_CARRIER)] THEN
  UNDISCH_TAC `ring_regular r (x:A)` THEN
  ASM_SIMP_TAC[ring_regular; RING_ADD; CONTRAPOS_THM] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `x:A = ring_sub r (ring_add r x z) z` SUBST1_TAC THENL
   [RING_TAC; ASM_SIMP_TAC[RING_ZERODIVISOR_NILPOTENT_CLAUSES]]);;

let RING_UNIT_NILPOTENT_CLAUSES_1 = prove
 (`(!r z:A. ring_nilpotent r z ==> ring_unit r (ring_add r (ring_1 r) z)) /\
   (!r z:A. ring_nilpotent r z ==> ring_unit r (ring_add r z (ring_1 r))) /\
   (!r z:A. ring_nilpotent r z ==> ring_unit r (ring_sub r (ring_1 r) z)) /\
   (!r z:A. ring_nilpotent r z ==> ring_unit r (ring_sub r z (ring_1 r)))`,
  SIMP_TAC[RING_NILPOTENT_IN_CARRIER; RING_RULE
    `z IN ring_carrier r
     ==> ring_add r z (ring_1 r) = ring_add r (ring_1 r) z /\
         ring_sub r z (ring_1 r) = ring_neg r (ring_sub r (ring_1 r) z)`] THEN
  SIMP_TAC[RING_UNIT_NEG_EQ; RING_SUB; RING_1; RING_NILPOTENT_IN_CARRIER] THEN
  MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> p /\ p /\ q`) THEN
  SIMP_TAC[RING_NILPOTENT_IN_CARRIER; RING_NILPOTENT_NEG; RING_RULE
    `z IN ring_carrier r
     ==> ring_add r (ring_1 r) z = ring_sub r (ring_1 r) (ring_neg r z)`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_nilpotent; ring_unit] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[RING_SUB; RING_1] THEN
  EXISTS_TAC `ring_sum r {i | i < n} (\i. ring_pow r z i):A` THEN
  REWRITE_TAC[RING_SUM] THEN
  GEN_REWRITE_TAC RAND_CONV [RING_RULE
    `ring_1 r = ring_sub r (ring_1 r) (ring_0 r)`] THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  UNDISCH_THEN `~(n = 0)` (K ALL_TAC) THEN SPEC_TAC(`n:num`,`k:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[NUMSEG_CLAUSES_LT] THEN
  ASM_SIMP_TAC[RING_SUM_CLAUSES; FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[ring_pow; RING_SUB_REFL; RING_MUL_RZERO; RING_SUB; RING_1;
               IN_ELIM_THM; LT_REFL; RING_POW] THEN
  ASM_SIMP_TAC[RING_ADD_LDISTRIB; RING_MUL; RING_SUB; RING_1; RING_SUM;
               RING_POW] THEN
  RING_TAC THEN REWRITE_TAC[RING_SUM]);;

let RING_UNIT_NILPOTENT_CLAUSES = prove
 (`(!r u z:A. ring_unit r u /\ ring_nilpotent r z
              ==> ring_unit r (ring_add r u z)) /\
   (!r u z:A. ring_nilpotent r z /\ ring_unit r u
              ==> ring_unit r (ring_add r z u)) /\
   (!r u z:A. ring_unit r u /\ ring_nilpotent r z
              ==> ring_unit r (ring_sub r u z)) /\
   (!r u z:A. ring_nilpotent r z /\ ring_unit r u
              ==> ring_unit r (ring_sub r z u))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_unit]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(RING_RULE
   `u IN ring_carrier r /\ v IN ring_carrier r /\ z IN ring_carrier r /\
    ring_mul r u v:A = ring_1 r
    ==> ring_add r u z =
        ring_mul r u (ring_add r (ring_1 r) (ring_mul r v z)) /\
        ring_add r z u =
        ring_mul r u (ring_add r (ring_1 r) (ring_mul r v z)) /\
        ring_sub r u z =
        ring_mul r u (ring_sub r (ring_1 r) (ring_mul r v z)) /\
        ring_sub r z u =
        ring_mul r u (ring_neg r
           (ring_sub r (ring_1 r) (ring_mul r v z)))`) THEN
  ASM_SIMP_TAC[RING_NILPOTENT_IN_CARRIER] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC RING_UNIT_MUL THEN
  ASM_SIMP_TAC[RING_UNIT_NILPOTENT_CLAUSES_1; RING_UNIT_NEG;
               RING_NILPOTENT_NEG; RING_NILPOTENT_LMUL] THEN
  ASM_MESON_TAC[RING_UNIT_MUL_EQ; RING_UNIT_1]);;

(* ------------------------------------------------------------------------- *)
(* UFDs. We use Kaplansky's characterization as the initial definition,      *)
(* since it has a nice compact and explicit form, but then we derive         *)
(* several other common definitions as "UFD if and only if ..." theorems.    *)
(* ------------------------------------------------------------------------- *)

let UFD = new_definition
 `UFD (r:A ring) <=>
        integral_domain r /\
        !j. prime_ideal r j /\ ~(j = {ring_0 r})
            ==> ?p. ring_prime r p /\ p IN j`;;

let UFD_IMP_INTEGRAL_DOMAIN = prove
 (`!r:A ring. UFD r ==> integral_domain r`,
  SIMP_TAC[UFD]);;

let PID_IMP_UFD = prove
 (`!r:A ring. PID r ==> UFD r`,
  GEN_TAC THEN REWRITE_TAC[PID; UFD] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[prime_ideal; proper_ideal]; SIMP_TAC[principal_ideal]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PRIME_IDEAL_SING]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [IDEAL_GENERATED_EQ_0]) THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_INC_GEN; IN_SING]);;

let FIELD_IMP_UFD = prove
 (`!r:A ring. field r ==> UFD r`,
  SIMP_TAC[FIELD_IMP_PID; PID_IMP_UFD]);;

let ISOMORPHIC_RING_UFDNESS = prove
 (`!(r:A ring) (r':B ring). r isomorphic_ring r' ==> (UFD r <=> UFD r')`,
  let lemma = prove
   (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> UFD r ==> UFD r'`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[UFD] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ISOMORPHIC_RING_INTEGRAL_DOMAINNESS]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `f:A->B` o REWRITE_RULE[isomorphic_ring]) THEN
    DISCH_TAC THEN X_GEN_TAC `k:B->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `{x | x IN ring_carrier r /\ (f:A->B) x IN k}`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN
        ASM_MESON_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM];
        RULE_ASSUM_TAC(REWRITE_RULE[RING_ISOMORPHISM; ring_homomorphism]) THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_IDEAL_IMP_SUBSET) THEN
        ASM SET_TAC[]];
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[RING_PRIME_ISOMORPHIC_IMAGE_EQ]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  ASM_REWRITE_TAC[]);;

let UFD_EQ_PRIMEFACT = prove
 (`!r:A ring.
        UFD r <=>
        integral_domain r /\
        !x. x IN ring_carrier r /\ ~(x = ring_0 r)
            ==> ?n p. (!i. 1 <= i /\ i <= n ==> ring_prime r (p i)) /\
                      ring_associates r (ring_product r (1..n) p) x`,
  GEN_TAC THEN REWRITE_TAC[UFD] THEN
  ASM_CASES_TAC `integral_domain(r:A ring)` THEN ASM_REWRITE_TAC[] THEN
  (X_CHOOSE_THEN `pp:A->bool` MP_TAC o prove_inductive_relations_exist)
   `(!u:A. ring_unit r u ==> pp u) /\
    !p a. ring_prime r p /\ pp a ==> pp (ring_mul r p a)` THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o ONCE_REWRITE_RULE[CONJ_ASSOC]) THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT1 th) THEN
                       MP_TAC(derive_strong_induction(CONJ_PAIR th))) THEN
  MP_TAC(ISPEC `pp:A->bool` IN) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:A. x IN pp ==> x IN ring_carrier r` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[ring_unit; ring_prime; RING_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x u:A. x IN pp /\ ring_unit r u ==> ring_mul r x u IN pp) /\
    (!u x:A. ring_unit r u /\ x IN pp ==> ring_mul r u x IN pp)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_UNIT_IN_CARRIER; RING_MUL_SYM];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM]] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[RING_UNIT_MUL; RING_MUL_AC; RING_PRIME_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:A. ring_prime r p ==> p IN pp` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_UNIT_1; RING_MUL_RID; RING_PRIME_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:A. x IN ring_carrier r /\ y IN ring_carrier r
            ==> (ring_mul r x y IN pp <=> x IN pp /\ y IN pp)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `!x:A. x IN pp ==> !y. y IN pp ==> ring_mul r x y IN pp`
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[RING_MUL_AC; RING_PRIME_IN_CARRIER];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!z:A. z IN pp
            ==> !x y:A. x IN ring_carrier r /\
                        y IN ring_carrier r /\
                        ring_mul r x y = z
                        ==> x IN pp /\ y IN pp`
    MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[RING_UNIT_MUL_EQ]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`p:A`; `z:A`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_MUL; RING_PRIME_IN_CARRIER] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_prime]) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_SIMP_TAC[RING_DIVIDES_RMUL; RING_DIVIDES_REFL] THEN
    REWRITE_TAC[ring_divides] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))
    THENL
     [SUBGOAL_THEN `(w:A) IN pp /\ y IN pp` MP_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[]];
      SUBGOAL_THEN `(x:A) IN pp /\ w IN pp` MP_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[]]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`r:A ring`; `p:A`] THEN
    ASM_SIMP_TAC[RING_MUL] THEN ASM_MESON_TAC[RING_MUL_AC; RING_MUL];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `!x:A. x IN ring_carrier r /\ ~(x = ring_0 r) ==> x IN pp` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `!j. prime_ideal r j
          ==> !x:A. x IN pp
                    ==> x IN j /\ ~(ring_unit r x)
                         ==> ?p. ring_prime r p /\ p IN pp /\ p IN j`
    MP_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`p:A`; `a:A`] THEN
      ASM_SIMP_TAC[RING_MUL_IN_PRIME_IDEAL; RING_PRIME_IN_CARRIER;
                   RING_UNIT_MUL_EQ] THEN
      ASM_CASES_TAC `(p:A) IN j` THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[ring_prime]; REPEAT STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [prime_ideal]) THEN
      ASM_REWRITE_TAC[PROPER_IDEAL_UNIT; prime_ideal] THEN ASM SET_TAC[];
      REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
      FIRST_X_ASSUM(K ALL_TAC o SPEC `ring_carrier r:A->bool`) THEN
      STRIP_TAC] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      ASM_CASES_TAC `(x:A) IN pp` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL
       [`r:A ring`; `pp:A->bool`; `ideal_generated r {x:A}`]
        PRIME_SUPERIDEAL_EXCLUDING_EXISTS) THEN
      REWRITE_TAC[NOT_IMP; RING_IDEAL_IDEAL_GENERATED] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC; ring_multsys; SUBSET] THEN
      ASM_SIMP_TAC[RING_UNIT_1; IDEAL_GENERATED_SING_ALT] THEN
      REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`] THEN
      ASM_SIMP_TAC[FORALL_IN_GSPEC] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:A->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool`) THEN
      ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
        DISCH_THEN(MP_TAC o SPEC `ring_mul r x (ring_1 r):A`) THEN
        ASM_MESON_TAC[RING_1; IN_SING; RING_MUL_RID];
        ASM_MESON_TAC[RING_MUL_RID; RING_UNIT_1; RING_PRIME_IN_CARRIER]];
      X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `?z:A. z IN j /\ z IN ring_carrier r /\
              ~(z = ring_0 r) /\ ~(ring_unit r z)`
      STRIP_ASSUME_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [prime_ideal]) THEN
      REWRITE_TAC[PROPER_IDEAL_UNIT; ring_ideal] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(!x. R x ==> Q x) /\ (!x. Q x ==> R x)
    ==> ((!x. P x ==> Q x) <=> (!x. P x ==> R x))`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(K ALL_TAC o SPEC `ring_carrier r:A->bool`) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_ASSOCIATES] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:A`; `n:num`; `p:num->A`; `u:A`] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    SUBGOAL_THEN `!m:num. m <= n ==> ring_product r (1..m) p:A IN pp`
    MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE_REFL]] THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[RING_PRODUCT_CLAUSES_NUMSEG_ALT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[RING_UNIT_1] THEN
    ASM_MESON_TAC[ARITH_RULE `SUC m <= n ==> m <= n`; RING_PRODUCT;
                  RING_PRIME_IN_CARRIER; ARITH_RULE `1 <= SUC n`];
    FIRST_X_ASSUM MATCH_MP_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`] THEN
    REWRITE_TAC[RING_PRODUCT_CLAUSES_NUMSEG_ALT; ARITH_EQ] THEN
    ASM_REWRITE_TAC[RING_ASSOCIATES_1];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `z:A`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `q:num->A`] THEN STRIP_TAC THEN
  EXISTS_TAC `SUC n` THEN
  EXISTS_TAC `\i. if i = SUC n then p else (q:num->A) i` THEN
  REWRITE_TAC[RING_PRODUCT_CLAUSES_NUMSEG_ALT; ARITH_RULE `1 <= SUC n`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LE]; ASM_SIMP_TAC[RING_PRIME_IN_CARRIER]] THEN
  MATCH_MP_TAC RING_ASSOCIATES_MUL THEN
  ASM_SIMP_TAC[RING_ASSOCIATES_REFL; RING_PRIME_IN_CARRIER] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `ring_associates r x z ==> y = x ==> ring_associates r y z`)) THEN
  MATCH_MP_TAC RING_PRODUCT_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
  MESON_TAC[ARITH_RULE `~(SUC n <= n)`]);;

let UFD_EQ_PRIMEFACT_NONUNIT = prove
 (`!r:A ring.
        UFD r <=>
        integral_domain r /\
        !x. x IN ring_carrier r /\ ~(x = ring_0 r) /\ ~(ring_unit r x)
            ==> ?n p. 1 <= n /\
                      (!i. 1 <= i /\ i <= n ==> ring_prime r (p i)) /\
                      ring_product r (1..n) p = x`,
  GEN_TAC THEN REWRITE_TAC[UFD_EQ_PRIMEFACT] THEN
  ASM_CASES_TAC `integral_domain(r:A ring)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MONO_EXISTS THEN MATCH_MP_TAC num_INDUCTION THEN
    ASM_REWRITE_TAC[RING_PRODUCT_CLAUSES_NUMSEG_ALT; ARITH_EQ] THEN
    ASM_REWRITE_TAC[RING_ASSOCIATES_1; ARITH_RULE `1 <= SUC n`] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num->A`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`; LE_REFL; RING_PRIME_IN_CARRIER] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_ASSOCIATES] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A`
     (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) o CONJUNCT2) THEN
    EXISTS_TAC `\i. if i = SUC n then ring_mul r u (p(SUC n):A) else p i` THEN
    ASM_SIMP_TAC[RING_MUL; RING_PRIME_IN_CARRIER; ARITH_RULE `1 <= SUC n`;
                 LE_REFL; RING_UNIT_IN_CARRIER] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[LE] THEN DISCH_THEN(K ALL_TAC) THEN
      FIRST_ASSUM(MP_TAC o SPEC `SUC n`) THEN
      ANTS_TAC THENL [ARITH_TAC; MATCH_MP_TAC EQ_IMP] THEN
      MATCH_MP_TAC RING_ASSOCIATES_PRIME THEN
      MATCH_MP_TAC RING_ASSOCIATES_LMUL THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`; LE_REFL; RING_PRIME_IN_CARRIER];
      MATCH_MP_TAC(MESON[]
       `f (f u q) p' = f (f q p') u /\ p' = p
        ==> f (f u q) p = f (f q p') u`) THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[RING_MUL_AC; RING_PRODUCT; RING_UNIT_IN_CARRIER;
                     ARITH_RULE `1 <= SUC n`; LE_REFL; RING_PRIME_IN_CARRIER];
        MATCH_MP_TAC RING_PRODUCT_EQ THEN GEN_TAC THEN
        REWRITE_TAC[IN_NUMSEG] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`]]];
    ASM_CASES_TAC `ring_unit r (x:A)` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `0` THEN
      REWRITE_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`] THEN
      REWRITE_TAC[RING_PRODUCT_CLAUSES_NUMSEG_ALT; ARITH_EQ] THEN
      ASM_REWRITE_TAC[RING_ASSOCIATES_1];
      MESON_TAC[RING_ASSOCIATES_REFL; RING_PRODUCT]]]);;

let UFD_PRIME_FACTOR_EXISTS = prove
 (`!r x:A.
        UFD r /\ x IN ring_carrier r /\ ~(x = ring_0 r) /\ ~(ring_unit r x)
        ==> ?p. ring_prime r p /\ ring_divides r p x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [UFD_EQ_PRIMEFACT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A`)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `xs:num->A`] THEN
  DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES_NUMSEG; ARITH_EQ; RING_ASSOCIATES_1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES_LEFT; LE_REFL; RING_PRIME_IN_CARRIER] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_DIVIDES_ASSOCIATES) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        (REWRITE_RULE[CONJ_ASSOC] RING_DIVIDES_RMUL_REV))) THEN
  ASM_MESON_TAC[RING_PRODUCT; LE_REFL; RING_PRIME_IN_CARRIER]);;

let UFD_IRREDUCIBLE_EQ_PRIME = prove
 (`!r p:A. UFD r ==> (ring_irreducible r p <=> ring_prime r p)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[UFD; INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE]] THEN
  ASM_MESON_TAC[RING_PRIME_DIVIDES_IRREDUCIBLE; UFD_PRIME_FACTOR_EXISTS;
                ring_irreducible]);;

let UFD_EQ_ATOMIC = prove
 (`!r:A ring.
        UFD r <=>
        integral_domain r /\
        (!p. ring_irreducible r p ==> ring_prime r p) /\
        (!x. x IN ring_carrier r /\ ~(x = ring_0 r)
             ==> ?n p. (!i. 1 <= i /\ i <= n ==> ring_irreducible r (p i)) /\
                       ring_associates r (ring_product r (1..n) p) x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `!p:A. ring_irreducible r p <=> ring_prime r p` THENL
   [ASM_REWRITE_TAC[UFD_EQ_PRIMEFACT];
    ASM_MESON_TAC[UFD_IRREDUCIBLE_EQ_PRIME; UFD;
                  INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE]]);;

let UFD_EQ_ATOMIC_NONUNIT = prove
 (`!r:A ring.
        UFD r <=>
        integral_domain r /\
        (!p. ring_irreducible r p ==> ring_prime r p) /\
        (!x. x IN ring_carrier r /\ ~(x = ring_0 r) /\ ~(ring_unit r x)
             ==> ?n p. 1 <= n /\
                       (!i. 1 <= i /\ i <= n ==> ring_irreducible r (p i)) /\
                       ring_product r (1..n) p = x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `!p:A. ring_irreducible r p <=> ring_prime r p` THENL
   [ASM_REWRITE_TAC[UFD_EQ_PRIMEFACT_NONUNIT];
    ASM_MESON_TAC[UFD_IRREDUCIBLE_EQ_PRIME; UFD;
                  INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE]]);;

let UFD_EQ_UNIQUE_FACTORIZATION = prove
 (`!r:A ring.
     UFD r <=>
     integral_domain r /\
     !x. x IN ring_carrier r /\ ~(x = ring_0 r)
         ==> ?n p. (!i. 1 <= i /\ i <= n ==> ring_irreducible r (p i)) /\
                   ring_associates r (ring_product r (1..n) p) x /\
                   !m q. (!j. 1 <= j /\ j <= m ==> ring_irreducible r (q j)) /\
                         ring_associates r (ring_product r (1..m) q) x
                         ==> ?f. IMAGE f (1..n) = 1..m /\
                                 (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n
                                        ==> (f i = f j <=> i = j)) /\
                                 (!i. 1 <= i /\ i <= n
                                      ==> ring_associates r (p i) (q(f i)))`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I  [UFD_EQ_PRIMEFACT]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_SIMP_TAC[UFD_IRREDUCIBLE_EQ_PRIME] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num->A` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `q:num->A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `1..n`; `p:num->A`; `1..m`; `q:num->A`]
      RING_ASSOCIATES_PRIMEFACTS_BIJECTION) THEN
    REWRITE_TAC[INJECTIVE_ON_ALT] THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[RING_ASSOCIATES_TRANS; RING_ASSOCIATES_SYM;
                  UFD_IRREDUCIBLE_EQ_PRIME];
    STRIP_TAC THEN
    ASM_REWRITE_TAC[UFD_EQ_ATOMIC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]]] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN REWRITE_TAC[ring_prime] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ring_irreducible]; STRIP_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[RING_MUL; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `a:A = ring_0 r` THEN ASM_REWRITE_TAC[RING_DIVIDES_0] THEN
  ASM_CASES_TAC `b:A = ring_0 r` THEN ASM_REWRITE_TAC[RING_DIVIDES_0] THEN
  ASM_CASES_TAC `c:A = ring_0 r` THENL
   [ASM_MESON_TAC[RING_MUL_RZERO; integral_domain]; ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `c:A` th) THEN
    MP_TAC(SPEC `b:A` th) THEN
    MP_TAC(SPEC `a:A` th) THEN
    MP_TAC(SPEC `ring_mul r a b:A` th)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[integral_domain; RING_MUL]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n_ab:num`; `p_ab:num->A`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n_a:num`; `p_a:num->A`] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(K ALL_TAC) THEN
  MAP_EVERY X_GEN_TAC [`n_b:num`; `p_b:num->A`] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(K ALL_TAC) THEN
  MAP_EVERY X_GEN_TAC [`n_c:num`; `p_c:num->A`] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL
     [`n_a + n_b:num`;
      `\i. if i <= n_a then (p_a:num->A) i else p_b(i - n_a)`] th) THEN
    MP_TAC(SPECL
      [`SUC n_c`; `\i. if i = SUC n_c then p else (p_c:num->A) i`] th)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [REWRITE_TAC[LE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_PRODUCT_CLAUSES_NUMSEG_ALT; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC RING_ASSOCIATES_MUL THEN
    ASM_REWRITE_TAC[RING_ASSOCIATES_REFL] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
      MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] RING_ASSOCIATES_TRANS)) THEN
    MATCH_MP_TAC(MESON[RING_ASSOCIATES_REFL]
     `y IN ring_carrier r /\ x = y ==> ring_associates r x y`) THEN
    REWRITE_TAC[RING_PRODUCT] THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
    GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= n_ab /\
                    ring_associates r (p_ab k) (p:A)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `f:num->num` MP_TAC) THEN
    REWRITE_TAC[numseg] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= n_ab /\ f(k) = SUC n_c` MP_TAC THENL
     [MP_TAC(ARITH_RULE `1 <= SUC n_c /\ SUC n_c <= SUC n_c`); ALL_TAC] THEN
    ASM SET_TAC[];
    FIRST_X_ASSUM(K ALL_TAC o check (is_exists o concl))] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[NUMSEG_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_UNION o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG; DISJOINT; EXTENSION; IN_ELIM_THM] THEN
      REWRITE_TAC[NOT_IN_EMPTY; IN_INTER; IN_NUMSEG] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    SUBST1_TAC(SYM(ASSUME `ring_mul r a b:A = ring_mul r p c`)) THEN
    MATCH_MP_TAC RING_ASSOCIATES_MUL THEN CONJ_TAC THEN
   FIRST_X_ASSUM(MATCH_MP_TAC o
      MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] RING_ASSOCIATES_TRANS)) THEN
    MATCH_MP_TAC(MESON[RING_ASSOCIATES_REFL]
     `y IN ring_carrier r /\ x = y ==> ring_associates r x y`) THEN
    REWRITE_TAC[RING_PRODUCT] THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ THEN
      GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[NUMSEG_OFFSET_IMAGE] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_IMAGE o lhand o snd) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_PRODUCT_EQ THEN
    GEN_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG; o_THM] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_SUB] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN DISCH_TAC THENL
   [DISJ1_TAC THEN TRANS_TAC RING_DIVIDES_TRANS `(p_ab:num->A) k` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[RING_DIVIDES_ASSOCIATES; RING_ASSOCIATES_SYM];
      ALL_TAC] THEN
    TRANS_TAC RING_DIVIDES_TRANS
     `ring_product r {f(k:num)} (p_a:num->A)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[RING_PRODUCT_SING; o_DEF] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[RING_DIVIDES_ASSOCIATES] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT
       `~p ==> p ==> q`)) THEN
      MATCH_MP_TAC RING_IRREDUCIBLE_IN_CARRIER THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[numseg]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    TRANS_TAC RING_DIVIDES_TRANS
     `ring_product r (1..n_a) (p_a:num->A)` THEN
    ASM_SIMP_TAC[RING_DIVIDES_ASSOCIATES] THEN
    MATCH_MP_TAC RING_DIVIDES_PRODUCT_SUBSET THEN
    REWRITE_TAC[FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[numseg]) THEN ASM SET_TAC[];
    DISJ2_TAC THEN TRANS_TAC RING_DIVIDES_TRANS `(p_ab:num->A) k` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[RING_DIVIDES_ASSOCIATES; RING_ASSOCIATES_SYM];
      ALL_TAC] THEN
    TRANS_TAC RING_DIVIDES_TRANS
     `ring_product r {f(k:num) - n_a} (p_b:num->A)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[RING_PRODUCT_SING; o_DEF] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[RING_DIVIDES_ASSOCIATES] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT
       `~p ==> p ==> q`)) THEN
      MATCH_MP_TAC RING_IRREDUCIBLE_IN_CARRIER THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE
       `1 <= k /\ k <= a + b /\ ~(k <= a)
        ==> 1 <= k - a /\ k - a <= b`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[numseg]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    TRANS_TAC RING_DIVIDES_TRANS
     `ring_product r (1..n_b) (p_b:num->A)` THEN
    ASM_SIMP_TAC[RING_DIVIDES_ASSOCIATES] THEN
    MATCH_MP_TAC RING_DIVIDES_PRODUCT_SUBSET THEN
    REWRITE_TAC[FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG] THEN
    MATCH_MP_TAC(ARITH_RULE
       `1 <= k /\ k <= a + b /\ ~(k <= a)
        ==> 1 <= k - a /\ k - a <= b`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[numseg]) THEN ASM SET_TAC[]]);;

let UFD_COPRIME = prove
 (`!r a b:A.
        UFD r
        ==> (ring_coprime r (a,b) <=>
             a IN ring_carrier r /\ b IN ring_carrier r /\
             ~(a = ring_0 r /\ b = ring_0 r) /\
             !p. ring_prime r p
                 ==> ~(ring_divides r p a /\ ring_divides r p b))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `a:A = ring_0 r /\ b = ring_0 r` THENL
   [ASM_REWRITE_TAC[RING_0; RING_COPRIME_00; RING_DIVIDES_0] THEN
    ASM_MESON_TAC[UFD; integral_domain; TRIVIAL_RING_10];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ring_coprime] THEN
  EQ_TAC THENL [MESON_TAC[ring_prime]; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `d:A` THEN
  ASM_CASES_TAC `d:A = ring_0 r` THEN ASM_REWRITE_TAC[RING_DIVIDES_ZERO] THEN
  STRIP_TAC THEN ASM_CASES_TAC `ring_unit r (d:A)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `d:A`] UFD_PRIME_FACTOR_EXISTS) THEN
  ASM_MESON_TAC[RING_DIVIDES_TRANS; RING_DIVIDES_IN_CARRIER]);;

let UFD_PRIME_FACTOR_INDUCT = prove
 (`!r P:A->bool.
        UFD r /\
        P(ring_0 r) /\
        (!u. ring_unit r u ==> P u) /\
        (!p a. ring_prime r p /\ a IN ring_carrier r /\ P a
               ==> P(ring_mul r p a))
        ==> !a. a IN ring_carrier r ==> P a`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `a:A = ring_0 r` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ring_unit r (a:A)` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!(p:num->A) n.
        (!i. 1 <= i /\ i <= n ==> ring_prime r (p i))
        ==> P(ring_product r (1..n) p)`
  MP_TAC THENL
   [GEN_TAC;
    FIRST_ASSUM(MP_TAC o SPEC `a:A` o CONJUNCT2 o
     GEN_REWRITE_RULE I [UFD_EQ_PRIMEFACT_NONUNIT]) THEN
    ASM_MESON_TAC[]] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[RING_PRODUCT_CLAUSES_NUMSEG_ALT; ARITH_EQ] THEN
  ASM_SIMP_TAC[RING_UNIT_1; LE_REFL; ARITH_RULE `1 <= SUC n`;
               RING_PRIME_IN_CARRIER] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[RING_PRODUCT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let UFD_IMP_GCD_EXISTS = prove
 (`!r a b:A.
        UFD r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> ?d. d IN ring_carrier r /\
                ring_divides r d a /\ ring_divides r d b /\
                !d'. ring_divides r d' a /\ ring_divides r d' b
                     ==> ring_divides r d' d`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC UFD_PRIME_FACTOR_INDUCT THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[RING_DIVIDES_0] THEN MESON_TAC[RING_DIVIDES_REFL];
    SIMP_TAC[RING_DIVIDES_UNIT] THEN
    MESON_TAC[RING_DIVIDES_UNIT; RING_UNIT_DIVIDES_ANY; RING_DIVIDES_REFL];
    MAP_EVERY X_GEN_TAC [`p:A`; `m:A`] THEN STRIP_TAC THEN
    X_GEN_TAC `b:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `p:A`; `b:A`]
        INTEGRAL_DOMAIN_PRIME_DIVIDES_OR_COPRIME) THEN
    ASM_SIMP_TAC[UFD_IMP_INTEGRAL_DOMAIN]] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:A`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:A`) THEN ASM_REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ring_mul r p d:A` THEN
    ASM_SIMP_TAC[RING_MUL; RING_DIVIDES_MUL2; RING_DIVIDES_REFL];
    FIRST_X_ASSUM(MP_TAC o SPEC `b:A`) THEN ASM_REWRITE_TAC[IMP_IMP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:A` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[RING_DIVIDES_LMUL; RING_PRIME_IN_CARRIER]] THEN
  X_GEN_TAC `e:A` THEN
  (ASM_CASES_TAC `(e:A) IN ring_carrier r` THENL
    [ALL_TAC; ASM_MESON_TAC[ring_divides]]) THEN
  ASM_CASES_TAC `ring_divides r (p:A) e` THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_DIVIDES_PRIME_LMUL;
               UFD_IMP_INTEGRAL_DOMAIN] THEN
  UNDISCH_TAC `ring_divides r (p:A) e` THEN
  GEN_REWRITE_TAC LAND_CONV [ring_divides] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d':A`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_DIVIDES_LMUL2; UFD_IMP_INTEGRAL_DOMAIN] THEN
  ASM_MESON_TAC[ring_prime; RING_DIVIDES_RMUL_REV;
                INTEGRAL_DOMAIN_PRIME_COPRIME_EQ; UFD_IMP_INTEGRAL_DOMAIN]);;

let PID_EQ_UFD_PRIME_MAXIMAL = prove
 (`!r:A ring.
        PID r <=>
        UFD r /\
        !j. prime_ideal r j /\ ~(j = {ring_0 r}) ==> maximal_ideal r j`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[PID_IMP_UFD; PID_MAXIMAL_EQ_PRIME_IDEAL] THEN
  STRIP_TAC THEN REWRITE_TAC[PID_EQ_INTEGRAL_DOMAIN_PRIME_PRINCIPAL] THEN
  ASM_SIMP_TAC[UFD_IMP_INTEGRAL_DOMAIN] THEN
  X_GEN_TAC `j:A->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j = {ring_0 r:A}` THEN
  ASM_REWRITE_TAC[PRINCIPAL_IDEAL_0] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [UFD]) THEN
  DISCH_THEN(MP_TAC o SPEC `j:A->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[principal_ideal] THEN EXISTS_TAC `p:A` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ideal_generated r {p:A}`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[IDEAL_GENERATED_EQ_0; ring_prime; RING_PRIME_IDEAL];
    REWRITE_TAC[maximal_ideal; NOT_EXISTS_THM]] THEN
  DISCH_THEN(MP_TAC o SPEC `j:A->bool` o CONJUNCT2) THEN
  ASM_SIMP_TAC[PRIME_IMP_PROPER_IDEAL] THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET t ==> ~(s PSUBSET t) ==> s = t`) THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_MINIMAL_EQ; PRIME_IMP_RING_IDEAL] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Euclidean rings.                                                          *)
(* ------------------------------------------------------------------------- *)

let euclidean_ring = new_definition
 `euclidean_ring r <=>
        ?n:A->num.
            !a b. a IN ring_carrier r /\ b IN ring_carrier r /\ ~(b = ring_0 r)
                  ==> ?q t. q IN ring_carrier r /\ t IN ring_carrier r /\
                            ring_add r (ring_mul r b q) t = a /\
                            (t = ring_0 r \/ n(t) < n(b))`;;

let EUCLIDEAN_RING = prove
 (`!r:A ring.
        euclidean_ring r <=>
        ?n:A->num.
            !a b. a IN ring_carrier r /\ b IN ring_carrier r /\
                  ~(b = ring_0 r) /\ n(b) <= n(a)
                  ==> ?q. q IN ring_carrier r /\
                          (ring_mul r b q = a \/
                           n(ring_sub r a (ring_mul r b q)) < n a)`,
  GEN_TAC THEN REWRITE_TAC[euclidean_ring] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `n:A->num` THEN
  REWRITE_TAC[] THEN EQ_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `q:A` THEN DISCH_THEN(X_CHOOSE_THEN `t:A` MP_TAC) THEN
    REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_CASES_TAC `t:A = ring_0 r` THEN
    ASM_SIMP_TAC[RING_MUL; RING_ADD_RZERO] THEN
    STRIP_TAC THEN DISJ2_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (ARITH_RULE `t:num < b ==> b <= a /\ u = t ==> u < a`)) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[RING_EQ_SUB_RADD; RING_MUL] THEN
    ASM_MESON_TAC[RING_ADD_SYM; RING_MUL];
    ALL_TAC] THEN
  ASM_CASES_TAC `ring_divides r b (a:A)` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `ring_0 r:A` THEN
    ASM_SIMP_TAC[RING_0; RING_ADD_RZERO; RING_MUL];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ring_divides]) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM; MESON[]
     `(!x. ~(P x /\ a = f x)) <=> !x. P x ==> ~(f x = a)`] THEN
    DISCH_TAC] THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC
   `\m. m IN IMAGE (n:A->num)
              {ring_sub r a (ring_mul r b q) | q | q IN ring_carrier r}`
   num_WOP))) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_IN_GSPEC] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC; NOT_LT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:A` THEN STRIP_TAC THEN
  EXISTS_TAC `ring_sub r a (ring_mul r b q):A` THEN
  ASM_SIMP_TAC[GSYM RING_EQ_SUB_LADD; RING_MUL; RING_SUB] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[ring_sub; RING_NEG_ADD; RING_NEG; RING_MUL; RING_NEG_NEG;
                 RING_ADD_ASSOC; RING_ADD_RNEG; RING_ADD_LZERO];
    DISJ2_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ring_sub r a (ring_mul r b q):A`; `b:A`]) THEN
  ASM_SIMP_TAC[RING_MUL; RING_SUB; RING_SUB_EQ_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_EQ_SUB_LADD; RING_MUL; GSYM RING_ADD_LDISTRIB] THEN
    ASM_SIMP_TAC[RING_ADD];
    ASM_SIMP_TAC[ring_sub; GSYM RING_NEG_ADD; GSYM RING_ADD_ASSOC;
                 RING_NEG; RING_MUL; GSYM RING_ADD_LDISTRIB; NOT_LT] THEN
    ASM_SIMP_TAC[GSYM ring_sub; RING_ADD]]);;

let EUCLIDEAN_RING_ALT = prove
 (`!r:A ring.
        euclidean_ring r <=>
         ?n:A->num.
           (!a b. ring_divides r a b /\ (b = ring_0 r ==> a = ring_0 r)
                  ==> n(a) <= n(b)) /\
           (!a b. a IN ring_carrier r /\ b IN ring_carrier r /\ ~(b = ring_0 r)
                   ==> ?q t. q IN ring_carrier r /\ t IN ring_carrier r /\
                            ring_add r (ring_mul r b q) t = a /\
                            (t = ring_0 r \/ n(t) < n(b)))`,
  GEN_TAC THEN REWRITE_TAC[euclidean_ring] THEN
  EQ_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:A->num`) THEN
  ASSUME_TAC(ISPEC `r:A ring` RING_0) THEN
  SUBGOAL_THEN
   `!a. a IN ring_carrier r /\ ~(a = ring_0 r)
        ==> ?m. m IN { (n:A->num) (ring_mul r a b) | b |
                       b IN ring_carrier r /\ ~(ring_mul r a b = ring_0 r)}`
  MP_TAC THENL
   [X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC BINDER_CONV [TAUT `p <=> p /\ T`] THEN
    PURE_REWRITE_TAC[EXISTS_IN_GSPEC] THEN EXISTS_TAC `ring_1 r:A` THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_1];
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV) [num_WOP]] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; LEFT_IMP_EXISTS_THM; SKOLEM_THM; NOT_LT] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT
   `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  X_GEN_TAC `dd:A->A` THEN STRIP_TAC THEN
  EXISTS_TAC `(n:A->num) o (\x. ring_mul r x (dd x))` THEN
  REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN
    REWRITE_TAC[ring_divides; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
    DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `c:A` THEN
    DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `a:A = ring_0 r` THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; LE_REFL] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_MUL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC; RING_MUL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  UNDISCH_THEN
   `!a b. a IN ring_carrier r /\ b IN ring_carrier r /\ ~(b = ring_0 r)
          ==> (?q t.
                   q IN ring_carrier r /\
                   t IN ring_carrier r /\
                   ring_add r (ring_mul r b q) t = a /\
                   (t = ring_0 r \/ (n:A->num) t < n b))`
   (MP_TAC o SPECL [`a:A`; `ring_mul r b (dd b):A`]) THEN
  ASM_SIMP_TAC[RING_MUL; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:A`; `t:A`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`ring_mul r ((dd:A->A) b) q`; `t:A`] THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_MUL] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP
   (TAUT `p \/ q ==> p \/ ~p /\ q`)) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] LET_TRANS)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:A`; `ring_1 r:A`]) THEN
  ASM_SIMP_TAC[RING_MUL_RID; RING_1]);;

let EUCLIDEAN_IMP_PRINCIPAL_IDEAL_RING = prove
 (`!r j:A->bool. euclidean_ring r /\ ring_ideal r j ==> principal_ideal r j`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [euclidean_ring]) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:A->num`) THEN
  ASM_CASES_TAC `j = {ring_0 r:A}` THEN ASM_REWRITE_TAC[PRINCIPAL_IDEAL_0] THEN
  MP_TAC(SPEC `\m. m IN IMAGE (n:A->num) (j DELETE ring_0 r)` num_WOP) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; MEMBER_NOT_EMPTY; IMAGE_EQ_EMPTY] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL[`r:A ring`; `j:A->bool`] IN_RING_IDEAL_0) THEN ASM SET_TAC[];
    ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`]] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_DELETE; principal_ideal] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(b:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; IDEAL_GENERATED_MINIMAL_EQ] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[SUBSET]] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`]) THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING_ALT; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:A` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `t:A = ring_0 r` THEN
  ASM_SIMP_TAC[RING_MUL; RING_ADD_RZERO] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:A`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  SUBGOAL_THEN `t = ring_add r (ring_neg r (ring_mul r b q))
                               (ring_add r (ring_mul r b q) t):A`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(K ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[RING_ADD_ASSOC; RING_ADD_LNEG; RING_MUL; RING_NEG;
                 RING_ADD_LZERO];
    MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IN_RING_IDEAL_NEG THEN ASM_SIMP_TAC[IN_RING_IDEAL_RMUL]]);;

let EUCLIDEAN_DOMAIN_IMP_PID = prove
 (`!r:A ring. integral_domain r /\ euclidean_ring r ==> PID r`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[PID] THEN
  ASM_SIMP_TAC[EUCLIDEAN_IMP_PRINCIPAL_IDEAL_RING]);;

let EUCLIDEAN_RING_UNIVERSAL_SIDE_DIVISOR = prove
 (`!r:A ring.
        euclidean_ring r /\ ~trivial_ring r /\ ~field r
        ==> ?a. a IN ring_carrier r /\ ~(a = ring_0 r) /\ ~(ring_unit r a) /\
                !b. b IN ring_carrier r
                    ==> ?u. (ring_unit r u \/ u = ring_0 r) /\
                            ring_divides r a (ring_sub r b u)`,
  SIMP_TAC[IMP_CONJ; FIELD_EQ_ALL_UNITS; TRIVIAL_RING_10] THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [euclidean_ring]) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:A->num`) THEN
  MP_TAC(fst(EQ_IMP_RULE(ISPEC
   `\m. m IN IMAGE (n:A->num)
                   {x | x IN ring_carrier r /\
                        ~(x = ring_0 r) /\ ~ring_unit r x}`
   num_WOP))) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
  ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; NOT_LT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:A`; `a:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:A` THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
  ASM_SIMP_TAC[ring_sub; GSYM RING_ADD_ASSOC; RING_MUL; RING_NEG;
               RING_ADD_RNEG; RING_ADD_RZERO] THEN
  ASM_SIMP_TAC[RING_DIVIDES_RMUL; RING_DIVIDES_REFL] THEN
  ASM_CASES_TAC `u:A = ring_0 r` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NOT_LT]);;

let EUCLIDEAN_RING_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f /\ euclidean_ring r ==> euclidean_ring r'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_epimorphism; euclidean_ring] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:A->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y. minimal p.
    p IN IMAGE n {x | x IN ring_carrier r /\ (f:A->B) x = y}` THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[] (fst(EQ_IMP_RULE(ISPEC
   `\p:num. p IN IMAGE n {x | x IN ring_carrier r /\ (f:A->B) x = f b}`
   MINIMAL)))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]] THEN
  SPEC_TAC
   (`minimal p. p IN IMAGE n {x | x IN ring_carrier r /\ (f:A->B) x = f b}`,
    `c:num`) THEN
  ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; IN_ELIM_THM; NOT_LT] THEN
  X_GEN_TAC `b':A` THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `b:A`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b':A`]) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_0]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:A` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(REWRITE_RULE[] (fst(EQ_IMP_RULE(ISPEC
   `\p:num. p IN IMAGE n {x | x IN ring_carrier r /\ (f:A->B) x = f t}`
   MINIMAL)))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]] THEN
  ABBREV_TAC
   `v = minimal p.
          p IN IMAGE n {x | x IN ring_carrier r /\ (f:A->B) x = f t}` THEN
  ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; NOT_LT] THEN
  GEN_REWRITE_TAC I [IMP_CONJ] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':A`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `t:A`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `t':A` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_IMAGE; IN_ELIM_THM]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_MUL; RING_HOMOMORPHISM_ADD; RING_MUL];
    ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_0]; ASM_MESON_TAC[LET_TRANS]]);;

let EUCLIDEAN_QUOTIENT_RING = prove
 (`!r j:A->bool.
        euclidean_ring r /\ ring_ideal r j
        ==> euclidean_ring (quotient_ring r j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EUCLIDEAN_RING_EPIMORPHIC_IMAGE) THEN
  ASM_MESON_TAC[RING_EPIMORPHISM_RING_COSET]);;

let ISOMORPHIC_RING_EUCLIDEANNESS = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> (euclidean_ring r <=> euclidean_ring r')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[isomorphic_ring] THEN
  REWRITE_TAC[ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[EUCLIDEAN_RING_EPIMORPHIC_IMAGE;
                RING_ISOMORPHISM_IMP_EPIMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* A bit more about Noetherian rings.                                        *)
(* ------------------------------------------------------------------------- *)

let NOETHERIAN_RING = prove
 (`!r:A ring.
        noetherian_ring r <=>
        WF(\j j'. ring_ideal r j /\ ring_ideal r j' /\ j' PSUBSET j)`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> ~q) /\ (p ==> q) ==> (p <=> q)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[noetherian_ring; WF_DCHAIN; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?s:num->A->bool.
        (!n. FINITE(s n) /\ s n SUBSET j) /\
        (!n. ideal_generated r (s n) PSUBSET ideal_generated r (s(SUC n)))`
    STRIP_ASSUME_TAC THENL
     [ALL_TAC;
      EXISTS_TAC `\n. ideal_generated r ((s:num->A->bool) n)` THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]] THEN
    MATCH_MP_TAC DEPENDENT_CHOICE THEN
    CONJ_TAC THENL [MESON_TAC[EMPTY_SUBSET; FINITE_RULES]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `k:A->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE RAND_CONV [finitely_generated_ideal]) THEN
    REWRITE_TAC[NOT_EXISTS_THM; GSYM SUBSET_ANTISYM_EQ] THEN
    DISCH_THEN(MP_TAC o SPEC `k:A->bool`) THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_MINIMAL_EQ] THEN
    MATCH_MP_TAC(TAUT `(p /\ q) /\ (~r ==> s) ==> ~(p /\ q /\ r) ==> s`) THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[ring_ideal]) THEN ASM SET_TAC[];
      REWRITE_TAC[SET_RULE `~(s SUBSET t) <=> ?x. x IN s /\ ~(x IN t)`]] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(a:A) INSERT k` THEN
    ASM_REWRITE_TAC[FINITE_INSERT; INSERT_SUBSET] THEN
    SIMP_TAC[PSUBSET_ALT; IDEAL_GENERATED_MONO;
             SET_RULE `s SUBSET a INSERT s`] THEN
    EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_ideal]) THEN ASM SET_TAC[];
    REWRITE_TAC[noetherian_ring; WF_DCHAIN; FORALL_AND_THM] THEN
    DISCH_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `s:num->A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `UNIONS (IMAGE (s:num->A->bool) (:num))`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC RING_IDEAL_UNIONS THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_IMAGE_2; IN_UNIV] THEN
      MATCH_MP_TAC(MESON[LE_CASES]
       `(!m n. m <= n ==> (s:num->A->bool) m SUBSET s n)
        ==> !m n. s m SUBSET s n \/ s n SUBSET s m`) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM SET_TAC[];
      REWRITE_TAC[finitely_generated_ideal; NOT_EXISTS_THM]] THEN
    X_GEN_TAC `k:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (s:num->A->bool) (:num)`; `k:A->bool`]
        FINITE_SUBSET_UNIONS_CHAIN) THEN
    ASM_REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE_2; IN_UNIV; NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IDEAL_GENERATED_SUBSET_CARRIER_SUBSET];
      SET_TAC[];
      MATCH_MP_TAC(MESON[LE_CASES]
       `(!m n. m <= n ==> (s:num->A->bool) m SUBSET s n)
        ==> !m n. s m SUBSET s n \/ s n SUBSET s m`) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
      SUBGOAL_THEN `(s:num->A->bool) (SUC m) SUBSET s(m)`
      MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      TRANS_TAC SUBSET_TRANS `ideal_generated r k:A->bool` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[]]]);;

let NOETHERIAN_RING_EQ_ACC = prove
 (`!r:A ring.
        noetherian_ring r <=>
        ~(?j. (!n. ring_ideal r (j n)) /\
              (!n. j n PSUBSET j(n + 1)))`,
  REWRITE_TAC[NOETHERIAN_RING; WF_DCHAIN; ADD1] THEN MESON_TAC[]);;

let NOETHERIAN_RING_EQ_MAXIMAL = prove
 (`!r:A ring.
        noetherian_ring r <=>
        !u. ~(u = {}) /\ (!j. j IN u ==> ring_ideal r j)
            ==> ?k. k IN u /\ !j. j IN u ==> ~(k PSUBSET j)`,
  GEN_TAC THEN REWRITE_TAC[NOETHERIAN_RING; WF] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM SET_TAC[]);;

let NOETHERIAN_RING_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f /\ noetherian_ring r
        ==> noetherian_ring r'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[noetherian_ring] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP
   RING_EPIMORPHISM_IDEAL_CORRESPONDENCE th]) THEN
  X_GEN_TAC `k:B->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `j:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool` o REWRITE_RULE[noetherian_ring]) THEN
  ASM_REWRITE_TAC[finitely_generated_ideal] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (f:A->B) s` THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ring_epimorphism]) THEN ASM SET_TAC[];
    ASM_MESON_TAC[IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE]]);;

let NOETHERIAN_QUOTIENT_RING = prove
 (`!r j:A->bool.
        noetherian_ring r /\ ring_ideal r j
        ==> noetherian_ring (quotient_ring r j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] NOETHERIAN_RING_EPIMORPHIC_IMAGE) THEN
  ASM_MESON_TAC[RING_EPIMORPHISM_RING_COSET]);;

let ISOMORPHIC_RING_NOETHERIANNESS = prove
 (`!(r:A ring) (r':B ring).
         r isomorphic_ring r' ==> (noetherian_ring r <=> noetherian_ring r')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] NOETHERIAN_RING_EPIMORPHIC_IMAGE) THEN
  ASM_MESON_TAC[ISOMORPHIC_RING_SYM; isomorphic_ring;
                RING_ISOMORPHISM_IMP_EPIMORPHISM]);;

let NOETHERIAN_PROD_RING = prove
 (`!(r1:A ring) (r2:B ring).
        noetherian_ring(prod_ring r1 r2) <=>
        noetherian_ring r1 /\ noetherian_ring r2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] NOETHERIAN_RING_EPIMORPHIC_IMAGE) THEN
    MESON_TAC[RING_EPIMORPHISM_FST; RING_EPIMORPHISM_SND];
    STRIP_TAC] THEN
  REWRITE_TAC[noetherian_ring] THEN ONCE_REWRITE_TAC[RING_IDEAL_PROD_RING] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:A#B->bool`; `k1:A->bool`; `k2:B->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k2:B->bool` o REWRITE_RULE[noetherian_ring]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k1:A->bool` o REWRITE_RULE[noetherian_ring]) THEN
  ASM_REWRITE_TAC[finitely_generated_ideal; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `s1:A->bool` THEN STRIP_TAC THEN
  X_GEN_TAC `s2:B->bool` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
  EXISTS_TAC `(ring_0 r1 INSERT s1:A->bool) CROSS
              (ring_0 r2 INSERT s2:B->bool)` THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_CROSS; PROD_RING; SUBSET_CROSS;
               INSERT_SUBSET; RING_0; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[IDEAL_GENERATED_INSERT_ZERO] THEN
  MATCH_MP_TAC FINITE_CROSS THEN ASM_REWRITE_TAC[FINITE_INSERT]);;

let NOETHERIAN_PRODUCT_RING = prove
 (`!(r:K->A ring) k.
        noetherian_ring(product_ring k r) <=>
        FINITE {i | i IN k /\ ~trivial_ring(r i)} /\
        !i. i IN k ==> noetherian_ring (r i)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [ALL_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (REWRITE_RULE[IMP_CONJ_ALT] NOETHERIAN_RING_EPIMORPHIC_IMAGE)) THEN
      ASM_MESON_TAC[RING_EPIMORPHISM_PRODUCT_PROJECTION]] THEN
    REWRITE_TAC[MESON[INFINITE] `FINITE s <=> ~INFINITE s`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [noetherian_ring]) THEN
    DISCH_THEN(MP_TAC o SPEC
     `{x | x IN ring_carrier(product_ring k (r:K->A ring)) /\
           FINITE {i | i IN k /\ ~(x i = ring_0(r i))}}`) THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [REWRITE_TAC[ring_ideal; SUBSET_RESTRICT] THEN
      SIMP_TAC[IN_ELIM_THM; RING_0; RING_NEG; RING_ADD; RING_MUL] THEN
      REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
       [MATCH_MP_TAC(MESON[FINITE_EMPTY; MEMBER_NOT_EMPTY]
         `(!x. x IN s ==> F) ==> FINITE s`) THEN
        SIMP_TAC[IN_ELIM_THM; PRODUCT_RING; RESTRICTION] THEN MESON_TAC[];
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC);
        DISCH_THEN(CONJUNCTS_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        REWRITE_TAC[IMP_IMP; GSYM FINITE_UNION];
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `i:K` THEN
      ASM_CASES_TAC `(i:K) IN k` THEN
      ASM_REWRITE_TAC[CONTRAPOS_THM; IN_UNION; IN_ELIM_THM;
                      GSYM DE_MORGAN_THM] THEN
      ASM_REWRITE_TAC[PRODUCT_RING; RESTRICTION] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[PRODUCT_RING; IN_CARTESIAN_PRODUCT]) THEN
      ASM_SIMP_TAC[RING_NEG_0; RING_ADD_LZERO; RING_0; RING_MUL_RZERO];
      REWRITE_TAC[finitely_generated_ideal] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:(K->A)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `!x. x IN ideal_generated (product_ring k (r:K->A ring)) s
            ==> {i | i IN k /\ ~(x i = ring_0(r i))} SUBSET
                UNIONS {{i | i IN k /\ ~(y i = ring_0(r i))} | y |
                        y IN s}`
      MP_TAC THENL
       [MATCH_MP_TAC IDEAL_GENERATED_INDUCT THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[];
          SIMP_TAC[PRODUCT_RING; RESTRICTION] THEN SET_TAC[];
          GEN_TAC;
          REPEAT GEN_TAC THEN REWRITE_TAC[GSYM UNION_SUBSET];
          REPEAT GEN_TAC THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `i:K` THEN
        ASM_CASES_TAC `(i:K) IN k` THEN
        ASM_REWRITE_TAC[CONTRAPOS_THM; IN_UNION; IN_ELIM_THM;
                        GSYM DE_MORGAN_THM] THEN
        ASM_REWRITE_TAC[PRODUCT_RING; RESTRICTION] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[PRODUCT_RING; IN_CARTESIAN_PRODUCT]) THEN
        ASM_SIMP_TAC[RING_NEG_0; RING_ADD_LZERO; RING_0; RING_MUL_RZERO];
        ASM_REWRITE_TAC[NOT_FORALL_THM; IN_ELIM_THM]] THEN
      ABBREV_TAC
        `k' = UNIONS {{i | i IN k /\ ~(y i = ring_0((r:K->A ring) i))} | y |
                       y IN s}` THEN
      SUBGOAL_THEN `FINITE(k':K->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "k'" THEN REWRITE_TAC[FINITE_UNIONS] THEN
        ASM_SIMP_TAC[FINITE_IMAGE; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `ideal_generated r s = s'
          ==> s SUBSET ideal_generated r s /\ (!x. x IN s' ==> P x)
              ==> !x. x IN s ==> P x`)) THEN
        ASM_SIMP_TAC[IDEAL_GENERATED_SUBSET_CARRIER_SUBSET; IN_ELIM_THM];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `~({i | i IN k /\ ~trivial_ring ((r:K->A ring) i)} SUBSET k')`
      MP_TAC THENL
       [ASM_MESON_TAC[INFINITE; FINITE_SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; NOT_IMP; IN_ELIM_THM; NOT_FORALL_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:K` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `RESTRICTION k
                    (\i. if i IN a INSERT k' then ring_1(r i)
                         else ring_0((r:K->A ring) i))` THEN
      REWRITE_TAC[PRODUCT_RING; RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
      REPEAT CONJ_TAC THENL
       [MESON_TAC[RING_0; RING_1];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(a:K) INSERT k'` THEN
        SIMP_TAC[RESTRICTION; FINITE_INSERT] THEN ASM SET_TAC[];
        EXISTS_TAC `a:K` THEN ASM_REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[RESTRICTION; IN_INSERT; GSYM TRIVIAL_RING_10]]];
    STRIP_TAC] THEN
  REWRITE_TAC[noetherian_ring] THEN
  FIRST_ASSUM(fun th ->
    ONCE_REWRITE_TAC[MATCH_MP RING_IDEAL_PRODUCT_RING th]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:(K->A)->bool`; `j:K->A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `!i. i IN k ==> finitely_generated_ideal ((r:K->A ring) i) (j i)`
  MP_TAC THENL [ASM_MESON_TAC[noetherian_ring]; ALL_TAC] THEN
  REWRITE_TAC[finitely_generated_ideal] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM;
              TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  X_GEN_TAC `s:K->(A->bool)` THEN STRIP_TAC THEN
  EXISTS_TAC `cartesian_product k
                (\i. ring_0 ((r:K->A ring) i) INSERT s i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_CARTESIAN_PRODUCT; FINITE_INSERT] THEN
    DISJ2_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM; trivial_ring] THEN ASM SET_TAC[];
    REWRITE_TAC[PRODUCT_RING; SUBSET_CARTESIAN_PRODUCT] THEN
    ASM_SIMP_TAC[INSERT_SUBSET; RING_0];
    ASM_SIMP_TAC[IDEAL_GENERATED_CARTESIAN_PRODUCT; INSERT_SUBSET; RING_0] THEN
    REWRITE_TAC[CARTESIAN_PRODUCT_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
    ASM_SIMP_TAC[CARTESIAN_PRODUCT_EQ; IDEAL_GENERATED_INSERT_ZERO]]);;

(* ------------------------------------------------------------------------- *)
(* The special case of ACC for principal ideals (ACCP), which holds in UFDs. *)
(* ------------------------------------------------------------------------- *)

let RING_ACCP = prove
 (`!r:A ring.
    WF (\j j'. principal_ideal r j /\ principal_ideal r j' /\ j' PSUBSET j) <=>
    WF (\x y. ring_divides r x y /\ ~(ring_divides r y x))`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o ISPEC `\x:A. ideal_generated r {x}` o
        MATCH_MP WF_MEASURE_GEN) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] WF_SUBSET) THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    REWRITE_TAC[PRINCIPAL_IDEAL_IDEAL_GENERATED_SING] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_DIVIDES_IN_CARRIER) THEN
    ASM_SIMP_TAC[PSUBSET_IDEALS_GENERATED_SING];
    SUBGOAL_THEN
     `?g. !j. principal_ideal r j
              ==> g j IN ring_carrier r /\ ideal_generated r {g j:A} = j`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SKOLEM_THM; principal_ideal] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o ISPEC `g:(A->bool)->A` o MATCH_MP
     (INST_TYPE [`:B->bool`,`:A`] WF_MEASURE_GEN)) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] WF_SUBSET) THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[PSUBSET_IDEALS_GENERATED_SING]]);;

let RING_DIVIDES_WF = prove
 (`!r:A ring.
        noetherian_ring r \/ UFD r
        ==> WF (\x y. ring_divides r x y /\ ~(ring_divides r y x))`,
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOETHERIAN_RING]) THEN
    REWRITE_TAC[GSYM RING_ACCP] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] WF_SUBSET) THEN
    SIMP_TAC[PRINCIPAL_IMP_RING_IDEAL];
    FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o
      GEN_REWRITE_RULE I [UFD_EQ_PRIMEFACT]) THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:A->num`; `p:A->num->A`] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `\x. (if x = ring_0 r then 1 else 0),(n:A->num) x`
      (MATCH_MP WF_MEASURE_GEN
        (MATCH_MP WF_LEX (CONJ WF_num WF_num)))) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] WF_SUBSET) THEN
    REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    ASM_CASES_TAC `(x:A) IN ring_carrier r /\ y IN ring_carrier r` THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
      ASM_MESON_TAC[ring_divides]] THEN
    ASM_CASES_TAC `x:A = ring_0 r` THEN ASM_SIMP_TAC[RING_DIVIDES_0] THEN
    ASM_CASES_TAC `y:A = ring_0 r` THEN ASM_REWRITE_TAC[ARITH] THEN
    STRIP_TAC THEN MP_TAC(ISPECL
     [`r:A ring`; `1..n(x:A)`; `(p:A->num->A) x`;
      `1..n(y:A)`; `(p:A->num->A) y`]
        RING_DIVIDES_PRIMEFACTS_LT) THEN
    ASM_REWRITE_TAC[CARD_NUMSEG_1] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `y:A` th) THEN MP_TAC(SPEC `x:A` th)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[IN_NUMSEG; FINITE_NUMSEG;
                 INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE] THEN
    ASM_MESON_TAC[RING_ASSOCIATES_DIVIDES]]);;

let RING_PRINCIPAL_IDEALS_WF = prove
 (`!r:A ring.
        noetherian_ring r \/ UFD r
        ==> WF (\j j'. principal_ideal r j /\ principal_ideal r j' /\
                       j' PSUBSET j)`,
  REWRITE_TAC[RING_ACCP; RING_DIVIDES_WF]);;

let ACCP_RING_PROPER_DIVISOR_INDUCT = prove
 (`!r P:A->bool.
        WF (\x y. ring_divides r x y /\ ~(ring_divides r y x)) /\
        (!a. a IN ring_carrier r /\
             (!d. ring_divides r d a /\ ~(ring_divides r a d) ==> P d)
             ==> P a)
        ==> !a. a IN ring_carrier r ==> P a`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [WF_IND]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[ring_divides]);;

let RING_PROPER_DIVISOR_INDUCT = prove
 (`!r P:A->bool.
        (noetherian_ring r \/ UFD r) /\
        (!a. a IN ring_carrier r /\
             (!d. ring_divides r d a /\ ~(ring_divides r a d) ==> P d)
             ==> P a)
        ==> !a. a IN ring_carrier r ==> P a`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC ACCP_RING_PROPER_DIVISOR_INDUCT THEN
  ASM_SIMP_TAC[RING_DIVIDES_WF]);;

let ACCP_DOMAIN_ATOMIC = prove
 (`!r a:A.
        integral_domain r /\
        WF (\x y. ring_divides r x y /\ ~ring_divides r y x) /\
        a IN ring_carrier r /\ ~(a = ring_0 r)
        ==> ?n p. (!i. 1 <= i /\ i <= n ==> ring_irreducible r (p i)) /\
                  ring_associates r (ring_product r (1..n) p) a`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC ACCP_RING_PROPER_DIVISOR_INDUCT THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `ring_unit r (a:A)` THENL
   [MAP_EVERY EXISTS_TAC [`0`; `(\i. ring_0 r):num->A`] THEN
    REWRITE_TAC[RING_PRODUCT_CLAUSES_NUMSEG; ARITH_EQ; RING_0] THEN
    ASM_REWRITE_TAC[RING_ASSOCIATES_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `ring_irreducible r (a:A)` THENL
   [MAP_EVERY EXISTS_TAC [`1`; `(\i. a):num->A`] THEN
    ASM_REWRITE_TAC[NUMSEG_SING; RING_PRODUCT_SING; RING_ASSOCIATES_REFL];
    RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; GSYM CONJ_ASSOC])] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ring_irreducible]) THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `c:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun t -> MP_TAC(SPEC `c:A` t) THEN MP_TAC(SPEC `b:A` t)) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(a:A = ring_0 r)` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RING_DIVIDES_RMUL; RING_DIVIDES_LMUL; RING_DIVIDES_REFL] THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_DIVIDES_MUL_SELF; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n1:num`; `p1:num->A`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n2:num`; `p2:num->A`] THEN STRIP_TAC THEN
  EXISTS_TAC `n1 + n2:num` THEN
  EXISTS_TAC `\i. if i <= n1 then (p1:num->A) i else p2(i - n1)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[NUMSEG_ADD_SPLIT; ARITH_RULE `1 <= n + 1`]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; DISJOINT; EXTENSION; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_INTER; IN_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_ASSOCIATES_MUL THEN CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[NUMSEG_OFFSET_IMAGE] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_IMAGE o lhand o snd) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
    RING_ASSOCIATES_TRANS)) THEN
  MATCH_MP_TAC(MESON[RING_ASSOCIATES_REFL]
   `y IN ring_carrier r /\ x = y ==> ring_associates r x y`) THEN
  REWRITE_TAC[RING_PRODUCT] THEN MATCH_MP_TAC RING_PRODUCT_EQ THEN
  GEN_TAC THEN REWRITE_TAC[IN_NUMSEG; o_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_SUB] THEN ASM_ARITH_TAC);;

let ACCP_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS = prove
 (`!r x:A.
        integral_domain r /\
        WF (\x y. ring_divides r x y /\ ~ring_divides r y x) /\
        x IN ring_carrier r /\ ~(x = ring_0 r) /\ ~(ring_unit r x)
        ==> ?p. ring_irreducible r p /\ ring_divides r p x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `x:A`] ACCP_DOMAIN_ATOMIC) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[IMP_CONJ] THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES_NUMSEG; ARITH_EQ; RING_ASSOCIATES_1;
    ARITH_RULE `1 <= SUC n`; LE_REFL; RING_IRREDUCIBLE_IN_CARRIER] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  X_GEN_TAC `q:num->A` THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  EXISTS_TAC `q(SUC n):A` THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`; LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        RING_ASSOCIATES_DIVIDES)) THEN
  REPEAT(DISCH_THEN(MP_TAC o SPEC `q(SUC n):A`)) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`; LE_REFL; RING_IRREDUCIBLE_IN_CARRIER;
               RING_ASSOCIATES_REFL; RING_DIVIDES_LMUL; RING_DIVIDES_REFL;
               RING_PRODUCT]);;

let NOETHERIAN_DOMAIN_ATOMIC = prove
 (`!r a:A.
        integral_domain r /\
        (noetherian_ring r \/ UFD r) /\
        a IN ring_carrier r /\ ~(a = ring_0 r)
        ==> ?n p. (!i. 1 <= i /\ i <= n ==> ring_irreducible r (p i)) /\
                  ring_associates r (ring_product r (1..n) p) a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ACCP_DOMAIN_ATOMIC THEN
  ASM_SIMP_TAC[RING_DIVIDES_WF]);;

let NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS = prove
 (`!r x:A.
        integral_domain r /\
        (noetherian_ring r \/ UFD r) /\
        x IN ring_carrier r /\ ~(x = ring_0 r) /\ ~(ring_unit r x)
        ==> ?p. ring_irreducible r p /\ ring_divides r p x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ACCP_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS THEN
  ASM_SIMP_TAC[RING_DIVIDES_WF]);;

let UFD_EQ_ACCP = prove
 (`!r:A ring.
        UFD r <=>
        integral_domain r /\
        (!p. ring_irreducible r p ==> ring_prime r p) /\
        WF (\x y. ring_divides r x y /\ ~ring_divides r y x)`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[UFD_IMP_INTEGRAL_DOMAIN; UFD_IRREDUCIBLE_EQ_PRIME;
             RING_DIVIDES_WF];
    STRIP_TAC THEN ASM_REWRITE_TAC[UFD_EQ_ATOMIC] THEN
    ASM_SIMP_TAC[ACCP_DOMAIN_ATOMIC]]);;

(* ------------------------------------------------------------------------- *)
(* An actual (somewhat carefully totalized) function for the ring gcd.       *)
(* We try to make most of the properties true without any restrictions,      *)
(* and force to 1 in the coprime case to maintain the common idiom of using  *)
(* gcd(a,b) = 1 <=> coprime(a,b), and we also force a preference for the     *)
(* injection of N, just so we get the nonnegative integers in integer_ring.  *)
(* ------------------------------------------------------------------------- *)

let ring_gcd = new_definition
 `ring_gcd (r:A ring) (a,b) =
        if a IN ring_carrier r /\ b IN ring_carrier r ==> ring_coprime r (a,b)
        then ring_1 r
        else if ?d. d IN IMAGE (ring_of_num r) (:num) /\
                    ring_divides r d a /\
                    ring_divides r d b /\
                    !d'. ring_divides r d' a /\ ring_divides r d' b
                         ==> ring_divides r d' d
        then @d. d IN IMAGE (ring_of_num r) (:num) /\
                 ring_divides r d a /\
                 ring_divides r d b /\
                 !d'. ring_divides r d' a /\ ring_divides r d' b
                      ==> ring_divides r d' d
        else if ?d. d IN ring_carrier r /\
                    ring_divides r d a /\
                    ring_divides r d b /\
                    !d'. ring_divides r d' a /\ ring_divides r d' b
                         ==> ring_divides r d' d
        then @d. d IN ring_carrier r /\
                 ring_divides r d a /\
                 ring_divides r d b /\
                 !d'. ring_divides r d' a /\ ring_divides r d' b
                      ==> ring_divides r d' d
        else @d. ring_divides r d a /\ ring_divides r d b /\
                 ~(ring_unit r d)`;;

let RING_GCD_WORKS = prove
 (`!r a b:A.
        ring_gcd r (a,b) IN ring_carrier r /\
        ring_divides r (ring_gcd r (a,b)) a /\
        ring_divides r (ring_gcd r (a,b)) b /\
        (!d'. ring_divides r d' a /\ ring_divides r d' b
              ==> ring_divides r d' (ring_gcd r (a,b))) <=>
        ?d. d IN ring_carrier r /\
            ring_divides r d a /\ ring_divides r d b /\
            !d'. ring_divides r d' a /\ ring_divides r d' b
                 ==> ring_divides r d' d`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THENL
   [ALL_TAC; ASM_MESON_TAC[ring_divides]] THEN
  ASM_CASES_TAC `(b:A) IN ring_carrier r` THENL
   [ALL_TAC; ASM_MESON_TAC[ring_divides]] THEN
  ASM_CASES_TAC `ring_coprime r (a:A,b)` THEN ASM_REWRITE_TAC[ring_gcd] THENL
   [REWRITE_TAC[RING_DIVIDES_1; RING_1; RING_DIVIDES_ONE] THEN
    ASM_REWRITE_TAC[GSYM ring_coprime];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RING_OF_NUM]);;

let RING_GCD_UNIQUE = prove
 (`!r a b d:A.
        ring_divides r d a /\ ring_divides r d b /\
        (!d'. ring_divides r d' a /\ ring_divides r d' b
              ==> ring_divides r d' d)
        ==> ring_associates r (ring_gcd r (a,b)) d`,
  REPEAT STRIP_TAC THEN MP_TAC(snd(EQ_IMP_RULE
   (ISPECL [`r:A ring`; `a:A`; `b:A`] RING_GCD_WORKS))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ring_divides]; ALL_TAC] THEN
  REWRITE_TAC[ring_associates] THEN ASM_MESON_TAC[]);;

let RING_GCD_REFL = prove
 (`!r a:A. a IN ring_carrier r ==> ring_associates r (ring_gcd r (a,a)) a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_GCD_UNIQUE THEN
  ASM_REWRITE_TAC[RING_DIVIDES_REFL]);;

let RING_GCD = prove
 (`!r a b:A. ring_gcd r (a,b) IN ring_carrier r`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `a:A`; `b:A`] RING_GCD_WORKS) THEN
  MATCH_MP_TAC(TAUT `(p ==> r) /\ (~q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [SIMP_TAC[]; DISCH_TAC] THEN ASM_REWRITE_TAC[ring_gcd] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_1] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [NOT_IMP]) THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `(?x. P x) ==> (!x. P x ==> Q x) ==> ~(!x. ~(Q x))`)) THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; RING_OF_NUM];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ring_coprime]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[ring_divides]]);;

let RING_GCD_EQ = prove
 (`!r a b a' b':A.
        (!d. d IN ring_carrier r
             ==> (ring_divides r d a /\ ring_divides r d b <=>
                  ring_divides r d a' /\ ring_divides r d b'))
        ==> ring_gcd r (a,b) = ring_gcd r (a',b')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
   `(!d. P d ==> Q d) ==> (!d. ~(P d) ==> Q d) ==> (!d. Q d)`)) THEN
  ANTS_TAC THENL [SIMP_TAC[ring_divides]; DISCH_TAC] THEN
  REWRITE_TAC[ring_gcd; ring_coprime] THEN
  REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> p /\ (q /\ r) /\ s`] THEN
  REWRITE_TAC[TAUT `ring_divides r d a /\ ring_divides r d b /\ q <=>
                    (ring_divides r d a /\ ring_divides r d b) /\ q`] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN SIMP_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `ring_1 r:A`) THEN
  SIMP_TAC[RING_DIVIDES_1]);;

let RING_GCD_SYM = prove
 (`!r a b:A. ring_gcd r (a,b) = ring_gcd r (b,a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_GCD_EQ THEN
  CONV_TAC TAUT);;

let RING_GCD_DIVIDES = prove
 (`(!r a b:A. ring_divides r (ring_gcd r (a,b)) a <=> a IN ring_carrier r) /\
   (!r a b:A. ring_divides r (ring_gcd r (a,b)) b <=> b IN ring_carrier r)`,
  REPEAT STRIP_TAC THEN
  (EQ_TAC THENL [MESON_TAC[RING_DIVIDES_IN_CARRIER]; DISCH_TAC]) THEN
  MP_TAC(ISPECL [`r:A ring`; `a:A`; `b:A`] RING_GCD_WORKS) THEN
  MATCH_MP_TAC(TAUT `(p ==> r) /\ (~q ==> r) ==> (p <=> q) ==> r`) THEN
  (CONJ_TAC THENL [SIMP_TAC[]; DISCH_TAC]) THEN ASM_REWRITE_TAC[ring_gcd] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_DIVIDES_1] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [NOT_IMP]) THEN
  (COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `(?x. P x) ==> (!x. P x ==> Q x) ==> ~(!x. ~(Q x))`)) THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; RING_OF_NUM];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ring_coprime]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[ring_divides]]));;

let RING_UNIT_GCD = prove
 (`!r a b:A.
        ring_unit r (ring_gcd r (a,b)) <=>
        a IN ring_carrier r /\ b IN ring_carrier r ==> ring_coprime r (a,b)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; SIMP_TAC[ring_gcd; RING_UNIT_1]] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `a:A`; `b:A`] RING_GCD_WORKS) THEN
  MATCH_MP_TAC(TAUT `(p ==> r) /\ (~q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ring_coprime]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
    X_GEN_TAC `d:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:A`) THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    ASM_SIMP_TAC[RING_DIVIDES_UNIT];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[ring_gcd] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `(?x. P x) ==> (!x. P x ==> Q x) ==> ~(!x. ~(Q x))`)) THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; RING_OF_NUM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [ring_coprime]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[ring_divides]);;

let RING_GCD_EQ_1 = prove
 (`!r a b:A.
        ring_gcd r (a,b) = ring_1 r <=>
        a IN ring_carrier r /\ b IN ring_carrier r ==> ring_coprime r (a,b)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[ring_gcd]] THEN
  REWRITE_TAC[GSYM RING_UNIT_GCD] THEN SIMP_TAC[RING_UNIT_1]);;

let UFD_DIVIDES_GCD = prove
 (`!r a b d:A.
        UFD r /\ ring_divides r d a /\ ring_divides r d b
        ==> ring_divides r d (ring_gcd r (a,b))`,
  MESON_TAC[REWRITE_RULE[GSYM RING_GCD_WORKS] UFD_IMP_GCD_EXISTS;
            RING_DIVIDES_IN_CARRIER]);;

let UFD_DIVIDES_GCD_EQ = prove
 (`!r a b d:A.
        UFD r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_divides r d (ring_gcd r (a,b)) <=>
             ring_divides r d a /\ ring_divides r d b)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[UFD_DIVIDES_GCD] THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] RING_DIVIDES_TRANS) THEN
  ASM_REWRITE_TAC[RING_GCD_DIVIDES]);;

let RING_GCD_00 = prove
 (`!r:A ring. ring_gcd r (ring_0 r,ring_0 r) = ring_0 r`,
  GEN_TAC THEN
  GEN_REWRITE_TAC I [GSYM(CONJUNCT1 RING_ASSOCIATES_0)] THEN
  MATCH_MP_TAC RING_GCD_UNIQUE THEN
  REWRITE_TAC[RING_DIVIDES_0; RING_0]);;

let FIELD_GCD = prove
 (`!r a b:A.
        field r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> ring_gcd r (a,b) =
            if a = ring_0 r /\ b = ring_0 r then ring_0 r else ring_1 r`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_GCD_00] THEN
  ASM_SIMP_TAC[RING_GCD_EQ_1; FIELD_COPRIME]);;

(* ------------------------------------------------------------------------- *)
(* Bezout rings, where gcds also work and we have Bezout identity.           *)
(* Note that we are not automatically assuming the integral domain property. *)
(* ------------------------------------------------------------------------- *)

let bezout_ring = new_definition
 `bezout_ring (r:A ring) <=>
        !j. finitely_generated_ideal r j ==> principal_ideal r j`;;

let BEZOUT_RING_FINITELY_GENERATED_EQ_PRINCIPAL_IDEAL = prove
 (`!r j:A->bool.
        bezout_ring (r:A ring)
        ==> (finitely_generated_ideal r j <=> principal_ideal r j)`,
  MESON_TAC[bezout_ring; PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL]);;

let PID_IMP_BEZOUT_RING = prove
 (`!r:A ring. PID r ==> bezout_ring r`,
  SIMP_TAC[PID; bezout_ring; FINITELY_GENERATED_IMP_RING_IDEAL]);;

let FIELD_IMP_BEZOUT_RING = prove
 (`!r:A ring. field r ==> bezout_ring r`,
  SIMP_TAC[FIELD_IMP_PID; PID_IMP_BEZOUT_RING]);;

let BEZOUT_RING_2 = prove
 (`!r:A ring.
        bezout_ring r <=>
        !a b. a IN ring_carrier r /\ b IN ring_carrier r
              ==> principal_ideal r (ideal_generated r {a,b})`,
  GEN_TAC THEN REWRITE_TAC[bezout_ring] THEN EQ_TAC THEN
  SIMP_TAC[FINITELY_GENERATED_IDEAL_GENERATED; FINITE_INSERT;
           FINITE_EMPTY] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!s:A->bool.
        FINITE s
        ==> s SUBSET ring_carrier r
            ==> principal_ideal r (ideal_generated r s)`
  MP_TAC THENL [ALL_TAC; MESON_TAC[finitely_generated_ideal]] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[INSERT_SUBSET] THEN
  REWRITE_TAC[IDEAL_GENERATED_EMPTY; PRINCIPAL_IDEAL_0] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [principal_ideal]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A` (STRIP_ASSUME_TAC o GSYM)) THEN
  ONCE_REWRITE_TAC[IDEAL_GENERATED_INSERT] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM IDEAL_GENERATED_INSERT]);;

let BEZOUT_RING_SETADD = prove
 (`!r:A ring.
        bezout_ring r <=>
        !j k. principal_ideal r j /\ principal_ideal r k
              ==> principal_ideal r (ring_setadd r j k)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[GSYM BEZOUT_RING_FINITELY_GENERATED_EQ_PRINCIPAL_IDEAL;
           FINITELY_GENERATED_IDEAL_SETADD] THEN
  STRIP_TAC THEN REWRITE_TAC[BEZOUT_RING_2] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b} = {a} UNION {b}`] THEN
  REWRITE_TAC[IDEAL_GENERATED_UNION] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[PRINCIPAL_IDEAL_IDEAL_GENERATED_SING]);;

let PID_EQ_NOETHERIAN_BEZOUT_DOMAIN = prove
 (`!r:A ring. PID r <=>
              integral_domain r /\
              noetherian_ring r /\
              bezout_ring r`,
  REWRITE_TAC[PID; noetherian_ring; bezout_ring] THEN
  MESON_TAC[PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL;
            FINITELY_GENERATED_IMP_RING_IDEAL]);;

let BEZOUT_RING_IMP_BEZOUT = prove
 (`!r a b:A.
        bezout_ring r /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> ?d. d IN ring_carrier r /\
                ring_divides r d a /\ ring_divides r d b /\
                ?x y. x IN ring_carrier r /\ y IN ring_carrier r /\
                      ring_add r (ring_mul r a x) (ring_mul r b y) = d`,
  REWRITE_TAC[bezout_ring] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ideal_generated r {a:A,b}`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[finitely_generated_ideal] THEN
    EXISTS_TAC `{a:A,b}` THEN
    ASM_SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; FINITE_RULES];
    ALL_TAC] THEN
  REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; principal_ideal] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `d:A`) THEN ASM_REWRITE_TAC[RING_DIVIDES_REFL] THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_INC; IN_INSERT;
               INSERT_SUBSET; EMPTY_SUBSET] THEN
  ONCE_REWRITE_TAC[IDEAL_GENERATED_INSERT] THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING_ALT] THEN
  REWRITE_TAC[ring_setadd; IN_ELIM_THM] THEN MESON_TAC[]);;

let RING_IMP_GCD_EXISTS = prove
 (`!r a b:A.
        (UFD r \/ bezout_ring r) /\
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> ?d. d IN ring_carrier r /\
                ring_divides r d a /\ ring_divides r d b /\
                !d'. ring_divides r d' a /\ ring_divides r d' b
                     ==> ring_divides r d' d`,
  REPEAT STRIP_TAC THENL [ASM_SIMP_TAC[UFD_IMP_GCD_EXISTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `a:A`; `b:A`] BEZOUT_RING_IMP_BEZOUT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_SIMP_TAC[RING_DIVIDES_ADD; RING_DIVIDES_RMUL]);;

let BEZOUT_RING_IMP_GCD = prove
 (`!r a b:A.
        bezout_ring r /\
        a IN ring_carrier r /\ b IN ring_carrier r
        ==> ?x y. x IN ring_carrier r /\ y IN ring_carrier r /\
                  ring_add r (ring_mul r a x) (ring_mul r b y) =
                  ring_gcd r (a,b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `a:A`; `b:A`] BEZOUT_RING_IMP_BEZOUT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:A` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `a:A`; `b:A`; `d:A`] RING_GCD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[RING_DIVIDES_ADD; RING_DIVIDES_RMUL];
    GEN_REWRITE_TAC LAND_CONV [RING_ASSOCIATES_SYM]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_DIVIDES_ASSOCIATES) THEN
  REWRITE_TAC[ring_divides] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ring_mul r x u:A`; `ring_mul r y u:A`] THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_MUL; GSYM RING_ADD_RDISTRIB]);;

let BEZOUT_RING_COPRIME = prove
 (`!r a b:A.
        bezout_ring r
        ==> (ring_coprime r (a,b) <=>
             a IN ring_carrier r /\ b IN ring_carrier r /\
             ?x y. x IN ring_carrier r /\ y IN ring_carrier r /\
                   ring_add r (ring_mul r a x) (ring_mul r b y) = ring_1 r)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[ring_coprime]] THEN
  ASM_CASES_TAC `(b:A) IN ring_carrier r` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[ring_coprime]] THEN
  EQ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `a:A`; `b:A`] RING_GCD_EQ_1) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC BEZOUT_RING_IMP_GCD THEN ASM_REWRITE_TAC[];
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[ring_coprime; GSYM RING_DIVIDES_ONE] THEN
    ASM_SIMP_TAC[RING_DIVIDES_ADD; RING_DIVIDES_RMUL]]);;

let BEZOUT_RING_COPRIME_COMAXIMAL = prove
 (`!r a b:A.
        bezout_ring r
        ==> (ring_coprime r (a,b) <=>
             a IN ring_carrier r /\
             b IN ring_carrier r /\
             ring_setadd r (ideal_generated r {a}) (ideal_generated r {b}) =
             ring_carrier r)`,
  SIMP_TAC[BEZOUT_RING_COPRIME; RING_IDEAL_EQ_CARRIER; RING_IDEAL_SETADD;
           RING_IDEAL_IDEAL_GENERATED] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(b:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING_ALT; ring_setadd; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let BEZOUT_RING_COMAXIMAL_COPRIME = prove
 (`!r j k:A->bool.
        bezout_ring r /\ ring_ideal r j /\ ring_ideal r k
        ==> (ring_setadd r j k = ring_carrier r <=>
             ?a b. a IN j /\ b IN k /\ ring_coprime r (a,b))`,
  SIMP_TAC[RING_IDEAL_EQ_CARRIER; RING_IDEAL_SETADD; BEZOUT_RING_COPRIME] THEN
  REWRITE_TAC[ring_setadd; IN_ELIM_THM] THEN
  ASM_MESON_TAC[RING_MUL_RID; SUBSET; RING_IDEAL_IMP_SUBSET;
                IN_RING_IDEAL_RMUL; RING_1]);;

let RING_DIVIDES_GCD = prove
 (`!r a b d:A.
        (UFD r \/ bezout_ring r) /\ ring_divides r d a /\ ring_divides r d b
        ==> ring_divides r d (ring_gcd r (a,b))`,
  MESON_TAC[REWRITE_RULE[GSYM RING_GCD_WORKS] RING_IMP_GCD_EXISTS;
            RING_DIVIDES_IN_CARRIER]);;

let RING_DIVIDES_GCD_EQ = prove
 (`!r a b d:A.
        (UFD r \/ bezout_ring r) /\ a IN ring_carrier r /\ b IN ring_carrier r
        ==> (ring_divides r d (ring_gcd r (a,b)) <=>
             ring_divides r d a /\ ring_divides r d b)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  EQ_TAC THEN ASM_SIMP_TAC[RING_DIVIDES_GCD] THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] RING_DIVIDES_TRANS) THEN
  ASM_REWRITE_TAC[RING_GCD_DIVIDES]);;

let BEZOUT_RING_IRREDUCIBLE_IMP_PRIME = prove
 (`!r p:A. bezout_ring r /\ ring_irreducible r p ==> ring_prime r p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_irreducible; ring_prime] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:A`; `a:A`] o
        MATCH_MP BEZOUT_RING_COPRIME) THEN
  ASM_SIMP_TAC[RING_IRREDUCIBLE_COPRIME_EQ; ring_irreducible] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  SUBGOAL_THEN `b:A = ring_mul r b (ring_1 r:A)` SUBST1_TAC THENL
   [ASM_MESON_TAC[RING_MUL_RID]; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[RING_ADD_LDISTRIB; GSYM RING_MUL_ASSOC; RING_MUL] THEN
  MATCH_MP_TAC RING_DIVIDES_ADD THEN
  ASM_MESON_TAC[RING_MUL_AC; RING_MUL; RING_DIVIDES_RMUL; RING_DIVIDES_REFL]);;

let BEZOUT_DOMAIN_IRREDUCIBLE_EQ_PRIME = prove
 (`!r p:A. integral_domain r /\ bezout_ring r
           ==> (ring_irreducible r p <=> ring_prime r p)`,
  MESON_TAC[BEZOUT_RING_IRREDUCIBLE_IMP_PRIME;
            INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE]);;

let PID_EQ_ACCP_BEZOUT_DOMAIN = prove
 (`!r:A ring.
        PID r <=>
        integral_domain r /\
        bezout_ring r /\
        WF (\x y. ring_divides r x y /\ ~ring_divides r y x)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[PID_IMP_UFD; PID_IMP_BEZOUT_RING; RING_DIVIDES_WF;
           PID_IMP_INTEGRAL_DOMAIN] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[PID] THEN
  X_GEN_TAC `j:A->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:A. x IN j` o GEN_REWRITE_RULE I [WF]) THEN
  ASM_REWRITE_TAC[principal_ideal] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[IN_RING_IDEAL_0]; MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM SET_TAC[]; DISCH_TAC] THEN
  ASM_SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; IDEAL_GENERATED_MINIMAL_EQ] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[SUBSET]] THEN
  X_GEN_TAC `b:A` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM] THEN
  SUBGOAL_THEN `(b:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ring_gcd r (a,b):A`) THEN
  ASM_SIMP_TAC[RING_GCD_DIVIDES; RING_DIVIDES_GCD_EQ] THEN
  ASM_REWRITE_TAC[CONTRAPOS_THM; RING_DIVIDES_REFL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `a:A`; `b:A`] BEZOUT_RING_IMP_GCD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_SIMP_TAC[IN_RING_IDEAL_ADD; IN_RING_IDEAL_RMUL]);;

let PID_EQ_UFD_BEZOUT_RING = prove
 (`!r:A ring. PID r <=> UFD r /\ bezout_ring r`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[PID_IMP_UFD; PID_IMP_BEZOUT_RING] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[PID_EQ_ACCP_BEZOUT_DOMAIN] THEN
  ASM_SIMP_TAC[UFD_IMP_INTEGRAL_DOMAIN; RING_DIVIDES_WF]);;

let PID_EQ_BEZOUT_ATOMIC = prove
 (`!r:A ring.
        PID r <=>
        integral_domain r /\
        bezout_ring r /\
        !x. x IN ring_carrier r /\ ~(x = ring_0 r)
            ==> ?n p. (!i. 1 <= i /\ i <= n ==> ring_irreducible r (p i)) /\
                      ring_associates r (ring_product r (1..n) p) x`,
  REWRITE_TAC[PID_EQ_UFD_BEZOUT_RING; UFD_EQ_ATOMIC] THEN
  MESON_TAC[BEZOUT_RING_IRREDUCIBLE_IMP_PRIME]);;

let BEZOUT_RING_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f /\ bezout_ring r ==> bezout_ring r'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[bezout_ring; finitely_generated_ideal] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[MESON[] `(!x. a = x ==> P x) <=> P a`] THEN
  REWRITE_TAC[IMP_IMP] THEN FIRST_ASSUM
   (SUBST1_TAC o SYM o CONJUNCT2 o REWRITE_RULE[ring_epimorphism]) THEN
  REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN DISCH_TAC THEN
  X_GEN_TAC `s:A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PRINCIPAL_IDEAL_EPIMORPHIC_IMAGE;
                IDEAL_GENERATED_BY_EPIMORPHIC_IMAGE]);;

let BEZOUT_QUOTIENT_RING = prove
 (`!r j:A->bool.
        bezout_ring r /\ ring_ideal r j
        ==> bezout_ring (quotient_ring r j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] BEZOUT_RING_EPIMORPHIC_IMAGE) THEN
  ASM_MESON_TAC[RING_EPIMORPHISM_RING_COSET]);;

let ISOMORPHIC_RING_BEZOUTNESS = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> (bezout_ring r <=> bezout_ring r')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[isomorphic_ring] THEN
  REWRITE_TAC[ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[BEZOUT_RING_EPIMORPHIC_IMAGE;
                RING_ISOMORPHISM_IMP_EPIMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* More divisibility properties that need something like GCD domain.         *)
(* ------------------------------------------------------------------------- *)

let RING_GCD_LMUL = prove
 (`!r a b c:A.
        (UFD r \/ integral_domain r /\ bezout_ring r) /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> ring_associates r (ring_gcd r (ring_mul r c a,ring_mul r c b))
                              (ring_mul r c (ring_gcd r (a,b)))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `integral_domain(r:A ring)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[UFD]] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `c:A = ring_0 r` THENL
   [ASM_SIMP_TAC[RING_MUL_LZERO; RING_GCD_00; RING_ASSOCIATES_REFL;
                 RING_GCD; RING_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_divides r (c:A) (ring_gcd r (ring_mul r c a,ring_mul r c b))`
  MP_TAC THENL
   [ASM_SIMP_TAC[RING_DIVIDES_GCD_EQ; RING_MUL] THEN
    ASM_SIMP_TAC[RING_DIVIDES_RMUL; RING_DIVIDES_REFL];
    GEN_REWRITE_TAC LAND_CONV [ring_divides]] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:A` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_ASSOCIATES_MUL THEN
  ASM_REWRITE_TAC[RING_ASSOCIATES_REFL] THEN
  ASM_REWRITE_TAC[RING_ASSOCIATES_SAME_DIVISORS; RING_GCD] THEN
  X_GEN_TAC `d:A` THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS `ring_divides r (ring_mul r c d) (ring_mul r c e:A)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[INTEGRAL_DOMAIN_DIVIDES_LMUL2]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[RING_DIVIDES_GCD_EQ; RING_MUL; INTEGRAL_DOMAIN_DIVIDES_LMUL2]);;

let RING_GCD_RMUL = prove
 (`!r a b c:A.
        (UFD r \/ integral_domain r /\ bezout_ring r) /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> ring_associates r (ring_gcd r (ring_mul r a c,ring_mul r b c))
                              (ring_mul r (ring_gcd r (a,b)) c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_GCD_LMUL) THEN
  ASM_MESON_TAC[RING_MUL_SYM; RING_MUL; RING_GCD]);;

let RING_COPRIME_DIVPROD_LEFT = prove
 (`!r a b c:A.
        (UFD r \/ integral_domain r /\ bezout_ring r) /\
        a IN ring_carrier r /\ b IN ring_carrier r /\
        ring_divides r c (ring_mul r a b) /\ ring_coprime r (a,c)
        ==> ring_divides r c b`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `integral_domain(r:A ring)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[UFD]] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `(c:A) IN ring_carrier r` THENL
   [ALL_TAC; ASM_MESON_TAC[ring_divides]] THEN
  SUBGOAL_THEN `b:A = ring_mul r (ring_gcd r (a,c)) b` SUBST1_TAC THENL
   [ASM_MESON_TAC[RING_GCD_EQ_1; RING_MUL_LID]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_GCD_RMUL o rand o snd) THEN
  ASM_REWRITE_TAC[ring_associates] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] RING_DIVIDES_TRANS) THEN
  ASM_SIMP_TAC[RING_DIVIDES_GCD_EQ; RING_MUL] THEN
  ASM_SIMP_TAC[RING_DIVIDES_RMUL; RING_DIVIDES_REFL]);;

let RING_COPRIME_DIVPROD_RIGHT = prove
 (`!r a b c:A.
        (UFD r \/ integral_domain r /\ bezout_ring r) /\
        a IN ring_carrier r /\ b IN ring_carrier r /\
        ring_divides r c (ring_mul r a b) /\ ring_coprime r (b,c)
        ==> ring_divides r c a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `b:A`; `a:A`; `c:A`]
   RING_COPRIME_DIVPROD_LEFT) THEN
  ASM_MESON_TAC[RING_MUL_SYM]);;

let RING_DIVIDES_MUL = prove
 (`!r a b c:A.
        (UFD r \/ integral_domain r /\ bezout_ring r) /\
        ring_coprime r (a,b) /\ ring_divides r a c /\ ring_divides r b c
        ==> ring_divides r (ring_mul r a b) c`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `integral_domain(r:A ring)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[UFD]] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `(a:A) IN ring_carrier r` THENL
   [ALL_TAC; ASM_MESON_TAC[ring_divides]] THEN
  ASM_CASES_TAC `(b:A) IN ring_carrier r` THENL
   [ALL_TAC; ASM_MESON_TAC[ring_divides]] THEN
  ASM_CASES_TAC `(c:A) IN ring_carrier r` THENL
   [ALL_TAC; ASM_MESON_TAC[ring_divides]] THEN
  SUBGOAL_THEN `c:A = ring_mul r (ring_gcd r (a,b)) c` SUBST1_TAC THENL
   [ASM_MESON_TAC[RING_GCD_EQ_1; RING_MUL_LID]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_GCD_RMUL o rand o snd) THEN
  ASM_REWRITE_TAC[ring_associates] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] RING_DIVIDES_TRANS) THEN
  ASM_SIMP_TAC[RING_DIVIDES_GCD_EQ; RING_MUL] THEN
  ASM_MESON_TAC[RING_DIVIDES_MUL2; RING_DIVIDES_REFL; RING_MUL_SYM]);;

let RING_COPRIME_LMUL = prove
 (`!r a b c:A.
        (UFD r \/ integral_domain r /\ bezout_ring r) /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> (ring_coprime r (ring_mul r a b,c) <=>
             ring_coprime r (a,c) /\ ring_coprime r (b,c))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `integral_domain(r:A ring)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[UFD]] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[ring_coprime; RING_MUL] THEN EQ_TAC THENL
   [ASM_MESON_TAC[RING_DIVIDES_LMUL; RING_DIVIDES_RMUL; RING_DIVIDES_TRANS;
                  RING_DIVIDES_REFL];
    DISCH_TAC] THEN
  X_GEN_TAC `d:A` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(d:A) IN ring_carrier r` THENL
   [ALL_TAC; ASM_MESON_TAC[ring_divides]] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_COPRIME_DIVPROD_LEFT THEN
  EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[ring_coprime] THEN ASM_MESON_TAC[RING_DIVIDES_TRANS]);;

let RING_COPRIME_RMUL = prove
 (`!r a b c:A.
        (UFD r \/ integral_domain r /\ bezout_ring r) /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> (ring_coprime r (a,ring_mul r b c) <=>
             ring_coprime r (a,b) /\ ring_coprime r (a,c))`,
  ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN SIMP_TAC[RING_COPRIME_LMUL]);;

(* ------------------------------------------------------------------------- *)
(* The general concept of a Boolean ring.                                    *)
(* ------------------------------------------------------------------------- *)

let boolean_ring = new_definition
 `boolean_ring (r:A ring) <=>
        !x. x IN ring_carrier r ==> ring_mul r x x = x`;;

let BOOLEAN_RING_SQUARE = prove
 (`!r x:A.
        boolean_ring r /\ x IN ring_carrier r
        ==> ring_mul r x x = x`,
  SIMP_TAC[boolean_ring]);;

let BOOLEAN_RING_DOUBLE = prove
 (`!r x:A.
        boolean_ring r /\ x IN ring_carrier r
        ==> ring_add r x x = ring_0 r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_ADD_LCANCEL_IMP THEN
  MAP_EVERY EXISTS_TAC [`r:A ring`; `ring_add r x x :A`] THEN
  ASM_SIMP_TAC[RING_ADD; RING_0; RING_ADD_RZERO] THEN
  TRANS_TAC EQ_TRANS `ring_mul r (ring_add r x x) (ring_add r x x):A` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[boolean_ring; RING_ADD]] THEN
  ASM_SIMP_TAC[RING_ADD; RING_ADD_LDISTRIB; RING_ADD_RDISTRIB] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[boolean_ring]) THEN
  ASM_SIMP_TAC[GSYM RING_ADD_ASSOC; RING_ADD]);;

let BOOLEAN_RING_NEG = prove
 (`!r x:A. boolean_ring r /\ x IN ring_carrier r ==> ring_neg r x = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_LNEG_UNIQUE THEN
  ASM_SIMP_TAC[BOOLEAN_RING_DOUBLE]);;

let BOOLEAN_RING_POW = prove
 (`!r (x:A) n.
        boolean_ring r /\ x IN ring_carrier r
        ==> ring_pow r x n = if n = 0 then ring_1 r else x`,
  SIMP_TAC[boolean_ring; RING_POW_IDEMPOTENT]);;

let BOOLEAN_RING_OF_NUM = prove
 (`!(r:A ring) n.
        boolean_ring r
        ==> ring_of_num r n = if ODD n then ring_1 r else ring_0 r`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[ring_of_num; ODD] THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[RING_ADD_LZERO; RING_1] THEN
  ASM_MESON_TAC[BOOLEAN_RING_DOUBLE; RING_1]);;

let BOOLEAN_RING_CHAR = prove
 (`!r:A ring.
        boolean_ring r ==> ring_char r = if trivial_ring r then 1 else 2`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[RING_CHAR_EQ_1] THEN
  MATCH_MP_TAC(MESON[DIVIDES_ANTISYM]
   `(!n:num. m divides n <=> p divides n) ==> m = p`) THEN
  ASM_SIMP_TAC[GSYM RING_OF_NUM_EQ_0; BOOLEAN_RING_OF_NUM] THEN
  REWRITE_TAC[GSYM NOT_EVEN; COND_SWAP; EVEN_EXISTS; GSYM divides] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM TRIVIAL_RING_10]);;

let BOOLEAN_RING_UNIT = prove
 (`!r x:A. boolean_ring r ==> (ring_unit r x <=> x = ring_1 r)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[RING_UNIT_1]] THEN
  REWRITE_TAC[ring_unit; LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
  TRANS_TAC EQ_TRANS `ring_mul r x (ring_mul r x y):A` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[RING_MUL_RID]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[boolean_ring]) THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC]);;

let BOOLEAN_RING_ZERODIVISOR = prove
 (`!r x:A.
        boolean_ring r
        ==> (ring_zerodivisor r x <=> x IN ring_carrier r /\ ~(x = ring_1 r))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:A = ring_1 r` THEN
  ASM_REWRITE_TAC[RING_ZERODIVISOR_1] THEN
  EQ_TAC THEN REWRITE_TAC[RING_ZERODIVISOR_IN_CARRIER] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ring_zerodivisor] THEN
  EXISTS_TAC `ring_sub r (x:A) (ring_1 r)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[boolean_ring]) THEN
  ASM_SIMP_TAC[RING_SUB; RING_1; RING_SUB_EQ_0; RING_SUB_LDISTRIB;
               RING_MUL_RID]);;

let BOOLEAN_RING_REGULAR = prove
 (`!r x:A.
        boolean_ring r ==> (ring_regular r x <=> x = ring_1 r)`,
  SIMP_TAC[ring_regular; BOOLEAN_RING_ZERODIVISOR] THEN MESON_TAC[RING_1]);;

let BOOLEAN_RING_IRREDUCIBLE = prove
 (`!r x:A. boolean_ring r ==> ~(ring_irreducible r x)`,
  SIMP_TAC[ring_irreducible; BOOLEAN_RING_UNIT] THEN
  REWRITE_TAC[boolean_ring] THEN MESON_TAC[]);;

let BOOLEAN_RING_DIVIDES = prove
 (`!r x y:A.
        boolean_ring r
        ==> (ring_divides r x y <=>
             x IN ring_carrier r /\ y IN ring_carrier r /\
             ring_mul r x y = y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_divides] THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(y:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RING_MUL_SYM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[boolean_ring]) THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC]);;

let BOOLEAN_RING_NILPOTENT = prove
 (`!r x:A. boolean_ring r ==> (ring_nilpotent r x <=> x = ring_0 r)`,
  REWRITE_TAC[ring_nilpotent] THEN
  MESON_TAC[BOOLEAN_RING_POW; RING_POW_1; RING_0; ARITH_RULE `~(1 = 0)`]);;

let BOOLEAN_RING_RADICAL = prove
 (`!r j:A->bool.
        boolean_ring r /\ ring_ideal r j ==> radical r j = j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; RADICAL_SUBSET] THEN
  ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN
  REWRITE_TAC[SUBSET; radical; IN_ELIM_THM] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  ASM_SIMP_TAC[BOOLEAN_RING_POW]);;

let TRIVIAL_IMP_BOOLEAN_RING = prove
 (`!r:A ring. trivial_ring r ==> boolean_ring r`,
  SIMP_TAC[trivial_ring; boolean_ring; IN_SING; RING_MUL_LZERO; RING_0]);;

let BOOLEAN_RING_10 = prove
 (`!r:A ring. ring_carrier r = {ring_0 r,ring_1 r} ==> boolean_ring r`,
  SIMP_TAC[boolean_ring; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[RING_MUL_LZERO; RING_MUL_LID; RING_0; RING_1]);;

let BOOLEAN_RING_2 = prove
 (`!r:A ring. ring_carrier r HAS_SIZE 2 ==> boolean_ring r`,
  SIMP_TAC[RING_CARRIER_HAS_SIZE_2; BOOLEAN_RING_10]);;

let ISOMORPHIC_RING_BOOLEANNESS = prove
 (`!r r'. r isomorphic_ring r' ==> (boolean_ring r <=> boolean_ring r')`,
  REWRITE_TAC[isomorphic_ring; boolean_ring; ring_isomorphism;
              ring_isomorphisms; ring_homomorphism] THEN
  SET_TAC[]);;

let BOOLEAN_RING_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f /\ boolean_ring r ==> boolean_ring r'`,
  REWRITE_TAC[boolean_ring; ring_epimorphism; ring_homomorphism] THEN
  SET_TAC[]);;

let BOOLEAN_QUOTIENT_RING = prove
 (`!r j:A->bool.
        boolean_ring r /\ ring_ideal r j
        ==> boolean_ring (quotient_ring r j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] BOOLEAN_RING_EPIMORPHIC_IMAGE) THEN
  ASM_MESON_TAC[RING_EPIMORPHISM_RING_COSET]);;

let BOOLEAN_RING_SUBRING_GENERATED = prove
 (`!r s:A->bool. boolean_ring r ==> boolean_ring (subring_generated r s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[boolean_ring] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
        RING_CARRIER_SUBRING_GENERATED_SUBSET) THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN ASM SET_TAC[]);;

let BOOLEAN_RING_MONOMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B).
        ring_monomorphism(r,r') f /\ boolean_ring r' ==> boolean_ring r`,
  MATCH_MP_TAC SUBRING_IMP_MONOMORPHIC_PROPERTY THEN
  REWRITE_TAC[BOOLEAN_RING_SUBRING_GENERATED] THEN
  REWRITE_TAC[ISOMORPHIC_RING_BOOLEANNESS]);;

let BOOLEAN_PROD_RING = prove
 (`!(r1:A ring) (r2:B ring).
        boolean_ring (prod_ring r1 r2) <=>
        boolean_ring r1 /\ boolean_ring r2`,
  REWRITE_TAC[boolean_ring; PROD_RING; FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
  MESON_TAC[RING_0]);;

let BOOLEAN_PRODUCT_RING = prove
 (`!k (r:K->A ring).
        boolean_ring (product_ring k r) <=>
        !i. i IN k ==> boolean_ring (r i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[boolean_ring; PRODUCT_RING] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; RESTRICTION_UNIQUE] THEN
  SIMP_TAC[FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ;
           CARTESIAN_PRODUCT_EQ_EMPTY; RING_CARRIER_NONEMPTY] THEN
  SIMP_TAC[IN_CARTESIAN_PRODUCT] THEN MESON_TAC[]);;

let BOOLEAN_IMP_BEZOUT_RING = prove
 (`!r:A ring. boolean_ring r ==> bezout_ring r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEZOUT_RING_2] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  REWRITE_TAC[PRINCIPAL_IDEAL_ALT] THEN
  EXISTS_TAC `ring_add r (ring_add r x y) (ring_mul r x y):A` THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
  ASM_SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; RING_IDEAL_IDEAL_GENERATED] THEN
  ASM_SIMP_TAC[IN_RING_IDEAL_ADD; IN_RING_IDEAL_MUL; IN_INSERT;
               RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_INC_GEN] THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING; RING_ADD; RING_MUL; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[ring_divides; RING_ADD; RING_MUL] THEN CONJ_TAC THENL
   [EXISTS_TAC `x:A`; EXISTS_TAC `y:A`] THEN
  ASM_SIMP_TAC[RING_ADD_RDISTRIB; RING_ADD; RING_MUL] THENL
   [SUBGOAL_THEN
     `ring_mul r (ring_mul r x y) x:A = ring_mul r y (ring_mul r x x)`
    SUBST1_TAC THENL [ASM_MESON_TAC[RING_MUL_AC; RING_MUL]; ALL_TAC];
    SUBGOAL_THEN
     `ring_add r (ring_mul r x y) (ring_mul r y y):A =
      ring_add r (ring_mul r y y) (ring_mul r x y)`
    SUBST1_TAC THENL [ASM_SIMP_TAC[RING_ADD_AC; RING_MUL]; ALL_TAC]] THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; GSYM RING_ADD_ASSOC; RING_MUL] THEN
  ASM_SIMP_TAC[BOOLEAN_RING_SQUARE; BOOLEAN_RING_DOUBLE; RING_MUL] THEN
  ASM_SIMP_TAC[RING_ADD_RZERO]);;

let BOOLEAN_RING_MAXIMAL_EQ_PRIME_IDEAL = prove
 (`!r j:A->bool.
           boolean_ring r ==> (maximal_ideal r j <=> prime_ideal r j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[MAXIMAL_IMP_PRIME_IDEAL] THEN
  ASM_CASES_TAC `ring_ideal r (j:A->bool)` THENL
   [ALL_TAC; ASM_MESON_TAC[PRIME_IMP_RING_IDEAL]] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_DOMAIN_QUOTIENT_RING;
               GSYM FIELD_QUOTIENT_RING] THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p ==> q`] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] FINITE_INTEGRAL_DOMAIN_IMP_FIELD) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRAL_DOMAIN_ZERODIVISOR) THEN
  ASM_SIMP_TAC[BOOLEAN_RING_ZERODIVISOR; BOOLEAN_QUOTIENT_RING] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `(!a. a IN s /\ ~(a = z) <=> a = w) ==> s SUBSET {w,z}`)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]);;

let BOOLEAN_RING_MULTSYS = prove
 (`!r x:A.
        boolean_ring r
        ==> (ring_multsys r {ring_1 r,x} <=> x IN ring_carrier r)`,
  REWRITE_TAC[boolean_ring] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[RING_MULTSYS_IDEMPOT] THEN REWRITE_TAC[ring_multsys] THEN
  ASM SET_TAC[]);;

let BOOLEAN_PROPER_IDEAL_COMPLEMENT = prove
 (`!r j x:A.
        boolean_ring r /\ proper_ideal r j /\ x IN j
        ==> ?y. y IN ring_carrier r DIFF j /\ ring_mul r x y = ring_0 r`,
  REWRITE_TAC[proper_ideal] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_ideal; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?z:A. z IN ring_carrier r /\ ~(z IN j)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `ring_add r z (ring_mul r x z):A` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[IN_DIFF; RING_ADD; RING_MUL] THEN
    UNDISCH_TAC `~((z:A) IN j)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    DISCH_TAC THEN SUBGOAL_THEN
     `z:A = ring_sub r (ring_add r z (ring_mul r x z)) (ring_mul r x z)`
    SUBST1_TAC THENL [RING_TAC; MATCH_MP_TAC IN_RING_IDEAL_SUB] THEN
    ASM_SIMP_TAC[IN_RING_IDEAL_RMUL];
    MP_TAC(ISPECL [`r:A ring`; `x:A`] BOOLEAN_RING_SQUARE) THEN
    MP_TAC(ISPECL [`r:A ring`; `ring_mul r x z:A`] BOOLEAN_RING_DOUBLE) THEN
    ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN RING_TAC]);;

let BOOLEAN_INTEGRAL_DOMAIN = prove
 (`!r:A ring.
        boolean_ring r /\ integral_domain r <=> ring_carrier r HAS_SIZE 2`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[RING_CARRIER_HAS_SIZE_2] THEN
  SIMP_TAC[TRIVIAL_RING_10; INTEGRAL_DOMAIN_10; BOOLEAN_RING_10] THEN
  REWRITE_TAC[integral_domain] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `a IN s /\ b IN s /\ (!c. c IN s /\ ~(c = a) /\ ~(c = b) ==> F)
    ==> s = {a,b}`) THEN
  REWRITE_TAC[RING_0; RING_1] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `ring_sub r x (ring_1 r):A`]) THEN
  ASM_SIMP_TAC[RING_SUB; RING_1; RING_SUB_LDISTRIB; RING_MUL_RID] THEN
  ASM_SIMP_TAC[RING_SUB_EQ_0; RING_1; RING_MUL] THEN
  ASM_MESON_TAC[boolean_ring]);;

(* ------------------------------------------------------------------------- *)
(* Von Neumann regular rings.                                                *)
(* ------------------------------------------------------------------------- *)

let vnregular_ring = new_definition
 `vnregular_ring (r:A ring) <=>
        !a. a IN ring_carrier r
            ==> ?x. x IN ring_carrier r /\
                    ring_mul r a (ring_mul r x a) = a`;;

let FIELD_IMP_VNREGULAR_RING = prove
 (`!r:A ring. field r ==> vnregular_ring r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vnregular_ring] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `ring_inv r x:A` THEN
  ASM_CASES_TAC `x:A = ring_0 r` THEN
  ASM_SIMP_TAC[RING_INV; RING_MUL; RING_MUL_LZERO; RING_0] THEN
  ASM_SIMP_TAC[FIELD_MUL_LINV; RING_MUL_RID]);;

let BOOLEAN_IMP_VNREGULAR_RING = prove
 (`!r:A ring. boolean_ring r ==> vnregular_ring r`,
  GEN_TAC THEN REWRITE_TAC[boolean_ring; vnregular_ring] THEN
  STRIP_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  EXISTS_TAC `x:A` THEN ASM_SIMP_TAC[]);;

let VNREGULAR_RING_EPIMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_epimorphism(r,r') f /\ vnregular_ring r ==> vnregular_ring r'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_epimorphism; vnregular_ring] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN DISCH_TAC THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:A` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN
  ASM_MESON_TAC[RING_MUL]);;

let VNREGULAR_QUOTIENT_RING = prove
 (`!r j:A->bool.
        vnregular_ring r /\ ring_ideal r j
        ==> vnregular_ring (quotient_ring r j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] VNREGULAR_RING_EPIMORPHIC_IMAGE) THEN
  ASM_MESON_TAC[RING_EPIMORPHISM_RING_COSET]);;

let ISOMORPHIC_RING_VNREGULARITY = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> (vnregular_ring r <=> vnregular_ring r')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[isomorphic_ring] THEN
  REWRITE_TAC[ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[VNREGULAR_RING_EPIMORPHIC_IMAGE;
                RING_ISOMORPHISM_IMP_EPIMORPHISM]);;

let VNREGULAR_PROD_RING = prove
 (`!(r1:A ring) (r2:B ring).
        vnregular_ring(prod_ring r1 r2) <=>
        vnregular_ring r1 /\ vnregular_ring r2`,
  REWRITE_TAC[vnregular_ring; PROD_RING] THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
  REWRITE_TAC[IN_CROSS; PAIR_EQ] THEN MESON_TAC[RING_0]);;

let VNREGULAR_PRODUCT_RING = prove
 (`!(r:K->A ring) k.
        vnregular_ring(product_ring k r) <=>
        !i. i IN k ==> vnregular_ring (r i)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] VNREGULAR_RING_EPIMORPHIC_IMAGE)) THEN
    ASM_MESON_TAC[RING_EPIMORPHISM_PRODUCT_PROJECTION];
    DISCH_TAC] THEN
  REWRITE_TAC[vnregular_ring; PRODUCT_RING] THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [CARTESIAN_PRODUCT_AS_RESTRICTIONS] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; RESTRICTION_EXTENSION] THEN
  SIMP_TAC[RESTRICTION] THEN REWRITE_TAC[EXISTS_CARTESIAN_PRODUCT_ELEMENT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[vnregular_ring]) THEN ASM SET_TAC[]);;

let VNREGULAR_IMP_REDUCED_RING = prove
 (`!r (x:A) n.
        vnregular_ring r /\ x IN ring_carrier r /\ ring_pow r x n = ring_0 r
        ==> x = ring_0 r`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o REWRITE_RULE[vnregular_ring]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`r:A ring`; `ring_mul r y x:A`; `n:num`]
        RING_POW_IDEMPOTENT) THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_MUL] THEN
  DISCH_THEN(MP_TAC o SYM) THEN
  ASM_SIMP_TAC[RING_MUL_POW; RING_MUL_RZERO; RING_POW] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[GSYM TRIVIAL_RING_10; trivial_ring] THEN ASM SET_TAC[];
    ASM_MESON_TAC[RING_MUL_RZERO]]);;

let VNREGULAR_RING_NILPOTENT = prove
 (`!r x:A.
        vnregular_ring r ==> (ring_nilpotent r x <=> x = ring_0 r)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[RING_NILPOTENT_0] THEN
  REWRITE_TAC[ring_nilpotent] THEN ASM_MESON_TAC[VNREGULAR_IMP_REDUCED_RING]);;

let VNREGULAR_RING_REGULAR = prove
 (`!r a:A. vnregular_ring r ==> (ring_regular r a <=> ring_unit r a)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[RING_UNIT_IMP_REGULAR] THEN
  REWRITE_TAC[ring_regular; ring_zerodivisor; ring_unit] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A` o GEN_REWRITE_RULE I [vnregular_ring]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `b:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ring_sub r (ring_mul r a b) (ring_1 r):A`) THEN
  ASM_SIMP_TAC[RING_1; RING_SUB; RING_MUL] THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN RING_TAC);;

let VNREGULAR_DOMAIN = prove
 (`!r:A ring.
        vnregular_ring r /\ integral_domain r <=> field r`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[FIELD_IMP_VNREGULAR_RING; FIELD_IMP_INTEGRAL_DOMAIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[FIELD_EQ_ALL_UNITS; GSYM VNREGULAR_RING_REGULAR] THEN
  SIMP_TAC[INTEGRAL_DOMAIN_EQ_ALL_REGULAR]);;

let VNREGULAR_RING_PRINCIPAL_IDEALS = prove
 (`!r:A ring.
        vnregular_ring r <=>
        !j. principal_ideal r j
            ==> ?e. e IN ring_carrier r /\
                    ring_mul r e e = e /\
                    j = ideal_generated r {e}`,
  GEN_TAC THEN REWRITE_TAC[vnregular_ring] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `j:A->bool` THEN REWRITE_TAC[principal_ideal] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ring_mul r y x:A` THEN
    ASM_SIMP_TAC[RING_MUL; GSYM RING_MUL_ASSOC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    ASM_SIMP_TAC[IDEALS_GENERATED_SING_EQ; RING_MUL] THEN
    ASM_SIMP_TAC[ring_associates; RING_DIVIDES_REFL; RING_DIVIDES_LMUL] THEN
    ASM_SIMP_TAC[ring_divides; RING_MUL] THEN
    EXISTS_TAC `x:A` THEN ASM_MESON_TAC[RING_MUL_AC; RING_MUL];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ideal_generated r {x:A}`) THEN
    REWRITE_TAC[PRINCIPAL_IDEAL_IDEAL_GENERATED_SING] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:A` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[IDEALS_GENERATED_SING_EQ; ring_associates] THEN
    ASM_REWRITE_TAC[ring_divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) o GSYM) THEN
    EXISTS_TAC `z:A` THEN ASM_MESON_TAC[RING_MUL; RING_MUL_AC]]);;

let VNREGULAR_IMP_BEZOUT_RING = prove
 (`!r:A ring. vnregular_ring r ==> bezout_ring r`,
  GEN_TAC THEN
  REWRITE_TAC[BEZOUT_RING_SETADD; VNREGULAR_RING_PRINCIPAL_IDEALS] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`j:A->bool`; `k:A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `k:A->bool` th) THEN MP_TAC(SPEC `j:A->bool` th)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `e:A` THEN STRIP_TAC THEN
  X_GEN_TAC `i:A` THEN STRIP_TAC THEN
  REWRITE_TAC[PRINCIPAL_IDEAL_ALT] THEN
  EXISTS_TAC `ring_sub r (ring_add r e i) (ring_mul r e i):A` THEN
  ASM_REWRITE_TAC[GSYM IDEAL_GENERATED_INSERT] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[IDEAL_GENERATED_MINIMAL_EQ; RING_IDEAL_IDEAL_GENERATED] THEN
  CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `t SUBSET u ==> s INTER t SUBSET u`) THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THENL
   [MATCH_MP_TAC IN_RING_IDEAL_SUB THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_RING_IDEAL_ADD;
      MATCH_MP_TAC IN_RING_IDEAL_MUL] THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN CONJ_TAC THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_INSERT];
    ASM_SIMP_TAC[IDEAL_GENERATED_SING_ALT; RING_SUB; RING_ADD; RING_MUL] THEN
    REWRITE_TAC[IN_ELIM_THM]] THEN
  CONJ_TAC THENL [EXISTS_TAC `e:A`; EXISTS_TAC `i:A`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC RING_RULE);;

let VNREGULAR_RING_FINITELY_GENERATED_IDEALS = prove
 (`!r:A ring.
        vnregular_ring r <=>
        !j. finitely_generated_ideal r j
            ==> ?e. e IN ring_carrier r /\
                    ring_mul r e e = e /\
                    j = ideal_generated r {e}`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BEZOUT_RING_FINITELY_GENERATED_EQ_PRINCIPAL_IDEAL;
               VNREGULAR_IMP_BEZOUT_RING] THEN
  ASM_REWRITE_TAC[GSYM VNREGULAR_RING_PRINCIPAL_IDEALS] THEN
  REWRITE_TAC[VNREGULAR_RING_PRINCIPAL_IDEALS] THEN
  ASM_MESON_TAC[PRINCIPAL_IMP_FINITELY_GENERATED_IDEAL]);;

let VNREGULAR_RING_IDEAL_IDEMPOT = prove
 (`!r j:A->bool.
        vnregular_ring r /\ ring_ideal r j ==> ring_setmul r j j = j`,
  REWRITE_TAC[vnregular_ring] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[RING_SETMUL_SUBSET_IDEAL;
               RING_IDEAL_IMP_SUBSET; SUBSET_REFL] THEN
  REWRITE_TAC[SUBSET; ring_setmul; IN_ELIM_THM] THEN
  ASM_MESON_TAC[IN_RING_IDEAL_LMUL; RING_IDEAL_IMP_SUBSET; SUBSET]);;

let VNREGULAR_RING = prove
 (`!r:A ring.
        vnregular_ring (r:A ring) <=>
        !a. a IN ring_carrier r
            ==> ?x. x IN ring_carrier r /\
                    ring_mul r a (ring_mul r x a) = a /\
                    ring_mul r x (ring_mul r a x) = x`,
  GEN_TAC THEN REWRITE_TAC[vnregular_ring] THEN
  EQ_TAC THENL [DISCH_TAC; MESON_TAC[]] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ring_mul r x (ring_mul r a x):A` THEN
  ASM_SIMP_TAC[RING_MUL] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  CONV_TAC RING_RULE);;

let VNREGULAR_RING_ALT = prove
 (`!r:A ring.
        vnregular_ring (r:A ring) <=>
        !a. a IN ring_carrier r
            ==> ?!x. x IN ring_carrier r /\
                     ring_mul r a (ring_mul r x a) = a /\
                     ring_mul r x (ring_mul r a x) = x`,
  GEN_TAC THEN REWRITE_TAC[VNREGULAR_RING] THEN MATCH_MP_TAC(MESON[]
   `(!a x y. P a /\ R a x /\ R a y ==> x = y)
    ==> ((!a. P a ==> ?x. R a x) <=> (!a. P a ==> ?!x. R a x))`) THEN
  CONV_TAC RING_RULE);;

let VNREGULAR_FRACTION_RING = prove
 (`!r:A ring.
        vnregular_ring r ==> (fraction_ring r) isomorphic_ring r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fraction_ring] THEN
  MATCH_MP_TAC RING_LOCALIZATION_UNCHANGED THEN
  REWRITE_TAC[RING_MULTSYS_REGULAR] THEN
  ASM_SIMP_TAC[VNREGULAR_RING_REGULAR; SUBSET_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The ring of Booleans under xor, and, basically the field GF(2).           *)
(* ------------------------------------------------------------------------- *)

let bool_ring = new_definition
 `bool_ring = ring((:bool),F,T,I,(\x y. ~(x <=> y)),(/\))`;;

let BOOL_RING = prove
 (`ring_carrier bool_ring = (:bool) /\
   ring_0 bool_ring = F /\
   ring_1 bool_ring = T /\
   ring_neg bool_ring = I /\
   ring_add bool_ring = (\x y. ~(x <=> y)) /\
   ring_mul bool_ring = (/\)`,
  PURE_REWRITE_TAC
   [GSYM PAIR_EQ; ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul;
    BETA_THM; PAIR] THEN
  PURE_REWRITE_TAC[bool_ring; GSYM(CONJUNCT2 ring_tybij)] THEN
  REWRITE_TAC[IN_UNIV; I_THM] THEN CONV_TAC TAUT);;

let FIELD_BOOL_RING = prove
 (`field bool_ring`,
  REWRITE_TAC[field; BOOL_RING; EXISTS_BOOL_THM; FORALL_BOOL_THM]);;

let NOT_TRIVIAL_BOOL_RING = prove
 (`~trivial_ring bool_ring`,
  REWRITE_TAC[TRIVIAL_RING_10; BOOL_RING]);;

let BOOLEAN_RING_BOOL_RING = prove
 (`boolean_ring bool_ring`,
  REWRITE_TAC[boolean_ring; BOOL_RING]);;

let INTEGRAL_DOMAIN_BOOL_RING = prove
 (`integral_domain bool_ring`,
  SIMP_TAC[FIELD_BOOL_RING; FIELD_IMP_INTEGRAL_DOMAIN]);;

let BOOL_RING_CARRIER_HAS_SIZE_2 = prove
 (`ring_carrier bool_ring HAS_SIZE 2`,
  REWRITE_TAC[BOOL_RING; HAS_SIZE_BOOL]);;

let ISOMORPHIC_RING_BOOL_RING = prove
 (`(!r:A ring. r isomorphic_ring bool_ring <=> ring_carrier r HAS_SIZE 2) /\
   (!r:A ring. bool_ring isomorphic_ring r <=> ring_carrier r HAS_SIZE 2)`,
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV)
   [ISOMORPHIC_RING_SYM] THEN
  REWRITE_TAC[] THEN GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ISOMORPHIC_RING_SIZE th]) THEN
    REWRITE_TAC[BOOL_RING_CARRIER_HAS_SIZE_2];
    REWRITE_TAC[RING_CARRIER_HAS_SIZE_2; TRIVIAL_RING_10] THEN STRIP_TAC] THEN
  ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  REWRITE_TAC[isomorphic_ring; BOOL_RING] THEN
  EXISTS_TAC `(\p. if p then ring_1 r else ring_0 r):bool->A` THEN
  REWRITE_TAC[RING_ISOMORPHISM; ring_homomorphism; BOOL_RING] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; I_THM; IN_UNIV;
              GSYM SUBSET_ANTISYM_EQ; IN_IMAGE] THEN
  REWRITE_TAC[FORALL_BOOL_THM; EXISTS_BOOL_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_INSERT; RING_0; RING_1; NOT_IN_EMPTY;
               RING_MUL_LID; RING_ADD_LZERO; RING_MUL_LZERO;
               RING_MUL_RID; RING_ADD_RZERO; RING_NEG_0] THEN
  MATCH_MP_TAC(RING_RULE
   `x IN ring_carrier r /\ y IN ring_carrier r /\
    ring_add r x y = ring_0 r
    ==> y = ring_neg r x /\ ring_0 r = ring_add r x y`) THEN
  REWRITE_TAC[RING_1] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `s = {a,b} ==> x IN s /\ ~(x = b) ==> x = a`)) THEN
  ASM_SIMP_TAC[RING_ADD; RING_1; RING_ADD_EQ_LEFT]);;

(* ------------------------------------------------------------------------- *)
(* The ring of integers.                                                     *)
(* ------------------------------------------------------------------------- *)

let integer_ring = new_definition
 `integer_ring = ring((:int),&0,&1,( -- ),( + ),( * ))`;;

let INTEGER_RING = prove
 (`ring_carrier integer_ring = (:int) /\
   ring_0 integer_ring = &0 /\
   ring_1 integer_ring = &1 /\
   ring_neg integer_ring = ( -- ) /\
   ring_add integer_ring = ( + ) /\
   ring_mul integer_ring = ( * )`,
  PURE_REWRITE_TAC
   [GSYM PAIR_EQ; ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul;
    BETA_THM; PAIR] THEN
  PURE_REWRITE_TAC[integer_ring; GSYM(CONJUNCT2 ring_tybij)] THEN
  REWRITE_TAC[IN_UNIV] THEN CONV_TAC INT_RING);;

let INTEGER_RING_UNIT = prove
 (`!x. ring_unit integer_ring x <=> x = &1 \/ x = -- &1`,
  REWRITE_TAC[ring_unit; INTEGER_RING; INT_MUL_EQ_1; IN_UNIV] THEN
  MESON_TAC[]);;

let INTEGER_RING_DIVIDES = prove
 (`!a b. ring_divides integer_ring a b <=> a divides b`,
  REWRITE_TAC[ring_divides; INTEGER_RING; IN_UNIV; int_divides]);;

let NOT_TRIVIAL_INTEGER_RING = prove
 (`~trivial_ring integer_ring`,
  REWRITE_TAC[TRIVIAL_RING_10; INTEGER_RING] THEN
  CONV_TAC INT_REDUCE_CONV);;

let NOT_FIELD_INTEGER_RING = prove
 (`~field integer_ring`,
  REWRITE_TAC[FIELD_EQ_ALL_UNITS; INTEGER_RING_UNIT; INTEGER_RING] THEN
  DISCH_THEN(MP_TAC o SPEC `&2:int` o CONJUNCT2) THEN REWRITE_TAC[IN_UNIV] THEN
  CONV_TAC INT_REDUCE_CONV);;

let RING_HOMOMORPHISM_INTEGER_RING_OF_INT = prove
 (`!r:A ring. ring_homomorphism (integer_ring,r) (ring_of_int r)`,
  GEN_TAC THEN REWRITE_TAC[ring_homomorphism; INTEGER_RING] THEN
  REWRITE_TAC[IN_UNIV; RING_OF_INT_0; RING_OF_INT_1; RING_OF_INT_NEG] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RING_OF_INT] THEN
  REWRITE_TAC[RING_OF_INT_ADD; RING_OF_INT_MUL]);;

let RING_MONOMORPHISM_INTEGER_RING_OF_INT = prove
 (`!r:A ring. ring_monomorphism (integer_ring,r) (ring_of_int r) <=>
              ring_char r = 0`,
  SIMP_TAC[RING_MONOMORPHISM_ALT; RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
  REWRITE_TAC[RING_OF_INT_EQ_0; INTEGER_RING; IN_UNIV; GSYM INT_OF_NUM_EQ] THEN
  MESON_TAC[INTEGER_RULE `!x:int. &0 divides x <=> x = &0`;
            INTEGER_RULE `!x:int. x divides x`]);;

let INTEGRAL_DOMAIN_INTEGER_RING = prove
 (`integral_domain integer_ring`,
  REWRITE_TAC[integral_domain; INTEGER_RING; INT_ENTIRE; IN_UNIV] THEN
  CONV_TAC INT_REDUCE_CONV);;

let EUCLIDEAN_INTEGER_RING = prove
 (`euclidean_ring integer_ring`,
  REWRITE_TAC[euclidean_ring; INTEGER_RING; IN_UNIV] THEN
  EXISTS_TAC `num_of_int o abs` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; o_DEF] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
  MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a div b:int`; `a rem b:int`] THEN
  MP_TAC(SPECL [`a:int`; `b:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let PID_INTEGER_RING = prove
 (`PID integer_ring`,
  MATCH_MP_TAC EUCLIDEAN_DOMAIN_IMP_PID THEN
  REWRITE_TAC[INTEGRAL_DOMAIN_INTEGER_RING; EUCLIDEAN_INTEGER_RING]);;

let UFD_INTEGER_RING = prove
 (`UFD integer_ring`,
  SIMP_TAC[PID_IMP_UFD; PID_INTEGER_RING]);;

let BEZOUT_INTEGER_RING = prove
 (`bezout_ring integer_ring`,
  SIMP_TAC[PID_INTEGER_RING; PID_IMP_BEZOUT_RING]);;

let INTEGER_RING_OF_NUM = prove
 (`ring_of_num integer_ring = int_of_num`,
  REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ring_of_num; INTEGER_RING; GSYM INT_OF_NUM_SUC]);;

let INTEGER_RING_OF_INT = prove
 (`ring_of_int integer_ring = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM] THEN
  REWRITE_TAC[RING_OF_INT_CLAUSES; FORALL_INT_CASES] THEN
  REWRITE_TAC[INTEGER_RING_OF_NUM; INTEGER_RING]);;

let INTEGER_RING_CHAR = prove
 (`ring_char integer_ring = 0`,
  SIMP_TAC[RING_CHAR_EQ_0; INTEGER_RING_OF_NUM; INTEGER_RING; INT_OF_NUM_EQ]);;

let INTEGER_RING_COPRIME = prove
 (`ring_coprime integer_ring = coprime`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; int_coprime] THEN
  SIMP_TAC[BEZOUT_RING_COPRIME; BEZOUT_INTEGER_RING] THEN
  REWRITE_TAC[INTEGER_RING; IN_UNIV]);;

let INTEGER_RING_ASSOCIATES = prove
 (`!x y. ring_associates integer_ring x y <=> x = y \/ x = --y`,
  SIMP_TAC[INTEGRAL_DOMAIN_ASSOCIATES; INTEGRAL_DOMAIN_INTEGER_RING] THEN
  REWRITE_TAC[INTEGER_RING_UNIT; INTEGER_RING; IN_UNIV] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; UNWIND_THM2; EXISTS_OR_THM] THEN
  INT_ARITH_TAC);;

let INTEGER_RING_GCD = prove
 (`ring_gcd integer_ring = gcd`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN
  REWRITE_TAC[ring_gcd; INTEGER_RING; IN_UNIV; INTEGER_RING_COPRIME] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `&0:int <= x /\ (x = &1 \/ x = -- &1) ==> &1 = x`) THEN
    REWRITE_TAC[int_gcd; GSYM INTEGER_RING_ASSOCIATES] THEN
    REWRITE_TAC[ring_associates; INTEGER_RING_DIVIDES] THEN
    CONJ_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `P x /\ (!x'. P x' ==> x' = x)
    ==> (if ?x. P x then @x. P x else a) = x`) THEN
  REWRITE_TAC[INTEGER_RING_DIVIDES] THEN CONJ_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; CONV_TAC INTEGER_RULE] THEN
    REWRITE_TAC[IN_IMAGE; INTEGER_RING_OF_NUM; IN_UNIV] THEN
    REWRITE_TAC[INT_OF_NUM_EXISTS; int_gcd];
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; INTEGER_RING_OF_NUM; IN_UNIV]] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  MATCH_MP_TAC(INT_ARITH
   `&0:int <= x /\ &0 <= y /\ (x = y \/ x = --y) ==> x = y`) THEN
  REWRITE_TAC[INT_POS; int_gcd; GSYM INTEGER_RING_ASSOCIATES] THEN
  REWRITE_TAC[ring_associates; INTEGER_RING_DIVIDES] THEN
  ASM_SIMP_TAC[INTEGER_RULE
   `(n:int) divides a /\ n divides b ==> n divides gcd(a,b)`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Ring of integers mod n, defaulting to all integers when n = 0             *)
(* ------------------------------------------------------------------------- *)

let integer_mod_ring = new_definition
 `integer_mod_ring n =
        if n = 0 then integer_ring else
        ring({m | &0 <= m /\ m < &n},
             &0,
             &1 rem &n,
             (\a. --a rem &n),
             (\a b. (a + b) rem &n),
             (\a b. (a * b) rem &n))`;;

let INTEGER_MOD_RING = prove
 (`ring_carrier (integer_mod_ring 0) = (:int) /\
   (!n. 0 < n
        ==> ring_carrier(integer_mod_ring n) = {m | &0 <= m /\ m < &n}) /\
   (!n. ring_0 (integer_mod_ring n) = &0) /\
   (!n. ring_1 (integer_mod_ring n) = &1 rem &n) /\
   (!n. ring_neg (integer_mod_ring n) = (\a. --a rem &n)) /\
   (!n. ring_add (integer_mod_ring n) = (\a b. (a + b) rem &n)) /\
   (!n. ring_mul (integer_mod_ring n) = (\a b. (a * b) rem &n))`,
  REWRITE_TAC[integer_mod_ring; INTEGER_RING] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `n:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_RING; LT_REFL; INT_REM_0] THENL
   [REWRITE_TAC[FUN_EQ_THM]; ASM_SIMP_TAC[LE_1]] THEN
  PURE_REWRITE_TAC
   [GSYM PAIR_EQ; ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul;
    BETA_THM; PAIR] THEN
  PURE_REWRITE_TAC[integer_mod_ring; GSYM(CONJUNCT2 ring_tybij)] THEN
  MP_TAC(GEN `m:int` (SPECL [`m:int`; `&n:int`] INT_DIVISION)) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ; INT_ABS_NUM; FORALL_AND_THM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; INT_LE_REFL] THEN
  ASM_SIMP_TAC[INT_OF_NUM_LT; LE_1; INT_ADD_LID; INT_ADD_RID] THEN
  ONCE_REWRITE_TAC[GSYM INT_ADD_REM; GSYM INT_MUL_REM] THEN
  REWRITE_TAC[INT_REM_REM] THEN REWRITE_TAC[INT_ADD_REM; INT_MUL_REM] THEN
  SIMP_TAC[INT_MUL_LID; INT_ADD_LINV; INT_REM_ZERO; INT_REM_LT] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INTEGER_RULE);;

let IN_INTEGER_MOD_RING_CARRIER = prove
 (`!n a. a IN ring_carrier(integer_mod_ring n) <=>
         &n:int = &0 \/ &0 <= a /\ a < &n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[CONJUNCT1 INTEGER_MOD_RING; IN_UNIV; INT_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[INTEGER_MOD_RING; LE_1; IN_ELIM_THM]);;

let INTEGER_MOD_RING_CARRIER_REM = prove
 (`!n x. x rem &n IN ring_carrier(integer_mod_ring n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[INTEGER_MOD_RING; LE_1; IN_UNIV; IN_ELIM_THM] THEN
  ASM_MESON_TAC[INT_DIVISION; INT_OF_NUM_EQ; INT_ABS_NUM]);;

let INTEGER_MOD_RING_TRIVIAL = prove
 (`integer_mod_ring 0 = integer_ring`,
  REWRITE_TAC[integer_mod_ring]);;

let INTEGER_MOD_RING_SUB = prove
 (`!n. ring_sub (integer_mod_ring n) = \a b. (a - b) rem &n`,
  REWRITE_TAC[ring_sub; INT_SUB; INTEGER_MOD_RING; FUN_EQ_THM] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

let INTEGER_MOD_RING_POW = prove
 (`!n a k. ring_pow (integer_mod_ring n) a k = (a pow k) rem &n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[INTEGER_MOD_RING; ring_pow; INT_POW] THEN
  ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN REWRITE_TAC[INT_REM_REM]);;

let INTEGER_MOD_RING_OF_NUM = prove
 (`!n k. ring_of_num (integer_mod_ring n) k = &k rem &n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ring_of_num; INTEGER_MOD_RING; GSYM INT_OF_NUM_SUC] THEN
  REWRITE_TAC[INT_REM_ZERO] THEN MESON_TAC[INT_ADD_REM; INT_REM_REM]);;

let INTEGER_MOD_RING_OF_INT = prove
 (`!n x. ring_of_int (integer_mod_ring n) x = x rem &n`,
  REWRITE_TAC[RING_OF_INT_CLAUSES; FORALL_INT_CASES] THEN
  REWRITE_TAC[INTEGER_MOD_RING_OF_NUM; INTEGER_MOD_RING; INT_NEG_REM]);;

let INTEGER_MOD_RING_CLAUSES = prove
 (`ring_carrier (integer_mod_ring 0) = (:int) /\
   (!n. 0 < n
        ==> ring_carrier(integer_mod_ring n) = {m | &0 <= m /\ m < &n}) /\
   (!n. ring_0 (integer_mod_ring n) = &0) /\
   (!n. ring_1 (integer_mod_ring n) = &1 rem &n) /\
   (!n. ring_neg (integer_mod_ring n) = (\a. --a rem &n)) /\
   (!n. ring_add (integer_mod_ring n) = (\a b. (a + b) rem &n)) /\
   (!n. ring_sub (integer_mod_ring n) = (\a b. (a - b) rem &n)) /\
   (!n. ring_mul (integer_mod_ring n) = (\a b. (a * b) rem &n)) /\
   (!n. ring_pow (integer_mod_ring n) = (\a k. (a pow k) rem &n)) /\
   (!n. ring_of_num (integer_mod_ring n) = (\k. &k rem &n)) /\
   (!n. ring_of_int (integer_mod_ring n) = \x. x rem &n)`,
  REWRITE_TAC[INTEGER_MOD_RING; INTEGER_MOD_RING_SUB; FUN_EQ_THM;
              INTEGER_MOD_RING_POW; INTEGER_MOD_RING_OF_NUM;
              INTEGER_MOD_RING_OF_INT]);;

let INTEGER_MOD_RING_CHAR = prove
 (`!n. ring_char (integer_mod_ring n) = n`,
  REWRITE_TAC[RING_CHAR_UNIQUE; INTEGER_MOD_RING_OF_NUM; INTEGER_MOD_RING] THEN
  REWRITE_TAC[num_divides] THEN
  REWRITE_TAC[INTEGER_RULE `(d:int) divides x <=> (x == &0) (mod d)`] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_ZERO]);;

let INTEGER_MOD_RING_DIVIDES = prove
 (`!n a b. ring_divides (integer_mod_ring n) a b <=>
           a IN ring_carrier(integer_mod_ring n) /\
           b IN ring_carrier(integer_mod_ring n) /\
           gcd(a,&n) divides b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[integer_mod_ring; INTEGER_RING; INTEGER_RING_DIVIDES] THEN
    REWRITE_TAC[IN_UNIV] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[ring_divides; INTEGER_MOD_RING; LE_1]] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC(TAUT
   `(p /\ q ==> (r <=> s)) ==> (p /\ q /\ r <=> p /\ q /\ s)`) THEN
  STRIP_TAC THEN REWRITE_TAC[INTEGER_RULE
   `gcd(a,n) divides b <=> ?x:int. (a * x == b) (mod n)`] THEN
  ASM_SIMP_TAC[GSYM INT_REM_EQ; INT_REM_LT] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:int`) THEN EXISTS_TAC `x rem &n` THEN
  ASM_SIMP_TAC[INT_LT_REM; INT_REM_POS; INT_OF_NUM_EQ;
               INT_OF_NUM_LT; LE_1] THEN
  ASM_MESON_TAC[INT_REM_REM; INT_MUL_REM]);;

let INTEGER_MOD_RING_ASSOCIATES = prove
 (`!n x y. ring_associates (integer_mod_ring n) x y <=>
           x IN ring_carrier(integer_mod_ring n) /\
           y IN ring_carrier(integer_mod_ring n) /\
           gcd(x,&n) = gcd(y,&n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_associates] THEN
  REWRITE_TAC[INTEGER_MOD_RING_DIVIDES] THEN
  ASM_CASES_TAC `x IN ring_carrier (integer_mod_ring n)` THEN
  ASM_CASES_TAC `y IN ring_carrier (integer_mod_ring n)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[INTEGER_RULE
   `gcd(x:int,n) divides y /\ gcd(y,n) divides x <=>
    gcd(x,n) divides gcd(y,n) /\ gcd(y,n) divides gcd(x,n)`] THEN
  REWRITE_TAC[GSYM INTEGER_RING_DIVIDES; GSYM ring_associates] THEN
  REWRITE_TAC[INTEGER_RING_ASSOCIATES] THEN MATCH_MP_TAC(INT_ARITH
   `&0:int <= x /\ &0 <= y ==> (x = y \/ x = --y <=> x = y)`) THEN
  REWRITE_TAC[int_gcd]);;

let INTEGER_MOD_RING_UNIT = prove
 (`!n x. ring_unit (integer_mod_ring n) x <=>
         x IN ring_carrier(integer_mod_ring n) /\ coprime(x,&n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RING_UNIT_DIVIDES; INTEGER_MOD_RING_DIVIDES; RING_1] THEN
  AP_TERM_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[integer_mod_ring; INTEGER_RING] THEN CONV_TAC INTEGER_RULE;
    ASM_SIMP_TAC[INTEGER_MOD_RING]] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[INT_REM_REFL] THEN CONV_TAC INTEGER_RULE;
    REWRITE_TAC[INTEGER_RULE `coprime(x:int,y) <=> gcd(x,y) divides &1`]] THEN
  AP_TERM_TAC THEN REWRITE_TAC[INT_REM_EQ_SELF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_EQ]) THEN ASM_INT_ARITH_TAC);;

let TRIVIAL_INTEGER_MOD_RING = prove
 (`!n. trivial_ring (integer_mod_ring n) <=> n = 1`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[integer_mod_ring; NOT_TRIVIAL_INTEGER_RING; ARITH_EQ];
    ASM_SIMP_TAC[TRIVIAL_RING_10; INTEGER_MOD_RING]] THEN
  EQ_TAC THEN SIMP_TAC[INT_REM_REFL] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INT_ARITH `x:int = &1 ==> ~(x = &0)`) THEN
  REWRITE_TAC[INT_REM_EQ_SELF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_EQ]) THEN ASM_INT_ARITH_TAC);;

let FINITE_INTEGER_MOD_RING = prove
 (`!n. FINITE(ring_carrier(integer_mod_ring n)) <=> ~(n = 0)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[integer_mod_ring; INTEGER_RING; GSYM INFINITE] THEN
    REWRITE_TAC[int_INFINITE];
    ASM_SIMP_TAC[INTEGER_MOD_RING; LE_1; FINITE_INT_SEG]]);;

let CARD_INTEGER_MOD_RING = prove
 (`!n. ~(n = 0) ==> CARD(ring_carrier(integer_mod_ring n)) = n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTEGER_MOD_RING; LE_1] THEN
  SUBGOAL_THEN `{m:int | &0 <= m /\ m < &n} = IMAGE (&) {i | i < n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
    SIMP_TAC[IN_ELIM_THM; IN_IMAGE; INT_OF_NUM_LT; INT_POS] THEN
    REWRITE_TAC[GSYM INT_FORALL_POS; IMP_CONJ] THEN
    REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_EQ; UNWIND_THM1];
    SIMP_TAC[CARD_IMAGE_INJ; INT_OF_NUM_EQ; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[CARD_NUMSEG_LT]]);;

let FIELD_INTEGER_MOD_RING = prove
 (`!n. field (integer_mod_ring n) <=> prime n`,
  GEN_TAC THEN REWRITE_TAC[prime] THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[integer_mod_ring; NOT_FIELD_INTEGER_RING] THEN
    DISCH_THEN(MP_TAC o SPEC `2` o CONJUNCT2) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    REWRITE_TAC[FIELD_EQ_ALL_UNITS; GSYM TRIVIAL_RING_10]] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[TRIVIAL_INTEGER_MOD_RING] THEN
  ASM_SIMP_TAC[INTEGER_MOD_RING; LE_1; INTEGER_MOD_RING_UNIT] THEN
  REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; GSYM INT_FORALL_POS] THEN
  REWRITE_TAC[GSYM num_coprime; INT_OF_NUM_EQ; INT_OF_NUM_LT] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `d:num` THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LE_LT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:num`) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[NUMBER_RULE `0 divides n <=> n = 0`];
      DISCH_TAC THEN DISJ1_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
       `coprime(d,n) ==> d divides n ==> coprime(d,d)`)) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE];
    DISCH_TAC THEN REWRITE_TAC[coprime] THEN
    X_GEN_TAC `e:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:num`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE)) THEN ASM_ARITH_TAC]);;

let INTEGRAL_DOMAIN_INTEGER_MOD_RING = prove
 (`!n. integral_domain (integer_mod_ring n) <=> n = 0 \/ prime n`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[integer_mod_ring; INTEGRAL_DOMAIN_INTEGER_RING];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[prime; integral_domain; GSYM TRIVIAL_RING_10] THEN
    ASM_REWRITE_TAC[TRIVIAL_INTEGER_MOD_RING];
    ASM_SIMP_TAC[FINITE_INTEGRAL_DOMAIN_EQ_FIELD;
                 FINITE_INTEGER_MOD_RING; FIELD_INTEGER_MOD_RING]]);;

(* ------------------------------------------------------------------------- *)
(* Conversion for explicit calculation over integer_mod_ring n (nonzero n)   *)
(* ------------------------------------------------------------------------- *)

let RING_INV_INTEGER_MOD_RING = prove
 (`!n a. ring_inv (integer_mod_ring n) (&a) =
         if (n = 0 \/ ~(n = 1) /\ a < n) /\ coprime(a,n)
         then &(inverse_mod n a) else &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_inv] THEN
  SIMP_TAC[INTEGER_MOD_RING; INTEGER_MOD_RING_UNIT; GSYM num_coprime] THEN
  ASM_CASES_TAC `coprime(a:num,n)` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[COPRIME_0; INTEGER_MOD_RING; LE_1; inverse_mod; ARITH] THEN
    REWRITE_TAC[IN_UNIV; INT_MUL_LID; IN_ELIM_THM; INT_REM_0; SELECT_UNIQUE];
    ASM_SIMP_TAC[INTEGER_MOD_RING; LE_1; IN_ELIM_THM] THEN
    REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_LE; LE_0] THEN DISCH_TAC] THEN
  ASM_CASES_TAC `a:num < n` THEN ASM_REWRITE_TAC[COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SELECT_UNIQUE THENL
   [REWRITE_TAC[INT_REM_1] THEN INT_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `p:int` THEN REWRITE_TAC[] THEN EQ_TAC THENL
   [SPEC_TAC(`p:int`,`p:int`) THEN
    REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INVERSE_MOD_UNIQUE THEN ASM_SIMP_TAC[CONG; LT_IMP_LE];
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_REM; GSYM CONG] THEN
    REWRITE_TAC[INVERSE_MOD_BOUND; INVERSE_MOD_RMUL_EQ] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let INTEGER_MOD_RING_RED_CONV =
  let [pth_0; pth_1; pth_num; pth_neg; pth_add; pth_sub; pth_mul; pth_pow] =
      (CONJUNCTS o prove)
   (`ring_0 (integer_mod_ring n) = &0 /\
     ring_1 (integer_mod_ring n) = &1 rem &n /\
     ring_of_num (integer_mod_ring n) m = &m rem &n /\
     ring_neg (integer_mod_ring n) (&a) = --(&a) rem &n /\
     ring_add (integer_mod_ring n) (&a) (&b) = (&a + &b) rem &n /\
     ring_sub (integer_mod_ring n) (&a) (&b) = (&a - &b) rem &n /\
     ring_mul (integer_mod_ring n) (&a) (&b) = (&a * &b) rem &n /\
     ring_pow (integer_mod_ring n) (&a) k = (&a pow k) rem &n`,
   REWRITE_TAC[ring_sub; INT_SUB; INTEGER_MOD_RING_OF_NUM] THEN
   REWRITE_TAC[INTEGER_MOD_RING_POW; INTEGER_MOD_RING] THEN
   CONV_TAC INT_REM_DOWN_CONV THEN REFL_TAC)
  and pth_inv = SPEC_ALL RING_INV_INTEGER_MOD_RING
  and pth_div = prove
   (`ring_div (integer_mod_ring n) (&a) (&b) =
        if (n = 0 \/ ~(n = 1) /\ b < n) /\ coprime(b,n)
         then (&a * &(inverse_mod n b)) rem &n else &0`,
    REWRITE_TAC[ring_div; RING_INV_INTEGER_MOD_RING] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_MOD_RING] THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_REM_ZERO]) in
  let baseconv =
    GEN_REWRITE_CONV I [pth_0] ORELSEC
    ((GEN_REWRITE_CONV I [pth_1; pth_num] ORELSEC
      (GEN_REWRITE_CONV I [pth_neg] THENC
       LAND_CONV(TRY_CONV INT_NEG_CONV)) ORELSEC
      (GEN_REWRITE_CONV I [pth_add] THENC
       LAND_CONV(TRY_CONV INT_ADD_CONV)) ORELSEC
      (GEN_REWRITE_CONV I [pth_sub] THENC
       LAND_CONV(TRY_CONV INT_SUB_CONV)) ORELSEC
      (GEN_REWRITE_CONV I [pth_mul] THENC
       LAND_CONV(TRY_CONV INT_MUL_CONV))) THENC
     INT_REM_CONV) ORELSEC
    (GEN_REWRITE_CONV I [pth_pow] THENC INT_POW_REM_CONV) ORELSEC
    (GEN_REWRITE_CONV I [pth_inv] THENC
     RATOR_CONV(LAND_CONV(DEPTH_CONV(NUM_RED_CONV ORELSEC COPRIME_CONV))) THENC
     (GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)] ORELSEC
      (GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)] THENC
       RAND_CONV INVERSE_MOD_CONV))) ORELSEC
    (GEN_REWRITE_CONV I [pth_div] THENC
     RATOR_CONV(LAND_CONV(DEPTH_CONV(NUM_RED_CONV ORELSEC COPRIME_CONV))) THENC
     (GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)] ORELSEC
      (GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)] THENC
       LAND_CONV(RAND_CONV(RAND_CONV INVERSE_MOD_CONV) THENC
                 INT_MUL_CONV) THENC
       INT_REM_CONV))) in
  fun tm ->
    let th = baseconv tm in
    if is_intconst(rand(concl th)) then th
    else failwith "INTEGER_MOD_RING_RED_CONV";;

(* ------------------------------------------------------------------------- *)
(* The ring (and field) of real numbers.                                     *)
(* ------------------------------------------------------------------------- *)

let real_ring = new_definition
 `real_ring = ring((:real),&0,&1,( -- ),( + ),( * ))`;;

let REAL_RING_CLAUSES = prove
 (`ring_carrier real_ring = (:real) /\
   ring_0 real_ring = &0 /\
   ring_1 real_ring = &1 /\
   ring_neg real_ring = ( -- ) /\
   ring_add real_ring = ( + ) /\
   ring_mul real_ring = ( * )`,
  PURE_REWRITE_TAC
   [GSYM PAIR_EQ; ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul;
    BETA_THM; PAIR] THEN
  PURE_REWRITE_TAC[real_ring; GSYM(CONJUNCT2 ring_tybij)] THEN
  REWRITE_TAC[IN_UNIV] THEN CONV_TAC REAL_RING);;

let FIELD_REAL_RING = prove
 (`field real_ring`,
  REWRITE_TAC[field; REAL_RING_CLAUSES; IN_UNIV] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MESON_TAC[REAL_MUL_RINV]);;

let INTEGRAL_DOMAIN_REAL_RING = prove
 (`integral_domain real_ring`,
  REWRITE_TAC[integral_domain; REAL_RING_CLAUSES; REAL_ENTIRE; IN_UNIV] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let REAL_RING_OF_NUM = prove
 (`ring_of_num real_ring = real_of_num`,
  REWRITE_TAC[FUN_EQ_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ring_of_num; REAL_RING_CLAUSES; GSYM REAL_OF_NUM_SUC]);;

let REAL_RING_OF_INT = prove
 (`ring_of_int real_ring = real_of_int`,
  REWRITE_TAC[FUN_EQ_THM; I_THM] THEN
  REWRITE_TAC[RING_OF_INT_CLAUSES; FORALL_INT_CASES] THEN
  REWRITE_TAC[int_neg_th; int_of_num_th; REAL_RING_OF_NUM] THEN
  REWRITE_TAC[REAL_RING_CLAUSES]);;

let REAL_RING_CHAR = prove
 (`ring_char real_ring = 0`,
  SIMP_TAC[RING_CHAR_EQ_0; REAL_RING_OF_NUM; REAL_RING_CLAUSES;
           REAL_OF_NUM_EQ]);;

let REAL_RING_SUB = prove
 (`ring_sub real_ring = (-)`,
  REWRITE_TAC[FUN_EQ_THM; ring_sub; REAL_RING_CLAUSES] THEN REAL_ARITH_TAC);;

let REAL_RING_INV = prove
 (`ring_inv real_ring = inv`,
  REWRITE_TAC[FUN_EQ_THM; ring_inv; REAL_RING_CLAUSES] THEN
  SIMP_TAC[FIELD_UNIT; FIELD_REAL_RING; REAL_RING_CLAUSES;
           IN_UNIV; COND_SWAP] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_INV_0] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN POP_ASSUM MP_TAC THEN
  CONV_TAC REAL_FIELD);;

let REAL_RING_DIV = prove
 (`ring_div real_ring = (/)`,
  REWRITE_TAC[FUN_EQ_THM; ring_div; REAL_RING_CLAUSES; REAL_RING_INV] THEN
  REAL_ARITH_TAC);;

let REAL_RING_POW = prove
 (`ring_pow real_ring = (pow)`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; real_pow; REAL_RING_CLAUSES]);;

let REAL_FIELD_CLAUSES = prove
 (`ring_carrier real_ring = (:real) /\
   ring_0 real_ring = &0 /\
   ring_1 real_ring = &1 /\
   ring_neg real_ring = ( -- ) /\
   ring_add real_ring = ( + ) /\
   ring_mul real_ring = ( * ) /\
   ring_of_num real_ring = real_of_num /\
   ring_sub real_ring = (-) /\
   ring_inv real_ring = inv /\
   ring_div real_ring = (/) /\
   ring_pow real_ring = (pow)`,
  REWRITE_TAC[REAL_RING_CLAUSES; REAL_RING_OF_NUM; REAL_RING_SUB;
              REAL_RING_INV; REAL_RING_DIV; REAL_RING_POW]);;

(* ------------------------------------------------------------------------- *)
(* Monoid of monomials over an arbitrary set of "variables".                 *)
(* ------------------------------------------------------------------------- *)

let monomial_1 = new_definition
 `monomial_1 = \i:V. 0`;;

let monomial_mul = new_definition
 `monomial_mul (m1:V->num) (m2:V->num) =
     \i. m1 i + m2 i`;;

let monomial_div = new_definition
 `monomial_div (m1:V->num) (m2:V->num) =
     \i. m1 i - m2 i`;;

let monomial_restrict = new_definition
 `monomial_restrict s (m:V->num) = \i. if i IN s then m i else 0`;;

let monomial_divides = new_definition
 `monomial_divides (m1:V->num) (m2:V->num) <=> !i. m1 i <= m2 i`;;

let monomial_var = new_definition
 `monomial_var (v:V) = \i. if i = v then 1 else 0`;;

let monomial_vars = new_definition
 `monomial_vars m = {i:V | ~(m i = 0)}`;;

let monomial_deg = new_definition
 `monomial_deg m = nsum (monomial_vars m) (m:V->num)`;;

let monomial = new_definition
 `monomial (s:V->bool) m <=>
     FINITE(monomial_vars m) /\ (monomial_vars m) SUBSET s`;;

let MONOMIAL_POINTWISE_TAC =
  let monomial_eq = prove
   (`!m1 m2:V->num. m1 = m2 <=> !x. m1 x = m2 x`,
    REWRITE_TAC[FUN_EQ_THM]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[monomial_eq; monomial_divides] THEN
  REWRITE_TAC[monomial_1; monomial_mul; monomial_div;
              monomial_restrict; monomial_var] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN TRY EQ_TAC THEN
  REWRITE_TAC[AND_FORALL_THM; IMP_IMP] THEN
  TRY(MATCH_MP_TAC MONO_FORALL);;

let MONOMIAL_TAC =
  MONOMIAL_POINTWISE_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_ARITH_TAC;;

let MONOMIAL_RULE tm = prove(tm,MONOMIAL_TAC);;

let MONOMIAL_VARS_1 = prove
 (`monomial_vars (monomial_1:V->num) = {}`,
  REWRITE_TAC[monomial_vars; monomial_1; EMPTY_GSPEC]);;

let MONOMIAL_VARS_EQ_EMPTY = prove
 (`!m:V->num. monomial_vars m = {} <=> m = monomial_1`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
  REWRITE_TAC[NOT_IN_EMPTY; monomial_vars; monomial_1; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MONOMIAL_VARS_MUL = prove
 (`!m1 m2:V->num.
        monomial_vars(monomial_mul m1 m2) =
        monomial_vars m1 UNION monomial_vars m2`,
  REWRITE_TAC[monomial_vars; monomial_mul; ADD_EQ_0] THEN SET_TAC[]);;

let MONOMIAL_VARS_VAR = prove
 (`!v:V. monomial_vars(monomial_var v) = {v}`,
  GEN_TAC THEN REWRITE_TAC[monomial_vars; monomial_var] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SET_TAC[]);;

let MONOMIAL_VARS_RESTRICT = prove
 (`!s m:V->num.
        monomial_vars(monomial_restrict s m) = s INTER monomial_vars m`,
  REWRITE_TAC[monomial_vars; monomial_restrict] THEN SET_TAC[]);;

let MONOMIAL_MONO = prove
 (`!s t (m:V->num).
        monomial s m /\ s SUBSET t ==> monomial t m`,
  REWRITE_TAC[monomial] THEN SET_TAC[]);;

let MONOMIAL_UNIV = prove
 (`!s m. monomial s m ==> monomial (:V) m`,
  REWRITE_TAC[monomial] THEN SET_TAC[]);;

let MONOMIAL_1 = prove
 (`!s:V->bool. monomial s monomial_1`,
  REWRITE_TAC[monomial; monomial_1; monomial_vars; EMPTY_GSPEC] THEN
  REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET]);;

let MONOMIAL_MUL = prove
 (`!(s:V->bool) m1 m2.
        monomial s (monomial_mul m1 m2) <=> monomial s m1 /\ monomial s m2`,
  REWRITE_TAC[monomial; monomial_mul; monomial_vars; ADD_EQ_0; SET_RULE
   `{x | ~(P x /\ Q x)} = {x | ~P x} UNION {x | ~Q x}`] THEN
  REWRITE_TAC[UNION_SUBSET; FINITE_UNION] THEN REWRITE_TAC[CONJ_ACI]);;

let MONOMIAL_DIVISOR = prove
 (`!(s:V->bool) d m.
        monomial s m /\ monomial_divides d m ==> monomial s d`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[monomial; monomial_vars; monomial_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(MESON[FINITE_SUBSET; SUBSET_TRANS]
   `s SUBSET t ==> FINITE t /\ t SUBSET u ==> FINITE s /\ s SUBSET u`) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM] THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN ARITH_TAC);;

let MONOMIAL_VAR = prove
 (`!(s:V->bool) v. monomial s (monomial_var v) <=> v IN s`,
  REWRITE_TAC[monomial; monomial_vars; monomial_var] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MESON[] `~(if p then F else T) <=> p`] THEN
  REWRITE_TAC[SING_GSPEC; FINITE_SING; SING_SUBSET]);;

let MONOMIAL_RESTRICT = prove
 (`!(s:V->bool) m. FINITE s ==> monomial s (monomial_restrict s m)`,
  REWRITE_TAC[monomial; MONOMIAL_VARS_RESTRICT] THEN
  SIMP_TAC[FINITE_INTER; INTER_SUBSET]);;

let MONOMIAL = prove
 (`monomial (:V) m <=> FINITE(monomial_vars m)`,
  REWRITE_TAC[monomial; SUBSET_UNIV]);;

let MONOMIAL_DEG_1 = prove
 (`monomial_deg (monomial_1:V->num) = 0`,
  REWRITE_TAC[monomial_deg; MONOMIAL_VARS_1; NSUM_CLAUSES]);;

let MONOMIAL_DEG_VAR = prove
 (`!v:V. monomial_deg (monomial_var v) = 1`,
  REWRITE_TAC[monomial_deg; MONOMIAL_VARS_VAR; NSUM_SING] THEN
  REWRITE_TAC[monomial_var]);;

let MONOMIAL_DEG_EQ_0_ALT = prove
 (`!m. monomial (:V) m ==> (monomial_deg m = 0 <=> m = monomial_1)`,
  REWRITE_TAC[MONOMIAL] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN SIMP_TAC[MONOMIAL_DEG_1] THEN
  ASM_SIMP_TAC[monomial_deg; NSUM_EQ_0_IFF] THEN
  REWRITE_TAC[GSYM MONOMIAL_VARS_EQ_EMPTY; monomial_vars] THEN SET_TAC[]);;

let MONOMIAL_DEG_EQ_0 = prove
 (`!s m. monomial s m ==> (monomial_deg m = 0 <=> m = monomial_1)`,
  SIMP_TAC[monomial; SUBSET_UNIV; MONOMIAL_DEG_EQ_0_ALT]);;

let MONOMIAL_DIV_DIVIDES = prove
 (`!m d:V->num. monomial_divides (monomial_div m d) m`,
  MONOMIAL_TAC);;

let MONOMIAL_DIV = prove
 (`!s m d:V->num. monomial s m ==> monomial s (monomial_div m d)`,
  MESON_TAC[MONOMIAL_DIVISOR; MONOMIAL_DIV_DIVIDES]);;

let MONOMIAL_DIVIDES_1 = prove
 (`!m:V->num. monomial_divides monomial_1 m`,
  MONOMIAL_TAC);;

let MONOMIAL_DIVIDES_EXISTS = prove
 (`!m1 m2:V->num.
        monomial_divides m1 m2 <=> ?m. m2 = monomial_mul m1 m`,
  MONOMIAL_POINTWISE_TAC THEN REWRITE_TAC[UNWIND_THM2;
   ARITH_RULE `a:num = b + m <=> m = a - b /\ b <= a`] THEN
  ARITH_TAC);;

let MONOMIAL_DEG_MUL = prove
 (`!(m1:V->num) m2.
        monomial (:V) m1 /\ monomial (:V) m2
        ==> monomial_deg(monomial_mul m1 m2) =
            monomial_deg m1 + monomial_deg m2`,
  REWRITE_TAC[monomial; monomial_vars] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[monomial_deg; monomial_vars; monomial_mul; ADD_EQ_0] THEN
  REWRITE_TAC[SET_RULE
   `{i | ~(P i /\ Q i)} = {i | ~P i} UNION {i | ~Q i}`] THEN
  ASM_SIMP_TAC[NSUM_ADD; FINITE_UNION] THEN BINOP_TAC THEN
  MATCH_MP_TAC NSUM_SUPERSET THEN SET_TAC[]);;

let MONOMIAL_DEG_LE = prove
 (`!(m1:V->num) m2.
        monomial (:V) m2 /\
        monomial_divides m1 m2
        ==> monomial_deg m1 <= monomial_deg m2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MONOMIAL; CONJ_ASSOC; monomial_vars] THEN
  ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
  REWRITE_TAC[MONOMIAL_DIVIDES_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:V->num` THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [monomial_mul] THEN
  REWRITE_TAC[ADD_EQ_0; FINITE_UNION; SET_RULE
   `{i | ~(P i /\ Q i)} = {i | ~P i} UNION {i | ~Q i}`] THEN
  SIMP_TAC[MONOMIAL_DEG_MUL; MONOMIAL; GSYM monomial_vars; LE_ADD]);;

let MONOMIAL_VAR_EQ = prove
 (`!v w:V. monomial_var v = monomial_var w <=> v = w`,
  REWRITE_TAC[monomial_var; FUN_EQ_THM] THEN
  MESON_TAC[NUM_REDUCE_CONV `1 = 0`]);;

let MONOMIAL_MUL_LID = prove
 (`!m:V->num. monomial_mul monomial_1 m = m`,
  MONOMIAL_TAC);;

let MONOMIAL_MUL_RID = prove
 (`!m:V->num. monomial_mul m monomial_1 = m`,
  MONOMIAL_TAC);;

let MONOMIAL_MUL_SYM = prove
 (`!m1 m2:V->num.
        monomial_mul m1 m2 = monomial_mul m2 m1`,
  MONOMIAL_TAC);;

let MONOMIAL_MUL_ASSOC = prove
 (`!m1 m2 m3:V->num.
        monomial_mul m1 (monomial_mul m2 m3) =
        monomial_mul (monomial_mul m1 m2) m3`,
  MONOMIAL_TAC);;

let MONOMIAL_MUL_AC = prove
 (`(!m1 m2. monomial_mul m1 m2 = monomial_mul m2 m1) /\
   (!m1 m2 m3. monomial_mul (monomial_mul m1 m2) m3 =
            monomial_mul m1 (monomial_mul m2 m3)) /\
   (!m1 m2 m3. monomial_mul m1 (monomial_mul m2 m3) =
            monomial_mul m2 (monomial_mul m1 m3))`,
  MONOMIAL_TAC);;

let MONOMIAL_MUL_EQ_1 = prove
 (`!m1 m2:V->num.
        monomial_mul m1 m2 = monomial_1 <=>
        m1 = monomial_1 /\ m2 = monomial_1`,
  MONOMIAL_TAC);;

let MONOMIAL_MUL_LCANCEL = prove
 (`!m m1 m2:V->num. monomial_mul m m1 = monomial_mul m m2 <=> m1 = m2`,
  MONOMIAL_TAC);;

let MONOMIAL_MUL_RCANCEL = prove
 (`!m m1 m2:V->num. monomial_mul m1 m = monomial_mul m2 m <=> m1 = m2`,
  MONOMIAL_TAC);;

let MONOMIAL_DIVIDES_REFL = prove
 (`!m:V->num. monomial_divides m m`,
  MONOMIAL_TAC);;

let MONOMIAL_DIVIDES_TRANS = prove
 (`!m1 m2 m3:V->num.
        monomial_divides m1 m2 /\ monomial_divides m2 m3
        ==> monomial_divides m1 m3`,
  MONOMIAL_TAC);;

let MONOMIAL_DIVIDES_ANTISYM = prove
 (`!m1 m2:V->num.
        monomial_divides m1 m2 /\ monomial_divides m2 m1 <=> m1 = m2`,
  MONOMIAL_TAC);;

let MONOMIAL_DIVIDES_LMUL = prove
 (`!d m1 m2:V->num.
        monomial_divides d m2 ==> monomial_divides d (monomial_mul m1 m2)`,
  MONOMIAL_TAC);;

let MONOMIAL_DIVIDES_RMUL = prove
 (`!d m1 m2:V->num.
        monomial_divides d m1 ==> monomial_divides d (monomial_mul m1 m2)`,
  MONOMIAL_TAC);;

let MONOMIAL_DIV_LMUL_EQ = prove
 (`!m1 m2:V->num.
        monomial_mul m2 (monomial_div m1 m2) = m1 <=> monomial_divides m2 m1`,
  MONOMIAL_TAC);;

let MONOMIAL_DIV_LMUL = prove
 (`!m1 m2:V->num.
        monomial_divides m2 m1 ==> monomial_mul m2 (monomial_div m1 m2) = m1`,
  MONOMIAL_TAC);;

let MONOMIAL_DIV_RMUL_EQ = prove
 (`!m1 m2:V->num.
        monomial_mul (monomial_div m1 m2) m2 = m1 <=> monomial_divides m2 m1`,
  MONOMIAL_TAC);;

let MONOMIAL_DIV_RMUL = prove
 (`!m1 m2:V->num.
        monomial_divides m2 m1 ==> monomial_mul (monomial_div m1 m2) m2 = m1`,
  MONOMIAL_TAC);;

let MONOMIAL_VAR_DIVIDES = prove
 (`!m v:V. monomial_divides (monomial_var v) m <=> v IN monomial_vars m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[monomial_divides; monomial_var] THEN
  REWRITE_TAC[monomial_vars; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `v:V`) THEN REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let MONOMIAL_VARS_DIVISOR = prove
 (`!d m:V->num.
        monomial_divides d m ==> monomial_vars d SUBSET monomial_vars m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[monomial_divides; monomial_vars] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN ARITH_TAC);;

let MONOMIAL_FINITE_DIVISORS = prove
 (`!m:V->num. FINITE {d | monomial_divides d m} <=> FINITE(monomial_vars m)`,
  GEN_TAC THEN EQ_TAC THENL
   [MP_TAC(ISPECL
     [`monomial_var:V->V->num`; `monomial_vars m:V->bool`]
      FINITE_IMAGE_INJ_EQ) THEN
    SIMP_TAC[MONOMIAL_VAR_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; monomial_vars; IN_ELIM_THM] THEN
    REWRITE_TAC[monomial_divides; monomial_var] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[monomial_vars] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `cartesian_product UNIV (\i:V. 0..m i)` THEN
    REWRITE_TAC[FINITE_CARTESIAN_PRODUCT; FINITE_NUMSEG; IN_UNIV] THEN
     REWRITE_TAC[SUBSET; monomial_divides; IN_CARTESIAN_PRODUCT] THEN
     SIMP_TAC[EXTENSIONAL_UNIV; IN_UNIV; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
     DISJ2_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM; IN_SING] THEN
     MESON_TAC[LE]]);;

let MONOMIAL_FINITE_DIVISORPAIRS = prove
 (`!m:V->num. FINITE {(m1,m2) | monomial_mul m1 m2 = m} <=>
              FINITE(monomial_vars m)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MONOMIAL_FINITE_DIVISORS] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o ISPEC `FST:(V->num)#(V->num)->V->num` o
        MATCH_MP FINITE_IMAGE) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `n:V->num` THEN REWRITE_TAC[monomial_mul; monomial_divides] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC
     [`n:V->num`; `\v. (m:V->num) v - n v`] THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; ARITH_RULE `n + m - n:num = m <=> n <= m`];
    DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{d:V->num | monomial_divides d m} CROSS {d | monomial_divides d m}` THEN
    ASM_REWRITE_TAC[FINITE_CROSS_EQ] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_CROSS; IN_ELIM_THM] THEN
    MESON_TAC[MONOMIAL_DIVIDES_LMUL; MONOMIAL_DIVIDES_RMUL;
              MONOMIAL_DIVIDES_REFL]]);;

let MONOMIAL_INDUCT = prove
 (`!s (P:(V->num)->bool).
        P monomial_1 /\
        (!m v. monomial s m /\ P m /\ v IN s
               ==> P(monomial_mul (monomial_var v) m))
        ==> !m. monomial s m ==> P m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d m:V->num. monomial s m /\ monomial_deg m = d ==> P m`
  MP_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MONOMIAL_DEG_EQ_0]; ALL_TAC] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  X_GEN_TAC `m:V->num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(monomial_vars(m:V->num) = {})` MP_TAC THENL
   [ASM_MESON_TAC[MONOMIAL_VARS_EQ_EMPTY; MONOMIAL_DEG_1; NOT_SUC];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `v:V` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
   SPECL [`monomial_div m (monomial_var(v:V))`; `v:V`]) THEN
  ASM_SIMP_TAC[MONOMIAL_DIV_LMUL; MONOMIAL_VAR_DIVIDES] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MONOMIAL_DIVISOR; MONOMIAL_DIV_DIVIDES];
    FIRST_X_ASSUM MATCH_MP_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[monomial]) THEN ASM SET_TAC[]] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[MONOMIAL_DIVISOR; MONOMIAL_DIV_DIVIDES];
    GEN_REWRITE_TAC I [GSYM SUC_INJ]] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN TRANS_TAC EQ_TRANS
   `monomial_deg(monomial_mul (monomial_var v)
                              (monomial_div m (monomial_var v)):V->num)` THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[MONOMIAL_DIV_LMUL; MONOMIAL_VAR_DIVIDES]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MONOMIAL_DEG_MUL o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MONOMIAL; MONOMIAL_VAR; IN_UNIV] THEN
    MATCH_MP_TAC MONOMIAL_DIV THEN ASM_MESON_TAC[MONOMIAL_UNIV];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MONOMIAL_DEG_VAR] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* General power series / polynomial sets and operations.                    *)
(*                                                                           *)
(* For the operations we use the name "poly", but they don't care about the  *)
(* underlying variable support sets, which are always going to be preserved. *)
(* The idea is they can be used for any kind of polynomials or power series. *)
(* There is also no inherent cardinality restriction on the "variables".     *)
(* ------------------------------------------------------------------------- *)

let ring_powerseries = new_definition
 `ring_powerseries r p <=>
        (!m. p m IN ring_carrier r) /\
        !m. INFINITE(monomial_vars m) ==> p m = ring_0 r`;;

let ring_polynomial = new_definition
 `ring_polynomial r p <=>
        ring_powerseries r p /\ FINITE {m | ~(p m = ring_0 r)}`;;

let RING_POLYNOMIAL_IMP_POWERSERIES = prove
 (`!r (p:(V->num)->A). ring_polynomial r p ==> ring_powerseries r p`,
  SIMP_TAC[ring_polynomial]);;

let poly_vars = new_definition
 `poly_vars r p = UNIONS { monomial_vars m | ~(p m = ring_0 r)}`;;

let poly_const = new_definition
 `poly_const (r:A ring) (c:A) =
        \m:V->num. if m = monomial_1 then c else ring_0 r`;;

let poly_0 = new_definition
 `poly_0 (r:A ring) = poly_const r (ring_0 r)`;;

let poly_1 = new_definition
 `poly_1 (r:A ring) = poly_const r (ring_1 r)`;;

let poly_neg = new_definition
 `poly_neg (r:A ring) p = \m:V->num. ring_neg r (p m)`;;

let poly_add = new_definition
 `poly_add (r:A ring) p1 p2 =
        \m:V->num. ring_add r (p1 m) (p2 m)`;;

let poly_mul = new_definition
 `poly_mul (r:A ring) p1 p2 =
        \m:V->num. ring_sum r {(m1,m2) | monomial_mul m1 m2 = m}
                              (\(m1,m2). ring_mul r (p1 m1) (p2 m2))`;;

let poly_var = new_definition
 `poly_var (r:A ring) (v:V) =
        \m:V->num. if m = monomial_var v then ring_1 r else ring_0 r`;;

let POLY_CONST_0 = prove
 (`!r:A ring. poly_const r (ring_0 r) = \x. ring_0 r`,
  REWRITE_TAC[poly_const; COND_ID]);;

let RING_POWERSERIES_CONST = prove
 (`!r c. ring_powerseries r (poly_const r c :(V->num)->A) <=>
         c IN ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_powerseries; poly_const] THEN
  REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  SIMP_TAC[RING_0; MONOMIAL_VARS_1; INFINITE; FINITE_EMPTY; COND_ID] THEN
  MESON_TAC[]);;

let RING_POWERSERIES_VAR = prove
 (`!r v. ring_powerseries r (poly_var r v:(V->num)->A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_powerseries; poly_var] THEN
  REWRITE_TAC[COND_RATOR; COND_RAND] THEN
  SIMP_TAC[RING_0; RING_1; MONOMIAL_VARS_VAR; INFINITE; FINITE_SING] THEN
  REWRITE_TAC[COND_ID]);;

let RING_POWERSERIES_0 = prove
 (`!r. ring_powerseries r (poly_0 r:(V->num)->A)`,
  REWRITE_TAC[poly_0; RING_POWERSERIES_CONST; RING_0]);;

let RING_POWERSERIES_1 = prove
 (`!r. ring_powerseries r (poly_1 r:(V->num)->A)`,
  REWRITE_TAC[poly_1; RING_POWERSERIES_CONST; RING_1]);;

let RING_POWERSERIES_NEG = prove
 (`!r (p:(V->num)->A).
        ring_powerseries r p ==> ring_powerseries r (poly_neg r p)`,
  SIMP_TAC[ring_powerseries; poly_neg; RING_NEG; RING_NEG_0]);;

let RING_POWERSERIES_ADD = prove
 (`!r p1 (p2:(V->num)->A).
        ring_powerseries r p1 /\ ring_powerseries r p2
        ==> ring_powerseries r (poly_add r p1 p2)`,
  SIMP_TAC[ring_powerseries; poly_add; RING_ADD; RING_0; RING_ADD_LZERO]);;

let RING_POWERSERIES_MUL = prove
 (`!r p1 (p2:(V->num)->A).
        ring_powerseries r p1 /\ ring_powerseries r p2
        ==> ring_powerseries r (poly_mul r p1 p2)`,
  SIMP_TAC[ring_powerseries; poly_mul; RING_SUM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:V->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN(K ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE [MONOMIAL_VARS_MUL; INFINITE; FINITE_UNION]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE [GSYM INFINITE; DE_MORGAN_THM]) THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO]);;

let RING_POLYNOMIAL_CONST = prove
 (`!r c. ring_polynomial r (poly_const r c :(V->num)->A) <=>
         c IN ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_polynomial; RING_POWERSERIES_CONST] THEN
  MATCH_MP_TAC(TAUT `q ==> (p /\ q <=> p)`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{(monomial_1:V->num)}` THEN
  REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
  REWRITE_TAC[poly_const] THEN MESON_TAC[]);;

let RING_POLYNOMIAL_VAR = prove
 (`!r v. ring_polynomial r (poly_var r v:(V->num)->A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_polynomial; RING_POWERSERIES_VAR] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{(monomial_var v:V->num)}` THEN
  REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
  REWRITE_TAC[poly_var] THEN MESON_TAC[]);;

let RING_POLYNOMIAL_0 = prove
 (`!r. ring_polynomial r (poly_0 r:(V->num)->A)`,
  REWRITE_TAC[poly_0; RING_POLYNOMIAL_CONST; RING_0]);;

let RING_POLYNOMIAL_1 = prove
 (`!r. ring_polynomial r (poly_1 r:(V->num)->A)`,
  REWRITE_TAC[poly_1; RING_POLYNOMIAL_CONST; RING_1]);;

let RING_POLYNOMIAL_NEG = prove
 (`!r (p:(V->num)->A).
        ring_polynomial r p ==> ring_polynomial r (poly_neg r p)`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_polynomial; RING_POWERSERIES_NEG] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM] THEN
  SIMP_TAC[poly_neg; RING_NEG_0]);;

let RING_POLYNOMIAL_ADD = prove
 (`!r p1 (p2:(V->num)->A).
        ring_polynomial r p1 /\ ring_polynomial r p2
        ==> ring_polynomial r (poly_add r p1 p2)`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_polynomial; RING_POWERSERIES_ADD] THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o CONJUNCT2)) THEN
  REWRITE_TAC[GSYM FINITE_UNION; IMP_IMP] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_UNION; GSYM DE_MORGAN_THM; IN_ELIM_THM;
              CONTRAPOS_THM] THEN
  SIMP_TAC[poly_add; RING_0; RING_ADD_LZERO]);;

let RING_POLYNOMIAL_MUL = prove
 (`!r p1 (p2:(V->num)->A).
        ring_polynomial r p1 /\ ring_polynomial r p2
        ==> ring_polynomial r (poly_mul r p1 p2)`,
  REPEAT GEN_TAC THEN SIMP_TAC[ring_polynomial; RING_POWERSERIES_MUL] THEN
  DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[poly_mul] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{ monomial_mul m1 m2 |
                m1 IN {m | ~((p1:(V->num)->A) m = ring_0 r)} /\
                m2 IN {m | ~((p2:(V->num)->A) m = ring_0 r)}}` THEN
  ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT] THEN
  REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN X_GEN_TAC `m:V->num` THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`m1:V->num`; `m2:V->num`] THEN DISCH_TAC THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m1:V->num`; `m2:V->num`]) THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_powerseries]) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO]);;

let POLY_ADD_SYM = prove
 (`!r p1 (p2:(V->num)->A).
        ring_powerseries r p1 /\ ring_powerseries r p2
        ==> poly_add r p1 p2 = poly_add r p2 p1`,
  REWRITE_TAC[ring_powerseries] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_add] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN RING_TAC);;

let POLY_ADD_ASSOC = prove
 (`!r p1 p2 (p3:(V->num)->A).
      ring_powerseries r p1 /\
      ring_powerseries r p2 /\
      ring_powerseries r p3
      ==> poly_add r p1 (poly_add r p2 p3) = poly_add r (poly_add r p1 p2) p3`,
  REWRITE_TAC[ring_powerseries] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_add] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN RING_TAC);;

let POLY_ADD_LZERO = prove
 (`!r (p:(V->num)->A).
        ring_powerseries r p
        ==> poly_add r (poly_0 r) p = p`,
  REWRITE_TAC[ring_powerseries] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_add; poly_0; POLY_CONST_0] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN RING_TAC);;

let POLY_ADD_LNEG = prove
 (`!r (p:(V->num)->A).
        ring_powerseries r p
        ==> poly_add r (poly_neg r p) p = poly_0 r`,
  REWRITE_TAC[ring_powerseries] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[poly_add; poly_neg; poly_0; POLY_CONST_0] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN RING_TAC);;

let POLY_MUL_SYM = prove
 (`!r p1 (p2:(V->num)->A).
        ring_powerseries r p1 /\ ring_powerseries r p2
        ==> poly_mul r p1 p2 = poly_mul r p2 p1`,
  REWRITE_TAC[ring_powerseries] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_mul] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN
  MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
  REPEAT(EXISTS_TAC `\(m:V->num,m':V->num). (m',m)`) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN SIMP_TAC[] THEN
  CONJ_TAC THEN REPEAT(DISCH_THEN(K ALL_TAC)) THEN
  REPEAT GEN_TAC THENL [ALL_TAC; DISCH_TAC THEN RING_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MONOMIAL_MUL_SYM] THEN
  SET_TAC[]);;

let POLY_ADD_LDISTRIB = prove
 (`!r p1 p2 (p3:(V->num)->A).
      ring_powerseries r p1 /\
      ring_powerseries r p2 /\
      ring_powerseries r p3
      ==> poly_mul r p1 (poly_add r p2 p3) =
          poly_add r (poly_mul r p1 p2) (poly_mul r p1 p3)`,
  REWRITE_TAC[ring_powerseries] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_add; poly_vars; poly_mul] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN
  REWRITE_TAC[] THEN ASM_CASES_TAC `FINITE(monomial_vars(m:V->num))` THENL
   [ASM_SIMP_TAC[GSYM RING_SUM_ADD; MONOMIAL_FINITE_DIVISORPAIRS;
                 RING_MUL; FORALL_IN_GSPEC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN RING_TAC;
    MATCH_MP_TAC(MESON[RING_ADD_LZERO; RING_ADD_RZERO; RING_0]
     `x = ring_0 r /\ y = ring_0 r /\ z = ring_0 r
      ==> z = ring_add r x y`) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`m1:V->num`; `m2:V->num`] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN(K ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE [MONOMIAL_VARS_MUL; FINITE_UNION]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE [GSYM INFINITE; DE_MORGAN_THM]) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO;
                 RING_ADD_LZERO; RING_0; RING_ADD]]);;

let POLY_MUL_LID = prove
 (`!r (p:(V->num)->A).
        ring_powerseries r p
        ==> poly_mul r (poly_1 r) p = p`,
  REWRITE_TAC[ring_powerseries] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_mul; poly_1; poly_const] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  ONCE_REWRITE_TAC[COND_RATOR] THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_LID] THEN
  MATCH_MP_TAC(MESON[]
   `!t. ring_sum r t f = a /\ ring_sum r s f = ring_sum r t f
        ==> ring_sum r s f = a`) THEN
  EXISTS_TAC `{(monomial_1:V->num,m:V->num)}` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[RING_SUM_SING]; ALL_TAC] THEN
  MATCH_MP_TAC RING_SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
  REWRITE_TAC[IN_SING; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN
  MESON_TAC[MONOMIAL_MUL_LID]);;

let POLY_MUL_ASSOC = prove
 (`!r p1 p2 (p3:(V->num)->A).
      ring_powerseries r p1 /\ ring_powerseries r p2 /\ ring_powerseries r p3
      ==> poly_mul r p1 (poly_mul r p2 p3) = poly_mul r (poly_mul r p1 p2) p3`,
  let lemma = prove
   (`!r p1 p2 (p3:(V->num)->A).
      ring_powerseries r p1 /\ ring_powerseries r p2 /\ ring_powerseries r p3
      ==> poly_mul r p1 (poly_mul r p2 p3) =
          \m. ring_sum r
               {(m1,m2,m3) | monomial_mul m1 (monomial_mul m2 m3) = m}
               (\(m1,m2,m3). ring_mul r (p1 m1) (ring_mul r (p2 m2) (p3 m3)))`,
    REWRITE_TAC[ring_powerseries] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[poly_mul] THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `FINITE(monomial_vars m:V->bool)` THENL
     [ALL_TAC;
      MATCH_MP_TAC(MESON[]
       `ring_sum r s f = ring_0 r /\ ring_sum r t g = ring_0 r
        ==> ring_sum r s f = ring_sum r t g`) THEN
      CONJ_TAC THEN REPLICATE_TAC 2
       (MATCH_MP_TAC RING_SUM_EQ_0 THEN
        REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN REPEAT GEN_TAC THEN
        DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN(K ALL_TAC) THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [MONOMIAL_VARS_MUL; INFINITE; FINITE_UNION]) THEN
        RULE_ASSUM_TAC(REWRITE_RULE [GSYM INFINITE; DE_MORGAN_THM]) THEN
        FIRST_X_ASSUM DISJ_CASES_TAC THEN
        ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO; RING_MUL; RING_SUM] THEN
        MATCH_MP_TAC(MESON[RING_MUL_RZERO]
         `x IN ring_carrier r /\ y = ring_0 r
          ==> ring_mul r x y = ring_0 r`) THEN
        ASM_REWRITE_TAC[] THEN TRY(FIRST_X_ASSUM DISJ_CASES_TAC) THEN
        ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO])] THEN
    MP_TAC(ISPECL
     [`r:A ring`;
      `{m1,m2 | monomial_mul m1 m2:V->num = m}`;
      `\(m1:V->num,m). {m2,m3 | monomial_mul m2 m3:V->num = m}`;
      `\(m1:V->num,m:V->num) (m2:V->num,m3:V->num).
          ring_mul (r:A ring) (p1 m1)
                   (ring_mul r (p2 m2) (p3 m3))`]
     RING_SUM_SUM_PRODUCT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      ASM_REWRITE_TAC[MONOMIAL_FINITE_DIVISORPAIRS] THEN
      ASM_SIMP_TAC[RING_MUL] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MONOMIAL_VARS_MUL; FINITE_UNION]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_IMP] THEN
    BINOP_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`m1:V->num`; `m2:V->num`] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MONOMIAL_VARS_MUL; FINITE_UNION]) THEN
      ASM_SIMP_TAC[GSYM RING_SUM_LMUL; RING_MUL; FORALL_IN_GSPEC;
                   MONOMIAL_FINITE_DIVISORPAIRS] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC];
      MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES] THEN
    MAP_EVERY EXISTS_TAC
     [`\((m1:V->num,m2:V->num),(m3:V->num,m4:V->num)). (m1,m3,m4)`;
      `\(m1:V->num,m3:V->num,m4:V->num). (m1,monomial_mul m3 m4),(m3,m4)`] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_SIMP_TAC[RING_MUL] THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_MUL_SYM o rand o snd) THEN
  ASM_SIMP_TAC[RING_POWERSERIES_MUL] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[lemma] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `\(m1:V->num,m2:V->num,m3:V->num). m3,m1,m2` THEN
  EXISTS_TAC `\(m3:V->num,m1:V->num,m2:V->num). m1,m2,m3` THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_powerseries]) THEN
  ASM_SIMP_TAC[RING_MUL; IN_ELIM_TRIPLE_THM] THEN
  REWRITE_TAC[MONOMIAL_MUL_AC] THEN SIMP_TAC[] THEN
  REPEAT STRIP_TAC THEN RING_TAC);;

let POLY_VARS_CONST = prove
 (`!(r:A ring) c. poly_vars r (poly_const r c) = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poly_vars; poly_const] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[MESON[] `~(if p then q else T) <=> p /\ ~q`] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  ASM_CASES_TAC `c:A = ring_0 r` THEN
  ASM_REWRITE_TAC[SING_GSPEC; EMPTY_GSPEC; IMAGE_CLAUSES] THEN
  REWRITE_TAC[UNIONS_1; UNIONS_0; MONOMIAL_VARS_1]);;

let POLY_VARS_0 = prove
 (`!r:A ring. poly_vars r (poly_0 r) = {}`,
  REWRITE_TAC[poly_0; POLY_VARS_CONST]);;

let POLY_VARS_1 = prove
 (`!r:A ring. poly_vars r (poly_1 r) = {}`,
  REWRITE_TAC[poly_1; POLY_VARS_CONST]);;

let POLY_VARS_VAR = prove
 (`!(r:A ring) (v:V).
        poly_vars r (poly_var r v) =
        if trivial_ring r then {} else {v}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poly_vars; poly_var; TRIVIAL_RING_10] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  ASM_REWRITE_TAC[MESON[] `~(if p then q else T) <=> p /\ ~q`] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  ASM_REWRITE_TAC[SING_GSPEC; EMPTY_GSPEC; IMAGE_CLAUSES] THEN
  REWRITE_TAC[UNIONS_1; UNIONS_0; MONOMIAL_VARS_1; MONOMIAL_VARS_VAR]);;

let POLY_VARS_NEG = prove
 (`!r (p:(V->num)->A).
        ring_powerseries r p ==> poly_vars r (poly_neg r p) = poly_vars r p`,
  REWRITE_TAC[ring_powerseries; poly_vars; poly_neg] THEN
  SIMP_TAC[RING_NEG_EQ_0]);;

let POLY_VARS_ADD = prove
 (`!r (p1:(V->num)->A) (p2:(V->num)->A).
        ring_powerseries r p1 /\ ring_powerseries r p2
        ==> poly_vars r (poly_add r p1 p2) SUBSET
            poly_vars r p1 UNION poly_vars r p2`,
  REWRITE_TAC[ring_powerseries; poly_vars; poly_add; GSYM UNIONS_UNION] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[GSYM IMAGE_UNION] THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN RING_TAC);;

let POLY_VARS_MUL = prove
 (`!r (p1:(V->num)->A) (p2:(V->num)->A).
        ring_powerseries r p1 /\ ring_powerseries r p2
        ==> poly_vars r (poly_mul r p1 p2) SUBSET
            poly_vars r p1 UNION poly_vars r p2`,
  REWRITE_TAC[ring_powerseries; poly_vars; poly_mul] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; UNIONS_GSPEC] THEN
  X_GEN_TAC `x:V` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:V->num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] RING_SUM_EQ_0)) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(MP_TAC o MATCH_MP (RING_RULE
   `~(ring_mul r x y = ring_0 r)
    ==> x IN ring_carrier r /\ y IN ring_carrier r
        ==> ~(x = ring_0 r) /\ ~(y = ring_0 r)`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [MONOMIAL_VARS_MUL]) THEN
  ASM SET_TAC[]);;

let FINITE_POLYNOMIAL_VARS = prove
 (`!r (p:(V->num)->A). ring_polynomial r p ==> FINITE(poly_vars r p)`,
  REWRITE_TAC[ring_polynomial; ring_powerseries; INFINITE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_vars; FINITE_UNIONS] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Actual polynomial and power series rings.                                 *)
(* ------------------------------------------------------------------------- *)

let powser_ring = new_definition
 `powser_ring (r:A ring) (s:V->bool) =
        ring({p | ring_powerseries r p /\ poly_vars r p SUBSET s},
             poly_0 r,poly_1 r,poly_neg r,poly_add r,poly_mul r)`;;

let poly_ring = new_definition
 `poly_ring (r:A ring) (s:V->bool) =
        ring({p | ring_polynomial r p /\ poly_vars r p SUBSET s},
             poly_0 r,poly_1 r,poly_neg r,poly_add r,poly_mul r)`;;

let POWSER_RING = prove
 (`(!(r:A ring) (s:V->bool).
        ring_carrier(powser_ring r s) =
        {p | ring_powerseries r p /\ poly_vars r p SUBSET s}) /\
   (!(r:A ring) (s:V->bool). ring_0(powser_ring r s) = poly_0 r) /\
   (!(r:A ring) (s:V->bool). ring_1(powser_ring r s) = poly_1 r) /\
   (!(r:A ring) (s:V->bool). ring_neg(powser_ring r s) = poly_neg r) /\
   (!(r:A ring) (s:V->bool). ring_add(powser_ring r s) = poly_add r) /\
   (!(r:A ring) (s:V->bool). ring_mul(powser_ring r s) = poly_mul r)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  PURE_REWRITE_TAC
   [GSYM PAIR_EQ; ring_carrier; ring_0; ring_1; ring_neg; ring_add; ring_mul;
    BETA_THM; PAIR] THEN
  PURE_REWRITE_TAC[powser_ring; GSYM(CONJUNCT2 ring_tybij)] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[RING_POWERSERIES_0; POLY_VARS_0; EMPTY_SUBSET;
              RING_POWERSERIES_1; POLY_VARS_1] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[RING_POWERSERIES_NEG; POLY_VARS_NEG];
    SIMP_TAC[RING_POWERSERIES_ADD] THEN REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_VARS_ADD o lhand o snd) THEN
    ASM SET_TAC[];
    SIMP_TAC[RING_POWERSERIES_MUL] THEN REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_VARS_MUL o lhand o snd) THEN
    ASM SET_TAC[];
    MESON_TAC[POLY_ADD_SYM];
    MESON_TAC[POLY_ADD_ASSOC];
    MESON_TAC[POLY_ADD_LZERO];
    MESON_TAC[POLY_ADD_LNEG];
    MESON_TAC[POLY_MUL_SYM];
    MESON_TAC[POLY_MUL_ASSOC];
    MESON_TAC[POLY_MUL_LID];
    MESON_TAC[POLY_ADD_LDISTRIB]]);;

let POLY_RING_SUBRING_OF_POWSER_RING = prove
 (`!(r:A ring) (s:V->bool).
        {p | ring_polynomial r p /\ poly_vars r p SUBSET s}
        subring_of powser_ring r s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subring_of; POWSER_RING; IN_ELIM_THM] THEN
  REWRITE_TAC[RING_POLYNOMIAL_0; POLY_VARS_0; EMPTY_SUBSET;
              RING_POLYNOMIAL_1; POLY_VARS_1] THEN
  GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
  SIMP_TAC[IN_ELIM_THM; RING_POLYNOMIAL_IMP_POWERSERIES] THEN
  SIMP_TAC[RING_POLYNOMIAL_NEG; RING_POLYNOMIAL_ADD; RING_POLYNOMIAL_MUL] THEN
  SIMP_TAC[POLY_VARS_NEG; ring_polynomial] THEN REPEAT STRIP_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) POLY_VARS_ADD o lhand o snd);
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_VARS_MUL o lhand o snd)] THEN
  ASM SET_TAC[]);;

let POLY_RING_AS_SUBRING = prove
 (`!(r:A ring) (s:V->bool).
        poly_ring r s =
        subring_generated (powser_ring r s)
                          {p | ring_polynomial r p /\ poly_vars r p SUBSET s}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[poly_ring; subring_generated; CONJUNCT2 POWSER_RING] THEN
  AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[GSYM(CONJUNCT1 SUBRING_GENERATED)] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN
  REWRITE_TAC[POLY_RING_SUBRING_OF_POWSER_RING]);;

let POLY_RING_AS_SUBRING_ALT = prove
 (`!(r:A ring) (s:V->bool).
        poly_ring r s =
        subring_generated (powser_ring r s) {p | ring_polynomial r p}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT] THEN
  REWRITE_TAC[POLY_RING_AS_SUBRING] THEN
  AP_TERM_TAC THEN REWRITE_TAC[POWSER_RING; ring_polynomial] THEN SET_TAC[]);;

let POLY_RING_AS_SUBRING_FINITE = prove
 (`!(r:A ring) (s:V->bool).
           poly_ring r s =
           subring_generated (powser_ring r s)
                             {p | FINITE {m | ~(p m = ring_0 r)}}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[POLY_RING_AS_SUBRING_ALT] THEN
  ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT] THEN AP_TERM_TAC THEN
  REWRITE_TAC[POWSER_RING; ring_polynomial] THEN SET_TAC[]);;

let POLY_CARRIER_SUBRING_OF_POWSER_RING = prove
 (`!(r:A ring) (s:V->bool).
        ring_carrier(poly_ring r s) subring_of powser_ring r s`,
  REWRITE_TAC[SUBRING_SUBRING_GENERATED; POLY_RING_AS_SUBRING]);;

let RING_MONOMORPHISM_POLY_POWSER = prove
 (`!r s:A->bool. ring_monomorphism(poly_ring r s,powser_ring r s) (\x. x)`,
  REWRITE_TAC[POLY_RING_AS_SUBRING; RING_MONOMORPHISM_INCLUSION]);;

let POLY_RING = prove
 (`(!(r:A ring) (s:V->bool).
        ring_carrier(poly_ring r s) =
        {p | ring_polynomial r p /\ poly_vars r p SUBSET s}) /\
   (!(r:A ring) (s:V->bool). ring_0(poly_ring r s) = poly_0 r) /\
   (!(r:A ring) (s:V->bool). ring_1(poly_ring r s) = poly_1 r) /\
   (!(r:A ring) (s:V->bool). ring_neg(poly_ring r s) = poly_neg r) /\
   (!(r:A ring) (s:V->bool). ring_add(poly_ring r s) = poly_add r) /\
   (!(r:A ring) (s:V->bool). ring_mul(poly_ring r s) = poly_mul r)`,
  REWRITE_TAC[POLY_RING_AS_SUBRING] THEN
  SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING;
           POLY_RING_SUBRING_OF_POWSER_RING] THEN
  REWRITE_TAC[SUBRING_GENERATED] THEN REWRITE_TAC[POWSER_RING]);;

let FINITE_POLY_VARS = prove
 (`!(r:A ring) (s:V->bool) p.
        p IN ring_carrier(poly_ring r s) ==> FINITE(poly_vars r p)`,
  SIMP_TAC[FINITE_POLYNOMIAL_VARS; POLY_RING; IN_ELIM_THM]);;

let RING_CARRIER_POLY_RING_FINITE = prove
 (`!(r:A ring) (s:V->bool).
           ring_carrier(poly_ring r s) =
           ring_carrier(powser_ring r s) INTER
           {p | FINITE {m | ~(p m = ring_0 r)}}`,
  REWRITE_TAC[POLY_RING; POWSER_RING; ring_polynomial] THEN SET_TAC[]);;

let POLY_VAR = prove
 (`!(r:A ring) (s:V->bool) i.
        poly_var r i IN ring_carrier(poly_ring r s) <=>
        trivial_ring r \/ i IN s`,
  REWRITE_TAC[POLY_RING; IN_ELIM_THM; RING_POLYNOMIAL_VAR] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[POLY_VARS_VAR] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET; SING_SUBSET]);;

let POLY_CONST = prove
 (`!(r:A ring) (s:V->bool) c.
        poly_const r c IN ring_carrier(poly_ring r s) <=>
        c IN ring_carrier r`,
  REWRITE_TAC[POLY_RING; IN_ELIM_THM; RING_POLYNOMIAL_CONST] THEN
  REWRITE_TAC[POLY_VARS_CONST; EMPTY_SUBSET]);;

let POWSER_VAR = prove
 (`!(r:A ring) (s:V->bool) i.
        poly_var r i IN ring_carrier(powser_ring r s) <=>
        trivial_ring r \/ i IN s`,
  REWRITE_TAC[POWSER_RING; IN_ELIM_THM; RING_POWERSERIES_VAR] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[POLY_VARS_VAR] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET; SING_SUBSET]);;

let POWSER_CONST = prove
 (`!(r:A ring) (s:V->bool) c.
        poly_const r c IN ring_carrier(powser_ring r s) <=>
        c IN ring_carrier r`,
  REWRITE_TAC[POWSER_RING; IN_ELIM_THM; RING_POWERSERIES_CONST] THEN
  REWRITE_TAC[POLY_VARS_CONST; EMPTY_SUBSET]);;

let POLY_CONST_NEG = prove
 (`!r x. poly_const r (ring_neg r x):(V->num)->A =
         poly_neg r (poly_const r x)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `m:V->num` THEN REWRITE_TAC[poly_const; poly_neg] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_NEG_0]);;

let POLY_CONST_ADD = prove
 (`!r x y.
        poly_const r (ring_add r x y):(V->num)->A =
        poly_add r (poly_const r x) (poly_const r y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `m:V->num` THEN REWRITE_TAC[poly_const; poly_add] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[RING_ADD_RZERO; RING_0]);;

let POLY_CONST_MUL = prove
 (`!r x y.
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> poly_const r (ring_mul r x y):(V->num)->A =
            poly_mul r (poly_const r x) (poly_const r y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `m:V->num` THEN REWRITE_TAC[poly_const; poly_mul] THEN
  ASM_SIMP_TAC[MESON[RING_0; RING_MUL_LZERO; RING_MUL_RZERO]
   `x IN ring_carrier r /\ y IN ring_carrier r
    ==> ring_mul r (if p then x else ring_0 r)
                    (if q then y else ring_0 r) =
        (if p /\ q then ring_mul r x y else ring_0 r)`] THEN
  ASM_REWRITE_TAC[GSYM PAIR_EQ; GSYM LAMBDA_PAIR_THM] THEN
  ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_PAIR_THM; RING_MUL] THEN
  REWRITE_TAC[MONOMIAL_MUL_LID] THEN MESON_TAC[]);;

let POLY_CONST_EQ = prove
 (`!r x y. poly_const r x :(V->num)->A = poly_const r y <=> x = y`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN
  REWRITE_TAC[poly_const] THEN MESON_TAC[]);;

let RING_HOMOMORPHISM_POLY_CONST = prove
 (`!(r:A ring) (s:V->bool).
        ring_homomorphism (r,poly_ring r s) (poly_const r)`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[POLY_CONST; POLY_CONST_NEG; POLY_CONST_ADD; POLY_CONST_MUL] THEN
  REWRITE_TAC[POLY_RING; poly_0; poly_1]);;

let RING_MONOMORPHISM_POLY_CONST = prove
 (`!(r:A ring) (s:V->bool).
        ring_monomorphism (r,poly_ring r s) (poly_const r)`,
  REWRITE_TAC[ring_monomorphism; RING_HOMOMORPHISM_POLY_CONST] THEN
  SIMP_TAC[POLY_CONST_EQ]);;

let RING_HOMOMORPHISM_POWSER_CONST = prove
 (`!(r:A ring) (s:V->bool).
        ring_homomorphism (r,powser_ring r s) (poly_const r)`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[POWSER_CONST; POLY_CONST_NEG; POLY_CONST_ADD; POLY_CONST_MUL] THEN
  REWRITE_TAC[POWSER_RING; poly_0; poly_1]);;

let RING_MONOMORPHISM_POWSER_CONST = prove
 (`!(r:A ring) (s:V->bool).
        ring_monomorphism (r,powser_ring r s) (poly_const r)`,
  REWRITE_TAC[ring_monomorphism; RING_HOMOMORPHISM_POWSER_CONST] THEN
  SIMP_TAC[POLY_CONST_EQ]);;

let POWSER_SUM = prove
 (`!(r:A ring) (s:V->bool) f (k:K->bool).
        FINITE k /\
        (!i. i IN k ==> f i IN ring_carrier(powser_ring r s))
        ==> ring_sum (powser_ring r s) k f = \m. ring_sum r k (\i. f i m)`,
  REPLICATE_TAC 3 GEN_TAC THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[POWSER_RING; poly_0; poly_add; POLY_CONST_0] THEN
  SIMP_TAC[ring_powerseries; IN_ELIM_THM]);;

let POLY_SUM = prove
 (`!(r:A ring) (s:V->bool) f (k:K->bool).
        FINITE k /\
        (!i. i IN k ==> f i IN ring_carrier(poly_ring r s))
        ==> ring_sum (poly_ring r s) k f = \m. ring_sum r k (\i. f i m)`,
  REPLICATE_TAC 3 GEN_TAC THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[POLY_RING; poly_0; poly_add; POLY_CONST_0] THEN
  SIMP_TAC[ring_polynomial; ring_powerseries; IN_ELIM_THM]);;

let POLY_RING_VAR_POW = prove
 (`!(r:A ring) (s:V->bool) i k.
        ring_pow (poly_ring r s) (poly_var r i) k =
        \m. if m = (\j. if j = i then k else 0)
            then ring_1 r else ring_0 r`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ring_pow; POLY_RING; poly_1; poly_const; COND_ID;
                  monomial_1; monomial_var; poly_var; poly_mul] THEN
  REWRITE_TAC[MESON
   [RING_MUL_LZERO; RING_MUL_RZERO; RING_MUL_LID;
    RING_MUL_RID; RING_0; RING_1]
   `ring_mul r (if p then ring_1 r else ring_0 r)
               (if q then ring_1 r else ring_0 r) =
    if p /\ q then ring_1 r else ring_0 r`] THEN
  REWRITE_TAC[GSYM PAIR_EQ; GSYM LAMBDA_PAIR_THM] THEN
  REWRITE_TAC[RING_SUM_DELTA; RING_1; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[monomial_mul] THEN ABS_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN AP_TERM_TAC THEN
  ABS_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let POLY_RING_PRODUCT_VAR_POW = prove
 (`!(r:A ring) (s:V->bool) m k.
        FINITE k /\ k SUBSET s
        ==> ring_product (poly_ring r s) k
                         (\i. ring_pow (poly_ring r s) (poly_var r i) (m i)) =
            \m'. if m' = (\i. if i IN k then m i else 0)
                 then ring_1 r else ring_0 r`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; FORALL_IN_INSERT; INSERT_SUBSET] THEN
  REWRITE_TAC[POLY_RING; NOT_IN_EMPTY; poly_1; poly_const; monomial_1] THEN
  MAP_EVERY X_GEN_TAC [`i:V`; `k:V->bool`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT `~p ==> p ==> q`)) THEN
    REWRITE_TAC[GSYM(CONJUNCT1 POLY_RING)] THEN MATCH_MP_TAC RING_POW THEN
    REWRITE_TAC[POLY_RING; IN_ELIM_THM; RING_POLYNOMIAL_VAR] THEN
    REWRITE_TAC[POLY_VARS_VAR] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_RING_VAR_POW; poly_mul; MESON
   [RING_MUL_LZERO; RING_MUL_RZERO; RING_MUL_LID;
    RING_MUL_RID; RING_0; RING_1]
   `ring_mul r (if p then ring_1 r else ring_0 r)
               (if q then ring_1 r else ring_0 r) =
    if p /\ q then ring_1 r else ring_0 r`] THEN
  REWRITE_TAC[GSYM PAIR_EQ; GSYM LAMBDA_PAIR_THM] THEN
  REWRITE_TAC[RING_SUM_DELTA; RING_1; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[monomial_mul] THEN ABS_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `j:V` THEN
  ASM_CASES_TAC `j:V = i` THEN ASM_REWRITE_TAC[IN_INSERT; ADD_CLAUSES]);;

let POLY_RING_PRODUCT_VAR = prove
 (`!(r:A ring) (s:V->bool) k.
        FINITE k /\ k SUBSET s
        ==> ring_product (poly_ring r s) k (poly_var r) =
            \m. if m = (\i. if i IN k then 1 else 0)
                then ring_1 r else ring_0 r`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`r:A ring`; `s:V->bool`; `\i:V. 1`; `k:V->bool`]
        POLY_RING_PRODUCT_VAR_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_PRODUCT_EQ THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[RING_POW_1; POLY_VAR]);;

let POLY_RING_EXPAND = prove
 (`!(r:A ring) (s:V->bool) p.
       p IN ring_carrier (poly_ring r s)
       ==> ring_sum (poly_ring r s) {m | ~(p m = ring_0 r)}
             (\m. ring_mul (poly_ring r s)
                   (poly_const r (p m))
                   (ring_product (poly_ring r s) (monomial_vars m)
                     (\i. ring_pow (poly_ring r s) (poly_var r i) (m i)))) =
           p`,
  let lemma = prove
   (`!(r:A ring) (s:V->bool) m.
          FINITE(monomial_vars m) /\ monomial_vars m SUBSET s
          ==> ring_product (poly_ring r s) (monomial_vars m)
                 (\i. ring_pow (poly_ring r s) (poly_var r i) (m i)) =
               \m'. if m' = m then ring_1 r else ring_0 r`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[POLY_RING_PRODUCT_VAR_POW] THEN
    REWRITE_TAC[monomial_vars; IN_ELIM_THM] THEN
    REWRITE_TAC[MESON[] `(if ~(m = 0) then m else 0) = m`] THEN
    REWRITE_TAC[ETA_AX]) in
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_SUM o lhand o snd) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE
     [POLY_RING; ring_polynomial; ring_powerseries; IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[RING_PRODUCT] THEN
    REWRITE_TAC[POLY_RING; IN_ELIM_THM; POLY_VARS_CONST; EMPTY_SUBSET] THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL_CONST];
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN
  REWRITE_TAC[] THEN TRANS_TAC EQ_TRANS
   `ring_sum r {m | ~((p:(V->num)->A) m = ring_0 r)}
               (\m'. ring_mul (poly_ring r s) (poly_const r (p m'))
                         (\m''. if m'' = m'
                                then ring_1 r else ring_0 r) (m:V->num))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `m':V->num` THEN DISCH_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC lemma THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [POLY_RING]) THEN
    REWRITE_TAC[IN_ELIM_THM; ring_polynomial; ring_powerseries] THEN
    REWRITE_TAC[INFINITE; GSYM monomial_vars; poly_vars; UNIONS_SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE
     [POLY_RING; IN_ELIM_THM; ring_polynomial; ring_powerseries]) THEN
    ASM_SIMP_TAC[poly_const; poly_mul; POLY_RING; MESON
     [RING_MUL_LZERO; RING_MUL_RZERO; RING_MUL_RID; RING_0; RING_1]
     `x IN ring_carrier r
      ==> ring_mul r (if p then x else ring_0 r)
                     (if q then ring_1 r else ring_0 r) =
           (if p /\ q then x else ring_0 r)`] THEN
    ASM_REWRITE_TAC[GSYM PAIR_EQ; GSYM LAMBDA_PAIR_THM] THEN
    ASM_SIMP_TAC[RING_SUM_DELTA; RING_1; IN_ELIM_PAIR_THM;
                 MONOMIAL_MUL_LID] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;

let POLY_RING_INDUCT = prove
 (`!(r:A ring) (s:V->bool) P.
        (!c. c IN ring_carrier r ==> P(poly_const r c)) /\
        (!i. i IN s ==> P(poly_var r i)) /\
        (!x y. P x /\ P y ==> P(ring_add (poly_ring r s) x y)) /\
        (!x y. P x /\ P y ==> P(ring_mul (poly_ring r s) x y))
        ==> !p. p IN ring_carrier(poly_ring r s) ==> P p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [POLY_RING]) THEN
  REWRITE_TAC[IN_ELIM_THM; ring_polynomial; ring_powerseries] THEN
  REWRITE_TAC[INFINITE; GSYM monomial_vars; poly_vars] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC RAND_CONV [SYM(MATCH_MP POLY_RING_EXPAND th)]) THEN
  MP_TAC(ASSUME `FINITE {m | ~((p:(V->num)->A) m = ring_0 r)}`) THEN
  SPEC_TAC(`{m | ~((p:(V->num)->A) m = ring_0 r)}`,`k:(V->num)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `ring_0 r:A`) THEN
    REWRITE_TAC[RING_0; poly_0; POLY_RING];
    MAP_EVERY X_GEN_TAC [`m:V->num`; `ms:(V->num)->bool`]] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(p:(V->num)->A) m = ring_0 r` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `ring_0 r:A`) THEN
    REWRITE_TAC[RING_0] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[GSYM poly_0] THEN
    SUBST1_TAC(MESON[POLY_RING]
     `poly_0 r:(V->num)->A = ring_0(poly_ring r s)`) THEN
    SIMP_TAC[RING_MUL_LZERO; RING_PRODUCT];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN `(monomial_vars m:V->bool) SUBSET s` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(monomial_vars m:V->bool)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`monomial_vars m:V->bool`,`l:V->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_PRODUCT_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EMPTY_SUBSET] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ring_1 r:A`) THEN
    REWRITE_TAC[RING_1; poly_1; POLY_RING];
    MAP_EVERY X_GEN_TAC [`i:V`; `ois:V->bool`]] THEN
  REWRITE_TAC[INSERT_SUBSET] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`(m:V->num) i`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ring_pow] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `ring_1 r:A`) THEN
    REWRITE_TAC[RING_1; poly_1; POLY_RING];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

let POLY_RING_INDUCT_STRONG = prove
 (`!(r:A ring) (s:V->bool) P.
        (!c. c IN ring_carrier r ==> P(poly_const r c)) /\
        (!i. i IN s ==> P(poly_var r i)) /\
        (!x y. x IN ring_carrier(poly_ring r s) /\
               y IN ring_carrier(poly_ring r s) /\
               P x /\ P y
               ==> P(ring_add (poly_ring r s) x y)) /\
        (!x y. x IN ring_carrier(poly_ring r s) /\
               y IN ring_carrier(poly_ring r s) /\
               P x /\ P y ==> P(ring_mul (poly_ring r s) x y))
        ==> !p. p IN ring_carrier(poly_ring r s) ==> P p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p /\ q`] THEN
  MATCH_MP_TAC POLY_RING_INDUCT THEN
  ASM_SIMP_TAC[POLY_CONST; POLY_VAR; RING_ADD; RING_MUL]);;

let POLY_RING_HOMOMORPHISM_UNIQUE = prove
 (`!(r:A ring) (r':B ring) (s:V->bool) f g.
        ring_homomorphism(poly_ring r s,r') f /\
        ring_homomorphism(poly_ring r s,r') g /\
        (!c. c IN ring_carrier r ==> f(poly_const r c) = g(poly_const r c)) /\
        (!i. i IN s ==> f(poly_var r i) = g(poly_var r i))
        ==> !p. p IN ring_carrier(poly_ring r s) ==> f p = g p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_homomorphism] THEN
  STRIP_TAC THEN MATCH_MP_TAC POLY_RING_INDUCT_STRONG THEN
  ASM_SIMP_TAC[]);;

let TRIVIAL_POWSER_RING = prove
 (`!(r:A ring) (s:V->bool). trivial_ring(powser_ring r s) <=> trivial_ring r`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
        TRIVIAL_RING_MONOMORPHIC_PREIMAGE) THEN
    MESON_TAC[RING_MONOMORPHISM_POWSER_CONST];
    SIMP_TAC[TRIVIAL_RING_10; FUN_EQ_THM; POWSER_RING;
             poly_0; poly_1; poly_const]]);;

let TRIVIAL_POLY_RING = prove
 (`!(r:A ring) (s:V->bool). trivial_ring(poly_ring r s) <=> trivial_ring r`,
  REWRITE_TAC[POLY_RING_AS_SUBRING; TRIVIAL_RING_SUBRING_GENERATED] THEN
  REWRITE_TAC[TRIVIAL_POWSER_RING]);;

let RING_CARRIER_POWSER_RING = prove
 (`!(r:A ring) (s:V->bool).
        ring_carrier(powser_ring r s) =
        {p | (!m. p m IN ring_carrier r) /\
             (!m. ~(monomial s m) ==> p m = ring_0 r)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[POWSER_RING] THEN
  REWRITE_TAC[ring_powerseries; INFINITE; poly_vars; UNIONS_SUBSET] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; monomial] THEN SET_TAC[]);;

let RING_CARRIER_POLY_RING = prove
 (`!(r:A ring) (s:V->bool).
        ring_carrier(poly_ring r s) =
        {p | (!m. p m IN ring_carrier r) /\
             FINITE {m | ~(p m = ring_0 r)} /\
             (!m. ~(monomial s m) ==> p m = ring_0 r)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[POLY_RING] THEN
  REWRITE_TAC[ring_powerseries; ring_polynomial; INFINITE; poly_vars;
              UNIONS_SUBSET; FORALL_IN_GSPEC; monomial] THEN
  SET_TAC[]);;

let POWSER_RING_EQ = prove
 (`!(r:A ring) (s:V->bool) p q.
        p IN ring_carrier(powser_ring r s) /\
        q IN ring_carrier(powser_ring r s)
        ==> (p = q <=> !m. monomial s m ==> p m = q m)`,
  REWRITE_TAC[RING_CARRIER_POWSER_RING; IN_ELIM_THM] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let POWSER_RING_EQ_IMP = prove
 (`!(r:A ring) (s:V->bool) p q.
        p IN ring_carrier(powser_ring r s) /\
        q IN ring_carrier(powser_ring r s) /\
        (!m. monomial s m ==> p m = q m)
        ==> p = q`,
  REWRITE_TAC[RING_CARRIER_POWSER_RING; IN_ELIM_THM] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let POLY_RING_EQ = prove
 (`!(r:A ring) (s:V->bool) p q.
        p IN ring_carrier(poly_ring r s) /\
        q IN ring_carrier(poly_ring r s)
        ==> (p = q <=> !m. monomial s m ==> p m = q m)`,
  REWRITE_TAC[RING_CARRIER_POLY_RING; IN_ELIM_THM] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let POLY_RING_EQ_IMP = prove
 (`!(r:A ring) (s:V->bool) p q.
        p IN ring_carrier(poly_ring r s) /\
        q IN ring_carrier(poly_ring r s) /\
        (!m. monomial s m ==> p m = q m)
        ==> p = q`,
  REWRITE_TAC[RING_CARRIER_POLY_RING; IN_ELIM_THM] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The extension of a homomorphism to one from a polynomial ring.            *)
(* ------------------------------------------------------------------------- *)

let poly_extend = new_definition
 `poly_extend (r,r') (h:A->B) (x:V->B) p =
        ring_sum r' {m | ~(p m = ring_0 r)}
                    (\m. ring_mul r' (h (p m))
                           (ring_product r' (monomial_vars m)
                                            (\i. ring_pow r' (x i) (m i))))`;;

let POLY_EXTEND = prove
 (`!r r' (h:A->B) p (x:V->B). poly_extend (r,r') h x p IN ring_carrier r'`,
  REWRITE_TAC[poly_extend; RING_SUM]);;

let POLY_EXTEND_SUPERSET = prove
 (`!s r r' (h:A->B) p (x:V->B).
        ring_homomorphism(r,r') h /\
        {m | ~(p m = ring_0 r)} SUBSET s
        ==> poly_extend (r,r') h x (p:(V->num)->A) =
            ring_sum r' s (\m. ring_mul r' (h (p m))
                                (ring_product r' (monomial_vars m)
                                         (\i. ring_pow r' (x i) (m i))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_extend] THEN
  REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_SUPERSET THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; RING_MUL_LZERO; RING_PRODUCT]);;

let POLY_EXTEND_CONST = prove
 (`!r r' (h:A->B) (x:V->B) c.
        ring_homomorphism(r,r') h /\ c IN ring_carrier r
        ==> poly_extend (r,r') h x (poly_const r c) = h c`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_extend; poly_const] THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[MESON[] `~(if p then q else T) <=> p /\ ~q`] THEN
  ASM_CASES_TAC `c:A = ring_0 r` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; RING_SUM_CLAUSES] THEN
  REWRITE_TAC[RING_SUM_SING; SING_GSPEC; MONOMIAL_VARS_1] THEN
  ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; RING_MUL_RID]);;

let POLY_EXTEND_0 = prove
 (`!r r' (h:A->B) (x:V->B).
        ring_homomorphism(r,r') h
        ==> poly_extend (r,r') h x (poly_0 r) = ring_0 r'`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[poly_0; POLY_EXTEND_CONST; RING_0] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[]);;

let POLY_EXTEND_1 = prove
 (`!r r' (h:A->B) (x:V->B).
        ring_homomorphism(r,r') h
        ==> poly_extend (r,r') h x (poly_1 r) = ring_1 r'`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[poly_1; POLY_EXTEND_CONST; RING_1] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_1 THEN ASM_REWRITE_TAC[]);;

let POLY_EXTEND_VAR = prove
 (`!r r' (h:A->B) (x:V->B) i.
        ring_homomorphism(r,r') h /\ x i IN ring_carrier r'
        ==> poly_extend (r,r') h x (poly_var r i) = x i`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `trivial_ring (r:A ring)` THENL
   [ASM_SIMP_TAC[RING_HOMOMORPHISM_FROM_TRIVIAL_RING] THEN
    REWRITE_TAC[trivial_ring] THEN MATCH_MP_TAC(SET_RULE
     `a IN s ==> (s = {z} /\ P) /\ b IN s ==> a = b`) THEN
    REWRITE_TAC[POLY_EXTEND];
    RULE_ASSUM_TAC(REWRITE_RULE[TRIVIAL_RING_10])] THEN
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_extend; poly_var] THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  ONCE_REWRITE_TAC[COND_RATOR] THEN
  ASM_REWRITE_TAC[MESON[] `~(if p then q else T) <=> p /\ ~q`] THEN
  REWRITE_TAC[RING_SUM_SING; SING_GSPEC] THEN
  SIMP_TAC[RING_MUL_LID; RING_PRODUCT; MONOMIAL_VARS_VAR] THEN
  REWRITE_TAC[RING_PRODUCT_SING] THEN
  ASM_SIMP_TAC[RING_POW; monomial_var; RING_POW_1]);;

let POLY_EXTEND_NEG = prove
 (`!r r' (h:A->B) (x:V->B) p.
      ring_homomorphism(r,r') h /\ ring_polynomial r p
      ==> poly_extend (r,r') h x (poly_neg r p) =
          ring_neg r' (poly_extend (r,r') h x p)`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[ring_polynomial; ring_powerseries] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[poly_extend; poly_neg] THEN
  ASM_SIMP_TAC[RING_NEG_EQ_0; GSYM RING_SUM_NEG; RING_MUL; RING_PRODUCT] THEN
  ASM_SIMP_TAC[RING_MUL_LNEG; RING_PRODUCT]);;

let POLY_EXTEND_ADD = prove
 (`!r r' (h:A->B) (x:V->B) p1 p2.
      ring_homomorphism(r,r') h /\
      ring_polynomial r p1 /\ ring_polynomial r p2
      ==> poly_extend (r,r') h x (poly_add r p1 p2) =
          ring_add r' (poly_extend (r,r') h x p1) (poly_extend (r,r') h x p2)`,
  REWRITE_TAC[ring_polynomial; ring_powerseries] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{m | ~((p1:(V->num)->A) m = ring_0 r)} UNION
                  {m | ~((p2:(V->num)->A) m = ring_0 r)}`;
                 `r:A ring`; `r':B ring`; `h:A->B`] POLY_EXTEND_SUPERSET) THEN
  ASM_SIMP_TAC[SUBSET_UNION] THEN DISCH_THEN(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[poly_add; SUBSET; IN_UNION; IN_ELIM_THM] THEN RING_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[RING_ADD_RDISTRIB; RING_PRODUCT; RING_SUM_ADD; RING_MUL;
               FINITE_UNION; poly_add]);;

let POLY_EXTEND_MUL = prove
 (`!r r' (h:A->B) (x:V->B) p1 p2.
      ring_homomorphism(r,r') h /\
      ring_polynomial r p1 /\ ring_polynomial r p2 /\
      (!i. i IN poly_vars r p1 UNION poly_vars r p2 ==> x i IN ring_carrier r')
      ==> poly_extend (r,r') h x (poly_mul r p1 p2) =
          ring_mul r' (poly_extend (r,r') h x p1) (poly_extend (r,r') h x p2)`,
  let lemma = prove
   (`{x,y | P x y} = IMAGE (\(x,y). y,x) {x,y | P y x}`,
    REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_extend] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_polynomial; ring_powerseries]) THEN
  ASM_SIMP_TAC[GSYM RING_SUM_LMUL; RING_SUM; RING_MUL; RING_PRODUCT] THEN
  ASM_SIMP_TAC[GSYM RING_SUM_RMUL; RING_SUM; RING_MUL; RING_PRODUCT] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [RING_SUM_SUM_PRODUCT; RING_MUL; RING_PRODUCT] THEN
  MP_TAC(ISPECL [`r':B ring`; `\(m1:V->num,m2). monomial_mul m1 m2`]
        RING_SUM_IMAGE_GEN) THEN
  ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[SET_RULE
   `{z | z IN {x,y | P x y} /\ Q z} = {x,y | P x y /\ Q(x,y)}`] THEN
  MATCH_MP_TAC(MESON[]
   `(rsum UNIV f = rsum s f /\ rsum UNIV g = rsum t g) /\
    rsum UNIV f = rsum UNIV g
    ==> rsum s f = rsum t g`) THEN
 CONJ_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RING_SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET_UNIV; IN_UNIV; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_PRODUCT] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[RING_SUM_CLAUSES]
     `s = {} ==> ring_sum r s f = ring_0 r`) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC RING_SUM_EQ] THEN
  X_GEN_TAC `m:V->num` THEN REWRITE_TAC[IN_UNIV] THEN
  ASM_CASES_TAC `INFINITE(monomial_vars m:V->bool)` THENL
   [MP_TAC(ISPECL [`r:A ring`; `p1:(V->num)->A`; `p2:(V->num)->A`]
      RING_POLYNOMIAL_MUL) THEN
    ASM_SIMP_TAC[ring_polynomial; ring_powerseries] THEN STRIP_TAC THEN
    SIMP_TAC[RING_MUL_LZERO; RING_PRODUCT] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN
    REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`m1:V->num`; `m2:V->num`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [MONOMIAL_VARS_MUL]) THEN
    ASM_REWRITE_TAC[INFINITE; FINITE_UNION; monomial_vars] THEN
    REWRITE_TAC[GSYM INFINITE; GSYM monomial_vars; DE_MORGAN_THM] THEN
    ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[MESON[INFINITE]
       `~INFINITE s <=> FINITE s`])] THEN
  REWRITE_TAC[poly_mul] THEN FIRST_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP RING_HOMOMORPHISM_SUM th) o
        lhand o lhand o snd)) THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[MONOMIAL_FINITE_DIVISORPAIRS] THEN ASM_SIMP_TAC[RING_MUL];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[poly_mul] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_PRODUCT; FORALL_IN_GSPEC; RING_MUL] THEN
    ASM_REWRITE_TAC[MONOMIAL_FINITE_DIVISORPAIRS];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [lemma] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; PAIR_EQ] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[o_DEF] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
    REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MONOMIAL_MUL_SYM]] THEN
  MATCH_MP_TAC(MESON[]
   `rsum s f = rsum t f /\ rsum t f = rsum t g
    ==> rsum s f = rsum t g`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_SUPERSET THEN
    CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[]] THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO; RING_PRODUCT];
    MATCH_MP_TAC RING_SUM_EQ] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`m1:V->num`; `m2:V->num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(RING_RULE
   `a IN ring_carrier r /\ b IN ring_carrier r /\ c IN ring_carrier r /\
    x IN ring_carrier r /\ y IN ring_carrier r /\
    ring_mul r a b = c
    ==> ring_mul r (ring_mul r x y) c =
        ring_mul r (ring_mul r x a) (ring_mul r y b)`) THEN
  ASM_SIMP_TAC[RING_PRODUCT] THEN
  MATCH_MP_TAC(MESON[]
   `(ring_product r s f = ring_product r u f /\
     ring_product r t g = ring_product r u g) /\
    ring_mul r (ring_product r u f) (ring_product r u g) =
    ring_product r u h
    ==> ring_mul r (ring_product r s f) (ring_product r t g) =
        ring_product r u h`) THEN
  CONJ_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[MONOMIAL_VARS_MUL] THEN
    CONJ_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_PRODUCT_SUPERSET THEN
    REWRITE_TAC[SUBSET_UNION; IN_UNION] THEN
    REWRITE_TAC[IMP_CONJ_ALT] THEN SIMP_TAC[] THEN
    REWRITE_TAC[monomial_vars; IN_ELIM_THM] THEN
    SIMP_TAC[ring_pow];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_PRODUCT_MUL o lhand o snd) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MESON[INFINITE] `~INFINITE s <=> FINITE s`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:V` THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[MONOMIAL_VARS_MUL; IN_UNION] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_POW THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[poly_vars] THEN
    ASM SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_PRODUCT_EQ THEN EXPAND_TAC "m" THEN
  REWRITE_TAC[MONOMIAL_VARS_MUL; IN_UNION] THEN REWRITE_TAC[monomial_mul] THEN
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_POW_ADD THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[poly_vars] THEN
  ASM SET_TAC[]);;

let RING_HOMOMORPHISM_POLY_EXTEND = prove
 (`!r r' s (h:A->B) (x:V->B).
        ring_homomorphism(r,r') h /\
        (!i. i IN s ==> x i IN ring_carrier r')
        ==> ring_homomorphism (poly_ring r s,r') (poly_extend(r,r') h x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_homomorphism] THEN
  REWRITE_TAC[POLY_RING; IN_ELIM_THM; SUBSET; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[POLY_EXTEND; POLY_EXTEND_0; POLY_EXTEND_1] THEN
  ASM_SIMP_TAC[POLY_EXTEND_NEG; POLY_EXTEND_ADD] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_EXTEND_MUL THEN
  ASM SET_TAC[]);;

let POLY_EXTEND_UNIQUE = prove
 (`!r r' s (h:A->B) (x:V->B) k p.
        ring_homomorphism(r,r') h /\
        ring_homomorphism(poly_ring r s,r') k /\
        (!a. a IN ring_carrier r ==> k(poly_const r a) = h a) /\
        (!i. i IN s ==> k(poly_var r i) = x i) /\
        p IN ring_carrier(poly_ring r s)
        ==> poly_extend(r,r') h x p = k p`,
  REWRITE_TAC[CONJ_ASSOC] THEN ONCE_REWRITE_TAC [IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC POLY_RING_HOMOMORPHISM_UNIQUE THEN
  EXISTS_TAC `r':B ring` THEN
  ASM_SIMP_TAC[POLY_EXTEND_CONST; ETA_AX] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:V` THEN DISCH_TAC;
    X_GEN_TAC `i:V` THEN DISCH_TAC THEN
    MATCH_MP_TAC POLY_EXTEND_VAR THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:V`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_homomorphism])) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[POLY_VAR]);;

let POLY_EXTEND_ID = prove
 (`!(r:A ring) (s:V->bool) p.
        p IN ring_carrier(poly_ring r s)
        ==> poly_extend (r,poly_ring r s) (poly_const r) (poly_var r) p = p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_EXTEND_UNIQUE THEN
  EXISTS_TAC `s:V->bool` THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_ID; RING_HOMOMORPHISM_POLY_CONST]);;

let POLY_EXTEND_COMPOSE = prove
 (`!r s r' t r'' (f:A->B) (g:B->C) (h:V->W) k p.
        ring_homomorphism(r,r') f /\
        ring_homomorphism(r',r'') g /\
        IMAGE h s SUBSET t /\
        IMAGE k t SUBSET ring_carrier r'' /\
        p IN ring_carrier(poly_ring r s)
        ==> poly_extend (r',r'') g k
             (poly_extend (r,poly_ring r' t)
                 (poly_const r' o f) (poly_var r' o h) p) =
            poly_extend (r,r'') (g o f) (k o h) p`,
  REPLICATE_TAC 9 GEN_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC POLY_RING_HOMOMORPHISM_UNIQUE THEN
  EXISTS_TAC `r'':C ring` THEN REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `poly_ring (r':B ring) (t:W->bool)` THEN
    REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN
    ASM_SIMP_TAC[POLY_VAR; o_THM] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `r':B ring` THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST];
    MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN
    ASM_SIMP_TAC[o_THM] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `r':B ring` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `c:A` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EXTEND_CONST o
      rand o lhand o snd) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EXTEND_CONST o
      rand o rand o snd) THEN
    REPLICATE_TAC 2
    (ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
      [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
       EXISTS_TAC `r':B ring` THEN
       ASM_REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST];
       DISCH_THEN SUBST1_TAC]) THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC POLY_EXTEND_CONST THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RING_HOMOMORPHISM]) THEN ASM SET_TAC[];
    X_GEN_TAC `x:V` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EXTEND_VAR o
      rand o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[o_THM; POLY_VAR] THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
      EXISTS_TAC `r':B ring` THEN
      ASM_REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EXTEND_VAR o
      rand o snd) THEN
    ASM_SIMP_TAC[o_THM] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC POLY_EXTEND_VAR THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Some "natural" isomorphisms between polynomial / power series variants.   *)
(* ------------------------------------------------------------------------- *)

let RING_ISOMORPHISM_POWSER_RING_TRIVIAL,
    RING_ISOMORPHISM_POLY_RING_TRIVIAL = (CONJ_PAIR o prove)
 (`(!r. ring_isomorphism (r,powser_ring r {})
                         (poly_const r:A->(V->num)->A)) /\
   (!r. ring_isomorphism (r,poly_ring r {})
                         (poly_const r:A->(V->num)->A))`,
  CONJ_TAC THEN GEN_TAC THEN
  REWRITE_TAC[RING_ISOMORPHISM_MONOMORPHISM_ALT] THEN
  REWRITE_TAC[RING_MONOMORPHISM_POLY_CONST; RING_MONOMORPHISM_POWSER_CONST;
              POLY_RING; POWSER_RING] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN
  X_GEN_TAC `p:(V->num)->A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[poly_vars; SUBSET_EMPTY; EMPTY_UNIONS;
              ring_polynomial; ring_powerseries] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; MONOMIAL_VARS_EQ_EMPTY] THEN
  DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; poly_const] THEN
  EXISTS_TAC `(p:(V->num)->A) monomial_1` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let ISOMORPHIC_POWSER_RING_TRIVIAL = prove
 (`(!r. (powser_ring r {}:((V->num)->A)ring) isomorphic_ring r) /\
   (!r. r isomorphic_ring (powser_ring r {}:((V->num)->A)ring))`,
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [ISOMORPHIC_RING_SYM] THEN
  REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[isomorphic_ring] THEN
  MESON_TAC[RING_ISOMORPHISM_POWSER_RING_TRIVIAL]);;

let ISOMORPHIC_POLY_RING_TRIVIAL = prove
 (`(!r. (poly_ring r {}:((V->num)->A)ring) isomorphic_ring r) /\
   (!r. r isomorphic_ring (poly_ring r {}:((V->num)->A)ring))`,
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [ISOMORPHIC_RING_SYM] THEN
  REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[isomorphic_ring] THEN
  MESON_TAC[RING_ISOMORPHISM_POLY_RING_TRIVIAL]);;

let RING_ISOMORPHISMS_POWSER_RINGS = prove
 (`!r r' s s' (f:A->B) g (i:V->W) j.
        ring_isomorphisms(r,r') (f,g) /\
        (!x. x IN s ==> i(x) IN s' /\ j(i x) = x) /\
        (!y. y IN s' ==> j(y) IN s /\ i(j y) = y)
        ==> ring_isomorphisms (powser_ring r s,powser_ring r' s')
            ((\p m. if monomial_vars m SUBSET s'
                    then f(p(\v. if v IN s then m(i v) else 0))
                    else ring_0 r'),
             (\q m. if monomial_vars m SUBSET s
                    then g(q(\v. if v IN s' then m(j v) else 0))
                    else ring_0 r))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ring_isomorphisms] THEN
  REWRITE_TAC[ring_homomorphism] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN STRIP_TAC THEN
  REWRITE_TAC[o_DEF; RING_ISOMORPHISMS] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[POWSER_RING; ring_powerseries; poly_vars] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; UNIONS_SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM; monomial_vars] THEN CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC;
      X_GEN_TAC `q:(W->num)->B` THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[RING_0];
        X_GEN_TAC `m:V->num` THEN
        COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC INFINITE_SUPERSET THEN
        EXISTS_TAC `IMAGE (i:V->W) {i | ~(m i = 0)}` THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        MATCH_MP_TAC INFINITE_IMAGE THEN ASM SET_TAC[];
        MESON_TAC[];
        ALL_TAC]] THEN
     (GEN_REWRITE_TAC I [FUN_EQ_THM] THEN GEN_TAC THEN
      ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      REWRITE_TAC[MESON[] `~((if p then x else 0) = 0) <=> p /\ ~(x = 0)`] THEN
      REWRITE_TAC[SUBSET_RESTRICT] THEN
      MATCH_MP_TAC(MESON[] `n = m /\ g(f(p m)) = p m ==> g(f(p n)) = p m`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN ASM SET_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]])] THEN
  REWRITE_TAC[RING_HOMOMORPHISM] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    REWRITE_TAC[POWSER_RING; ring_powerseries; poly_vars] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; UNIONS_SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM; monomial_vars] THEN
    X_GEN_TAC `p:(V->num)->A` THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[RING_0];
      X_GEN_TAC `m:W->num` THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC INFINITE_SUPERSET THEN
      EXISTS_TAC `IMAGE (j:W->V) {i | ~(m i = 0)}` THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC INFINITE_IMAGE THEN ASM SET_TAC[];
      MESON_TAC[]];
    REWRITE_TAC[POWSER_RING; poly_1; poly_const] THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:W->num` THEN
    REWRITE_TAC[monomial_1; monomial_vars] THEN
    ASM_CASES_TAC `m = \v:W. 0` THEN ASM_REWRITE_TAC[] THENL
     [ASM_REWRITE_TAC[COND_ID; EMPTY_GSPEC; EMPTY_SUBSET]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
    ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`p:(V->num)->A`; `q:(V->num)->A`] THEN
    REWRITE_TAC[POWSER_RING; ring_powerseries; poly_vars] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; UNIONS_SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM; monomial_vars; INFINITE] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:W->num` THEN
    REWRITE_TAC[poly_add] THEN
    ASM_CASES_TAC `{i:W | ~(m i = 0)} SUBSET s'` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[RING_0; RING_ADD_LZERO] THEN
    MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `f:A->B`]
        RING_HOMOMORPHISM_ADD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE];
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`p:(V->num)->A`; `q:(V->num)->A`] THEN
    REWRITE_TAC[POWSER_RING; ring_powerseries; poly_vars] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; UNIONS_SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM; monomial_vars; INFINITE] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:W->num` THEN
    REWRITE_TAC[poly_mul]] THEN
  ASM_CASES_TAC `{i:W | ~(m i = 0)} SUBSET s'` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
    MAP_EVERY X_GEN_TAC [`m1:W->num`; `m2:W->num`] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[monomial_mul; ADD_EQ_0]) THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL]) THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO; RING_0] THEN
    ASM SET_TAC[]] THEN
  SUBGOAL_THEN
   `{m1,m2 | monomial_mul m1 m2 = (\v. if v IN s then m (i v) else 0)} =
    IMAGE (\(m1,m2). (\v. if v IN s then m1 ((i:V->W) v) else 0),
                     (\v. if v IN s then m2 (i v) else 0))
          {m1,m2 | monomial_mul m1 m2 = m}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM; IN_IMAGE] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`m1:V->num`; `m2:V->num`] THEN
      REWRITE_TAC[FUN_EQ_THM; monomial_mul] THEN DISCH_TAC THEN
      EXISTS_TAC `\w. if w IN s' then m1 ((j:W->V) w) else 0` THEN
      EXISTS_TAC `\w. if w IN s' then m2 ((j:W->V) w) else 0` THEN
      REWRITE_TAC[AND_FORALL_THM] THEN ASM_SIMP_TAC[] THEN CONJ_TAC THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ADD_CLAUSES] THEN
      ASM_REWRITE_TAC[GSYM ADD_EQ_0] THEN ASM SET_TAC[];
      REWRITE_TAC[FUN_EQ_THM; monomial_mul] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o
    rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[FUN_EQ_THM; monomial_mul] THEN
    MAP_EVERY X_GEN_TAC
     [`m1:W->num`; `m2:W->num`; `m1':W->num`; `m2':W->num`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN MATCH_MP_TAC(MESON[]
     `!j. (!x. P(j x) ==> Q x) ==> (!x. P x) ==> (!x. Q x)`) THEN
    EXISTS_TAC `j:W->V` THEN X_GEN_TAC `w:W` THEN
    ASM_CASES_TAC `(w:W) IN s'` THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN(K ALL_TAC) THEN TRANS_TAC EQ_TRANS `0` THEN
    MP_TAC ADD_EQ_0 THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
  REWRITE_TAC[] THEN
  ASM_CASES_TAC `FINITE(monomial_vars m:W->bool)` THENL
   [MP_TAC(GEN `h:(W->num)#(W->num)->A`
     (ISPECL [`r:A ring`; `r':B ring`; `f:A->B`;
              `h:(W->num)#(W->num)->A`]
     (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] RING_HOMOMORPHISM_SUM))) THEN
    DISCH_THEN(fun th ->
      W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[RING_MUL; FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC[MONOMIAL_FINITE_DIVISORPAIRS];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`m1:W->num`; `m2:W->num`] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[o_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[monomial_mul; ADD_EQ_0]) THEN
    REPEAT(COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]]) THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
      RING_HOMOMORPHISM_MUL) THEN
    ASM_REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_GSPEC] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INFINITE]) THEN
    REWRITE_TAC[monomial_vars] THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `ring_0 r':B` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      AP_TERM_TAC;
      CONV_TAC SYM_CONV] THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC(RING_RULE
     `x IN ring_carrier r /\ y IN ring_carrier r /\
      (x = ring_0 r \/ y = ring_0 r)
      ==> ring_mul r x y = ring_0 r`) THEN
    ASM_SIMP_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[]
     `monomial_mul m1 m2 = m
      ==> (INFINITE(monomial_vars(monomial_mul m1 m2)) <=>
           INFINITE(monomial_vars m))`)) THEN
    ASM_REWRITE_TAC[MONOMIAL_VARS_MUL] THEN
    ASM_REWRITE_TAC[monomial_vars] THEN
    REWRITE_TAC[INFINITE; FINITE_UNION; DE_MORGAN_THM] THEN
    MATCH_MP_TAC MONO_OR THEN ASM_REWRITE_TAC[GSYM INFINITE] THEN
    CONJ_TAC THEN DISCH_TAC THEN
    TRY(FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        AP_TERM_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM INFINITE] THEN MATCH_MP_TAC INFINITE_SUPERSET THENL
     [EXISTS_TAC `IMAGE (j:W->V) {i:W | ~(m1 i = 0)}`;
      EXISTS_TAC `IMAGE (j:W->V) {i:W | ~(m2 i = 0)}`;
      EXISTS_TAC `IMAGE (j:W->V) {i:W | ~(m1 i = 0)}`;
      EXISTS_TAC `IMAGE (j:W->V) {i:W | ~(m2 i = 0)}`] THEN
    UNDISCH_THEN `monomial_mul m1 m2:W->num = m` (SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[monomial_mul; ADD_EQ_0]) THEN
    (CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THEN
    MATCH_MP_TAC INFINITE_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

let ISOMORPHIC_POWSER_RINGS = prove
 (`!(r:A ring) (s:V->bool) (r':B ring) (s':W->bool).
        r isomorphic_ring r' /\ s =_c s'
        ==> (powser_ring r s) isomorphic_ring (powser_ring r' s')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; EQ_C_BIJECTIONS] THEN
  REWRITE_TAC[isomorphic_ring; ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_ISOMORPHISMS_POWSER_RINGS) THEN
  MESON_TAC[]);;

let RING_ISOMORPHISMS_POLY_RINGS = prove
 (`!r r' s s' (f:A->B) g (i:V->W) j.
        ring_isomorphisms(r,r') (f,g) /\
        (!x. x IN s ==> i(x) IN s' /\ j(i x) = x) /\
        (!y. y IN s' ==> j(y) IN s /\ i(j y) = y)
        ==> ring_isomorphisms (poly_ring r s,poly_ring r' s')
            ((\p m. if monomial_vars m SUBSET s'
                    then f(p(\v. if v IN s then m(i v) else 0))
                    else ring_0 r'),
             (\q m. if monomial_vars m SUBSET s
                    then g(q(\v. if v IN s' then m(j v) else 0))
                    else ring_0 r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_ISOMORPHISMS_POWSER_RINGS) THEN
  REWRITE_TAC[POLY_RING_AS_SUBRING] THEN
  MATCH_MP_TAC RING_ISOMORPHISMS_BETWEEN_SUBRINGS THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[ring_isomorphisms; RING_HOMOMORPHISM]
   `ring_isomorphisms (r,r') (f,g)
    ==> IMAGE f (ring_carrier r) SUBSET ring_carrier r' /\
        IMAGE g (ring_carrier r') SUBSET ring_carrier r`)) THEN
  REWRITE_TAC[POWSER_RING; POLY_RING; ring_polynomial] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x. P x /\ Q x /\ R x /\ P'(f x) /\ R'(f x) ==> Q'(f x))
    ==> IMAGE f {x | P x /\ R x} SUBSET {y | P' y /\ R' y}
        ==> IMAGE f {x | (P x /\ Q x) /\ R x} SUBSET
                    {y | (P' y /\ Q' y) /\ R' y}`) THEN
  REWRITE_TAC[MESON[] `~((if p then x else z) = z) <=> p /\ ~(x = z)`] THENL
   [X_GEN_TAC `p:(V->num)->A`; X_GEN_TAC `p:(W->num)->B`] THEN
  REWRITE_TAC[ring_powerseries; poly_vars] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THENL
   [EXISTS_TAC `IMAGE (\m v. if v IN s' then m((j:W->V) v) else 0)
                      {m | ~(p m:A = ring_0 r)}`;
    EXISTS_TAC `IMAGE (\m v. if v IN s then m((i:V->W) v) else 0)
                      {m | ~(p m:B = ring_0 r')}`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THENL
   [X_GEN_TAC `m:W->num`; X_GEN_TAC `m:V->num`] THEN
  STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THENL
   [EXISTS_TAC `\v. if v IN s then m((i:V->W) v) else 0`;
    EXISTS_TAC `\v. if v IN s' then m((j:W->V) v) else 0`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN RULE_ASSUM_TAC(REWRITE_RULE
   [monomial_vars; ring_isomorphisms; ring_homomorphism]) THEN
  (CONJ_TAC THENL
   [GEN_REWRITE_TAC I [FUN_EQ_THM] THEN GEN_TAC THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM SET_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT
     `~p ==> (q ==> p) ==> ~q`)) THEN
    SIMP_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE
     [ring_isomorphisms; ring_homomorphism]) THEN
    ASM_REWRITE_TAC[]]));;

let ISOMORPHIC_POLY_RINGS = prove
 (`!(r:A ring) (s:V->bool) (r':B ring) (s':W->bool).
        r isomorphic_ring r' /\ s =_c s'
        ==> (poly_ring r s) isomorphic_ring (poly_ring r' s')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; EQ_C_BIJECTIONS] THEN
  REWRITE_TAC[isomorphic_ring; ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_ISOMORPHISMS_POLY_RINGS) THEN
  MESON_TAC[]);;

let RING_ISOMORPHISMS_POWSER_POWSER_RING = prove
 (`!(r:A ring) u v:V->bool.
        DISJOINT u v
        ==> ring_isomorphisms
             (powser_ring (powser_ring r u) v,powser_ring r (u UNION v))
             ((\p m. if monomial (u UNION v) m
                     then p (monomial_restrict v m) (monomial_restrict u m)
                     else ring_0 r),
              (\p m1 m2. if monomial v m1 /\ monomial u m2
                         then p(monomial_mul m1 m2) else ring_0 r))`,
  MAP_EVERY X_GEN_TAC [`r:A ring`; `v:V->bool`; `u:V->bool`] THEN
  ONCE_REWRITE_TAC[UNION_COMM; DISJOINT_SYM] THEN DISCH_TAC THEN
  REWRITE_TAC[monomial_restrict] THEN
  GEN_REWRITE_TAC I [RING_ISOMORPHISMS_SYM] THEN
  REWRITE_TAC[RING_ISOMORPHISMS; RING_CARRIER_POWSER_RING; IN_ELIM_THM] THEN
  REWRITE_TAC[CONJUNCT2 POWSER_RING] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `p:(V->num)->A` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:V->num` THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [monomial]) THEN
    REWRITE_TAC[monomial; monomial_vars; SUBSET_RESTRICT; MESON[]
     `~((if p then x else 0) = 0) <=> p /\ ~(x = 0)`] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{x | x IN s /\ P x} = {x | x IN {y | P y} /\ x IN s}`] THEN
    SIMP_TAC[FINITE_RESTRICT] THEN STRIP_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; monomial_mul] THEN GEN_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]) THEN
    ASM SET_TAC[];
    X_GEN_TAC `q:(V->num)->(V->num)->A` THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_0];
      MESON_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m1:V->num` THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m2:V->num` THEN
    REWRITE_TAC[MONOMIAL_MUL] THEN
    REWRITE_TAC[monomial] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      BINOP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `i:V` THEN REWRITE_TAC[monomial_mul] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[monomial; monomial_vars]) THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[EQ_ADD_LCANCEL_0; EQ_ADD_RCANCEL_0] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
      REWRITE_TAC[GSYM monomial] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[poly_0; poly_const; COND_ID]]] THEN
  REWRITE_TAC[RING_HOMOMORPHISM] THEN
  GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[RING_CARRIER_POWSER_RING; IN_ELIM_THM] THEN
    X_GEN_TAC `p:(V->num)->A` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[RING_0]; ALL_TAC] THEN
    SIMP_TAC[POWSER_RING; poly_0; poly_const; COND_ID];
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m1:V->num` THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m2:V->num` THEN
    REWRITE_TAC[poly_const; poly_1; POWSER_RING; MONOMIAL_MUL_EQ_1] THEN
    ASM_CASES_TAC `m1:V->num = monomial_1` THEN
    ASM_REWRITE_TAC[poly_0; poly_const; COND_ID] THEN
    ASM_CASES_TAC `m2:V->num = monomial_1` THEN
    ASM_REWRITE_TAC[MONOMIAL_1; COND_ID];
    MAP_EVERY X_GEN_TAC [`p:(V->num)->A`; `q:(V->num)->A`] THEN
    STRIP_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m1:V->num` THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m2:V->num` THEN
    REWRITE_TAC[POWSER_RING; poly_add] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[RING_ADD_LZERO; RING_0];
    MAP_EVERY X_GEN_TAC [`p:(V->num)->A`; `q:(V->num)->A`] THEN
    REWRITE_TAC[RING_CARRIER_POWSER_RING; IN_ELIM_THM] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `m:V->num`] THEN
  ASM_CASES_TAC `monomial u (m:V->num)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `n:V->num` THEN
    REWRITE_TAC[POWSER_RING] THEN REWRITE_TAC[poly_mul] THEN
    MATCH_MP_TAC(MESON[]
     `ring_0 (powser_ring r t) m = ring_0 r /\
      ring_sum (powser_ring r t) s f = ring_0 (powser_ring r t)
      ==> ring_0 r = ring_sum (powser_ring r t) s f m`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[POWSER_RING; poly_0; poly_const; COND_ID]; ALL_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`ma:V->num`; `mb:V->num`] THEN
    DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC(RING_RULE
       `(x IN ring_carrier r /\ y IN ring_carrier r) /\
        (x = ring_0 r \/ y = ring_0 r)
        ==> ring_mul r x y = ring_0 r`) THEN
    REWRITE_TAC[RING_CARRIER_POWSER_RING; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[RING_0]; ALL_TAC] THEN
    UNDISCH_TAC `~monomial (u:V->bool) m` THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[MONOMIAL_MUL; DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[POWSER_RING; poly_0; poly_const; COND_ID]] THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `n:V->num` THEN
  REWRITE_TAC[POWSER_RING] THEN REWRITE_TAC[poly_mul] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POWSER_SUM o  rator o rand o snd) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; MONOMIAL_FINITE_DIVISORPAIRS] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[monomial]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN
    REWRITE_TAC[RING_CARRIER_POWSER_RING; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_0];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
  ASM_CASES_TAC `monomial (v:V->bool) n` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`ma:V->num`; `mb:V->num`] THEN
    DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[POWSER_RING; poly_mul] THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`mc:V->num`; `md:V->num`] THEN
    DISCH_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_0; RING_MUL_LZERO; RING_MUL_RZERO] THEN
    UNDISCH_TAC `~monomial (v:V->bool) n` THEN EXPAND_TAC "n" THEN
    REWRITE_TAC[MONOMIAL_MUL; DE_MORGAN_THM] THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[POWSER_RING; poly_mul] THEN
  REWRITE_TAC[LAMBDA_PAIR] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SUM_PRODUCT o rand o snd) THEN
  REWRITE_TAC[MONOMIAL_FINITE_DIVISORPAIRS] THEN ANTS_TAC THENL
   [REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[monomial]; ALL_TAC]) THEN
    ASM_MESON_TAC[RING_0; RING_MUL];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[MESON[RING_0; RING_MUL_LZERO; RING_MUL_RZERO]
   `x IN ring_carrier r /\ y IN ring_carrier r
    ==> ring_mul r (if p then x else ring_0 r) (if q then y else ring_0 r) =
        if p /\ q then ring_mul r x y else ring_0 r`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [LAMBDA_PAIR] THEN
  REWRITE_TAC[GSYM RING_SUM_RESTRICT_SET] THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN {f a b | P a b} /\ Q x} = {f a b |a,b| P a b /\ Q(f a b)}`] THEN
  REWRITE_TAC[SET_RULE
   `{f x y | (x IN {g a b | P a b} /\ y IN {h c d | Q c d}) /\ R x y} =
    {f (g a b) (h c d) |a,b,c,d| P a b /\ Q c d /\ R (g a b) (h c d)}`] THEN
  MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `(\(m',n'). (monomial_restrict u m',monomial_restrict u n'),
                         (monomial_restrict v m',monomial_restrict v n'))
              :(V->num)#(V->num)->((V->num)#(V->num))#((V->num)#(V->num))` THEN
  EXISTS_TAC `\((m1,n1),(m1',n1')). (monomial_mul m1 m1':V->num,
                                     monomial_mul n1 n1':V->num)` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; IN_ELIM_QUAD_THM] THEN
  ASM_SIMP_TAC[RING_MUL] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [monomial])) THEN
  UNDISCH_TAC `DISJOINT (u:V->bool) v` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[monomial; MONOMIAL_VARS_RESTRICT; INTER_SUBSET; PAIR_EQ] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ALL_TAC;
    DISCH_THEN(fun th ->
      MP_TAC th THEN
      MP_TAC(AP_TERM `monomial_vars:(V->num)->V->bool` th) THEN
      MP_TAC(AP_TERM `FINITE o (monomial_vars:(V->num)->V->bool)` th))] THEN
  ASM_REWRITE_TAC[o_THM; MONOMIAL_VARS_MUL; FINITE_UNION] THEN
  ASM_SIMP_TAC[FINITE_INTER] THEN REPEAT STRIP_TAC THEN
  TRY(MATCH_MP_TAC(MESON[]
    `x = x' /\ y = y'
     ==> ring_mul r (p x) (q y) = ring_mul r (p x') (q y')`)) THEN
  REPEAT CONJ_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM])) THEN
  REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `i:V` THEN REWRITE_TAC[monomial_mul; monomial_restrict] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:V` o GEN_REWRITE_RULE I [SUBSET])) THEN
  REWRITE_TAC[monomial_vars; IN_ELIM_THM] THEN
  MAP_EVERY ASM_CASES_TAC [`(i:V) IN u`; `(i:V) IN v`] THEN
  ASM_REWRITE_TAC[EQ_ADD_LCANCEL_0; EQ_ADD_RCANCEL_0] THEN
  TRY ARITH_TAC THEN ASM SET_TAC[]);;

let ISOMORPHIC_RING_POWSER_POWSER = prove
 (`!(r:A ring) u v:V->bool.
        DISJOINT u v
        ==> powser_ring (powser_ring r u) v isomorphic_ring
            powser_ring r (u UNION v)`,
  MP_TAC RING_ISOMORPHISMS_POWSER_POWSER_RING THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  MESON_TAC[]);;

let ISOMORPHIC_RING_POWSER_POWSER_GEN = prove
 (`!(r:A ring) (r':B ring) (u:U->bool) (v:V->bool) (w:W->bool).
        r isomorphic_ring r' /\ u +_c v =_c w
        ==> powser_ring (powser_ring r u) v isomorphic_ring powser_ring r' w`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC ISOMORPHIC_RING_TRANS
   `powser_ring (r:A ring) ((u:U->bool) +_c (v:V->bool))` THEN
  ASM_SIMP_TAC[ISOMORPHIC_POWSER_RINGS; CARD_EQ_REFL] THEN
  REWRITE_TAC[add_c] THEN
  W(MP_TAC o PART_MATCH (rand o rand) ISOMORPHIC_RING_POWSER_POWSER o
    rand o snd) THEN
  REWRITE_TAC[sum_DISTINCT; SET_RULE
     `DISJOINT {f x | x IN s} {g y | y IN t} <=>
      !x y. x IN s /\ y IN t ==> ~(f x = g y)`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ISOMORPHIC_RING_TRANS) THEN
  REPEAT(MATCH_MP_TAC ISOMORPHIC_POWSER_RINGS THEN CONJ_TAC) THEN
  REWRITE_TAC[ISOMORPHIC_RING_REFL] THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC CARD_EQ_IMAGE THEN
  SIMP_TAC[sum_INJECTIVE]);;

let RING_CARRIER_POWSER_SUBRING_GENERATED = prove
 (`!r (s:A->bool) (v:V->bool).
        s subring_of r
        ==> ring_carrier (powser_ring (subring_generated r s) v) =
            ring_carrier (powser_ring r v) INTER {p | !m. p m IN s}`,
  SIMP_TAC[RING_CARRIER_POWSER_RING; CARRIER_SUBRING_GENERATED_SUBRING] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; subring_of] THEN SET_TAC[]);;

let RING_CARRIER_POLY_SUBRING_GENERATED = prove
 (`!r (s:A->bool) (v:V->bool).
        s subring_of r
        ==> ring_carrier (poly_ring (subring_generated r s) v) =
            ring_carrier (poly_ring r v) INTER {p | !m. p m IN s}`,
  SIMP_TAC[RING_CARRIER_POLY_RING; CARRIER_SUBRING_GENERATED_SUBRING] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; subring_of] THEN SET_TAC[]);;

let SUBRING_POWSER_INTO_SUBRING = prove
 (`!r (s:A->bool) (v:V->bool).
        s subring_of r
        ==> ring_carrier (powser_ring r v) INTER {p | !m. p m IN s}
            subring_of powser_ring r v`,
  REWRITE_TAC[subring_of; INTER_SUBSET] THEN
  SIMP_TAC[IN_INTER; RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
  REWRITE_TAC[RING_CARRIER_POWSER_RING; CONJUNCT2 POWSER_RING] THEN
  REWRITE_TAC[IN_ELIM_THM; poly_0; poly_1; poly_const;
              poly_neg; poly_add; poly_mul] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  MAP_EVERY X_GEN_TAC [`p:(V->num)->A`; `q:(V->num)->A`] THEN
  STRIP_TAC THEN X_GEN_TAC `m:V->num` THEN
  MATCH_MP_TAC(REWRITE_RULE[]
   (ISPECL [`r:A ring`; `\x:A. x IN s`] RING_SUM_CLOSED)) THEN
  ASM_SIMP_TAC[FORALL_PAIR_THM]);;

let SUBRING_POLY_INTO_SUBRING = prove
 (`!r (s:A->bool) (v:V->bool).
        s subring_of r
        ==> ring_carrier (poly_ring r v) INTER {p | !m. p m IN s}
            subring_of poly_ring r v`,
  REWRITE_TAC[subring_of; INTER_SUBSET] THEN
  SIMP_TAC[IN_INTER; RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
  REWRITE_TAC[RING_CARRIER_POLY_RING; CONJUNCT2 POLY_RING] THEN
  REWRITE_TAC[IN_ELIM_THM; poly_0; poly_1; poly_const;
              poly_neg; poly_add; poly_mul] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  MAP_EVERY X_GEN_TAC [`p:(V->num)->A`; `q:(V->num)->A`] THEN
  STRIP_TAC THEN X_GEN_TAC `m:V->num` THEN
  MATCH_MP_TAC(REWRITE_RULE[]
   (ISPECL [`r:A ring`; `\x:A. x IN s`] RING_SUM_CLOSED)) THEN
  ASM_SIMP_TAC[FORALL_PAIR_THM]);;

let RING_ISOMORPHISMS_POWSER_SUBRING_GENERATED = prove
 (`!r (s:A->bool) (v:V->bool).
        s subring_of r
        ==> ring_isomorphisms
             (powser_ring (subring_generated r s) v,
              subring_generated (powser_ring r v) {p | !m. p m IN s})
             (I,I)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RING_ISOMORPHISMS; RING_HOMOMORPHISM] THEN
  REWRITE_TAC[I_THM; IMAGE_I; CONJUNCT2 SUBRING_GENERATED] THEN
  ASM_SIMP_TAC[RING_CARRIER_POWSER_SUBRING_GENERATED] THEN
  GEN_REWRITE_TAC I [TAUT `(p /\ q) /\ r <=> q /\ (r /\ p)`] THEN
  CONJ_TAC THENL
   [SIMP_TAC[CONJUNCT2 POWSER_RING; CONJUNCT2 SUBRING_GENERATED;
             poly_1; poly_const; poly_add; poly_mul] THEN
    MAP_EVERY X_GEN_TAC [`p:(V->num)->A`; `q:(V->num)->A`] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_SUM_SUBRING_GENERATED] THEN
    ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s <=> !x. x IN s ==> P x`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[subring_of]) THEN
    ASM_SIMP_TAC[FORALL_IN_GSPEC];
    REWRITE_TAC[SET_RULE
     `(!y. y IN t ==> y IN s) /\ s SUBSET t <=> s = t`] THEN
    ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN
    ASM_SIMP_TAC[SUBRING_POWSER_INTO_SUBRING]]);;

let ISOMORPHIC_RINGS_POWSER_SUBRING_GENERATED = prove
 (`!r (s:A->bool) (v:V->bool).
        s subring_of r
        ==> (powser_ring (subring_generated r s) v) isomorphic_ring
            (subring_generated (powser_ring r v) {p | !m. p m IN s})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  REPEAT(EXISTS_TAC `I:((V->num)->A)->((V->num)->A)`) THEN
  ASM_SIMP_TAC[RING_ISOMORPHISMS_POWSER_SUBRING_GENERATED]);;

let RING_ISOMORPHISMS_POLY_SUBRING_GENERATED = prove
 (`!r (s:A->bool) (v:V->bool).
        s subring_of r
        ==> ring_isomorphisms
             (poly_ring (subring_generated r s) v,
              subring_generated (poly_ring r v) {p | !m. p m IN s})
             (I,I)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RING_ISOMORPHISMS; RING_HOMOMORPHISM] THEN
  REWRITE_TAC[I_THM; IMAGE_I; CONJUNCT2 SUBRING_GENERATED] THEN
  ASM_SIMP_TAC[RING_CARRIER_POLY_SUBRING_GENERATED] THEN
  GEN_REWRITE_TAC I [TAUT `(p /\ q) /\ r <=> q /\ (r /\ p)`] THEN
  CONJ_TAC THENL
   [SIMP_TAC[CONJUNCT2 POLY_RING; CONJUNCT2 SUBRING_GENERATED;
             poly_1; poly_const; poly_add; poly_mul] THEN
    MAP_EVERY X_GEN_TAC [`p:(V->num)->A`; `q:(V->num)->A`] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_SUM_SUBRING_GENERATED] THEN
    ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s <=> !x. x IN s ==> P x`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[subring_of]) THEN
    ASM_SIMP_TAC[FORALL_IN_GSPEC];
    REWRITE_TAC[SET_RULE
     `(!y. y IN t ==> y IN s) /\ s SUBSET t <=> s = t`] THEN
    ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN
    ASM_SIMP_TAC[SUBRING_POLY_INTO_SUBRING]]);;

let ISOMORPHIC_RINGS_POLY_SUBRING_GENERATED = prove
 (`!r (s:A->bool) (v:V->bool).
        s subring_of r
        ==> (poly_ring (subring_generated r s) v) isomorphic_ring
            (subring_generated (poly_ring r v) {p | !m. p m IN s})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  REPEAT(EXISTS_TAC `I:((V->num)->A)->((V->num)->A)`) THEN
  ASM_SIMP_TAC[RING_ISOMORPHISMS_POLY_SUBRING_GENERATED]);;

let RING_ISOMORPHISMS_POLY_POLY_RING = prove
 (`!(r:A ring) u v:V->bool.
        DISJOINT u v
        ==> ring_isomorphisms
             (poly_ring (poly_ring r u) v,poly_ring r (u UNION v))
             ((\p m. if monomial (u UNION v) m
                     then p (monomial_restrict v m) (monomial_restrict u m)
                     else ring_0 r),
              (\p m1 m2. if monomial v m1 /\ monomial u m2
                         then p(monomial_mul m1 m2) else ring_0 r))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
   [GSYM(CONJUNCT2(SPEC_ALL I_O_ID))] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [GSYM(CONJUNCT1(SPEC_ALL I_O_ID))] THEN
  MATCH_MP_TAC RING_ISOMORPHISMS_COMPOSE THEN
  EXISTS_TAC
   `subring_generated (poly_ring (powser_ring r u) v)
     {p:(V->num)->(V->num)->A | !m. p m IN ring_carrier (poly_ring r u)}` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV)
     [ONCE_REWRITE_RULE[SUBRING_GENERATED_RESTRICT]
         POLY_RING_AS_SUBRING_FINITE] THEN
    REWRITE_TAC[GSYM RING_CARRIER_POLY_RING_FINITE] THEN
    MATCH_MP_TAC RING_ISOMORPHISMS_POLY_SUBRING_GENERATED THEN
    REWRITE_TAC[POLY_CARRIER_SUBRING_OF_POWSER_RING];
    ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT]] THEN
  REWRITE_TAC
   [ONCE_REWRITE_RULE[SUBRING_GENERATED_RESTRICT]
         POLY_RING_AS_SUBRING_FINITE] THEN
  REWRITE_TAC[GSYM RING_CARRIER_POLY_RING_FINITE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUBRING_GENERATED_SUBRING_GENERATED o
    lhand o lhand o snd) THEN
  REWRITE_TAC[POLY_CARRIER_SUBRING_OF_POWSER_RING] THEN
  REWRITE_TAC[RING_CARRIER_POLY_RING_FINITE] THEN
  REWRITE_TAC[GSYM SUBRING_GENERATED_RESTRICT] THEN
  REWRITE_TAC[GSYM POLY_RING_AS_SUBRING_FINITE] THEN
  REWRITE_TAC[GSYM RING_CARRIER_POLY_RING_FINITE] THEN
  REWRITE_TAC[SET_RULE `s INTER s INTER t = s INTER t`] THEN ANTS_TAC THENL
   [MATCH_MP_TAC(MESON[SUBRING_OF_SUBRING_GENERATED_REV; POLY_RING_AS_SUBRING]
     `t subring_of poly_ring r s ==> t subring_of powser_ring r s`) THEN
    MATCH_MP_TAC SUBRING_POLY_INTO_SUBRING THEN
    REWRITE_TAC[POLY_CARRIER_SUBRING_OF_POWSER_RING];
    DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [ONCE_REWRITE_RULE[SUBRING_GENERATED_RESTRICT]
         POLY_RING_AS_SUBRING_FINITE] THEN
  MATCH_MP_TAC RING_ISOMORPHISMS_BETWEEN_SUBRINGS THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_ISOMORPHISMS_POWSER_POWSER_RING THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ring_isomorphisms] THEN
    GEN_REWRITE_TAC LAND_CONV [CONJ_ASSOC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  REWRITE_TAC[ring_homomorphism] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV)
     [RING_CARRIER_POLY_RING_FINITE];
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV)
     [RING_CARRIER_POLY_RING_FINITE]] THEN
  REWRITE_TAC[INTER_ASSOC] THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s /\ x IN s' ==> f x IN t')
    ==> IMAGE f s SUBSET t
        ==> IMAGE f (s INTER s') SUBSET t INTER t'`) THEN
  REWRITE_TAC[RING_CARRIER_POLY_RING_FINITE; IN_INTER; IN_ELIM_THM] THEN
  REWRITE_TAC[MESON[] `~((if p then x else z) = z) <=> p /\ ~(x = z)`] THENL
   [X_GEN_TAC `p:(V->num)->(V->num)->A` THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `{ monomial_mul m1 m2 |
        m1 IN {m | ~(p m = ring_0 (powser_ring r u))} /\
        m2 IN {m | ~((p:(V->num)->(V->num)->A) m1 m = ring_0 r)}}` THEN
    ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `m:V->num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    EXISTS_TAC `monomial_restrict v m:V->num` THEN
    EXISTS_TAC `monomial_restrict u m:V->num` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    REWRITE_TAC[POWSER_RING; poly_0; poly_const; COND_ID] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; X_GEN_TAC `i:V`] THEN
    REWRITE_TAC[monomial_restrict; monomial_mul] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [monomial]) THEN
    REWRITE_TAC[monomial_vars] THEN ASM SET_TAC[];
    X_GEN_TAC `p:(V->num)->A` THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [RING_CARRIER_POWSER_RING; monomial; IN_ELIM_THM]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[POWSER_RING; poly_0; poly_const; COND_ID] THEN
      ONCE_REWRITE_TAC[FUN_EQ_THM] THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
       `UNIONS { {d | monomial_divides d m} |
                 m IN {m | ~((p:(V->num)->A) m = ring_0 r)}}` THEN
      ASM_SIMP_TAC[FINITE_UNIONS; SIMPLE_IMAGE; FINITE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; UNIONS_IMAGE; FORALL_IN_GSPEC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MONOMIAL_FINITE_DIVISORS] THEN ASM SET_TAC[];
        GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `n:V->num` THEN REWRITE_TAC[NOT_FORALL_THM; MESON[]
         `~((if p then x else z) = z) <=> p /\ ~(x = z)`] THEN
        DISCH_THEN(X_CHOOSE_THEN `p:V->num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `monomial_mul n p:V->num` THEN
        ASM_SIMP_TAC[MONOMIAL_DIVIDES_RMUL; MONOMIAL_DIVIDES_REFL]];
      X_GEN_TAC `m:V->num` THEN
      ASM_SIMP_TAC[RING_CARRIER_POWSER_RING; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[RING_0]; ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
       `UNIONS { {d | monomial_divides d m} |
                 m IN {m | ~((p:(V->num)->A) m = ring_0 r)}}` THEN
      ASM_SIMP_TAC[FINITE_UNIONS; SIMPLE_IMAGE; FINITE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; UNIONS_IMAGE; FORALL_IN_GSPEC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MONOMIAL_FINITE_DIVISORS] THEN ASM SET_TAC[];
        GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `n:V->num` THEN STRIP_TAC THEN
        EXISTS_TAC `monomial_mul m n:V->num` THEN
        ASM_SIMP_TAC[MONOMIAL_DIVIDES_LMUL; MONOMIAL_DIVIDES_REFL]]]]);;

let ISOMORPHIC_RING_POLY_POLY = prove
 (`!(r:A ring) u v:V->bool.
        DISJOINT u v
        ==> poly_ring (poly_ring r u) v isomorphic_ring
            poly_ring r (u UNION v)`,
  MP_TAC RING_ISOMORPHISMS_POLY_POLY_RING THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  MESON_TAC[]);;

let ISOMORPHIC_RING_POLY_POLY_GEN = prove
 (`!(r:A ring) (r':B ring) (u:U->bool) (v:V->bool) (w:W->bool).
        r isomorphic_ring r' /\ u +_c v =_c w
        ==> poly_ring (poly_ring r u) v isomorphic_ring poly_ring r' w`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC ISOMORPHIC_RING_TRANS
   `poly_ring (r:A ring) ((u:U->bool) +_c (v:V->bool))` THEN
  ASM_SIMP_TAC[ISOMORPHIC_POLY_RINGS; CARD_EQ_REFL] THEN
  REWRITE_TAC[add_c] THEN
  W(MP_TAC o PART_MATCH (rand o rand) ISOMORPHIC_RING_POLY_POLY o
    rand o snd) THEN
  REWRITE_TAC[sum_DISTINCT; SET_RULE
     `DISJOINT {f x | x IN s} {g y | y IN t} <=>
      !x y. x IN s /\ y IN t ==> ~(f x = g y)`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ISOMORPHIC_RING_TRANS) THEN
  REPEAT(MATCH_MP_TAC ISOMORPHIC_POLY_RINGS THEN CONJ_TAC) THEN
  REWRITE_TAC[ISOMORPHIC_RING_REFL] THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC CARD_EQ_IMAGE THEN
  SIMP_TAC[sum_INJECTIVE]);;

(* ------------------------------------------------------------------------- *)
(* Monomial divisibility is a partial order, and on a *finite* set of        *)
(* variables any preorder extending it (in particular a "compatible" one)    *)
(* is automatically a WQO, hence wellfounded, and hence WO whenever total.   *)
(* ------------------------------------------------------------------------- *)

let POSET_MONOMIAL_DIVIDES = prove
 (`poset(monomial_divides:(V->num)->(V->num)->bool)`,
  REWRITE_TAC[poset; MONOMIAL_DIVIDES_REFL] THEN
  REWRITE_TAC[MONOMIAL_DIVIDES_TRANS; MONOMIAL_DIVIDES_ANTISYM]);;

let FLD_MONOMIAL_DIVIDES = prove
 (`fld(monomial_divides) = (:V->num)`,
  SIMP_TAC[QOSET_FLD; POSET_IMP_QOSET; POSET_MONOMIAL_DIVIDES] THEN
  REWRITE_TAC[MONOMIAL_DIVIDES_REFL; UNIV_GSPEC]);;

let COMPATIBLE_MONOMIAL_ORDER = prove
 (`!(<<=) (s:V->bool).
     (!m. monomial s m ==> monomial_1 <<= m) /\
     (!m n p. monomial s m /\ monomial s n /\ monomial s p /\ n <<= p
              ==> monomial_mul m n <<= monomial_mul m p)
     ==> !m n. monomial s m /\ monomial s n /\ monomial_divides m n
               ==> m <<= n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`m:V->num`; `monomial_1:V->num`; `monomial_div n m:V->num`]) THEN
  ASM_SIMP_TAC[MONOMIAL_DIV; MONOMIAL_DIV_LMUL] THEN
  REWRITE_TAC[MONOMIAL_1; MONOMIAL_MUL_RID]);;

let WQOSET_COMPATIBLE_MONOMIAL_ORDER = prove
 (`!(<<=) (s:V->bool).
       FINITE s /\ qoset(<<=) /\ fld(<<=) SUBSET {m | monomial s m} /\
       (!m n. monomial s m /\ monomial s n /\ monomial_divides m n ==> m <<= n)
       ==> wqoset(<<=)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WQOSET_SUPERSET THEN
  EXISTS_TAC `\m (n:V->num). monomial s m /\ monomial s n /\
                             monomial_divides m n` THEN
  ASM_SIMP_TAC[FLD_RESTRICT_QOSET; POSET_IMP_QOSET; POSET_MONOMIAL_DIVIDES;
               FLD_MONOMIAL_DIVIDES; IN_UNIV; IN_GSPEC] THEN
  MP_TAC(ISPECL [`(<=):num->num->bool`; `s:V->bool`]
        WQOSET_POINTWISE) THEN
  ASM_REWRITE_TAC[WQOSET_num] THEN DISCH_THEN(MP_TAC o SPEC
    `monomial (s:V->bool)` o MATCH_MP WQOSET_RESTRICT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; monomial; monomial_vars; monomial_divides] THEN
  MP_TAC(ARITH_RULE `0 <= 0`) THEN SET_TAC[]);;

let WF_COMPATIBLE_MONOMIAL_ORDER = prove
 (`!(<<=) (s:V->bool).
       FINITE s /\ qoset(<<=) /\ fld(<<=) SUBSET {m | monomial s m} /\
       (!m n. monomial s m /\ monomial s n /\ monomial_divides m n ==> m <<= n)
       ==> WF(strictly(<<=))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP WQOSET_COMPATIBLE_MONOMIAL_ORDER) THEN
  REWRITE_TAC[WQOSET_IMP_WF]);;

let WOSET_COMPATIBLE_MONOMIAL_ORDER = prove
 (`!(<<=) (s:V->bool).
       FINITE s /\ toset(<<=) /\ fld(<<=) SUBSET {m | monomial s m} /\
       (!m n. monomial s m /\ monomial s n /\ monomial_divides m n ==> m <<= n)
       ==> woset(<<=)`,
  SIMP_TAC[WOSET_WQOSET] THEN
  MESON_TAC[WQOSET_COMPATIBLE_MONOMIAL_ORDER; TOSET_IMP_QOSET]);;

(* ------------------------------------------------------------------------- *)
(* A more general monomial ordering on monomials over any set of             *)
(* variables (the monomials themselves are still finitely supported).        *)
(* This is simply the classic Dershowitz-Manna multiset ordering, which      *)
(* has all the main properties we want. It's parametrized by a variable      *)
(* ordering, which can be either a reflexive or irreflexive relation.        *)
(* Whatever the parametrizing "order" is, the overall monomial order is      *)
(* at least reflexive and transitive and compatible with multiplication.     *)
(* If the variable order is a partial order on variables it is also          *)
(* equivalent to the Huet-Oppen form, and in the case of a total order       *)
(* becomes a lexicographic order. It also inherits being a partial order,    *)
(* total order, wellorder and being wellfounded in general from the          *)
(* variable order. It is *not* designed to preserve any equivalences         *)
(* given a non-antisymmetric variable order.                                 *)
(* ------------------------------------------------------------------------- *)

let monomial_le = new_definition
 `monomial_le (<<=) (m1:V->num) m2 <=>
        monomial (:V) m1 /\ monomial (:V) m2 /\
        ?ma mb. monomial (:V) ma /\ monomial (:V) mb /\
                monomial_mul m1 ma = monomial_mul m2 mb /\
                !i. i IN monomial_vars mb
                    ==> ?j. j IN monomial_vars ma /\ properly(<<=) i j`;;

let monomial_lt = new_definition
  `monomial_lt (<<=) (m1:V->num) m2 <=>
        ~(m1 = m2) /\ monomial_le (<<=) (m1:V->num) m2`;;

let PROPERLY_MONOMIAL_LE = prove
 (`!(<<=):V->V->bool. properly(monomial_le(<<=)) = monomial_lt(<<=)`,
  REWRITE_TAC[FUN_EQ_THM; properly; monomial_lt] THEN MESON_TAC[]);;

let MONOMIAL_LE_MONO = prove
 (`!l l'. (!x y. l x y ==> l' x y)
         ==> (!m n. monomial_le l m n ==> monomial_le l' m n)`,
  REWRITE_TAC[monomial_le; properly] THEN MESON_TAC[]);;

let MONOMIAL_LT_MONO = prove
 (`!l l'. (!x y. l x y ==> l' x y)
         ==> (!m n. monomial_lt l m n ==> monomial_lt l' m n)`,
  REWRITE_TAC[monomial_lt; monomial_le; properly] THEN MESON_TAC[]);;

let MONOMIAL_LE_PROPERLY = prove
 (`!(<<=):V->V->bool. monomial_le (properly(<<=)) = monomial_le (<<=)`,
  REWRITE_TAC[FUN_EQ_THM; monomial_le; PROPERLY_PROPERLY]);;

let MONOMIAL_LT_PROPERLY = prove
 (`!(<<=):V->V->bool. monomial_lt (properly(<<=)) = monomial_lt (<<=)`,
  REWRITE_TAC[FUN_EQ_THM; monomial_lt; monomial_le; PROPERLY_PROPERLY]);;

let MONOMIAL_LE_IMPROPERLY = prove
 (`!(<<):V->V->bool.
        monomial_le (\x y. x << y \/ x = y) = monomial_le (<<)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MONOMIAL_LE_PROPERLY] THEN
  AP_TERM_TAC THEN REWRITE_TAC[properly; FUN_EQ_THM] THEN MESON_TAC[]);;

let MONOMIAL_LT_IMPROPERLY = prove
 (`!(<<):V->V->bool. monomial_lt (\x y. x << y \/ x = y) = monomial_lt (<<)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MONOMIAL_LT_PROPERLY] THEN
  AP_TERM_TAC THEN REWRITE_TAC[properly; FUN_EQ_THM] THEN MESON_TAC[]);;

let MONOMIAL_LE_REFL = prove
 (`!(<<=) m. monomial_le (<<=) m m <=> monomial (:V) m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[monomial_le] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(EXISTS_TAC `monomial_1:V->num`) THEN
  REWRITE_TAC[MONOMIAL_VARS_1; MONOMIAL_MUL_LID; MONOMIAL_MUL_RID] THEN
  REWRITE_TAC[MONOMIAL_1; NOT_IN_EMPTY]);;

let MONOMIAL_LT_REFL = prove
 (`!(<<) m:V->num. ~(monomial_lt (<<) m m)`,
  REWRITE_TAC[monomial_lt]);;

let MONOMIAL_LT_IMP_LE = prove
 (`!(<<) m1 m2:V->num. monomial_lt (<<) m1 m2 ==> monomial_le (<<) m1 m2`,
  SIMP_TAC[monomial_lt]);;

let MONOMIAL_LE_LT = prove
 (`!(<<) m1 m2:V->num.
        monomial_le (<<) m1 m2 <=>
        monomial_lt (<<) m1 m2 \/
        monomial (:V) m1 /\ monomial (:V) m2 /\ m1 = m2`,
  REWRITE_TAC[monomial_lt] THEN MESON_TAC[MONOMIAL_LE_REFL]);;

let MONOMIAL_LE_TRANS = prove
 (`!(<<=) m1 m2 m3:V->num.
        monomial_le (<<=) m1 m2 /\ monomial_le (<<=) m2 m3
        ==> monomial_le (<<=) m1 m3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[monomial_le; LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ma:V->num`; `mb:V->num`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`mc:V->num`; `md:V->num`] THEN STRIP_TAC THEN
  EXISTS_TAC `monomial_mul ma mc:V->num` THEN
  EXISTS_TAC `monomial_mul mb md:V->num` THEN
  ASM_REWRITE_TAC[MONOMIAL_MUL; MONOMIAL_VARS_MUL] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN CONV_TAC MONOMIAL_RULE);;

let QOSET_MONOMIAL_LE = prove
 (`!(<<=):V->V->bool. qoset(monomial_le (<<=))`,
  REWRITE_TAC[qoset; MONOMIAL_LE_TRANS; MONOMIAL_LE_REFL] THEN
  REWRITE_TAC[fld; monomial_le; IN_ELIM_THM] THEN MESON_TAC[]);;

let FLD_MONOMIAL_LE = prove
 (`!(<<=). fld(monomial_le(<<=)) = {m | monomial (:V) m}`,
  GEN_TAC THEN REWRITE_TAC[GSYM MONOMIAL_LE_REFL] THEN
  MATCH_MP_TAC QOSET_FLD THEN REWRITE_TAC[QOSET_MONOMIAL_LE]);;

let MONOMIAL_LE_LMUL = prove
 (`!(<<=) m m1 m2:V->num.
        monomial_le (<<=) (monomial_mul m m1) (monomial_mul m m2) <=>
        monomial (:V) m /\ monomial_le (<<=) m1 m2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[monomial_le] THEN
  REWRITE_TAC[MONOMIAL_VARS_MUL; MONOMIAL_MUL] THEN
  REWRITE_TAC[GSYM MONOMIAL_MUL_ASSOC; MONOMIAL_MUL_LCANCEL] THEN
  REWRITE_TAC[CONJ_ACI]);;

let MONOMIAL_LE_RMUL = prove
 (`!(<<=) m m1 m2:V->num.
        monomial_le (<<=) (monomial_mul m1 m) (monomial_mul m2 m) <=>
        monomial (:V) m /\ monomial_le (<<=) m1 m2`,
  ONCE_REWRITE_TAC[MONOMIAL_MUL_SYM] THEN
  REWRITE_TAC[MONOMIAL_LE_LMUL]);;

let MONOMIAL_LT_LMUL = prove
 (`!(<<=) m m1 m2:V->num.
        monomial_lt (<<=) (monomial_mul m m1) (monomial_mul m m2) <=>
        monomial (:V) m /\ monomial_lt (<<=) m1 m2`,
  REWRITE_TAC[monomial_lt; MONOMIAL_MUL_LCANCEL; MONOMIAL_LE_LMUL] THEN
  MESON_TAC[]);;

let MONOMIAL_LT_RMUL = prove
 (`!(<<=) m m1 m2:V->num.
        monomial_lt (<<=) (monomial_mul m1 m) (monomial_mul m2 m) <=>
        monomial (:V) m /\ monomial_lt (<<=) m1 m2`,
  REWRITE_TAC[monomial_lt; MONOMIAL_MUL_RCANCEL; MONOMIAL_LE_RMUL] THEN
  MESON_TAC[]);;

let MONOMIAL_LE_MUL2 = prove
 (`!(<<=) m1 m1' m2 m2':V->num.
         monomial_le (<<=) m1 m1' /\
         monomial_le (<<=) m2 m2'
        ==> monomial_le (<<=) (monomial_mul m1 m2) (monomial_mul m1' m2')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MONOMIAL_LE_TRANS THEN
  EXISTS_TAC  `monomial_mul m1' m2:V->num` THEN
  ASM_REWRITE_TAC[MONOMIAL_LE_LMUL; MONOMIAL_LE_RMUL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[monomial_le]) THEN ASM_REWRITE_TAC[]);;

let MONOMIAL_LE_DIVISOR = prove
 (`!m d:V->num. monomial (:V) m /\ monomial_divides d m
                ==> monomial_le (<<=) d m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[monomial_le] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MONOMIAL_DIVISOR]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`monomial_div m d:V->num`; `monomial_1:V->num`] THEN
  ASM_REWRITE_TAC[MONOMIAL_DIV_LMUL_EQ; MONOMIAL_MUL_RID] THEN
  ASM_SIMP_TAC[MONOMIAL_DIV; MONOMIAL_1; MONOMIAL_VARS_1; NOT_IN_EMPTY]);;

let MONOMIAL_GE_1 = prove
 (`!(<<=) (m:V->num).
        monomial_le (<<=) monomial_1 m <=> monomial (:V) m`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[monomial_le]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] MONOMIAL_LE_DIVISOR) THEN
  REWRITE_TAC[MONOMIAL_DIVIDES_1]);;

let MONOMIAL_LE_VARS = prove
 (`!(<<=) v w:V.
    v <<= w ==> monomial_le (<<=) (monomial_var v) (monomial_var w)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `v:V = w` THEN ASM_REWRITE_TAC[MONOMIAL_LE_REFL] THEN
  REWRITE_TAC[monomial_le; MONOMIAL_VAR; IN_UNIV] THEN
  REWRITE_TAC[FINITE_SING] THEN MAP_EVERY EXISTS_TAC
   [`monomial_var(w:V)`; `monomial_var(v:V)`] THEN
  REWRITE_TAC[MONOMIAL_VARS_VAR; MONOMIAL_VAR; IN_UNIV] THEN
  REWRITE_TAC[MONOMIAL_MUL_SYM; properly] THEN ASM SET_TAC[]);;

let MONOMIAL_LT_VARS = prove
 (`!(<<=) v w:V.
    properly(<<=) v w ==> monomial_lt (<<=) (monomial_var v) (monomial_var w)`,
  SIMP_TAC[monomial_lt; MONOMIAL_VAR_EQ; properly; MONOMIAL_LE_VARS]);;

let MONOMIAL_LE_POSET = prove
 (`!(<<=):V->V->bool.
        poset(<<=)
        ==> monomial_le (<<=) =
            \m1 m2. monomial (:V) m1 /\ monomial (:V) m2 /\
                    !i. m2 i < m1 i ==> ?j. i <<= j /\ m1 j < m2 j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`m1:V->num`; `m2:V->num`] THEN
  REWRITE_TAC[monomial_le; properly; MONOMIAL] THEN
  ASM_CASES_TAC `FINITE(monomial_vars m1:V->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `FINITE(monomial_vars m2:V->bool)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `\i. (m2:V->num) i - m1 i` THEN
    EXISTS_TAC `\i. (m1:V->num) i - m2 i` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `monomial_vars(m2:V->num)`;
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `monomial_vars(m1:V->num)`;
      REWRITE_TAC[monomial_mul] THEN ABS_TAC THEN ARITH_TAC;
      X_GEN_TAC `i:V` THEN REWRITE_TAC[monomial_vars; IN_ELIM_THM] THEN
      REWRITE_TAC[ARITH_RULE `~(a - b = 0) <=> b < a`] THEN
      ASM_MESON_TAC[LT_ANTISYM]] THEN
    ASM_REWRITE_TAC[SUBSET; monomial_vars; IN_ELIM_THM] THEN ARITH_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  MAP_EVERY X_GEN_TAC [`ma:V->num`; `mb:V->num`] THEN
  REPLICATE_TAC 3 DISCH_TAC THEN
  REWRITE_TAC[monomial_vars; IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. (ma:V->num) i < mb i ==> (?j. i <<= j /\ mb j < ma j)`
  MP_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[monomial_mul] THEN MESON_TAC[ARITH_RULE
     `a + b:num = c + d ==> (b < d <=> c < a) /\ (a < c <=> d < b)`]] THEN
  X_GEN_TAC `i:V` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[MESON[]
   `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x y:V. x = y \/ x <<= y`;
                 `{j:V | j IN monomial_vars mb /\ (i:V) <<= j}`]
        POSET_MAX) THEN
  ASM_SIMP_TAC[NOT_IMP; FINITE_RESTRICT] THEN REWRITE_TAC[monomial_vars] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC; FORALL_IN_GSPEC; strictly] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [poset]) THEN
    REWRITE_TAC[poset; fld] THEN SET_TAC[];
    ASM_MESON_TAC[ARITH_RULE `a < b ==> ~(b = 0)`;
                  ARITH_RULE `a <= b /\ ~(a = 0) ==> ~(b = 0)`];
    REWRITE_TAC[fld] THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `j:V` STRIP_ASSUME_TAC) THEN
    UNDISCH_THEN
     `!i:V. ~(mb i = 0) ==> (?j. ~(ma j = 0) /\ i <<= j /\ ~(i = j))`
     (MP_TAC o SPEC `j:V`) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `k:V` THEN STRIP_TAC THEN
    SUBGOAL_THEN `((i:V) <<= (k:V)):bool` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[poset]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:V`)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[NOT_IMP] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[properly] THEN RULE_ASSUM_TAC(REWRITE_RULE[poset]) THEN
    ASM_MESON_TAC[]]);;

let MONOMIAL_LE_ANTISYM = prove
 (`!(<<=) m1 m2:V->num.
        poset(<<=) /\
        monomial_le (<<=) m1 m2 /\
        monomial_le (<<=) m2 m1
        ==> m1 = m2`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ] THEN
  SIMP_TAC[MONOMIAL_LE_POSET] THEN REWRITE_TAC[poset] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[ARITH_RULE `m:num = n <=> ~(m < n) /\ ~(n < m)`] THEN
  MATCH_MP_TAC(SET_RULE
   `~(~({i | P i} = {})) /\ ~(~({i | Q i} = {}))
    ==> !i. ~(P i) /\ ~(Q i)`) THEN
  CONJ_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\x y:V. x = y \/ x <<= y` POSET_MAX) THENL
   [DISCH_THEN(MP_TAC o SPEC `{i | (m1:V->num) i < m2 i}`);
    DISCH_THEN(MP_TAC o SPEC `{i | (m2:V->num) i < m1 i}`)] THEN
  (ASM_REWRITE_TAC[NOT_IMP; SUBSET; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[poset] THEN ASM_MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[MONOMIAL]) THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `monomial_vars(monomial_mul m1 m2:V->num)` THEN
    ASM_REWRITE_TAC[MONOMIAL_VARS_MUL; FINITE_UNION] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; monomial_vars; IN_UNION] THEN ARITH_TAC;
    REWRITE_TAC[fld; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[properly] THEN ASM_METIS_TAC[LT_ANTISYM]]));;

let MONOMIAL_LET_ANTISYM = prove
 (`!(<<=) m1 m2.
        poset(<<=)
        ==> ~(monomial_le (<<=) m1 m2 /\ monomial_lt (<<=) m2 m1)`,
  REWRITE_TAC[monomial_lt; TAUT `~(p /\ ~q /\ r) <=> r /\ p ==> q`] THEN
  REWRITE_TAC[IMP_IMP; MONOMIAL_LE_ANTISYM]);;

let MONOMIAL_LTE_ANTISYM = prove
 (`!(<<=) m1 m2.
        poset(<<=)
        ==> ~(monomial_lt (<<=) m1 m2 /\ monomial_le (<<=) m2 m1)`,
  REWRITE_TAC[monomial_lt; TAUT `~((~p /\ q) /\ r) <=> q /\ r ==> p`] THEN
  REWRITE_TAC[IMP_IMP; MONOMIAL_LE_ANTISYM]);;

let MONOMIAL_LT_ANTISYM = prove
 (`!(<<=) m1 m2.
        poset(<<=)
        ==> ~(monomial_lt (<<=) m1 m2 /\ monomial_lt (<<=) m2 m1)`,
  MESON_TAC[MONOMIAL_LT_IMP_LE; MONOMIAL_LTE_ANTISYM]);;

let MONOMIAL_LET_TRANS = prove
 (`!(<<=) m1 m2 m3:V->num.
        poset(<<=) /\
        monomial_le (<<=) m1 m2 /\
        monomial_lt (<<=) m2 m3
        ==> monomial_lt (<<=) m1 m3`,
  REWRITE_TAC[monomial_lt] THEN
  MESON_TAC[MONOMIAL_LE_TRANS; MONOMIAL_LE_ANTISYM]);;

let MONOMIAL_LTE_TRANS = prove
 (`!(<<=) m1 m2 m3.
        poset(<<=) /\
        monomial_lt (<<=) m1 m2 /\
        monomial_le (<<=) m2 m3
        ==> monomial_lt (<<=) m1 m3`,
  REWRITE_TAC[monomial_lt] THEN
  MESON_TAC[MONOMIAL_LE_TRANS; MONOMIAL_LE_ANTISYM]);;

let MONOMIAL_LT_TRANS = prove
 (`!(<<=) m1 m2 m3.
        poset(<<=) /\
        monomial_lt (<<=) m1 m2 /\
        monomial_lt (<<=) m2 m3
        ==> monomial_lt (<<=) m1 m3`,
  MESON_TAC[MONOMIAL_LT_IMP_LE; MONOMIAL_LTE_TRANS]);;

let MONOMIAL_LET_MUL2 = prove
 (`!(<<=) m1 m1' m2 m2':V->num.
        poset(<<=) /\
        monomial_le (<<=) m1 m1' /\ monomial_lt (<<=) m2 m2'
        ==> monomial_lt (<<=) (monomial_mul m1 m2) (monomial_mul m1' m2')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MONOMIAL_LET_TRANS THEN
  EXISTS_TAC  `monomial_mul m1' m2:V->num` THEN
  ASM_REWRITE_TAC[MONOMIAL_LT_LMUL; MONOMIAL_LE_RMUL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[monomial_lt; monomial_le]) THEN
  ASM_REWRITE_TAC[]);;

let MONOMIAL_LTE_MUL2 = prove
 (`!(<<=) m1 m1' m2 m2':V->num.
        poset(<<=) /\
        monomial_lt (<<=) m1 m1' /\ monomial_le (<<=) m2 m2'
        ==> monomial_lt (<<=) (monomial_mul m1 m2) (monomial_mul m1' m2')`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MONOMIAL_MUL_SYM] THEN
  MATCH_MP_TAC MONOMIAL_LET_MUL2 THEN ASM_MESON_TAC[]);;

let MONOMIAL_LT_MUL2 = prove
 (`!(<<=) m1 m1' m2 m2':V->num.
        poset(<<=) /\
        monomial_lt (<<=) m1 m1' /\ monomial_lt (<<=) m2 m2'
        ==> monomial_lt (<<=) (monomial_mul m1 m2) (monomial_mul m1' m2')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MONOMIAL_LET_MUL2 THEN
  ASM_SIMP_TAC[MONOMIAL_LT_IMP_LE]);;

let POSET_MONOMIAL_LE = prove
 (`!(<<=):V->V->bool. poset(<<=) ==> poset(monomial_le(<<=))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[poset; FLD_MONOMIAL_LE; MONOMIAL_LE_REFL] THEN
  REWRITE_TAC[IN_ELIM_THM; MONOMIAL_LE_TRANS] THEN
  ASM_MESON_TAC[MONOMIAL_LE_ANTISYM]);;

let MONOMIAL_LE_VARS_EQ = prove
 (`!(<<=) v w.
        poset(<<=) /\ fld(<<=) = (:V)
        ==> (monomial_le (<<=) (monomial_var v) (monomial_var w) <=>
             v <<= w)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[MONOMIAL_LE_VARS] THEN
  ASM_SIMP_TAC[MONOMIAL_LE_POSET; MONOMIAL_VARS_VAR] THEN
  REWRITE_TAC[FINITE_SING; monomial_var] THEN
  SIMP_TAC[MESON[ARITH_RULE `0 < 1 /\ ~(1 < 0)`; LT_REFL]
   `(if p then 1 else 0) < (if q then 1 else 0) <=> ~p /\ q`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2; IMP_CONJ; FORALL_UNWIND_THM2] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[poset]) THEN ASM SET_TAC[]);;

let MONOMIAL_LT_VARS_EQ = prove
 (`!(<<=) v w:V.
        poset(<<=)
        ==> (monomial_lt (<<=) (monomial_var v) (monomial_var w) <=>
             v <<= w /\ ~(v = w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[monomial_lt] THEN
  ASM_CASES_TAC `v:V = w` THEN ASM_REWRITE_TAC[MONOMIAL_VAR_EQ] THEN
  ASM_SIMP_TAC[MONOMIAL_LE_POSET; MONOMIAL_VARS_VAR;
               MONOMIAL_VAR; IN_UNIV] THEN
  SIMP_TAC[monomial_var; MESON[ARITH_RULE `0 < 1 /\ ~(1 < 0)`; LT_REFL]
   `(if p then 1 else 0) < (if q then 1 else 0) <=> ~p /\ q`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2; IMP_CONJ; FORALL_UNWIND_THM2] THEN
  ASM_REWRITE_TAC[]);;

let MONOMIAL_LT_TOSET = prove
 (`!(<<=) m1 m2.
        toset (<<=) /\ fld (<<=) = (:V)
        ==> (monomial_lt (<<=) m1 m2 <=>
             monomial (:V) m1 /\ monomial (:V) m2 /\
             ?i. m1 i < m2 i /\ !j. properly (<<=) i j ==> m1 j = m2 j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[monomial_lt] THEN
  ASM_CASES_TAC `m1:V->num = m2` THEN ASM_REWRITE_TAC[LT_REFL] THEN
  ASM_SIMP_TAC[MONOMIAL_LE_POSET; TOSET_IMP_POSET; properly; CONJ_ASSOC] THEN
  REWRITE_TAC[MONOMIAL; GSYM FINITE_UNION] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`(<<=):V->V->bool`; `{i | ~((m1:V->num) i = m2 i)}`]
        TOSET_MAX) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; IN_ELIM_THM] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; monomial_vars] THEN
        ARITH_TAC;
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        REWRITE_TAC[GSYM FUN_EQ_THM] THEN ASM_REWRITE_TAC[ETA_AX]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:V` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [toset]) THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN
      REPEAT STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[LT_ANTISYM]] THEN
      MATCH_MP_TAC(ARITH_RULE `~(a:num = b) /\ ~(a < b) ==> b < a`) THEN
      ASM_METIS_TAC[LT_ANTISYM; LT_TRANS]];
    DISCH_THEN(X_CHOOSE_THEN `j:V` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `i:V` THEN DISCH_TAC THEN EXISTS_TAC `j:V` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [toset]) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN ASM_METIS_TAC[LT_ANTISYM; LT_TRANS]]);;

let MONOMIAL_LE_TOSET = prove
 (`!(<<=) m1 m2.
        toset (<<=) /\ fld (<<=) = (:V)
        ==> (monomial_le (<<=) m1 m2 <=>
             monomial (:V) m1 /\ monomial (:V) m2 /\
             (m1 = m2 \/
              ?i. m1 i < m2 i /\ !j. properly (<<=) i j ==> m1 j = m2 j))`,
  SIMP_TAC[MONOMIAL_LE_LT; MONOMIAL_LT_TOSET] THEN MESON_TAC[]);;

let TOSET_MONOMIAL_LE = prove
 (`!(<<=). toset (<<=) /\ fld (<<=) = (:V) ==> toset(monomial_le (<<=))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[toset; FLD_MONOMIAL_LE] THEN
  ASM_SIMP_TAC[MONOMIAL_LE_TOSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:V->num`; `y:V->num`] THEN
  TRY(X_GEN_TAC `z:V->num`) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC)
         THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[properly] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [toset]) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:V` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:V` STRIP_ASSUME_TAC) THEN DISJ2_TAC THEN
    SUBGOAL_THEN `(i:V) <<= (j:V) \/ j <<= i`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL [EXISTS_TAC `j:V`; EXISTS_TAC `i:V`] THEN
    ASM_MESON_TAC[LT_ANTISYM; LT_TRANS];
    DISCH_THEN(X_CHOOSE_THEN `i:V` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:V` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(i:V) <<= (j:V) \/ j <<= i`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[LT_ANTISYM; LT_TRANS];
    ASM_CASES_TAC `x:V->num = y` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(<<=):V->V->bool`; `{i | ~((x:V->num) i = y i)}`]
        TOSET_MAX) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[toset; IN_UNIV] THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[MONOMIAL]) THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `monomial_vars(x:V->num) UNION monomial_vars y` THEN
        ASM_REWRITE_TAC[FINITE_UNION] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; monomial_vars] THEN
        ARITH_TAC;
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        REWRITE_TAC[GSYM FUN_EQ_THM] THEN ASM_REWRITE_TAC[ETA_AX]];
      REWRITE_TAC[OR_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:V` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
       `~(m:num = n) ==> m < n \/ n < m`)) THEN
      MATCH_MP_TAC MONO_OR THEN ASM_MESON_TAC[]]]);;

let WF_MONOMIAL_LT = prove
 (`!(<<):V->V->bool. WF(<<) ==> WF(monomial_lt(<<))`,
  SUBGOAL_THEN
   `!(<<):V->V->bool.
        WF(<<) /\
        (\m1 m2. monomial (:V) m1 /\ monomial (:V) m2 /\
                 !i. m2 i < m1 i ==> ?j. i << j /\ m1 j < m2 j) =
        monomial_le (<<)
        ==> WF(monomial_lt(<<))`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `(<<):V->V->bool` THEN STRIP_TAC THEN
    (X_CHOOSE_THEN `(<<<):V->V->bool` MP_TAC o prove_inductive_relations_exist)
     `(!x y. x << y ==> x <<< y) /\
      (!(x:V) y z. x <<< y /\ y <<< z ==> x <<< z)` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
    MATCH_MP_TAC WF_SUBSET THEN
    EXISTS_TAC `monomial_lt((<<<):V->V->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MONOMIAL_LT_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[WF] THEN X_GEN_TAC `P:V->bool` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `\y:V. ?z:V. P z /\ z <<< y` o
        GEN_REWRITE_RULE I [WF]) THEN
      SUBGOAL_THEN `!x:V z:V. x <<< z ==> x << z \/ ?y:V. x <<< y /\ y << z`
      MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; MESON_TAC[]];
      FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [WF]) THEN
      DISCH_TAC] THEN
    ONCE_REWRITE_TAC[GSYM MONOMIAL_LE_IMPROPERLY] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MONOMIAL_LE_POSET o rand o snd) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP WF_ANTISYM) THEN
      REWRITE_TAC[poset] THEN ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      MESON_TAC[LT_ANTISYM]]] THEN
  X_GEN_TAC `(<<):V->V->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")) THEN
  (X_CHOOSE_THEN `w:(V->num)->bool` MP_TAC o prove_inductive_relations_exist)
   `!m. monomial (:V) m /\ (!m'. monomial_lt (<<) m' m ==> w m') ==> w m` THEN
  MP_TAC(SET_RULE `!m:V->num. w m <=> m IN w`) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I") (LABEL_TAC "C" o GSYM)) THEN
  SUBGOAL_THEN `!m. monomial (:V) m ==> m IN w` ASSUME_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[WF_IND] THEN X_GEN_TAC `P:(V->num)->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!m:V->num. m IN w ==> P m` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE
        [monomial_lt; monomial_le; GSYM MONOMIAL]) THEN
      ASM_MESON_TAC[]]] THEN
  MATCH_MP_TAC MONOMIAL_INDUCT THEN REWRITE_TAC[IN_UNIV] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MONOMIAL_1] THEN
    REWRITE_TAC[monomial_lt] THEN USE_THEN "D" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[monomial_1; LT; FUN_EQ_THM] THEN MESON_TAC[LE_1];
    GEN_REWRITE_TAC I [SWAP_FORALL_THM]] THEN
  SUBGOAL_THEN
   `!P. (!m. m IN w /\ (!m'. monomial_lt (<<) m' m ==> P m') ==> P m)
           ==> !m:V->num. m IN w ==> P m`
   (LABEL_TAC "J")
  THENL
   [GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `a ==> b <=> a ==> a /\ b`] THEN
    REMOVE_THEN "I" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(!x y. Q x y ==> R x y) ==> (!x y. P x y /\ Q x y ==> R x y)`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [WF_IND]) THEN
  X_GEN_TAC `a:V` THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  DISCH_TAC THEN
  USE_THEN "J" MATCH_MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  X_GEN_TAC `m0:V->num` THEN STRIP_TAC THEN
  USE_THEN "R" MATCH_MP_TAC THEN
  REWRITE_TAC[MONOMIAL_MUL; MONOMIAL_VAR; IN_UNIV] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; X_GEN_TAC `n:V->num` THEN DISCH_TAC] THEN
  ASM_CASES_TAC `(n:V->num)(a) = m0(a) + 1` THENL
   [ABBREV_TAC `n0:V->num = \b. if b = a then m0(a) else (n:V->num) b` THEN
    SUBGOAL_THEN `n = monomial_mul (monomial_var a) (n0:V->num)`
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "n0" THEN
      REWRITE_TAC[FUN_EQ_THM; monomial_mul; monomial_var] THEN
      X_GEN_TAC `i:V` THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MONOMIAL_LT_LMUL]];
    ALL_TAC] THEN
  ABBREV_TAC
   `n0:V->num = \b. if m0(b) < n(b) /\ b << (a:V) then m0(b) else n b` THEN
  SUBGOAL_THEN `monomial_le (<<) (n0:V->num) m0` ASSUME_TAC THENL
   [EXPAND_TAC "n0" THEN USE_THEN "D" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[monomial_lt]) THEN
      USE_THEN "D" (SUBST1_TAC o SYM) THEN REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[MONOMIAL_MUL] THEN
      SIMP_TAC[MONOMIAL_VAR; IN_UNIV] THEN
      REWRITE_TAC[MONOMIAL; GSYM FINITE_UNION] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
      REWRITE_TAC[monomial_vars; SUBSET; IN_UNION; IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `i:V` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LT_REFL] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[monomial_lt]) THEN
    USE_THEN "D" (SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `i:V` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[monomial_mul; monomial_var] THEN
    ASM_CASES_TAC `i:V = a` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `j:V` THEN ASM_CASES_TAC `j:V = a` THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN ASM_ARITH_TAC] THEN
    UNDISCH_THEN `i:V = a` SUBST_ALL_TAC THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `j:V` THEN ASM_CASES_TAC `j:V = a` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(n0:V->num) IN w` ASSUME_TAC THENL
   [ASM_CASES_TAC `n0:V->num = m0` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[monomial_lt];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?k:V->num. monomial {b | b << (a:V)} k /\ n = monomial_mul k n0`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `monomial_div (n:V->num) n0` THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM EQ_SYM_EQ] THEN
    REWRITE_TAC[MONOMIAL_DIV_RMUL_EQ] THEN EXPAND_TAC "n0" THEN
    REWRITE_TAC[monomial; monomial_div; monomial_divides] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    REWRITE_TAC[monomial_vars; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [monomial_lt]) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      USE_THEN "D" (SUBST1_TAC o SYM) THEN REWRITE_TAC[MONOMIAL] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
      REWRITE_TAC[SUBSET; monomial_vars; IN_ELIM_THM] THEN ARITH_TAC;
      GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `monomial {b:V | b << (a:V)} k` THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`k:V->num`,`k:V->num`) THEN
  MATCH_MP_TAC MONOMIAL_INDUCT THEN
  REWRITE_TAC[IN_ELIM_THM; MONOMIAL_MUL_LID; GSYM MONOMIAL_MUL_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let WOSET_MONOMIAL_LE = prove
 (`!(<<=). woset(<<=) /\ fld(<<=) = (:V) ==> woset(monomial_le(<<=))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WOSET_WF] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `(<<=):V->V->bool` TOSET_MONOMIAL_LE) THEN
    ASM_SIMP_TAC[WOSET_IMP_TOSET] THEN SIMP_TAC[toset];
    REWRITE_TAC[PROPERLY_MONOMIAL_LE] THEN
    ONCE_REWRITE_TAC[GSYM MONOMIAL_LT_PROPERLY] THEN
    MATCH_MP_TAC WF_MONOMIAL_LT THEN ASM_MESON_TAC[WOSET_WF]]);;

(* ------------------------------------------------------------------------- *)
(* Cardinalities of sets of monomials, polynomials and of power series.      *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_MONOMIALS_FINITE = prove
 (`!s:V->bool. FINITE s /\ ~(s = {}) ==> {m | monomial s m} =_c (:num)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[monomial; monomial_vars] THEN
  ASM_SIMP_TAC[MESON[FINITE_SUBSET]
   `FINITE s ==> (FINITE t /\ t SUBSET s <=> t SUBSET s)`] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x | ~(f x = k x)} SUBSET s <=>
    IMAGE f s SUBSET UNIV /\ {x | ~(f x = k x)} SUBSET s`] THEN
  W(MP_TAC o PART_MATCH lhand CARD_EQ_FUNSPACE o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
  MATCH_MP_TAC CARD_EQ_EXP_INFINITE_FINITE THEN
  ASM_REWRITE_TAC[num_INFINITE]);;

let CARD_EQ_MONOMIALS_INFINITE = prove
 (`!s:V->bool. INFINITE s ==> {m | monomial s m} =_c s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[monomial; monomial_vars] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{m | FINITE {i | ~(m i = 0)} /\ {i | ~(m i = 0)} SUBSET s} =
    {m | IMAGE m s SUBSET (:num) /\
         {i | ~(m i = 0)} SUBSET s /\
         FINITE {i | ~(m i = 0)}}`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_EQ_RESTRICTED_FUNSPACE_INFINITE o
    lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_UNIV] THEN MP_TAC(ARITH_RULE `~(1 = 0)`) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS)] THEN
  W(MP_TAC o PART_MATCH lhand CARD_MUL_SYM o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
  MATCH_MP_TAC CARD_MUL_ABSORB THEN
  ASM_REWRITE_TAC[GSYM INFINITE_CARD_LE; UNIV_NOT_EMPTY]);;

let CARD_EQ_MONOMIALS_COUNTABLE = prove
 (`!s:V->bool. COUNTABLE s /\ ~(s = {}) ==> {m | monomial s m} =_c (:num)`,
  REWRITE_TAC[COUNTABLE_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_EQ_MONOMIALS_FINITE] THEN
  TRANS_TAC CARD_EQ_TRANS `s:V->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CARD_EQ_MONOMIALS_INFINITE THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        CARD_EQ_INFINITE)) THEN
  REWRITE_TAC[num_INFINITE]);;

let CARD_EQ_POWSER_RING_COUNTABLE = prove
 (`!(r:A ring) (s:V->bool).
        COUNTABLE s /\ ~(s = {})
        ==> ring_carrier(powser_ring r s) =_c (ring_carrier r) ^_c (:num)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{m | monomial (s:V->bool) m}`; `ring_carrier r:A->bool`;
    `(\m. ring_0 r):(V->num)->A`] CARD_EQ_FUNSPACE) THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CARD_EQ_CONG THEN
  ASM_SIMP_TAC[CARD_EXP_CONG; CARD_EQ_REFL; CARD_EQ_MONOMIALS_COUNTABLE] THEN
  MATCH_MP_TAC CARD_EQ_REFL_IMP THEN
  REWRITE_TAC[RING_CARRIER_POWSER_RING] THEN
  MP_TAC(ISPEC `r:A ring` RING_0) THEN SET_TAC[]);;

let CARD_EQ_POWSER_RING_FINITE = prove
 (`!(r:A ring) (s:V->bool).
        FINITE s /\ ~(s = {})
        ==> ring_carrier(powser_ring r s) =_c (ring_carrier r) ^_c (:num)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_EQ_POWSER_RING_COUNTABLE THEN
  ASM_SIMP_TAC[FINITE_IMP_COUNTABLE]);;

let CARD_EQ_POWSER_RING_INFINITE = prove
 (`!(r:A ring) (s:V->bool).
        INFINITE s
        ==> ring_carrier(powser_ring r s) =_c (ring_carrier r) ^_c s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{m | monomial (s:V->bool) m}`; `ring_carrier r:A->bool`;
    `(\m. ring_0 r):(V->num)->A`] CARD_EQ_FUNSPACE) THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CARD_EQ_CONG THEN
  ASM_SIMP_TAC[CARD_EXP_CONG; CARD_EQ_REFL; CARD_EQ_MONOMIALS_INFINITE] THEN
  MATCH_MP_TAC CARD_EQ_REFL_IMP THEN
  REWRITE_TAC[RING_CARRIER_POWSER_RING] THEN
  MP_TAC(ISPEC `r:A ring` RING_0) THEN SET_TAC[]);;

let CARD_EQ_POLY_RING_COUNTABLE = prove
 (`!(r:A ring) (s:V->bool).
        ~trivial_ring r /\ COUNTABLE s /\ ~(s = {})
        ==> ring_carrier(poly_ring r s) =_c (ring_carrier r) *_c (:num)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{m | monomial (s:V->bool) m}`; `ring_carrier r:A->bool`;
    `(\m. ring_0 r):(V->num)->A`] CARD_EQ_RESTRICTED_FUNSPACE_INFINITE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM TRIVIAL_RING_ALT] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RING_0] THEN
    MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] CARD_EQ_INFINITE)
        num_INFINITE) THEN
    MATCH_MP_TAC CARD_EQ_MONOMIALS_COUNTABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CARD_EQ_CONG] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_REFL_IMP THEN
    REWRITE_TAC[RING_CARRIER_POLY_RING] THEN
    MP_TAC(ISPEC `r:A ring` RING_0) THEN SET_TAC[];
    W(MP_TAC o PART_MATCH lhand CARD_MUL_SYM o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
    ASM_SIMP_TAC[CARD_MUL_CONG; CARD_EQ_REFL; CARD_EQ_MONOMIALS_COUNTABLE]]);;

let CARD_EQ_POLY_RING_FINITE = prove
 (`!(r:A ring) (s:V->bool).
        ~trivial_ring r /\ FINITE s /\ ~(s = {})
        ==> ring_carrier(poly_ring r s) =_c (ring_carrier r) *_c (:num)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_EQ_POLY_RING_COUNTABLE THEN
  ASM_SIMP_TAC[FINITE_IMP_COUNTABLE]);;

let CARD_EQ_POLY_RING_INFINITE = prove
 (`!(r:A ring) (s:V->bool).
        ~trivial_ring r /\ INFINITE s
        ==> ring_carrier(poly_ring r s) =_c (ring_carrier r) *_c s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{m | monomial (s:V->bool) m}`; `ring_carrier r:A->bool`;
    `(\m. ring_0 r):(V->num)->A`] CARD_EQ_RESTRICTED_FUNSPACE_INFINITE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM TRIVIAL_RING_ALT] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RING_0] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] CARD_EQ_INFINITE)) THEN
    MATCH_MP_TAC CARD_EQ_MONOMIALS_INFINITE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CARD_EQ_CONG] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_REFL_IMP THEN
    REWRITE_TAC[RING_CARRIER_POLY_RING] THEN
    MP_TAC(ISPEC `r:A ring` RING_0) THEN SET_TAC[];
    W(MP_TAC o PART_MATCH lhand CARD_MUL_SYM o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
    ASM_SIMP_TAC[CARD_MUL_CONG; CARD_EQ_REFL; CARD_EQ_MONOMIALS_INFINITE]]);;

(* ------------------------------------------------------------------------- *)
(* Zerodivisors and units in polynomial and power series rings.              *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_DOMAIN_POWSER_RING = prove
 (`!(r:A ring) (s:V->bool).
        integral_domain(powser_ring r s) <=> integral_domain r`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
     INTEGRAL_DOMAIN_MONOMORPHIC_PREIMAGE) THEN
    MESON_TAC[RING_MONOMORPHISM_POWSER_CONST];
    REWRITE_TAC[integral_domain; GSYM TRIVIAL_RING_10]] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[TRIVIAL_POWSER_RING] THEN
  REWRITE_TAC[RING_CARRIER_POWSER_RING] THEN REWRITE_TAC[POWSER_RING] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`p:(V->num)->A`; `q:(V->num)->A`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM; FUN_EQ_THM; NOT_FORALL_THM; poly_0] THEN
  REWRITE_TAC[POLY_CONST_0; poly_mul] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `(:V)` WO) THEN DISCH_THEN(X_CHOOSE_TAC `l:V->V->bool`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WOSET_MONOMIAL_LE) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [WOSET]) THEN
  REWRITE_TAC[FLD_MONOMIAL_LE] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `{m | ~((q:(V->num)->A) m = ring_0 r)}` th) THEN
    MP_TAC(SPEC `{m | ~((p:(V->num)->A) m = ring_0 r)}` th)) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; MONOMIAL; IN_ELIM_THM; SUBSET] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[monomial]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mp:V->num` STRIP_ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[monomial]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mq:V->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `monomial_mul mp mq:V->num` THEN MATCH_MP_TAC(MESON[]
   `!m. ~(ring_sum r {m} f = z) /\ ring_sum r s f = ring_sum r {m} f
        ==> ~(ring_sum r s f = z)`) THEN
  EXISTS_TAC `(mp:V->num),(mq:V->num)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_SUM_SING; RING_MUL] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC RING_SUM_SUPERSET THEN
  REWRITE_TAC[SING_SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; IN_SING] THEN
  MAP_EVERY X_GEN_TAC [`np:V->num`; `nq:V->num`] THEN
  DISCH_TAC THEN REWRITE_TAC[PAIR_EQ; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `(p:(V->num)->A) np = ring_0 r` THENL
   [ASM_SIMP_TAC[RING_MUL_LZERO]; ALL_TAC] THEN
  ASM_CASES_TAC `(q:(V->num)->A) nq = ring_0 r` THENL
   [ASM_SIMP_TAC[RING_MUL_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[MONOMIAL_LT_REFL]
   `m' = m ==> !l. ~monomial_lt l m m'`)) THEN
  DISCH_THEN(MP_TAC o SPEC `l:V->V->bool`) THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC MONOMIAL_LTE_MUL2;
    MATCH_MP_TAC MONOMIAL_LET_MUL2] THEN
  ASM_SIMP_TAC[monomial_lt; WOSET_IMP_POSET]);;

let INTEGRAL_DOMAIN_POLY_RING = prove
 (`!(r:A ring) (s:V->bool).
        integral_domain(poly_ring r s) <=> integral_domain r`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_DOMAIN_POWSER_RING]] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
    INTEGRAL_DOMAIN_MONOMORPHIC_PREIMAGE) THEN
  MESON_TAC[RING_MONOMORPHISM_POLY_CONST; RING_MONOMORPHISM_POLY_POWSER]);;

let RING_UNIT_POWSER_RING = prove
 (`!(r:A ring) (s:V->bool) p.
        ring_unit (powser_ring r s) p <=>
        p IN ring_carrier(powser_ring r s) /\
        ring_unit r (p monomial_1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_unit] THEN
  EQ_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
       [RING_CARRIER_POWSER_RING]) THEN
      SIMP_TAC[IN_ELIM_THM];
      FIRST_X_ASSUM(X_CHOOSE_THEN `q:(V->num)->A` MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC[POWSER_RING] THEN DISCH_TAC THEN
      EXISTS_TAC `(q:(V->num)->A) monomial_1` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[RING_CARRIER_POWSER_RING; IN_ELIM_THM]) THEN
      FIRST_X_ASSUM(MP_TAC o C AP_THM `monomial_1:V->num`) THEN
      ASM_REWRITE_TAC[poly_mul; poly_1; MONOMIAL_MUL_EQ_1; poly_const] THEN
      REWRITE_TAC[SET_RULE `{f x y | x = a /\ y = b} = {f a b}`] THEN
      ASM_SIMP_TAC[RING_SUM_SING; RING_MUL]];
    ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
    MP_TAC(ISPECL [`r:A ring`; `s:V->bool`] POWSER_RING_EQ) THEN
    ASM_SIMP_TAC[POWSER_RING_EQ; RING_MUL; RING_1] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[RING_CARRIER_POWSER_RING; CONJUNCT2 POWSER_RING] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
       [RING_CARRIER_POWSER_RING]) THEN
    REWRITE_TAC[IN_ELIM_THM; poly_mul; poly_1; poly_const]] THEN
  SUBGOAL_THEN
   `!(q:(V->num)->A) m.
      monomial s m /\
      (!m. p m IN ring_carrier r) /\
      (!m. q m IN ring_carrier r)
      ==> ring_sum r {m1,m2 | monomial_mul m1 m2 = m}
                     (\(m1,m2). ring_mul r (p m1) (q m2)) =
          ring_add r (ring_mul r (p monomial_1) (q m))
                     (ring_sum r ({m1,m2 | monomial_mul m1 m2 = m} DELETE
                                  (monomial_1,m))
                                 (\(m1,m2). ring_mul r (p m1) (q m2)))`
  MP_TAC THENL
   [SIMP_TAC[RING_SUM_DELETE; RING_MUL; MONOMIAL_MUL_LID;
             MONOMIAL_FINITE_DIVISORPAIRS; monomial; IN_ELIM_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(RING_RULE
     `x IN ring_carrier r /\ y IN ring_carrier r
       ==> x = ring_add r y (ring_sub r x y)`) THEN
    ASM_SIMP_TAC[RING_SUM; RING_MUL];
    SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN STRIP_TAC] THEN
  REWRITE_TAC[NOT_IMP; AND_FORALL_THM] THEN
  MP_TAC(ISPEC `(:V)` WO) THEN DISCH_THEN(X_CHOOSE_TAC `l:V->V->bool`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WOSET_MONOMIAL_LE) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [WOSET_WF]) THEN
  REWRITE_TAC[PROPERLY_MONOMIAL_LE] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP WF_REC_EXISTS) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
    REWRITE_TAC[monomial] THEN STRIP_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RING_SUM_EQ THEN
    REWRITE_TAC[IN_DELETE; IMP_CONJ; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`m1:V->num`; `m2:V->num`] THEN
    ASM_CASES_TAC `m1:V->num = monomial_1` THEN
    ASM_SIMP_TAC[PAIR_EQ; MONOMIAL_MUL_LID] THEN DISCH_TAC THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM MONOMIAL_MUL_LID] THEN
    REWRITE_TAC[MONOMIAL_LT_RMUL] THEN
    ASM_REWRITE_TAC[monomial_lt; MONOMIAL_GE_1] THEN
    ASM_MESON_TAC[MONOMIAL_MUL; MONOMIAL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:(V->num)->A`; `m:V->num`] THEN
  REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN STRIP_ASSUME_TAC o CONJUNCT1) THEN
  ASM_CASES_TAC `monomial s (m:V->num)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; MESON_TAC[RING_0]] THEN
  SUBGOAL_THEN
   `!w x z:A.
     w IN ring_carrier r /\ x IN ring_carrier r /\ z IN ring_carrier r /\
     (!z. z IN ring_carrier r
          ==> ?y. y IN ring_carrier r /\
                  ring_mul r x y = z)
     ==> ?y. y IN ring_carrier r /\
             ring_add r (ring_mul r x y) z = w`
  MATCH_MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:A`; `b:A`; `c:A`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPEC `ring_sub r a c:A`) THEN
    ASM_SIMP_TAC[RING_SUB] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN RING_TAC;
    ASM_REWRITE_TAC[RING_SUM]] THEN
  CONJ_TAC THENL [MESON_TAC[RING_0; RING_1]; ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ring_mul r b a:A` THEN
  ASM_SIMP_TAC[RING_MUL; RING_MUL_ASSOC; RING_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Decision procedure for integral domains, again proceeding indirectly      *)
(* via a totalized form (namely the ring of polynomials). Stylistically      *)
(* very like RING_RULE, but may also generate side-conditions of the form    *)
(* "~(ring_char r divides n)" for particular numerals n. As with RING_RULE   *)
(* such side-conditions get absorbed if they are there clearly in the        *)
(* antecedent, up to shallow preprocessing.                                  *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_DOMAIN_RULE =
  let INTEGRAL_DOMAIN_TOTALIZATION = prove
   (`!r:A ring.
        integral_domain r
        ==> ?r' f. integral_domain r' /\
                   ring_carrier r' = (:num#A) /\
                   ring_monomorphism(r,r') f`,
    REPEAT STRIP_TAC THEN MP_TAC(snd(EQ_IMP_RULE(ISPECL
     [`poly_ring (r:A ring) (:num#A)`; `(:num#A)`]
     ISOMORPHIC_COPY_OF_RING))) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `(:num#A)`]
          CARD_EQ_POLY_RING_INFINITE) THEN
      ASM_REWRITE_TAC[INFINITE_CROSS_UNIV; num_INFINITE] THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_EQ_TRANS) THEN
      MATCH_MP_TAC CARD_MUL_ABSORB THEN
      REWRITE_TAC[INFINITE_CROSS_UNIV; num_INFINITE;
                  RING_CARRIER_NONEMPTY] THEN
      TRANS_TAC CARD_LE_TRANS `(:A)` THEN
      SIMP_TAC[CARD_LE_SUBSET; SUBSET_UNIV] THEN
      REWRITE_TAC[GSYM CROSS_UNIV; CROSS; GSYM mul_c] THEN
      TRANS_TAC CARD_LE_TRANS `{0} *_c (:A)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
        REWRITE_TAC[CARD_MUL_LID];
        MATCH_MP_TAC CARD_LE_MUL THEN REWRITE_TAC[CARD_LE_REFL] THEN
        REWRITE_TAC[CARD_SING_LE; UNIV_NOT_EMPTY]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r':(num#A)ring` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [isomorphic_ring]) THEN
    DISCH_THEN(X_CHOOSE_TAC `f:((num#A->num)->A)->num#A`) THEN
    EXISTS_TAC `(f:((num#A->num)->A)->num#A) o poly_const (r:A ring)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `integral_domain(poly_ring (r:A ring) (:num#A))`
      MP_TAC THENL
       [ASM_REWRITE_TAC[INTEGRAL_DOMAIN_POLY_RING]; MATCH_MP_TAC EQ_IMP] THEN
      MATCH_MP_TAC ISOMORPHIC_RING_INTEGRAL_DOMAINNESS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN
      EXISTS_TAC `poly_ring (r:A ring) (:num#A)` THEN
      REWRITE_TAC[RING_MONOMORPHISM_POLY_CONST] THEN
      ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_MONOMORPHISM]]) in
  let rec ringtypes tm =
    match tm with
      Comb(Const("!",_),Abs(_,t)) | Comb(Const("?",_),Abs(_,t)) -> ringtypes t
    | Comb(Const("~",_),t) -> ringtypes t
    | Comb(Comb(Const("/\\",_),s),t) -> union (ringtypes s) (ringtypes t)
    | Comb(Comb(Const("\\/",_),s),t) -> union (ringtypes s) (ringtypes t)
    | Comb(Comb(Const("==>",_),s),t) -> union (ringtypes s) (ringtypes t)
    | Comb(Comb(Const("=",_),s),t) ->
        let ty = type_of t in
        if ty = bool_ty then union (ringtypes s) (ringtypes t)
        else [ty]
    | Comb(Comb(Const("IN",_),t),Comb(Const("ring_carrier",_),r)) ->
        [type_of t]
    | _ -> [] in
  let imp_imp_rule = GEN_REWRITE_RULE I [IMP_IMP]
  and left_exists_rule = GEN_REWRITE_RULE I [LEFT_FORALL_IMP_THM]
  and disch_disj_rule = GEN_REWRITE_RULE I [TAUT `p ==> q <=> ~p \/ q`]
  and disch_ndisj_rule = GEN_REWRITE_RULE I [TAUT `~p ==> q <=> p \/ q`] in
  let INTEGRAL_DOMAIN_WORD tm =
    let dty =
      match ringtypes tm with
       [ty] -> ty
      | _ -> failwith "INTEGRAL_DOMAIN_RULE: can't deduce which ring" in
    let rty = mk_type("ring",[dty]) in
    let rtm =
      match filter ((=) rty o type_of) (frees tm) with
        [t] -> t
      | _ -> failwith "INTEGRAL_DOMAIN_RULE: can't deduce which ring" in
     let tvs = type_vars_in_term tm in
     let dty' = mk_vartype("Z"^itlist ((^) o dest_vartype) tvs "") in
     let rty' = mk_type("ring",[dty']) in
     let avvers = variables tm in
     let rtm' = variant avvers (mk_var("r'",rty'))
     and htm = variant avvers (mk_var("h",mk_fun_ty dty dty')) in
     let hasm = list_mk_icomb "ring_monomorphism" [mk_pair(rtm,rtm'); htm] in
     let hth = ASSUME hasm in
     let th = RING_MONOMORPHIC_IMAGE_RULE hth tm in
     let utm = rand(concl th) in
     let hvs = find_terms
      (fun t -> is_comb t && rator t = htm && is_var(rand t)) utm in
     let gvs = map (fun t -> mk_var(fst(dest_var(rand t)),type_of t)) hvs in
     let vtm = subst (zip gvs hvs) utm in
     let arty = mk_type("ring",[aty]) in
     let atm =
       vsubst [mk_var("r",arty),mk_var(fst(dest_var rtm'),arty)]
              (inst[aty,dty'] vtm) in
     let th1 = RING_INTEGRAL_DOMAIN_UNIVERSAL atm in
     let th2 = INST_TYPE [dty',aty] th1 in
     let th3 = INST [rtm',mk_var("r",rty')] th2 in
     let th4 = INST (zip hvs gvs) th3 in
     let th5 = EQ_MP (SYM th) th4 in
     let xtms = subtract (hyp th5) [hasm] in
     let th6 =
       funpow (length xtms) UNDISCH
          (SUBS [SYM(MATCH_MP RING_CHAR_MONOMORPHIC_IMAGE hth)]
                (itlist DISCH xtms th5)) in
     let ueq = mk_eq(list_mk_icomb "ring_carrier" [rtm'],
                     mk_const("UNIV",[dty',aty]))
     and idt = list_mk_icomb "integral_domain" [rtm'] in
     let th7 = imp_imp_rule (DISCH idt
                 (imp_imp_rule (DISCH ueq (DISCH hasm th6)))) in
     let th8 = left_exists_rule(GEN htm th7) in
     let th9 = left_exists_rule(GEN rtm' th8) in
     let th10 = INST_TYPE [mk_type("prod",[mk_type("num",[]);dty]),dty'] th9 in
     let th11 =
      PART_MATCH rand INTEGRAL_DOMAIN_TOTALIZATION (lhand(concl th10)) in
     MP th10 (UNDISCH th11) in
  let INTEGRAL_DOMAIN_CORE =
    let pth = TAUT `p ==> q <=> (p \/ q <=> q)`
    and ptm = `p:bool` and qtm = `q:bool` in
    fun tm ->
      let negdjs,posdjs = partition is_neg (disjuncts tm) in
      let hyper,nsides = partition (is_eq o rand) negdjs
      and concs,psides = partition is_eq posdjs in
      let th0 = INTEGRAL_DOMAIN_WORD (list_mk_disj(hyper @ concs)) in
      let th1 = itlist (fun nst th -> disch_disj_rule (DISCH (rand nst) th))
                       nsides th0 in
      let th2 = itlist (fun pst th -> disch_ndisj_rule (DISCH pst th))
                       (map mk_neg psides) th1 in
      let th3 = INST[concl th2,ptm; tm,qtm] pth in
      MP (EQ_MP (SYM th3) (DISJ_ACI_RULE(rand(concl th3)))) th2 in
    let init_conv =
      TOP_DEPTH_CONV BETA_CONV THENC
      PRESIMP_CONV THENC
      CONDS_ELIM_CONV THENC
      NNFC_CONV THENC CNF_CONV THENC
      SKOLEM_CONV THENC PRENEX_CONV THENC
      GEN_REWRITE_CONV REDEPTH_CONV
       [RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THENC
      GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM DISJ_ASSOC] THENC
      GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM CONJ_ASSOC] in
    let INTEGRAL_DOMAIN_RULE_BASIC tm =
      let avs,bod = strip_forall tm in
      let th1 = init_conv bod in
      let tm' = rand(concl th1) in
      let avs',bod' = strip_forall tm' in
      let th2 = end_itlist CONJ (map INTEGRAL_DOMAIN_CORE (conjuncts bod')) in
      let th3 = EQ_MP (SYM th1) (GENL avs' th2) in
      let imps = hyp th3 in
      let th4 =
        if imps = [] then th3
        else DISCH_ALL
               (itlist PROVE_HYP (CONJUNCTS(ASSUME(list_mk_conj imps))) th3) in
      GENL avs th4 in
    fun tm ->
      let tvs = type_vars_in_term tm in
      let ty = mk_vartype("Y"^itlist ((^) o dest_vartype) tvs "") in
      let tm' = inst[ty,aty] tm in
      INST_TYPE [aty,ty] (INTEGRAL_DOMAIN_RULE_BASIC tm');;

(* ------------------------------------------------------------------------- *)
(* An elimination-based tactic for fields analogous to REAL_FIELD etc.       *)
(* When this succeeds it may in general leave subgoals about characteristic. *)
(* ------------------------------------------------------------------------- *)

let FIELD_TAC =
  let carrier_tac =
    W(fun (asl,w) ->
          let vs = filter ((=) `:A` o type_of)
                          (union (frees w) (freesl (map (concl o snd) asl))) in
          let cjs = map (fun x -> vsubst[x,`x:A`] `(x:A) IN ring_carrier f`)
                        vs in
          if cjs = [] then ALL_TAC else
          SUBGOAL_THEN (list_mk_conj cjs) STRIP_ASSUME_TAC THENL
           [REPEAT CONJ_TAC THEN RING_CARRIER_TAC; ALL_TAC])
  and rabinify_tac =
    let rabinowitsch_lemma = prove
     (`!x y:A. ~(x = y)
               ==> !r. field r /\ x IN ring_carrier r /\ y IN ring_carrier r
                        ==> ?z. z IN ring_carrier r /\
                                ring_mul r (ring_sub r x y) z = ring_1 r`,
      REPEAT STRIP_TAC THEN EXISTS_TAC `ring_inv r (ring_sub r x y):A` THEN
      ASM_SIMP_TAC[FIELD_MUL_RINV; RING_SUB_EQ_0; RING_INV; RING_SUB]) in
    REPEAT
     (FIRST_X_ASSUM(MP_TAC o ISPEC `f:A ring` o
         MATCH_MP rabinowitsch_lemma) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
        RING_CARRIER_TAC; STRIP_TAC])
  and invelim_tac =
    let is_fieldinv = can (term_match [] `ring_inv f (x:A)`)
    and pth = prove
     (`!f t:A.
            field f
            ==> t IN ring_carrier f
                ==> ring_inv f t = ring_0 f /\ t = ring_0 f \/
                    (?z. z IN ring_carrier f /\
                         ring_inv f t = z /\ ring_mul f t z = ring_1 f)`,
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
      REPEAT STRIP_TAC THEN ASM_CASES_TAC `t:A = ring_0 f` THEN
      ASM_SIMP_TAC[RING_INV_0; UNWIND_THM1; FIELD_MUL_RINV; RING_INV]) in
    W(fun (asl,w) ->
          let ctms = sort free_in (find_terms is_fieldinv w) in
          if ctms = [] then failwith "invelim_tac" else
          FIRST_ASSUM(MP_TAC o ISPEC (rand(hd ctms)) o MATCH_MP pth) THEN
          ANTS_TAC THENL [RING_CARRIER_TAC; ALL_TAC] THEN
          DISCH_THEN(DISJ_CASES_THEN2
           (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)
           (CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC
             (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC))))) in
  REWRITE_TAC[DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  TRY(MATCH_MP_TAC(MESON[] `(~(a = b) ==> F) ==> a = b`) THEN DISCH_TAC) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN
  carrier_tac THEN
  ASM_REWRITE_TAC[] THEN
  rabinify_tac THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (find_term is_eq) o concl))) THEN
  REWRITE_TAC[ring_div] THEN
  REPEAT invelim_tac THEN
  W(fun (asl,w) ->
        let th = INTEGRAL_DOMAIN_RULE w in
        MATCH_ACCEPT_TAC th ORELSE MATCH_MP_TAC th) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC;;

let FIELD_INV_EQ_0 = prove
 (`!f x:A. field f /\ x IN ring_carrier f
           ==> (ring_inv f x = ring_0 f <=> x = ring_0 f)`,
  FIELD_TAC);;

let FIELD_DIV_EQ_0 = prove
 (`!f x y:A. field f /\ x IN ring_carrier f /\ y IN ring_carrier f
           ==> (ring_div f x y = ring_0 f <=> x = ring_0 f \/ y = ring_0 f)`,
  FIELD_TAC);;

(* ------------------------------------------------------------------------- *)
(* A more direct tactic to pull division terms up, but not using any         *)
(* intelligence on the side-conditions, just finding them in the             *)
(* assumptions modulo straightforward backchaining.                          *)
(* ------------------------------------------------------------------------- *)

let RING_PULL_DIV = prove
 (`!f:A ring.
    field f
    ==> (!x y n. x IN ring_carrier f /\ y IN ring_carrier f
                 ==> ring_pow f (ring_div f x y) n =
                     ring_div f (ring_pow f x n) (ring_pow f y n)) /\
        (!x1 y1 x2 y2.
                x1 IN ring_carrier f /\ x2 IN ring_carrier f /\
                y1 IN ring_carrier f /\ y2 IN ring_carrier f
                ==> ring_div f (ring_div f x1 y1) (ring_div f x2 y2) =
                    ring_div f (ring_mul f x1 y2) (ring_mul f x2 y1)) /\
        (!x1 x2 y. x1 IN ring_carrier f /\ x2 IN ring_carrier f /\
                   y IN ring_carrier f /\ ~(y = ring_0 f)
                   ==> ring_add f (ring_div f x1 y) (ring_div f x2 y) =
                       ring_div f (ring_add f x1 x2) y /\
                       ring_sub f (ring_div f x1 y) (ring_div f x2 y) =
                       ring_div f (ring_sub f x1 x2) y /\
                       (ring_div f x1 y = ring_div f x2 y <=> x1 = x2) /\
                       ring_add f (ring_div f x1 y) x2 =
                       ring_div f (ring_add f x1 (ring_mul f x2 y)) y /\
                       ring_add f x1 (ring_div f x2 y) =
                       ring_div f (ring_add f (ring_mul f x1 y) x2) y /\
                       ring_sub f (ring_div f x1 y) x2 =
                       ring_div f (ring_sub f x1 (ring_mul f x2 y)) y /\
                       ring_sub f x1 (ring_div f x2 y) =
                       ring_div f (ring_sub f (ring_mul f x1 y) x2) y /\
                       ring_mul f (ring_div f x1 y) x2 =
                       ring_div f (ring_mul f x1 x2) y /\
                       ring_mul f x1 (ring_div f x2 y) =
                       ring_div f (ring_mul f x1 x2) y /\
                       (ring_div f x1 y = x2 <=> x1 = ring_mul f x2 y) /\
                       (x1 = ring_div f x2 y <=> ring_mul f x1 y = x2)) /\
        (!x y. x IN ring_carrier f /\ y IN ring_carrier f /\
               ~(x = ring_0 f) /\ ~(y = ring_0 f)
               ==> ~(ring_mul f x y = ring_0 f)) /\
        (!x n. x IN ring_carrier f /\ ~(x = ring_0 f)
               ==> ~(ring_pow f x n = ring_0 f))`,
  SIMP_TAC[FIELD_POW_EQ_0] THEN
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [SIMP_TAC[ring_div; RING_MUL_POW; RING_POW_INV; RING_INV];
    FIELD_TAC]);;

let RING_PULL_DIV_CONV =
  let divthms,sidethms = chop_list 13
    (CONJUNCTS(REWRITE_RULE[FORALL_AND_THM; IMP_IMP; GSYM CONJ_ASSOC;
                            RIGHT_IMP_FORALL_THM;
                            TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]
                   RING_PULL_DIV)) in
  let simpers = map (PART_MATCH (lhand o rand)) divthms
  and siders = map (PART_MATCH rand) sidethms in
  fun asm ->
    let rec sideprove t =
        try find (fun a -> concl a = t) asm with Failure _ ->
        try RING_CARRIER_RULE asm t with Failure _ ->
        tryfind (fun sfn ->
                   let th = sfn t in
                   let scs = conjuncts(fst(dest_imp(concl th))) in
                   MP th (end_itlist CONJ (map sideprove scs)))
                siders in
   fun tm ->
        tryfind (fun sfn ->
                let th = sfn tm in
                let scs = conjuncts(fst(dest_imp(concl th))) in
                MP th (end_itlist CONJ (map sideprove scs)))
        simpers;;

let RING_PULL_DIV_TAC (asl,w) =
  CONV_TAC (REDEPTH_CONV(RING_PULL_DIV_CONV (map snd asl))) (asl,w);;
