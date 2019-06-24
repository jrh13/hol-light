(* ========================================================================= *)
(* Simple formulation of rings (commutative, with 1) as type "(A)ring".      *)
(* ========================================================================= *)

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
 (`!r x y:A. x IN ring_carrier r ==> ring_sub r x x = ring_0 r`,
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

let RING_POW_ID = prove
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

let ring_unit = new_definition
 `ring_unit r (a:A) <=>
        a IN ring_carrier r /\
        ?x. x IN ring_carrier r /\ ring_mul r a x = ring_1 r`;;

let ring_associates = new_definition
 `ring_associates r (a:A) b <=> ring_divides r a b /\ ring_divides r b a`;;

let ring_coprime = new_definition
 `ring_coprime r (a:A,b) <=>
        !d. ring_divides r d a /\ ring_divides r d b ==> ring_unit r d`;;

let ring_inv = new_definition
 `ring_inv r (a:A) =
        if ring_unit r a
        then @x. x IN ring_carrier r /\ ring_mul r a x = ring_1 r
        else ring_0 r`;;

let ring_div = new_definition
 `ring_div r (a:A) b = ring_mul r a (ring_inv r b)`;;

let RING_UNIT_IN_CARRIER = prove
 (`!r a:A. ring_unit r a ==> a IN ring_carrier r`,
  SIMP_TAC[ring_unit]);;

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

let RING_INV_MUL = prove
 (`!r a b:A.
        ring_unit r a /\ ring_unit r b
        ==> ring_inv r (ring_mul r a b) =
            ring_mul r (ring_inv r a) (ring_inv r b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_RINV_UNIQUE THEN
  ASM_SIMP_TAC[RING_MUL; RING_INV; RING_UNIT_IN_CARRIER] THEN
  TRANS_TAC EQ_TRANS
   `ring_mul r (ring_mul r a (ring_inv r a))
               (ring_mul r b (ring_inv r b)):A` THEN
  CONJ_TAC THENL
   [ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
        [RING_MUL; RING_INV; RING_MUL_AC; RING_UNIT_IN_CARRIER];
    ASM_SIMP_TAC[RING_MUL_RINV; RING_MUL_LID; RING_1; RING_UNIT_IN_CARRIER]]);;

let RING_INV_INV = prove
 (`!r a:A. ring_unit r a ==> ring_inv r (ring_inv r a) = a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_RINV_UNIQUE THEN
  ASM_SIMP_TAC[RING_INV; RING_UNIT_IN_CARRIER; RING_MUL_LINV]);;

let RING_UNIT_DIVIDES = prove
 (`!r a:A. ring_unit r a <=> ring_divides r a (ring_1 r)`,
  REWRITE_TAC[ring_unit; ring_divides] THEN MESON_TAC[RING_1]);;

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

let RING_UNIT_DIVIDES_ANY = prove
 (`!r a b:A. ring_unit r a /\ b IN ring_carrier r ==> ring_divides r a b`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ring_unit; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[ring_divides] THEN
  EXISTS_TAC `ring_mul r c b:A` THEN
  ASM_SIMP_TAC[RING_MUL; RING_MUL_ASSOC; RING_MUL_LID]);;

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

let RING_DIVIDES_NEG = prove
 (`!r a d:A. ring_divides r d a ==> ring_divides r d (ring_neg r a)`,
  MESON_TAC[RING_SUB_LZERO; RING_DIVIDES_SUB; ring_divides; RING_0;
            RING_DIVIDES_0]);;

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

let RING_DIVIDES_LMUL2 = prove
 (`!r d a x:A.
        x IN ring_carrier r /\ d IN ring_carrier r /\
        ring_divides r (ring_mul r x d) a
        ==> ring_divides r d a`,
  REWRITE_TAC[ring_divides] THEN MESON_TAC[RING_MUL_AC; RING_MUL]);;

let RING_DIVIDES_RMUL2 = prove
 (`!r d a x:A.
        x IN ring_carrier r /\ d IN ring_carrier r /\
        ring_divides r (ring_mul r d x) a
        ==> ring_divides r d a`,
  REWRITE_TAC[ring_divides] THEN MESON_TAC[RING_MUL_AC; RING_MUL]);;

let RING_ASSOCIATES_IN_CARRIER = prove
 (`!r a a':A. ring_associates r a a'
              ==> a IN ring_carrier r /\ a' IN ring_carrier r`,
  SIMP_TAC[ring_associates; ring_divides]);;

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

let RING_ZERODIVISOR_0 = prove
 (`!r:A ring. ring_zerodivisor r (ring_0 r) <=> ~trivial_ring r`,
  REWRITE_TAC[ring_zerodivisor; TRIVIAL_RING_SUBSET; RING_0] THEN
  REWRITE_TAC[SUBSET; IN_SING] THEN MESON_TAC[RING_MUL_LZERO]);;

let RING_REGULAR_0 = prove
 (`!r:A ring. ring_regular r (ring_0 r) <=> trivial_ring r`,
  REWRITE_TAC[ring_regular; RING_ZERODIVISOR_0; RING_0]);;

let RING_REGULAR_1 = prove
 (`!r:A ring. ring_regular r (ring_1 r)`,
  REWRITE_TAC[ring_zerodivisor; ring_regular] THEN
  MESON_TAC[RING_MUL_LID; RING_1]);;

let RING_REGULAR_MUL = prove
 (`!r x y:A.
        ring_regular r x /\
        ring_regular r y
        ==> ring_regular r (ring_mul r x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_regular; ring_zerodivisor] THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier r` THEN
  ASM_CASES_TAC `(y:A) IN ring_carrier r` THEN
  ASM_SIMP_TAC[RING_MUL] THEN
  ASM_MESON_TAC[GSYM RING_MUL_ASSOC; RING_MUL]);;

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
  MESON_TAC[RING_ASSOCIATES_DIVIDES; RING_ASSOCIATES_REFL; ring_divides]);;

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
 (`!r k (u:(A->bool)->bool).
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

let RING_SUB_SUBRING_GENERATED = prove
 (`!r s:A->bool. ring_sub (subring_generated r s) = ring_sub r`,
  REWRITE_TAC[FUN_EQ_THM; ring_sub; SUBRING_GENERATED]);;

let RING_POW_SUBRING_GENERATED = prove
 (`!r s:A->bool. ring_pow (subring_generated r s) = ring_pow r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; SUBRING_GENERATED]);;

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

let FINITE_SUBRING_GENERATED = prove
 (`!r s:A->bool.
        FINITE(ring_carrier r)
        ==> FINITE(ring_carrier(subring_generated r s))`,
  MESON_TAC[FINITE_SUBSET; RING_CARRIER_SUBRING_GENERATED_SUBSET]);;

let SUBRING_GENERATED_SUBSET_CARRIER = prove
 (`!r h:A->bool.
     ring_carrier r INTER h SUBSET ring_carrier(subring_generated r h)`,
  REWRITE_TAC[subring_of; SUBRING_GENERATED; SUBSET_INTERS] THEN SET_TAC[]);;

let CARRIER_SUBRING_GENERATED_SUBRING = prove
 (`!r h:A->bool.
        h subring_of r ==> ring_carrier (subring_generated r h) = h`,
  REWRITE_TAC[subring_of; SUBRING_GENERATED; INTERS_GSPEC] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[SET_RULE `h SUBSET g ==> g INTER h = h`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL [GEN_REWRITE_TAC I [SUBSET]; ASM SET_TAC[]] THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `h:A->bool`) THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

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

let SUBRING_GENERATED_IDEMPOT = prove
 (`!r s:A->bool.
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
 (`!r k (u:(A->bool)->bool).
        ~(u = {}) /\
        (!h. h IN u ==> ring_ideal r h) /\
        (!g h. g IN u /\ h IN u ==> g SUBSET h \/ h SUBSET g)
        ==> ring_ideal r (UNIONS u)`,
  REWRITE_TAC[ring_ideal] THEN SET_TAC[]);;

let RING_IDEAL_IMP_SUBSET = prove
 (`!r s:A->bool. ring_ideal r s ==> s SUBSET ring_carrier r`,
  SIMP_TAC[ring_ideal]);;

let RING_IDEAL_IMP_NONEMPTY = prove
 (`!r s:A->bool. ring_ideal r s ==> ~(s = {})`,
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

let CARRIER_RING_IDEAL = prove
 (`!r:A ring. ring_ideal r (ring_carrier r)`,
  REWRITE_TAC[ring_ideal; SUBSET_REFL] THEN
  SIMP_TAC[RING_0; RING_NEG; RING_ADD; RING_MUL]);;

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
 (`!r s t u:A->bool.
        s SUBSET ring_carrier r /\ t SUBSET ring_carrier r
        ==> ring_setadd r s t = ring_setadd r t s`,
  REWRITE_TAC[SUBSET; EXTENSION; IN_ELIM_THM; ring_setadd] THEN
  MESON_TAC[RING_ADD_SYM]);;

let RING_SETMUL_SYM = prove
 (`!r s t u:A->bool.
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
 (`!r j k:A->bool.
        s SUBSET ring_carrier r /\ ring_0 r IN t
        ==> s SUBSET ring_setadd r s t`,
  REWRITE_TAC[SUBSET; ring_setadd; IN_ELIM_THM] THEN
  MESON_TAC[RING_ADD_RZERO]);;

let RING_SETADD_SUPERSET_RIGHT = prove
 (`!r j k:A->bool.
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
  REWRITE_TAC[CARRIER_RING_IDEAL; INTER_SUBSET]);;

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
        ==> !x. x IN (ideal_generated r s) ==> P x`,
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

let IDEAL_GENERATED_SUBSET = prove
 (`!r h:A->bool.
         ideal_generated r h SUBSET ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ideal_generated] THEN
  MATCH_MP_TAC(SET_RULE `a IN s ==> INTERS s SUBSET a`) THEN
  REWRITE_TAC[IN_ELIM_THM; CARRIER_RING_IDEAL; INTER_SUBSET]);;

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
  SIMP_TAC[IDEAL_GENERATED_RING_IDEAL; CARRIER_RING_IDEAL] THEN
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
        a IN ring_carrier r /\ ~(a = ring_0 r) /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_mul r a x = ring_mul r a y <=> x = y)`,
  MESON_TAC[INTEGRAL_DOMAIN_MUL_LCANCEL]);;

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
        a IN ring_carrier r /\ ~(a = ring_0 r) /\
        x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_mul r x a = ring_mul r y a <=> x = y)`,
  MESON_TAC[INTEGRAL_DOMAIN_MUL_LCANCEL_EQ; RING_MUL_SYM]);;

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
 (`!(G1:A ring) (G2:B ring) h1 h2.
        (h1 CROSS h2) subring_of (prod_ring G1 G2) <=>
        h1 subring_of G1 /\ h2 subring_of G2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[subring_of; FORALL_PAIR_THM; PROD_RING; IN_CROSS] THEN
  REWRITE_TAC[SUBSET_CROSS] THEN SET_TAC[]);;

let PROD_RING_SUBRING_GENERATED = prove
 (`!(G1:A ring) (G2:B ring) h1 h2.
        h1 subring_of G1 /\ h2 subring_of G2
        ==> (prod_ring (subring_generated G1 h1) (subring_generated G2 h2) =
             subring_generated (prod_ring G1 G2) (h1 CROSS h2))`,
  SIMP_TAC[RINGS_EQ; CONJUNCT2 PROD_RING; CONJUNCT2 SUBRING_GENERATED] THEN
  SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING;
           CROSS_SUBRING_OF_PROD_RING; PROD_RING]);;

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

let RING_HOMOMORPHISM_ZERO = prove
 (`!r:A ring. ring_homomorphism (r,r) (\x. x)`,
  REWRITE_TAC[ring_homomorphism; IMAGE_ID; SUBSET_REFL]);;

let RING_MONOMORPHISM_ZERO = prove
 (`!r:A ring. ring_monomorphism (r,r) (\x. x)`,
  SIMP_TAC[ring_monomorphism; RING_HOMOMORPHISM_ZERO]);;

let RING_EPIMORPHISM_ZERO = prove
 (`!r:A ring. ring_epimorphism (r,r) (\x. x)`,
  SIMP_TAC[ring_epimorphism; RING_HOMOMORPHISM_ZERO; IMAGE_ID]);;

let RING_ISOMORPHISMS_ZERO = prove
 (`!r:A ring. ring_isomorphisms (r,r) ((\x. x),(\x. x))`,
  REWRITE_TAC[ring_isomorphisms; RING_HOMOMORPHISM_ZERO]);;

let RING_ISOMORPHISM_ZERO = prove
 (`!r:A ring. ring_isomorphism (r,r) (\x. x)`,
  REWRITE_TAC[ring_isomorphism] THEN MESON_TAC[RING_ISOMORPHISMS_ZERO]);;

let RING_HOMOMORPHISM_COMPOSE = prove
 (`!G1 G2 G3 (f:A->B) (g:B->C).
        ring_homomorphism(G1,G2) f /\ ring_homomorphism(G2,G3) g
        ==> ring_homomorphism(G1,G3) (g o f)`,
  SIMP_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM]);;

let RING_MONOMORPHISM_COMPOSE = prove
 (`!G1 G2 G3 (f:A->B) (g:B->C).
        ring_monomorphism(G1,G2) f /\ ring_monomorphism(G2,G3) g
        ==> ring_monomorphism(G1,G3) (g o f)`,
  REWRITE_TAC[ring_monomorphism; ring_homomorphism; INJECTIVE_ON_ALT] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM]);;

let RING_MONOMORPHISM_COMPOSE_REV = prove
 (`!(f:A->B) (g:B->C) A B C.
        ring_homomorphism(A,B) f /\ ring_homomorphism(B,C) g /\
        ring_monomorphism(A,C) (g o f)
        ==> ring_monomorphism(A,B) f`,
  REWRITE_TAC[ring_monomorphism; o_THM] THEN MESON_TAC[]);;

let RING_EPIMORPHISM_COMPOSE = prove
 (`!G1 G2 G3 (f:A->B) (g:B->C).
        ring_epimorphism(G1,G2) f /\ ring_epimorphism(G2,G3) g
        ==> ring_epimorphism(G1,G3) (g o f)`,
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

let RING_HOMOMORPHISM_BETWEEN_SUBRINGS = prove
 (`!r r' g h (f:A->B).
      ring_homomorphism(r,r') f /\ IMAGE f g SUBSET h
      ==> ring_homomorphism(subring_generated r g,subring_generated r' h) f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN] THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_FROM_SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p /\ q`] THEN
  MATCH_MP_TAC SUBRING_GENERATED_INDUCT THEN RULE_ASSUM_TAC
   (REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  MP_TAC(REWRITE_RULE[SUBSET] (ISPECL [`r:A ring`; `g:A->bool`]
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

let SUBRING_OF_HOMOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B).
        ring_homomorphism (r,r') f /\ h subring_of r
        ==> IMAGE f h subring_of r'`,
  REWRITE_TAC[ring_homomorphism; subring_of] THEN SET_TAC[]);;

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

let RING_MONOMORPHISM_EPIMORPHISM = prove
 (`!r r' f:A->B.
        ring_monomorphism (r,r') f /\ ring_epimorphism (r,r') f <=>
        ring_isomorphism (r,r') f`,
  REWRITE_TAC[RING_ISOMORPHISM; ring_monomorphism; ring_epimorphism] THEN
  MESON_TAC[]);;

let RING_ISOMORPHISM_IMP_MONOMORPHISM = prove
 (`!r r' (f:A->B).
        ring_isomorphism (r,r') f ==> ring_monomorphism (r,r') f`,
  SIMP_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM]);;

let RING_ISOMORPHISM_IMP_EPIMORPHISM = prove
 (`!r r' (f:A->B).
        ring_isomorphism (r,r') f ==> ring_epimorphism (r,r') f`,
  SIMP_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM]);;

let RING_MONOMORPHISM_IMP_HOMOMORPHISM = prove
 (`!(f:A->B) r r'. ring_monomorphism(r,r') f ==> ring_homomorphism(r,r') f`,
  SIMP_TAC[ring_monomorphism]);;

let RING_EPIMORPHISM_IMP_HOMOMORPHISM = prove
 (`!(f:A->B) r r'. ring_epimorphism(r,r') f ==> ring_homomorphism(r,r') f`,
  SIMP_TAC[ring_epimorphism]);;

let RING_ISOMORPHISM_IMP_HOMOMORPHISM = prove
 (`!(f:A->B) r r'. ring_isomorphism(r,r') f ==> ring_homomorphism(r,r') f`,
  SIMP_TAC[RING_ISOMORPHISM]);;

let RING_ISOMORPHISMS_BETWEEN_SUBRINGS = prove
 (`!r r' g h (f:A->B) f'.
      ring_isomorphisms(r,r') (f,f') /\
      IMAGE f g SUBSET h /\ IMAGE f' h SUBSET g
      ==> ring_isomorphisms (subring_generated r g,subring_generated r' h)
                             (f,f')`,
  SIMP_TAC[ring_isomorphisms; RING_HOMOMORPHISM_BETWEEN_SUBRINGS] THEN
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
 (`!G1 G2 G3 (f1:A->B) (f2:B->C) g1 g2.
        ring_isomorphisms(G1,G2) (f1,g1) /\ ring_isomorphisms(G2,G3) (f2,g2)
        ==> ring_isomorphisms(G1,G3) (f2 o f1,g1 o g2)`,
  SIMP_TAC[ring_isomorphisms; ring_homomorphism;
           SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM]);;

let RING_ISOMORPHISM_COMPOSE = prove
 (`!G1 G2 G3 (f:A->B) (g:B->C).
        ring_isomorphism(G1,G2) f /\ ring_isomorphism(G2,G3) g
        ==> ring_isomorphism(G1,G3) (g o f)`,
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

let RING_ISOMORPHISMS_PROD_RING_SWAP = prove
 (`!(r:A ring) (r':B ring).
        ring_isomorphisms (prod_ring r r',prod_ring r' r)
                           ((\(x,y). y,x),(\(y,x). x,y))`,
  REWRITE_TAC[ring_isomorphisms; FORALL_PAIR_THM] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_PAIRWISE; o_DEF; LAMBDA_PAIR] THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] RING_HOMOMORPHISM_OF_FST;
              REWRITE_RULE[o_DEF] RING_HOMOMORPHISM_OF_SND] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_ZERO]);;

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
  REWRITE_TAC[RING_ISOMORPHISM_ZERO]);;

let ISOMORPHIC_RING_SYM = prove
 (`!(r:A ring) (r':B ring). r isomorphic_ring r' <=> r' isomorphic_ring r`,
  REWRITE_TAC[isomorphic_ring; ring_isomorphism] THEN
  MESON_TAC[RING_ISOMORPHISMS_SYM]);;

let ISOMORPHIC_RING_TRANS = prove
 (`!(G1:A ring) (G2:B ring) (G3:C ring).
        G1 isomorphic_ring G2 /\ G2 isomorphic_ring G3
        ==> G1 isomorphic_ring G3`,
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

let ISOMORPHIC_RING_PROD_RINGS = prove
 (`!(r:A ring) (r':B ring) (r':C ring) (r'':D ring).
        r isomorphic_ring r' /\ r' isomorphic_ring r''
        ==> (prod_ring r r') isomorphic_ring (prod_ring r' r'')`,
  REWRITE_TAC[isomorphic_ring; ring_isomorphism; RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM RING_ISOMORPHISMS_PAIRED2] THEN MESON_TAC[]);;

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

let ISOMORPHIC_RING_CARD_EQ = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> ring_carrier r =_c ring_carrier r'`,
  REWRITE_TAC[isomorphic_ring; GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[eq_c; ring_monomorphism; ring_epimorphism] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

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
           NOT_INSERT_EMPTY; CARRIER_RING_IDEAL]);;

let RING_COSET_EQ = prove
 (`!r t x y:A.
        ring_ideal r j /\ x IN ring_carrier r /\ y IN ring_carrier r
        ==> (ring_coset r j x = ring_coset r j y <=> ring_sub r x y IN j)`,
  SIMP_TAC[RING_SETADD_RCANCEL_SET; RING_COSET_SETADD]);;

let RING_COSET_EQ_IDEAL = prove
 (`!r j x:A.
        ring_ideal r j /\ x IN ring_carrier r
        ==> (ring_coset r j x = j <=> x IN j)`,
  SIMP_TAC[RING_COSET_SETADD; RING_SETADD_LSUBSET_EQ; SING_SUBSET] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY]);;

let RING_COSET_EQ_EMPTY = prove
 (`!r j x:A. ring_coset r j x = {} <=> j = {}`,
  REWRITE_TAC[RING_COSET_SETADD; RING_SETADD_EQ_EMPTY; NOT_INSERT_EMPTY]);;

let RING_COSET_NONEMPTY = prove
 (`!r j x:A. ring_ideal r j ==> ~(ring_coset r j x = {})`,
  REWRITE_TAC[RING_COSET_EQ_EMPTY; RING_IDEAL_IMP_NONEMPTY]);;

let IN_RING_COSET_SELF = prove
 (`!r j x:A.
      ring_ideal r j /\ x IN ring_carrier r ==> x IN ring_coset r j x`,
  REWRITE_TAC[ring_ideal; RING_COSET_SETADD; ring_setadd;
              IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[RING_ADD_RZERO]);;

let UNIONS_RING_COSETS = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> UNIONS {ring_coset r j x |x| x IN ring_carrier r} =
            ring_carrier r`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[RING_COSET; RING_IDEAL_IMP_SUBSET] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; SUBSET] THEN
  ASM_MESON_TAC[IN_RING_COSET_SELF]);;

let RING_COSETS_EQ = prove
 (`!r j x y:A.
        ring_ideal r j /\ x IN ring_carrier r /\ y IN ring_carrier r
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
  RULE_ASSUM_TAC(REWRITE_RULE[ring_ideal; SUBSET]) THEN
  REWRITE_TAC[ring_sub] THEN
  ASM_SIMP_TAC[GSYM RING_ADD_ASSOC; RING_ADD_RNEG; RING_ADD_RZERO] THEN
  DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_ADD_SYM o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[RING_ADD; RING_NEG]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[RING_ADD_ASSOC; RING_SUB; RING_ADD; RING_NEG; RING_ADD_LNEG]);;

let DISJOINT_RING_COSETS = prove
 (`!r j x y:A.
        ring_ideal r j /\ x IN ring_carrier r /\ y IN ring_carrier r
        ==> (DISJOINT (ring_coset r j x) (ring_coset r j y) <=>
             ~(ring_coset r j x = ring_coset r j y))`,
  SIMP_TAC[RING_COSETS_EQ]);;

let IMAGE_RING_COSET_SWITCH = prove
 (`!r j x y:A.
        ring_ideal r j /\ x IN ring_carrier r /\ y IN ring_carrier r
        ==> IMAGE (\a. ring_add r (ring_sub r y x) a)
                  (ring_coset r j x) =
            ring_coset r j y`,
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
   `ring_setadd r {ring_sub r y x:A} (ring_coset r j x)` THEN
  CONJ_TAC THENL [REWRITE_TAC[ring_setadd] THEN SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
  REWRITE_TAC[RING_COSET_SETADD; ring_sub] THEN
  ASM_SIMP_TAC[RING_SETADD_ASSOC; RING_SETADD; SING_SUBSET;
               RING_ADD; RING_NEG; RING_SETADD_SING; GSYM RING_ADD_ASSOC;
               RING_ADD_LNEG; RING_ADD_RZERO]);;

let CARD_EQ_RING_COSETS = prove
 (`!r j x y:A.
        ring_ideal r j /\ x IN ring_carrier r /\ y IN ring_carrier r
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
  ASM_MESON_TAC[RING_SUB; SUBSET; RING_COSET; RING_IDEAL_IMP_SUBSET]);;

let CARD_EQ_RING_COSET_IDEAL = prove
 (`!r j x:A.
        ring_ideal r j /\ x IN ring_carrier r
        ==> ring_coset r j x =_c j`,
 MESON_TAC[CARD_EQ_RING_COSETS; RING_0; RING_COSET_0;
           RING_IDEAL_IMP_SUBSET]);;

let LAGRANGE_THEOREM_RING_EXPLICIT = prove
 (`!r j:A->bool.
        FINITE(ring_carrier r) /\ ring_ideal r j
        ==> CARD {ring_coset r j x |x| x IN ring_carrier r} * CARD j =
            CARD(ring_carrier r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(j:A->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; ring_ideal]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [SYM(MATCH_MP UNIONS_RING_COSETS th)]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNIONS o rand o snd) THEN
  ASM_REWRITE_TAC[SIMPLE_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE] THEN
  ASM_SIMP_TAC[GSYM DISJOINT; DISJOINT_RING_COSETS] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; RING_COSET; ring_ideal];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[GSYM NSUM_CONST; FINITE_IMAGE] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CARD_EQ_CARD_IMP THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CARD_EQ_RING_COSET_IDEAL]);;

let LAGRANGE_THEOREM_RING_IDEAL = prove
 (`!r j:A->bool.
        FINITE(ring_carrier r) /\ ring_ideal r j
        ==> (CARD j) divides CARD(ring_carrier r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP LAGRANGE_THEOREM_RING_EXPLICIT) THEN
  NUMBER_TAC);;

let RING_SETADD_PROD_RING = prove
 (`!(G1:A ring) (G2:B ring) s1 s2 t1 t2.
        ring_setadd (prod_ring G1 G2) (s1 CROSS s2) (t1 CROSS t2) =
        (ring_setadd G1 s1 t1) CROSS (ring_setadd G2 s2 t2)`,
  REWRITE_TAC[ring_setadd; CROSS; PROD_RING; SET_RULE
   `{f x y | x IN {s a b | P a b} /\ y IN {t c d | Q c d}} =
    {f (s a b) (t c d) | P a b /\ Q c d}`] THEN
  SET_TAC[]);;

let RING_COSET_PROD_RING = prove
 (`!G1 G2 h1 h2 (x1:A) (x2:B).
        ring_coset (prod_ring G1 G2) (h1 CROSS h2) (x1,x2) =
        (ring_coset G1 h1 x1) CROSS (ring_coset G2 h2 x2)`,
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
        a IN ring_carrier r /\ ring_ideal r j
        ==> ring_setneg r (ring_coset r j a) = ring_coset r j (ring_neg r a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_coset] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; ring_setneg; FORALL_IN_GSPEC; IMP_CONJ;
              RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[SET_RULE `{f x | x IN {g a | P a}} = {f (g a) | P a}`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `ring_neg r x:A` THEN
  ASM_SIMP_TAC[IN_RING_IDEAL_NEG] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
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

let RING_KERNEL_RIGHT_COSET = prove
 (`!r j:A->bool.
        ring_ideal r j
        ==> ring_kernel(r,quotient_ring r j) (ring_coset r j) = j`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ring_kernel; QUOTIENT_RING_0] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[RING_COSET_EQ_IDEAL; RING_IDEAL_IMP_SUBSET; SUBSET]);;

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
