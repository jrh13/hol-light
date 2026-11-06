(* ========================================================================= *)
(* Integral elements of ring extensions, integral closure and integrally     *)
(* closed domains.                                                           *)
(*                                                                           *)
(*   integral_element (r,s) h x   <=> x is a root of a monic polynomial      *)
(*                                    over r, mapped into s by h             *)
(*   integrally_closed r          <=> domain, integrally closed in its       *)
(*                                    fraction ring                          *)
(*                                                                           *)
(* The integral closure of r in s along h is the set                         *)
(* {x | integral_element (r,s) h x}.                                         *)
(*                                                                           *)
(* Main results: the determinant trick over any finite index set             *)
(* (INTEGRAL_ELEMENT_FINITE_MODULE, via ring_charpoly and                    *)
(* RING_DET_DEPENDENT_COLUMNS_MUL of ring_det.ml), the explicit form         *)
(* INTEGRAL_ELEMENT_EXPLICIT, closure under the ring operations              *)
(* (INTEGRAL_CLOSURE_SUBRING), images and preimages, transitivity            *)
(* (INTEGRAL_ELEMENT_TRANS, INTEGRAL_CLOSURE_IDEMPOT), integral over a field *)
(* = algebraic, the characterization INTEGRALLY_CLOSED_ALT (a domain is      *)
(* integrally closed iff every homogenized monic relation a^n + sum c_i a^i  *)
(* b^(n-i) = 0 with b nonzero forces b to divide a), hence UFDs, PIDs,       *)
(* fields and the integers are integrally closed, integral closures in       *)
(* fields are integrally closed (INTEGRALLY_CLOSED_INTEGRAL_CLOSURE) and     *)
(* INTEGRALLY_CLOSED_DIVIDES; integral elements of the prime subfield in     *)
(* characteristic 0 are integers (INTEGRAL_ELEMENT_PRIME_SUBFIELD).          *)
(* Localizations of integrally closed domains at multiplicative sets not     *)
(* containing 0 are integrally closed (INTEGRALLY_CLOSED_LOCALIZATION; a     *)
(* generic lemma: RING_LOCALIZATION_COMMON_DENOMINATOR). Route:              *)
(* module-finiteness is expressed with ring_span of fieldtheory.ml (spans of *)
(* finite sets over any ring) and the stabilizers of spans; adjoining one    *)
(* root of a monic relation (INTEGRAL_SPAN_ADJOIN) gives the closure         *)
(* properties and transitivity.                                              *)
(*                                                                           *)
(* Integrality over any ring r, h : r -> k into a field and g : k -> l a     *)
(* field extension: an element x of l integral over r along g o h is         *)
(* algebraic over k, and the coefficients of its minimal polynomial over k   *)
(* are integral over r (INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL, from            *)
(* INTEGRAL_ELEMENT_MONIC_DIVISOR: the coefficients of a monic divisor       *)
(* over k of a monic polynomial over r are integral over r); in a finite     *)
(* extension its trace and norm are integral over r                          *)
(* (ALGEBRA_TRACE_NORM_INTEGRAL). Over an intermediate ring the element      *)
(* stays integral (INTEGRAL_ELEMENT_INTERMEDIATE).                           *)
(*                                                                           *)
(* Integrally closed domains. If k is a field of fractions of r along h      *)
(* (field_of_fractions (r,k) h), r is integrally closed iff every element of *)
(* k integral over r lies in h(r) (INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS).    *)
(* Then, for r integrally closed:                                            *)
(*                                                                           *)
(*   x algebraic over k is integral over r iff the coefficients of its       *)
(*   minimal polynomial over k lie in h(r)                                   *)
(*   (INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL);                                 *)
(*   in a finite extension the trace and the norm of an integral element     *)
(*   lie in h(r) (INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM);                     *)
(*   an integral x has an integral inverse iff its norm is h(u) for a unit   *)
(*   u of r (INTEGRALLY_CLOSED_UNIT_NORM), that is, x is a unit of the       *)
(*   integral closure iff its norm is the image of a unit of r               *)
(*   (INTEGRAL_CLOSURE_UNIT_NORM).                                           *)
(*                                                                           *)
(* Routes for these: the coefficients of a monic divisor are integral since  *)
(* its roots in a splitting field are roots of the monic polynomial over r   *)
(* and the integral elements form a subring (POLY_SPLITS_IN_SUBRING_MONIC).  *)
(* The trace and norm are -[l:k(x)] c_(d-1) and ((-1)^d c_0)^[l:k(x)] for    *)
(* the minimal polynomial X^d + c_(d-1) X^(d-1) + ... + c_0                  *)
(* (ALGEBRA_TRACE_MINIMAL_POLYNOMIAL, ALGEBRA_NORM_MINIMAL_POLYNOMIAL of     *)
(* Library/fieldtheory.ml). For the unit criterion: if N(x) = h(u) then the  *)
(* constant coefficient c_0 = h(a_0) of the minimal polynomial is a unit,    *)
(* and x^d + ... + c_0 = c_0 + x s (RING_MONIC_RELATION_FACTOR of            *)
(* Library/ringtheory.ml) gives the integral inverse -h(a_0)^-1 s; the       *)
(* converse is N(x) N(y) = N(1) = 1.                                         *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (POLY_EXTEND_MONIC_UNIVARIATE,                *)
(* RING_MONIC_RELATION_FACTOR), Library/fieldtheory.ml (ring_span,           *)
(* algebraic_over, field_extension, subfield_generated, minimal              *)
(* polynomials), Library/ring_det.ml (ring_det, ring_charpoly,               *)
(* algebra_trace, algebra_norm).                                             *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_det.ml";;

let integral_element = new_definition
 `integral_element (r:A ring,r':B ring) (h:A->B) (x:B) <=>
  x IN ring_carrier r' /\
  ?p. p IN ring_carrier(poly_ring r (:1)) /\
      monic r p /\
      poly_extend (r,r') h (\v:1. x) p = ring_0 r'`;;

let integrally_closed = new_definition
 `integrally_closed (r:A ring) <=>
  integral_domain r /\
  !x. integral_element
       (r,fraction_ring r) (ring_fractionate r {a | ring_regular r a}) x
      ==> x IN IMAGE (ring_fractionate r {a | ring_regular r a})
                      (ring_carrier r)`;;

(* ------------------------------------------------------------------------- *)
(* Basic closure properties.                                                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_ELEMENT_IN_CARRIER = prove
 (`!r:A ring r':B ring h x.
        integral_element (r,r') h x ==> x IN ring_carrier r'`,
  SIMP_TAC[integral_element]);;

let INTEGRAL_ELEMENT_IMAGE = prove
 (`!r:A ring r':B ring h a.
        ring_homomorphism(r,r') h /\ a IN ring_carrier r
        ==> integral_element (r,r') h (h a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral_element] THEN
  SUBGOAL_THEN `(h:A->B) a IN ring_carrier r'` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ASM_REWRITE_TAC[]] THEN
  EXISTS_TAC `poly_sub r (poly_var r one) (poly_const r (a:A))` THEN
  ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR;
               RING_POLYNOMIAL_CONST; MONIC_X_MINUS_A; POLY_EXTEND_SUB;
               POLY_EXTEND_VAR; POLY_EXTEND_CONST; RING_SUB_REFL]);;

let INTEGRAL_ELEMENT_0 = prove
 (`!r:A ring r':B ring h.
        ring_homomorphism(r,r') h
        ==> integral_element (r,r') h (ring_0 r')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_HOMOMORPHISM_0) THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_IMAGE THEN ASM_REWRITE_TAC[RING_0]);;

let INTEGRAL_ELEMENT_1 = prove
 (`!r:A ring r':B ring h.
        ring_homomorphism(r,r') h
        ==> integral_element (r,r') h (ring_1 r')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_HOMOMORPHISM_1) THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_IMAGE THEN ASM_REWRITE_TAC[RING_1]);;

(* ------------------------------------------------------------------------- *)
(* The monic relation of an integral element, with coefficients in r.        *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_ELEMENT_RELATION = prove
 (`!r:A ring r':B ring h x.
        ring_homomorphism(r,r') h /\ integral_element (r,r') h x
        ==> ?n c. (!i. i < n ==> c i IN ring_carrier r) /\
                  ring_add r' (ring_pow r' x n)
                    (ring_sum r' {i | i < n}
                       (\i. ring_mul r' (h(c i)) (ring_pow r' x i))) =
                  ring_0 r'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integral_element] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`poly_deg r (p:(1->num)->A)`; `\i. coeff i (p:(1->num)->A)`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_EXTEND_MONIC_UNIVARIATE THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The determinant trick: an element stabilizing a finitely generated module *)
(* that contains 1 is a root of the characteristic polynomial of its action. *)
(* INTEGRAL_ELEMENT_MODULE is the case t = {i | i < k} with e 0 = 1.         *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_ELEMENT_FINITE_MODULE = prove
 (`!r:A ring r':B ring h x (t:K->bool) (e:K->B).
        ring_homomorphism(r,r') h /\ FINITE t /\ x IN ring_carrier r' /\
        (!i. i IN t ==> e i IN ring_carrier r') /\
        (?c. (!i. i IN t ==> c i IN ring_carrier r) /\
             ring_1 r' = ring_sum r' t (\i. ring_mul r' (h(c i)) (e i))) /\
        (!j. j IN t
             ==> ?c. (!i. i IN t ==> c i IN ring_carrier r) /\
                     ring_mul r' x (e j) =
                     ring_sum r' t (\i. ring_mul r' (h(c i)) (e i)))
        ==> integral_element (r,r') h x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
   [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:K->K->A` THEN DISCH_THEN(LABEL_TAC "m") THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:K->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(!i j. i IN t /\ j IN t ==> (m:K->K->A) i j IN ring_carrier r) /\
    (!i j. i IN t /\ j IN t ==> (h:A->B)(m i j) IN ring_carrier r') /\
    (!i. i IN t ==> h((c:K->A) i) IN ring_carrier r')`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  REWRITE_TAC[integral_element] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `ring_charpoly r t (m:K->K->A)` THEN
  ASM_SIMP_TAC[RING_CHARPOLY; RING_CHARPOLY_MONIC; RING_CHARPOLY_EXTEND] THEN
  ABBREV_TAC
   `d = ring_det r' (t:K->bool)
          (\i j. ring_sub r' (if i = j then x else ring_0 r')
                             ((h:A->B)(m i j)))` THEN
  SUBGOAL_THEN `!i. i IN t ==> ring_mul r' ((e:K->B) i) d = ring_0 r'`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN EXPAND_TAC "d" THEN
    MATCH_MP_TAC RING_DET_DEPENDENT_COLUMNS_MUL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[RING_SUB; RING_0];
      X_GEN_TAC `j:K` THEN DISCH_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sub r' (ring_sum r' t (\k:K. if k = j then ring_mul r' x (e j)
                                      else ring_0 r'))
                  (ring_sum r' t (\k. ring_mul r' ((h:A->B)((m:K->K->A) j k))
                                                  ((e:K->B) k)))` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[RING_MUL; RING_0];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ASM_CASES_TAC `k:K = j` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[RING_SUB_RDISTRIB; RING_MUL_LZERO; RING_0] THEN
      ASM_MESON_TAC[];
      REMOVE_THEN "m" (MP_TAC o SPEC `j:K`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC[RING_SUM_DELTA; RING_MUL; RING_SUB_REFL; RING_SUM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:B) IN ring_carrier r'` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[RING_DET]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `ring_mul r' (d:B) (ring_1 r')` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[RING_MUL_RID]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RING_SUM_LMUL; RING_MUL] THEN
  MATCH_MP_TAC RING_SUM_EQ_0 THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `ring_mul r' ((h:A->B)((c:K->A) i)) (ring_mul r' ((e:K->B) i) d)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `ring_mul r d (ring_mul r a b) = ring_mul r a (ring_mul r b (d:B))`) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[RING_MUL_RZERO]]);;

let INTEGRAL_ELEMENT_MODULE = prove
 (`!r:A ring r':B ring h z (e:num->B) (c:num->num->A) k.
        ring_homomorphism(r,r') h /\
        z IN ring_carrier r' /\
        0 < k /\
        e 0 = ring_1 r' /\
        (!j. j < k ==> e j IN ring_carrier r') /\
        (!i j. i < k /\ j < k ==> c i j IN ring_carrier r) /\
        (!j. j < k ==>
           ring_mul r' z (e j) =
           ring_sum r' {i | i < k}
             (\i. ring_mul r' (h(c j i)) (e i)))
        ==> integral_element (r,r') h z`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:num`,`:K`] INTEGRAL_ELEMENT_FINITE_MODULE) THEN
  MAP_EVERY EXISTS_TAC [`{i:num | i < k}`; `e:num->B`] THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `\i:num. if i = 0 then ring_1 r else ring_0 r:A` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[RING_0; RING_1];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r' {i:num | i < k}
        (\i. if i = 0 then ring_1 r' else ring_0 (r':B ring))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[RING_SUM_DELTA; IN_ELIM_THM; RING_1];
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[RING_HOMOMORPHISM_1; RING_HOMOMORPHISM_0; RING_MUL_LZERO;
                   RING_MUL_LID; RING_1]];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    EXISTS_TAC `(c:num->num->A) j` THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Spans of finite sets (ring_span of fieldtheory.ml, over any ring) and     *)
(* their stabilizers. Adjoining a root of a monic relation whose             *)
(* coefficients stabilize the span of g: the products a z^j (a IN g,         *)
(* j < m) span a module containing 1, stable under z and under every         *)
(* stabilizer of the span of g.                                              *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_SPAN_LMUL = prove
 (`!r:A ring r':B ring h s s' w.
        w IN ring_carrier r' /\
        (!y. y IN s /\ y IN ring_carrier r'
             ==> ring_mul r' w y IN ring_span (r,r') h s')
        ==> !y. y IN ring_span (r,r') h s
                ==> ring_mul r' w y IN ring_span (r,r') h s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN ring_span (r,r') h s
        ==> y IN ring_carrier r' /\
            ring_mul r' w y IN ring_span (r,r') (h:A->B) s'`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC ring_span_INDUCT THEN
  ASM_SIMP_TAC[RING_MUL_RZERO; RING_SPAN_0; RING_0] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:B`; `z:B`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_ADD; RING_ADD_LDISTRIB; RING_SPAN_ADD];
    MAP_EVERY X_GEN_TAC [`a:A`; `y:B`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RING_MUL] THEN
    SUBGOAL_THEN
     `ring_mul r' w (ring_mul r' (h a) y) =
      ring_mul r' ((h:A->B) a) (ring_mul r' w y)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul r w (ring_mul r a y) =
        ring_mul r a (ring_mul r w (y:B))`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RING_SPAN_MUL THEN ASM_REWRITE_TAC[]]]);;

let INTEGRAL_ELEMENT_SPAN = prove
 (`!r:A ring r':B ring h g x.
        ring_homomorphism(r,r') h /\ FINITE g /\ g SUBSET ring_carrier r' /\
        ring_1 r' IN ring_span (r,r') h g /\ x IN ring_carrier r' /\
        (!y. y IN ring_span (r,r') h g
             ==> ring_mul r' x y IN ring_span (r,r') h g)
        ==> integral_element (r,r') h x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:B. y IN g ==> ring_mul r' x y IN ring_span (r,r') (h:A->B) g`
  MP_TAC THENL
   [ASM_MESON_TAC[RING_SPAN_INC; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `ring_1 r' IN ring_span (r,r') (h:A->B) g` THEN
  ASM_SIMP_TAC[RING_SPAN_FINITE; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:B`,`:K`] INTEGRAL_ELEMENT_FINITE_MODULE) THEN
  MAP_EVERY EXISTS_TAC [`g:B->bool`; `\y:B. y`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]);;

let INTEGRAL_SPAN_ADJOIN = prove
 (`!r:A ring t:B ring k g z (d:num->B) m.
        ring_homomorphism(r,t) k /\ FINITE g /\ g SUBSET ring_carrier t /\
        ring_1 t IN ring_span (r,t) k g /\ z IN ring_carrier t /\
        (!j. j < m
             ==> d j IN ring_carrier t /\
                 !y. y IN ring_span (r,t) k g
                     ==> ring_mul t (d j) y IN ring_span (r,t) k g) /\
        ring_add t (ring_pow t z m)
          (ring_sum t {j | j < m} (\j. ring_mul t (d j) (ring_pow t z j))) =
        ring_0 t
        ==> ?g'. FINITE g' /\ g' SUBSET ring_carrier t /\
                 ring_1 t IN ring_span (r,t) k g' /\
                 (!y. y IN ring_span (r,t) k g'
                      ==> ring_mul t z y IN ring_span (r,t) k g') /\
                 (!w. w IN ring_carrier t /\
                      (!y. y IN ring_span (r,t) k g
                           ==> ring_mul t w y IN ring_span (r,t) k g)
                      ==> !y. y IN ring_span (r,t) k g'
                              ==> ring_mul t w y IN ring_span (r,t) k g')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `g:B->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!y:B. y IN ring_carrier t ==> y IN ring_span (r,t) (k:A->B) g`
    ASSUME_TAC THENL
     [UNDISCH_TAC
       `ring_add t (ring_pow t z 0)
          (ring_sum t {j | j < 0}
            (\j. ring_mul t ((d:num->B) j) (ring_pow t z j))) = ring_0 t` THEN
      REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; RING_SUM_CLAUSES; ring_pow] THEN
      SIMP_TAC[RING_ADD_RZERO; RING_1] THEN
      MESON_TAC[RING_MUL_RID; RING_MUL_RZERO; RING_SPAN_0];
      CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC RING_MUL THEN ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  ABBREV_TAC `g' = {ring_mul t (a:B) (ring_pow t z j) |
                    a IN g /\ j IN {j:num | j < m}}` THEN
  SUBGOAL_THEN `!a:B. a IN g ==> a IN ring_carrier t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN g' <=>
        ?a j. a IN g /\ j < m /\ y = ring_mul t (a:B) (ring_pow t z j)`
  (LABEL_TAC "g'") THENL
   [EXPAND_TAC "g'" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u j. u IN ring_span (r,t) k g /\ j < m
          ==> ring_mul t u (ring_pow t z j) IN ring_span (r,t) (k:A->B) g'`
  (LABEL_TAC "aux") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(u:B) IN ring_carrier t` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul t u (ring_pow t z j) = ring_mul t (ring_pow t z j) (u:B)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[RING_POW]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `t:B ring`; `k:A->B`; `g:B->bool`;
                   `g':B->bool`; `ring_pow t (z:B) j`] INTEGRAL_SPAN_LMUL) THEN
    ASM_SIMP_TAC[RING_POW] THEN ANTS_TAC THENL
     [X_GEN_TAC `y:B` THEN STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_INC THEN
      ASM_SIMP_TAC[RING_MUL; RING_POW] THEN
      USE_THEN "g'" (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY EXISTS_TAC [`y:B`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[RING_POW];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `g':B->bool` THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "g'" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    EXPAND_TAC "g'" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC[RING_MUL; RING_POW];
    REMOVE_THEN "aux" (MP_TAC o SPECL [`ring_1 t:B`; `0`]) THEN
    ASM_SIMP_TAC[LE_1; ring_pow; RING_MUL_LID; RING_1];
    ALL_TAC;
    X_GEN_TAC `w:B` THEN STRIP_TAC] THEN
  MATCH_MP_TAC INTEGRAL_SPAN_LMUL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:B` THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  USE_THEN "g'" (fun th -> REWRITE_TAC[th; LEFT_IMP_EXISTS_THM]) THEN
  MAP_EVERY X_GEN_TAC [`a:B`; `j:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[RING_MUL_ASSOC; RING_POW] THEN
    USE_THEN "aux" MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_SPAN_INC]] THEN
  SUBGOAL_THEN
   `ring_mul t z (ring_mul t a (ring_pow t z j)) =
    ring_mul t a (ring_pow t (z:B) (SUC j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[ring_pow] THEN MATCH_MP_TAC(RING_RULE
     `ring_mul r z (ring_mul r a p) = ring_mul r a (ring_mul r z (p:B))`) THEN
    ASM_SIMP_TAC[RING_POW];
    ALL_TAC] THEN
  ASM_CASES_TAC `SUC j < m` THENL
   [USE_THEN "aux" MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_SPAN_INC];
    SUBGOAL_THEN `SUC j = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC]] THEN
  SUBGOAL_THEN
   `ring_pow t z m =
    ring_neg t (ring_sum t {j | j < m}
                  (\j. ring_mul t ((d:num->B) j) (ring_pow t z j)))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_RNEG_UNIQUE THEN
    ASM_SIMP_TAC[RING_POW; RING_SUM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_RNEG; RING_SUM; GSYM RING_SUM_LMUL;
               FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; RING_POW] THEN
  MATCH_MP_TAC RING_SPAN_NEG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_SPAN_SUM THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_mul t a (ring_mul t ((d:num->B) i) (ring_pow t z i)) =
    ring_mul t (ring_mul t (d i) a) (ring_pow t z i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `ring_mul r a (ring_mul r d p) = ring_mul r (ring_mul r d a) (p:B)`) THEN
    ASM_SIMP_TAC[RING_POW];
    USE_THEN "aux" MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_SPAN_INC]]);;

let INTEGRAL_ELEMENT_FROM_RELATION = prove
 (`!r:A ring r':B ring h x n c.
        ring_homomorphism(r,r') h /\ x IN ring_carrier r' /\
        (!i. i < n ==> c i IN ring_carrier r) /\
        ring_add r' (ring_pow r' x n)
          (ring_sum r' {i | i < n}
             (\i. ring_mul r' (h(c i)) (ring_pow r' x i))) = ring_0 r'
        ==> integral_element (r,r') h x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `h:A->B`; `{ring_1 r':B}`; `x:B`;
                 `\i:num. (h:A->B)(c i)`; `n:num`] INTEGRAL_SPAN_ADJOIN) THEN
  ASM_SIMP_TAC[FINITE_SING; SING_SUBSET; RING_1; RING_SPAN_INC; IN_SING] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:A->B)(c(i:num)) IN ring_carrier r'` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ASM_REWRITE_TAC[]] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_MUL THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:B->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_SPAN THEN EXISTS_TAC `g:B->bool` THEN
    ASM_REWRITE_TAC[]]);;

let INTEGRAL_ELEMENT_OVER_SUBRING = prove
 (`!r s (h:A->B) t x.
        ring_homomorphism(r,s) h /\
        IMAGE h (ring_carrier r) SUBSET ring_carrier(subring_generated s t) /\
        integral_element (r,s) h x
        ==> integral_element (subring_generated s t,s) I x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `h:A->B`; `x:B`]
    INTEGRAL_ELEMENT_RELATION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:num->A`] THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `(h:A->B) o (c:num->A)`] THEN
  ASM_REWRITE_TAC[I_THM; o_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[I_DEF; RING_HOMOMORPHISM_INCLUSION];
    ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER];
    ASM SET_TAC[]]);;

let INTEGRAL_SPAN_FINITE_SET = prove
 (`!r:A ring t:B ring k b.
        ring_homomorphism(r,t) k /\ FINITE b /\
        (!y. y IN b ==> integral_element (r,t) k y)
        ==> ?g. FINITE g /\ g SUBSET ring_carrier t /\
                ring_1 t IN ring_span (r,t) k g /\
                !y. y IN b
                    ==> !z. z IN ring_span (r,t) k g
                            ==> ring_mul t y z IN ring_span (r,t) k g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[IMP_CONJ] THEN SPEC_TAC(`b:B->bool`,`b:B->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `{ring_1 t:B}` THEN
    SIMP_TAC[FINITE_SING; SING_SUBSET; RING_1; RING_SPAN_INC; IN_SING;
             NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:B`; `b:B->bool`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun ih -> STRIP_TAC THEN MP_TAC ih) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:B->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`r:A ring`; `t:B ring`; `k:A->B`; `a:B`]
    INTEGRAL_ELEMENT_RELATION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:num->A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `t:B ring`; `k:A->B`; `g:B->bool`; `a:B`;
                 `\i:num. (k:A->B)(c i)`; `n:num`] INTEGRAL_SPAN_ADJOIN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(k:A->B)(c(i:num)) IN ring_carrier t` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ASM_REWRITE_TAC[]] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_MUL THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g':B->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:B` THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]]);;

let INTEGRAL_ELEMENT_EXPLICIT = prove
 (`!r:A ring r':B ring h x.
        ring_homomorphism(r,r') h
        ==> (integral_element (r,r') h x <=>
             x IN ring_carrier r' /\
             ?n c. 0 < n /\
                   (!i. i < n ==> c(i) IN ring_carrier r) /\
                   ring_add r' (ring_pow r' x n)
                               (ring_sum r' {i | i < n}
                                  (\i. ring_mul r' (h(c i))
                                                   (ring_pow r' x i)))
                   = ring_0 r')`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->A`] THEN ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier r'` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `h:A->B`; `x:B`]
    INTEGRAL_ELEMENT_RELATION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:num->A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->A`] THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC] THEN
  MAP_EVERY EXISTS_TAC [`1`; `\i:num. ring_0 r:A`] THEN
  REWRITE_TAC[ARITH; RING_0] THEN
  UNDISCH_TAC
   `ring_add r' (ring_pow r' x n)
      (ring_sum r' {i | i < n}
         (\i. ring_mul r' ((h:A->B)(c i)) (ring_pow r' x i))) =
    ring_0 r'` THEN
  ASM_REWRITE_TAC[LT; EMPTY_GSPEC; RING_SUM_CLAUSES; ring_pow] THEN
  SIMP_TAC[RING_ADD_RZERO; RING_1] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[RING_MUL_RID; RING_MUL_RZERO]
   `(!y. y IN ring_carrier r' ==> ring_mul r' y (ring_1 r') = y) /\
    (!y. y IN ring_carrier r' ==> ring_mul r' y (ring_0 r') = ring_0 r') /\
    ring_1 r' = ring_0 r' /\ a IN ring_carrier r'
    ==> a = ring_0 (r':B ring)`) THEN
  ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO; RING_ADD; RING_POW; RING_SUM]);;

(* ------------------------------------------------------------------------- *)
(* Closure under the ring operations.                                        *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_ELEMENT_ADD = prove
 (`!r:A ring r':B ring h x y.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x /\ integral_element (r,r') h y
        ==> integral_element (r,r') h (ring_add r' x y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `h:A->B`; `{x:B,y}`]
    INTEGRAL_SPAN_FINITE_SET) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                  NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:B->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier r' /\ y IN ring_carrier r'`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_SPAN THEN EXISTS_TAC `g:B->bool` THEN
  ASM_SIMP_TAC[RING_ADD] THEN
  X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:B) IN ring_carrier r'` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_ADD_RDISTRIB] THEN
  MATCH_MP_TAC RING_SPAN_ADD THEN ASM_SIMP_TAC[]);;

let INTEGRAL_ELEMENT_MUL = prove
 (`!r:A ring r':B ring h x y.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x /\ integral_element (r,r') h y
        ==> integral_element (r,r') h (ring_mul r' x y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `h:A->B`; `{x:B,y}`]
    INTEGRAL_SPAN_FINITE_SET) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                  NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:B->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier r' /\ y IN ring_carrier r'`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_SPAN THEN EXISTS_TAC `g:B->bool` THEN
  ASM_SIMP_TAC[RING_MUL] THEN
  X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:B) IN ring_carrier r'` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RING_MUL_ASSOC]);;

let INTEGRAL_ELEMENT_NEG = prove
 (`!r:A ring r':B ring h x.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x
        ==> integral_element (r,r') h (ring_neg r' x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER) THEN
  SUBGOAL_THEN
   `ring_neg r' x = ring_mul r' ((h:A->B)(ring_neg r (ring_1 r))) (x:B)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> SIMP_TAC[RING_1; MATCH_MP RING_HOMOMORPHISM_NEG th;
                                   MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    ASM_SIMP_TAC[RING_MUL_LNEG; RING_MUL_LID; RING_1];
    MATCH_MP_TAC INTEGRAL_ELEMENT_MUL THEN
    ASM_SIMP_TAC[INTEGRAL_ELEMENT_IMAGE; RING_NEG; RING_1]]);;

let INTEGRAL_ELEMENT_SUB = prove
 (`!r:A ring r':B ring h x y.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x /\ integral_element (r,r') h y
        ==> integral_element (r,r') h (ring_sub r' x y)`,
  SIMP_TAC[ring_sub; INTEGRAL_ELEMENT_ADD; INTEGRAL_ELEMENT_NEG]);;

let INTEGRAL_ELEMENT_POW = prove
 (`!r:A ring r':B ring h x n.
        ring_homomorphism(r,r') h /\
        integral_element (r,r') h x
        ==> integral_element (r,r') h (ring_pow r' x n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_pow; INTEGRAL_ELEMENT_1; INTEGRAL_ELEMENT_MUL]);;

let INTEGRAL_CLOSURE_SUBRING = prove
 (`!r:A ring r':B ring h.
        ring_homomorphism(r,r') h
        ==> {x | integral_element (r,r') h x} subring_of r'`,
  SIMP_TAC[subring_of; SUBSET; IN_ELIM_THM;
           INTEGRAL_ELEMENT_IN_CARRIER; INTEGRAL_ELEMENT_0;
           INTEGRAL_ELEMENT_1; INTEGRAL_ELEMENT_NEG; INTEGRAL_ELEMENT_ADD;
           INTEGRAL_ELEMENT_MUL] THEN
  MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]);;

let INTEGRAL_CLOSURE_SUPSET_IMAGE = prove
 (`!r:A ring r':B ring h.
        ring_homomorphism(r,r') h
        ==> IMAGE h (ring_carrier r) SUBSET {x | integral_element (r,r') h x}`,
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
           INTEGRAL_ELEMENT_IMAGE]);;

let INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE = prove
 (`!r:A ring r':B ring r'':C ring h g x.
        ring_homomorphism(r,r') h /\ ring_homomorphism(r',r'') g /\
        integral_element (r,r') h x
        ==> integral_element (r,r'') (g o h) (g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integral_element] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:(1->num)->A`
     STRIP_ASSUME_TAC)))) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  EXISTS_TAC `p:(1->num)->A` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `r'':C ring`; `h:A->B`; `(:1)`;
                 `\v:1. (x:B)`; `g:B->C`; `p:(1->num)->A`]
    POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
  SUBGOAL_THEN `(g:B->C) o (\v:1. x) = (\v. g x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_0]);;

let INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE = prove
 (`!r:A ring r':B ring r'':C ring h g x.
        ring_homomorphism(r,r') h /\ ring_monomorphism(r',r'') g /\
        x IN ring_carrier r' /\
        integral_element (r,r'') (g o h) (g x)
        ==> integral_element (r,r') h x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integral_element] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC))))) THEN
  REWRITE_TAC[ring_monomorphism] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `p:(1->num)->A` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[POLY_EXTEND; RING_0] THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `r'':C ring`; `h:A->B`; `(:1)`;
                 `\v:1. (x:B)`; `g:B->C`; `p:(1->num)->A`]
    POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
  SUBGOAL_THEN `(g:B->C) o (\v:1. x) = (\v. g x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; DISCH_THEN SUBST1_TAC] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_0]);;

(* Integrality inside a subring containing the image of h.                   *)
let INTEGRAL_ELEMENT_SUBRING_GENERATED = prove
 (`!r:A ring r':B ring h s x.
        ring_homomorphism(r,r') h /\
        s subring_of r' /\ IMAGE h (ring_carrier r) SUBSET s
        ==> (integral_element (r,subring_generated r' s) h x <=>
             integral_element (r,r') h x /\ x IN s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral_element] THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING] THEN
  REWRITE_TAC[SUBRING_GENERATED] THEN
  ASM_CASES_TAC `(x:B) IN s` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier r'` ASSUME_TAC THENL
   [ASM_MESON_TAC[subring_of; SUBSET]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!p. p IN ring_carrier(poly_ring r (:1))
        ==> poly_extend (r,subring_generated r' s) (h:A->B) (\v:1. x) p =
            poly_extend (r,r') h (\v. x) p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN
    EXISTS_TAC `(:1)` THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_INTO_SUBRING_EQ;
                 CARRIER_SUBRING_GENERATED_SUBRING];
    EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `p:(1->num)->A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Transitivity: integral over an integral extension is integral.            *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_ELEMENT_TRANS = prove
 (`!r:A ring s:B ring t:C ring f g x.
        ring_homomorphism(r,s) f /\ ring_homomorphism(s,t) g /\
        (!y. y IN ring_carrier s ==> integral_element (r,s) f y) /\
        integral_element (s,t) g x
        ==> integral_element (r,t) (g o f) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(r:A ring,t:C ring) ((g:B->C) o (f:A->B))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:B ring`; `t:C ring`; `g:B->C`; `x:C`]
    INTEGRAL_ELEMENT_RELATION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:num->B`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `t:C ring`; `(g:B->C) o (f:A->B)`;
                 `IMAGE (\i. (g:B->C)(c i)) {i:num | i < n}`]
    INTEGRAL_SPAN_FINITE_SET) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE;
               IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE THEN
    EXISTS_TAC `s:B ring` THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g1:C->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`r:A ring`; `t:C ring`; `(g:B->C) o (f:A->B)`; `g1:C->bool`;
                 `x:C`; `\i:num. (g:B->C)(c i)`; `n:num`]
    INTEGRAL_SPAN_ADJOIN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    DISCH_THEN(X_CHOOSE_THEN `g2:C->bool` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_SPAN THEN EXISTS_TAC `g2:C->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]);;

(* The integral closure is integrally closed in the big ring.                *)
let INTEGRAL_CLOSURE_IDEMPOT = prove
 (`!r:A ring r':B ring h x.
        ring_homomorphism(r,r') h /\
        integral_element
          (subring_generated r' {x | integral_element (r,r') h x},r') I x
        ==> integral_element (r,r') h x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {x | integral_element (r:A ring,r':B ring) h x}` THEN
  SUBGOAL_THEN
   `(s:B->bool) subring_of r' /\ IMAGE (h:A->B) (ring_carrier r) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    ASM_SIMP_TAC[INTEGRAL_CLOSURE_SUBRING; INTEGRAL_CLOSURE_SUPSET_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `subring_generated r' (s:B->bool)`; `r':B ring`;
                 `h:A->B`; `I:B->B`; `x:B`] INTEGRAL_ELEMENT_TRANS) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_INTO_SUBRING_EQ; I_O_ID;
               INTEGRAL_ELEMENT_SUBRING_GENERATED;
               CARRIER_SUBRING_GENERATED_SUBRING] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[I_DEF; RING_HOMOMORPHISM_INCLUSION];
      EXPAND_TAC "s" THEN SIMP_TAC[IN_ELIM_THM]];
    EXPAND_TAC "s" THEN SIMP_TAC[IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Fields, algebraic elements.                                               *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC = prove
 (`!k:A ring l:B ring h x.
        field_extension (k,l) h
        ==> (integral_element (k,l) h x <=> algebraic_over (k,l) h x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  EQ_TAC THENL
   [REWRITE_TAC[integral_element; algebraic_over] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `p:(1->num)->A` THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES] THEN MATCH_MP_TAC MONIC_IMP_NONZERO THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL; FIELD_IMP_NONTRIVIAL_RING];
    DISCH_TAC THEN REWRITE_TAC[integral_element] THEN
    ASM_MESON_TAC[ALGEBRAIC_OVER_IN_CARRIER; MINIMAL_POLYNOMIAL]]);;

let INTEGRAL_ELEMENT_IN_ADJOIN_INV = prove
 (`!(k:A ring) a x.
        field k /\ a subring_of k /\ x IN ring_carrier k /\ ~(x = ring_0 k) /\
        x IN ring_carrier(subring_generated k (ring_inv k x INSERT a))
        ==> integral_element (subring_generated k a,k) I x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `a SUBSET ring_carrier k /\ ring_1 k IN a /\
    ring_carrier(subring_generated k a) = (a:A->bool) /\
    (!z. z IN a ==> ring_neg k z IN a)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING] THEN
    UNDISCH_TAC `(a:A->bool) subring_of k` THEN SIMP_TAC[subring_of];
    ALL_TAC] THEN
  ABBREV_TAC `y = ring_inv k (x:A)` THEN
  SUBGOAL_THEN `(y:A) IN ring_carrier k` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN ASM_SIMP_TAC[RING_INV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ring_mul k (ring_pow k x i) (ring_pow k (y:A) i) = ring_1 k`
  ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    ASM_SIMP_TAC[GSYM RING_MUL_POW; RING_INV; FIELD_MUL_RINV; RING_POW_ONE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A->bool`; `a:A->bool`; `y:A`; `x:A`]
    IDEAL_GENERATED_ADJOIN_EXPLICIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `subring_generated k (a:A->bool)` RING_IDEAL_CARRIER) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `x = ring_mul k x (ring_1 k:A)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_MUL_RID]; ALL_TAC] THEN
    MP_TAC(ISPECL [`subring_generated k ((y:A) INSERT a)`;
                   `ideal_generated (subring_generated k ((y:A) INSERT a)) a`;
                   `x:A`; `ring_1 k:A`] IN_RING_IDEAL_LMUL) THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; CONJUNCT2 SUBRING_GENERATED] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    UNDISCH_TAC `(a:A->bool) SUBSET ring_carrier k` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  SUBGOAL_THEN `!i. (c:num->A) i IN a /\ c i IN ring_carrier k` ASSUME_TAC
  THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a:A->bool) SUBSET ring_carrier k` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_pow k x (SUC n) =
    ring_sum k (0..n) (\i. ring_mul k ((c:num->A) i) (ring_pow k x (n - i)))`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `ring_mul k (ring_pow k x n)
       (ring_sum k (0..n)
         (\i. ring_mul k ((c:num->A) i) (ring_pow k (y:A) i)))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> REWRITE_TAC[check (fun th ->
        is_eq(concl th) && rand(concl th) = `x:A`) th]) THEN
      REWRITE_TAC[ring_pow] THEN MATCH_MP_TAC RING_MUL_SYM THEN
      ASM_SIMP_TAC[RING_POW];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG; RING_MUL; RING_POW]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_pow k (x:A) n = ring_mul k (ring_pow k x (n - i)) (ring_pow k x i)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM RING_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[RING_POW; RING_RULE
     `ring_mul k b d = ring_1 k
      ==> ring_mul k (ring_mul k a b) (ring_mul k c d) = ring_mul k c (a:A)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_pow k x (SUC n) =
    ring_sum k (0..n) (\j. ring_mul k ((c:num->A) (n - j)) (ring_pow k x j))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    MP_TAC(ISPECL [`k:A ring`;
      `\i. ring_mul k ((c:num->A) i) (ring_pow k (x:A) (n - i))`; `0`; `n:num`]
      RING_SUM_REFLECT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN
      ASM_SIMP_TAC[RING_POW];
      REWRITE_TAC[LT; SUB_0]] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subring_generated k (a:A->bool)`; `k:A ring`; `I:A->A`;
                 `x:A`] INTEGRAL_ELEMENT_EXPLICIT) THEN
  REWRITE_TAC[I_DEF; RING_HOMOMORPHISM_INCLUSION] THEN
  REWRITE_TAC[GSYM I_DEF; I_THM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `SUC n` THEN
  EXISTS_TAC `\j. ring_neg k ((c:num->A) (n - j))` THEN
  ASM_SIMP_TAC[LT_0; RING_NEG_IN_SUBRING_GENERATED; SUBRING_GENERATED_INC_GEN;
               RING_NEG] THEN
  REWRITE_TAC[NUMSEG_LT; NOT_SUC; SUC_SUB1] THEN
  ASM_SIMP_TAC[RING_MUL_LNEG; RING_MUL; RING_POW] THEN
  ASM_SIMP_TAC[RING_SUM_NEG; FINITE_NUMSEG; RING_MUL; RING_POW] THEN
  ASM_SIMP_TAC[GSYM ring_sub; RING_SUB_EQ_0; RING_SUM; RING_POW] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The homogeneous form H(a,b) = a^n + sum_{i<n} c_i a^i b^(n-i) of a monic  *)
(* relation (clearing denominators): scaling, images, the UFD argument,      *)
(* fractions x = a/b with x * f(b) = f(a).                                   *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_HOMOGENEOUS_SCALE = prove
 (`!r:A ring p a b c n.
        p IN ring_carrier r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
        (!i. i < n ==> c i IN ring_carrier r)
        ==> ring_add r (ring_pow r (ring_mul r p a) n)
              (ring_sum r {i | i < n}
                 (\i. ring_mul r (c i)
                        (ring_mul r (ring_pow r (ring_mul r p a) i)
                                    (ring_pow r (ring_mul r p b) (n - i))))) =
            ring_mul r (ring_pow r p n)
              (ring_add r (ring_pow r a n)
                 (ring_sum r {i | i < n}
                    (\i. ring_mul r (c i)
                           (ring_mul r (ring_pow r a i)
                                       (ring_pow r b (n - i))))))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RING_ADD_LDISTRIB; RING_POW; RING_SUM; RING_MUL_POW] THEN
  AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; RING_POW] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_pow r p n = ring_mul r (ring_pow r p i) (ring_pow r (p:A) (n - i))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul r c (ring_mul r (ring_mul r p a) (ring_mul r q b)) =
    ring_mul r (ring_mul r p q) (ring_mul r c (ring_mul r a (b:A)))`) THEN
  ASM_SIMP_TAC[RING_POW]);;

let INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE = prove
 (`!r:A ring t:B ring f a b c n.
        ring_homomorphism(r,t) f /\
        a IN ring_carrier r /\ b IN ring_carrier r /\
        (!i. i < n ==> c i IN ring_carrier r)
        ==> f(ring_add r (ring_pow r a n)
                (ring_sum r {i | i < n}
                   (\i. ring_mul r (c i)
                          (ring_mul r (ring_pow r a i)
                                      (ring_pow r b (n - i)))))) =
            ring_add t (ring_pow t (f a) n)
              (ring_sum t {i | i < n}
                 (\i. ring_mul t (f(c i))
                        (ring_mul t (ring_pow t (f a) i)
                                    (ring_pow t (f b) (n - i)))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_ADD th;
                 MATCH_MP RING_HOMOMORPHISM_POW th; RING_POW; RING_SUM]) THEN
  AP_TERM_TAC THEN
  FIRST_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP RING_HOMOMORPHISM_SUM th) o
     lhand o snd)) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; RING_POW] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
                 MATCH_MP RING_HOMOMORPHISM_POW th; RING_POW; RING_MUL]));;

let RING_REGULAR_MUL_EQ_0 = prove
 (`!r a x:A.
        ring_regular r a /\ x IN ring_carrier r
        ==> (ring_mul r a x = ring_0 r <=> x = ring_0 r)`,
  REWRITE_TAC[ring_regular; ring_zerodivisor] THEN
  MESON_TAC[RING_MUL_RZERO]);;

let INTEGRAL_HOMOGENEOUS_CLEAR = prove
 (`!t:B ring x u d n.
        x IN ring_carrier t /\ ring_regular t u /\
        (!i. i < n ==> d i IN ring_carrier t)
        ==> (ring_add t (ring_pow t (ring_mul t x u) n)
               (ring_sum t {i | i < n}
                  (\i. ring_mul t (d i)
                         (ring_mul t (ring_pow t (ring_mul t x u) i)
                                     (ring_pow t u (n - i))))) = ring_0 t <=>
             ring_add t (ring_pow t x n)
               (ring_sum t {i | i < n}
                  (\i. ring_mul t (d i) (ring_pow t x i))) = ring_0 t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u:B) IN ring_carrier t` ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_regular]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:B ring`; `u:B`; `x:B`; `ring_1 t:B`; `d:num->B`; `n:num`]
    INTEGRAL_HOMOGENEOUS_SCALE) THEN
  ASM_SIMP_TAC[RING_MUL_RID; RING_1; RING_POW_ONE] THEN
  SUBGOAL_THEN `ring_mul t u x = ring_mul t x (u:B)` SUBST1_TAC THENL
   [ASM_MESON_TAC[RING_MUL_SYM]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `ring_sum t {i | i < n}
      (\i. ring_mul t ((d:num->B) i)
             (ring_mul t (ring_pow t x i) (ring_1 t))) =
    ring_sum t {i | i < n} (\i. ring_mul t (d i) (ring_pow t x i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_regular t (ring_pow t (u:B) n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_REGULAR_POW]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_REGULAR_MUL_EQ_0; RING_ADD; RING_POW; RING_SUM]);;

(* The UFD argument: H(a,b) = 0 forces b to divide a.                        *)
let INTEGRAL_UFD_HOMOGENEOUS_DIVIDES = prove
 (`!r:A ring a b c n.
        UFD r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
        (!i. i < n ==> c i IN ring_carrier r) /\
        ring_add r (ring_pow r a n)
          (ring_sum r {i | i < n}
             (\i. ring_mul r (c i)
                    (ring_mul r (ring_pow r a i) (ring_pow r b (n - i))))) =
        ring_0 r
        ==> ring_divides r b a`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `UFD (r:A ring)
    ==> !b. b IN ring_carrier r
            ==> !a c n. a IN ring_carrier r /\
                        (!i. i < n ==> c i IN ring_carrier r) /\
                        ring_add r (ring_pow r a n)
                          (ring_sum r {i | i < n}
                             (\i. ring_mul r (c i)
                                    (ring_mul r (ring_pow r a i)
                                                (ring_pow r b (n - i))))) =
                        ring_0 r
                        ==> ring_divides r b a`
   (fun th -> MESON_TAC[th]) THEN
  DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP UFD_IMP_INTEGRAL_DOMAIN) THEN
  MATCH_MP_TAC UFD_PRIME_FACTOR_INDUCT THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:A`; `c:num->A`; `n:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[RING_DIVIDES_ZERO] THEN
    UNDISCH_TAC
     `ring_add r (ring_pow r a n)
        (ring_sum r {i | i < n}
          (\i. ring_mul r ((c:num->A) i)
                 (ring_mul r (ring_pow r a i)
                             (ring_pow r (ring_0 r) (n - i))))) =
      ring_0 r` THEN
    SUBGOAL_THEN
     `ring_sum r {i | i < n}
        (\i. ring_mul r ((c:num->A) i)
               (ring_mul r (ring_pow r a i)
                           (ring_pow r (ring_0 r) (n - i)))) = ring_0 r`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ_0 THEN
      ASM_SIMP_TAC[IN_ELIM_THM; RING_POW_ZERO; ARITH_RULE
       `i < n ==> ~(n - i = 0)`; RING_MUL_RZERO; RING_POW];
      ASM_SIMP_TAC[RING_ADD_RZERO; RING_POW; INTEGRAL_DOMAIN_POW_EQ_0]];
    MESON_TAC[RING_UNIT_DIVIDES_ANY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `b:A`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `c:num->A`; `n:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN ring_carrier r /\ ~(p = ring_0 r)` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[ring_prime]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_divides r p (a:A)` MP_TAC THENL
   [MATCH_MP_TAC RING_PRIME_DIVIDES_POW THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `ring_pow r a n =
      ring_neg r (ring_sum r {i | i < n}
       (\i. ring_mul r ((c:num->A) i)
             (ring_mul r (ring_pow r a i)
                         (ring_pow r (ring_mul r p b) (n - i)))))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_RNEG_UNIQUE THEN
      ASM_SIMP_TAC[RING_POW; RING_SUM];
      MATCH_MP_TAC RING_DIVIDES_NEG] THEN
    MATCH_MP_TAC RING_SUM_CLOSED THEN
    SIMP_TAC[RING_DIVIDES_0; RING_DIVIDES_ADD] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REPEAT(MATCH_MP_TAC RING_DIVIDES_LMUL THEN
           ASM_SIMP_TAC[RING_POW; RING_MUL]) THEN
    SUBGOAL_THEN `n - i = SUC(n - i - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ring_pow]] THEN
    ASM_SIMP_TAC[RING_MUL_POW; RING_POW] THEN
    MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC[RING_POW; RING_MUL] THEN
    ASM_SIMP_TAC[RING_DIVIDES_RMUL; RING_DIVIDES_REFL];
    GEN_REWRITE_TAC LAND_CONV [ring_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':A` STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2)
    THEN FIRST_X_ASSUM SUBST_ALL_TAC] THEN
  MATCH_MP_TAC RING_DIVIDES_LMUL2 THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`c:num->A`; `n:num`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A`; `a':A`; `b:A`; `c:num->A`; `n:num`]
    INTEGRAL_HOMOGENEOUS_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SYM) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; RING_POW; RING_ADD; RING_SUM;
               INTEGRAL_DOMAIN_POW_EQ_0]);;

(* The homogeneous form vanishes iff the dehomogenized relation holds, for   *)
(* x with x * f(b) = f(a) and f(b) regular.                                  *)
let INTEGRAL_HOMOGENEOUS_RELATION = prove
 (`!r:A ring t:B ring f a b x c n.
        ring_homomorphism(r,t) f /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ x IN ring_carrier t /\
        ring_regular t (f b) /\ ring_mul t x (f b) = f a /\
        (!i. i < n ==> c i IN ring_carrier r)
        ==> (f(ring_add r (ring_pow r a n)
                (ring_sum r {i | i < n}
                   (\i. ring_mul r (c i)
                          (ring_mul r (ring_pow r a i)
                                      (ring_pow r b (n - i)))))) = ring_0 t <=>
             ring_add t (ring_pow t x n)
               (ring_sum t {i | i < n}
                  (\i. ring_mul t (f(c i)) (ring_pow t x i))) = ring_0 t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `t:B ring`; `f:A->B`; `a:A`; `b:A`; `c:num->A`;
                 `n:num`] INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INTEGRAL_HOMOGENEOUS_CLEAR THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]);;

(* For a monomorphism f and x with x * f(b) = f(a), f(b) regular: x is in   *)
(* the image of f iff b divides a.                                           *)
let INTEGRAL_MONOMORPHISM_IN_IMAGE = prove
 (`!r:A ring t:B ring f a b x.
        ring_monomorphism(r,t) f /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ x IN ring_carrier t /\
        ring_regular t (f b) /\ ring_mul t x (f b) = f a
        ==> (x IN IMAGE f (ring_carrier r) <=> ring_divides r b a)`,
  REWRITE_TAC[ring_monomorphism] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!d. d IN ring_carrier r ==> (f:A->B) d IN ring_carrier t`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. d IN ring_carrier r
        ==> (f:A->B)(ring_mul r b d) = ring_mul t (f b) (f d)`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_MUL]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; ring_divides] THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:A` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[RING_MUL] THEN
    UNDISCH_TAC `ring_mul t x ((f:A->B) b) = f a` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `ring_mul t ((f:A->B) b) (ring_sub t x (f d)) = ring_0 t`
    MP_TAC THENL
     [ASM_SIMP_TAC[RING_SUB_LDISTRIB] THEN
      SUBGOAL_THEN `ring_mul t ((f:A->B) b) x = f a` SUBST1_TAC THENL
       [ASM_MESON_TAC[RING_MUL_SYM]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:A` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      MATCH_MP_TAC RING_SUB_REFL THEN ASM_SIMP_TAC[RING_MUL];
      ASM_SIMP_TAC[RING_REGULAR_MUL_EQ_0; RING_SUB; RING_SUB_EQ_0]]]);;

(* Elements of the fraction ring as fractions a/b.                           *)
let INTEGRAL_FRACTION_RING_DENOMINATOR = prove
 (`!r (x:(A#A)->bool).
        x IN ring_carrier(fraction_ring r)
        ==> ?a b. a IN ring_carrier r /\ ring_regular r b /\
                  ring_regular (fraction_ring r)
                    (ring_fractionate r {a | ring_regular r a} b) /\
                  ring_mul (fraction_ring r) x
                    (ring_fractionate r {a | ring_regular r a} b) =
                  ring_fractionate r {a | ring_regular r a} a`,
  REWRITE_TAC[fraction_ring] THEN
  SIMP_TAC[RING_LOCALIZATION_CARRIER; RING_MULTSYS_REGULAR] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:A ring`; `x:(A#A)->bool`; `a:A`; `b:A`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_UNIT_IMP_REGULAR THEN
    MATCH_MP_TAC RING_UNIT_FRACTIONATE THEN
    ASM_REWRITE_TAC[RING_MULTSYS_REGULAR; IN_ELIM_THM];
    MATCH_MP_TAC LOCALEQUIV_MUL_LCANCEL THEN
    ASM_REWRITE_TAC[RING_MULTSYS_REGULAR; IN_ELIM_THM]]);;

(* Integrality in the fraction ring, cleared of denominators.                *)
let INTEGRAL_FRACTION_RING_RELATION = prove
 (`!r (x:(A#A)->bool).
        integral_element
          (r,fraction_ring r) (ring_fractionate r {a | ring_regular r a}) x
        ==> ?a b c n. a IN ring_carrier r /\ ring_regular r b /\
                      ring_regular (fraction_ring r)
                        (ring_fractionate r {a | ring_regular r a} b) /\
                      ring_mul (fraction_ring r) x
                        (ring_fractionate r {a | ring_regular r a} b) =
                      ring_fractionate r {a | ring_regular r a} a /\
                      (!i. i < n ==> c i IN ring_carrier r) /\
                      ring_add r (ring_pow r a n)
                        (ring_sum r {i | i < n}
                          (\i. ring_mul r (c i)
                                 (ring_mul r (ring_pow r a i)
                                             (ring_pow r b (n - i))))) =
                      ring_0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `r:A ring` RING_MONOMORPHISM_FRACTIONATE) THEN
  REWRITE_TAC[RING_MONOMORPHISM_ALT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `x:(A#A)->bool`]
    INTEGRAL_FRACTION_RING_DENOMINATOR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `fraction_ring r:((A#A)->bool) ring`;
                 `ring_fractionate r {a:A | ring_regular r a}`;
                 `x:(A#A)->bool`] INTEGRAL_ELEMENT_RELATION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:num->A`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`; `c:num->A`; `n:num`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `(b:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_REGULAR_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_ADD; RING_POW; RING_SUM] THEN
  MP_TAC(ISPECL [`r:A ring`; `fraction_ring r:((A#A)->bool) ring`;
                 `ring_fractionate r {a:A | ring_regular r a}`;
                 `a:A`; `b:A`; `x:(A#A)->bool`; `c:num->A`; `n:num`]
    INTEGRAL_HOMOGENEOUS_RELATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]);;

(* Integrally closed domains: the homogenized monic relations force          *)
(* divisibility.                                                             *)
let INTEGRALLY_CLOSED_ALT = prove
 (`!r:A ring.
        integrally_closed r <=>
        integral_domain r /\
        !a b c n.
          a IN ring_carrier r /\ b IN ring_carrier r /\ ~(b = ring_0 r) /\
          (!i. i < n ==> c i IN ring_carrier r) /\
          ring_add r (ring_pow r a n)
            (ring_sum r {i | i < n}
               (\i. ring_mul r (c i)
                      (ring_mul r (ring_pow r a i) (ring_pow r b (n - i))))) =
          ring_0 r
          ==> ring_divides r b a`,
  GEN_TAC THEN REWRITE_TAC[integrally_closed] THEN
  ASM_CASES_TAC `integral_domain(r:A ring)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r:A ring` RING_MONOMORPHISM_FRACTIONATE) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM th)) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:A`; `b:A`; `c:num->A`; `n:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ring_regular r (b:A)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[INTEGRAL_DOMAIN_REGULAR]; ALL_TAC] THEN
    ABBREV_TAC `x = ring_localequiv r {a:A | ring_regular r a} (a,b)` THEN
    SUBGOAL_THEN
     `x IN ring_carrier(fraction_ring r) /\
      ring_regular (fraction_ring r)
        (ring_fractionate r {a:A | ring_regular r a} b) /\
      ring_mul (fraction_ring r) x
        (ring_fractionate r {a:A | ring_regular r a} b) =
      ring_fractionate r {a | ring_regular r a} a`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN REWRITE_TAC[fraction_ring] THEN
      ASM_SIMP_TAC[RING_LOCALEQUIV_IN_CARRIER; RING_MULTSYS_REGULAR;
                   IN_ELIM_THM; LOCALEQUIV_MUL_LCANCEL] THEN
      MATCH_MP_TAC RING_UNIT_IMP_REGULAR THEN
      MATCH_MP_TAC RING_UNIT_FRACTIONATE THEN
      ASM_REWRITE_TAC[RING_MULTSYS_REGULAR; IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `fraction_ring r:((A#A)->bool) ring`;
                   `ring_fractionate r {a:A | ring_regular r a}`;
                   `a:A`; `b:A`; `x:(A#A)->bool`]
      INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->A`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `fraction_ring r:((A#A)->bool) ring`;
                   `ring_fractionate r {a:A | ring_regular r a}`;
                   `a:A`; `b:A`; `x:(A#A)->bool`;
                   `c:num->A`; `n:num`] INTEGRAL_HOMOGENEOUS_RELATION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_0];
    X_GEN_TAC `x:(A#A)->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRAL_FRACTION_RING_RELATION) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`; `c:num->A`; `n:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(b:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_REGULAR_IN_CARRIER]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `fraction_ring r:((A#A)->bool) ring`;
                   `ring_fractionate r {a:A | ring_regular r a}`;
                   `a:A`; `b:A`; `x:(A#A)->bool`]
      INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`c:num->A`; `n:num`] THEN
    ASM_MESON_TAC[INTEGRAL_DOMAIN_REGULAR]]);;

(* ------------------------------------------------------------------------- *)
(* Integrally closed domains.                                                *)
(* ------------------------------------------------------------------------- *)

let UFD_IMP_INTEGRALLY_CLOSED = prove
 (`!r:A ring. UFD r ==> integrally_closed r`,
  SIMP_TAC[INTEGRALLY_CLOSED_ALT; UFD_IMP_INTEGRAL_DOMAIN] THEN
  MESON_TAC[INTEGRAL_UFD_HOMOGENEOUS_DIVIDES]);;

let PID_IMP_INTEGRALLY_CLOSED = prove
 (`!r:A ring. PID r ==> integrally_closed r`,
  SIMP_TAC[PID_IMP_UFD; UFD_IMP_INTEGRALLY_CLOSED]);;

let FIELD_IMP_INTEGRALLY_CLOSED = prove
 (`!r:A ring. field r ==> integrally_closed r`,
  SIMP_TAC[FIELD_IMP_PID; PID_IMP_INTEGRALLY_CLOSED]);;

let INTEGRALLY_CLOSED_INTEGER_RING = prove
 (`integrally_closed integer_ring`,
  SIMP_TAC[UFD_INTEGER_RING; UFD_IMP_INTEGRALLY_CLOSED]);;

(* In a field of characteristic 0, the integral elements (over Z) of the     *)
(* prime subfield are the integers.                                          *)
let INTEGRAL_ELEMENT_PRIME_SUBFIELD = prove
 (`!k:A ring x.
        field k /\ ring_char k = 0 /\
        x IN ring_carrier(subfield_generated k {ring_0 k}) /\
        integral_element (integer_ring,k) (ring_of_int k) x
        ==> ?n. x = ring_of_int k n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`; `x:A`]
    SUBFIELD_GENERATED_QUOTIENTS) THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; RING_CARRIER_SUBRING_GENERATED_0] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
              LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a':A`; `b':A`; `a:int`; `b:int`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN `ring_monomorphism(integer_ring,k) (ring_of_int k:int->A)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_MONOMORPHISM_INTEGER_RING_OF_INT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_regular k (ring_of_int k (b:int):A) /\
    ring_mul k x (ring_of_int k b) = ring_of_int k a`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_DOMAIN_REGULAR; RING_OF_INT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ring_div] THEN
    SUBGOAL_THEN `ring_unit k (ring_of_int k (b:int):A)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[FIELD_UNIT; RING_OF_INT]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_OF_INT; RING_INV; RING_MUL_LINV;
                 RING_MUL_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`integer_ring`; `k:A ring`; `ring_of_int k:int->A`;
                 `a:int`; `b:int`; `x:A`] INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN
  ASM_REWRITE_TAC[CONJUNCT1 INTEGER_RING; IN_UNIV] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]] THEN
  MP_TAC(ISPECL [`integer_ring`; `k:A ring`; `ring_of_int k:int->A`; `x:A`]
    INTEGRAL_ELEMENT_RELATION) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT;
                  LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:num->int`] THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_UFD_HOMOGENEOUS_DIVIDES THEN
  MAP_EVERY EXISTS_TAC [`c:num->int`; `n:num`] THEN
  REWRITE_TAC[UFD_INTEGER_RING; CONJUNCT1 INTEGER_RING; IN_UNIV] THEN
  UNDISCH_TAC `ring_monomorphism(integer_ring,k) (ring_of_int k:int->A)` THEN
  REWRITE_TAC[RING_MONOMORPHISM_ALT] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[CONJUNCT1 INTEGER_RING; IN_UNIV] THEN
  MP_TAC(ISPECL [`integer_ring`; `k:A ring`; `ring_of_int k:int->A`;
                 `a:int`; `b:int`; `x:A`; `c:num->int`; `n:num`]
    INTEGRAL_HOMOGENEOUS_RELATION) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT;
                  CONJUNCT1 INTEGER_RING; IN_UNIV] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* Integral closures in fields are integrally closed.                        *)
let INTEGRALLY_CLOSED_INTEGRAL_CLOSURE = prove
 (`!r:A ring l:B ring h.
        field l /\ ring_homomorphism(r,l) h
        ==> integrally_closed
              (subring_generated l {x | integral_element (r,l) h x})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. integral_element
          (subring_generated l {x | integral_element (r,l) h x},l) I x
        ==> x IN {x | integral_element (r:A ring,l:B ring) h x}`
  MP_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[INTEGRAL_CLOSURE_IDEMPOT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `l:B ring`; `h:A->B`]
    INTEGRAL_CLOSURE_SUBRING) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`{x | integral_element (r:A ring,l:B ring) h x}`,`s:B->bool`) THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `R = subring_generated l (s:B->bool)` THEN
  SUBGOAL_THEN
   `ring_carrier R = (s:B->bool) /\ ring_0 R = ring_0 l /\
    ring_mul R = ring_mul l /\ ring_homomorphism (R,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    SIMP_TAC[ASSUME `(s:B->bool) subring_of l`;
             CARRIER_SUBRING_GENERATED_SUBRING] THEN
    REWRITE_TAC[SUBRING_GENERATED; I_DEF; RING_HOMOMORPHISM_INCLUSION];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:B. x IN s ==> x IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[subring_of; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[INTEGRALLY_CLOSED_ALT] THEN CONJ_TAC THENL
   [EXPAND_TAC "R" THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_SUBRING_GENERATED; FIELD_IMP_INTEGRAL_DOMAIN];
    ASM_REWRITE_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`a:B`; `b:B`; `c:num->B`; `n:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `y = ring_mul l a (ring_inv l (b:B))` THEN
  SUBGOAL_THEN `(y:B) IN ring_carrier l /\ ring_mul l y b = a`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    SUBGOAL_THEN `ring_unit l (b:B)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[FIELD_UNIT]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV; GSYM RING_MUL_ASSOC; RING_MUL_LINV;
                 RING_MUL_RID];
    ALL_TAC] THEN
  REWRITE_TAC[ring_divides] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `y:B` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->B`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`R:B ring`; `l:B ring`; `I:B->B`; `a:B`; `b:B`; `y:B`;
                   `c:num->B`; `n:num`] INTEGRAL_HOMOGENEOUS_RELATION) THEN
    ASM_REWRITE_TAC[I_THM] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_REGULAR; FIELD_IMP_INTEGRAL_DOMAIN];
    ASM_MESON_TAC[RING_MUL_SYM]]);;

(* The divisibility criterion in the form used for Dedekind domains.         *)
let INTEGRALLY_CLOSED_DIVIDES = prove
 (`!r (a:A) b n c.
        integrally_closed r /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ ~(b = ring_0 r) /\
        (!i. i < n ==> c(i) IN ring_carrier r) /\
        ring_pow r a n =
          ring_sum r {i | i < n}
            (\i. ring_mul r (c i)
                   (ring_mul r (ring_pow r a i) (ring_pow r b (n - i))))
        ==> ring_divides r b a`,
  REWRITE_TAC[INTEGRALLY_CLOSED_ALT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\i. ring_neg r ((c:num->A) i)`; `n:num`] THEN
  ASM_SIMP_TAC[RING_NEG] THEN
  MATCH_MP_TAC(MESON[RING_ADD_RNEG; RING_SUM]
   `ring_sum r s g = ring_neg r (ring_sum r s f)
    ==> ring_add r (ring_sum r (s:num->bool) f) (ring_sum r s g) =
        ring_0 (r:A ring)`) THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_NEG o rand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; RING_POW] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; RING_MUL_LNEG; RING_MUL; RING_POW]);;

let INTEGRAL_ELEMENT_FRACTION_IN_IMAGE = prove
 (`!(r:A ring) (w:W ring) u y.
        PID r /\ field w /\ ring_monomorphism(r,w) u /\
        (?p q. p IN ring_carrier r /\ q IN ring_carrier r /\
               ~(q = ring_0 r) /\ ring_mul w (u q) y = u p) /\
        integral_element (r,w) u y
        ==> y IN IMAGE u (ring_carrier r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `p:A` (X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC))
     MP_TAC)))) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [ring_monomorphism]) THEN
  ASM_SIMP_TAC[INTEGRAL_ELEMENT_EXPLICIT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `ring_regular w ((u:A->W) q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_REGULAR; RING_HOMOMORPHISM_IN_CARRIER] THEN
    ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `w:W ring`; `u:A->W`; `p:A`; `q:A`; `y:W`]
    INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[RING_MUL_SYM] THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_IN_CARRIER] THEN
    ASM_MESON_TAC[RING_MUL_SYM; RING_HOMOMORPHISM_IN_CARRIER];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC INTEGRAL_UFD_HOMOGENEOUS_DIVIDES THEN
  MAP_EVERY EXISTS_TAC [`c:num->A`; `n:num`] THEN
  ASM_SIMP_TAC[PID_IMP_UFD] THEN
  MP_TAC(ISPECL [`r:A ring`; `w:W ring`; `u:A->W`; `p:A`; `q:A`; `y:W`;
                 `c:num->A`; `n:num`] INTEGRAL_HOMOGENEOUS_RELATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RING_MUL_SYM; RING_HOMOMORPHISM_IN_CARRIER];
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    W(fun (asl,w) -> MP_TAC(ISPECL [`r:A ring`; `w:W ring`; `u:A->W`; lhs w]
      RING_MONOMORPHISM_EQ_0)) THEN
    ASM_SIMP_TAC[RING_ADD; RING_POW; RING_SUM]]);;

let INTEGRALLY_CLOSED_INTEGRAL_IMAGE = prove
 (`!(r:A ring) (l:C ring) h y.
        integrally_closed r /\ ring_monomorphism(fraction_ring r,l) h /\
        y IN IMAGE h (ring_carrier(fraction_ring r)) /\
        integral_element (r,l) (h o ring_fractionate r {a | ring_regular r a})
                         y
        ==> y IN IMAGE (h o ring_fractionate r {a | ring_regular r a})
                       (ring_carrier r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:A#A->bool` STRIP_ASSUME_TAC)
    MP_TAC))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `fraction_ring(r:A ring)`; `l:C ring`;
                 `ring_fractionate (r:A ring) {a | ring_regular r a}`;
                 `h:(A#A->bool)->C`; `q:A#A->bool`]
    INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_FRACTIONATE;
               RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `integrally_closed(r:A ring)` THEN
  REWRITE_TAC[integrally_closed] THEN
  DISCH_THEN(MP_TAC o SPEC `q:A#A->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_IMAGE; o_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integral closure and localization.                                        *)
(* ------------------------------------------------------------------------- *)

(* Finitely many elements of a localization have a common denominator (a     *)
(* generic fact about ring_localization; natural home ringtheory.ml).        *)

let RING_LOCALIZATION_COMMON_DENOMINATOR = prove
 (`!r s t:(A#A->bool)->bool.
        ring_multsys r s /\ FINITE t /\
        t SUBSET ring_carrier(ring_localization r s)
        ==> ?d. d IN s /\
                !x. x IN t
                    ==> ?a. a IN ring_carrier r /\
                            ring_mul (ring_localization r s)
                              (ring_fractionate r s d) x =
                            ring_fractionate r s a`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ring_multsys; SUBSET]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_FRACTIONATE) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; INSERT_SUBSET; FORALL_IN_INSERT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A#A->bool`; `t:(A#A->bool)->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `y IN ring_carrier(ring_localization r (s:A->bool))` THEN
  ASM_SIMP_TAC[RING_LOCALIZATION_CARRIER; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  EXISTS_TAC `ring_mul r d b:A` THEN
  SUBGOAL_THEN `(d:A) IN ring_carrier r /\ (b:A) IN ring_carrier r`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_MUL;
    MATCH_MP RING_HOMOMORPHISM_MUL th; GSYM RING_MUL_ASSOC;
    RING_FRACTIONATE_IN_CARRIER; RING_LOCALEQUIV_IN_CARRIER;
    LOCALEQUIV_MUL_RCANCEL]) THEN
  CONJ_TAC THENL
   [EXISTS_TAC `ring_mul r d a:A` THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_MUL;
      MATCH_MP RING_HOMOMORPHISM_MUL th]);
    ALL_TAC] THEN
  X_GEN_TAC `x:A#A->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A#A->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ring_mul r b c:A` THEN
  SUBGOAL_THEN `x IN ring_carrier(ring_localization r (s:A->bool))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_localization r (s:A->bool)`;
    `ring_fractionate r s (d:A)`; `ring_fractionate r s (b:A)`]
    RING_MUL_SYM) THEN
  ASM_SIMP_TAC[RING_FRACTIONATE_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[RING_MUL;
    MATCH_MP RING_HOMOMORPHISM_MUL th; GSYM RING_MUL_ASSOC;
    RING_FRACTIONATE_IN_CARRIER]));;

(* Localizations of integrally closed domains at multiplicative sets not     *)
(* containing 0 are integrally closed. Route: INTEGRALLY_CLOSED_ALT on both  *)
(* sides. Given H(x,y) = 0 in the localization (f = ring_fractionate), take  *)
(* a common denominator d of x, y and the coefficients c_i: f d x = f a,     *)
(* f d y = f b and f d c_i = f e_i. By the local lemma the image of the      *)
(* homogeneous form H(da,b) with coefficients d^(n-1-i) e_i is               *)
(* f(d)^n f(d)^n H(x,y) = 0; f is injective, so b divides da, and as f d is  *)
(* a unit, y divides x.                                                      *)

let INTEGRALLY_CLOSED_LOCALIZATION = prove
 (`!r s:A->bool.
        integrally_closed r /\ ring_multsys r s /\ ~(ring_0 r IN s)
        ==> integrally_closed (ring_localization r s)`,
  let lemma = prove
   (`!r t (f:A->B) d a b e x y c n.
        ring_homomorphism(r,t) f /\
        d IN ring_carrier r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
        x IN ring_carrier t /\ y IN ring_carrier t /\
        ring_mul t (f d) x = f a /\ ring_mul t (f d) y = f b /\
        (!i. i < n ==> e i IN ring_carrier r /\ c i IN ring_carrier t /\
                       ring_mul t (f d) (c i) = f(e i))
        ==> f(ring_add r (ring_pow r (ring_mul r d a) n)
                (ring_sum r {i | i < n}
                   (\i. ring_mul r (ring_mul r (ring_pow r d (n - SUC i)) (e i))
                          (ring_mul r (ring_pow r (ring_mul r d a) i)
                                      (ring_pow r b (n - i)))))) =
            ring_mul t (ring_pow t (f d) n)
              (ring_mul t (ring_pow t (f d) n)
                (ring_add t (ring_pow t x n)
                  (ring_sum t {i | i < n}
                    (\i. ring_mul t (c i)
                           (ring_mul t (ring_pow t x i)
                                       (ring_pow t y (n - i)))))))`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[FORALL_AND_THM;
                TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(f:A->B) d IN ring_carrier t` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`r:A ring`; `t:B ring`; `f:A->B`; `ring_mul r d a:A`; `b:A`;
      `\i. ring_mul r (ring_pow r d (n - SUC i)) ((e:num->A) i)`; `n:num`]
     INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; RING_POW]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
    UNDISCH_THEN `ring_mul t ((f:A->B) d) x = f a` (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN `ring_mul t ((f:A->B) d) y = f b` (SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`t:B ring`; `(f:A->B) d`; `x:B`; `y:B`; `c:num->B`; `n:num`]
      INTEGRAL_HOMOGENEOUS_SCALE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`t:B ring`; `(f:A->B) d`; `ring_mul t ((f:A->B) d) x`;
                   `ring_mul t ((f:A->B) d) y`; `c:num->B`; `n:num`]
      INTEGRAL_HOMOGENEOUS_SCALE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `n - i = SUC(n - SUC i)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
       MATCH_MP RING_HOMOMORPHISM_POW th; RING_POW]) THEN
    UNDISCH_THEN `!i:num. i < n ==> ring_mul t ((f:A->B) d) (c i) = f(e i)`
     (MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(c:num->B) i IN ring_carrier t` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_MUL_POW; ring_pow; RING_MUL; RING_POW] THEN
    RING_TAC) in
  REPEAT GEN_TAC THEN REWRITE_TAC[INTEGRALLY_CLOSED_ALT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "div"))
    STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_LOCALIZATION] THEN
  SUBGOAL_THEN
   `ring_monomorphism (r,ring_localization r s)
                      (ring_fractionate r (s:A->bool))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_MONOMORPHISM_FRACTIONATE_GEN; SUBSET; IN_ELIM_THM;
                 INTEGRAL_DOMAIN_REGULAR] THEN
    ASM_MESON_TAC[RING_MULTSYS];
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)] THEN
  MAP_EVERY X_GEN_TAC
   [`x:A#A->bool`; `y:A#A->bool`; `c:num->A#A->bool`; `n:num`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`;
    `(x:A#A->bool) INSERT y INSERT IMAGE (c:num->A#A->bool) {i | i < n}`]
    RING_LOCALIZATION_COMMON_DENOMINATOR) THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; FINITE_NUMSEG_LT; INSERT_SUBSET;
               SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FORALL_IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `e:num->A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(d:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MULTSYS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_unit (ring_localization r s) (ring_fractionate r s (d:A)) /\
    ring_fractionate r s d IN ring_carrier (ring_localization r s)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_UNIT_FRACTIONATE; RING_FRACTIONATE_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_associates (ring_localization r s) y (ring_fractionate r s b) /\
    ring_associates (ring_localization r s) x
      (ring_fractionate r s (ring_mul r d a:A))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
    UNDISCH_THEN `ring_mul (ring_localization r s) (ring_fractionate r s d) x =
                  ring_fractionate r s (a:A)` (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN `ring_mul (ring_localization r s) (ring_fractionate r s d) y =
                  ring_fractionate r s (b:A)` (SUBST1_TAC o SYM) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_ASSOCIATES_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RING_ASSOCIATES_TRANS THEN
      EXISTS_TAC `ring_mul (ring_localization r s)
                    (ring_fractionate r s (d:A)) x` THEN
      CONJ_TAC THEN MATCH_MP_TAC RING_ASSOCIATES_LMUL THEN
      ASM_SIMP_TAC[RING_MUL]];
    ALL_TAC] THEN
  REMOVE_THEN "div" (MP_TAC o SPECL
   [`ring_mul r d a:A`; `b:A`;
    `\i. ring_mul r (ring_pow r d (n - SUC i)) ((e:num->A) i)`; `n:num`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_MUL; RING_POW] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(MATCH_MP RING_ASSOCIATES_EQ_0 (ASSUME
       `ring_associates (ring_localization r s) y
                        (ring_fractionate r s (b:A))`)) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]);
      FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [RING_MONOMORPHISM_ALT]) THEN
      ASM_SIMP_TAC[RING_ADD; RING_POW; RING_SUM; RING_MUL] THEN
      MP_TAC(ISPECL [`r:A ring`; `ring_localization r (s:A->bool)`;
        `ring_fractionate r (s:A->bool)`; `d:A`; `a:A`; `b:A`; `e:num->A`;
        `x:A#A->bool`; `y:A#A->bool`; `c:num->A#A->bool`; `n:num`]
        lemma) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[RING_MUL_RZERO; RING_POW]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `ring_localization r (s:A->bool)`;
      `ring_fractionate r (s:A->bool)`; `b:A`; `ring_mul r d a:A`]
      RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC RING_ASSOCIATES_DIVIDES THEN
    ONCE_REWRITE_TAC[RING_ASSOCIATES_SYM] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Integral elements over any ring: intermediate rings, monic divisors,      *)
(* minimal polynomials, traces and norms.                                    *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_ELEMENT_INTERMEDIATE = prove
 (`!r:A ring s:B ring t:C ring f g x.
        ring_homomorphism(r,s) f /\ ring_homomorphism(s,t) g /\
        integral_element (r,t) (g o f) x
        ==> integral_element (s,t) g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(r,t) ((g:B->C) o (f:A->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `s:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `t:C ring`; `(g:B->C) o (f:A->B)`; `x:C`]
    INTEGRAL_ELEMENT_RELATION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:num->A`] THEN
  REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `(f:A->B) o (c:num->A)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
  EXISTS_TAC `r:A ring` THEN ASM_SIMP_TAC[]);;

let INTEGRAL_ELEMENT_MONIC_DIVISOR = prove
 (`!r:A ring k:B ring h p q.
        ring_homomorphism(r,k) h /\ field k /\
        p IN ring_carrier(poly_ring k (:1)) /\ monic k p /\
        q IN ring_carrier(poly_ring r (:1)) /\ monic r q /\
        ring_divides (poly_ring k (:1)) p (h o q)
        ==> !i. integral_element (r,k) h (coeff i p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN
  MP_TAC(ISPECL [`k:B ring`; `p:(1->num)->B`]
    SPLITTING_EXTENSION_EXISTS_BIGENOUGH) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[MONIC_IMP_NONZERO; RING_POLYNOMIAL;
                  FIELD_IMP_NONTRIVIAL_RING];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`l:(B#num)ring`; `e:B->B#num`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SPLITTING_EXTENSION_SPLITS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SPLITTING_IMP_FIELD_EXTENSION) THEN
  REWRITE_TAC[poly_splits_over; field_extension] THEN STRIP_TAC THEN
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `ring_homomorphism(r,l) ((e:B->B#num) o (h:A->B))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE]; ALL_TAC] THEN
  ABBREV_TAC
   `S = {x | integral_element (r,l) ((e:B->B#num) o (h:A->B)) x}` THEN
  SUBGOAL_THEN `(S:B#num->bool) subring_of l` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `monic l ((e:B->B#num) o (p:(1->num)->B))` ASSUME_TAC THENL
   [REWRITE_TAC[monic; COEFF_COMPOSE] THEN
    SUBGOAL_THEN `poly_deg l ((e:B->B#num) o (p:(1->num)->B)) = poly_deg k p`
    SUBST1_TAC THENL
     [MATCH_MP_TAC POLY_DEG_MONOMORPHIC_IMAGE THEN
      ASM_MESON_TAC[RING_POLYNOMIAL];
      ALL_TAC] THEN
    UNDISCH_TAC `monic k (p:(1->num)->B)` THEN REWRITE_TAC[monic] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[RING_HOMOMORPHISM_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?s. s IN ring_carrier(poly_ring l (:1)) /\
        ((e:B->B#num) o (h:A->B)) o (q:(1->num)->A) =
        poly_mul l ((e:B->B#num) o (p:(1->num)->B)) s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM o_ASSOC] THEN
    MP_TAC(ISPECL [`poly_ring (k:B ring) (:1)`;
                   `poly_ring (l:(B#num)ring) (:1)`;
                   `\p:(1->num)->B. (e:B->B#num) o p`;
                   `p:(1->num)->B`;
                   `(h:A->B) o (q:(1->num)->A)`]
      RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_RINGS] THEN
    REWRITE_TAC[ring_divides; POLY_RING_CLAUSES] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ring_carrier l /\
        poly_eval l ((e:B->B#num) o (p:(1->num)->B)) z = ring_0 l
        ==> z IN S`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:B#num` THEN STRIP_TAC THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; integral_element] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `q:(1->num)->A` THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval] THEN
    SUBGOAL_THEN
     `(e:B->B#num) o (p:(1->num)->B) IN ring_carrier(poly_ring l (:1))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC `k:B ring` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_MUL o lhand o snd) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RING_MUL_LZERO THEN REWRITE_TAC[POLY_EVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(B#num)ring`; `S:B#num->bool`;
                 `(e:B->B#num) o (p:(1->num)->B)`]
    POLY_SPLITS_IN_SUBRING_MONIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP POLY_SPLITS_IN_CARRIER) THEN
  DISCH_THEN(MP_TAC o SPEC `(\v:1. i:num)` o
    MATCH_MP POLY_MONOMIAL_IN_CARRIER) THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; o_THM] THEN
  EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:(B#num)ring`;
                 `h:A->B`; `e:B->B#num`;
                 `coeff i (p:(1->num)->B)`]
    INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[COEFF] THEN
  ASM_MESON_TAC[POLY_MONOMIAL_IN_CARRIER]);;

let INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL = prove
 (`!r:A ring k:B ring l:C ring h g x.
        ring_homomorphism(r,k) h /\ field_extension(k,l) g /\
        integral_element (r,l) (g o h) x
        ==> algebraic_over (k,l) g x /\
            !i. integral_element (r,k) h
                  (coeff i (minimal_polynomial (k,l) g x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `ring_homomorphism(r,l) ((g:B->C) o (h:A->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [integral_element]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(h:A->B) o (q:(1->num)->A) IN ring_carrier(poly_ring k (:1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `r:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `monic k ((h:A->B) o (q:(1->num)->A))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `q:(1->num)->A`]
      MONIC_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_extend (k,l) (g:B->C) (\v:1. x) ((h:A->B) o (q:(1->num)->A)) =
    ring_0 l`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; o_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over (k,l) (g:B->C) x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[algebraic_over] THEN
    EXISTS_TAC `(h:A->B) o (q:(1->num)->A)` THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES] THEN
    MATCH_MP_TAC MONIC_IMP_NONZERO THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL; FIELD_IMP_NONTRIVIAL_RING];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_MONIC_DIVISOR THEN
  EXISTS_TAC `q:(1->num)->A` THEN
  ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_DIVIDES; MINIMAL_POLYNOMIAL_IN_CARRIER;
               MINIMAL_POLYNOMIAL_MONIC]);;

let ALGEBRA_TRACE_NORM_INTEGRAL = prove
 (`!r:A ring k:B ring l:C ring h g x.
        ring_homomorphism(r,k) h /\ finite_extension(k,l) g /\
        integral_element (r,l) (g o h) x
        ==> integral_element (r,k) h (algebra_trace (k,l) g x) /\
            integral_element (r,k) h (algebra_norm (k,l) g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:C ring`; `h:A->B`; `g:B->C`;
                 `x:C`] INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER) THEN
  ASM_SIMP_TAC[ALGEBRA_TRACE_MINIMAL_POLYNOMIAL;
               ALGEBRA_NORM_MINIMAL_POLYNOMIAL] THEN
  ABBREV_TAC `S = {y | integral_element (r,k) (h:A->B) y}` THEN
  SUBGOAL_THEN `(S:B->bool) subring_of k` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. coeff i (minimal_polynomial (k,l) (g:B->C) x) IN (S:B->bool)`
  MP_TAC THENL [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. integral_element (r,k) (h:A->B) y <=> y IN S`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]; DISCH_TAC] THEN
  REPEAT(FIRST[CONJ_TAC; FIRST_ASSUM MATCH_ACCEPT_TAC;
                MATCH_MP_TAC IN_SUBRING_POW; MATCH_MP_TAC IN_SUBRING_MUL;
                MATCH_MP_TAC IN_SUBRING_NEG; MATCH_MP_TAC IN_SUBRING_NUM;
                MATCH_MP_TAC IN_SUBRING_1]));;

(* ------------------------------------------------------------------------- *)
(* Integrally closed domains with a field of fractions: the minimal          *)
(* polynomial criterion, traces, norms and units.                            *)
(* ------------------------------------------------------------------------- *)

let INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS = prove
 (`!r:A ring k:B ring h.
        field_of_fractions (r,k) h
        ==> (integrally_closed r <=>
             !x. integral_element (r,k) h x
                 ==> x IN IMAGE h (ring_carrier r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_OF_FRACTIONS_IMP_INTEGRAL_DOMAIN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `!a:A. a IN ring_carrier r ==> (h:A->B) a IN ring_carrier k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] RING_MONOMORPHISM_EQ_0)
   (ASSUME `ring_monomorphism(r,k) (h:A->B)`)) THEN
  SUBGOAL_THEN
   `!b:A. b IN ring_carrier r /\ ~(b = ring_0 r)
         ==> ring_regular k ((h:A->B) b)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_DOMAIN_REGULAR; FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INTEGRALLY_CLOSED_ALT] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B` o
      check (fun th -> is_forall(concl th) &&
             fst(dest_var(fst(dest_forall(concl th)))) = "x")) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ring_mul k x ((h:A->B) b) = h a` ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS `ring_mul k ((h:A->B) b) x` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
      INTEGRAL_ELEMENT_EXPLICIT) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `c:num->A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `a:A`; `b:A`; `x:B`]
      INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`c:num->A`; `n:num`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `a:A`; `b:A`; `x:B`;
                   `c:num->A`; `n:num`] INTEGRAL_HOMOGENEOUS_RELATION) THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_ADD; RING_POW; RING_SUM];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`; `c:num->A`; `n:num`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~((h:A->B) b = ring_0 k)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?x:B. x IN ring_carrier k /\ ring_mul k x (h b) = h(a:A)`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `ring_mul k ((h:A->B) a) (ring_inv k (h b))` THEN
      ASM_SIMP_TAC[RING_MUL; RING_INV] THEN
      ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_INV; FIELD_MUL_LINV;
                   RING_MUL_RID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `a:A`; `b:A`; `x:B`]
      INTEGRAL_MONOMORPHISM_IN_IMAGE) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->A`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `a:A`; `b:A`; `x:B`;
                   `c:num->A`; `n:num`] INTEGRAL_HOMOGENEOUS_RELATION) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[]]);;

let INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL = prove
 (`!r:A ring k:B ring l:C ring h g x.
        integrally_closed r /\ field_of_fractions (r,k) h /\
        field_extension(k,l) g /\ algebraic_over (k,l) g x
        ==> (integral_element (r,l) (g o h) x <=>
             !i. coeff i (minimal_polynomial (k,l) g x) IN
                 IMAGE h (ring_carrier r))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`]
      INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:C ring`; `h:A->B`; `g:B->C`;
                   `x:C`] INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:num->A`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> concl th = `ring_monomorphism(k,l) (g:B->C)`)) THEN
  MP_TAC(ISPECL [`g:B->C`; `k:B ring`; `l:C ring`; `x:C`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = minimal_polynomial (k,l) (g:B->C) x` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
  MAP_EVERY EXISTS_TAC [`poly_deg k (p:(1->num)->B)`; `a:num->A`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:B ring` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
    check (fun th -> rand(concl th) = `ring_0 l:C`)) THEN
  ASM_SIMP_TAC[POLY_EXTEND_MONIC_UNIVARIATE; o_THM]);;

let INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM = prove
 (`!r:A ring k:B ring l:C ring h g x.
        integrally_closed r /\ field_of_fractions (r,k) h /\
        finite_extension(k,l) g /\ integral_element (r,l) (g o h) x
        ==> algebra_trace (k,l) g x IN IMAGE h (ring_carrier r) /\
            algebra_norm (k,l) g x IN IMAGE h (ring_carrier r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_homomorphism(r,k) (h:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[field_of_fractions; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`]
    INTEGRALLY_CLOSED_FIELD_OF_FRACTIONS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:C ring`; `h:A->B`; `g:B->C`;
                 `x:C`] ALGEBRA_TRACE_NORM_INTEGRAL) THEN
  ASM_SIMP_TAC[]);;

let INTEGRALLY_CLOSED_UNIT_NORM = prove
 (`!r:A ring k:B ring l:C ring h g x.
        integrally_closed r /\ field_of_fractions (r,k) h /\
        finite_extension(k,l) g /\ integral_element (r,l) (g o h) x
        ==> ((?y. integral_element (r,l) (g o h) y /\
                  ring_mul l x y = ring_1 l) <=>
             ?u. ring_unit r u /\ algebra_norm (k,l) g x = h u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    check (fun th -> concl th = `field_extension(k,l) (g:B->C)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> concl th = `ring_monomorphism(k,l) (g:B->C)`)) THEN
  SUBGOAL_THEN `ring_homomorphism(r,l) ((g:B->C) o (h:A->B))` ASSUME_TAC
  THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER) THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:C` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP INTEGRAL_ELEMENT_IN_CARRIER o
      check (fun th ->
        concl th = `integral_element (r,l) ((g:B->C) o (h:A->B)) y`)) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:C ring`; `h:A->B`; `g:B->C`;
                   `x:C`] INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:C ring`; `h:A->B`; `g:B->C`;
                   `y:C`] INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[ring_unit] THEN
    EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_monomorphism] o
      check (fun th -> concl th = `ring_monomorphism(r,k) (h:A->B)`)) THEN
    ASM_SIMP_TAC[RING_MUL; RING_1] THEN
    TRANS_TAC EQ_TRANS `algebra_norm (k,l) (g:B->C) (ring_mul l x y)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[ALGEBRA_NORM_MUL] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP RING_HOMOMORPHISM_MUL o
        check (fun th -> concl th = `ring_homomorphism(r,k) (h:A->B)`)) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[ALGEBRA_NORM_1] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:C ring`; `h:A->B`; `g:B->C`;
                 `x:C`] INTEGRAL_ELEMENT_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:C ring`; `h:A->B`; `g:B->C`;
                 `x:C`] INTEGRALLY_CLOSED_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[IN_IMAGE; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num->A` (ASSUME_TAC o GSYM)) THEN
  MP_TAC(ISPECL [`g:B->C`; `k:B ring`; `l:C ring`; `x:C`]
    MINIMAL_POLYNOMIAL) THEN
  MP_TAC(ISPECL [`g:B->C`; `k:B ring`; `l:C ring`; `x:C`]
    ALGEBRA_NORM_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = minimal_polynomial (k,l) (g:B->C) x` THEN
  ABBREV_TAC
   `m = extension_degree
         (subfield_generated l (x INSERT IMAGE (g:B->C) (ring_carrier k)),l)
         I` THEN
  ABBREV_TAC `d = poly_deg k (p:(1->num)->B)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC IRREDUCIBLE_IMP_POLY_DEG_NZ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    MP_TAC(ISPECL [`g:B->C`; `k:B ring`; `l:C ring`;
                   `x INSERT IMAGE (g:B->C) (ring_carrier k)`]
      FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    ASM_SIMP_TAC[EXTENSION_DEGREE_EQ_0; FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. (a:num->A) i IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_pow r (ring_neg r (ring_1 r)) d IN ring_carrier r /\
    ring_unit r (ring_pow r (ring_neg r (ring_1 r)) d) /\
    (h:A->B)(ring_pow r (ring_neg r (ring_1 r)) d) =
    ring_pow k (ring_neg k (ring_1 k)) d`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[RING_POW; RING_NEG; RING_1; RING_UNIT_POW; RING_UNIT_NEG;
             RING_UNIT_1] THEN
    FIRST_ASSUM((fun th -> SIMP_TAC(RING_NEG :: RING_1 :: map (C MATCH_MP th)
     [RING_HOMOMORPHISM_POW; RING_HOMOMORPHISM_NEG; RING_HOMOMORPHISM_1])) o
     check (fun th -> concl th = `ring_homomorphism(r,k) (h:A->B)`));
    ALL_TAC] THEN
  ABBREV_TAC `e = ring_pow (r:A ring) (ring_neg r (ring_1 r)) d` THEN
  SUBGOAL_THEN `ring_unit r ((a:num->A) 0)` MP_TAC THENL
   [SUBGOAL_THEN `u = ring_pow r (ring_mul r e ((a:num->A) 0)) m`
    SUBST_ALL_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [ring_monomorphism] o
        check (fun th -> concl th = `ring_monomorphism(r,k) (h:A->B)`)) THEN
      ASM_SIMP_TAC[RING_POW; RING_MUL; RING_UNIT_IN_CARRIER] THEN
      FIRST_ASSUM((fun th -> ASM_SIMP_TAC(RING_MUL :: map (C MATCH_MP th)
       [RING_HOMOMORPHISM_POW; RING_HOMOMORPHISM_MUL])) o
       check (fun th -> concl th = `ring_homomorphism(r,k) (h:A->B)`));
      ALL_TAC] THEN
    UNDISCH_TAC
     `ring_unit r (ring_pow r (ring_mul r e ((a:num->A) 0)) m)` THEN
    ASM_SIMP_TAC[RING_UNIT_POW_EQ; RING_UNIT_MUL_EQ; RING_MUL];
    REWRITE_TAC[ring_unit] THEN
    DISCH_THEN(X_CHOOSE_THEN `a0:A` STRIP_ASSUME_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN
   `ring_add l (ring_pow l x d)
      (ring_sum l {i | i < d}
        (\i. ring_mul l ((g:B->C) (coeff i p)) (ring_pow l x i))) =
    ring_0 l`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      lhand(concl th) = `poly_extend (k,l) (g:B->C) (\v:1. x) p`)) THEN
    EXPAND_TAC "d" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC POLY_EXTEND_MONIC_UNIVARIATE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:C ring`; `x:C`; `\i. (g:B->C) (coeff i (p:(1->num)->B))`;
                 `d:num`] RING_MONIC_RELATION_FACTOR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC `k:B ring` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL];
    DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC
   `s = ring_add l (ring_pow l x (d - 1))
          (ring_sum l {i | i < d - 1}
            (\i. ring_mul l ((g:B->C) (coeff (i + 1) p))
                            (ring_pow l x i)))` THEN
  DISCH_TAC THEN
  EXISTS_TAC `ring_mul l (ring_neg l ((g:B->C) ((h:A->B) a0))) s` THEN
  SUBGOAL_THEN
   `!c. c IN ring_carrier r ==> (g:B->C) ((h:A->B) c) IN ring_carrier l`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `k:B ring` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `r:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ABBREV_TAC `t = {y | integral_element (r,l) ((g:B->C) o (h:A->B)) y}` THEN
    SUBGOAL_THEN `(t:C->bool) subring_of l` ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!c. c IN ring_carrier r ==> (g:B->C) ((h:A->B) c) IN t`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`r:A ring`; `l:C ring`; `(g:B->C) o (h:A->B)`; `c:A`]
        INTEGRAL_ELEMENT_IMAGE) THEN
      ASM_REWRITE_TAC[o_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:C) IN t` ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(s:C) IN t` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC IN_SUBRING_ADD THEN
      ASM_SIMP_TAC[IN_SUBRING_POW] THEN
      MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN
      ASM_SIMP_TAC[IN_SUBRING_POW] THEN
      FIRST_ASSUM((fun th ->
          REWRITE_TAC[GSYM(CONJUNCT1(SPEC `i + 1:num` th))]) o
        check (fun th -> is_forall(concl th) &&
               is_conj(snd(dest_forall(concl th))))) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul l (ring_neg l ((g:B->C) ((h:A->B) a0))) s IN t`
    MP_TAC THENL
     [MATCH_MP_TAC IN_SUBRING_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IN_SUBRING_NEG THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul l ((g:B->C) ((h:A->B) a0)) (g (h ((a:num->A) 0))) = ring_1 l`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `l:C ring`; `(g:B->C) o (h:A->B)`]
      RING_HOMOMORPHISM_MUL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`a0:A`; `(a:num->A) 0`]) THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `ring_mul r a0 ((a:num->A) 0) = ring_1 r` SUBST1_TAC THENL
     [ASM_MESON_TAC[RING_MUL_SYM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `l:C ring`; `(g:B->C) o (h:A->B)`]
      RING_HOMOMORPHISM_1) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:C) IN ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    SIMP_TAC[RING_ADD; RING_POW; RING_SUM; ASSUME `(x:C) IN ring_carrier l`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:B->C) (coeff 0 p) = g ((h:A->B) ((a:num->A) 0))`
  SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC
   `ring_add l ((g:B->C) ((h:A->B) ((a:num->A) 0))) (ring_mul l x s) =
    ring_0 l` THEN
  UNDISCH_TAC
   `ring_mul l ((g:B->C) ((h:A->B) a0)) (g (h ((a:num->A) 0))) = ring_1 l` THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul (l:C ring) b c = ring_1 l
    ==> ring_add l c (ring_mul l x s) = ring_0 l
        ==> ring_mul l x (ring_mul l (ring_neg l b) s) = ring_1 l`) THEN
  ASM_SIMP_TAC[]);;

let INTEGRAL_CLOSURE_UNIT_NORM = prove
 (`!r:A ring k:B ring l:C ring h g x.
        integrally_closed r /\ field_of_fractions (r,k) h /\
        finite_extension(k,l) g
        ==> (ring_unit
              (subring_generated l {y | integral_element (r,l) (g o h) y})
              x <=>
             integral_element (r,l) (g o h) x /\
             ?u. ring_unit r u /\ algebra_norm (k,l) g x = h u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{y | integral_element (r,l) ((g:B->C) o (h:A->B)) y} subring_of l`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:B ring` THEN
    ASM_MESON_TAC[field_of_fractions; RING_MONOMORPHISM_IMP_HOMOMORPHISM;
                  FINITE_IMP_FIELD_EXTENSION; FIELD_EXTENSION_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [ring_unit] THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; CONJUNCT2 SUBRING_GENERATED;
               IN_ELIM_THM] THEN
  ASM_CASES_TAC `integral_element (r,l) ((g:B->C) o (h:A->B)) x` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRALLY_CLOSED_UNIT_NORM THEN ASM_REWRITE_TAC[]);;
