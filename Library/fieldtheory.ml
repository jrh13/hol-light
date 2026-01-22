(* ========================================================================= *)
(* Basic field theory, in particular some properties of field extensions.    *)
(* ========================================================================= *)

needs "Library/matroids.ml";;
needs "Library/ringtheory.ml";;

(* ------------------------------------------------------------------------- *)
(* Subfields. This does *not* build in the assumption that the overring r    *)
(* is itself a field, just that s is. For example Q is a subfield of R[x].   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("subfield_of",(12,"right"));;

let subfield_of = new_definition
 `(s:A->bool) subfield_of (r:A ring) <=>
  s subring_of r /\ field(subring_generated r s)`;;

let SUBFIELD_IMP_SUBRING_OF = prove
 (`!r s:A->bool. s subfield_of r ==> s subring_of r`,
  SIMP_TAC[subfield_of]);;

let SUBFIELD_OF_IMP_SUBSET = prove
 (`!r s:A->bool. s subfield_of r ==> s SUBSET ring_carrier r`,
  SIMP_TAC[subring_of; subfield_of]);;

let SUBFIELD_OF_IMP_10 = prove
 (`!(r:A ring) s. s subfield_of r ==> ~(ring_1 r = ring_0 r)`,
  SIMP_TAC[subfield_of; field; SUBRING_GENERATED]);;

let SUBFIELD_OF_IMP_NONTRIVIAL = prove
 (`!(r:A ring) s. s subfield_of r ==> ~trivial_ring r`,
  REWRITE_TAC[TRIVIAL_RING_10; SUBFIELD_OF_IMP_10]);;

let IN_SUBFIELD_LINV = prove
 (`!r s x:A. s subfield_of r /\ x IN s /\ ~(x = ring_0 r)
             ==> ring_inv r x IN s /\ ring_mul r x (ring_inv r x) = ring_1 r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subfield_of; field; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN STRIP_TAC THEN
  ASM_METIS_TAC[RING_RINV_UNIQUE; SUBRING_OF_IMP_SUBSET; SUBSET]);;

let IN_SUBFIELD_RINV = prove
 (`!r s x:A. s subfield_of r /\ x IN s /\ ~(x = ring_0 r)
             ==> ring_inv r x IN s /\ ring_mul r (ring_inv r x) x = ring_1 r`,
  MESON_TAC[IN_SUBFIELD_LINV; RING_MUL_SYM; SUBFIELD_OF_IMP_SUBSET; SUBSET]);;

let IN_SUBFIELD_INV = prove
 (`!r s x:A. s subfield_of r /\ x IN s ==> ring_inv r x IN s`,
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[IN_SUBFIELD_LINV; RING_INV_0; IN_SUBRING_0; subfield_of]);;

let RING_INV_SUBRING_GENERATED = prove
 (`!r s x:A.
        s subfield_of r /\ x IN s /\ ~(x = ring_0 r)
        ==> ring_inv (subring_generated r s) x = ring_inv r x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_LINV_UNIQUE THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; SUBFIELD_IMP_SUBRING_OF;
               CONJUNCT2 SUBRING_GENERATED] THEN
  ASM_MESON_TAC[IN_SUBFIELD_RINV]);;

let SUBFIELD_OF_FIELD_INV = prove
 (`!k (s:A->bool).
        field k /\ s subring_of k /\
        (!x. x IN s ==> ring_inv k x IN s)
        ==> s subfield_of k`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[subfield_of] THEN
  ASM_SIMP_TAC[field; CONJUNCT2 SUBRING_GENERATED; FIELD_NONTRIVIAL;
               CARRIER_SUBRING_GENERATED_SUBRING] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN EXISTS_TAC `ring_inv k x:A` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC RING_MUL_RINV THEN
  ASM_SIMP_TAC[FIELD_UNIT] THEN ASM_MESON_TAC[subring_of; SUBSET]);;

let SUBFIELD_OF_INTERS = prove
 (`!r (gs:(A->bool)->bool).
        (!g. g IN gs ==> g subfield_of r) /\ ~(gs = {})
        ==> (INTERS gs) subfield_of r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subfield_of] THEN
  SIMP_TAC[SUBRING_OF_INTERS; field; CARRIER_SUBRING_GENERATED_SUBRING;
           CONJUNCT2 SUBRING_GENERATED] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:A->bool`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `g:A->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[IMP_CONJ]] THEN
  SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INTERS] THEN X_GEN_TAC `h:A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:A->bool`) THEN
  ASM_SIMP_TAC[IMP_CONJ; CARRIER_SUBRING_GENERATED_SUBRING] THEN
  DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  ASM SET_TAC[RING_RINV_UNIQUE; SUBRING_OF_IMP_SUBSET]);;

let SUBFIELD_OF_INTER = prove
 (`!r g h:A->bool.
        g subfield_of r /\ h subfield_of r ==> (g INTER h) subfield_of r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC SUBFIELD_OF_INTERS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; NOT_INSERT_EMPTY]);;

let CARRIER_SUBFIELD_OF = prove
 (`!r:A ring. ring_carrier r subfield_of r <=> field r`,
  REWRITE_TAC[subfield_of; CARRIER_SUBRING_OF] THEN
  REWRITE_TAC[SUBRING_GENERATED_RING_CARRIER]);;

let IN_SUBFIELD_0 = prove
 (`!r h:A->bool. h subfield_of r ==> ring_0 r IN h`,
  SIMP_TAC[subfield_of; IN_SUBRING_0]);;

let IN_SUBFIELD_1 = prove
 (`!r h:A->bool. h subfield_of r ==> ring_1 r IN h`,
  SIMP_TAC[subfield_of; IN_SUBRING_1]);;

let IN_SUBFIELD_NEG = prove
 (`!r h x:A. h subfield_of r /\ x IN h ==> ring_neg r x IN h`,
  SIMP_TAC[subfield_of; IN_SUBRING_NEG]);;

let IN_SUBFIELD_ADD = prove
 (`!r h x y:A. h subfield_of r /\ x IN h /\ y IN h ==> ring_add r x y IN h`,
  SIMP_TAC[subfield_of; IN_SUBRING_ADD]);;

let IN_SUBFIELD_MUL = prove
 (`!r h x y:A. h subfield_of r /\ x IN h /\ y IN h ==> ring_mul r x y IN h`,
  SIMP_TAC[subfield_of; IN_SUBRING_MUL]);;

let IN_SUBFIELD_SUB = prove
 (`!r h x y:A. h subfield_of r /\ x IN h /\ y IN h ==> ring_sub r x y IN h`,
  SIMP_TAC[subfield_of; IN_SUBRING_SUB]);;

let IN_SUBFIELD_POW = prove
 (`!r h (x:A) n. h subfield_of r /\ x IN h ==> ring_pow r x n IN h`,
  SIMP_TAC[subfield_of; IN_SUBRING_POW]);;

let IN_SUBFIELD_SUM = prove
 (`!r h (f:K->A) s.
        h subfield_of r /\ (!a. a IN s ==> f a IN h) ==> ring_sum r s f IN h`,
  SIMP_TAC[subfield_of; IN_SUBRING_SUM]);;

let IN_SUBFIELD_PRODUCT = prove
 (`!r h (f:K->A) s.
      h subfield_of r /\ (!a. a IN s ==> f a IN h) ==> ring_product r s f IN h`,
  SIMP_TAC[subfield_of; IN_SUBRING_PRODUCT]);;

let SUBFIELD_OF_HOMOMORPHIC_EQUALITIES = prove
 (`!k l (f:A->B) g.
        field k /\ field l /\
        ring_homomorphism(k,l) f /\ ring_homomorphism(k,l) g
        ==> {x | x IN ring_carrier k /\ f x = g x} subfield_of k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  ASM SET_TAC[FIELD_HOMOMORPHISM_INV; SUBRING_OF_HOMOMORPHIC_EQUALITIES;
              RING_INV]);;

let SUBFIELD_OF_FIXPOINTS = prove
 (`!k (f:A->A).
        field k /\ ring_endomorphism k f
        ==> {x | x IN ring_carrier k /\ f x = x} subfield_of k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_OF_HOMOMORPHIC_EQUALITIES THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_ID; ring_endomorphism]);;

let SUBFIELD_OF_SUBRING_QUOTIENTS = prove
 (`!r s:A->bool.
        ~(trivial_ring r) /\ s subring_of r /\
        (!x. x IN s /\ ~(x = ring_0 r) ==> ring_unit r x)
        ==> { ring_div r x y | x,y | x IN s /\ y IN s /\ ~(y = ring_0 r) }
            subfield_of r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subfield_of] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  SIMP_TAC[field; CARRIER_SUBRING_GENERATED_SUBRING] THEN
  REWRITE_TAC[NOT_IMP; SUBRING_GENERATED] THEN REWRITE_TAC[subring_of] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; SUBSET] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [subring_of]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; TRIVIAL_RING_10]) THEN
  SUBGOAL_THEN
   `!x:A. x IN s /\ ~(x = ring_0 r) ==> ring_mul r x (ring_inv r x) = ring_1 r`
  (LABEL_TAC "*") THENL [ASM_MESON_TAC[RING_MUL_RINV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[RING_DIV];
    MAP_EVERY EXISTS_TAC [`ring_0 r:A`; `ring_1 r:A`] THEN
    ASM_SIMP_TAC[RING_DIV_1; RING_0];
    MAP_EVERY EXISTS_TAC [`ring_1 r:A`; `ring_1 r:A`] THEN
    ASM_SIMP_TAC[RING_DIV_1; RING_1];
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ring_neg r a:A`; `b:A`] THEN
    ASM_SIMP_TAC[ring_div] THEN RING_TAC THEN ASM SET_TAC[RING_INV];
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`c:A`; `d:A`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`ring_add r (ring_mul r a d) (ring_mul r b c):A`;
      `ring_mul r b d:A`] THEN
    ASM_SIMP_TAC[ring_div; RING_INV_MUL] THEN REMOVE_THEN "*"
     (fun th -> MP_TAC(SPEC `d:A` th) THEN  MP_TAC(SPEC `b:A` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(ring_1 r:A = ring_0 r)` THEN
    RING_TAC THEN ASM_SIMP_TAC[RING_INV];
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`c:A`; `d:A`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`ring_mul r a c:A`; `ring_mul r b d:A`] THEN
    ASM_SIMP_TAC[ring_div; RING_INV_MUL] THEN REMOVE_THEN "*"
     (fun th -> MP_TAC(SPEC `d:A` th) THEN  MP_TAC(SPEC `b:A` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(ring_1 r:A = ring_0 r)` THEN
    RING_TAC THEN ASM_SIMP_TAC[RING_INV];
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    REWRITE_TAC[ring_div] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`b:A`; `a:A`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_INV; RING_MUL_LZERO]; DISCH_TAC] THEN
    REMOVE_THEN "*"
     (fun th -> MP_TAC(SPEC `b:A` th) THEN  MP_TAC(SPEC `a:A` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
    RING_TAC THEN ASM_SIMP_TAC[RING_INV]]);;

(* ------------------------------------------------------------------------- *)
(* Subfields generated by a set, totalized to whole ring in trivial case.    *)
(* ------------------------------------------------------------------------- *)

let subfield_generated = new_definition
 `subfield_generated r (s:A->bool) =
      ring((if ?h. h subfield_of r /\ (ring_carrier r INTER s) SUBSET h then
            INTERS {h | h subfield_of r /\ (ring_carrier r INTER s) SUBSET h}
            else ring_carrier r),
           ring_0 r,ring_1 r,ring_neg r,ring_add r,ring_mul r)`;;

let SUBFIELD_GENERATED = prove
 (`(!r s:A->bool.
        ring_carrier (subfield_generated r s) =
          if ?h. h subfield_of r /\ (ring_carrier r INTER s) SUBSET h then
            INTERS {h | h subfield_of r /\ (ring_carrier r INTER s) SUBSET h}
            else ring_carrier r) /\
   (!r s:A->bool. ring_0 (subfield_generated r s) = ring_0 r) /\
   (!r s:A->bool. ring_1 (subfield_generated r s) = ring_1 r) /\
   (!r s:A->bool. ring_neg (subfield_generated r s) = ring_neg r) /\
   (!r s:A->bool. ring_add (subfield_generated r s) = ring_add r) /\
   (!r s:A->bool. ring_mul (subfield_generated r s) = ring_mul r)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE
   (ISPEC(rand(rand(snd(strip_forall(concl subfield_generated)))))
   (CONJUNCT2 ring_tybij)))) THEN
  REWRITE_TAC[GSYM subfield_generated] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN
    ASM_REWRITE_TAC[ring_carrier; ring_0; ring_1; ring_neg;
                    ring_add; ring_mul]] THEN
  REPLICATE_TAC 4 (GEN_REWRITE_TAC I [CONJ_ASSOC]) THEN CONJ_TAC THENL
   [COND_CASES_TAC THEN
    SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
    REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
    MESON_TAC[subfield_of; subring_of];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `h:A->bool` STRIP_ASSUME_TAC) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `h:A->bool`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP SUBFIELD_OF_IMP_SUBSET) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]);
    ALL_TAC] THEN
  ASM_MESON_TAC[RING_ADD_SYM; RING_ADD_ASSOC; RING_ADD_LZERO; RING_ADD_LNEG;
    RING_MUL_SYM; RING_MUL_ASSOC; RING_MUL_LID; RING_ADD_LDISTRIB]);;

let CARRIER_SUBFIELD_GENERATED_FIELD = prove
 (`!r s:A->bool.
        field r
        ==> ring_carrier(subfield_generated r s) =
            INTERS {h | h subfield_of r /\ (ring_carrier r INTER s) SUBSET h}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBFIELD_GENERATED] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ring_carrier r:A->bool` o
    GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[CARRIER_SUBFIELD_OF] THEN SET_TAC[]);;

let CARRIER_SUBFIELD_GENERATED_SUBFIELD = prove
 (`!r s:A->bool.
        s subfield_of r ==> ring_carrier(subfield_generated r s) = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBFIELD_GENERATED] THEN
  ASM SET_TAC[SUBFIELD_OF_IMP_SUBSET]);;

let RING_CARRIER_SUBFIELD_GENERATED_SUBSET = prove
 (`!r h:A->bool.
        ring_carrier (subfield_generated r h) SUBSET ring_carrier r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBFIELD_GENERATED] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  ASM SET_TAC[SUBFIELD_OF_IMP_SUBSET]);;

let SUBFIELD_GENERATED_RESTRICT = prove
 (`!r s:A->bool.
        subfield_generated r s =
        subfield_generated r (ring_carrier r INTER s)`,
  REWRITE_TAC[subfield_generated; SET_RULE `g INTER g INTER s = g INTER s`]);;

let SUBFIELD_GENERATED_MONO = prove
 (`!r s t:A->bool.
        s SUBSET t
        ==> ring_carrier(subfield_generated r s) SUBSET
            ring_carrier(subfield_generated r t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBFIELD_GENERATED] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(MATCH_MP_TAC INTERS_ANTIMONO) THEN ASM SET_TAC[SUBFIELD_OF_IMP_SUBSET]);;

let SUBFIELD_GENERATED_MINIMAL = prove
 (`!r h s:A->bool.
        s SUBSET h /\ h subfield_of r
        ==> ring_carrier(subfield_generated r s) SUBSET h`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBFIELD_GENERATED] THEN
  ASM SET_TAC[SUBFIELD_OF_IMP_SUBSET]);;

let SUBRING_SUBSET_SUBFIELD_GENERATED = prove
 (`!r s:A->bool.
        ring_carrier(subring_generated r s) SUBSET
        ring_carrier(subfield_generated r s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBFIELD_GENERATED] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET] THEN
  REWRITE_TAC[SUBRING_GENERATED] THEN MATCH_MP_TAC INTERS_ANTIMONO THEN
  REWRITE_TAC[subfield_of] THEN SET_TAC[]);;

let SUBRING_SUBFIELD_GENERATED = prove
 (`!r s:A->bool.
        ring_carrier(subfield_generated r s) subring_of r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBFIELD_GENERATED] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CARRIER_SUBRING_OF] THEN
  MATCH_MP_TAC SUBRING_OF_INTERS THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  SIMP_TAC[subfield_of]);;

let SUBFIELD_GENERATED_TRIVIAL = prove
 (`!r s:A->bool.
        ~(?h. h subfield_of r /\ ring_carrier r INTER s SUBSET h)
        ==> subfield_generated r s = r`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RINGS_EQ; SUBFIELD_GENERATED]);;

let SUBRING_EQ_SUBFIELD_GENERATED = prove
 (`!r s:A->bool.
        field(subring_generated r s)
        ==> subring_generated r s = subfield_generated r s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RINGS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; CONJUNCT2 SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED] THEN
  ONCE_REWRITE_TAC[SUBFIELD_GENERATED_RESTRICT] THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
  ASM_REWRITE_TAC[SUBRING_GENERATED_SUBSET_CARRIER; subfield_of] THEN
  ASM_REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBRING_SUBRING_GENERATED]);;

let SUBRING_GENERATED_BY_SUBFIELD_GENERATED = prove
 (`!r s:A->bool.
        subring_generated r (ring_carrier(subfield_generated r s)) =
        subfield_generated r s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RINGS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; CONJUNCT2 SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    REWRITE_TAC[SUBRING_SUBFIELD_GENERATED; SUBSET_REFL];
    MATCH_MP_TAC SUBRING_GENERATED_SUBSET_CARRIER_SUBSET THEN
    REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET]]);;

let SUBFIELD_GENERATED_SUBSET_CARRIER = prove
 (`!r h:A->bool.
     ring_carrier r INTER h SUBSET ring_carrier(subfield_generated r h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBFIELD_GENERATED] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INTER_SUBSET] THEN ASM SET_TAC[]);;

let SUBFIELD_SUBFIELD_GENERATED_ALT = prove
 (`!r s:A->bool.
        ring_carrier(subfield_generated r s) subfield_of r <=>
        ?h. h subfield_of r /\ ring_carrier r INTER s SUBSET h`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC SUBFIELD_OF_INTERS THEN
  ASM_SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]);;

let SUBFIELD_SUBFIELD_GENERATED = prove
 (`!r s:A->bool.
        field r ==> ring_carrier(subfield_generated r s) subfield_of r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBFIELD_SUBFIELD_GENERATED_ALT] THEN
  EXISTS_TAC `ring_carrier r:A->bool` THEN
  ASM_REWRITE_TAC[CARRIER_SUBFIELD_OF; INTER_SUBSET]);;

let FIELD_SUBFIELD_GENERATED_ALT = prove
 (`!r s:A->bool. field(subfield_generated r s) <=>
                 ?h. h subfield_of r /\ ring_carrier r INTER s SUBSET h`,
  REWRITE_TAC[GSYM SUBFIELD_SUBFIELD_GENERATED_ALT] THEN
  REWRITE_TAC[subfield_of; SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[SUBRING_SUBFIELD_GENERATED]);;

let FIELD_SUBFIELD_GENERATED_EQ = prove
 (`!r s:A->bool.
        field(subfield_generated r s) <=>
        ring_carrier(subfield_generated r s) subfield_of r`,
  REWRITE_TAC[SUBFIELD_SUBFIELD_GENERATED_ALT; FIELD_SUBFIELD_GENERATED_ALT]);;

let SUBFIELD_SUBFIELD_GENERATED_EQ = prove
 (`!r s:A->bool.
        ring_carrier(subfield_generated r s) subfield_of r <=>
        field(subfield_generated r s)`,
  REWRITE_TAC[FIELD_SUBFIELD_GENERATED_EQ]);;

let FIELD_SUBFIELD_GENERATED = prove
 (`!r s:A->bool. field r ==> field(subfield_generated r s)`,
  MESON_TAC[SUBFIELD_SUBFIELD_GENERATED; subfield_of;
            SUBRING_GENERATED_BY_SUBFIELD_GENERATED]);;

let FIELD_SUBFIELD_GENERATED_MONO = prove
 (`!r s t:A->bool.
        s SUBSET t /\ field(subfield_generated r t)
        ==> field(subfield_generated r s)`,
  REWRITE_TAC[FIELD_SUBFIELD_GENERATED_ALT] THEN SET_TAC[]);;

let SUBFIELD_GENERATED_EQ = prove
 (`!r s:A->bool.
        subfield_generated r s = r <=>
        ring_carrier(subfield_generated r s) = ring_carrier r`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [RINGS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED]);;

let SUBFIELDS_GENERATED_EQ = prove
 (`!r s:A->bool.
     (!h. h subfield_of r
          ==> (ring_carrier r INTER s SUBSET h <=>
               ring_carrier r INTER t SUBSET h))
     ==> subfield_generated r s = subfield_generated r t`,
  REWRITE_TAC[TAUT `(p ==> (q <=> r)) <=> (p /\ q <=> p /\ r)`] THEN
  SIMP_TAC[subfield_generated]);;

let SUBFIELD_GENERATED_SUPERSET = prove
 (`!r s:A->bool.
    subfield_generated r s = r <=>
    ring_carrier r SUBSET ring_carrier(subfield_generated r s)`,
  REWRITE_TAC[SUBFIELD_GENERATED_EQ; GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET]);;

let FINITE_SUBFIELD_GENERATED = prove
 (`!r s:A->bool.
        FINITE(ring_carrier r)
        ==> FINITE(ring_carrier(subfield_generated r s))`,
  MESON_TAC[FINITE_SUBSET; RING_CARRIER_SUBFIELD_GENERATED_SUBSET]);;

let SUBSET_CARRIER_SUBFIELD_GENERATED = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier r /\ s SUBSET t
        ==> s SUBSET ring_carrier(subfield_generated r t)`,
  MESON_TAC[SUBSET_TRANS; SUBSET_INTER; SUBFIELD_GENERATED_SUBSET_CARRIER]);;

let SUBFIELD_GENERATED_MINIMAL_EQ = prove
 (`!r h s:A->bool.
        h subfield_of r
        ==> (ring_carrier(subfield_generated r s) SUBSET h <=>
             ring_carrier r INTER s SUBSET h)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
    REWRITE_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER];
    ONCE_REWRITE_TAC[SUBFIELD_GENERATED_RESTRICT] THEN
    ASM_SIMP_TAC[SUBFIELD_GENERATED_MINIMAL]]);;

let SUBFIELD_GENERATED_RING_CARRIER = prove
 (`!r:A ring. subfield_generated r (ring_carrier r) = r`,
  GEN_TAC THEN REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET] THEN
  MESON_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED; SUBRING_GENERATED_RING_CARRIER;
            SUBSET_TRANS]);;

let SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET = prove
 (`!r s:A->bool.
        s SUBSET ring_carrier r
        ==> s SUBSET ring_carrier(subfield_generated r s)`,
  MESON_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER;
            SET_RULE `s SUBSET t <=> t INTER s = s`]);;

let SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED = prove
 (`!r s:A->bool.
        subfield_generated r (ring_carrier(subfield_generated r s)) =
        subfield_generated r s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBFIELD_GENERATED] THEN
  ASM_CASES_TAC
   `ring_carrier (subfield_generated r s:A ring) subfield_of r` THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBFIELD_SUBFIELD_GENERATED_ALT]) THEN
  ASM_SIMP_TAC[SUBFIELD_GENERATED_TRIVIAL; SUBFIELD_GENERATED_RING_CARRIER]);;

let SUBFIELD_GENERATED_REFL = prove
 (`!r s:A->bool. ring_carrier r SUBSET s ==> subfield_generated r s = r`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SUBFIELD_GENERATED_RESTRICT] THEN
  ASM_SIMP_TAC[SET_RULE `u SUBSET s ==> u INTER s = u`] THEN
  REWRITE_TAC[SUBFIELD_GENERATED_RING_CARRIER]);;

let SUBFIELD_GENERATED_INC = prove
 (`!r s x:A.
        s SUBSET ring_carrier r /\ x IN s
        ==> x IN ring_carrier(subfield_generated r s)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; GSYM SUBSET] THEN
  REWRITE_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET]);;

let SUBFIELD_GENERATED_INC_GEN = prove
 (`!r s x:A.
        x IN ring_carrier r /\ x IN s
        ==> x IN ring_carrier(subfield_generated r s)`,
  MESON_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER; IN_INTER; SUBSET]);;

let SUBRING_OF_SUBFIELD_GENERATED_EQ = prove
 (`!r h k:A->bool.
        h subring_of (subfield_generated r k) <=>
        h subring_of r /\ h SUBSET ring_carrier(subfield_generated r k)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> r) /\ (r ==> (p <=> q)) ==> (p <=> q /\ r)`) THEN
  REWRITE_TAC[SUBRING_OF_IMP_SUBSET] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[subring_of; CONJUNCT2 SUBFIELD_GENERATED] THEN
  ASM SET_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET]);;

let SUBFIELD_OF_SUBFIELD_GENERATED_EQ = prove
 (`!r h k:A->bool.
        h subfield_of (subfield_generated r k) <=>
        h subfield_of r /\ h SUBSET ring_carrier(subfield_generated r k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[subfield_of; SUBRING_OF_SUBFIELD_GENERATED_EQ] THEN
  REWRITE_TAC[TAUT
    `((p /\ q) /\ r <=> (p /\ s) /\ q) <=> (p /\ q ==> (r <=> s))`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(h:A->bool) subring_of (subfield_generated r k)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBRING_OF_SUBFIELD_GENERATED_EQ];
    ASM_SIMP_TAC[field; CONJUNCT2 SUBFIELD_GENERATED; CONJUNCT2
                 SUBRING_GENERATED] THEN
    ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING]]);;

let SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ = prove
 (`!r h k:A->bool.
        k subfield_of r
        ==> (h subfield_of (subfield_generated r k) <=>
             h subfield_of r /\ h SUBSET k)`,
  REWRITE_TAC[SUBFIELD_OF_SUBFIELD_GENERATED_EQ] THEN
  SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD]);;

let SUBFIELD_OF_SUBFIELD_GENERATED = prove
 (`!r g h:A->bool.
        g subfield_of r /\ g SUBSET h
        ==> g subfield_of (subfield_generated r h)`,
  SIMP_TAC[SUBFIELD_OF_SUBFIELD_GENERATED_EQ] THEN
  SET_TAC[SUBFIELD_OF_IMP_SUBSET; SUBFIELD_GENERATED_SUBSET_CARRIER]);;

let SUBFIELD_OF_SUBFIELD_GENERATED_REV = prove
 (`!r g h:A->bool.
        g subfield_of (subfield_generated r h)
        ==> g subfield_of r`,
  SIMP_TAC[SUBFIELD_OF_SUBFIELD_GENERATED_EQ]);;

let SUBFIELD_GENERATED_IDEMPOT = prove
 (`!r s:A->bool.
        subfield_generated (subfield_generated r s) s =
        subfield_generated r s`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `subfield_generated r s:A ring = r` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
    SUBFIELD_GENERATED_TRIVIAL)) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> p) ==> p`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
    SUBFIELD_GENERATED_TRIVIAL)) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBFIELD_GENERATED] THEN
  ONCE_REWRITE_TAC[SUBFIELD_GENERATED] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC INTERS_ANTIMONO_GEN THEN X_GEN_TAC `h:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `j:A->bool` MP_TAC) THEN
    REWRITE_TAC[SUBFIELD_OF_SUBFIELD_GENERATED_EQ] THEN STRIP_TAC THEN
    EXISTS_TAC `h INTER j:A->bool` THEN ASM_SIMP_TAC[SUBFIELD_OF_INTER] THEN
    ASM SET_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET];
    EXISTS_TAC `h:A->bool` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBFIELD_OF_SUBFIELD_GENERATED_EQ]) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    ASM SET_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER]]);;

let SUBFIELD_GENERATED_SUBFIELD_GENERATED = prove
 (`!r s t:A->bool.
        s subfield_of r /\ t subfield_of r
        ==> subfield_generated (subfield_generated r s) t =
            subfield_generated r (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBFIELD_GENERATED] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SUBFIELD_GENERATED_RESTRICT] THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; SUBFIELD_OF_INTER] THEN
  MATCH_MP_TAC CARRIER_SUBFIELD_GENERATED_SUBFIELD THEN
  ASM_SIMP_TAC[SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ] THEN
  ASM_SIMP_TAC[INTER_SUBSET; SUBFIELD_OF_INTER]);;

let SUBRING_GENERATED_SUBFIELD_GENERATED = prove
 (`!r s:A->bool.
        subring_generated (subfield_generated r s) s =
        subring_generated r s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBRING_GENERATED;
              CONJUNCT2 SUBFIELD_GENERATED] THEN
  REWRITE_TAC[SUBRING_GENERATED; SUBRING_OF_SUBFIELD_GENERATED_EQ] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC INTERS_ANTIMONO_GEN THEN X_GEN_TAC `h:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THENL
   [EXISTS_TAC `h INTER ring_carrier (subfield_generated r s):A->bool` THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBRING_OF_INTER THEN
      ASM_REWRITE_TAC[SUBRING_SUBFIELD_GENERATED];
      ASM SET_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET]];
    EXISTS_TAC `h:A->bool` THEN
    ASM SET_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER]]);;

let TRIVIAL_RING_SUBFIELD_GENERATED = prove
 (`!r s:A->bool.
        trivial_ring(subfield_generated r s) <=> trivial_ring r`,
  REWRITE_TAC[TRIVIAL_RING_10; CONJUNCT2 SUBFIELD_GENERATED]);;

let SUBFIELD_GENERATED_UNION_LEFT = prove
 (`!r s t:A->bool.
        subfield_generated r (ring_carrier(subfield_generated r s) UNION t) =
        subfield_generated r (s UNION t)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBFIELDS_GENERATED_EQ THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNION_OVER_INTER; UNION_SUBSET] THEN
  ASM_SIMP_TAC[GSYM SUBFIELD_GENERATED_MINIMAL_EQ] THEN
  REWRITE_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED]);;

let SUBFIELD_GENERATED_UNION_RIGHT = prove
 (`!r s t:A->bool.
        subfield_generated r (s UNION ring_carrier(subfield_generated r t)) =
        subfield_generated r (s UNION t)`,
  ONCE_REWRITE_TAC[UNION_COMM] THEN
  REWRITE_TAC[SUBFIELD_GENERATED_UNION_LEFT]);;

let SUBFIELD_GENERATED_UNION = prove
 (`!r s t:A->bool.
        subfield_generated r (ring_carrier(subfield_generated r s) UNION
                              ring_carrier(subfield_generated r t)) =
        subfield_generated r (s UNION t)`,
  REWRITE_TAC[SUBFIELD_GENERATED_UNION_LEFT;
              SUBFIELD_GENERATED_UNION_RIGHT]);;

let SUBFIELD_OF_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) r r' s.
        ring_monomorphism(r,r') f /\ s subfield_of r
        ==> IMAGE f s subfield_of r'`,
  REWRITE_TAC[subfield_of] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM;
                  SUBRING_OF_HOMOMORPHIC_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_monomorphism (subring_generated r s:A ring,r') (f:A->B)`
  MP_TAC THENL
   [ASM_SIMP_TAC[RING_MONOMORPHISM_FROM_SUBRING_GENERATED];
    REWRITE_TAC[GSYM RING_ISOMORPHISM_ONTO_IMAGE]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_ISOMORPHIC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
  ASM_REWRITE_TAC[ring_image] THEN
  ASM_MESON_TAC[SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE;
                RING_MONOMORPHISM_IMP_HOMOMORPHISM; subring_of;
                CARRIER_SUBRING_GENERATED_SUBRING]);;

let SUBFIELD_OF_MONOMORPHIC_PREIMAGE = prove
 (`!r r' (f:A->B) h.
        ring_monomorphism(r,r') f /\
        h subfield_of r' /\
        h SUBSET IMAGE f (ring_carrier r)
        ==> {x | x IN ring_carrier r /\ f x IN h} subfield_of r`,
  REWRITE_TAC[subfield_of] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM;
                  SUBRING_OF_HOMOMORPHIC_PREIMAGE];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_monomorphism
     (subring_generated r {x | x IN ring_carrier r /\ f x IN h}:A ring,r')
     (f:A->B)`
  MP_TAC THENL
   [ASM_SIMP_TAC[RING_MONOMORPHISM_FROM_SUBRING_GENERATED];
    REWRITE_TAC[GSYM RING_ISOMORPHISM_ONTO_IMAGE]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_ISOMORPHIC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
  ASM_REWRITE_TAC[ring_image] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `field (subring_generated r' h:B ring)` THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL
   [`r:A ring`; `r':B ring`; `f:A->B`;
    `{x | x IN ring_carrier r /\ (f:A->B) x IN h}`]
   SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; SUBSET_RESTRICT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_IMAGE_PREIMAGE_EQ THEN
  EXISTS_TAC `r':B ring` THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; ring_image]);;

let SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE = prove
 (`!r r' (f:A->B) s.
        ring_monomorphism(r,r') f /\
        s SUBSET ring_carrier r /\
        field(subfield_generated r s)
        ==> ring_carrier (subfield_generated r' (IMAGE f s)) =
            IMAGE f (ring_carrier(subfield_generated r s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SET_RULE
     `IMAGE f s SUBSET t <=> s SUBSET {x | x IN s /\ f x IN t}`] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THENL
   [ASM_SIMP_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET; IMAGE_SUBSET] THEN
    MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
    EXISTS_TAC `r:A ring` THEN
    ASM_REWRITE_TAC[SUBFIELD_SUBFIELD_GENERATED_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[];
    DISCH_THEN(ASSUME_TAC o MATCH_MP (SET_RULE
     `s SUBSET {x | x IN t /\ P x} ==> s SUBSET t`))] THEN
  MATCH_MP_TAC SUBFIELD_OF_SUBFIELD_GENERATED_REV THEN
  EXISTS_TAC `s:A->bool` THEN
  MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_PREIMAGE THEN
  EXISTS_TAC `r':B ring` THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_FROM_SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBFIELD_SUBFIELD_GENERATED_ALT] THEN
    EXISTS_TAC `IMAGE (f:A->B) (ring_carrier(subfield_generated r s))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]];
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
    ASM_SIMP_TAC[IMAGE_SUBSET]] THEN
  MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
  ASM_MESON_TAC[SUBFIELD_SUBFIELD_GENERATED_EQ]);;

let RING_SUB_SUBFIELD_GENERATED = prove
 (`!r s:A->bool. ring_sub (subfield_generated r s) = ring_sub r`,
  REWRITE_TAC[FUN_EQ_THM; ring_sub; SUBFIELD_GENERATED]);;

let RING_POW_SUBFIELD_GENERATED = prove
 (`!r s:A->bool. ring_pow (subfield_generated r s) = ring_pow r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_pow; SUBFIELD_GENERATED]);;

let RING_OF_NUM_SUBFIELD_GENERATED = prove
 (`!r s:A->bool. ring_of_num (subfield_generated r s) = ring_of_num r`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ring_of_num; SUBFIELD_GENERATED]);;

let RING_OF_INT_SUBFIELD_GENERATED = prove
 (`!r s:A->bool. ring_of_int (subfield_generated r s) = ring_of_int r`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[ring_of_int; RING_OF_NUM_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[SUBFIELD_GENERATED]);;

let RING_CHAR_SUBFIELD_GENERATED = prove
 (`!r s:A->bool. ring_char(subfield_generated r s) = ring_char r`,
  REWRITE_TAC[RING_CHAR_UNIQUE] THEN
  REWRITE_TAC[SUBFIELD_GENERATED; RING_OF_NUM_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[RING_OF_NUM_EQ_0]);;

let RING_0_IN_SUBFIELD_GENERATED = prove
 (`!r (s:A->bool). ring_0 r IN ring_carrier (subfield_generated r s)`,
  MESON_TAC[RING_0; SUBFIELD_GENERATED]);;

let RING_1_IN_SUBFIELD_GENERATED = prove
 (`!r (s:A->bool). ring_1 r IN ring_carrier (subfield_generated r s)`,
  MESON_TAC[RING_1; SUBFIELD_GENERATED]);;

let RING_NEG_IN_SUBFIELD_GENERATED = prove
 (`!r s x:A.
        x IN ring_carrier (subfield_generated r s)
        ==> ring_neg r x IN ring_carrier (subfield_generated r s)`,
  MESON_TAC[RING_NEG; SUBFIELD_GENERATED]);;

let RING_ADD_IN_SUBFIELD_GENERATED = prove
 (`!r s x y:A.
        x IN ring_carrier (subfield_generated r s) /\
        y IN ring_carrier (subfield_generated r s)
        ==> ring_add r x y IN ring_carrier (subfield_generated r s)`,
  MESON_TAC[RING_ADD; SUBFIELD_GENERATED]);;

let RING_MUL_IN_SUBFIELD_GENERATED = prove
 (`!r s x y:A.
        x IN ring_carrier (subfield_generated r s) /\
        y IN ring_carrier (subfield_generated r s)
        ==> ring_mul r x y IN ring_carrier (subfield_generated r s)`,
  MESON_TAC[RING_MUL; SUBFIELD_GENERATED]);;

let RING_POW_IN_SUBFIELD_GENERATED = prove
 (`!r s (x:A) n.
        x IN ring_carrier (subfield_generated r s)
        ==> ring_pow r x n IN ring_carrier (subfield_generated r s)`,
  MESON_TAC[RING_POW; RING_POW_SUBFIELD_GENERATED]);;

let RING_INV_SUBFIELD_GENERATED = prove
 (`!r s x:A.
        field(subfield_generated r s) /\
        x IN ring_carrier(subfield_generated r s) /\
        ~(x = ring_0 r)
        ==> ring_inv (subfield_generated r s) x = ring_inv r x`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC RING_INV_SUBRING_GENERATED THEN
  ASM_REWRITE_TAC[SUBFIELD_SUBFIELD_GENERATED_EQ]);;

let RING_INV_IN_SUBFIELD_GENERATED = prove
 (`!r s x:A.
        field(subfield_generated r s) /\
        x IN ring_carrier(subfield_generated r s)
        ==> ring_inv r x IN ring_carrier(subfield_generated r s)`,
  MESON_TAC[RING_INV_0; RING_0_IN_SUBFIELD_GENERATED;
            RING_INV; RING_INV_SUBFIELD_GENERATED]);;

let RING_DIV_IN_SUBFIELD_GENERATED = prove
 (`!r s x y:A.
        field(subfield_generated r s) /\
        x IN ring_carrier (subfield_generated r s) /\
        y IN ring_carrier (subfield_generated r s)
        ==> ring_div r x y IN ring_carrier (subfield_generated r s)`,
  SIMP_TAC[ring_div; RING_MUL_IN_SUBFIELD_GENERATED;
           RING_INV_IN_SUBFIELD_GENERATED]);;

let SUBFIELD_GENERATED_INDUCT = prove
 (`!r P s:A->bool.
        field(subfield_generated r s) /\
        (!x. x IN ring_carrier r /\ x IN s ==> P x) /\
        P(ring_0 r) /\
        P(ring_1 r) /\
        (!x. x IN ring_carrier r /\ P x ==> P(ring_neg r x)) /\
        (!x. x IN ring_carrier r /\ ~(x = ring_0 r) /\ P x
             ==> P(ring_inv r x)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_add r x y)) /\
        (!x y. x IN ring_carrier r /\ y IN ring_carrier r /\ P x /\ P y
               ==> P(ring_mul r x y))
        ==> !x. x IN ring_carrier(subfield_generated r s) ==> P x`,
  MATCH_MP_TAC(MESON[]
   `(!k. field k ==> P k) /\ ((!k. field k ==> P k) ==> !r. P r)
    ==> !r. P r`) THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_carrier(subfield_generated k s) SUBSET
      {x:A | x IN ring_carrier k /\ P x}`
    MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    ONCE_REWRITE_TAC[SUBFIELD_GENERATED_RESTRICT] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
    CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC SUBFIELD_OF_FIELD_INV] THEN
    ASM_REWRITE_TAC[subring_of; IN_ELIM_THM; RING_0; RING_1] THEN
    SIMP_TAC[RING_NEG; RING_ADD; RING_MUL; RING_INV] THEN
    ASM SET_TAC[RING_INV_0];
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `subfield_generated r s:A ring`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`P:A->bool`; `s:A->bool`]) THEN
  REWRITE_TAC[SUBFIELD_GENERATED_IDEMPOT] THEN
  ASM_REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[RING_INV_SUBFIELD_GENERATED] THEN
  ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET]);;

let POLY_CONST_SUBFIELD_GENERATED = prove
 (`!r s. poly_const (subfield_generated r s):A->(V->num)->A = poly_const r`,
  REWRITE_TAC[FUN_EQ_THM; poly_const; CONJUNCT2 SUBFIELD_GENERATED]);;

let POLY_SUBFIELD_GENERATED_CLAUSES = prove
 (`(!(r:A ring) s (v:V->bool).
        ring_0 (poly_ring (subfield_generated r s) v) =
        ring_0 (poly_ring r v)) /\
   (!(r:A ring) s (v:V->bool).
        ring_1 (poly_ring (subfield_generated r s) v) =
        ring_1 (poly_ring r v)) /\
   (!(r:A ring) s (v:V->bool).
        ring_neg (poly_ring (subfield_generated r s) v) =
        ring_neg (poly_ring r v)) /\
   (!(r:A ring) s (v:V->bool).
        ring_add (poly_ring (subfield_generated r s) v) =
        ring_add (poly_ring r v)) /\
   (!(r:A ring) s (v:V->bool) p q.
        (!m. p m IN ring_carrier(subfield_generated r s)) /\
        (!m. q m IN ring_carrier(subfield_generated r s))
        ==> ring_mul (poly_ring (subfield_generated r s) v) p q =
            ring_mul (poly_ring r v) p q) /\
   (!(r:A ring) s (v:V->bool).
        ring_sub (poly_ring (subfield_generated r s) v) =
        ring_sub (poly_ring r v))`,
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[POLY_SUBRING_GENERATED_CLAUSES]);;

let FIELD_SUBFIELD_GENERATED_UNITS = prove
 (`!r s:A->bool.
        field(subfield_generated r s) <=>
        ~(trivial_ring r) /\
        !x. x IN ring_carrier(subring_generated r s) /\ ~(x = ring_0 r)
            ==> ring_unit r x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FIELD_IMP_NONTRIVIAL_RING) THEN
    SIMP_TAC[TRIVIAL_RING_SUBFIELD_GENERATED] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FIELD_EQ_ALL_UNITS]) THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    REWRITE_TAC[ring_unit; CONJUNCT2 SUBRING_GENERATED] THEN
    REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
     SUBRING_SUBSET_SUBFIELD_GENERATED) THEN
    MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
    SET_TAC[];
    STRIP_TAC THEN REWRITE_TAC[FIELD_SUBFIELD_GENERATED_ALT] THEN
    EXISTS_TAC
     `{ ring_div r x y | x,y |
        x IN ring_carrier(subring_generated r s) /\
        y IN ring_carrier(subring_generated r s) /\
        ~(y:A = ring_0 r) }` THEN
    ASM_SIMP_TAC[SUBFIELD_OF_SUBRING_QUOTIENTS; SUBRING_SUBRING_GENERATED] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `ring_1 r:A`] THEN
    ASM_SIMP_TAC[GSYM TRIVIAL_RING_10; RING_DIV_1] THEN
    REWRITE_TAC[RING_1_IN_SUBRING_GENERATED] THEN
    MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
      SUBRING_GENERATED_SUBSET_CARRIER) THEN
    ASM SET_TAC[]]);;

let SUBFIELD_GENERATED_SUBRING_QUOTIENTS = prove
 (`!r s:A->bool.
        ~(trivial_ring r) /\
        (!x. x IN ring_carrier(subring_generated r s) /\ ~(x = ring_0 r)
             ==> ring_unit r x)
        ==> subfield_generated r s =
            subring_generated r
             { ring_div r x y | x,y |
               x IN ring_carrier(subring_generated r s) /\
               y IN ring_carrier(subring_generated r s) /\
               ~(y = ring_0 r) }`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SUBFIELD_GENERATED_RESTRICT] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [SUBRING_GENERATED_RESTRICT] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV o ONCE_DEPTH_CONV)
   [SUBRING_GENERATED_RESTRICT] THEN
  MP_TAC(SET_RULE `ring_carrier r INTER s SUBSET ring_carrier(r:A ring)`) THEN
  SPEC_TAC(`ring_carrier r INTER s:A->bool`,`s:A->bool`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `ring_carrier(subring_generated r s):A->bool`]
    SUBFIELD_OF_SUBRING_QUOTIENTS) THEN
  ASM_REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`] FIELD_SUBFIELD_GENERATED_UNITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[RINGS_EQ] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; CONJUNCT2 SUBFIELD_GENERATED] THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; SUBFIELD_IMP_SUBRING_OF] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `ring_1 r:A`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[RING_1_IN_SUBRING_GENERATED; RING_DIV_1] THEN
    ASM_SIMP_TAC[GSYM TRIVIAL_RING_10; SUBRING_GENERATED_INC_GEN];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_DIV_IN_SUBFIELD_GENERATED THEN
    ASM SET_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED]]);;

let RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS = prove
 (`!r s:A->bool.
        ~(trivial_ring r) /\
        (!x. x IN ring_carrier(subring_generated r s) /\ ~(x = ring_0 r)
             ==> ring_unit r x)
        ==> ring_carrier(subfield_generated r s) =
             { ring_div r x y | x,y |
               x IN ring_carrier(subring_generated r s) /\
               y IN ring_carrier(subring_generated r s) /\
               ~(y = ring_0 r) }`,
  ASM_SIMP_TAC[SUBFIELD_GENERATED_SUBRING_QUOTIENTS] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN
  MATCH_MP_TAC SUBFIELD_IMP_SUBRING_OF THEN
  ASM_SIMP_TAC[SUBFIELD_OF_SUBRING_QUOTIENTS; SUBRING_SUBRING_GENERATED]);;

let SUBFIELD_GENERATED_QUOTIENTS = prove
 (`!r s x:A.
        field(subfield_generated r s) /\
        x IN ring_carrier (subfield_generated r s)
        ==> ?a b. a IN ring_carrier(subring_generated r s) /\
                  b IN ring_carrier(subring_generated r s) /\
                  ~(b = ring_0 r) /\
                  ring_div r a b = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
    [FIELD_SUBFIELD_GENERATED_UNITS]) THEN
  ASM_SIMP_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS] THEN
  SET_TAC[]);;

let FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR = prove
 (`!r s d:A->bool.
      field(subfield_generated r s) /\
      FINITE d /\
      d SUBSET ring_carrier(subfield_generated r s)
      ==> ?c. c IN ring_carrier(subring_generated r s) /\
              ~(c = ring_0 r) /\
              !x. x IN d
                  ==> ring_mul r c x IN ring_carrier(subring_generated r s)`,
  SUBGOAL_THEN
   `!r s d:A->bool.
        field r /\
        FINITE d /\
        d SUBSET ring_carrier(subfield_generated r s)
        ==> ?c. c IN ring_carrier(subring_generated r s) /\
                ~(c = ring_0 r) /\
                !x. x IN d
                    ==> ring_mul r c x IN ring_carrier(subring_generated r s)`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
      ISPECL [`subfield_generated r s:A ring`; `s:A->bool`; `d:A->bool`]) THEN
    ASM_REWRITE_TAC[SUBRING_GENERATED_SUBFIELD_GENERATED] THEN
    ASM_REWRITE_TAC[SUBFIELD_GENERATED_IDEMPOT] THEN
    REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED]] THEN
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[EMPTY_SUBSET; INSERT_SUBSET] THEN CONJ_TAC THENL
   [EXISTS_TAC `ring_1 r:A` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[RING_1_IN_SUBRING_GENERATED; field];
    REWRITE_TAC[FORALL_IN_INSERT]] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `d:A->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `y:A`]
        SUBFIELD_GENERATED_QUOTIENTS) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; FIELD_SUBFIELD_GENERATED] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  EXISTS_TAC `ring_mul r b c:A` THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_MUL_IN_SUBRING_GENERATED];
    ASM_MESON_TAC[REWRITE_RULE[SUBSET] RING_CARRIER_SUBRING_GENERATED_SUBSET;
                  FIELD_MUL_EQ_0];
    SUBGOAL_THEN `ring_mul r (ring_mul r b c) y:A = ring_mul r a c` SUBST1_TAC
    THENL [ALL_TAC; ASM_SIMP_TAC[RING_MUL_IN_SUBRING_GENERATED]] THEN
    EXPAND_TAC "y" THEN UNDISCH_TAC `~(b:A = ring_0 r)` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP
     (REWRITE_RULE[SUBSET] RING_CARRIER_SUBRING_GENERATED_SUBSET))) THEN
    UNDISCH_TAC `field(r: A ring)` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    FIELD_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `ring_mul r (ring_mul r b c) x:A = ring_mul r b (ring_mul r c x)`
    SUBST1_TAC THENL [RING_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET; RING_CARRIER_SUBRING_GENERATED_SUBSET;
                  RING_CARRIER_SUBFIELD_GENERATED_SUBSET;
                  RING_MUL_IN_SUBRING_GENERATED; RING_DIV]]);;

let POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR = prove
 (`!r s v (p:(V->num)->A).
        field (subfield_generated r s) /\
        p IN ring_carrier(poly_ring (subfield_generated r s) v)
        ==> ?d. d IN ring_carrier(subring_generated r s) /\
                ~(d = ring_0 r) /\
                poly_mul r (poly_const r d) p IN
                ring_carrier(poly_ring (subring_generated r s) v)`,
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[POLY_SUBRING_GENERATED_CLAUSES] THEN
  REWRITE_TAC[POLY_RING; ring_polynomial; IN_ELIM_THM; ring_powerseries] THEN
  REWRITE_TAC[poly_vars] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `IMAGE (p:(V->num)->A) UNIV`]
        FINITE_SUBSET_SUBFIELD_GENERATED_DENOMINATOR) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `ring_0 r INSERT IMAGE (p:(V->num)->A) {m | ~(p m = ring_0 r)}` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INSERT] THEN SET_TAC[];
    MATCH_MP_TAC MONO_EXISTS] THEN
  REWRITE_TAC[IN_UNIV] THEN X_GEN_TAC `d:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
  MP_TAC(ISPECL
   [`subfield_generated r s:A ring`; `d:A`; `p:(V->num)->A`]
   POLY_MUL_CONST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ring_polynomial; ring_powerseries;
                    CONJUNCT2 SUBFIELD_GENERATED] THEN
    ASM SET_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED];
    MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `(:V)`;
                   `poly_const r d:(V->num)->A`; `p:(V->num)->A`]
      (el 4 (CONJUNCTS POLY_SUBFIELD_GENERATED_CLAUSES))) THEN
    ASM_REWRITE_TAC[POLY_RING; POLY_CONST_SUBFIELD_GENERATED]] THEN
  ANTS_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[poly_const] THEN
    ASM SET_TAC[RING_0_IN_SUBFIELD_GENERATED;
                SUBRING_SUBSET_SUBFIELD_GENERATED];
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED] THEN
  SUBGOAL_THEN
   `!m. ring_mul r d ((p:(V->num)->A) m) = ring_0 r <=> p m = ring_0 r`
   (fun th -> ASM_REWRITE_TAC[th] THEN ASM SET_TAC[]) THEN
  GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `d:A` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FIELD_MUL_EQ_0)) THEN
  ASM_REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; IMP_IMP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM SET_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED]);;

let IN_SUBFIELD_GENERATED_FINITARY = prove
 (`!r s x:A.
        x IN ring_carrier(subfield_generated r s)
        ==> ?t. FINITE t /\
                t SUBSET s /\
                x IN ring_carrier(subfield_generated r t)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `field(subfield_generated r s:A ring)` THENL
   [MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `x:A`]
      SUBFIELD_GENERATED_QUOTIENTS) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `z:A`] THEN STRIP_TAC THEN
    MAP_EVERY (MP_TAC o C ISPECL IN_SUBRING_GENERATED_FINITARY)
     [[`r:A ring`; `s:A->bool`; `z:A`];
      [`r:A ring`; `s:A->bool`; `y:A`]] THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
    X_GEN_TAC `u:A->bool` THEN STRIP_TAC THEN
    EXISTS_TAC `t UNION u:A->bool` THEN
    ASM_REWRITE_TAC[FINITE_UNION; UNION_SUBSET] THEN
    EXPAND_TAC "x" THEN MATCH_MP_TAC RING_DIV_IN_SUBFIELD_GENERATED THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[FIELD_SUBFIELD_GENERATED_MONO; UNION_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] SUBRING_SUBSET_SUBFIELD_GENERATED) THEN
    ASM_MESON_TAC[SUBRING_GENERATED_MONO; SUBSET; SUBSET_UNION];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [FIELD_SUBFIELD_GENERATED_UNITS]) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THENL
     [EXISTS_TAC `{}:A->bool` THEN
      ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET] THEN
      SUBGOAL_THEN `x:A = ring_0 r` SUBST1_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[trivial_ring]) THEN
        MP_TAC(ISPECL [`r:A ring`; `s:A->bool`]
           RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
        ASM SET_TAC[];
        ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        REWRITE_TAC[RING_0_IN_SUBRING_GENERATED]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
      REWRITE_TAC[NOT_IMP] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP IN_SUBRING_GENERATED_FINITARY) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:A->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `subfield_generated r t:A ring = r` SUBST1_TAC THENL
       [ALL_TAC; ASM SET_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET]] THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_TRIVIAL THEN
      REWRITE_TAC[GSYM FIELD_SUBFIELD_GENERATED_ALT] THEN
      REWRITE_TAC[FIELD_SUBFIELD_GENERATED_UNITS] THEN
      ASM_MESON_TAC[]]]);;

let PRIME_SUBFIELD_MINIMAL = prove
 (`!k s:A->bool.
        s subfield_of k
        ==> ring_carrier(subfield_generated k {ring_0 k}) SUBSET s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
  ASM_MESON_TAC[IN_SUBFIELD_0; SING_SUBSET]);;

let PRIME_SUBFIELD_EQ_SUBRING = prove
 (`!k:A ring.
        prime(ring_char k)
        ==> ring_carrier(subfield_generated k {ring_0 k}) =
            {ring_of_int k n | n IN (:int)}`,
  REWRITE_TAC[GSYM RING_CARRIER_SUBRING_GENERATED_0; GSYM FIELD_PRIME_SUBRING;
              SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  MESON_TAC[SUBRING_EQ_SUBFIELD_GENERATED]);;

let FROBENIUS_FIXED_FIELD = prove
 (`!k:A ring.
        field k /\ prime(ring_char k)
        ==> { x | x IN ring_carrier k /\ ring_pow k x (ring_char k) = x} =
            ring_carrier(subfield_generated k {ring_0 k})`,
  SIMP_TAC[PRIME_SUBFIELD_EQ_SUBRING; FROBENIUS_FIXED;
           FIELD_IMP_INTEGRAL_DOMAIN]);;

(* ------------------------------------------------------------------------- *)
(* Field extensions, allowing a general monomorphism. This does build        *)
(* in the assumption that both the rings involved are indeed fields.         *)
(* ------------------------------------------------------------------------- *)

let field_extension = new_definition
 `field_extension (k,l) (h:A->B) <=>
        field k /\ field l /\ ring_monomorphism(k,l) h`;;

let FIELD_EXTENSION_IMP_MONOMORPHISM = prove
 (`!(h:A->B) k l. field_extension (k,l) h ==> ring_monomorphism(k,l) h`,
  SIMP_TAC[field_extension]);;

let FIELD_EXTENSION_IMP_HOMOMORPHISM = prove
 (`!(h:A->B) k l. field_extension (k,l) h ==> ring_homomorphism(k,l) h`,
  SIMP_TAC[field_extension; ring_monomorphism]);;

let FIELD_EXTENSION_IMP_SUBSET = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> IMAGE h (ring_carrier k) SUBSET ring_carrier l`,
  MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM; ring_homomorphism]);;

let FIELD_EXTENSION_CARRIER = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ x IN ring_carrier k
        ==> h x IN ring_carrier l`,
  REWRITE_TAC[field_extension; ring_monomorphism; ring_homomorphism] THEN
  SET_TAC[]);;

let FIELD_EXTENSION_FROM_SUBRING_GENERATED = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h /\ field(subring_generated k s)
        ==> field_extension(subring_generated k s,l) h`,
  SIMP_TAC[field_extension; RING_MONOMORPHISM_FROM_SUBRING_GENERATED]);;

let FIELD_EXTENSION_EQ = prove
 (`!k l (f:A->B) f'.
        field_extension(k,l) f /\
        (!x. x IN ring_carrier k ==> f' x = f x)
        ==> field_extension (k,l) f'`,
  REWRITE_TAC[field_extension] THEN MESON_TAC[RING_MONOMORPHISM_EQ]);;

let FIELD_EXTENSION_REFL = prove
 (`!k:A ring. field_extension (k,k) I <=> field k`,
  REWRITE_TAC[field_extension; RING_MONOMORPHISM_I]);;

let FIELD_EXTENSION_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g
        ==> field_extension (k,m) (g o f)`,
  SIMP_TAC[field_extension] THEN MESON_TAC[RING_MONOMORPHISM_COMPOSE]);;

let FIELD_EXTENSION_ISOMORPHISM = prove
 (`!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism (k,l) f
        ==> field_extension (k,l) f`,
  REWRITE_TAC[field_extension] THEN
  MESON_TAC[ISOMORPHIC_RING_FIELDNESS; isomorphic_ring;
            RING_ISOMORPHISM_IMP_MONOMORPHISM]);;

let FIELD_EXTENSION_SUBRING_GENERATED = prove
 (`!(l:A ring) k.
        field_extension(subring_generated l k,l) I <=>
        field l /\ ring_carrier(subring_generated l k) subfield_of l`,
  REWRITE_TAC[field_extension; subfield_of] THEN
  REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] RING_MONOMORPHISM_INCLUSION] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  REWRITE_TAC[CONJ_ACI]);;

let FIELD_EXTENSION_INTO_SUBRING_GENERATED = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h /\
        s subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s
        ==> field_extension(k,subring_generated l s) h`,
  REWRITE_TAC[field_extension; subfield_of] THEN
  SIMP_TAC[RING_MONOMORPHISM_INTO_SUBRING]);;

let FIELD_EXTENSION_INTO_SUBFIELD_GENERATED = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h /\
        s subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET s
        ==> field_extension(k,subfield_generated l s) h`,
  MESON_TAC[SUBRING_EQ_SUBFIELD_GENERATED; subfield_of;
            FIELD_EXTENSION_INTO_SUBRING_GENERATED]);;

let KRONECKER_FIELD_EXTENSION = prove
 (`!(k:A ring) j.
        field k /\ maximal_ideal (poly_ring k (:1)) j
        ==> field_extension (k,quotient_ring (poly_ring k (:1)) j)
                            (ring_coset (poly_ring k (:1)) j o poly_const k)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[field_extension] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  ASM_SIMP_TAC[FIELD_QUOTIENT_RING] THEN
  REWRITE_TAC[RING_MONOMORPHISM_ALT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `poly_ring (k:A ring) (:1)` THEN
    REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST] THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[QUOTIENT_RING_0; o_THM; RING_COSET_EQ_IDEAL; POLY_CONST] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] FIELD_UNIT) THEN
  ASM_CASES_TAC `x:A = ring_0 k` THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `(:1)`; `x:A`] RING_UNIT_POLY_CONST) THEN
  ASM_MESON_TAC[RING_UNIT_NOT_IN_PRIME_IDEAL; MAXIMAL_IMP_PRIME_IDEAL]);;

let KRONECKER_SIMPLE_FIELD_EXTENSION = prove
 (`!(k:A ring) p.
      field k /\
      p IN ring_carrier(poly_ring k (:1)) /\ ~(poly_deg k p = 0) /\
      ~(?x. x IN ring_carrier k /\ poly_eval k p x = ring_0 k)
      ==> ?l h z:((1->num)->A)->bool.
                field_extension(k,l) h /\
                z IN ring_carrier l /\
                ~(z IN IMAGE h (ring_carrier k)) /\
                subring_generated l (z INSERT IMAGE h (ring_carrier k)) = l /\
                poly_eval l (h o p) z = ring_0 l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `p:(1->num)->A`]
    UFD_PRIME_FACTOR_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PID_IMP_UFD; PID_POLY_RING; RING_UNIT_POLY_DOMAIN;
                 INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN] THEN
    ASM_MESON_TAC[POLY_DEG_0; POLY_DEG_CONST; POLY_RING];
    DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `q IN ring_carrier(poly_ring (k:A ring) (:1))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_prime]; ALL_TAC] THEN
  ASM_CASES_TAC `q = ring_0 (poly_ring (k:A ring) (:1))` THENL
   [ASM_MESON_TAC[ring_prime]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`j = ideal_generated (poly_ring (k:A ring) (:1)) {q}`;
    `l = quotient_ring (poly_ring (k:A ring) (:1)) j`;
    `h = ring_coset (poly_ring (k:A ring) (:1)) j o poly_const k`;
    `z = ring_coset (poly_ring (k:A ring) (:1)) j (poly_var k one)`] THEN
  MAP_EVERY EXISTS_TAC
   [`l:(((1->num)->A)->bool)ring`;
    `h:A->((1->num)->A)->bool`;
    `z:((1->num)->A)->bool`] THEN
    SUBGOAL_THEN `maximal_ideal (poly_ring (k:A ring) (:1)) j` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN ASM_SIMP_TAC[MAXIMAL_IDEAL_SING; PID_POLY_RING] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE;
                 INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:((1->num)->A)->bool) IN ring_carrier l` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z"; "l"] THEN
    ASM_SIMP_TAC[QUOTIENT_RING; MAXIMAL_IMP_RING_IDEAL] THEN
    EXPAND_TAC "z" THEN REWRITE_TAC[SIMPLE_IMAGE; ETA_AX] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[POLY_VAR_UNIV];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`k:A ring`; `j:((1->num)->A)->bool`]
    KRONECKER_FIELD_EXTENSION) THEN
  ASM_REWRITE_TAC[field_extension] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(p ==> ~r) /\ q /\ r ==> ~p /\ q /\ r`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    ASM_MESON_TAC[RING_MONOMORPHISM_ALT; POLY_EVAL;
                  POLY_EVAL_HOMOMORPHIC_IMAGE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBRING_GENERATED_EQ] THEN
    MAP_EVERY EXPAND_TAC ["h"; "z"] THEN
    REWRITE_TAC[IMAGE_o; GSYM(CONJUNCT2 IMAGE_CLAUSES)] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_EPIMORPHISM_RING_COSET o
        MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
    ASM_REWRITE_TAC[ring_epimorphism] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC
     `poly_var (k:A ring) one INSERT IMAGE (poly_const k) (ring_carrier k)` o
     MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE)) THEN
    ASM_REWRITE_TAC[POLY_SUBRING_GENERATED_1;
                    SUBRING_GENERATED_RING_CARRIER] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
    SIMP_TAC[POLY_VAR_UNIV; POLY_CONST];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_RING_COSET o
        MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] POLY_EVAL_HOMOMORPHIC_IMAGE)) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  MAP_EVERY EXPAND_TAC ["h"; "z"] THEN REWRITE_TAC[GSYM o_ASSOC; o_THM] THEN
  DISCH_THEN(fun th ->
    W(MP_TAC o PART_MATCH (rand o rand) th o lhand o snd)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[POLY_VAR_UNIV] THEN
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[RING_HOMOMORPHISM_POLY_CONST];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_HOMOMORPHISM_0 o
    MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  EXPAND_TAC "h" THEN REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[poly_eval] THEN
  REWRITE_TAC[GSYM(MATCH_MP POLY_EXTEND_EVALUATE
   (ISPECL [`k:A ring`; `(:1)`] RING_HOMOMORPHISM_POLY_CONST))] THEN
  ASM_SIMP_TAC[ETA_ONE; POLY_EXTEND_ID; ETA_AX] THEN
  ASM_SIMP_TAC[RING_COSET_EQ; POLY_CONST; RING_0; MAXIMAL_IMP_RING_IDEAL] THEN
  ASM_SIMP_TAC[POLY_CONST_0; POLY_CLAUSES; RING_SUB_RZERO] THEN
  EXPAND_TAC "j" THEN ASM_SIMP_TAC[IN_IDEAL_GENERATED_SING]);;

(* ------------------------------------------------------------------------- *)
(* Linear span of a set of elements s in l with respect to a subfield/ring   *)
(* k, identified by a monomorphism h from k into l. The definition forces it *)
(* to be a subset of the carrier of l, regardless of other hypotheses.       *)
(* ------------------------------------------------------------------------- *)

let [ring_span_RULES;ring_span_INDUCT;ring_span_CASES] =
  let thr,thi,thc = new_inductive_set
   `(ring_0 (SND kl) IN ring_span kl (h:A->B) s) /\
    (!x. x IN s /\ x IN ring_carrier(SND kl) ==> x IN ring_span kl h s) /\
    (!x y. x IN ring_span kl h s /\ y IN ring_span kl h s
           ==> ring_add (SND kl) x y IN ring_span kl h s) /\
    (!a x. a IN ring_carrier(FST kl) /\
           h a IN ring_carrier(SND kl) /\
           x IN ring_span kl h s
           ==> ring_mul (SND kl) (h a) x IN ring_span kl h s)` in
  map (GENL [`h:A->B`; `k:A ring`; `l:B ring`] o REWRITE_RULE[] o
       SPECL [`(k:A ring),(l:B ring)`; `h:A->B`]) [thr;thi;thc];;

let [RING_SPAN_0; RING_SPAN_INC; RING_SPAN_ADD; RING_SPAN_MUL] =
  CONJUNCTS(REWRITE_RULE[FORALL_AND_THM] ring_span_RULES);;

let RING_SPAN_SUBSET = prove
 (`!(h:A->B) k l s. ring_span (k,l) h s SUBSET ring_carrier l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET] THEN
  MATCH_MP_TAC ring_span_INDUCT THEN
  ASM_SIMP_TAC[RING_0; RING_ADD; RING_MUL]);;

let RING_SPAN_SUPERSET_GEN = prove
 (`!(h:A->B) k l s. ring_carrier l INTER s SUBSET ring_span (k,l) h s`,
  SET_TAC[RING_SPAN_INC]);;

let RING_SPAN_SUPERSET = prove
 (`!(h:A->B) k l s.
        s SUBSET ring_carrier l ==> s SUBSET ring_span (k,l) h s`,
  SET_TAC[RING_SPAN_SUPERSET_GEN]);;

let RING_SPAN_SUPERSET_EQ = prove
 (`!(h:A->B) k l s. s SUBSET ring_span (k,l) h s <=> s SUBSET ring_carrier l`,
  SET_TAC[RING_SPAN_INC; RING_SPAN_SUBSET]);;

let RING_SPAN_MONO = prove
 (`!(h:A->B) k l s t.
        s SUBSET t ==> ring_span (k,l) h s SUBSET ring_span (k,l) h t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC ring_span_INDUCT THEN
  ASM_REWRITE_TAC[RING_SPAN_0; RING_SPAN_ADD; RING_SPAN_MUL] THEN
  ASM SET_TAC[RING_SPAN_INC]);;

let SUBSET_RING_SPAN = prove
 (`!(h:A->B) k l s t.
        ring_span (k,l) h s SUBSET ring_span (k,l) h t <=>
        ring_carrier l INTER s SUBSET ring_span (k,l) h t`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[RING_SPAN_SUPERSET_GEN; SUBSET_TRANS];
    REWRITE_TAC[SUBSET] THEN STRIP_TAC] THEN
  MATCH_MP_TAC ring_span_INDUCT THEN ASM SET_TAC[ring_span_RULES]);;

let RING_SPAN_RESTRICT = prove
 (`!(h:A->B) k l s.
        ring_span (k,l) h s = ring_span (k,l) h (ring_carrier l INTER s)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; INTER_SUBSET; RING_SPAN_MONO] THEN
  REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC ring_span_INDUCT THEN
  ASM_MESON_TAC[RING_SPAN_0; RING_SPAN_ADD; RING_SPAN_MUL;
                RING_SPAN_INC; IN_INTER]);;

let RING_SPAN_SPAN = prove
 (`!(h:A->B) k l s.
        ring_span (k,l) h (ring_span (k,l) h s) = ring_span (k,l) h s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  MESON_TAC[SUBSET_RING_SPAN; RING_SPAN_SUPERSET_GEN; SUBSET; IN_INTER;
            RING_SPAN_RESTRICT]);;

let RING_SPAN_FINITARY = prove
 (`!(h:A->B) k l s a.
        a IN ring_span (k,l) h s
        ==> ?t. FINITE t /\ t SUBSET s /\ a IN ring_span (k,l) h t`,
  REPLICATE_TAC 4 GEN_TAC THEN MATCH_MP_TAC ring_span_INDUCT THEN
  REWRITE_TAC[RING_SPAN_0] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{}:B->bool` THEN ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN EXISTS_TAC `{x:B}` THEN
    ASM_SIMP_TAC[FINITE_SING; SING_SUBSET; RING_SPAN_INC; IN_SING];
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `t:B->bool`) (X_CHOOSE_TAC `u:B->bool`)) THEN
    EXISTS_TAC `t UNION u:B->bool` THEN
    ASM_REWRITE_TAC[FINITE_UNION; UNION_SUBSET; SUBSET_REFL] THEN
    MATCH_MP_TAC RING_SPAN_ADD THEN
    ASM_MESON_TAC[RING_SPAN_MONO; SUBSET; IN_UNION];
    MESON_TAC[RING_SPAN_MUL]]);;

let RING_SPAN_NONEMPTY = prove
 (`!(h:A->B) k l s. ~(ring_span (k,l) h s = {})`,
  MESON_TAC[MEMBER_NOT_EMPTY; RING_SPAN_0]);;

let RING_SPAN_SELF = prove
 (`!(h:A->B) l k. ring_span (k,l) h (ring_carrier l) = ring_carrier l`,
  MESON_TAC[RING_SPAN_SUPERSET; RING_SPAN_SUBSET; SUBSET_ANTISYM;
            SUBSET_REFL]);;

let RING_SPAN_EMPTY = prove
 (`!(h:A->B) k l.
        ring_homomorphism(k,l) h ==> ring_span (k,l) h {} = {ring_0 l}`,
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SING_SUBSET; RING_SPAN_0] THEN
  REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC ring_span_INDUCT THEN
  REWRITE_TAC[IN_SING; NOT_IN_EMPTY] THEN
  ASM_SIMP_TAC[RING_MUL_RZERO; RING_0; RING_ADD_RZERO]);;

let RING_SPAN_NEG = prove
 (`!(h:A->B) k l s x.
        ring_homomorphism(k,l) h /\ x IN ring_span (k,l) h s
        ==> ring_neg l x IN ring_span (k,l) h s`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`;
                 `ring_neg k (ring_1 k):A`; `x:B`] RING_SPAN_MUL) THEN
  ASM_SIMP_TAC[RING_NEG; RING_1] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN RING_TAC THEN
  ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET; RING_0; RING_1]);;

let RING_SPAN_SUB = prove
 (`!(h:A->B) k l s x y.
        ring_homomorphism(k,l) h /\
        x IN ring_span (k,l) h s /\ y IN ring_span (k,l) h s
        ==> ring_sub l x y IN ring_span (k,l) h s`,
  MESON_TAC[ring_sub; RING_SPAN_NEG; RING_SPAN_ADD]);;

let RING_SPAN_SUM = prove
 (`!(h:A->B) k l f s (t:K->bool).
        (!i. i IN t ==> f i IN ring_span (k,l) h s)
        ==> ring_sum l t f IN ring_span (k,l) h s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `\x. x IN ring_span (k,l) (h:A->B) s`; `f:K->B`]
        RING_SUM_CLOSED) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[RING_SPAN_ADD; RING_SPAN_0]);;

let RING_SPAN_UNION = prove
 (`!(h:A->B) k l s t.
        ring_homomorphism(k,l) h
        ==> ring_span (k,l) h (s UNION t) =
            { ring_add l x y | x,y |
              x IN ring_span (k,l) h s /\ y IN ring_span (k,l) h t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ring_span_INDUCT;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_ADD THEN
    ASM_MESON_TAC[RING_SPAN_MONO; SUBSET; IN_UNION]] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[UNION_SUBSET; FORALL_IN_UNION; IN_ELIM_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN REPEAT CONJ_TAC THENL
   [REPEAT(EXISTS_TAC `ring_0 l:B`) THEN
    ASM_SIMP_TAC[RING_ADD_LZERO; RING_0; RING_SPAN_0];
    X_GEN_TAC `x:B` THEN REPEAT DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:B`; `ring_0 l:B`] THEN
    ASM_SIMP_TAC[RING_SPAN_0; RING_SPAN_INC; RING_ADD_RZERO];
    X_GEN_TAC `x:B` THEN REPEAT DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`ring_0 l:B`; `x:B`] THEN
    ASM_SIMP_TAC[RING_SPAN_0; RING_SPAN_INC; RING_ADD_LZERO];
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC [`x1:B`; `y1:B`; `x2:B`; `y2:B`] THEN
    REPEAT DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`ring_add l x1 x2:B`; `ring_add l y1 y2:B`] THEN
    ASM_SIMP_TAC[RING_SPAN_ADD] THEN RING_TAC THEN
    ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET];
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:A`; `x:B`; `y:B`] THEN
    REPEAT DISCH_TAC THEN MAP_EVERY EXISTS_TAC
     [`ring_mul l ((h:A->B) c) x`; `ring_mul l ((h:A->B) c) y`] THEN
    ASM_SIMP_TAC[RING_SPAN_MUL] THEN RING_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
      RING_SPAN_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[]]);;

let RING_SPAN_SING = prove
 (`!(h:A->B) k l x.
        ring_homomorphism(k,l) h /\ x IN ring_carrier l
        ==> ring_span (k,l) h {x} =
            { ring_mul l (h c) x | c | c IN ring_carrier k}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[RING_SPAN_MUL; RING_SPAN_INC; IN_SING] THEN
  MATCH_MP_TAC ring_span_INDUCT THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `ring_0 k:A` THEN ASM_SIMP_TAC[RING_MUL_LZERO; RING_0];
    REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2] THEN DISCH_TAC THEN
    EXISTS_TAC `ring_1 k:A` THEN ASM_SIMP_TAC[RING_MUL_LID; RING_1];
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:A`; `d:A`] THEN REPEAT DISCH_TAC THEN
    EXISTS_TAC `ring_add k c d:A`;
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:A`; `d:A`] THEN REPEAT DISCH_TAC THEN
    EXISTS_TAC `ring_mul k c d:A`] THEN
  ASM_SIMP_TAC[RING_ADD; RING_MUL] THEN RING_TAC THEN ASM_SIMP_TAC[]);;

let RING_SPAN_EXCHANGE = prove
 (`!(h:A->B) k l s a b.
        field k /\ ring_homomorphism(k,l) h /\
        a IN ring_span (k,l) h (b INSERT s) /\ ~(a IN ring_span (k,l) h s)
        ==> b IN ring_span (k,l) h (a INSERT s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(b:B) IN ring_carrier l` THENL
   [ALL_TAC;
    ASM_METIS_TAC[RING_SPAN_RESTRICT; SET_RULE
     `~(b IN l) ==> l INTER (b INSERT s) = l INTER s`]] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_CASES_TAC `(a:B) IN ring_carrier l` THENL
   [ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`];
    ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET; INSERT_SUBSET]] THEN
  ASM_SIMP_TAC[RING_SPAN_UNION; SING_SUBSET; RING_SPAN_SING] THEN
  REWRITE_TAC[SET_RULE
   `{f x y | x IN {g z | P z} /\ Q y} = {f (g z) y |y,z| P z /\ Q y}`] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x':B`; `c:A`] THEN
  ASM_CASES_TAC `x':B IN ring_carrier l` THENL
   [ALL_TAC; ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
        GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  ASM_CASES_TAC `c:A = ring_0 k` THENL
   [ASM_MESON_TAC[RING_ADD_LZERO; RING_MUL_LZERO]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`ring_neg l (ring_mul l ((h:A->B)(ring_inv k c)) x')`;
    `ring_inv k c:A`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [RING_SPAN_NEG; RING_SPAN_MUL; RING_INV] THEN
  ASM_SIMP_TAC[RING_ADD_LDISTRIB; RING_ADD; RING_MUL; RING_INV] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
    `ring_mul r c' c = ring_1 r
     ==> b = ring_add r (ring_add r (ring_mul r c' (ring_mul r c b)) x)
                        (ring_neg r x)`)) THEN
  ASM_MESON_TAC[FIELD_MUL_LINV; RING_INV; RING_MUL]);;

let RING_SPAN_FINITE = prove
 (`!(h:A->B) k l s.
      ring_homomorphism(k,l) h /\ FINITE s /\ s SUBSET ring_carrier l
      ==> ring_span (k,l) h s =
          { ring_sum l s (\x. ring_mul l (h(c x)) x) |c|
            !x. x IN s ==> c x IN ring_carrier k }`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[CONJUNCT1 RING_SUM_CLAUSES; RING_SPAN_EMPTY; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[INSERT_SUBSET]] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `s:B->bool`] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
  ASM_SIMP_TAC[RING_SPAN_UNION; SING_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RING_SPAN_SING; SET_RULE
   `{f x y | x IN {g w | P w} /\ y IN {h z | Q z}} =
    {f (g w) (h z) | P w /\ Q z}`] THEN
  REWRITE_TAC[SET_RULE `{x} UNION s = x INSERT s`] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; FORALL_IN_INSERT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
      GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`d:A`; `c:B->A`] THEN STRIP_TAC THEN
    EXISTS_TAC `\y. if y = x then d else (c:B->A) y` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_SUM_CLAUSES; RING_MUL] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN ASM_MESON_TAC[];
    X_GEN_TAC `c:B->A` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(c:B->A) x`; `c:B->A`] THEN
    ASM_SIMP_TAC[RING_SUM_CLAUSES; RING_MUL]]);;

let RING_SPAN_HOMOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m s.
        ring_homomorphism(k,l) f /\
        ring_homomorphism(l,m) g /\
        s SUBSET ring_carrier l
        ==> IMAGE g (ring_span (k,l) f s) =
            ring_span (k,m) (g o f) (IMAGE g s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!t. (!x. x IN s ==> x IN t /\ f(x) IN u)
          ==> IMAGE f s SUBSET u`) THEN
    EXISTS_TAC `ring_carrier l:B->bool` THEN
    MATCH_MP_TAC ring_span_INDUCT THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[RING_0; RING_ADD; RING_MUL; RING_SPAN_0;
                 RING_SPAN_ADD; RING_SPAN_INC; FUN_IN_IMAGE] THEN
    ASM_MESON_TAC[RING_SPAN_MUL; o_THM];
    MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
        RING_SPAN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN
    MATCH_MP_TAC ring_span_INDUCT THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[o_THM] THEN
    ASM_MESON_TAC[FUN_IN_IMAGE; RING_SPAN_0; RING_SPAN_ADD; RING_SPAN_MUL;
                  RING_SPAN_INC]]);;

(* ------------------------------------------------------------------------- *)
(* Set up the matroid derived from ring_span.                                *)
(* ------------------------------------------------------------------------- *)

let ring_matroid = new_definition
 `ring_matroid (k,l) (h:A->B) = matroid(ring_carrier l,ring_span (k,l) h)`;;

let RING_MATROID = prove
 (`!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h
        ==> matroid_set(ring_matroid (k,l) h) = ring_carrier l /\
            matroid_span(ring_matroid (k,l) h) = ring_span (k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[matroid_set; matroid_span] THEN
  REWRITE_TAC[GSYM PAIR_EQ; ring_matroid] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 matroid_tybij)] THEN
  ASM_SIMP_TAC[RING_SPAN_SUBSET; RING_SPAN_SUPERSET; RING_SPAN_MONO;
               RING_SPAN_SPAN; RING_SPAN_FINITARY; RING_SPAN_EXCHANGE]);;

(* ------------------------------------------------------------------------- *)
(* Some linear algebra basics with respect to that notion of span.           *)
(* ------------------------------------------------------------------------- *)

let ring_dependent = define
 `ring_dependent (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\
        ?a. a IN s /\ a IN ring_span (k,l) h (s DELETE a)`;;

let ring_independent = define
 `ring_independent (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\ ~(ring_dependent (k,l) h s)`;;

let ring_spanning = define
 `ring_spanning (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\ ring_span (k,l) h s = ring_carrier l`;;

let ring_basis = define
 `ring_basis (k,l) (h:A->B) s <=>
        ring_independent (k,l) h s /\ ring_spanning (k,l) h s`;;

let RING_DEPENDENT_IMP_SUBSET = prove
 (`!(h:A->B) k l s. ring_dependent (k,l) h s ==> s SUBSET ring_carrier l`,
  SIMP_TAC[ring_dependent]);;

let RING_INDEPENDENT_IMP_SUBSET = prove
 (`!(h:A->B) k l s. ring_independent (k,l) h s ==> s SUBSET ring_carrier l`,
  SIMP_TAC[ring_independent]);;

let RING_SPANNING_IMP_SUBSET = prove
 (`!(h:A->B) k l s. ring_spanning (k,l) h s ==> s SUBSET ring_carrier l`,
  SIMP_TAC[ring_spanning]);;

let RING_BASIS_IMP_SUBSET = prove
 (`!(h:A->B) k l s. ring_basis (k,l) h s ==> s SUBSET ring_carrier l`,
  SIMP_TAC[ring_independent; ring_basis]);;

let RING_MATROID_INDEPENDENT = prove
 (`!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h
        ==> (matroid_independent(ring_matroid (k,l) h) =
             ring_independent (k,l) h)`,
  SIMP_TAC[FUN_EQ_THM; matroid_independent; RING_MATROID] THEN
  REWRITE_TAC[ring_independent; ring_dependent] THEN MESON_TAC[]);;

let RING_MATROID_SPANNING = prove
 (`!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h
        ==> (matroid_spanning(ring_matroid (k,l) h) =
             ring_spanning (k,l) h)`,
  SIMP_TAC[FUN_EQ_THM; matroid_spanning; ring_spanning; RING_MATROID]);;

let RING_MATROID_BASIS = prove
 (`!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h
        ==> (matroid_basis(ring_matroid (k,l) h) =
             ring_basis (k,l) h)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  ASM_SIMP_TAC[matroid_basis; ring_basis; RING_MATROID_INDEPENDENT;
               ring_spanning; RING_MATROID_SPANNING] THEN
  MESON_TAC[RING_INDEPENDENT_IMP_SUBSET]);;

let RING_BASIS_EXISTS = prove
 (`!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h ==> ?b. ring_basis (k,l) h b`,
  SIMP_TAC[GSYM RING_MATROID_BASIS; MATROID_BASIS_EXISTS]);;

let RING_SPANNING_CONTAINS_BASIS = prove
 (`!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h /\ ring_spanning (k,l) h b
        ==> ?c. c SUBSET b /\ ring_basis (k,l) h c`,
  MESON_TAC[MATROID_SPANNING_CONTAINS_BASIS; RING_MATROID_SPANNING;
            RING_MATROID_BASIS]);;

let RING_BASES_CARD_EQ = prove
 (`!(h:A->B) k l b b'.
        field k /\ ring_homomorphism(k,l) h /\
        ring_basis (k,l) h b /\ ring_basis (k,l) h b'
        ==> b =_c b'`,
  MESON_TAC[RING_MATROID_BASIS; MATROID_BASES_CARD_EQ]);;

let RING_SPANNING_ALT = prove
 (`!(h:A->B) k l.
        ring_spanning (k,l) h s <=>
        s SUBSET ring_carrier l /\ ring_carrier l SUBSET ring_span (k,l) h s`,
  REWRITE_TAC[ring_spanning; GSYM SUBSET_ANTISYM_EQ; RING_SPAN_SUBSET]);;

let RING_SPANNING_IMP_NONEMPTY = prove
 (`!(h:A->B) k l b.
        field_extension(k,l) h /\ ring_spanning (k,l) h b ==> ~(b = {})`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:B->bool = {}` THEN
  ASM_REWRITE_TAC[field_extension; ring_spanning] THEN
  MESON_TAC[RING_SPAN_EMPTY; ring_monomorphism; trivial_ring;
            FIELD_IMP_NONTRIVIAL_RING]);;

let RING_INDEPENDENT_EMPTY = prove
 (`!(h:A->B) k l. ring_independent (k,l) h {}`,
  REWRITE_TAC[ring_dependent; ring_independent; EMPTY_SUBSET; NOT_IN_EMPTY]);;

let RING_INDEPENDENT_NONZERO = prove
 (`!(h:A->B) k l s. ring_independent (k,l) h s ==> ~(ring_0 l IN s)`,
  REWRITE_TAC[ring_independent; CONTRAPOS_THM; ring_dependent] THEN
  MESON_TAC[RING_SPAN_0]);;

let RING_DEPENDENT_MONO = prove
 (`!(h:A->B) k l s t.
    ring_dependent (k,l) h s /\ s SUBSET t /\ t SUBSET ring_carrier l
    ==> ring_dependent (k,l) h t`,
  REWRITE_TAC[ring_dependent] THEN
  ASM_MESON_TAC[RING_SPAN_MONO; SUBSET; IN_DELETE]);;

let RING_INDEPENDENT_MONO = prove
 (`!(h:A->B) k l s t.
        ring_independent (k,l) h t /\ s SUBSET t
        ==> ring_independent (k,l) h s`,
  REWRITE_TAC[ring_independent; ring_dependent] THEN
  ASM_MESON_TAC[RING_SPAN_MONO; SUBSET; IN_DELETE]);;

let RING_DEPENDENT_FINITARY = prove
 (`!(h:A->B) k l s.
        ring_dependent (k,l) h s <=>
        s SUBSET ring_carrier l /\
        ?t. FINITE t /\ t SUBSET s /\ ring_dependent (k,l) h t`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC [ring_dependent];
    MESON_TAC[RING_DEPENDENT_MONO; RING_DEPENDENT_IMP_SUBSET]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_SPAN_FINITARY) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a:B) INSERT t` THEN
  ASM_REWRITE_TAC[FINITE_INSERT; EXISTS_IN_INSERT] THEN
  SUBGOAL_THEN `(a INSERT t) DELETE (a:B) = t` SUBST1_TAC THEN
  ASM SET_TAC[]);;

let RING_INDEPENDENT_FINITARY = prove
 (`!(h:A->B) k l s.
        ring_independent (k,l) h s <=>
        s SUBSET ring_carrier l /\
        !t. FINITE t /\ t SUBSET s ==> ring_independent (k,l) h t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_independent] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RING_DEPENDENT_FINITARY] THEN
  SET_TAC[]);;

let RING_INDEPENDENT_LE_SPAN = prove
 (`!(h:A->B) k l s t.
        field k /\ ring_homomorphism(k,l) h /\ t SUBSET ring_carrier l /\
        FINITE t /\
        ring_independent (k,l) h s /\ s SUBSET ring_span (k,l) h t
        ==> FINITE s /\ CARD s <= CARD t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE THEN
  EXISTS_TAC `ring_matroid (k,l) (h:A->B)` THEN
  ASM_SIMP_TAC[RING_MATROID; RING_MATROID_INDEPENDENT]);;

let RING_DEPENDENT_FINITE = prove
 (`!(h:A->B) k l s.
        field k /\ ring_homomorphism(k,l) h /\ FINITE s
        ==> (ring_dependent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             ?c. ring_sum l s (\x. ring_mul l (h(c x)) x) = ring_0 l /\
                 (!x. x IN s ==> c x IN ring_carrier k) /\
                 ?x. x IN s /\ ~(c x = ring_0 k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_dependent] THEN
  ASM_CASES_TAC `(s:B->bool) SUBSET ring_carrier l` THEN
  ASM_SIMP_TAC[RING_SPAN_FINITE; FINITE_DELETE;
               SET_RULE `s SUBSET t ==> s DELETE a SUBSET t`] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
      GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  X_GEN_TAC `a:B` THEN ASM_CASES_TAC `(a:B) IN s` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c:B->A` THENL
   [DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    EXISTS_TAC `\x. if x = a then ring_neg k (ring_1 k) else (c:B->A) x` THEN
    ASM_SIMP_TAC[RING_SUM_CASES; COND_RAND; COND_RATOR] THEN
    ASM_SIMP_TAC[GSYM DELETE; RING_SUM_SING; RING_NEG; RING_1; RING_MUL;
      SET_RULE `a IN s ==> {x | x IN s /\ x = a} = {a}`] THEN
    ASM_SIMP_TAC[IN_SUBRING_1; IN_SUBRING_NEG; IN_DELETE; COND_ID] THEN
    ASM_SIMP_TAC[RING_NEG_EQ_0; RING_1; FIELD_NONTRIVIAL] THEN
    RING_TAC THEN ASM_SIMP_TAC[RING_SUM; RING_0; RING_1];
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `y = (h:A->B) (ring_neg k (ring_inv k ((c:B->A) a)))` THEN
    SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_NEG; RING_INV]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `ring_mul l (y:B)`) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) (GSYM RING_SUM_LMUL) o
      lhand o lhand o snd) THEN
    ASM_SIMP_TAC[RING_MUL; RING_MUL_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `s:B->bool = a INSERT (s DELETE a)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [th]) THEN
    ASM_SIMP_TAC[RING_SUM_CLAUSES; FINITE_DELETE; RING_MUL; IN_DELETE] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[RING_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_mul l y (ring_mul l (h((c:B->A) a)) a) = ring_neg l a`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
       `ring_mul l y y' = ring_neg l (ring_1 l)
        ==> ring_mul l y (ring_mul l y' a) = ring_neg l a`)) THEN
      ASM_SIMP_TAC[] THEN EXPAND_TAC "y" THEN
      MP_TAC(ISPECL [`k:A ring`; `(c:B->A) a`] FIELD_MUL_LINV) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `(h:A->B) o ring_neg k`) THEN
      ASM_SIMP_TAC[o_THM; RING_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[GSYM RING_MUL_LNEG; RING_INV] THEN EXPAND_TAC "y" THEN
      ASM_MESON_TAC[RING_INV; RING_NEG];
      ASM_SIMP_TAC[RING_SUM; RING_RULE
       `ring_add r (ring_neg r x) b = ring_mul r y (ring_0 r) <=>
        b = x`] THEN
      DISCH_TAC] THEN
    EXISTS_TAC
     `\x. ring_mul k (ring_neg k (ring_inv k (c a))) ((c:B->A) x)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[RING_MUL; RING_NEG; RING_INV]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN
    ASM_SIMP_TAC[RING_MUL; RING_NEG; RING_INV; IN_DELETE; RING_MUL_ASSOC] THEN
    ASM_MESON_TAC[RING_MUL; RING_NEG; RING_INV]]);;

let RING_INDEPENDENT_FINITE = prove
 (`!(h:A->B) k l s.
        field k /\ ring_homomorphism(k,l) h /\ FINITE s
        ==> (ring_independent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             !c. ring_sum l s (\x. ring_mul l (h(c x)) x) = ring_0 l /\
                 (!x. x IN s ==> c x IN ring_carrier k)
                 ==> (!x. x IN s ==> c x = ring_0 k))`,
  SIMP_TAC[ring_independent; RING_DEPENDENT_FINITE] THEN MESON_TAC[]);;

let RING_INDEPENDENT_FINITE_EQ = prove
 (`!(h:A->B) k l s.
        field k /\ ring_homomorphism(k,l) h /\ FINITE s
        ==> (ring_independent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             !c d. ring_sum l s (\x. ring_mul l (h(c x)) x) =
                   ring_sum l s (\x. ring_mul l (h(d x)) x) /\
                  (!x. x IN s
                       ==> c x IN ring_carrier k /\ d x IN ring_carrier k)
                 ==> (!x. x IN s ==> c x = d x))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RING_INDEPENDENT_FINITE] THEN
  ASM_CASES_TAC `(s:B->bool) SUBSET ring_carrier l` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`c:B->A`; `d:B->A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\x. ring_sub k ((d:B->A) x) (c x)`) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[RING_SUB_EQ_0; SUBSET]] THEN
    ASM_SIMP_TAC[RING_SUB] THEN FIRST_ASSUM(MP_TAC o MATCH_MP
     (MESON[RING_SUB_EQ_0; RING_SUM]
     `ring_sum r s x = ring_sum r s y
      ==> ring_sub r (ring_sum r s y) (ring_sum r s x) = ring_0 r`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o rand o snd) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[ring_homomorphism; RING_MUL; SUBSET; IN_IMAGE];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_SUB) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[RING_SUB_RDISTRIB];
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `c:B->A` THEN
    DISCH_THEN(MP_TAC o SPEC `(\x. ring_0 k):B->A`) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[RING_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[RING_MUL; RING_MUL_LZERO]]);;

let RING_DEPENDENT_SPAN_IMAGE = prove
 (`!(h:A->B) k l (f:K->B) s t.
        field k /\ ring_homomorphism(k,l) h /\ t SUBSET ring_carrier l /\
        FINITE s /\ FINITE t /\ IMAGE f s SUBSET ring_span (k,l) h t /\
        CARD t < CARD s
        ==> ?c. ring_sum l s (\x. ring_mul l (h(c x)) (f x)) = ring_0 l /\
                (!x. x IN s ==> c x IN ring_carrier k) /\
                ?x. x IN s /\ ~(c x = ring_0 k)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!i j. i IN s /\ j IN s ==> ((f:K->B) i = f j <=> i = j)` THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `IMAGE (f:K->B) s`; `t:B->bool`]
        RING_INDEPENDENT_LE_SPAN) THEN
    ASM_SIMP_TAC[ring_independent; CARD_IMAGE_INJ; FINITE_IMAGE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN SIMP_TAC[NOT_LE] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CARD_IMAGE_INJ]; ALL_TAC] THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> (p /\ ~q)`] THEN ANTS_TAC THENL
     [ASM SET_TAC[RING_SPAN_SUBSET];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_DEPENDENT_FINITE o
        lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `c:B->A` THEN ASM_SIMP_TAC[RING_SUM_IMAGE; IMP_CONJ; o_DEF] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `(c:B->A) o (f:K->B)` THEN
    ASM_SIMP_TAC[o_DEF] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE RAND_CONV [GSYM INJECTIVE_ON_ALT]) THEN
    REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP] THEN
    MAP_EVERY X_GEN_TAC [`m:K`; `n:K`] THEN STRIP_TAC THEN
    EXISTS_TAC
     `(\i. if i = m then ring_1 k
           else if i = n then ring_neg k (ring_1 k)
           else ring_0 k):K->A` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPLICATE_TAC 2
       (ONCE_REWRITE_TAC[COND_RAND] THEN
        ONCE_REWRITE_TAC[COND_RAND] THEN
        ONCE_REWRITE_TAC[COND_RATOR] THEN
        ASM_SIMP_TAC[RING_SUM_CASES; FINITE_RESTRICT]);
      MESON_TAC[RING_0; RING_1; RING_NEG];
      EXISTS_TAC `m:K` THEN ASM_MESON_TAC[FIELD_NONTRIVIAL]] THEN
    SUBGOAL_THEN `!x. x IN s ==> (f:K->B) x IN ring_carrier l` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      ASM_MESON_TAC[RING_SPAN_SUBSET; SUBFIELD_OF_IMP_SUBSET; SUBSET];
      ALL_TAC] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; RING_SUM_SING; RING_MUL; RING_1; RING_NEG;
                 SET_RULE `a IN s ==> {x | x IN s /\ x = a} = {a}`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[RING_SUM; RING_1; RING_MUL; RING_NEG;
                 RING_MUL_LNEG; RING_MUL_LID; RING_ADD_ASSOC; RING_SUM;
                 RING_ADD_RNEG; RING_ADD_LZERO] THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN
    ASM_SIMP_TAC[IN_ELIM_THM; RING_MUL_LZERO]]);;

let RING_SPAN_SUBSET_SUBRING_GENERATED = prove
 (`!(h:A->B) k l s.
        ring_span (k,l) h s SUBSET
        ring_carrier(subring_generated l (IMAGE h (ring_carrier k) UNION s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN
  MATCH_MP_TAC ring_span_INDUCT THEN
  SIMP_TAC[RING_0_IN_SUBRING_GENERATED; RING_ADD_IN_SUBRING_GENERATED] THEN
  REPEAT STRIP_TAC THENL
    [ALL_TAC; MATCH_MP_TAC RING_MUL_IN_SUBRING_GENERATED THEN CONJ_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[]);;

let RING_SPAN_SUBSET_SUBFIELD_GENERATED = prove
 (`!(h:A->B) k l s.
        ring_span (k,l) h s SUBSET
        ring_carrier(subfield_generated l (IMAGE h (ring_carrier k) UNION s))`,
  MESON_TAC[RING_SPAN_SUBSET_SUBRING_GENERATED; SUBSET_TRANS;
            SUBRING_SUBSET_SUBFIELD_GENERATED]);;

let RING_INDEPENDENT_INSERT = prove
 (`!(h:A->B) k l s a.
         field k /\
         ring_homomorphism (k,l) h /\
         s SUBSET ring_carrier l /\
         a IN ring_carrier l
        ==> (ring_independent (k,l) h (a INSERT s) <=>
             if a IN s then ring_independent (k,l) h s
             else ring_independent (k,l) h s /\ ~(a IN ring_span (k,l) h s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_matroid (k,l) (h:A->B)`; `s:B->bool`; `a:B`]
        MATROID_INDEPENDENT_INSERT) THEN
  ASM_SIMP_TAC[RING_MATROID; INSERT_SUBSET; RING_MATROID_INDEPENDENT]);;

let RING_INDEPENDENT_CARD_LE_SPANNING = prove
 (`!(h:A->B) k l b c.
        field k /\ ring_homomorphism (k,l) h /\
        ring_independent (k,l) h b /\ ring_spanning (k,l) h c
        ==> b <=_c c`,
  REWRITE_TAC[IMP_CONJ] THEN
  SIMP_TAC[GSYM RING_MATROID_INDEPENDENT; GSYM RING_MATROID_SPANNING] THEN
  MESON_TAC[MATROID_INDEPENDENT_CARD_LE_SPANNING]);;

(* ------------------------------------------------------------------------- *)
(* The general (finite or infinite) tower law for degree of field extensions *)
(* ------------------------------------------------------------------------- *)

let RING_SPANNING_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m b c.
      field_extension (k,l) f /\ ring_spanning (k,l) f b /\
      field_extension (l,m) g /\ ring_spanning (l,m) g c
      ==> ring_spanning (k,m) (g o f) {ring_mul m (g x) y | x IN b /\ y IN c}`,
  REWRITE_TAC[RING_SPANNING_ALT] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    ASM_MESON_TAC[FIELD_EXTENSION_CARRIER; RING_MUL; SUBSET];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS))] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:C` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_SPAN_FINITARY) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  X_GEN_TAC `c':C->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c':C->bool) SUBSET ring_carrier m` ASSUME_TAC
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_SPAN_FINITE; FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
  SPEC_TAC(`w:C`,`w:C`) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `d:C->B` THEN DISCH_TAC THEN MATCH_MP_TAC RING_SPAN_SUM THEN
  X_GEN_TAC `z:C` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(d:C->B) z IN ring_span (k,l) (f:A->B) b` MP_TAC THENL
   [ASM SET_TAC[]; DISCH_THEN(MP_TAC o MATCH_MP RING_SPAN_FINITARY)] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  X_GEN_TAC `b':B->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(b':B->bool) SUBSET ring_carrier l` ASSUME_TAC
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_SPAN_FINITE; FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
  SPEC_TAC(`(d:C->B) z`,`y:B`) THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `e:B->A` THEN DISCH_TAC THEN
  MP_TAC(GEN `i:B->B`
   (ISPECL [`l:B ring`; `m:C ring`; `g:B->C`; `i:B->B`; `b':B->bool`]
      (REWRITE_RULE[RIGHT_IMP_FORALL_THM] RING_HOMOMORPHISM_SUM))) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN DISCH_THEN(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o lhand o snd)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_CARRIER; SUBSET; RING_MUL];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o lhand o snd) THEN
  REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_CARRIER; SUBSET; RING_MUL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SPAN_SUM THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `g:B->C`] RING_HOMOMORPHISM_MUL) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN DISCH_THEN(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o lhand o snd)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_CARRIER; SUBSET; RING_MUL];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_MUL_ASSOC o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_CARRIER; SUBSET; RING_MUL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`]
        RING_SPAN_MUL) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC[RING_MUL] THEN ASM SET_TAC[]);;

let RING_INDEPENDENT_PRODUCTS,RING_INDEPENDENT_TRANS = (CONJ_PAIR o prove)
 (`(!(f:A->B) (g:B->C) k l m b c.
      field_extension (k,l) f /\ ring_independent (k,l) f b /\
      field_extension (l,m) g /\ ring_independent (l,m) g c
      ==> !x y x' y'. x IN b /\ y IN c /\ x' IN b /\ y' IN c
                      ==> (ring_mul m (g x) y = ring_mul m (g x') y' <=>
                           x = x' /\ y = y')) /\
   (!(f:A->B) (g:B->C) k l m b c.
      field_extension (k,l) f /\ ring_independent (k,l) f b /\
      field_extension (l,m) g /\ ring_independent (l,m) g c
      ==> ring_independent (k,m) (g o f)
           {ring_mul m (g x) y | x IN b /\ y IN c})`,
  let lemma = prove
   (`{ring_mul m ((g:B->C) x) y | x IN b' /\ y IN c'} =
     IMAGE (\(y,x). ring_mul m (g x) y) (c' CROSS b')`,
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; FORALL_IN_IMAGE; FORALL_IN_CROSS;
                FORALL_IN_GSPEC; SUBSET] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM; IN_CROSS] THEN
    SET_TAC[]) in
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ (q ==> r)`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!w:B. w IN b ==> w IN ring_carrier l) /\
    (!z:C. z IN c ==> z IN ring_carrier m) /\
    (!u. u IN ring_carrier k ==> (f:A->B) u IN ring_carrier l) /\
    (!v. v IN ring_carrier l ==> (g:B->C) v IN ring_carrier m)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE
     [ring_independent; field_extension;
      ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
    ASM_CASES_TAC `x:B = x'` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
        INTEGRAL_DOMAIN_MUL_LCANCEL)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[field_extension; RING_MONOMORPHISM_ALT]) THEN
      ASM_MESON_TAC[RING_INDEPENDENT_NONZERO; FIELD_IMP_INTEGRAL_DOMAIN];
      ALL_TAC] THEN
    ASM_CASES_TAC `y:C = y'` THEN ASM_REWRITE_TAC[] THENL
     [W(MP_TAC o PART_MATCH (funpow 5 rand o lhand)
        INTEGRAL_DOMAIN_MUL_RCANCEL o rand o snd) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[field_extension; ring_monomorphism]) THEN
      ASM_MESON_TAC[RING_INDEPENDENT_NONZERO; FIELD_IMP_INTEGRAL_DOMAIN];
      DISCH_TAC] THEN
    UNDISCH_TAC `ring_independent (l,m) (g:B->C) c` THEN
    REWRITE_TAC[ring_independent; ring_dependent] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y:C` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
     `!s. s SUBSET t /\ x IN s ==> x IN t`) THEN
    EXISTS_TAC `ring_span (l,m) (g:B->C) {y'}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_SPAN_MONO THEN ASM SET_TAC[];
      ASM_SIMP_TAC[RING_SPAN_SING; FIELD_EXTENSION_IMP_HOMOMORPHISM]] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `ring_div l x' x:B` THEN
    ASM_SIMP_TAC[RING_DIV] THEN
    MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `g:B->C`]
        FIELD_HOMOMORPHISM_DIV) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[field_extension; ring_monomorphism];
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC)] THEN
    UNDISCH_TAC `ring_mul m ((g:B->C) x) y = ring_mul m (g x') y'` THEN
    SUBGOAL_THEN
     `field m /\
      y IN ring_carrier m /\ y' IN ring_carrier m /\
      (g:B->C) x IN ring_carrier m /\ (g:B->C) x' IN ring_carrier m /\
      ~(g x = ring_0 m)`
    MP_TAC THENL
     [ASM_MESON_TAC[field_extension; RING_MONOMORPHISM_ALT;
                    RING_INDEPENDENT_NONZERO];
      POP_ASSUM_LIST(K ALL_TAC) THEN FIELD_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!b' c'. FINITE b' /\ FINITE c' /\ b' SUBSET b /\ c' SUBSET c
            ==> ring_independent (k,m) ((g:B->C) o (f:A->B))
                  {ring_mul m (g x) y | x IN b' /\ y IN c'}`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_INDEPENDENT_FINITE o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT] THEN
      ASM_MESON_TAC[field_extension; ring_monomorphism;
                    RING_HOMOMORPHISM_COMPOSE];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN ASM_MESON_TAC[RING_MUL];
      DISCH_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `c:C->A` THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[lemma] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_IMAGE o
       lhand o lhand o snd) THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_DEF] THEN ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN
    REWRITE_TAC[] THEN REWRITE_TAC[CROSS] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUM_PRODUCT o
        lhand o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN `ring_independent(l,m) (g:B->C) c'` MP_TAC THENL
     [ASM_MESON_TAC[RING_INDEPENDENT_MONO; SUBSET]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      RING_INDEPENDENT_FINITE o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[field_extension; ring_monomorphism];
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    DISCH_THEN(MP_TAC o SPEC
     `\y:C. ring_sum l b'
              (\x. ring_mul l ((f:A->B)(c(ring_mul m (g x:C) y))) x)`) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `P /\ x' = x /\ (Q ==> R) ==> (x = z /\ P ==> Q) ==> (x' = z ==> R)`) THEN
    REWRITE_TAC[RING_SUM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `y:C` THEN
      DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `g:B->C`;
                `\x. ring_mul l ((f:A->B) (c (ring_mul m ((g:B->C) x) y))) x`;
               `b':B->bool`]
        (REWRITE_RULE[RIGHT_IMP_FORALL_THM] RING_HOMOMORPHISM_SUM)) THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
      ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
      W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RMUL o rand o snd) THEN
      ASM_SIMP_TAC[o_THM] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[RING_MUL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) RING_MUL_ASSOC o lhand o snd) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM; RING_HOMOMORPHISM_MUL];
      GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
      MATCH_MP_TAC MONO_FORALL] THEN
    X_GEN_TAC `y:C` THEN ASM_CASES_TAC `(y:C) IN c'` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ring_independent(k,l) (f:A->B) b'` MP_TAC THENL
     [ASM_MESON_TAC[RING_INDEPENDENT_MONO; SUBSET]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      RING_INDEPENDENT_FINITE o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[field_extension; ring_monomorphism];
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    DISCH_THEN(MP_TAC o SPEC `\x. c(ring_mul m ((g:B->C) x) y):A`) THEN
    ASM_SIMP_TAC[RING_MUL];
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[RING_INDEPENDENT_FINITARY] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUBSET; FORALL_IN_GSPEC; RING_MUL]; ALL_TAC] THEN
    REWRITE_TAC[lemma; FORALL_FINITE_SUBSET_IMAGE] THEN
    X_GEN_TAC `t:C#B->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`IMAGE SND (t:C#B->bool)`; `IMAGE FST (t:C#B->bool)`]) THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      SIMP_TAC[FORALL_PAIR_THM; SUBSET; FORALL_IN_IMAGE; IN_CROSS] THEN
      MESON_TAC[];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] RING_INDEPENDENT_MONO)] THEN
    REWRITE_TAC[lemma] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS;
                IN_IMAGE; EXISTS_PAIR_THM] THEN
    MESON_TAC[]]);;

let RING_BASIS_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m b c.
      field_extension (k,l) f /\ ring_basis (k,l) f b /\
      field_extension (l,m) g /\ ring_basis (l,m) g c
      ==> ring_basis (k,m) (g o f) {ring_mul m (g x) y | x IN b /\ y IN c}`,
  REWRITE_TAC[ring_basis] THEN
  MESON_TAC[RING_INDEPENDENT_TRANS; RING_SPANNING_TRANS]);;

let FIELD_EXTENSION_TOWER_LAW = prove
 (`!(f:A->B) (g:B->C) k l m b c d.
     field_extension (k,l) f /\ field_extension (l,m) g /\
     ring_basis (k,l) f b /\ ring_basis (l,m) g c /\ ring_basis (k,m) (g o f) d
     ==> b *_c c =_c d`,
  REPEAT STRIP_TAC THEN TRANS_TAC CARD_EQ_TRANS
   `{ring_mul m ((g:B->C) x) y | x IN b /\ y IN c}` THEN
  CONJ_TAC THENL
   [TRANS_TAC CARD_EQ_TRANS
     `IMAGE (\(x:B,y:C). ring_mul m (g x) y) (b CROSS c)` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN REWRITE_TAC[CROSS; mul_c] THEN
      MATCH_MP_TAC CARD_EQ_IMAGE THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; PAIR_EQ] THEN
      ASM_MESON_TAC[RING_INDEPENDENT_PRODUCTS; ring_basis];
      MATCH_MP_TAC CARD_EQ_REFL_IMP THEN
      REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; FORALL_IN_IMAGE; FORALL_IN_CROSS;
                FORALL_IN_GSPEC; SUBSET] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM; IN_CROSS] THEN
      SET_TAC[]];
    MATCH_MP_TAC RING_BASES_CARD_EQ THEN
    MAP_EVERY EXISTS_TAC [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [ASM_MESON_TAC[field_extension; ring_monomorphism;
                    RING_HOMOMORPHISM_COMPOSE];
       ALL_TAC]) THEN
    MATCH_MP_TAC RING_BASIS_TRANS THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Finite field extensions, those finite-dimensional as vector spaces.       *)
(* ------------------------------------------------------------------------- *)

let finite_extension = new_definition
 `finite_extension (k,l) (h:A->B) <=>
        field_extension (k,l) h /\
        ?b. FINITE b /\ b SUBSET ring_carrier l /\
            ring_span (k,l) h b = ring_carrier l`;;

let RING_MATROID_FINITE_DIMENSIONAL = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> (matroid_finite_dimensional(ring_matroid (k,l) h) <=>
             finite_extension (k,l) h)`,
  SIMP_TAC[matroid_finite_dimensional; field_extension; finite_extension] THEN
  SIMP_TAC[RING_MATROID; RING_MATROID_SPANNING; ring_monomorphism] THEN
  REWRITE_TAC[ring_spanning]);;

let FINITE_IMP_FIELD_EXTENSION = prove
 (`!(h:A->B) k l. finite_extension(k,l) h ==> field_extension(k,l) h`,
  SIMP_TAC[finite_extension]);;

let FINITE_EXTENSION_RING_MATROID = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h <=>
        field_extension (k,l) h /\
        matroid_finite_dimensional (ring_matroid (k,l) h)`,
  MESON_TAC[FINITE_IMP_FIELD_EXTENSION; RING_MATROID_FINITE_DIMENSIONAL]);;

let FINITE_EXTENSION = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h <=>
        field_extension (k,l) h /\
        ?b. FINITE b /\ b SUBSET ring_carrier l /\
            ring_carrier l SUBSET ring_span (k,l) h b`,
  REWRITE_TAC[finite_extension; GSYM SUBSET_ANTISYM_EQ; field_extension] THEN
  MESON_TAC[RING_SPAN_SUBSET; RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let FINITE_EXTENSION_SPANNING = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h <=>
        field_extension (k,l) h /\ ?b. FINITE b /\ ring_spanning (k,l) h b`,
  REWRITE_TAC[finite_extension; ring_spanning]);;

let FINITE_EXTENSION_BASIS = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h <=>
        field_extension (k,l) h /\ ?b. FINITE b /\ ring_basis (k,l) h b`,
  REWRITE_TAC[FINITE_EXTENSION_SPANNING] THEN
  MESON_TAC[ring_basis; field_extension; ring_monomorphism;
            RING_SPANNING_CONTAINS_BASIS; FINITE_SUBSET]);;

let FINITE_EXTENSION_ANY = prove
 (`!(h:A->B) k l b.
        ring_basis (k,l) h b
        ==> (finite_extension (k,l) h <=>
             field_extension (k,l) h /\ FINITE b)`,
  MESON_TAC[RING_MATROID_FINITE_DIMENSIONAL; finite_extension;
            RING_MATROID_BASIS; field_extension; ring_monomorphism;
            MATROID_FINITE_DIMENSIONAL_ANY]);;

let FINITE_EXTENSION_ISOMORPHISM = prove
 (`!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism (k,l) f
        ==> finite_extension (k,l) f`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[finite_extension; FIELD_EXTENSION_ISOMORPHISM] THEN
  EXISTS_TAC `{ring_1 l:B}` THEN REWRITE_TAC[FINITE_SING; SING_SUBSET] THEN
  ASM_SIMP_TAC[RING_SPAN_SING; RING_1; RING_ISOMORPHISM_IMP_HOMOMORPHISM] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
  REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[RING_MUL_RID] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  ASM_SIMP_TAC[RING_MUL_RID] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_EPIMORPHISM) THEN
  REWRITE_TAC[ring_epimorphism] THEN ASM SET_TAC[]);;

let FINITE_EXTENSION_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m.
        finite_extension (k,l) f /\ finite_extension (l,m) g
        ==> finite_extension (k,m) (g o f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FINITE_EXTENSION_BASIS] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `b:B->bool` THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `c:C->bool` THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FIELD_EXTENSION_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`]
        RING_BASIS_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_TRANS; field_extension; ring_monomorphism];
    MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `d:C->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `b:B->bool`; `c:C->bool`; `d:C->bool`]
        FIELD_EXTENSION_TOWER_LAW) THEN
  ASM_MESON_TAC[CARD_MUL_FINITE; CARD_FINITE_CONG]);;

let FINITE_EXTENSION_TRANS_EQ = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g
        ==> (finite_extension (k,m) (g o f) <=>
             finite_extension (k,l) f /\ finite_extension (l,m) g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
        FIELD_EXTENSION_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`]
        RING_BASIS_EXISTS) THEN
  MP_TAC(ISPECL [`g:B->C`; `l:B ring`; `m:C ring`] RING_BASIS_EXISTS) THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`] RING_BASIS_EXISTS) THEN
  MAP_EVERY (fun t ->
    ANTS_TAC THENL
     [ASM_MESON_TAC[FIELD_EXTENSION_TRANS; field_extension; ring_monomorphism];
      DISCH_THEN(X_CHOOSE_TAC t)])
   [`b:B->bool`; `c:C->bool`; `d:C->bool`] THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `b:B->bool`; `c:C->bool`; `d:C->bool`]
        FIELD_EXTENSION_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`; `d:C->bool`]
        FINITE_EXTENSION_ANY) THEN
  MP_TAC(ISPECL [`g:B->C`; `l:B ring`; `m:C ring`; `c:C->bool`]
        FINITE_EXTENSION_ANY) THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `b:B->bool`]
        FINITE_EXTENSION_ANY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP CARD_FINITE_CONG) THEN
  REWRITE_TAC[CARD_MUL_FINITE_EQ] THEN
  ASM_MESON_TAC[RING_SPANNING_IMP_NONEMPTY; ring_basis]);;

(* ------------------------------------------------------------------------- *)
(* Finitely generated field extensions.                                      *)
(* ------------------------------------------------------------------------- *)

let finitely_generated_extension = new_definition
 `finitely_generated_extension (k,l) (h:A->B) <=>
     field_extension (k,l) h /\
     ?b. FINITE b /\ b SUBSET ring_carrier l /\
         subfield_generated l (IMAGE h (ring_carrier k) UNION b) = l`;;

let FINITELY_GENERATED_IMP_FIELD_EXTENSION = prove
 (`!(h:A->B) k l.
        finitely_generated_extension(k,l) h ==> field_extension(k,l) h`,
  SIMP_TAC[finitely_generated_extension]);;

let FINITE_IMP_FINITELY_GENERATED_EXTENSION = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h ==> finitely_generated_extension (k,l) h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[finite_extension; finitely_generated_extension] THEN
  REWRITE_TAC[SUBFIELD_GENERATED_EQ] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ;
              RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
  ASM_MESON_TAC[RING_SPAN_SUBSET_SUBFIELD_GENERATED; field_extension;
                RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let FINITELY_GENERATED_EXTENSION = prove
 (`!(h:A->B) k l.
     finitely_generated_extension (k,l) h <=>
     field_extension (k,l) h /\
     ?b. FINITE b /\ b SUBSET ring_carrier l /\
         ring_carrier l SUBSET
         ring_carrier(subfield_generated l (IMAGE h (ring_carrier k) UNION b))`,
  REWRITE_TAC[finitely_generated_extension; SUBFIELD_GENERATED_EQ;
              GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET]);;

let FINITELY_GENERATED_EXTENSION_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m.
        finitely_generated_extension (k,l) f /\
        finitely_generated_extension (l,m) g
        ==> finitely_generated_extension (k,m) (g o f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FINITELY_GENERATED_EXTENSION] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `b:B->bool` THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `c:C->bool` THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FIELD_EXTENSION_TRANS]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (g:B->C) b UNION c` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_UNION; UNION_SUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[SUBSET; FIELD_EXTENSION_CARRIER];
    REWRITE_TAC[IMAGE_o; GSYM UNION_ASSOC; GSYM IMAGE_UNION]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET];
    ASM_MESON_TAC[SUBFIELD_SUBFIELD_GENERATED; field_extension]] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> IMAGE f t SUBSET u ==> IMAGE f s SUBSET u`)) THEN
    MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `g:B->C`]
      SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE) THEN
    DISCH_THEN(fun th ->
      W(MP_TAC o PART_MATCH (rand o rand) th o lhand o snd)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FIELD_EXTENSION_IMP_MONOMORPHISM; UNION_SUBSET] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [field_extension; ring_monomorphism; ring_homomorphism]) THEN
      ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC[];
    REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC[IN_UNION] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_UNION] THEN
    ASM_MESON_TAC[SUBSET; FIELD_EXTENSION_CARRIER]]);;

(* ------------------------------------------------------------------------- *)
(* Algebraic elements and algebraic extensions.                              *)
(* ------------------------------------------------------------------------- *)

let algebraic_over = new_definition
 `algebraic_over (k,l) (h:A->B) x <=>
        x IN ring_carrier l /\
        ?p. p IN ring_carrier(poly_ring k (:1)) /\
            ~(p = ring_0(poly_ring k (:1))) /\
            poly_extend(k,l) h (\v. x) p = ring_0 l`;;

let transcendental_over = new_definition
 `transcendental_over (k,l) (h:A->B) x <=>
        x IN ring_carrier l /\ ~(algebraic_over (k,l) h x)`;;

let algebraic_extension = new_definition
 `algebraic_extension (k,l) (h:A->B) <=>
        field_extension (k,l) h /\
        !x. x IN ring_carrier l ==> algebraic_over (k,l) h x`;;

let ALGEBRAIC_OVER = prove
 (`!(h:A->B) k l (v:V) x.
         algebraic_over (k,l) h x <=>
         x IN ring_carrier l /\
         ?p. p IN ring_carrier (poly_ring k {v}) /\
             ~(p = ring_0 (poly_ring k {v})) /\
             poly_extend (k,l) h (\v. x) p = ring_0 l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[algebraic_over] THEN
  ASM_CASES_TAC `(x:B) IN ring_carrier l` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `{v:V}`; `(:1)`; `\x:V. one`; `\u:1. (v:V)`]
   RING_ISOMORPHISMS_POLY_REINDEX) THEN
  REWRITE_TAC[UNIV_1; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING] THEN
  W(fun (asl,w) ->
      let ft,gt = dest_pair(rand(lhand w)) in
      ABBREV_TAC(mk_eq(mk_var("f",type_of ft),ft)) THEN
      ABBREV_TAC(mk_eq(mk_var("g",type_of gt),gt))) THEN
  DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g:((1->num)->A)->(V->num)->A) p` THEN
    FIRST_X_ASSUM(ASSUME_TAC o el 1 o
        CONJUNCTS o GEN_REWRITE_RULE I [RING_ISOMORPHISMS_ISOMORPHISM]);
    DISCH_THEN(X_CHOOSE_THEN `q:(V->num)->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(f:((V->num)->A)->(1->num)->A) q` THEN
    FIRST_X_ASSUM(ASSUME_TAC o el 0 o
        CONJUNCTS o GEN_REWRITE_RULE I [RING_ISOMORPHISMS_ISOMORPHISM])] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP RING_ISOMORPHISM_IMP_MONOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        RING_MONOMORPHISM_EQ_0)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THENL
   [EXPAND_TAC "g" THEN MP_TAC(ISPECL
     [`h:A->B`; `k:A ring`; `l:B ring`; `{v:V}`; `{one}`; `p:(1->num)->A`;
      `\x:V. one`; `(\v. x):1->B`] POLY_EXTEND_REINDEX);
    EXPAND_TAC "f" THEN MP_TAC(ISPECL
     [`h:A->B`; `k:A ring`; `l:B ring`; `{one}`; `{v:V}`; `q:(V->num)->A`;
      `\x:1. (v:V)`; `(\v. x):V->B`] POLY_EXTEND_REINDEX)] THEN
  ASM_REWRITE_TAC[o_DEF; SET_RULE `BIJ (\x. b) {a} {b}`] THEN
  ASM_MESON_TAC[IN_POLY_RING_CARRIER]);;

let ALGEBRAIC_IMP_FIELD_EXTENSION = prove
 (`!(h:A->B) k l. algebraic_extension(k,l) h ==> field_extension(k,l) h`,
  SIMP_TAC[algebraic_extension]);;

let ALGEBRAIC_OVER_ALT = prove
 (`!(h:A->B) k l x.
        ring_monomorphism(k,l) h
        ==> (algebraic_over (k,l) (h:A->B) x <=>
             x IN ring_carrier l /\
             ?p. p IN ring_carrier(poly_ring k (:1)) /\
                 ~(poly_deg k p = 0) /\
                 poly_extend(k,l) h (\v. x) p = ring_0 l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[algebraic_over] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[POLY_DEG_0; POLY_RING]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `p:(1->num)->A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_POLY_RING_CARRIER]) THEN
  ASM_SIMP_TAC[POLY_DEG_EQ_0] THEN
  MATCH_MP_TAC(TAUT `(r ==> ~q) ==> p ==> q ==> ~r`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[POLY_EXTEND_CONST; RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  REWRITE_TAC[POLY_RING; poly_0; POLY_CONST_EQ] THEN
  ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]);;

let ALGEBRAIC_OVER_IN_CARRIER = prove
 (`!(h:A->B) k l a.
        algebraic_over (k,l) h a ==> a IN ring_carrier l`,
  SIMP_TAC[algebraic_over]);;

let TRANSCENDENTAL_OVER_IN_CARRIER = prove
 (`!(h:A->B) k l a.
        transcendental_over (k,l) h a ==> a IN ring_carrier l`,
  SIMP_TAC[transcendental_over]);;

let ALGEBRAIC_OVER_IMAGE_GEN = prove
 (`!(h:A->B) k l x.
        ~(trivial_ring k /\ x = ring_0 k /\ h x = ring_0 l) /\
        ring_homomorphism(k,l) h /\ x IN ring_carrier k
        ==> algebraic_over(k,l) h (h x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[algebraic_over] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ring_homomorphism]) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
  EXISTS_TAC `poly_sub k (poly_var k one) (poly_const k (x:A))` THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
   [POLY_CLAUSES] THEN
  ASM_SIMP_TAC[POLY_EXTEND_SUB; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST;
               POLY_EXTEND_VAR; POLY_EXTEND_CONST; IN_UNIV; RING_SUB_REFL;
               GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_VAR; RING_SUB_EQ_0;
               RING_POLYNOMIAL_CONST; RING_POLYNOMIAL_SUB] THEN
  ASM_REWRITE_TAC[POLY_VAR_EQ_CONST] THEN ASM_MESON_TAC[ring_homomorphism]);;

let ALGEBRAIC_OVER_IMAGE = prove
 (`!(h:A->B) k l x.
        field_extension(k,l) h /\ x IN ring_carrier k
        ==> algebraic_over(k,l) h (h x)`,
  MESON_TAC[ALGEBRAIC_OVER_IMAGE_GEN; field_extension; ring_monomorphism;
            FIELD_IMP_NONTRIVIAL_RING]);;

let ALGEBRAIC_OVER_IMAGE_SUBSET = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h
        ==> IMAGE h (ring_carrier k) SUBSET {x | algebraic_over(k,l) h x}`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  SIMP_TAC[ALGEBRAIC_OVER_IMAGE]);;

let ALGEBRAIC_OVER_REFL = prove
 (`!k y:A. field k
           ==> (algebraic_over (k,k) I y <=> y IN ring_carrier k)`,
  MESON_TAC[ALGEBRAIC_OVER_IN_CARRIER; ALGEBRAIC_OVER_IMAGE;
            FIELD_EXTENSION_REFL; I_THM]);;

let ALGEBRAIC_OVER_SUBRING_GENERATED = prove
 (`!(h:A->B) k l s x.
        field_extension(k,l) h /\
        IMAGE h (ring_carrier k) SUBSET s /\
        algebraic_over(k,l) h x /\ x IN s
        ==> algebraic_over(k,subring_generated l s) h x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [algebraic_over]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[algebraic_over; SUBRING_GENERATED_INC_GEN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:(1->num)->A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN
  EXISTS_TAC `(:1)` THEN ASM_SIMP_TAC[SUBRING_GENERATED_INC_GEN] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN
  ASM_MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]);;

let ALGEBRAIC_OVER_SUBFIELD_GENERATED = prove
 (`!(h:A->B) k l s x.
        field_extension(k,l) h /\
        IMAGE h (ring_carrier k) SUBSET s /\
        algebraic_over(k,l) h x /\ x IN s
        ==> algebraic_over(k,subfield_generated l s) h x`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  ASM_SIMP_TAC[SUBFIELD_GENERATED_INC_GEN] THEN
  TRANS_TAC SUBSET_TRANS `ring_carrier l INTER s:B->bool` THEN
  ASM_REWRITE_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER; SUBSET_INTER] THEN
  ASM_MESON_TAC[FIELD_EXTENSION_IMP_SUBSET]);;

let ALGEBRAIC_OVER_SUBRING_GENERATED_MONO = prove
 (`!(h:A->B) k l s t x.
        algebraic_over (subring_generated k s,l) h x /\ s SUBSET t
        ==> algebraic_over (subring_generated k t,l) h x`,
  REWRITE_TAC[algebraic_over; POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
  REWRITE_TAC[POLY_SUBRING_GENERATED_CLAUSES] THEN
  MESON_TAC[RING_CARRIER_POLY_SUBRING_GENERATED_MONO; SUBSET]);;

let ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED = prove
 (`!(h:A->B) k l s x.
        field_extension(k,l) h
        ==> (algebraic_over (subfield_generated k s,l) h x <=>
             algebraic_over (subring_generated k s,l) h x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[algebraic_over] THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    REWRITE_TAC[POLY_EXTEND_FROM_SUBRING_GENERATED;
                POLY_SUBRING_GENERATED_CLAUSES] THEN
    REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED];
    ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT] THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MESON_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER;
              ALGEBRAIC_OVER_SUBRING_GENERATED_MONO]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CONJUNCT1 POLY_RING]) THEN
  REWRITE_TAC[ring_polynomial; IN_ELIM_THM; ring_powerseries] THEN
  REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `s:A->bool`; `(:1)`; `p:(1->num)->A`]
        POLY_OVER_SUBFIELD_GENERATED_DENOMINATOR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[field_extension; FIELD_SUBFIELD_GENERATED];
    DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `poly_mul k (poly_const k d) p:(1->num)->A` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(snd(EQ_IMP_RULE(ISPECL [`subfield_generated k s:A ring`; `(:1)`]
        INTEGRAL_DOMAIN_POLY_RING))) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[FIELD_SUBFIELD_GENERATED;
                    FIELD_IMP_INTEGRAL_DOMAIN; field_extension];
      REWRITE_TAC[integral_domain]] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`poly_const k d:(1->num)->A`; `p:(1->num)->A`] o CONJUNCT2) THEN
    MP_TAC(ISPECL [`k:A ring`; `s:A->bool`; `(:1)`;
                   `poly_const k d:(1->num)->A`; `p:(1->num)->A`]
      (el 4 (CONJUNCTS POLY_SUBFIELD_GENERATED_CLAUSES))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
     `(p' ==> p) /\ p' /\ (q ==> t ==> r) /\ ~s
      ==> (p ==> q) ==> (p' /\ r ==> s) ==> ~t`) THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[POLY_RING; ring_polynomial; ring_powerseries; IN_ELIM_THM];
      ASM_MESON_TAC[POLY_CONST_SUBFIELD_GENERATED; POLY_CONST;
                    SUBRING_SUBSET_SUBFIELD_GENERATED; SUBSET];
      REWRITE_TAC[POLY_SUBFIELD_GENERATED_CLAUSES] THEN
      ASM_SIMP_TAC[POLY_RING];
      ASM_REWRITE_TAC[POLY_SUBFIELD_GENERATED_CLAUSES] THEN
      ASM_MESON_TAC[POLY_CONST_0; POLY_CONST_EQ; POLY_RING]];
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `(\v. x):1->B`;
                   `poly_const k d:(1->num)->A`; `p:(1->num)->A`]
        POLY_EXTEND_MUL) THEN
    ASM_SIMP_TAC[RING_MUL_RZERO; POLY_EXTEND] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_CONST; FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    ASM_REWRITE_TAC[ring_polynomial; ring_powerseries] THEN
    ASM SET_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET;
                RING_CARRIER_SUBRING_GENERATED_SUBSET]]);;

let ALGEBRAIC_OVER_NONMONOMORPHISM = prove
 (`!(h:A->B) k l a.
        ring_homomorphism(k,l) h /\ a IN ring_carrier l
        ==> (algebraic_over (k,l) h a <=>
             ~ring_monomorphism (poly_ring k (:1),l)
                                (poly_extend(k,l) h (\v. a)))`,
  SIMP_TAC[RING_MONOMORPHISM_ALT; RING_HOMOMORPHISM_POLY_EXTEND] THEN
  MESON_TAC[algebraic_over]);;

let ALGEBRAIC_EXTENSION = prove
 (`!(f:A->B) k l.
        algebraic_extension (k,l) f <=>
        field_extension (k,l) f /\
        !x. x IN ring_carrier l
            ==> ?p. p IN ring_carrier(poly_ring k (:1)) /\
                    ~(p = ring_0(poly_ring k (:1))) /\
                    poly_extend(k,l) f (\v. x) p = ring_0 l`,
  SIMP_TAC[algebraic_extension; algebraic_over]);;

let ALGEBRAIC_EXTENSION_ALT = prove
 (`!(f:A->B) k l.
        algebraic_extension (k,l) f <=>
        field_extension (k,l) f /\
        !x. x IN ring_carrier l
            ==> ?p. p IN ring_carrier(poly_ring k (:1)) /\
                    ~(p = ring_0(poly_ring k (:1))) /\
                    poly_eval l (f o p) x = ring_0 l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[field_extension; ALGEBRAIC_EXTENSION; ring_monomorphism] THEN
  REWRITE_TAC[poly_eval] THEN MESON_TAC[POLY_EXTEND_EVALUATE]);;

let ALGEBRAIC_OVER_EQ = prove
 (`!k l a (f:A->B) f'.
          ring_homomorphism (k,l) f /\
          (!x. x IN ring_carrier k ==> f' x = f x) /\
          algebraic_over (k,l) f a
          ==> algebraic_over (k,l) f' a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[algebraic_over] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `p:(1->num)->A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC POLY_EXTEND_EQ THEN EXISTS_TAC `(:1)` THEN
  ASM_REWRITE_TAC[]);;

let ALGEBRAIC_OVER_EQ_EQ = prove
 (`!k l a (f:A->B) f'.
        ring_homomorphism (k,l) f /\
        (!x. x IN ring_carrier k ==> f' x = f x)
        ==> (algebraic_over (k,l) f a <=> algebraic_over (k,l) f' a)`,
  MESON_TAC[ALGEBRAIC_OVER_EQ; RING_HOMOMORPHISM_EQ]);;

let ALGEBRAIC_EXTENSION_EQ = prove
 (`!k l (f:A->B) f'.
        algebraic_extension(k,l) f /\
        (!x. x IN ring_carrier k ==> f' x = f x)
        ==> algebraic_extension (k,l) f'`,
  REWRITE_TAC[algebraic_extension] THEN
  MESON_TAC[ALGEBRAIC_OVER_EQ; FIELD_EXTENSION_EQ; field_extension;
            RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT = prove
 (`!(h:A->B) k l a b n.
        field k /\ ring_homomorphism(k,l) h /\ a IN ring_carrier l /\
        b HAS_SIZE n /\ b SUBSET ring_carrier l /\
        ring_carrier l SUBSET ring_span (k,l) h b
        ==> ?p. p IN ring_carrier(poly_ring k (:1)) /\
                ~(p = ring_0 (poly_ring k (:1))) /\
                poly_deg k p <= n /\
                poly_extend (k,l) h (\v. a) p = ring_0 l`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `ring_pow l (a:B)`; `0..n`; `b:B->bool`]
    RING_DEPENDENT_SPAN_IMAGE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; RING_POW];
    REWRITE_TAC[IN_NUMSEG; LE_0; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `c:num->A` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC
   `p = \m. if m one <= n then (c:num->A) (m one) else ring_0 k` THEN
  EXISTS_TAC `p:(1->num)->A` THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM RING_POLYNOMIAL; ring_polynomial; ring_powerseries;
           MONOMIAL_VARS_UNIVARIATE; INFINITE; FINITE_MONOMIAL_VARS_1] THEN
    EXPAND_TAC "p" THEN CONJ_TAC THENL
     [ASM SET_TAC[RING_POW; RING_0; IN_NUMSEG; LE_0]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS {{m | m one = i} | i IN {i:num | i <= n}}` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[FINITE_UNIONS; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE] THEN
    X_GEN_TAC `i:num` THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{(\v. i):1->num}` THEN
    REWRITE_TAC[FINITE_SING; SUBSET; FORALL_IN_GSPEC; IN_SING] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[one];
    DISCH_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "p" THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_FUN_FROM_1; POLY_RING; POLY_0] THEN
    ASM_MESON_TAC[IN_NUMSEG; LE_0];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[POLY_DEG_LE_EQ; RING_POLYNOMIAL] THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[FORALL_FUN_FROM_1; MONOMIAL_DEG_UNIVARIATE] THEN
    ASM_MESON_TAC[IN_NUMSEG; LE_0];
    DISCH_TAC] THEN
  ASM_SIMP_TAC[POLY_EXTEND_UNIVARIATE] THEN EXPAND_TAC "p" THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_SIMP_TAC[COND_RAND; COND_RATOR; RING_MUL_LZERO; RING_POW] THEN
  REWRITE_TAC[GSYM RING_SUM_RESTRICT_SET] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_SUPERSET THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:(1->num)->A`; `(\x. i):1->num`]
    MONOMIAL_DEG_LE_POLY_DEG) THEN
  ASM_REWRITE_TAC[RING_POLYNOMIAL; MONOMIAL_DEG_UNIVARIATE] THEN
  MATCH_MP_TAC(TAUT
   `(p ==> r) ==> (~p ==> q) ==> ~q ==> r`) THEN
  EXPAND_TAC "p" THEN REWRITE_TAC[ASSUME `i:num <= n`] THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_POW]);;

let FINITE_IMP_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h ==> algebraic_extension (k,l) h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[finite_extension; algebraic_extension] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:B` THEN DISCH_TAC THEN
  REWRITE_TAC[algebraic_over] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`; `b:B->bool`;
            `CARD(b:B->bool)`] FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT) THEN
  ASM_REWRITE_TAC[HAS_SIZE; SUBSET_REFL] THEN
  ASM_MESON_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let RING_SIMPLE_EXTENSION_SPAN = prove
 (`!(h:A->B) k l a.
        ring_homomorphism(k,l) h /\ a IN ring_carrier l
        ==> ring_carrier
              (subring_generated l (a INSERT IMAGE h (ring_carrier k))) =
            ring_span (k,l) h { ring_pow l a n | n IN (:num) }`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM IMAGE_POLY_EXTEND_1];
        W(MP_TAC o PART_MATCH lhand RING_SPAN_SUBSET_SUBRING_GENERATED o
      lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
    MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_UNION; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN TRY(MATCH_MP_TAC RING_POW_IN_SUBRING_GENERATED) THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `p:(1->num)->A` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[POLY_EXTEND_UNIVARIATE] THEN
  MATCH_MP_TAC RING_SPAN_SUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_SPAN_MUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POLY_MONOMIAL_IN_CARRIER) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC[RING_POW] THEN SET_TAC[]);;

let RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN = prove
 (`!(h:A->B) k l p a.
        field k /\ ring_homomorphism(k,l) h /\ a IN ring_carrier l /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = ring_0(poly_ring k (:1))) /\
        poly_extend (k,l) h (\v. a) p = ring_0 l
        ==> ring_carrier
              (subring_generated l (a INSERT IMAGE h (ring_carrier k))) =
            ring_span (k,l) h { ring_pow l a n | n < poly_deg k p}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM IMAGE_POLY_EXTEND_1];
    ASM_SIMP_TAC[RING_SIMPLE_EXTENSION_SPAN] THEN
    MATCH_MP_TAC RING_SPAN_MONO THEN SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `f:(1->num)->A` THEN STRIP_TAC THEN MP_TAC(ISPECL
   [`k:A ring`; `f:(1->num)->A`; `p:(1->num)->A`] POLY_DIVISION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:(1->num)->A`; `r:(1->num)->A`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[POLY_RING] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  ASM_SIMP_TAC[POLY_EXTEND_ADD; POLY_EXTEND_MUL; RING_POLYNOMIAL_MUL] THEN
  ASM_SIMP_TAC[POLY_EXTEND; RING_MUL_RZERO; RING_ADD_LZERO] THEN
  ASM_SIMP_TAC[POLY_EXTEND_UNIVARIATE; GSYM RING_POLYNOMIAL] THEN
  MATCH_MP_TAC RING_SPAN_SUM THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_CASES_TAC `(r:(1->num)->A) (\v. i) = ring_0 k` THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_SPAN_0; RING_POW] THEN
  MATCH_MP_TAC RING_SPAN_MUL THEN ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL
   [ASM_MESON_TAC[POLY_MONOMIAL_IN_CARRIER; RING_POLYNOMIAL]; ALL_TAC]) THEN
  MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC[RING_POW] THEN
  MATCH_MP_TAC(SET_RULE
   `P i ==> ring_pow l a i IN {ring_pow l a n | P n}`) THEN
  POP_ASSUM MP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 MP_TAC SUBST1_TAC) THEN
  REWRITE_TAC[POLY_RING; POLY_0] THEN ASM_ARITH_TAC);;

let FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN = prove
 (`!(h:A->B) k l a.
        field k /\ integral_domain l /\
        ring_homomorphism(k,l) h /\
        algebraic_over (k,l) h a
        ==> field(subring_generated l (a INSERT IMAGE h (ring_carrier k)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  MP_TAC(ISPECL
   [`poly_ring (k:A ring) (:1)`; `l:B ring`;
    `poly_extend (k,l) (h:A->B) (\x:1. a)`]
   FIRST_RING_ISOMORPHISM_THEOREM) THEN
  REWRITE_TAC[ring_image] THEN
  ASM_SIMP_TAC[IMAGE_POLY_EXTEND_1; RING_HOMOMORPHISM_POLY_EXTEND] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
  ASM_SIMP_TAC[FIELD_QUOTIENT_RING; RING_IDEAL_RING_KERNEL;
               RING_HOMOMORPHISM_POLY_EXTEND] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PID_MAXIMAL_EQ_PRIME_IDEAL o snd) THEN
  ASM_SIMP_TAC[PID_POLY_RING; prime_ideal; proper_ideal;
              RING_IDEAL_RING_KERNEL; RING_HOMOMORPHISM_POLY_EXTEND] THEN
  REWRITE_TAC[ring_kernel] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[algebraic_over]) THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM]] THEN
  SIMP_TAC[PSUBSET_ALT; SUBSET_RESTRICT; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `poly_1 k:(1->num)->A` THEN
    ASM_SIMP_TAC[POLY_EXTEND_1; RING_HOMOMORPHISM_POLY_EXTEND] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_NONTRIVIAL; GSYM RING_POLYNOMIAL;
                 RING_POLYNOMIAL_1];
    MAP_EVERY X_GEN_TAC [`p:(1->num)->A`; `q:(1->num)->A`] THEN
    REWRITE_TAC[POLY_RING; IN_ELIM_THM; SUBSET_UNIV] THEN
    ASM_SIMP_TAC[POLY_EXTEND_MUL; RING_HOMOMORPHISM_POLY_EXTEND;
                 IN_UNIV; IMP_CONJ; INTEGRAL_DOMAIN_MUL_EQ_0; POLY_EXTEND]]);;

let FIELD_SIMPLE_ALGEBRAIC_EXTENSION_EQ = prove
 (`!(h:A->B) k l a.
        field k /\ integral_domain l /\
        ring_homomorphism(k,l) h /\ a IN ring_carrier l
        ==> (field(subring_generated l (a INSERT IMAGE h (ring_carrier k))) <=>
             algebraic_over (k,l) h a)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN] THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  ASM_SIMP_TAC[ALGEBRAIC_OVER_NONMONOMORPHISM] THEN
  REWRITE_TAC[GSYM RING_ISOMORPHISM_ONTO_IMAGE; ring_image] THEN
  ASM_SIMP_TAC[IMAGE_POLY_EXTEND_1] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_ISOMORPHIC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FIELD_POLY_RING] THEN
  REWRITE_TAC[UNIV_NOT_EMPTY]);;

let FIELD_SIMPLE_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l a.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a
        ==> field(subring_generated l (a INSERT IMAGE h (ring_carrier k)))`,
  REWRITE_TAC[field_extension] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM;
               FIELD_IMP_INTEGRAL_DOMAIN]);;

let FINITE_SIMPLE_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l a.
        field_extension(k,l) h /\
        algebraic_over(k,l) h a
        ==> finite_extension
             (k,subring_generated l (a INSERT IMAGE h (ring_carrier k))) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_SIMP_TAC[finite_extension; field_extension;
               FIELD_SIMPLE_ALGEBRAIC_EXTENSION] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC o
     CONJUNCT2 o GEN_REWRITE_RULE I [algebraic_over]) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN  CONJ_TAC THENL
   [MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  EXISTS_TAC `{ring_pow l (a:B) n | n < poly_deg k (p:(1->num)->A)}` THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_POW_IN_SUBRING_GENERATED THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC THEN
    ASM_REWRITE_TAC[IN_INSERT; INSERT_SUBSET] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
     [`h:A->B`; `k:A ring`;
      `subring_generated l (a INSERT IMAGE (h:A->B) (ring_carrier k))`;
      `p:(1->num)->A`; `a:B`]
     RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN) THEN
  SIMP_TAC[SUBRING_GENERATED_IDEMPOT; SUBSET_REFL] THEN
  REWRITE_TAC[RING_POW_SUBRING_GENERATED] THEN
  GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBRING_GENERATED_INC THEN
    ASM_REWRITE_TAC[IN_INSERT; INSERT_SUBSET] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[];
    REWRITE_TAC[SUBRING_GENERATED]] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN EXISTS_TAC `(:1)` THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN
  ASM_REWRITE_TAC[IN_INSERT; INSERT_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[]);;

let ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m z.
        ring_monomorphism (k,l) f /\ ring_homomorphism (l,m) g /\
        algebraic_over (k,m) (g o f) z
        ==> algebraic_over (l,m) g z`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  REWRITE_TAC[algebraic_over] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(f:A->B) o (p:(1->num)->A)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o ISPEC `p:(1->num)->A` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] POLY_EQ_0_MONOMORPHIC_IMAGE)) THEN
    ASM_MESON_TAC[POLY_RING; RING_POLYNOMIAL];
    MP_TAC(ISPECL
     [`k:A ring`; `l:B ring`; `m:C ring`; `f:A->B`; `g:B->C`]
     RING_HOMOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC
       `poly_extend (k,m) ((g:B->C) o (f:A->B)) (\v:1. z) p = ring_0 m` THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; o_ASSOC]]);;

let ALGEBRAIC_OVER_ISOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m z.
        ring_isomorphism (k,l) f /\ ring_homomorphism (l,m) g
        ==> (algebraic_over (k,m) (g o f) z <=> algebraic_over (l,m) g z)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE;
                  RING_ISOMORPHISM_IMP_MONOMORPHISM];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `f':B->A` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [ring_isomorphism]) THEN
  MATCH_MP_TAC
   (INST_TYPE [`:B`,`:A`; `:Y`,`:B`; `:Z`,`:C`]
         ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE) THEN
  MAP_EVERY EXISTS_TAC [`f':B->A`; `l:B ring`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC ALGEBRAIC_OVER_EQ THEN EXISTS_TAC `g:B->C`] THEN
  ASM_MESON_TAC[o_THM; ALGEBRAIC_OVER_EQ; RING_ISOMORPHISMS_ISOMORPHISM;
                RING_ISOMORPHISM_IMP_MONOMORPHISM; RING_HOMOMORPHISM_COMPOSE;
                RING_ISOMORPHISM_IMP_HOMOMORPHISM]);;

let ALGEBRAIC_OVER_RANGE = prove
 (`!(h:A->B) k l x.
        ring_monomorphism(k,l) h
        ==> (algebraic_over (k,l) h x <=>
             algebraic_over
               (subring_generated l (IMAGE h (ring_carrier k)),l) I x)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [GSYM RING_ISOMORPHISM_ONTO_IMAGE]) THEN
  ASM_REWRITE_TAC[ring_image; ring_isomorphism] THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':B->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`h':B->A`; `h:A->B`;
     `subring_generated l (IMAGE (h:A->B) (ring_carrier k))`;
     `k:A ring`; `l:B ring`; `x:B`]
   ALGEBRAIC_OVER_ISOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ALGEBRAIC_OVER_EQ_EQ THEN
  REWRITE_TAC[o_DEF; I_DEF; RING_HOMOMORPHISM_INCLUSION] THEN
  ASM_MESON_TAC[]);;

let ALGEBRAIC_OVER_FIELD_EXTENSION = prove
 (`!(f:A->B) (g:B->C) k l m z.
        field_extension (k,l) f /\ field_extension (l,m) g /\
        algebraic_over (k,m) (g o f) z
        ==> algebraic_over (l,m) g z`,
  REWRITE_TAC[field_extension] THEN
  MESON_TAC[ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE;
            RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l b.
        field_extension(k,l) h /\
        FINITE b /\
        (!x. x IN b ==> algebraic_over(k,l) h x)
        ==> finite_extension
             (k,subring_generated l (IMAGE h (ring_carrier k) UNION b)) h`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[EMPTY_SUBSET; INSERT_SUBSET; UNION_EMPTY; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_EXTENSION_ISOMORPHISM THEN
    ASM_MESON_TAC[field_extension; RING_ISOMORPHISM_ONTO_IMAGE; ring_image];
    REWRITE_TAC[FORALL_IN_INSERT]] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `b:B->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`I:B->B`;
    `subring_generated l (IMAGE (h:A->B) (ring_carrier k) UNION b)`;
    `l:B ring`;
    `y:B`]
    FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[finite_extension; field_extension]) THEN
      ASM_REWRITE_TAC[field_extension] THEN
      MATCH_MP_TAC RING_MONOMORPHISM_FROM_SUBRING_GENERATED THEN
      REWRITE_TAC[RING_MONOMORPHISM_I];
      MATCH_MP_TAC(REWRITE_RULE[TAUT
       `p /\ q /\ r ==> s <=> p /\ r ==> q ==> s`]
        ALGEBRAIC_OVER_FIELD_EXTENSION) THEN
      ASM_MESON_TAC[I_O_ID; finite_extension]];
    UNDISCH_TAC
     `finite_extension
       (k,subring_generated l (IMAGE h (ring_carrier k) UNION b))
       (h:A->B)` THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FINITE_EXTENSION_TRANS) THEN
    REWRITE_TAC[I_O_ID; IMAGE_I] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
    REWRITE_TAC[SUBRING_GENERATED_UNION_RIGHT] THEN
    AP_TERM_TAC THEN SET_TAC[]]);;

let FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h <=>
        finitely_generated_extension (k,l) h /\
        algebraic_extension (k,l) h`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION;
           FINITE_IMP_FINITELY_GENERATED_EXTENSION] THEN
  REWRITE_TAC[algebraic_extension] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[finitely_generated_extension] THEN
  ASM_MESON_TAC[FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION; SUBSET;
    SUBRING_EQ_SUBFIELD_GENERATED; finite_extension; field_extension]);;

let ALGEBRAIC_FROM_SUBRING_GENERATED = prove
 (`!(h:A->B) k l s x.
        field_extension (k,subring_generated l s) h /\
        algebraic_over(k,subring_generated l s) h x
        ==> algebraic_over(k,l) h x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[algebraic_over] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
        RING_CARRIER_SUBRING_GENERATED_SUBSET)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:(1->num)->A` THEN
  REWRITE_TAC[SUBRING_GENERATED] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN
  ASM_MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]);;

let ALGEBRAIC_EXTENSION_ISOMORPHISM = prove
 (`!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism (k,l) f
        ==> algebraic_extension (k,l) f`,
  MESON_TAC[FINITE_EXTENSION_ISOMORPHISM; FINITE_IMP_ALGEBRAIC_EXTENSION]);;

let ALGEBRAIC_EXTENSION_REFL = prove
 (`!k:A ring. algebraic_extension (k,k) I <=> field k`,
  MESON_TAC[ALGEBRAIC_EXTENSION; field_extension;
            ALGEBRAIC_EXTENSION_ISOMORPHISM; RING_ISOMORPHISM_I]);;

let ALGEBRAIC_EXTENSION_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m.
        algebraic_extension (k,l) f /\ algebraic_extension (l,m) g
        ==> algebraic_extension (k,m) (g o f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[algebraic_extension] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_TRANS]; DISCH_TAC] THEN
  X_GEN_TAC `z:C` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[algebraic_over] o SPEC `z:C`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p:(1->num)->B` THEN STRIP_TAC THEN MP_TAC(ISPECL
   [`f:A->B`; `g:B->C`; `k:A ring`;
    `subring_generated l
        (IMAGE (f:A->B) (ring_carrier k) UNION
         {p(\i:1. n) |n| n <= poly_deg l p})`;
    `subring_generated m (z INSERT IMAGE (g:B->C)
       (ring_carrier(subring_generated l
        (IMAGE (f:A->B) (ring_carrier k) UNION
         {p(\i:1. n) |n| n <= poly_deg l p}))))`]
    FINITE_EXTENSION_TRANS) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
    REWRITE_TAC[algebraic_extension; RIGHT_AND_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:C`) THEN MATCH_MP_TAC(TAUT
     `(p /\ r ==> s) /\ q ==> (p /\ (q ==> r) ==> s)`) THEN
    REWRITE_TAC[ALGEBRAIC_FROM_SUBRING_GENERATED] THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; IN_INSERT] THEN
    TRANS_TAC SUBSET_TRANS `IMAGE (g:B->C) (ring_carrier l)` THEN
    SIMP_TAC[IMAGE_SUBSET; RING_CARRIER_SUBRING_GENERATED_SUBSET] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [field_extension; ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[]] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[POLY_MONOMIAL_IN_CARRIER];
    DISCH_TAC] THEN
  MATCH_MP_TAC FINITE_SIMPLE_ALGEBRAIC_EXTENSION THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_FROM_SUBRING_GENERATED;
                  finite_extension; field_extension];
    ASM_REWRITE_TAC[algebraic_over]] THEN
  EXISTS_TAC `p:(1->num)->B` THEN
  ASM_REWRITE_TAC[POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
  ASM_REWRITE_TAC[POLY_SUBRING_GENERATED_CLAUSES] THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  ASM_SIMP_TAC[RING_CARRIER_POLY_SUBRING_GENERATED; IN_ELIM_THM;
               SUBRING_SUBRING_GENERATED; IN_INTER] THEN
  REWRITE_TAC[FORALL_FUN_FROM_1] THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `m:num <= poly_deg l (p:(1->num)->B)` THENL
   [MATCH_MP_TAC SUBRING_GENERATED_INC THEN
    CONJ_TAC THENL [REWRITE_TAC[UNION_SUBSET]; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[POLY_MONOMIAL_IN_CARRIER]] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [field_extension; ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[];
    POP_ASSUM MP_TAC THEN
    ASM_SIMP_TAC[POLY_DEG_GE_EQ; RING_POLYNOMIAL] THEN
    SIMP_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; TAUT `p \/ ~q <=> q ==> p`] THEN
    SIMP_TAC[MONOMIAL_DEG_UNIVARIATE; LE_REFL; RING_0_IN_SUBRING_GENERATED]]);;

let ALGEBRAIC_EXTENSION_TRANS_EQ = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g
        ==> (algebraic_extension (k,m) (g o f) <=>
             algebraic_extension (k,l) f /\
             algebraic_extension (l,m) g)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[ALGEBRAIC_EXTENSION_TRANS] THEN
  ASM_REWRITE_TAC[ALGEBRAIC_EXTENSION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
   [DISCH_TAC THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:B->C) y`) THEN ANTS_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC `p:(1->num)->A` THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[GSYM o_ASSOC; GSYM poly_eval] THEN
    MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `y:B`; `g:B->C`;
                   `(f:A->B) o (p:(1->num)->A)`]
        POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[IN_RING_POLYNOMIAL_CARRIER_COMPOSE;
                    FIELD_EXTENSION_IMP_HOMOMORPHISM];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[POLY_EVAL; RING_MONOMORPHISM_ALT;
                    FIELD_EXTENSION_IMP_MONOMORPHISM]];
    DISCH_TAC THEN X_GEN_TAC `z:C` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:C`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(f:A->B) o (p:(1->num)->A)` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_RING_POLYNOMIAL_CARRIER_COMPOSE;
                    FIELD_EXTENSION_IMP_HOMOMORPHISM];
      ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE; RING_POLYNOMIAL; POLY_CLAUSES;
                    FIELD_EXTENSION_IMP_MONOMORPHISM];
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
      REWRITE_TAC[o_ASSOC]]]);;

let CARD_LE_ALGEBRAIC_EXTENSION = prove
 (`!(f:A->B) k l (m:C->bool).
        algebraic_extension (k,l) f /\ INFINITE m /\ ring_carrier k <=_c m
        ==> ring_carrier l <=_c m`,
  REPEAT STRIP_TAC THEN TRANS_TAC CARD_LE_TRANS
   `UNIONS { {x | x IN ring_carrier l /\
                  poly_eval l ((f:A->B) o p) x = ring_0 l} |
             p IN ring_carrier (poly_ring k (:1)) /\
             ~(p = ring_0 (poly_ring k (:1)))}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_SUBSET THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[ALGEBRAIC_EXTENSION_ALT]) THEN
    SET_TAC[];
    MATCH_MP_TAC CARD_LE_UNIONS] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALGEBRAIC_EXTENSION; field_extension]) THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    W(MP_TAC o PART_MATCH lhand CARD_LE_IMAGE o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_TRANS) THEN
    TRANS_TAC CARD_LE_TRANS `ring_carrier (poly_ring (k:A ring) (:1))` THEN
    SIMP_TAC[CARD_LE_SUBSET; SUBSET_RESTRICT] THEN
    TRANS_TAC CARD_LE_TRANS `ring_carrier(k:A ring) *_c (:num)` THEN
    ASM_SIMP_TAC[CARD_MUL2_ABSORB_LE; GSYM INFINITE_CARD_LE] THEN
    MATCH_MP_TAC CARD_EQ_IMP_LE THEN MATCH_MP_TAC CARD_EQ_POLY_RING_FINITE THEN
    ASM_REWRITE_TAC[FINITE_1; UNIV_NOT_EMPTY] THEN
    ASM_MESON_TAC[FIELD_IMP_NONTRIVIAL_RING];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CARD_LE_FINITE_INFINITE THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_ROOT_BOUND o snd) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; SIMP_TAC[]] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[IN_RING_POLYNOMIAL_CARRIER_COMPOSE; ring_monomorphism];
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))] THEN
    REWRITE_TAC[CONTRAPOS_THM; FUN_EQ_THM; o_THM] THEN
    REWRITE_TAC[POLY_RING; POLY_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [POLY_RING; ring_polynomial; ring_powerseries; IN_ELIM_THM]) THEN
    ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]]);;

let CARD_EQ_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l.
        algebraic_extension (k,l) h /\ INFINITE(ring_carrier k)
        ==> ring_carrier l =_c ring_carrier k`,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_carrier k:A->bool`]
        CARD_LE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC[CARD_LE_REFL];
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_MONOMORPHISM) THEN
    REWRITE_TAC[le_c] THEN EXISTS_TAC `h:A->B` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[]]);;

let RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l f.
        algebraic_extension(k,l) h /\
        ring_monomorphism(l,l) f /\
        (!x. x IN ring_carrier k ==> f(h x) = h x)
        ==> ring_automorphism l f`,
  REWRITE_TAC[algebraic_extension] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[RING_ISOMORPHISM_MONOMORPHISM_ALT; ring_automorphism] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[algebraic_over] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  ABBREV_TAC `s = {x | x IN ring_carrier l /\
                       poly_extend (k,l) (h:A->B) (\v:1. x) p = ring_0 l}` THEN
  MP_TAC(ISPECL [`s:B->bool`; `f:B->B`] SURJECTIVE_IFF_INJECTIVE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; RING_MONOMORPHISM_IMP_HOMOMORPHISM;
                   GSYM poly_eval] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) POLY_ROOT_BOUND o snd) THEN
      ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `(:1)`]
        RING_MONOMORPHISM_POLY_RINGS) THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
      REWRITE_TAC[RING_MONOMORPHISM_ALT_EQ; ring_homomorphism] THEN
      ASM SET_TAC[];
      EXPAND_TAC "s" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `y:B` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `l:B ring`; `h:A->B`;
                     `(:1)`; `(\v. y):1->B`; `f:B->B`; `p:(1->num)->A`]
        POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; o_DEF] THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC POLY_EXTEND_EQ] THEN
      EXISTS_TAC `(:1)` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
    RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[]]);;

let RING_AUTOMORPHISM_FROBENIUS_GEN = prove
 (`!k:A ring.
        prime(ring_char k) /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I
        ==> ring_automorphism k (\x. ring_pow k x (ring_char k))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    RING_AUTOMORPHISM_OF_ALGEBRAIC_EXTENSION)) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[algebraic_extension]) THEN
  REWRITE_TAC[field_extension; I_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_FROBENIUS; FIELD_IMP_INTEGRAL_DOMAIN] THEN
  ASM_SIMP_TAC[GSYM FROBENIUS_FIXED_FIELD; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Algebraic elements form a field etc.                                      *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_OVER_0 = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h ==> algebraic_over(k,l) h (ring_0 l)`,
  MESON_TAC[ALGEBRAIC_OVER_IMAGE; field_extension; ring_monomorphism;
            RING_HOMOMORPHISM_0; RING_0]);;

let ALGEBRAIC_OVER_1 = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h ==> algebraic_over(k,l) h (ring_1 l)`,
  MESON_TAC[ALGEBRAIC_OVER_IMAGE; field_extension; ring_monomorphism;
            RING_HOMOMORPHISM_1; RING_1]);;

let ALGEBRAIC_OVER_NEG,ALGEBRAIC_OVER_INV = (CONJ_PAIR o prove)
 (`(!(h:A->B) k l a.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a
        ==> algebraic_over (k,l) h (ring_neg l a)) /\
   (!(h:A->B) k l a.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a
        ==> algebraic_over (k,l) h (ring_inv l a))`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
     FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
  REWRITE_TAC[algebraic_extension] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ALGEBRAIC_FROM_SUBRING_GENERATED THEN
  EXISTS_TAC `a INSERT IMAGE (h:A->B) (ring_carrier k)` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
   [MATCH_MP_TAC RING_NEG_IN_SUBRING_GENERATED;
    MATCH_MP_TAC IN_SUBFIELD_INV THEN
    ASM_SIMP_TAC[subfield_of; FIELD_SIMPLE_ALGEBRAIC_EXTENSION;
                 SUBRING_SUBRING_GENERATED;
                 SUBRING_GENERATED_BY_SUBRING_GENERATED]] THEN
  MATCH_MP_TAC SUBRING_GENERATED_INC THEN
  ASM_REWRITE_TAC[UNION_SUBSET; INSERT_SUBSET; EMPTY_SUBSET;
                  IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [algebraic_over; field_extension;
    ring_monomorphism; ring_homomorphism]) THEN
  ASM SET_TAC[]);;

let ALGEBRAIC_OVER_ADD,ALGEBRAIC_OVER_MUL = (CONJ_PAIR o prove)
 (`(!(h:A->B) k l a b.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a /\ algebraic_over (k,l) h b
        ==> algebraic_over (k,l) h (ring_add l a b)) /\
   (!(h:A->B) k l a b.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a /\ algebraic_over (k,l) h b
        ==> algebraic_over (k,l) h (ring_mul l a b))`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `{a:B,b}`]
     FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
  REWRITE_TAC[algebraic_extension] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ALGEBRAIC_FROM_SUBRING_GENERATED THEN
  EXISTS_TAC `IMAGE (h:A->B) (ring_carrier k) UNION {a, b}` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
   [MATCH_MP_TAC RING_ADD_IN_SUBRING_GENERATED;
    MATCH_MP_TAC RING_MUL_IN_SUBRING_GENERATED] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN
  ASM_REWRITE_TAC[UNION_SUBSET; INSERT_SUBSET; EMPTY_SUBSET;
                  IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [algebraic_over; field_extension;
    ring_monomorphism; ring_homomorphism]) THEN
  ASM SET_TAC[]);;

let ALGEBRAIC_OVER_SUB = prove
 (`!(h:A->B) k l a b.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a /\ algebraic_over (k,l) h b
        ==> algebraic_over (k,l) h (ring_sub l a b)`,
  SIMP_TAC[ring_sub; ALGEBRAIC_OVER_NEG; ALGEBRAIC_OVER_ADD]);;

let ALGEBRAIC_OVER_DIV = prove
 (`!(h:A->B) k l a b.
        field_extension (k,l) h /\
        algebraic_over (k,l) h a /\ algebraic_over (k,l) h b
        ==> algebraic_over (k,l) h (ring_div l a b)`,
  SIMP_TAC[ring_div; ALGEBRAIC_OVER_INV; ALGEBRAIC_OVER_MUL]);;

let ALGEBRAIC_OVER_POW = prove
 (`!(h:A->B) k l a n.
        field_extension (k,l) h /\ algebraic_over (k,l) h a
        ==> algebraic_over (k,l) h (ring_pow l a n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ring_pow] THEN
  ASM_MESON_TAC[ALGEBRAIC_OVER_1; ALGEBRAIC_OVER_MUL]);;

let SUBRING_OF_ALGEBRAIC_OVER = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> {x | algebraic_over (k,l) h x} subring_of l`,
  REWRITE_TAC[subring_of; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[ALGEBRAIC_OVER_0; ALGEBRAIC_OVER_1; ALGEBRAIC_OVER_NEG;
            ALGEBRAIC_OVER_ADD; ALGEBRAIC_OVER_MUL; ALGEBRAIC_OVER_IN_CARRIER;
            RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let SUBFIELD_OF_ALGEBRAIC_OVER = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> {x | algebraic_over (k,l) h x} subfield_of l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN
  ASM_SIMP_TAC[SUBRING_OF_ALGEBRAIC_OVER] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; RING_INV] THEN ASM_MESON_TAC[ALGEBRAIC_OVER_INV]);;

let ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC = prove
 (`!(h:A->B) k l s.
        field_extension (k,l) h /\
        (!x. x IN s ==> algebraic_over(k,l) h x)
        ==> !x. x IN ring_carrier
                  (subfield_generated l (IMAGE h (ring_carrier k) UNION s))
                ==> algebraic_over(k,l) h x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
  ASM_SIMP_TAC[SUBFIELD_OF_ALGEBRAIC_OVER] THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_UNION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[ALGEBRAIC_OVER_IMAGE]);;

let FIELD_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h /\ (!x. x IN s ==> algebraic_over(k,l) h x)
        ==> field(subring_generated l (IMAGE h (ring_carrier k) UNION s))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[field; GSYM TRIVIAL_RING_10; TRIVIAL_RING_SUBRING_GENERATED] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FIELD_IMP_NONTRIVIAL_RING; field_extension];
    REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED]] THEN
  X_GEN_TAC `a:B` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
        ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:B`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SUBSET; SUBRING_SUBSET_SUBFIELD_GENERATED]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
          FIELD_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  ASM_REWRITE_TAC[field; CONJUNCT2 SUBRING_GENERATED] THEN
  DISCH_THEN(MP_TAC o SPEC `a:B` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SUBSET; RING_CARRIER_SUBRING_GENERATED_SUBSET;
                  SUBRING_GENERATED_INC_GEN; IN_INSERT];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:B` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    SPEC_TAC(`y:B`,`y:B`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; SUBRING_SUBRING_GENERATED] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET) THEN
    ASM SET_TAC[]]);;

let SUBFIELD_OF_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h /\ (!x. x IN s ==> algebraic_over(k,l) h x)
        ==> ring_carrier(subring_generated l (IMAGE h (ring_carrier k) UNION s))
            subfield_of l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[subfield_of; SUBRING_SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  ASM_SIMP_TAC[FIELD_ALGEBRAIC_EXTENSION]);;

let FIELD_ALGEBRAIC_OVER = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> field(subring_generated l {x | algebraic_over (k,l) h x})`,
  MESON_TAC[subfield_of; SUBFIELD_OF_ALGEBRAIC_OVER]);;

let SUBRING_SUBFIELD_ALGEBRAIC_OVER = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> subring_generated l {x | algebraic_over (k,l) h x} =
            subfield_generated l {x | algebraic_over (k,l) h x}`,
  SIMP_TAC[SUBRING_EQ_SUBFIELD_GENERATED; FIELD_ALGEBRAIC_OVER]);;

let ALGEBRAIC_OVER_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m z.
        algebraic_extension(k,l) f /\ field_extension(l,m) g /\
        algebraic_over(l,m) g z
        ==> algebraic_over(k,m) (g o f) z`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`;
    `subring_generated m {x | algebraic_over(l,m) (g:B->C) x}`]
   ALGEBRAIC_EXTENSION_TRANS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[algebraic_extension] THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; ALGEBRAIC_OVER_IMAGE_SUBSET;
               SUBRING_OF_ALGEBRAIC_OVER; SUBFIELD_OF_ALGEBRAIC_OVER;
               FIELD_EXTENSION_INTO_SUBRING_GENERATED;
               ALGEBRAIC_OVER_SUBRING_GENERATED; IN_ELIM_THM] THEN
  ASM_MESON_TAC[ALGEBRAIC_FROM_SUBRING_GENERATED]);;

let ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION = prove
 (`!(f:A->B) (g:B->C) k l m x.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (algebraic_over (k,m) (g o f) x <=> algebraic_over (l,m) g x)`,
  ASM_MESON_TAC[ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE; ALGEBRAIC_OVER_TRANS;
                algebraic_extension; field_extension; ring_monomorphism]);;

(* ------------------------------------------------------------------------- *)
(* Extensions involving finite fields etc.                                   *)
(* ------------------------------------------------------------------------- *)

let FINITE_EQ_FIELD_EXTENSION = prove
 (`!(h:A->B) k l.
        FINITE(ring_carrier l)
        ==> (finite_extension(k,l) h <=> field_extension(k,l) h)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[FINITE_IMP_FIELD_EXTENSION] THEN
  REWRITE_TAC[finite_extension] THEN
  ASM_MESON_TAC[RING_SPAN_SELF; SUBSET_REFL]);;

let HAS_SIZE_FINITE_EXTENSION = prove
 (`!(h:A->B) k l b.
        field_extension (k,l) h /\ ring_basis (k,l) h b /\
        FINITE(ring_carrier k) /\ FINITE b
        ==> ring_carrier l HAS_SIZE CARD(ring_carrier k) EXP CARD b`,
  REWRITE_TAC[ring_basis; ring_spanning] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `ring_span (k,l) (h:A->B) b =
    IMAGE (\c. ring_sum l b (\x. ring_mul l (h (c x)) x))
          { c | (!x. x IN b ==> c x IN ring_carrier k) /\
                (!x. ~(x IN b) ==> c x = ARB) }`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_SPAN_FINITE; FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC(SET_RULE
     `!g. (!x. f(g x) = f x) /\ (!x. P x ==> P(g x) /\ Q(g x))
          ==> IMAGE f {x | P x} = IMAGE f {x | P x /\ Q x}`) THEN
    EXISTS_TAC `\c:B->A. RESTRICTION b c` THEN
    SIMP_TAC[RESTRICTION] THEN GEN_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    SIMP_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[GSYM FINITE_HAS_SIZE; HAS_SIZE_FUNSPACE] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B->bool`]
        RING_INDEPENDENT_FINITE_EQ) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[field_extension; ring_monomorphism]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    ASM_MESON_TAC[]]);;

let FINITE_FINITE_FIELD_EXTENSION = prove
 (`!(h:A->B) k l.
        FINITE(ring_carrier k)
        ==> (finite_extension(k,l) h <=>
             field_extension(k,l) h /\ FINITE(ring_carrier l))`,
  MESON_TAC[FINITE_EQ_FIELD_EXTENSION; FINITE_EXTENSION_BASIS;
            HAS_SIZE; HAS_SIZE_FINITE_EXTENSION; ring_basis]);;

let CARD_FINITE_EXTENSION = prove
 (`!(h:A->B) k l b.
        field_extension (k,l) h /\ ring_basis (k,l) h b /\
        FINITE(ring_carrier k) /\ FINITE b
        ==> CARD(ring_carrier l) = CARD(ring_carrier k) EXP CARD b`,
  MESON_TAC[HAS_SIZE; HAS_SIZE_FINITE_EXTENSION]);;

let FIELD_EXTENSION_FROM_PRIME_SUBRING = prove
 (`!r:A ring.
    field_extension (subring_generated r {ring_of_int r n | n IN (:int)},r)
                    I <=>
    field r /\ prime(ring_char r)`,
  REWRITE_TAC[field_extension; FIELD_PRIME_SUBRING; I_DEF] THEN
  REWRITE_TAC[RING_MONOMORPHISM_INCLUSION; CONJ_ACI]);;

let FINITE_INTEGRAL_DOMAIN_SIZE = prove
 (`!k:A ring.
        integral_domain k /\ FINITE(ring_carrier k)
        ==> ?p n. prime p /\ ~(n = 0) /\ CARD(ring_carrier k) = p EXP n`,
  SIMP_TAC[IMP_CONJ_ALT; FINITE_INTEGRAL_DOMAIN_EQ_FIELD] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `ring_char(k:A ring)` THEN
  MP_TAC(ISPEC `k:A ring` INTEGRAL_DOMAIN_CHAR) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_CHAR_FINITE] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `finite_extension (subring_generated k {ring_of_int k n | n IN (:int)},k)
                     (I:A->A)`
  MP_TAC THENL
   [ASM_SIMP_TAC[FINITE_EQ_FIELD_EXTENSION; FIELD_EXTENSION_FROM_PRIME_SUBRING];
    REWRITE_TAC[FINITE_EXTENSION_BASIS]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `b:A->bool` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] CARD_FINITE_EXTENSION)) THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; PRIME_SUBRING] THEN
  ASM_SIMP_TAC[FINITE_PRIME_SUBRING; CARD_PRIME_SUBRING; RING_CHAR_FINITE] THEN
  DISCH_TAC THEN EXISTS_TAC `CARD(b:A->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[EXP; TRIVIAL_RING_HAS_SIZE_1; HAS_SIZE;
                FIELD_IMP_NONTRIVIAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* Algebraic dependence and a corresponding notion of algebraic span,        *)
(* leading to basic results on transcendence bases and transcendence degree. *)
(*                                                                           *)
(* We special-case 0 in span to avoid excluding k's being the trivial ring.  *)
(* Because of the way polynomial rings are defined, all polynomials are      *)
(* considered zero over the trivial ring so the "non-trivial polynomial"     *)
(* part is degenerately false. For fields this is irrelevant, and there      *)
(* it is also equivalent to using "subfield_generated" instead.              *)
(* ------------------------------------------------------------------------- *)

let algebraically_dependent = new_definition
 `algebraically_dependent (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\
        ?p. p IN ring_carrier(poly_ring k s) /\
            ~(p = ring_0(poly_ring k s)) /\
            poly_extend(k,l) h (\x. x) p = ring_0 l`;;

let algebraically_independent = define
 `algebraically_independent (k,l) (h:A->B) s <=>
        s SUBSET ring_carrier l /\ ~(algebraically_dependent (k,l) h s)`;;

let algebraic_span = new_definition
 `algebraic_span (k,l) (h:A->B) s =
      ring_0 l INSERT
      {x | algebraic_over
            (subring_generated l (IMAGE h (ring_carrier k) UNION s),l) I x}`;;

let algebraically_spanning = define
 `algebraically_spanning (k,l) (h:A->B) s <=>
  s SUBSET ring_carrier l /\
  !y. y IN ring_carrier l
      ==> algebraic_over
           (subring_generated l (IMAGE h (ring_carrier k) UNION s),l) I y`;;

let transcendence_basis = define
 `transcendence_basis (k,l) (h:A->B) s <=>
        algebraically_spanning (k,l) h s /\
        algebraically_independent (k,l) h s`;;

let ALGEBRAICALLY_DEPENDENT_IMP_SUBSET = prove
 (`!(h:A->B) k l s.
        algebraically_dependent (k,l) h s ==> s SUBSET ring_carrier l`,
  SIMP_TAC[algebraically_dependent]);;

let ALGEBRAICALLY_INDEPENDENT_IMP_SUBSET = prove
 (`!(h:A->B) k l s.
        algebraically_independent (k,l) h s ==> s SUBSET ring_carrier l`,
  SIMP_TAC[algebraically_independent]);;

let TRANSCENDENCE_BASIS_IMP_SUBSET = prove
 (`!(h:A->B) k l s.
        transcendence_basis (k,l) h s ==> s SUBSET ring_carrier l`,
  SIMP_TAC[transcendence_basis; algebraically_independent]);;

let ALGEBRAICALLY_DEPENDENT_ALT = prove
 (`!(h:A->B) k l s.
        ring_monomorphism(k,l) h
        ==> (algebraically_dependent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             ?p. p IN ring_carrier(poly_ring k s) /\
                 ~(poly_deg k p = 0) /\
                 poly_extend(k,l) h (\x. x) p = ring_0 l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[algebraically_dependent] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[POLY_DEG_0; POLY_RING]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `p:(B->num)->A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_POLY_RING_CARRIER]) THEN
  ASM_SIMP_TAC[POLY_DEG_EQ_0] THEN
  MATCH_MP_TAC(TAUT `(r ==> ~q) ==> p ==> q ==> ~r`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[POLY_EXTEND_CONST; RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  REWRITE_TAC[POLY_RING; poly_0; POLY_CONST_EQ] THEN
  ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]);;

let ALGEBRAIC_SPAN = prove
 (`!(h:A->B) k l s.
    ~(trivial_ring l)
    ==> algebraic_span (k,l) h s =
         {x | algebraic_over
              (subring_generated l (IMAGE h (ring_carrier k) UNION s),l) I x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[algebraic_span] THEN
  REWRITE_TAC[SET_RULE `a INSERT s = s <=> a IN s`; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM I_THM] THEN
  MATCH_MP_TAC ALGEBRAIC_OVER_IMAGE_GEN THEN
  ASM_REWRITE_TAC[TRIVIAL_RING_SUBRING_GENERATED; CONJUNCT2 SUBRING_GENERATED;
          RING_0_IN_SUBRING_GENERATED; RING_HOMOMORPHISM_INCLUSION; I_DEF]);;

let ALGEBRAIC_SPAN_FIELD = prove
 (`!(h:A->B) k l s.
    field l
    ==> algebraic_span (k,l) h s =
         {x | algebraic_over
             (subfield_generated l (IMAGE h (ring_carrier k) UNION s),l) I x}`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ALGEBRAIC_SPAN; FIELD_IMP_NONTRIVIAL_RING] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:B` THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED THEN
  ASM_REWRITE_TAC[FIELD_EXTENSION_REFL]);;

let ALGEBRAIC_SPAN_RANGE = prove
 (`!(h:A->B) k l s.
        algebraic_span (k,l) h s =
        algebraic_span (subring_generated l (IMAGE h (ring_carrier k)),l) I s`,
  REWRITE_TAC[algebraic_span] THEN
  REWRITE_TAC[IMAGE_I; SUBRING_GENERATED_UNION_LEFT]);;

let ALGEBRAIC_SPAN_RESTRICT = prove
 (`!(h:A->B) k l s.
        algebraic_span (k,l) h s =
        algebraic_span (k,l) h (ring_carrier l INTER s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[algebraic_span] THEN
  ONCE_REWRITE_TAC[SUBRING_GENERATED_RESTRICT] THEN
  REWRITE_TAC[SET_RULE `s INTER (u UNION s INTER v) = s INTER (u UNION v)`]);;

let ALGEBRAIC_SPAN_SUBSET = prove
 (`!(h:A->B) k l s. algebraic_span (k,l) h s SUBSET ring_carrier l`,
  REWRITE_TAC[algebraic_span; INSERT_SUBSET; RING_0] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[ALGEBRAIC_OVER_IN_CARRIER]);;

let RING_SPAN_SUBSET_ALGEBRAIC_SPAN = prove
 (`!(h:A->B) k l s. ring_span (k,l) h s SUBSET algebraic_span (k,l) h s`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH lhand
    RING_SPAN_SUBSET_SUBRING_GENERATED o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  REWRITE_TAC[algebraic_span] THEN REWRITE_TAC[SUBSET; IN_INSERT] THEN
  X_GEN_TAC `x:B` THEN ASM_CASES_TAC `x:B = ring_0 l` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM I_THM] THEN
  MATCH_MP_TAC ALGEBRAIC_OVER_IMAGE_GEN THEN
  ASM_REWRITE_TAC[SUBRING_GENERATED] THEN
  REWRITE_TAC[I_DEF; RING_HOMOMORPHISM_INCLUSION]);;

let ALGEBRAIC_SPAN_SUPERSET = prove
 (`!(h:A->B) k l s.
        s SUBSET ring_carrier l ==> s SUBSET algebraic_span (k,l) h s`,
  MESON_TAC[RING_SPAN_SUPERSET; RING_SPAN_SUBSET_ALGEBRAIC_SPAN;
            SUBSET_TRANS]);;

let ALGEBRAIC_SPAN_MONO = prove
 (`!(h:A->B) k l s t.
    s SUBSET t ==> algebraic_span (k,l) h s SUBSET algebraic_span (k,l) h t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[algebraic_span] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> a INSERT s SUBSET a INSERT t`) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; algebraic_over;
              POLY_SUBRING_GENERATED_CLAUSES;
              POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
  X_GEN_TAC `y:B` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `p:(1->num)->B` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
  MATCH_MP_TAC RING_CARRIER_POLY_SUBRING_GENERATED_MONO THEN
  ASM SET_TAC[]);;

let ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h
        ==> algebraic_extension
             (k,subfield_generated l {x | algebraic_over (k,l) h x}) h`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[algebraic_extension] THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD;
               SUBFIELD_OF_ALGEBRAIC_OVER] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[SUBFIELD_OF_ALGEBRAIC_OVER; ALGEBRAIC_OVER_IMAGE_SUBSET];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[ALGEBRAIC_OVER_IMAGE_SUBSET; IN_ELIM_THM]]);;

let ALGEBRAIC_EXTENSION_SUBRING_GENERATED_ALGEBRAIC = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h
        ==> algebraic_extension
             (k,subring_generated l {x | algebraic_over (k,l) h x}) h`,
  MESON_TAC[SUBRING_SUBFIELD_ALGEBRAIC_OVER;
            ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC]);;

let ALGEBRAIC_SPAN_SPAN = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h
        ==> algebraic_span (k,l) h (algebraic_span (k,l) h s) =
            algebraic_span (k,l) h s`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [ALGEBRAIC_SPAN_RESTRICT] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ALGEBRAIC_SPAN_RESTRICT] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[ALGEBRAIC_SPAN_MONO; ALGEBRAIC_SPAN_SUPERSET; INTER_SUBSET] THEN
  MP_TAC(SET_RULE`(ring_carrier l INTER s:B->bool) SUBSET ring_carrier l`) THEN
  SPEC_TAC(`ring_carrier l INTER s:B->bool`,`s:B->bool`) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ALGEBRAIC_SPAN_FIELD] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`I:B->B`; `I:B->B`;
    `subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s)`;
    `subfield_generated l
       (IMAGE h (ring_carrier k) UNION
        {x | algebraic_over
               (subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s),
                l) I x})`;
  `l:B ring`; `x:B`] ALGEBRAIC_OVER_TRANS) THEN
  ASM_REWRITE_TAC[I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`I:B->B`;
      `subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s)`;
      `l:B ring`] ALGEBRAIC_EXTENSION_SUBFIELD_GENERATED_ALGEBRAIC) THEN
    ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[SET_RULE `s = t UNION s <=> t SUBSET s`] THEN
      MP_TAC(ISPECL
       [`I:B->B`;
        `subfield_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s)`;
        `l:B ring`] ALGEBRAIC_OVER_IMAGE_SUBSET) THEN
      ANTS_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[IMAGE_I] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
          SUBSET_TRANS) THEN
        W(MP_TAC o PART_MATCH (rand o rand)
          SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET o rand o snd) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[FIELD_EXTENSION_REFL] THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED]);;

let ALGEBRAIC_SPAN_FINITARY = prove
 (`!(h:A->B) k l s a.
        a IN algebraic_span (k,l) h s
        ==> ?t. FINITE t /\ t SUBSET s /\ a IN algebraic_span (k,l) h t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[algebraic_span; IN_INSERT] THEN
  ASM_CASES_TAC `a:B = ring_0 l` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[FINITE_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[algebraic_over; IN_ELIM_THM; POLY_SUBRING_GENERATED_CLAUSES] THEN
  REWRITE_TAC[POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:(1->num)->B` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_POLY_RING_SUBRING_GENERATED_FINITARY) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s INTER t:B->bool` THEN
  ASM_SIMP_TAC[FINITE_INTER; INTER_SUBSET] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s SUBSET t ==> x IN t`)) THEN
  MATCH_MP_TAC RING_CARRIER_POLY_SUBRING_GENERATED_MONO THEN
  ASM SET_TAC[]);;

let ALGEBRAIC_SPAN_EMPTY = prove
 (`!(h:A->B) k l.
     ring_monomorphism(k,l) h /\ ~trivial_ring l
     ==> algebraic_span (k,l) h {} = {x | algebraic_over (k,l) h x}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ALGEBRAIC_SPAN; UNION_EMPTY] THEN
  ASM_SIMP_TAC[GSYM ALGEBRAIC_OVER_RANGE]);;

let ALGEBRAICALLY_INDEPENDENT_EMPTY = prove
 (`!(h:A->B) k l.
    ring_monomorphism(k,l) h ==> algebraically_independent (k,l) h {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC
   [algebraically_independent; algebraically_dependent; EMPTY_SUBSET] THEN
  SUBGOAL_THEN
   `ring_epimorphism(k,poly_ring k {}) (poly_const k:A->(B->num)->A)`
  MP_TAC THENL
   [MESON_TAC[RING_ISOMORPHISM_POLY_RING_TRIVIAL;
              RING_ISOMORPHISM_IMP_EPIMORPHISM];
    REWRITE_TAC[ring_epimorphism]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[EMPTY_SUBSET; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[POLY_EXTEND_CONST; RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  REWRITE_TAC[POLY_RING; poly_0; POLY_CONST_EQ] THEN
  ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]);;

let ALGEBRAICALLY_DEPENDENT_SING = prove
 (`!(h:A->B) k l x.
        algebraically_dependent (k,l) h {x} <=>
        algebraic_over (k,l) h x`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`; `x:B`] ALGEBRAIC_OVER) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[algebraically_dependent; SING_SUBSET] THEN
  EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `p:(B->num)->A` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC POLY_EXTEND_EQ THEN EXISTS_TAC `{x:B}` THEN
  ASM_SIMP_TAC[IN_SING]);;

let ALGEBRAICALLY_INDEPENDENT_SING = prove
 (`!(h:A->B) k l x.
        algebraically_independent (k,l) h {x} <=>
        transcendental_over (k,l) h x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[algebraically_independent; transcendental_over;
              ALGEBRAICALLY_DEPENDENT_SING; SING_SUBSET]);;

let ALGEBRAICALLY_DEPENDENT_MONO = prove
 (`!(h:A->B) k l s t.
     algebraically_dependent (k,l) h s /\ s SUBSET t /\ t SUBSET ring_carrier l
     ==> algebraically_dependent (k,l) h t`,
  REWRITE_TAC[algebraically_dependent] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[CONJUNCT2 POLY_RING] THEN
  ASM_MESON_TAC[POLY_RING_MONO]);;

let ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO = prove
 (`!(h:A->B) k l s t d.
        algebraically_dependent (subring_generated k s,l) h d /\ s SUBSET t
        ==> algebraically_dependent (subring_generated k t,l) h d`,
  REWRITE_TAC[algebraically_dependent; POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
  REWRITE_TAC[POLY_SUBRING_GENERATED_CLAUSES] THEN
  MESON_TAC[RING_CARRIER_POLY_SUBRING_GENERATED_MONO; SUBSET]);;

let ALGEBRAICALLY_INDEPENDENT_MONO = prove
 (`!(h:A->B) k l s t.
        algebraically_independent (k,l) h t /\ s SUBSET t
        ==> algebraically_independent (k,l) h s`,
  REWRITE_TAC[algebraically_independent] THEN
  ASM_MESON_TAC[ALGEBRAICALLY_DEPENDENT_MONO; SUBSET_TRANS]);;

let ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO = prove
 (`!(h:A->B) k l s t d.
        algebraically_independent (subring_generated k t,l) h d /\ s SUBSET t
        ==> algebraically_independent (subring_generated k s,l) h d`,
  REWRITE_TAC[algebraically_independent] THEN
  MESON_TAC[ALGEBRAICALLY_DEPENDENT_OVER_SUBRING_GENERATED_MONO]);;

let ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL = prove
 (`!(h:A->B) k l s x.
        field_extension (k,l) h /\
        algebraically_independent (k,l) h s /\ x IN s
        ==> transcendental_over (k,l) h x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ALGEBRAICALLY_INDEPENDENT_SING] THEN
  MATCH_MP_TAC ALGEBRAICALLY_INDEPENDENT_MONO THEN
  ASM_MESON_TAC[SING_SUBSET]);;

let ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT = prove
 (`!(h:A->B) k l s.
        field_extension (k,l) h /\ algebraically_independent (k,l) h s
        ==> DISJOINT (IMAGE h (ring_carrier k)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE
   `DISJOINT (IMAGE f r) s <=> !a. a IN r ==> ~(f a IN s)`] THEN
  ASM_MESON_TAC[ALGEBRAIC_OVER_IMAGE; transcendental_over;
                ALGEBRAICALLY_INDEPENDENT_IMP_TRANSCENDENTAL]);;

let ALGEBRAICALLY_DEPENDENT_FINITARY = prove
 (`!(h:A->B) k l s.
        algebraically_dependent (k,l) h s <=>
        s SUBSET ring_carrier l /\
        ?t. FINITE t /\ t SUBSET s /\ algebraically_dependent (k,l) h t`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC [algebraically_dependent];
    MESON_TAC[ALGEBRAICALLY_DEPENDENT_MONO; algebraically_dependent]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `p:(B->num)->A` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP POLY_RING_IN_FINITE_VARIABLES) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:B->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `p:(B->num)->A`] THEN
  ASM_MESON_TAC[CONJUNCT2 POLY_RING]);;

let RING_MONOMORPHISM_POLY_EXTEND = prove
 (`!r r' s (h:A->B).
        ring_homomorphism(r,r') h /\ s SUBSET ring_carrier r'
        ==> (ring_monomorphism (poly_ring r s,r')
                               (poly_extend(r,r') h (\x. x)) <=>
             algebraically_independent (r,r') h s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[algebraically_independent] THEN
  ASM_REWRITE_TAC[RING_MONOMORPHISM_ALT; algebraically_dependent] THEN
  MATCH_MP_TAC(TAUT `p /\ (q <=> q') ==> (p /\ q <=> q')`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN ASM SET_TAC[]);;

let ALGEBRAICALLY_DEPENDENT_FROM_INSERT = prove
 (`!(h:A->B) k l s a.
        field_extension(k,l) h /\ ~algebraically_dependent (k,l) h s
        ==> (algebraically_dependent (k,l) h (a INSERT s) <=>
             ~(a IN s) /\ s SUBSET ring_carrier l /\
             a IN algebraic_span (k,l) h s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_CASES_TAC `(s:B->bool) SUBSET ring_carrier l` THEN
  ASM_REWRITE_TAC[] THENL
    [ALL_TAC; ASM_MESON_TAC[algebraically_dependent; INSERT_SUBSET]] THEN
  ASM_CASES_TAC `(a:B) IN ring_carrier l` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[algebraically_dependent; INSERT_SUBSET] THEN
    ASM SET_TAC[ALGEBRAIC_SPAN_SUBSET]] THEN
  ASM_CASES_TAC `(a:B) IN s` THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> a INSERT s = s`] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `s:B->bool`;
                 `h:A->B`] RING_MONOMORPHISM_POLY_EXTEND) THEN
  ASM_REWRITE_TAC[algebraically_independent] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`poly_extend (k,l) (h:A->B) (\x. x)`;
                 `poly_ring (k:A ring) (s:B->bool)`; `l:B ring`;
                 `a:B`; `a:B`] ALGEBRAIC_OVER) THEN
  MATCH_MP_TAC(TAUT
   `(p' <=> p) /\ (q <=> q') ==> (q <=> p) ==> (p' <=> q')`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`h:A->B`; `k:A ring`; `l:B ring`;  `s:B->bool`; `{a:B}`;
      `\x:B. x`] POLY_EXTEND_EXTEND) THEN
    MP_TAC(ISPECL [`k:A ring`; `s:B->bool`; `{a:B}`]
      RING_ISOMORPHISMS_POLY_POLY_RING) THEN
    ASM_REWRITE_TAC[SET_RULE `DISJOINT s {a} <=> ~(a IN s)`] THEN
    REWRITE_TAC[SET_RULE `s UNION {a} = a INSERT s`] THEN
    W(fun (asl,w) ->
        let ft,gt = dest_pair(rand(lhand w)) in
        ABBREV_TAC(mk_eq(mk_var("f",type_of ft),ft)) THEN
        ABBREV_TAC(mk_eq(mk_var("g",type_of gt),gt))) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    DISCH_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[algebraically_dependent; INSERT_SUBSET] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `p:(B->num)->A` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:(B->num)->A`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC
       `(g:((B->num)->A)->(B->num)->(B->num)->A) p` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(ASSUME_TAC o el 1 o
        CONJUNCTS o GEN_REWRITE_RULE I [RING_ISOMORPHISMS_ISOMORPHISM]) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
      REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_MONOMORPHISM) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        RING_MONOMORPHISM_EQ_0)) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC);
      DISCH_THEN(X_CHOOSE_THEN `p:(B->num)->(B->num)->A` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
       `(!x. P x) ==> (?x. P x ==> Q x) ==> (?x. Q x)`)) THEN
      EXISTS_TAC `(f:((B->num)->(B->num)->A)->(B->num)->A) p` THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_isomorphisms]) THEN
      REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC POLY_EXTEND_EQ THEN EXISTS_TAC `{a:B}` THEN
    ASM_SIMP_TAC[IN_SING];
    ASM_SIMP_TAC[ALGEBRAIC_SPAN; FIELD_IMP_NONTRIVIAL_RING; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`; `\x:B. x`]
          IMAGE_POLY_EXTEND) THEN
    REWRITE_TAC[SET_RULE `IMAGE (\x. x) s UNION t = t UNION s`] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `subring_generated (l:B ring)`) THEN
    REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
    REWRITE_TAC[POLY_SUBRING_GENERATED_CLAUSES] THEN
    REWRITE_TAC[GSYM poly_evaluate; GSYM poly_eval] THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_RANGE THEN ASM_REWRITE_TAC[]]);;

let ALGEBRAICALLY_DEPENDENT_INSERT = prove
 (`!(h:A->B) k l s a.
        field_extension(k,l) h
        ==> (algebraically_dependent (k,l) h (a INSERT s) <=>
             a IN ring_carrier l /\ algebraically_dependent (k,l) h s \/
             ~(a IN s) /\ s SUBSET ring_carrier l /\
             a IN algebraic_span (k,l) h s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `algebraically_dependent (k,l) (h:A->B) s` THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_DEPENDENT_FROM_INSERT] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_DEPENDENT_IMP_SUBSET) THEN
  ASM_CASES_TAC `(a:B) IN ring_carrier l` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC ALGEBRAICALLY_DEPENDENT_MONO THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[algebraically_dependent; INSERT_SUBSET] THEN
    ASM_CASES_TAC `(a:B) IN s` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[ALGEBRAIC_SPAN_SUBSET]]);;

let ALGEBRAICALLY_INDEPENDENT_INSERT = prove
 (`!(h:A->B) k l s a.
        field_extension(k,l) h
        ==> (algebraically_independent (k,l) h (a INSERT s) <=>
             algebraically_independent (k,l) h s /\
             a IN ring_carrier l /\
             (a IN s \/ ~(a IN algebraic_span (k,l) h s)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[algebraically_independent; ALGEBRAICALLY_DEPENDENT_INSERT] THEN
  ASM SET_TAC[ALGEBRAICALLY_DEPENDENT_IMP_SUBSET; ALGEBRAIC_SPAN_SUBSET]);;

let ALGEBRAICALLY_DEPENDENT_SPAN = prove
 (`!k l (h:A->B) s.
        field_extension(k,l) h
        ==> (algebraically_dependent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             ?a. a IN s /\ a IN algebraic_span (k,l) h (s DELETE a))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[HAS_SIZE]
   `((!s. FINITE s ==> P s) ==> (!s. P s)) /\
    (!n s. s HAS_SIZE n ==> P s)
    ==> !s. P s`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
        [ALGEBRAICALLY_DEPENDENT_FINITARY]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:B->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:B` THEN
      ASM_MESON_TAC[ALGEBRAIC_SPAN_MONO; SUBSET; IN_DELETE];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP ALGEBRAIC_SPAN_FINITARY) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC ALGEBRAICALLY_DEPENDENT_MONO THEN
      EXISTS_TAC `(a:B) INSERT t` THEN CONJ_TAC THENL
       [ALL_TAC; ASM SET_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(a:B) INSERT t`) THEN
      ASM_REWRITE_TAC[FINITE_INSERT] THEN DISCH_THEN SUBST1_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `a:B`] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
       `t SUBSET s DELETE a ==> (a INSERT t) DELETE a = t`)) THEN
      ASM_REWRITE_TAC[IN_INSERT]];
    MATCH_MP_TAC num_WF] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:B->bool` THEN REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_CASES_TAC `(s:B->bool) SUBSET ring_carrier l` THEN ASM_REWRITE_TAC[]
  THENL [ALL_TAC; ASM_REWRITE_TAC[algebraically_dependent]] THEN
  ASM_CASES_TAC
   `?t. t PSUBSET s /\ algebraically_dependent (k,l) (h:A->B) t`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> (p <=> q)`) THEN
    CONJ_TAC THENL [ASM SET_TAC[ALGEBRAICALLY_DEPENDENT_MONO]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `CARD(t:B->bool)`) THEN
    ASM_SIMP_TAC[CARD_PSUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `t:B->bool`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[HAS_SIZE; PSUBSET; FINITE_SUBSET];
      ASM_REWRITE_TAC[]] THEN
     DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
     MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:B` THEN
     ASM_MESON_TAC[ALGEBRAIC_SPAN_MONO; PSUBSET; SUBSET; IN_DELETE];
     FIRST_X_ASSUM(K ALL_TAC o SPEC `0`)] THEN
  EQ_TAC THENL
   [ASM_CASES_TAC `s:B->bool = {}` THEN
    ASM_SIMP_TAC[REWRITE_RULE[algebraically_independent; EMPTY_SUBSET]
                  ALGEBRAICALLY_INDEPENDENT_EMPTY] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:B` THEN DISCH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s DELETE (a:B)`; `a:B`]
        ALGEBRAICALLY_DEPENDENT_FROM_INSERT) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:B)` o
    GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> a INSERT (s DELETE a) = s`] THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> s DELETE a PSUBSET s`; IN_DELETE] THEN
  ASM SET_TAC[]);;

let ALGEBRAICALLY_INDEPENDENT_SPAN = prove
 (`!k l (h:A->B) s.
        field_extension(k,l) h
        ==> (algebraically_independent (k,l) h s <=>
             s SUBSET ring_carrier l /\
             !a. a IN s ==> ~(a IN algebraic_span (k,l) h (s DELETE a)))`,
  SIMP_TAC[algebraically_independent; ALGEBRAICALLY_DEPENDENT_SPAN] THEN
  SET_TAC[]);;

let ALGEBRAIC_SPAN_EXCHANGE = prove
 (`!(h:A->B) k l s a b.
        field_extension(k,l) h /\
        a IN algebraic_span (k,l) h (b INSERT s) /\
        ~(a IN algebraic_span (k,l) h s)
        ==> b IN algebraic_span (k,l) h (a INSERT s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ALGEBRAIC_SPAN_RESTRICT] THEN
  ASM_CASES_TAC `(b:B) IN ring_carrier l` THENL
   [ALL_TAC;
    ASM_MESON_TAC[SET_RULE
     `~(b IN s) ==> s INTER (b INSERT t) = s INTER t`]] THEN
  ASM_CASES_TAC `(a:B) IN ring_carrier l` THENL
   [ASM_SIMP_TAC[SET_RULE
     `b IN s ==> s INTER (b INSERT t) = b INSERT (s INTER t)`];
    ASM_MESON_TAC[ALGEBRAIC_SPAN_SUBSET; SUBSET]] THEN
  MP_TAC(SET_RULE
   `ring_carrier l INTER (s:B->bool) SUBSET ring_carrier l`) THEN
  SPEC_TAC(`ring_carrier l INTER (s:B->bool)`,`s:B->bool`) THEN
  X_GEN_TAC `s:B->bool` THEN
  ASM_CASES_TAC `a:B = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(a:B) IN s` THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
        ALGEBRAIC_SPAN_SUPERSET) THEN
    ASM SET_TAC[];
    REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN
   `?n t. t HAS_SIZE n /\ t SUBSET s /\
          a IN algebraic_span (k,l) (h:A->B) (b INSERT t)`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP ALGEBRAIC_SPAN_FINITARY) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`CARD(t DELETE (b:B))`; `t DELETE (b:B)`] THEN
    ASM_REWRITE_TAC[GSYM FINITE_HAS_SIZE; FINITE_DELETE] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                   `t:B->bool`; `(b:B) INSERT (t DELETE b)`]
        ALGEBRAIC_SPAN_MONO) THEN
    ASM SET_TAC[];
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; NOT_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] HAS_SIZE; GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_UNWIND_THM1] THEN
  X_GEN_TAC `t:B->bool` THEN REPLICATE_TAC 3 DISCH_TAC THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[TAUT `p ==> ~(q /\ r) <=> q ==> p ==> ~r`] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  REWRITE_TAC[FORALL_UNWIND_THM1] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:B->bool) SUBSET ring_carrier l` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~algebraically_dependent (k,l) (h:A->B) t` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ALGEBRAICALLY_DEPENDENT_SPAN] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t DELETE (c:B)`) THEN
    ASM_SIMP_TAC[CARD_PSUBSET; FINITE_DELETE; NOT_IMP;
                 SET_RULE `s DELETE a PSUBSET s <=> a IN s`] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC
     [GSYM(MATCH_MP ALGEBRAIC_SPAN_SPAN th)]) THEN
    UNDISCH_TAC `a IN algebraic_span (k,l) (h:A->B) (b INSERT t)` THEN
    SPEC_TAC(`a:B`,`a:B`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC ALGEBRAIC_SPAN_MONO THEN
    TRANS_TAC SUBSET_TRANS `c INSERT (b INSERT (t DELETE c)):B->bool` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ONCE_REWRITE_TAC[INSERT_SUBSET]] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `c IN algebraic_span (k,l) (h:A->B) (t DELETE c)` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
      MATCH_MP_TAC ALGEBRAIC_SPAN_MONO THEN ASM SET_TAC[];
      MATCH_MP_TAC ALGEBRAIC_SPAN_SUPERSET THEN ASM SET_TAC[]];
    FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))] THEN
  MATCH_MP_TAC(SET_RULE `!t. t SUBSET s /\ x IN t ==> x IN s`) THEN
  EXISTS_TAC `algebraic_span (k,l) (h:A->B) (a INSERT t)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALGEBRAIC_SPAN_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `(a:B) INSERT t`; `b:B`]
        ALGEBRAICALLY_DEPENDENT_FROM_INSERT) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `t:B->bool`; `a:B`]
        ALGEBRAICALLY_DEPENDENT_FROM_INSERT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (TAUT
   `(p <=> q /\ r) ==> ~r ==> ~p`)) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `t:B->bool`; `s:B->bool`]
        ALGEBRAIC_SPAN_MONO) THEN
    ASM SET_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_DEPENDENT_SPAN; INSERT_SUBSET] THEN
  EXISTS_TAC `a:B` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `(b:B) INSERT t`;
                 `(b INSERT a INSERT t) DELETE (a:B)`]
        ALGEBRAIC_SPAN_MONO) THEN
  ASM SET_TAC[]);;

let ALGEBRAICALLY_SPANNING = prove
 (`!(h:A->B) k l s.
        field_extension (k,l) h
        ==> (algebraically_spanning (k,l) (h:A->B) s <=>
             s SUBSET ring_carrier l /\
             algebraic_extension
              (subfield_generated l (IMAGE h (ring_carrier k) UNION s),l) I)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  REWRITE_TAC[algebraically_spanning; algebraic_extension] THEN
  ASM_SIMP_TAC[ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED;
                FIELD_EXTENSION_REFL] THEN
  MATCH_MP_TAC(TAUT `q ==> (p /\ r <=> p /\ q /\ r)`) THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  ASM_REWRITE_TAC[FIELD_EXTENSION_SUBRING_GENERATED] THEN
  REWRITE_TAC[subfield_of; SUBRING_SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED]);;

let algebraic_matroid = new_definition
 `algebraic_matroid (k,l) (h:A->B) =
     matroid(ring_carrier l,algebraic_span (k,l) h)`;;

let ALGEBRAIC_MATROID = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> matroid_set(algebraic_matroid (k,l) h) = ring_carrier l /\
            matroid_span(algebraic_matroid (k,l) h) = algebraic_span (k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[matroid_set; matroid_span] THEN
  REWRITE_TAC[GSYM PAIR_EQ; algebraic_matroid] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 matroid_tybij)] THEN
  ASM_SIMP_TAC[ALGEBRAIC_SPAN_SUBSET; ALGEBRAIC_SPAN_SUPERSET;
               ALGEBRAIC_SPAN_MONO; ALGEBRAIC_SPAN_SPAN;
               ALGEBRAIC_SPAN_FINITARY; ALGEBRAIC_SPAN_EXCHANGE]);;

let ALGEBRAIC_MATROID_INDEPENDENT = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> (matroid_independent(algebraic_matroid (k,l) h) =
             algebraically_independent (k,l) h)`,
  SIMP_TAC[FUN_EQ_THM; matroid_independent; ALGEBRAIC_MATROID] THEN
  SIMP_TAC[ALGEBRAICALLY_DEPENDENT_SPAN; algebraically_independent] THEN
  MESON_TAC[]);;

let ALGEBRAIC_MATROID_DEPENDENT = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> (matroid_dependent(algebraic_matroid (k,l) h) =
             algebraically_dependent (k,l) h)`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[matroid_dependent; algebraically_independent;
            ALGEBRAIC_MATROID_INDEPENDENT; ALGEBRAIC_MATROID;
            ALGEBRAICALLY_DEPENDENT_IMP_SUBSET]);;

let ALGEBRAIC_MATROID_SPANNING = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> (matroid_spanning(algebraic_matroid (k,l) h) =
             algebraically_spanning (k,l) h)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATROID_SPANNING_ALT; ALGEBRAIC_MATROID; FUN_EQ_THM] THEN
  REWRITE_TAC[algebraically_spanning; SUBSET] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  ASM_SIMP_TAC[ALGEBRAIC_SPAN; FIELD_IMP_NONTRIVIAL_RING] THEN
  SET_TAC[]);;

let ALGEBRAIC_MATROID_BASIS = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> (matroid_basis(algebraic_matroid (k,l) h) =
             transcendence_basis (k,l) h)`,
  SIMP_TAC[FUN_EQ_THM; matroid_basis; transcendence_basis;
           ALGEBRAIC_MATROID_INDEPENDENT; ALGEBRAIC_MATROID_SPANNING]);;

let TRANSCENDENCE_BASIS_EXISTS = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h ==> ?b. transcendence_basis (k,l) h b`,
  SIMP_TAC[GSYM ALGEBRAIC_MATROID_BASIS; MATROID_BASIS_EXISTS]);;

let ALGEBRAICALLY_SPANNING_CONTAINS_TRANSCENDENCE_BASIS = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h /\ algebraically_spanning (k,l) h b
        ==> ?c. c SUBSET b /\ transcendence_basis (k,l) h c`,
  MESON_TAC[MATROID_SPANNING_CONTAINS_BASIS; ALGEBRAIC_MATROID_SPANNING;
            ALGEBRAIC_MATROID_BASIS]);;

let TRANSCENDENCE_BASES_CARD_EQ = prove
 (`!(h:A->B) k l b b'.
        field_extension (k,l) h /\
        transcendence_basis (k,l) h b /\ transcendence_basis (k,l) h b'
        ==> b =_c b'`,
  MESON_TAC[ALGEBRAIC_MATROID_BASIS; MATROID_BASES_CARD_EQ]);;

let ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m s.
        s SUBSET ring_carrier l /\
        ring_homomorphism(k,l) f /\
        ring_monomorphism(l,m) g
        ==> (algebraically_dependent (k,m) (g o f) (IMAGE g s) <=>
             algebraically_dependent (k,l) f s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[ring_monomorphism]) THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `h:C->B`) THEN
  MP_TAC(ISPECL [`k:A ring`; `s:B->bool`; `IMAGE (g:B->C) s`;
                 `g:B->C`; `h:C->B`]
        RING_ISOMORPHISMS_POLY_REINDEX) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  REWRITE_TAC[algebraically_dependent] THEN
  SUBGOAL_THEN `IMAGE (g:B->C) s SUBSET ring_carrier m` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `BIJ (g:B->C) s (IMAGE g s) /\ BIJ (h:C->B) (IMAGE g s) s`
  STRIP_ASSUME_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(ASSUME_TAC o
    GEN_REWRITE_RULE I [RING_ISOMORPHISMS_ISOMORPHISM]) THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `p:(C->num)->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `poly_reindex (k:A ring) p (g:B->C) (s:B->bool)
                             (IMAGE (g:B->C) s)` THEN
    FIRST_X_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2);

    DISCH_THEN(X_CHOOSE_THEN `q:(B->num)->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `poly_reindex (k:A ring) q (h:C->B)
                             (IMAGE (g:B->C) s) (s:B->bool)` THEN
    FIRST_X_ASSUM(ASSUME_TAC o CONJUNCT1)] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_ISOMORPHISM_IMP_MONOMORPHISM) THEN
  (MATCH_MP_TAC(TAUT `p /\ q /\ (p ==> r) ==> p /\ q /\ r`) THEN
   REPEAT CONJ_TAC THENL
    [FIRST_ASSUM(MP_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
     REWRITE_TAC[ring_homomorphism] THEN ASM SET_TAC[];
     ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0];
     ALL_TAC]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_POLY_RING_CARRIER])
  THENL
   [MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`; `s:B->bool`;
                   `IMAGE (g:B->C) s`; `p:(C->num)->A`; `g:B->C`; `\x:C. x`]
     POLY_EXTEND_REINDEX) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `q = poly_reindex (k:A ring) (p:(C->num)->A) (g:B->C) (s:B->bool)
          (IMAGE (g:B->C) s)`;
    MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`;
                   `IMAGE (g:B->C) s`; `s:B->bool`; `q:(B->num)->A`;
                   `h:C->B`; `g:B->C`]
        POLY_EXTEND_REINDEX) THEN
     ASM_REWRITE_TAC[] THEN
     ABBREV_TAC
      `p = poly_reindex (k:A ring) (q:(B->num)->A) (h:C->B) (IMAGE g s) s`] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:C ring`;
                 `f:A->B`; `s:B->bool`; `\x:B. x`; `g:B->C`;
                 `q:(B->num)->A`]
    POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[o_DEF; IMAGE_ID; RING_MONOMORPHISM_IMP_HOMOMORPHISM] THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; POLY_EXTEND]; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(g:B->C) (ring_0 l) = ring_0 m` SUBST1_TAC THENL
   [ASM_MESON_TAC[ring_monomorphism; ring_homomorphism];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC POLY_EXTEND_EQ THEN
  EXISTS_TAC `IMAGE (g:B->C) s` THEN ASM SET_TAC[]);;

let ALGEBRAIC_OVER_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m z.
        z IN ring_carrier l /\
        ring_homomorphism(k,l) f /\
        ring_monomorphism(l,m) g
        ==> (algebraic_over (k,m) (g o f) (g z) <=>
             algebraic_over (k,l) f z)`,
  REWRITE_TAC[GSYM ALGEBRAICALLY_DEPENDENT_SING; GSYM SING_SUBSET] THEN
  MESON_TAC[ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE; IMAGE_CLAUSES]);;

let ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m s.
        ring_homomorphism(k,l) f /\
        ring_monomorphism(l,m) g /\
        s SUBSET ring_carrier l
        ==> IMAGE g (algebraic_span (k,l) f s) =
            IMAGE g (ring_carrier l) INTER
            algebraic_span (k,m) (g o f) (IMAGE g s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN u ==> (g x IN v <=> x IN s)) /\ s SUBSET u
    ==> IMAGE g s = IMAGE g u INTER v`) THEN
  REWRITE_TAC[ALGEBRAIC_SPAN_SUBSET] THEN
  X_GEN_TAC `z:B` THEN DISCH_TAC THEN
  REWRITE_TAC[algebraic_span] THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN BINOP_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`I:B->B`; `g:B->C`;
    `subring_generated l (IMAGE (f:A->B) (ring_carrier k) UNION s)`;
    `l:B ring`; `m:C ring`; `z:B`]
   ALGEBRAIC_OVER_MONOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[REWRITE_RULE[GSYM I_DEF] RING_HOMOMORPHISM_INCLUSION] THEN
  ASM_REWRITE_TAC[I_O_ID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[ALGEBRAIC_OVER_RANGE;
               RING_MONOMORPHISM_FROM_SUBRING_GENERATED] THEN
  MP_TAC(ISPECL
   [`l:B ring`; `m:C ring`; `g:B->C`;
    `IMAGE (f:A->B) (ring_carrier k) UNION s`]
        SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; UNION_SUBSET] THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  REWRITE_TAC[IMAGE_o; IMAGE_UNION]);;

let ALGEBRAICALLY_INDEPENDENT_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m s t.
        field_extension(k,l) f /\ field_extension(l,m) g /\
        algebraically_independent (k,l) f s /\
        algebraically_independent (l,m) g t
        ==> DISJOINT (IMAGE g s) t /\
            algebraically_independent (k,m) (g o f) (IMAGE g s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[algebraically_independent] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[UNION_SUBSET; CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:B->C`; `l:B ring`; `m:C ring`; `t:C->bool`]
        ALGEBRAICALLY_INDEPENDENT_IMP_DISJOINT) THEN
    ASM_REWRITE_TAC[algebraically_independent] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
    ASM SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
        FIELD_EXTENSION_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM ALGEBRAIC_MATROID_DEPENDENT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MATROID_MINIMALLY_DEPENDENT_SUBSET) THEN
  ASM_SIMP_TAC[ALGEBRAIC_MATROID_DEPENDENT] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[EXISTS_SUBSET_UNION; FINITE_UNION] THEN
  ONCE_REWRITE_TAC[TAUT
   `p /\ q /\ (r /\ s) /\ t <=> r /\ p /\ s /\ q /\ t`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s':B->bool`; `t':C->bool`] THEN
  ASM_CASES_TAC `t':C->bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_UNION; IMAGE_EQ_EMPTY; UNION_EMPTY] THEN
  REWRITE_TAC[NOT_IN_EMPTY; EMPTY_SUBSET; FINITE_EMPTY] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL
     [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`; `s:B->bool`]
     ALGEBRAICALLY_DEPENDENT_MONOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_MONOMORPHISM;
                 FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    ASM_MESON_TAC[IMAGE_SUBSET; ALGEBRAICALLY_DEPENDENT_MONO];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `c:C`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:C`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ALGEBRAIC_MATROID] THEN DISCH_TAC THEN
    UNDISCH_TAC `~algebraically_dependent (l,m) (g:B->C) t` THEN
    ASM_SIMP_TAC[ALGEBRAICALLY_DEPENDENT_SPAN] THEN
    EXISTS_TAC `c:C` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [algebraic_span]) THEN
    REWRITE_TAC[algebraic_span; IN_INSERT; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
      ALGEBRAIC_OVER_SUBRING_GENERATED_MONO) THEN
    REWRITE_TAC[IMAGE_o] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
    ASM SET_TAC[]]);;

let ALGEBRAICALLY_SPANNING_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m s t.
      field_extension (k,l) f /\ algebraically_spanning (k,l) f s /\
      field_extension (l,m) g /\ algebraically_spanning (l,m) g t
      ==> algebraically_spanning (k,m) (g o f) (IMAGE g s UNION t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `field_extension (k,m) ((g:B->C) o (f:A->B))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_TRANS]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM ALGEBRAIC_MATROID_SPANNING; MATROID_SPANNING_ALT] THEN
  MAP_EVERY UNDISCH_TAC
   [`algebraically_spanning (l,m) (g:B->C) t`;
    `algebraically_spanning (k,l) (f:A->B) s`] THEN
  ASM_SIMP_TAC[GSYM ALGEBRAIC_MATROID_SPANNING; matroid_spanning] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MATROID_SPAN_UNION_LEFT o
    funpow 4 rand o snd) THEN
  ASM_SIMP_TAC[ALGEBRAIC_MATROID; UNION_SUBSET] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
  SUBGOAL_THEN `IMAGE (g:B->C) s SUBSET ring_carrier m` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
    ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  TRANS_TAC SUBSET_TRANS
   `algebraic_span (k,m) (g o f)
     (IMAGE (g:B->C) (algebraic_span (k,l) (f:A->B) s) UNION t)` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    ONCE_REWRITE_TAC[ALGEBRAIC_SPAN_RANGE] THEN
    REWRITE_TAC[algebraic_span] THEN
    MATCH_MP_TAC(SET_RULE `s = t ==> a INSERT s SUBSET a INSERT t`) THEN
    REWRITE_TAC[IMAGE_I; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `z:C` THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[SUBRING_GENERATED_UNION_LEFT] THEN AP_TERM_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    MATCH_MP_TAC ALGEBRAIC_SPAN_MONO THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET s' ==> s UNION t SUBSET s' UNION t`) THEN
    ASM_SIMP_TAC[ALGEBRAIC_SPAN_MONOMORPHIC_IMAGE; INTER_SUBSET;
                 FIELD_EXTENSION_IMP_MONOMORPHISM;
                 RING_MONOMORPHISM_IMP_HOMOMORPHISM]]);;

let TRANSCENDENCE_BASIS_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m s t.
      field_extension (k,l) f /\ transcendence_basis (k,l) f s /\
      field_extension (l,m) g /\ transcendence_basis (l,m) g t
      ==> DISJOINT (IMAGE g s) t /\
          transcendence_basis (k,m) (g o f) (IMAGE g s UNION t)`,
  REWRITE_TAC[transcendence_basis] THEN
  MESON_TAC[ALGEBRAICALLY_INDEPENDENT_TRANS; ALGEBRAICALLY_SPANNING_TRANS]);;

let TRANSCENDENCE_BASIS_TOWER_LAW = prove
 (`!(f:A->B) (g:B->C) k l m b c d.
     field_extension (k,l) f /\ field_extension (l,m) g /\
     transcendence_basis (k,l) f b /\
     transcendence_basis (l,m) g c /\
     transcendence_basis (k,m) (g o f) d
     ==> b +_c c =_c d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`;
    `IMAGE (g:B->C) b UNION c`; `d:C->bool`]
   TRANSCENDENCE_BASES_CARD_EQ) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_TRANS; TRANSCENDENCE_BASIS_TRANS];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CARD_EQ_TRANS)] THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  TRANS_TAC CARD_EQ_TRANS `IMAGE (g:B->C) b +_c (c:C->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_DISJOINT_UNION THEN
    ASM_MESON_TAC[TRANSCENDENCE_BASIS_TRANS; DISJOINT];
    MATCH_MP_TAC CARD_ADD_CONG THEN REWRITE_TAC[CARD_EQ_REFL] THEN
    MATCH_MP_TAC CARD_EQ_IMAGE] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP TRANSCENDENCE_BASIS_IMP_SUBSET)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP
    FIELD_EXTENSION_IMP_MONOMORPHISM)) THEN
  REWRITE_TAC[ring_monomorphism] THEN ASM SET_TAC[]);;

let TRANSCENDENCE_BASIS_CARD_LE_LEFT = prove
 (`!(f:A->B) (g:B->C) k l m b c.
     field_extension (k,l) f /\ field_extension (l,m) g /\
     transcendence_basis (k,l) f b /\
     transcendence_basis (k,m) (g o f) c
     ==> b <=_c c`,
  ASM_MESON_TAC[TRANSCENDENCE_BASIS_EXISTS; TRANSCENDENCE_BASIS_TOWER_LAW;
                CARD_LE_ADDR; CARD_LE_ADDL; CARD_LE_TRANS; CARD_EQ_IMP_LE]);;

let TRANSCENDENCE_BASIS_CARD_LE_RIGHT = prove
 (`!(f:A->B) (g:B->C) k l m b c.
     field_extension (k,l) f /\ field_extension (l,m) g /\
     transcendence_basis (l,m) g b /\
     transcendence_basis (k,m) (g o f) c
     ==> b <=_c c`,
  ASM_MESON_TAC[TRANSCENDENCE_BASIS_EXISTS; TRANSCENDENCE_BASIS_TOWER_LAW;
                CARD_LE_ADDR; CARD_LE_ADDL; CARD_LE_TRANS; CARD_EQ_IMP_LE]);;

let ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED = prove
 (`!(f:A->B) (g:B->C) k l m s.
      algebraic_extension (k,l) f /\
      field_extension (l,m) g /\
      s SUBSET ring_carrier m
      ==> algebraic_extension
           (subfield_generated m (IMAGE (g o f) (ring_carrier k) UNION s),
            subfield_generated m (IMAGE g (ring_carrier l) UNION s)) I`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `field k /\ ring_monomorphism(k,l) (f:A->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension; field_extension]; ALL_TAC] THEN
  REWRITE_TAC[algebraic_extension] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[field_extension; FIELD_SUBFIELD_GENERATED] THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC RING_MONOMORPHISM_BETWEEN_SUBRINGS THEN
    REWRITE_TAC[IMAGE_I; RING_MONOMORPHISM_I; IMAGE_o] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[];
    DISCH_TAC THEN REWRITE_TAC[SET_RULE
     `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`]] THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET];
    MATCH_MP_TAC SUBFIELD_OF_SUBFIELD_GENERATED_REV THEN
    EXISTS_TAC `IMAGE (g:B->C) (ring_carrier l) UNION s` THEN
    MATCH_MP_TAC SUBFIELD_OF_ALGEBRAIC_OVER THEN ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `b:B` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED THEN
    REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED; IMAGE_I] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[field_extension; FIELD_SUBFIELD_GENERATED] THEN
      ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
      REWRITE_TAC[I_DEF; RING_MONOMORPHISM_INCLUSION];
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN REWRITE_TAC[IMAGE_o] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
      ASM SET_TAC[];
      ALL_TAC;
      MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
      ASM SET_TAC[]] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[algebraic_extension]) THEN
    DISCH_THEN(MP_TAC o SPEC `b:B`) THEN
    ASM_SIMP_TAC[ALGEBRAIC_OVER_RANGE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`I:B->B`; `g:B->C`;
      `subring_generated l (IMAGE (f:A->B) (ring_carrier k))`;
      `l:B ring`; `m:C ring`; `b:B`]
        ALGEBRAIC_OVER_MONOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[REWRITE_RULE[GSYM I_DEF] RING_HOMOMORPHISM_INCLUSION] THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_FROM_SUBRING_GENERATED;
                 ALGEBRAIC_OVER_RANGE; I_O_ID] THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
      ALGEBRAIC_OVER_SUBRING_GENERATED_MONO) THEN
    MP_TAC(ISPECL
     [`l:B ring`; `m:C ring`; `g:B->C`;
      `IMAGE (f:A->B) (ring_carrier k)`]
        SUBRING_GENERATED_BY_HOMOMORPHIC_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
      ASM SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    W(MP_TAC o PART_MATCH rand SUBRING_SUBSET_SUBFIELD_GENERATED o
      rand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
    MATCH_MP_TAC SUBRING_GENERATED_MONO THEN
    REWRITE_TAC[IMAGE_o] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM I_THM] THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN
    REWRITE_TAC[IMAGE_o] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[]]);;

let ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION = prove
 (`!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> algebraic_span (k,m) (g o f) s = algebraic_span (l,m) g s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ALGEBRAIC_SPAN_RESTRICT] THEN
  MP_TAC(SET_RULE
   `(ring_carrier m INTER s:C->bool) SUBSET ring_carrier m`) THEN
  SPEC_TAC(`ring_carrier m INTER s:C->bool`,`s:C->bool`) THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  ASM_SIMP_TAC[ALGEBRAIC_SPAN_FIELD] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:C` THEN
  MP_TAC(ISPECL
   [`I:C->C`; `I:C->C`;
    `subfield_generated m
       (IMAGE ((g:B->C) o (f:A->B)) (ring_carrier k) UNION s)`;
    `subfield_generated m (IMAGE (g:B->C) (ring_carrier l) UNION s)`;
    `m:C ring`; `z:C`] ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION) THEN
  REWRITE_TAC[I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ALGEBRAIC_EXTENSION_SUBFIELDS_GENERATED] THEN
  ASM_SIMP_TAC[field_extension; FIELD_SUBFIELD_GENERATED] THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_FROM_SUBRING_GENERATED;
               RING_MONOMORPHISM_I]);;

let ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION = prove
 (`!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (algebraically_dependent (k,m) (g o f) s <=>
             algebraically_dependent (l,m) g s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
        FIELD_EXTENSION_TRANS) THEN
  ASM_SIMP_TAC[ALGEBRAIC_IMP_FIELD_EXTENSION; ALGEBRAICALLY_DEPENDENT_SPAN;
               ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION]);;

let ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION = prove
 (`!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (algebraically_independent (k,m) (g o f) s <=>
             algebraically_independent (l,m) g s)`,
  SIMP_TAC[algebraically_independent;
           ALGEBRAICALLY_DEPENDENT_OVER_ALGEBRAIC_EXTENSION]);;

let ALGEBRAICALLY_SPANNING_SPAN = prove
 (`!(h:A->B) k l s.
        ~(trivial_ring l)
        ==> (algebraically_spanning (k,l) h s <=>
             s SUBSET ring_carrier l /\
             algebraic_span (k,l) h s = ring_carrier l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; ALGEBRAIC_SPAN_SUBSET] THEN
  ASM_SIMP_TAC[algebraically_spanning; ALGEBRAIC_SPAN] THEN SET_TAC[]);;

let ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION = prove
 (`!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (algebraically_spanning (k,m) (g o f) s <=>
             algebraically_spanning (l,m) g s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_SPANNING_SPAN; FIELD_IMP_NONTRIVIAL_RING;
               ALGEBRAIC_SPAN_OVER_ALGEBRAIC_EXTENSION]);;

let TRANSCENDENCE_BASIS_OVER_ALGEBRAIC_EXTENSION = prove
 (`!(f:A->B) (g:B->C) k l m s.
        algebraic_extension (k,l) f /\
        field_extension (l,m) g
        ==> (transcendence_basis (k,m) (g o f) s <=>
             transcendence_basis (l,m) g s)`,
  SIMP_TAC[transcendence_basis;
           ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION;
           ALGEBRAICALLY_SPANNING_OVER_ALGEBRAIC_EXTENSION]);;

let ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING = prove
 (`!(h:A->B) k l b c.
        field_extension (k,l) h /\
        algebraically_independent (k,l) h b /\ algebraically_spanning (k,l) h c
        ==> b <=_c c`,
  REWRITE_TAC[IMP_CONJ] THEN
  SIMP_TAC[GSYM ALGEBRAIC_MATROID_INDEPENDENT;
           GSYM ALGEBRAIC_MATROID_SPANNING] THEN
  MESON_TAC[MATROID_INDEPENDENT_CARD_LE_SPANNING]);;

let FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE = prove
 (`!(f:A->B) k l b.
        finitely_generated_extension (k,l) f /\
        algebraically_independent (k,l) f b
        ==> FINITE b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[finitely_generated_extension] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:B->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CARD_LE_FINITE)) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        ALGEBRAICALLY_INDEPENDENT_CARD_LE_SPANNING)) THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_SPANNING; ALGEBRAIC_EXTENSION_REFL] THEN
  ASM_MESON_TAC[field_extension]);;

let TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING = prove
 (`!(h:A->B) k l s.
        transcendence_basis (k,l) h s ==> algebraically_spanning (k,l) h s`,
  SIMP_TAC[transcendence_basis]);;

let TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT = prove
 (`!(h:A->B) k l s.
        transcendence_basis (k,l) h s ==> algebraically_independent (k,l) h s`,
  SIMP_TAC[transcendence_basis]);;

let TOTALLY_TRANSCENDENTAL_EXTENSION = prove
 (`!(f:A->B) k l b x.
        field_extension (k,l) f /\
        algebraically_independent (k,l) f b /\
        algebraic_over (k,l) f x /\
        x IN ring_carrier
              (subfield_generated l (IMAGE f (ring_carrier k) UNION b))
        ==> x IN IMAGE f (ring_carrier k)`,
  let baselemma = prove
   (`!k l a z:A.
          field l /\ k subfield_of l /\
          transcendental_over (subfield_generated l k,l) I a /\
          algebraic_over (subfield_generated l k,l) I z /\
          z IN ring_carrier(subfield_generated l (a INSERT k))
          ==> z IN k`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:A ring`; `a INSERT k:A->bool`; `z:A`]
          SUBFIELD_GENERATED_QUOTIENTS) THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; LEFT_IMP_EXISTS_THM] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TRANSCENDENTAL_OVER_IN_CARRIER) THEN
    ASM_SIMP_TAC[GSYM IMAGE_POLY_EVAL; SUBFIELD_IMP_SUBRING_OF] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `p:(1->num)->A` THEN STRIP_TAC THEN
    X_GEN_TAC `q:(1->num)->A` THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
    ASM_CASES_TAC `(z:A) IN k` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`I:A->A`; `I:A->A`;
      `subfield_generated l k:A ring`; `subfield_generated l ((z:A) INSERT k)`;
      `l:A ring`; `a:A`]
     ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION) THEN
    REWRITE_TAC[I_O_ID; NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[algebraic_extension] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[field_extension; FIELD_SUBFIELD_GENERATED] THEN
        ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        MATCH_MP_TAC RING_MONOMORPHISM_BETWEEN_SUBRINGS THEN
        REWRITE_TAC[IMAGE_I; RING_MONOMORPHISM_I] THEN
        MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC[];
        DISCH_THEN(MP_TAC o SPEC `{z:A}` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC)) THEN
        ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IMAGE_I] THEN
        ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
        REWRITE_TAC[SET_RULE `s UNION {a} = a INSERT s`;
                    SUBFIELD_GENERATED_IDEMPOT] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC ALGEBRAIC_OVER_SUBFIELD_GENERATED THEN
        ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
        ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        ASM_REWRITE_TAC[FIELD_EXTENSION_SUBRING_GENERATED] THEN
        ASM_SIMP_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED;
                     CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
        SET_TAC[]];
      ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
      ASM_REWRITE_TAC[FIELD_EXTENSION_SUBRING_GENERATED] THEN
      ASM_SIMP_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED;
                   SUBFIELD_SUBFIELD_GENERATED];
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [transcendental_over]) THEN
      SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC)] THEN
    ASM_SIMP_TAC[ALGEBRAIC_OVER_SUBFIELD_SUBRING_GENERATED;
                 FIELD_EXTENSION_REFL] THEN
    ASM_REWRITE_TAC[algebraic_over] THEN
    EXISTS_TAC
     `ring_sub (poly_ring (subring_generated l (z INSERT k)) (:1)) p
               (ring_mul ((poly_ring (subring_generated l (z INSERT k)) (:1)))
                         (poly_const (subring_generated l (z INSERT k)) (z:A))
                         q)` THEN
    MP_TAC(ISPECL [`l:A ring`; `k:A->bool`; `(z:A) INSERT k`; `(:1)`]
          RING_CARRIER_POLY_SUBRING_GENERATED_MONO) THEN
    ANTS_TAC THENL [SET_TAC[]; GEN_REWRITE_TAC LAND_CONV [SUBSET]] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `q:(1->num)->A` th) THEN MP_TAC(SPEC `p:(1->num)->A` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subring_generated l (z INSERT k):A ring`; `(:1)`; `z:A`]
          POLY_CONST) THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN ANTS_TAC THENL
     [MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
      ASM SET_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET];
      DISCH_TAC] THEN
    ASM_SIMP_TAC[RING_SUB; RING_MUL; RING_0; RING_SUB_EQ_0] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MP_TAC(ISPECL [`subring_generated l (z INSERT k):A ring`; `l:A ring`;
                     `(:1)`; `I:A->A`; `(\v. a):1->A`]
          RING_HOMOMORPHISM_POLY_EXTEND) THEN
      ASM_REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] RING_HOMOMORPHISM_INCLUSION] THEN
      DISCH_TAC THEN
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUB th; RING_MUL]) THEN
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
      REWRITE_TAC[POLY_EXTEND_FROM_SUBRING_GENERATED] THEN
      REWRITE_TAC[GSYM poly_evaluate; GSYM poly_eval] THEN
      REWRITE_TAC[POLY_SUBRING_GENERATED_CLAUSES] THEN
      ASM_SIMP_TAC[POLY_CONST_SUBRING_GENERATED; POLY_EVAL_CONST] THEN
      EXPAND_TAC "z" THEN
      UNDISCH_TAC `~(poly_eval l (q:(1->num)->A) a = ring_0 l)` THEN
      MP_TAC(ISPECL [`l:A ring`; `q:(1->num)->A`; `a:A`] POLY_EVAL) THEN
      MP_TAC(ISPECL [`l:A ring`; `p:(1->num)->A`; `a:A`] POLY_EVAL) THEN
      FIELD_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM
     `\p. p IN ring_carrier
             (poly_ring (subring_generated l k:A ring) (:1))`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLY_RING; IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_polynomial]) THEN
    REWRITE_TAC[ring_powerseries; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `~(z:A = ring_0 l)`
      (fun th -> ASSUME_TAC th THEN MP_TAC th) THENL
      [ASM_MESON_TAC[IN_SUBFIELD_0]; EXPAND_TAC "z"] THEN
    ASM_CASES_TAC `q:(1->num)->A = poly_0 l` THENL
     [REWRITE_TAC[ring_div] THEN ASM_SIMP_TAC[POLY_EVAL_0] THEN
      ASM_SIMP_TAC[RING_MUL_RZERO; RING_INV_0; POLY_EVAL];
      DISCH_THEN(K ALL_TAC) THEN POP_ASSUM MP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [FUN_EQ_THM] THEN
    REWRITE_TAC[POLY_0; NOT_FORALL_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:1->num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`subring_generated l (z INSERT k):A ring`;
      `z:A`; `q:(1->num)->A`] POLY_MUL_CONST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_INSERT];
        RULE_ASSUM_TAC(REWRITE_RULE[POLY_RING; IN_ELIM_THM]) THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[CONJUNCT2 SUBRING_GENERATED; CARRIER_SUBRING_GENERATED_SUBRING;
                 SUBFIELD_IMP_SUBRING_OF] THEN
    UNDISCH_TAC `~((z:A) IN k)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(q:(1->num)->A) m IN k /\ q m IN ring_carrier l`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC
       `q IN ring_carrier (poly_ring (subring_generated l k:A ring) (:1))` THEN
      REWRITE_TAC[POLY_RING; IN_ELIM_THM;
                  ring_polynomial; ring_powerseries] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[subfield_of]) THEN
      ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[subring_of]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `z:A = ring_mul l (ring_inv l (q m)) (ring_mul l z (q(m:1->num)))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~((q:(1->num)->A) m = ring_0 l)` THEN
      UNDISCH_TAC `(q:(1->num)->A) m IN ring_carrier l` THEN
      UNDISCH_TAC `(z:A) IN ring_carrier l` THEN
      UNDISCH_TAC `field(l:A ring)` THEN
      SPEC_TAC(`(q:(1->num)->A) m`,`qm:A`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN FIELD_TAC;
      MATCH_MP_TAC IN_SUBFIELD_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IN_SUBFIELD_INV THEN ASM_REWRITE_TAC[]]) in
  MATCH_MP_TAC(MESON[]
   `(!f k l x. (!b. FINITE b ==> P f k l b x) ==> !b. P f k l b x) /\
    (!b. FINITE b ==> !f k l x. P f k l b x)
     ==> !f k l b x. P f k l b x`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `IMAGE (f:A->B) (ring_carrier k) UNION b`;
                   `x:B`] IN_SUBFIELD_GENERATED_FINITARY) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[field_extension; FIELD_SUBFIELD_GENERATED];
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`]] THEN
    REWRITE_TAC[EXISTS_SUBSET_UNION; FINITE_UNION] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:B->bool`; `c:B->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:B->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ALGEBRAICALLY_INDEPENDENT_MONO]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s SUBSET t ==> x IN t`)) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC(SET_RULE `s = t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[UNION_EMPTY] THEN
    MATCH_MP_TAC CARRIER_SUBFIELD_GENERATED_SUBFIELD THEN
    MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
    ASM_MESON_TAC[CARRIER_SUBFIELD_OF; field_extension];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:B`; `b:B->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`f:A->B`; `k:A ring`; `l:B ring`; `y:B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_INDEPENDENT_INSERT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `l:B ring` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL
   [`ring_carrier (subfield_generated l
       (IMAGE (f:A->B) (ring_carrier k) UNION b))`;
    `l:B ring`; `a:B`; `y:B`] baselemma) THEN
  ASM_REWRITE_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED];
    UNDISCH_TAC `~(a IN algebraic_span (k,l) (f:A->B) b)` THEN
    ASM_SIMP_TAC[ALGEBRAIC_SPAN_FIELD; transcendental_over; IN_ELIM_THM;
                 SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED];
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED_MONO THEN
    EXISTS_TAC `IMAGE (f:A->B) (ring_carrier k)` THEN
    ASM_SIMP_TAC[GSYM ALGEBRAIC_OVER_RANGE] THEN
    REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[];
    ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
    REWRITE_TAC[SUBFIELD_GENERATED_UNION_RIGHT] THEN
    ASM_REWRITE_TAC[SET_RULE `{a} UNION s UNION b = s UNION a INSERT b`]]);;

let TOTALLY_TRANSCENDENTAL_EXTENSION_ALT = prove
 (`!(f:A->B) k l b.
        field_extension (k,l) f /\
        algebraically_independent (k,l) f b /\
        subfield_generated l (IMAGE f (ring_carrier k) UNION b) = l
        ==> {x | algebraic_over (k,l) f x} = IMAGE f (ring_carrier k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[ALGEBRAIC_OVER_IMAGE]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TOTALLY_TRANSCENDENTAL_EXTENSION THEN
  MAP_EVERY EXISTS_TAC [`l:B ring`; `b:B->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ALGEBRAIC_OVER_IN_CARRIER]);;

(* ------------------------------------------------------------------------- *)
(* A loose end about finitely generated extensions that seems to involve a   *)
(* bit more work than expected. This proof is mainly taken from that of      *)
(* theorem 24.9 in Isaacs: "Algebra: A Graduate Course".                     *)
(* ------------------------------------------------------------------------- *)

let FINITELY_GENERATED_EXTENSION_TRANS_EQ = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g
        ==> (finitely_generated_extension (k,m) (g o f) <=>
             finitely_generated_extension (k,l) f /\
             finitely_generated_extension (l,m) g)`,
  let choice_lemma = prove
   (`!P (s:A->bool).
          (!t. FINITE t /\ t SUBSET s ==> ?y. y IN s /\ P y t)
          ==> ?f. (!n. f n IN s) /\ (!n. P (f n) {f i | i < n})`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?f:num->A. !n. f n = @y. y IN s /\ P y {f i | i < n}`
    MP_TAC THENL
     [MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[AND_FORALL_THM] THEN
      GEN_TAC THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN MATCH_MP_TAC num_WF THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `{(f:num->A) i | i < n}`) THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
                   FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
      DISCH_THEN(MP_TAC o SELECT_RULE) THEN
      ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE_GEN]]) in
  let main_lemma = prove
   (`!(f:A->B) (g:B->C) k l m.
          algebraic_extension (k,l) f /\
          field_extension (l,m) g /\
          finitely_generated_extension (k,m) (g o f)
          ==> finitely_generated_extension (k,l) f`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP TRANSCENDENCE_BASIS_EXISTS o
          MATCH_MP FINITELY_GENERATED_IMP_FIELD_EXTENSION) THEN
    DISCH_THEN(X_CHOOSE_TAC `b:C->bool`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TRANSCENDENCE_BASIS_IMP_SUBSET) THEN
    MP_TAC(ISPECL
     [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`; `b:C->bool`]
     ALGEBRAICALLY_INDEPENDENT_OVER_ALGEBRAIC_EXTENSION) THEN
    ASM_SIMP_TAC[TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    SUBGOAL_THEN `field(k:A ring) /\ field(l:B ring) /\ field(m:C ring)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FINITELY_GENERATED_EXTENSION] THEN REWRITE_TAC[MESON[]
     `(?b. P b /\ Q b /\ R b) <=> ~(!b. P b /\ Q b ==> ~R b)`] THEN
    REWRITE_TAC[SET_RULE `~(s SUBSET t) <=> ?x. x IN s /\ ~(x IN t)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP choice_lemma) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num->B` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `A n = ring_carrier
              (subfield_generated l
              (IMAGE (f:A->B) (ring_carrier k) UNION {y i | i < n}))` THEN
    SUBGOAL_THEN
     `(!n. A n subfield_of (l:B ring)) /\
      (!n. IMAGE (f:A->B) (ring_carrier k) SUBSET A n) /\
      (!m n. m < n ==> A m PSUBSET A n)`
    MP_TAC THEN POP_ASSUM MP_TAC THENL
     [DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th] THEN ASSUME_TAC th) THEN
      REWRITE_TAC[SUBFIELD_SUBFIELD_GENERATED_EQ] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FIELD_SUBFIELD_GENERATED]; ALL_TAC] THEN
      CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
      REWRITE_TAC[PSUBSET_TRANS] THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[PSUBSET_ALT] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
        REWRITE_TAC[LT] THEN SET_TAC[];
        EXISTS_TAC `(y:num->B) n` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN; ASM_REWRITE_TAC[]] THEN
        ASM_REWRITE_TAC[LT] THEN SET_TAC[]];
      DISCH_THEN(K ALL_TAC) THEN STRIP_TAC] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `y:num->B`) o concl)) THEN
    ABBREV_TAC
     `B = \n:num. ring_carrier(subfield_generated m
                   (IMAGE (g:B->C) (A n) UNION b))` THEN
    SUBGOAL_THEN `!n. (B:num->C->bool) n subfield_of m` ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED];
      ALL_TAC] THEN
    SUBGOAL_THEN `!m n. m < n ==> (B:num->C->bool) m PSUBSET B n`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `!n:num. {x | algebraic_over (k,subfield_generated m (B n))
                                    ((g:B->C) o (f:A->B)) x} =
                IMAGE g (A n)`
      ASSUME_TAC THENL
       [ALL_TAC;
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
        ASM_REWRITE_TAC[PSUBSET] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
         [EXPAND_TAC "B" THEN REWRITE_TAC[] THEN DISCH_TAC THEN
          MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN ASM SET_TAC[];
          REWRITE_TAC[CONTRAPOS_THM]] THEN
        DISCH_TAC THEN FIRST_X_ASSUM(fun th ->
          MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [field_extension; ring_monomorphism; ring_homomorphism;
          subfield_of; subring_of]) THEN
        ASM SET_TAC[]] THEN
      X_GEN_TAC `n:num` THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN CONJ_TAC THENL
       [ALL_TAC;
        X_GEN_TAC `x:B` THEN DISCH_TAC THEN
        ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED THEN
        ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
        REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[FIELD_EXTENSION_TRANS];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
          REPEAT STRIP_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
          MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN;
          MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                         `x:B`] ALGEBRAIC_OVER_MONOMORPHIC_IMAGE) THEN
          ASM_SIMP_TAC[FIELD_EXTENSION_IMP_MONOMORPHISM;
                       RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
          SUBGOAL_THEN `(x:B) IN ring_carrier l` ASSUME_TAC THENL
           [RULE_ASSUM_TAC(REWRITE_RULE[subfield_of; subring_of]) THEN
            ASM SET_TAC[];
            ASM_MESON_TAC[algebraic_extension]];
          EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
          MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN] THEN
        RULE_ASSUM_TAC(REWRITE_RULE
         [field_extension; ring_monomorphism; ring_homomorphism;
          subfield_of; subring_of]) THEN
        ASM SET_TAC[]] THEN
      X_GEN_TAC `y:C` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g:B->C`; `subfield_generated l ((A:num->B->bool) n)`;
                     `m:C ring`; `b:C->bool`; `y:C`]
        TOTALLY_TRANSCENDENTAL_EXTENSION) THEN
      ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
      SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
        ASM_REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED];
        ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        MATCH_MP_TAC ALGEBRAICALLY_INDEPENDENT_OVER_SUBRING_GENERATED_MONO THEN
        EXISTS_TAC `ring_carrier l:B->bool` THEN
        ASM_REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
        ASM_REWRITE_TAC[SUBRING_GENERATED_RING_CARRIER];
        MATCH_MP_TAC ALGEBRAIC_FROM_SUBRING_GENERATED THEN
        EXISTS_TAC
         `ring_carrier (subfield_generated m ((B:num->C->bool) n))` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
          ASM_SIMP_TAC[field_extension; FIELD_SUBFIELD_GENERATED] THEN
          ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
          MATCH_MP_TAC RING_MONOMORPHISM_BETWEEN_SUBRINGS THEN
          ASM_SIMP_TAC[FIELD_EXTENSION_IMP_MONOMORPHISM] THEN
          ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
          EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
          RULE_ASSUM_TAC(REWRITE_RULE
           [field_extension; ring_monomorphism; ring_homomorphism;
            subfield_of; subring_of]) THEN
          ASM SET_TAC[];
          ASM_SIMP_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED;
                       CARRIER_SUBFIELD_GENERATED_SUBFIELD]] THEN
        MP_TAC(ISPECL
         [`f:A->B`; `g:B->C`; `k:A ring`;
          `subfield_generated l ((A:num->B->bool) n)`;
          `subfield_generated m ((B:num->C->bool) n)`]
         ALGEBRAIC_OVER_FROM_MONOMORPHIC_IMAGE) THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN
          ASM_SIMP_TAC[FIELD_EXTENSION_IMP_MONOMORPHISM] THEN
          ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
          MATCH_MP_TAC RING_HOMOMORPHISM_BETWEEN_SUBRINGS THEN
          ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
          ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
          EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
          RULE_ASSUM_TAC(REWRITE_RULE
           [field_extension; ring_monomorphism; ring_homomorphism;
            subfield_of; subring_of]) THEN
          ASM SET_TAC[]];
        FIRST_X_ASSUM(MP_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
        ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `finite_extension
        (subfield_generated m
           (IMAGE ((g:B->C) o (f:A->B)) (ring_carrier k) UNION b),m) I`
    MP_TAC THENL
     [REWRITE_TAC[FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP
        TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_SPANNING) THEN
      ASM_SIMP_TAC[ALGEBRAICALLY_SPANNING;
                   FINITELY_GENERATED_IMP_FIELD_EXTENSION] THEN
      DISCH_THEN(K ALL_TAC) THEN
      ASM_REWRITE_TAC[FINITELY_GENERATED_EXTENSION] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        ASM_REWRITE_TAC[FIELD_EXTENSION_SUBRING_GENERATED] THEN
        REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
        ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
        [FINITELY_GENERATED_EXTENSION]) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:C->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN REWRITE_TAC[IMAGE_o] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET s' ==> s UNION t SUBSET s' UNION t`) THEN
      REWRITE_TAC[SUBSET; IMAGE_I] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [field_extension; ring_monomorphism; ring_homomorphism;
        subfield_of; subring_of]) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FINITE_EXTENSION_RING_MATROID] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!n. ?y:C. y IN ring_carrier m /\ ~(y IN B n) /\ y IN B(SUC n)`
    MP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[subfield_of; subring_of; PSUBSET_ALT]) THEN
      ASM_MESON_TAC[SUBSET; ARITH_RULE `n < SUC n`];
      REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:num->C` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `!i j. (y:num->C) i IN B j <=> i < j` ASSUME_TAC THENL
     [ASM SET_TAC[NOT_LE; LE_SUC_LT; LT_CASES]; ALL_TAC] THEN
    SUBGOAL_THEN `!i j. (y:num->C) i = y j <=> i = j` ASSUME_TAC THENL
     [MATCH_MP_TAC WLOG_LT THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `IMAGE (y:num->C) (:num)` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] MATROID_DIMENSION_GE_FINITE_CARD)) THEN
    ASM_SIMP_TAC[FINITE_IMAGE_INJ_EQ] THEN
    REWRITE_TAC[REWRITE_RULE[INFINITE] num_INFINITE] THEN
    ASM_SIMP_TAC[RING_MATROID_INDEPENDENT; FIELD_SUBFIELD_GENERATED] THEN
    ONCE_REWRITE_TAC[MATROID_INDEPENDENT_FINITARY] THEN
    ASM_SIMP_TAC[RING_MATROID; FIELD_SUBFIELD_GENERATED;
                 FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE; SUBSET_UNIV] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `d:num->bool` THEN REWRITE_TAC[FINITE_SUBSET_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_TAC `nn:num`) THEN
    MATCH_MP_TAC MATROID_INDEPENDENT_MONO THEN
    EXISTS_TAC `IMAGE (y:num->C) {i | i < SUC nn}` THEN
    CONJ_TAC THENL
     [SPEC_TAC(`SUC nn`,`n:num`);
      MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
      REWRITE_TAC[IN_NUMSEG; IN_ELIM_THM; SUBSET] THEN ARITH_TAC] THEN
    ASM_SIMP_TAC[RING_MATROID_INDEPENDENT; FIELD_SUBFIELD_GENERATED;
                 FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[NUMSEG_CLAUSES_LT; IMAGE_CLAUSES; RING_INDEPENDENT_EMPTY] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_INDEPENDENT_INSERT o snd) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED;
                   FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
       RING_SPAN_SUBSET_SUBFIELD_GENERATED)) THEN
    REWRITE_TAC[IMAGE_I] THEN
    DISCH_THEN(MP_TAC o SPEC `(B:num->C->bool) n` o MATCH_MP (SET_RULE
     `x IN s ==> !t. s SUBSET t ==> x IN t`)) THEN
    ASM_REWRITE_TAC[NOT_LT] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET; IMAGE_o] THEN
    REWRITE_TAC[SUBSET; IMAGE_I] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [field_extension; ring_monomorphism; ring_homomorphism;
      subfield_of; subring_of]) THEN
    ASM SET_TAC[]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[FINITELY_GENERATED_EXTENSION_TRANS] THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
   [DISCH_TAC;
    ASM_REWRITE_TAC[FINITELY_GENERATED_EXTENSION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:C->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN REWRITE_TAC[IMAGE_o] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
    ASM SET_TAC[]] THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`]
        TRANSCENDENCE_BASIS_EXISTS) THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`]
        TRANSCENDENCE_BASIS_EXISTS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `b:B->bool` THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_MESON_TAC[FIELD_EXTENSION_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:C->bool`) THEN
  SUBGOAL_THEN `FINITE(b:B->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITELY_GENERATED_ALGEBRAICALLY_INDEPENDENT_IMP_FINITE;
                  TRANSCENDENCE_BASIS_IMP_ALGEBRAICALLY_INDEPENDENT;
                  TRANSCENDENCE_BASIS_CARD_LE_LEFT; CARD_LE_FINITE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:A->B`; `I:B->B`; `k:A ring`;
    `subfield_generated l (IMAGE (f:A->B) (ring_carrier k) UNION b)`;
    `l:B ring`] FINITELY_GENERATED_EXTENSION_TRANS) THEN
  REWRITE_TAC[I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[FINITELY_GENERATED_EXTENSION] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
      MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBFIELD_SUBFIELD_GENERATED; field_extension];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o
          MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
        ASM SET_TAC[]];
      EXISTS_TAC `b:B->bool` THEN
      ASM_REWRITE_TAC[SUBFIELD_GENERATED_IDEMPOT; SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC[IN_UNION] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o
        MATCH_MP TRANSCENDENCE_BASIS_IMP_SUBSET)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [field_extension; ring_monomorphism; ring_homomorphism]) THEN
      ASM SET_TAC[]];
      ALL_TAC] THEN
  MP_TAC(ISPECL
   [`I:B->B`; `g:B->C`;
    `subfield_generated l (IMAGE (f:A->B) (ring_carrier k) UNION b)`;
    `l:B ring`; `m:C ring`] main_lemma) THEN
  ASM_REWRITE_TAC[I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[ALGEBRAICALLY_SPANNING; transcendence_basis]; ALL_TAC] THEN
  REWRITE_TAC[FINITELY_GENERATED_EXTENSION] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
    ASM_REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    ASM_MESON_TAC[FIELD_SUBFIELD_GENERATED; field_extension];
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [finitely_generated_extension])] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:C->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET t ==> IMAGE g s UNION u SUBSET IMAGE g t UNION u`) THEN
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_REWRITE_TAC[IN_UNION] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    MATCH_MP TRANSCENDENCE_BASIS_IMP_SUBSET)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [field_extension; ring_monomorphism; ring_homomorphism]) THEN
  ASM SET_TAC[]);;
