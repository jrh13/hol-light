(* ========================================================================= *)
(* Basic field theory, in particular some properties of field extensions.    *)
(* ========================================================================= *)

needs "Library/matroids.ml";;
needs "Library/ringtheory.ml";;
needs "Library/ring_det.ml";;

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

let SUBFIELD_OF_UNIONS_DIRECTED = prove
 (`!r u:(A->bool)->bool.
        field r /\ ~(u = {}) /\ (!e. e IN u ==> e subfield_of r) /\
        (!e1 e2. e1 IN u /\ e2 IN u
                 ==> ?e. e IN u /\ e1 SUBSET e /\ e2 SUBSET e)
        ==> UNIONS u subfield_of r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "sf") (LABEL_TAC "dir")))) THEN
  SUBGOAL_THEN
   `!e. e IN u
        ==> e SUBSET ring_carrier r /\ ring_0 r IN e /\ ring_1 r IN e /\
            (!x:A. x IN e ==> ring_neg r x IN e /\ ring_inv r x IN e) /\
            (!x y. x IN e /\ y IN e
                   ==> ring_add r x y IN e /\ ring_mul r x y IN e)`
  (LABEL_TAC "cl") THENL
   [GEN_TAC THEN DISCH_THEN(fun th -> USE_THEN "sf" (MP_TAC o C MATCH_MP th))
    THEN DISCH_TAC THEN ASM_SIMP_TAC[IN_SUBFIELD_INV] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP SUBFIELD_IMP_SUBRING_OF) THEN
    SIMP_TAC[subring_of];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:A. x IN UNIONS u /\ y IN UNIONS u
            ==> ?e. e IN u /\ x IN e /\ y IN e`
  (LABEL_TAC "two") THENL
   [REWRITE_TAC[IN_UNIONS] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e1:A->bool`)
                               (X_CHOOSE_TAC `e2:A->bool`)) THEN
    USE_THEN "dir" (MP_TAC o SPECL [`e1:A->bool`; `e2:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e:A->bool. e IN u` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN ASM_REWRITE_TAC[subring_of] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "two" (MP_TAC o SPECL [`x:A`; `x:A`]) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN DISCH_TAC THEN
    USE_THEN "two" (MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN DISCH_TAC THEN
    USE_THEN "two" (MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "two" (MP_TAC o SPECL [`x:A`; `x:A`]) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]]);;

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

let SUBFIELD_OF_COMMON_FIXPOINTS = prove
 (`!k (G:(A->A)->bool).
        field k /\ (!f. f IN G ==> ring_endomorphism k f)
        ==> {x | x IN ring_carrier k /\ !f. f IN G ==> f x = x} subfield_of k`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `G:(A->A)->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; SET_RULE `{x:A | x IN s} = s`;
                  CARRIER_SUBFIELD_OF] THEN
  MP_TAC(ISPECL [`k:A ring`;
     `{{x | x IN ring_carrier k /\ (f:A->A) x = x} | f IN G}`]
     SUBFIELD_OF_INTERS) THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC; SUBFIELD_OF_FIXPOINTS; SIMPLE_IMAGE;
               IMAGE_EQ_EMPTY] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[INTERS_IMAGE; EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

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

let SUBFIELD_GENERATED_IDEMPOT_GEN = prove
 (`!r s t:A->bool.
        s SUBSET ring_carrier(subfield_generated r t)
        ==> subfield_generated (subfield_generated r t) s =
            subfield_generated r s`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `?h:A->bool. h subfield_of r /\ ring_carrier r INTER t SUBSET h`
  THENL [ALL_TAC; ASM_SIMP_TAC[SUBFIELD_GENERATED_TRIVIAL]] THEN
  FIRST_X_ASSUM(ASSUME_TAC o
    GEN_REWRITE_RULE I [GSYM SUBFIELD_SUBFIELD_GENERATED_ALT]) THEN
  SUBGOAL_THEN `(s:A->bool) SUBSET ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS; RING_CARRIER_SUBFIELD_GENERATED_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_carrier(subfield_generated r (s:A->bool)) subfield_of r`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBFIELD_SUBFIELD_GENERATED_ALT] THEN
    EXISTS_TAC `ring_carrier(subfield_generated r (t:A->bool))` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ring_carrier(subfield_generated r (s:A->bool)) INTER
                ring_carrier(subfield_generated r t)` THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
    ASM_SIMP_TAC[SUBFIELD_OF_SUBFIELD_GENERATED_EQ; SUBFIELD_OF_INTER;
                 INTER_SUBSET; SUBSET_INTER;
                 SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET];
    MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
    ASM_SIMP_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET] THEN
    MATCH_MP_TAC SUBFIELD_OF_SUBFIELD_GENERATED_REV THEN
    EXISTS_TAC `t:A->bool` THEN
    REWRITE_TAC[SUBFIELD_SUBFIELD_GENERATED_ALT] THEN
    EXISTS_TAC `ring_carrier(subfield_generated r (t:A->bool))` THEN
    ASM_REWRITE_TAC[SUBFIELD_OF_SUBFIELD_GENERATED_EQ; SUBSET_REFL;
                    INTER_SUBSET]]);;

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

let SUBFIELD_GENERATED_INSERT = prove
 (`!r (a:A) s:A->bool.
        subfield_generated r (a INSERT ring_carrier(subfield_generated r s)) =
        subfield_generated r (a INSERT s)`,
  ONCE_REWRITE_TAC[SET_RULE `(a:A) INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[SUBFIELD_GENERATED_UNION_RIGHT]);;

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

let RING_ORDER_SUBFIELD_GENERATED = prove
 (`!r s x:A.
        x IN ring_carrier(subfield_generated r s)
        ==> ring_order (subfield_generated r s) x = ring_order r x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_ORDER_UNIQUE th]) THEN
  REWRITE_TAC[RING_POW_SUBFIELD_GENERATED;
              el 2 (CONJUNCTS SUBFIELD_GENERATED)] THEN
  GEN_TAC THEN MATCH_MP_TAC RING_POW_EQ_1 THEN
  ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET]);;

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

let RING_OF_INT_IN_SUBFIELD_GENERATED = prove
 (`!r s:A->bool n. ring_of_int r n IN ring_carrier(subfield_generated r s)`,
  MESON_TAC[RING_OF_INT; RING_OF_INT_SUBFIELD_GENERATED]);;

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

let RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED = prove
 (`!(f:A->B) g k l s.
        field k /\ ring_homomorphism (k,l) f /\ ring_homomorphism (k,l) g /\
        (!x. x IN ring_carrier k /\ x IN s ==> f x = g x)
        ==> !x. x IN ring_carrier(subfield_generated k s) ==> f x = g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `g:A->B`] FIELD_HOMOMORPHISM_INV) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `f:A->B`] FIELD_HOMOMORPHISM_INV) THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INDUCT THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED]);;

let RING_HOMOMORPHISM_SUBFIELD_INCLUSION = prove
 (`!r s:A->bool. ring_homomorphism(subfield_generated r s,r) I`,
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[I_DEF; RING_HOMOMORPHISM_INCLUSION]);;

let RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED = prove
 (`!(f:A->B) r r' s.
        ring_homomorphism (r,r') f
        ==> ring_homomorphism(subfield_generated r s,r') f`,
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_FROM_SUBRING_GENERATED]);;

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

let POLY_DEG_SUBFIELD_GENERATED = prove
 (`!r s (p:(V->num)->A).
        poly_deg (subfield_generated r s) p = poly_deg r p`,
  REWRITE_TAC[poly_deg; CONJUNCT2 SUBFIELD_GENERATED]);;

let POLY_EVAL_SUBFIELD_GENERATED = prove
 (`!r s p x:A.
        p IN ring_carrier(poly_ring (subfield_generated r s) (:1)) /\
        x IN ring_carrier(subfield_generated r s)
        ==> poly_eval (subfield_generated r s) p x = poly_eval r p x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subfield_generated r (s:A->bool)`; `r:A ring`; `x:A`;
                 `I:A->A`; `p:(1->num)->A`] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_THM; I_O_ID]);;

let MONIC_SUBFIELD_GENERATED = prove
 (`!r:A ring s p. monic (subfield_generated r s) p <=> monic r p`,
  REWRITE_TAC[monic; POLY_DEG_SUBFIELD_GENERATED; SUBFIELD_GENERATED]);;

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

let PRIME_SUBFIELD_SUBFIELD_GENERATED = prove
 (`!(k:A ring) s.
        subfield_generated (subfield_generated k s)
                           {ring_0(subfield_generated k s)} =
        subfield_generated k {ring_0 k}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC
   `?h. h subfield_of (k:A ring) /\ ring_carrier k INTER s SUBSET h` THEN
  ASM_SIMP_TAC[SUBFIELD_GENERATED_TRIVIAL] THEN
  FIRST_ASSUM(ASSUME_TAC o
    REWRITE_RULE[GSYM SUBFIELD_SUBFIELD_GENERATED_ALT]) THEN
  REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN REWRITE_TAC[SING_SUBSET] THENL
   [ASM_SIMP_TAC[RING_0_IN_SUBFIELD_GENERATED; PRIME_SUBFIELD_MINIMAL;
                 SUBFIELD_OF_SUBFIELD_GENERATED_EQ] THEN
    REWRITE_TAC[SUBFIELD_SUBFIELD_GENERATED_ALT] THEN
    EXISTS_TAC `ring_carrier(subfield_generated k s):A->bool` THEN
    MP_TAC(ISPECL [`k:A ring`; `s:A->bool`] RING_0_IN_SUBFIELD_GENERATED) THEN
    ASM SET_TAC[];
    REWRITE_TAC[REWRITE_RULE[CONJUNCT2 SUBFIELD_GENERATED]
     (ISPEC `subfield_generated k s:A ring` RING_0_IN_SUBFIELD_GENERATED)] THEN
    MATCH_MP_TAC SUBFIELD_OF_SUBFIELD_GENERATED_REV THEN
    EXISTS_TAC `s:A->bool` THEN MATCH_MP_TAC SUBFIELD_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[FIELD_SUBFIELD_GENERATED_EQ]]);;

let PRIME_SUBFIELD_SUBFIELD = prove
 (`!k:A ring s.
        s subfield_of k
        ==> subfield_generated (subring_generated k s) {ring_0 k} =
            subfield_generated k {ring_0 k}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `subring_generated k s = subfield_generated k (s:A->bool)`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED;
                  CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    MP_TAC(ISPECL [`k:A ring`; `s:A->bool`]
      PRIME_SUBFIELD_SUBFIELD_GENERATED) THEN
    REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED]]);;

let PRIME_SUBFIELD_MONOMORPHIC_IMAGE = prove
 (`!k:A ring l:B ring h.
        field k /\ ring_monomorphism(k,l) h
        ==> IMAGE h (ring_carrier(subfield_generated k {ring_0 k})) =
            ring_carrier(subfield_generated l {ring_0 l})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `{ring_0 k:A}`]
    SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; SING_SUBSET; RING_0;
               IMAGE_CLAUSES] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_0; RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let PRIME_SUBFIELD_HOMOMORPHISM_EXISTS = prove
 (`!(k:A ring) (l:B ring).
        field k /\ field l /\ ring_char k = ring_char l
        ==> ?h. ring_homomorphism(subfield_generated k {ring_0 k},l) h`,
  let lemma = prove
   (`!f:A ring.
        field f
        ==> ring_carrier(subfield_generated f {ring_0 f}) =
            {ring_div f (ring_of_int f a) (ring_of_int f b) | a,b |
             ~(&(ring_char f) divides b)} /\
            ~(&(ring_char f) divides &1) /\
            ring_0 f = ring_div f (ring_of_int f (&0)) (ring_of_int f (&1)) /\
            ring_1 f = ring_div f (ring_of_int f (&1)) (ring_of_int f (&1)) /\
            (!a b. ring_neg f (ring_div f (ring_of_int f a) (ring_of_int f b)) =
                   ring_div f (ring_of_int f (--a)) (ring_of_int f b)) /\
            (!a b c d.
               ~(&(ring_char f) divides b) /\ ~(&(ring_char f) divides d)
               ==> ~(&(ring_char f) divides (b * d)) /\
                   (ring_div f (ring_of_int f a) (ring_of_int f b) =
                    ring_div f (ring_of_int f c) (ring_of_int f d) <=>
                    (a * d == c * b) (mod &(ring_char f))) /\
                   ring_add f (ring_div f (ring_of_int f a) (ring_of_int f b))
                              (ring_div f (ring_of_int f c) (ring_of_int f d)) =
                   ring_div f (ring_of_int f (a * d + c * b))
                              (ring_of_int f (b * d)) /\
                   ring_mul f (ring_div f (ring_of_int f a) (ring_of_int f b))
                              (ring_div f (ring_of_int f c) (ring_of_int f d)) =
                   ring_div f (ring_of_int f (a * c)) (ring_of_int f (b * d)))`,
    GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM RING_OF_INT_EQ_0; GSYM RING_OF_INT_EQ] THEN
    REWRITE_TAC[RING_OF_INT_0; RING_OF_INT_1; RING_OF_INT_NEG;
                RING_OF_INT_ADD; RING_OF_INT_MUL] THEN
    REPEAT CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand)
        RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS o lhand o snd) THEN
      REWRITE_TAC[RING_CARRIER_SUBRING_GENERATED_0] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING; FIELD_UNIT; IN_ELIM_THM;
                     IN_UNIV] THEN MESON_TAC[RING_OF_INT];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
      ASM_MESON_TAC[FIELD_NONTRIVIAL];
      ASM_SIMP_TAC[RING_DIV_1; RING_0];
      ASM_SIMP_TAC[RING_DIV_1; RING_1];
      REPEAT GEN_TAC THEN MP_TAC(ISPEC `f:A ring` RING_OF_INT) THEN
      ASM_REWRITE_TAC[] THEN FIELD_TAC;
      REPEAT GEN_TAC THEN MP_TAC(ISPEC `f:A ring` RING_OF_INT) THEN
      ASM_REWRITE_TAC[] THEN FIELD_TAC]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:B ring` lemma) THEN MP_TAC(ISPEC `k:A ring` lemma) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`&(ring_char(l:B ring)):int`,`p:int`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?h. !a b. ~(p divides b)
              ==> ring_div l (ring_of_int l a) (ring_of_int l b) =
                  (h:A->B) (ring_div k (ring_of_int k a) (ring_of_int k b))`
  (X_CHOOSE_THEN `h:A->B` (ASSUME_TAC o GSYM)) THENL
   [MP_TAC(ISPECL
     [`\x:int#int. ~(p divides SND x)`;
      `\x. ring_div (l:B ring) (ring_of_int l (FST x)) (ring_of_int l (SND x))`;
      `\x. ring_div (k:A ring) (ring_of_int k (FST x)) (ring_of_int k (SND x))`]
     FUNCTION_FACTORS_LEFT_GEN) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IMP_CONJ] THEN ASM_SIMP_TAC[];
    EXISTS_TAC `h:A->B`] THEN
  ASM_REWRITE_TAC[ring_homomorphism; CONJUNCT2 SUBFIELD_GENERATED] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IMP_CONJ;
              RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[RING_DIV; RING_OF_INT; INTEGER_RULE `(x:int == x) (mod n)`]);;

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

let FIELD_EXTENSION_IMP_SUBSET_I = prove
 (`!(k:A ring) l.
        field_extension(k,l) I
        ==> ring_carrier k SUBSET ring_carrier l`,
  MESON_TAC[FIELD_EXTENSION_IMP_SUBSET; IMAGE_I]);;

let FIELD_EXTENSION_CARRIER = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ x IN ring_carrier k
        ==> h x IN ring_carrier l`,
  REWRITE_TAC[field_extension; ring_monomorphism; ring_homomorphism] THEN
  SET_TAC[]);;

let FIELD_EXTENSION_FROM_SUBRING_GENERATED = prove
 (`!(h:A->B) k l s.
        field_extension (k,l) h /\ field(subring_generated k s)
        ==> field_extension(subring_generated k s,l) h`,
  SIMP_TAC[field_extension; RING_MONOMORPHISM_FROM_SUBRING_GENERATED]);;

let FIELD_EXTENSION_FROM_SUBFIELD_GENERATED = prove
 (`!(h:A->B) k l s.
        field_extension (k,l) h
        ==> field_extension(subfield_generated k s,l) h`,
  SIMP_TAC[field_extension; FIELD_SUBFIELD_GENERATED] THEN
  MESON_TAC[RING_MONOMORPHISM_FROM_SUBRING_GENERATED;
            SUBRING_GENERATED_BY_SUBFIELD_GENERATED]);;

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

let FIELD_EXTENSION_TRANS_I = prove
 (`!(k:A ring) l m.
     field_extension (k,l) I /\ field_extension (l,m) I
     ==> field_extension (k,m) I`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FIELD_EXTENSION_TRANS) THEN
  REWRITE_TAC[I_O_ID]);;

let FIELD_EXTENSION_INTO_INTERMEDIATE = prove
 (`!(h:A->B) k l m.
        field_extension(k,m) h /\ field_extension(l,m) I /\
        IMAGE h (ring_carrier k) SUBSET ring_carrier l
        ==> field_extension(k,l) h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism;
                              I_THM; SUBSET; FORALL_IN_IMAGE]) THEN
  ASM_REWRITE_TAC[ring_monomorphism; ring_homomorphism; SUBSET;
                  FORALL_IN_IMAGE] THEN
  ASM_MESON_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL]);;

let FIELD_EXTENSION_SUBFIELD_GENERATED = prove
 (`!(l:A ring) s.
        field_extension(subfield_generated l s,l) I <=> field l`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[field_extension];
    SIMP_TAC[FIELD_EXTENSION_FROM_SUBFIELD_GENERATED; FIELD_EXTENSION_REFL]]);;

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
        IMAGE h (ring_carrier k) SUBSET s
        ==> field_extension(k,subfield_generated l s) h`,
  REWRITE_TAC[field_extension] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED] THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
  ASM SET_TAC[]);;

let RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE = prove
 (`!(j:B->C) l m.
        field l /\ field m /\ ring_homomorphism(l,m) j
        ==> IMAGE j (ring_carrier l) subfield_of m /\
            ring_isomorphism
             (l,subfield_generated m (IMAGE j (ring_carrier l))) j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_monomorphism(l:B ring,m:C ring) j` ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (j:B->C) (ring_carrier l) subfield_of m` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
    EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[CARRIER_SUBFIELD_OF];
    ASM_SIMP_TAC[RING_ISOMORPHISM; CARRIER_SUBFIELD_GENERATED_SUBFIELD]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_IMP_HOMOMORPHISM THEN
    MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[field_extension; SUBSET_REFL];
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_monomorphism])]);;

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

let COPRIME_POLY_NO_COMMON_ROOT = prove
 (`!(k:A ring) (l:B ring) (h:A->B) p q.
        field_extension(k,l) h /\ ring_coprime(poly_ring k (:1)) (p, q)
        ==> ~(?x. x IN ring_carrier l /\
                  poly_eval l (h o p) x = ring_0 l /\
                  poly_eval l (h o q) x = ring_0 l)`,
  REWRITE_TAC[field_extension] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN MP_TAC(ISPECL
   [`poly_ring (k:A ring) (:1)`; `l:B ring`;
    `(\q. poly_eval l q y) o (\p. (h:A->B) o p)`;
    `p:(1->num)->A`; `q:(1->num)->A`] RING_COPRIME_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_COPRIME_00; FIELD_IMP_NONTRIVIAL_RING;
               PID_POLY_RING; PID_IMP_BEZOUT_RING; o_THM] THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
  EXISTS_TAC `poly_ring (l:B ring) (:1)` THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_RINGS; RING_HOMOMORPHISM_POLY_EVAL;
               RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let COPRIME_POLY_NO_COMMON_ROOT_I = prove
 (`!(k:A ring) (E:A ring) p q.
        field_extension(k,E) I /\
        ring_coprime(poly_ring k (:1)) (p, q)
        ==> ~(?x. x IN ring_carrier E /\
                  poly_eval E p x = ring_0 E /\
                  poly_eval E q x = ring_0 E)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `E:A ring`; `I:A->A`;
                 `p:(1->num)->A`; `q:(1->num)->A`]
    COPRIME_POLY_NO_COMMON_ROOT) THEN
  ASM_REWRITE_TAC[I_O_ID] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);;

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

let RING_SPAN_EQ = prove
 (`!k l (f:A->B) g s.
        (!x. x IN ring_carrier k ==> f x = g x)
        ==> ring_span(k,l) f s = ring_span(k,l) g s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THEN
  REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC ring_span_INDUCT THEN
  ASM_SIMP_TAC[RING_SPAN_ADD; RING_SPAN_0; RING_SPAN_INC] THEN
  ASM_MESON_TAC[RING_SPAN_MUL]);;

let RING_SPAN_EQ_IMAGE = prove
 (`!(h1:A->B) (h2:C->B) k1 k2 l.
        IMAGE h1 (ring_carrier k1) = IMAGE h2 (ring_carrier k2)
        ==> ring_span (k1,l) h1 = ring_span (k2,l) h2`,
  let lemma = prove
   (`!(h1:A->B) (h2:C->B) k1 k2 l s.
        IMAGE h1 (ring_carrier k1) SUBSET IMAGE h2 (ring_carrier k2)
        ==> ring_span (k1,l) h1 s SUBSET ring_span (k2,l) h2 s`,
    REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN
    DISCH_TAC THEN MATCH_MP_TAC ring_span_INDUCT THEN
    SIMP_TAC[RING_SPAN_0; RING_SPAN_INC; RING_SPAN_ADD] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `x:B`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:C` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_SPAN_MUL THEN
    ASM_MESON_TAC[]) in
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

let RING_SPAN_NONEMPTY = prove
 (`!(h:A->B) k l s. ~(ring_span (k,l) h s = {})`,
  MESON_TAC[MEMBER_NOT_EMPTY; RING_SPAN_0]);;

let RING_SPAN_SELF = prove
 (`!(h:A->B) l k. ring_span (k,l) h (ring_carrier l) = ring_carrier l`,
  MESON_TAC[RING_SPAN_SUPERSET; RING_SPAN_SUBSET; SUBSET_ANTISYM;
            SUBSET_REFL]);;

let RING_SPAN_EMPTY = prove
 (`!(h:A->B) k l. ring_span (k,l) h {} = {ring_0 l}`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; FORALL_AND_THM] THEN
  REWRITE_TAC[SING_SUBSET; RING_SPAN_0] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET] THEN
  MATCH_MP_TAC ring_span_INDUCT THEN REWRITE_TAC[IN_SING; NOT_IN_EMPTY] THEN
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

let RING_DEPENDENT_EQ = prove
 (`!k l (f:A->B) g s.
        (!x. x IN ring_carrier k ==> f x = g x)
        ==> (ring_dependent (k,l) f s <=> ring_dependent (k,l) g s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_dependent] THEN
  ASM_MESON_TAC[RING_SPAN_EQ]);;

let RING_INDEPENDENT_EQ = prove
 (`!k l (f:A->B) g s.
        (!x. x IN ring_carrier k ==> f x = g x)
        ==> (ring_independent (k,l) f s <=> ring_independent (k,l) g s)`,
  REWRITE_TAC[ring_independent] THEN MESON_TAC[RING_DEPENDENT_EQ]);;

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

let RING_DEPENDENT_SING = prove
 (`!(h:A->B) k l x.
        ring_dependent (k,l) h {x} <=> x = ring_0 l`,
  REWRITE_TAC[ring_dependent; SING_SUBSET] THEN
  REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[RING_SPAN_EMPTY; IN_SING; SET_RULE `{x:B} DELETE x = {}`] THEN
  MESON_TAC[RING_0]);;

let RING_DEPENDENT_ONE = prove
 (`!(h:A->B) k l.
        ring_dependent (k,l) h {ring_1 l} <=> trivial_ring l`,
  REWRITE_TAC[RING_DEPENDENT_SING; TRIVIAL_RING_10]);;

let RING_INDEPENDENT_SING = prove
 (`!(h:A->B) k l x.
        ring_independent (k,l) h {x} <=>
        x IN ring_carrier l /\ ~(x = ring_0 l)`,
  REWRITE_TAC[ring_independent; RING_DEPENDENT_SING; SING_SUBSET]);;

let RING_INDEPENDENT_ONE = prove
 (`!(h:A->B) k l.
        ring_independent (k,l) h {ring_1 l} <=> ~trivial_ring l`,
  REWRITE_TAC[RING_INDEPENDENT_SING; TRIVIAL_RING_10; RING_1]);;

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

(* ------------------------------------------------------------------------- *)
(* A homogeneous linear system over a field with more unknowns than          *)
(* equations has a nontrivial solution. Proof: the columns of the matrix, as *)
(* elements of the product ring of copies of k indexed by the equations, are *)
(* in the span of the standard basis, so RING_DEPENDENT_SPAN_IMAGE applies.  *)
(* ------------------------------------------------------------------------- *)

let HOMOGENEOUS_SYSTEM_NONTRIVIAL_SOLUTION = prove
 (`!(k:A ring) (s:K->bool) (t:L->bool) (c:K->L->A).
        field k /\ FINITE s /\ FINITE t /\ CARD s < CARD t /\
        (!i j. i IN s /\ j IN t ==> c i j IN ring_carrier k)
        ==> ?x. (!j. j IN t ==> x j IN ring_carrier k) /\
                (?j. j IN t /\ ~(x j = ring_0 k)) /\
                (!i. i IN s
                     ==> ring_sum k t (\j. ring_mul k (c i j) (x j)) =
                         ring_0 k)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `h = \a:A. RESTRICTION s (\i:K. a)` THEN
  ABBREV_TAC `b = \i:K. RESTRICTION s (\j. if j = i then ring_1 k
                                           else ring_0(k:A ring))` THEN
  SUBGOAL_THEN
   `ring_homomorphism(k,product_ring s (\i:K. k)) (h:A->K->A) /\
    (!a. a IN ring_carrier k ==> h a IN ring_carrier(product_ring s (\i. k))) /\
    (!i. i IN s ==> (b:K->K->A) i IN ring_carrier(product_ring s (\i. k)))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "b"] THEN
    REWRITE_TAC[RING_HOMOMORPHISM_DIAGONAL; PRODUCT_RING] THEN
    REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
    MESON_TAC[RING_0; RING_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`h:A->K->A`; `k:A ring`; `product_ring s (\i:K. (k:A ring))`;
    `\j:L. RESTRICTION s (\i:K. (c:K->L->A) i j)`; `t:L->bool`;
    `IMAGE (b:K->K->A) s`] RING_DEPENDENT_SPAN_IMAGE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[CARD_IMAGE_LE; LET_TRANS]] THEN
    X_GEN_TAC `j:L` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `RESTRICTION s (\i:K. (c:K->L->A) i j) =
      ring_sum (product_ring s (\i:K. k)) s
       (\i. ring_mul (product_ring s (\i:K. k)) (h(c i j)) (b i))`
    SUBST1_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_PRODUCT_RING o
        rand o snd) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[RESTRICTION_EXTENSION] THEN
      X_GEN_TAC `a:K` THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS
       `ring_sum k s (\i:K. if i = a then (c:K->L->A) a j else ring_0 k)` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[RING_SUM_DELTA]; ALL_TAC] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["h"; "b"] THEN
      ASM_SIMP_TAC[PRODUCT_RING; RESTRICTION] THEN
      ASM_CASES_TAC `a:K = i` THEN ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO];
      MATCH_MP_TAC RING_SPAN_SUM THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC RING_SPAN_MUL THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC[FUN_IN_IMAGE]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:L->A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `i:K` o check (is_eq o concl)) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_PRODUCT_RING o
      rator o lhand o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:L` THEN DISCH_TAC THEN
      MATCH_MP_TAC RING_MUL THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[PRODUCT_RING; RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
      ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "h" THEN ASM_SIMP_TAC[PRODUCT_RING; RESTRICTION] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN
    ASM_SIMP_TAC[RING_MUL_SYM]]);;

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

(* Agreement on the scalar image and generators extends to their span.      *)
let RING_HOMOMORPHISMS_EQ_FROM_RING_SPAN = prove
 (`!(h:A->B) (f:B->C) g k l m s.
        ring_homomorphism(l,m) f /\ ring_homomorphism(l,m) g /\
        (!a. a IN ring_carrier k /\ h a IN ring_carrier l
             ==> f(h a) = g(h a)) /\
        (!x. x IN ring_carrier l /\ x IN s ==> f x = g x)
        ==> !x. x IN ring_span(k,l) h s ==> f x = g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:B->C`; `g:B->C`; `l:B ring`; `m:C ring`;
                `IMAGE (h:A->B) (ring_carrier k) UNION s`]
    RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM SET_TAC[];
    MESON_TAC[RING_SPAN_SUBSET_SUBRING_GENERATED; SUBSET]]);;

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

let RING_DEPENDENT_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m s.
        s SUBSET ring_carrier l /\
        ring_homomorphism(k,l) f /\
        ring_monomorphism(l,m) g
        ==> (ring_dependent (k,m) (g o f) (IMAGE g s) <=>
             ring_dependent (k,l) f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_dependent] THEN
  SUBGOAL_THEN `ring_homomorphism(l:B ring,m:C ring) g` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:B->C) s SUBSET ring_carrier m` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE
     [ring_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `(x:B) IN s` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (g:B->C) s DELETE g x = IMAGE g (s DELETE x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!y:B. y IN s ==> ((g:B->C) y = g x <=> y = x))
      ==> IMAGE g s DELETE (g x) = IMAGE g (s DELETE x)`) THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC RING_MONOMORPHISM_INJECTIVE_EQ THEN
    MAP_EVERY EXISTS_TAC [`l:B ring`; `m:C ring`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `s DELETE (x:B)`] RING_SPAN_HOMOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:B) IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `x:B = z` (fun th -> ASM_MESON_TAC[th]) THEN
    MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `g:B->C`; `x:B`; `z:B`]
      RING_MONOMORPHISM_INJECTIVE_EQ) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    DISCH_TAC THEN EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[]]);;

let RING_INDEPENDENT_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m s.
        s SUBSET ring_carrier l /\
        ring_homomorphism(k,l) f /\
        ring_monomorphism(l,m) g
        ==> (ring_independent (k,m) (g o f) (IMAGE g s) <=>
             ring_independent (k,l) f s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ring_independent] THEN
  MATCH_MP_TAC(TAUT `(q <=> r) /\ p ==> (p /\ ~q <=> ~r)`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RING_DEPENDENT_MONOMORPHIC_IMAGE];
    RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism; ring_monomorphism]) THEN
    ASM SET_TAC[]]);;

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

let FINITE_EXTENSION_SUBFIELD_GENERATED = prove
 (`!(h:A->B) k l s.
        finite_extension(k,l) h /\ IMAGE h (ring_carrier k) SUBSET s
        ==> finite_extension(k,subfield_generated l s) h /\
            finite_extension(subfield_generated l s,l) I`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                 `subfield_generated l (s:B->bool)`; `l:B ring`]
    FINITE_EXTENSION_TRANS_EQ) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_INTO_SUBFIELD_GENERATED; I_O_ID;
               FIELD_EXTENSION_SUBFIELD_GENERATED]);;

let FINITE_EXTENSION_EQ_IMAGE = prove
 (`!(h1:A->B) (h2:C->B) k1 k2 l.
        field_extension(k1,l) h1 /\ field_extension(k2,l) h2 /\
        IMAGE h1 (ring_carrier k1) = IMAGE h2 (ring_carrier k2)
        ==> (finite_extension(k1,l) h1 <=> finite_extension(k2,l) h2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[finite_extension] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_SPAN_EQ_IMAGE th]));;

(* ------------------------------------------------------------------------- *)
(* The degree of a field extension as a natural number: the dimension as a   *)
(* vector space when finite, 0 otherwise.                                    *)
(* ------------------------------------------------------------------------- *)

let extension_degree = new_definition
 `extension_degree (k,l) (h:A->B) =
        if matroid_finite_dimensional (ring_matroid (k,l) h)
        then matroid_dimension (ring_matroid (k,l) h) else 0`;;

let EXTENSION_DEGREE_EQ_CARD_BASIS = prove
 (`!(h:A->B) k l b.
        field k /\ ring_homomorphism (k,l) h /\
        ring_basis (k,l) h b /\ FINITE b
        ==> extension_degree (k,l) h = CARD b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[extension_degree] THEN
  SUBGOAL_THEN `matroid_basis (ring_matroid (k,l) (h:A->B)) b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_MATROID_BASIS]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[MATROID_DIMENSION_EQ_CARD];
    ASM_MESON_TAC[MATROID_FINITE_DIMENSIONAL_ANY]]);;

let EXTENSION_DEGREE_LE_INDEPENDENT_BOUND = prove
 (`!(h:A->B) k l n.
        field k /\ ring_homomorphism(k,l) h /\
        (!s. ring_independent (k,l) h s ==> FINITE s /\ CARD s <= n)
        ==> extension_degree(k,l) h <= n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_matroid (k,l) (h:A->B)`; `n:num`]
    MATROID_DIMENSION_LE_INDEPENDENT_BOUND) THEN
  ASM_SIMP_TAC[RING_MATROID_INDEPENDENT; extension_degree]);;

let RING_INDEPENDENT_CARD_LE_EXTENSION_DEGREE = prove
 (`!(h:A->B) k l s.
        finite_extension(k,l) h /\ ring_independent (k,l) h s
        ==> FINITE s /\ CARD s <= extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    RING_MATROID_FINITE_DIMENSIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[extension_degree] THEN
  MATCH_MP_TAC MATROID_DIMENSION_GE_FINITE_CARD THEN
  ASM_SIMP_TAC[RING_MATROID_INDEPENDENT]);;

let EXTENSION_DEGREE_EQ_0 = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> (extension_degree (k,l) h = 0 <=> ~finite_extension (k,l) h)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[FINITE_EXTENSION_BASIS] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B->bool`]
      EXTENSION_DEGREE_EQ_CARD_BASIS) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN
    ASM_MESON_TAC[RING_SPANNING_IMP_NONEMPTY; ring_basis];
    ASM_SIMP_TAC[extension_degree; RING_MATROID_FINITE_DIMENSIONAL]]);;

let EXTENSION_DEGREE_TOWER_LAW = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g
        ==> extension_degree (k,m) (g o f) =
            extension_degree (k,l) f * extension_degree (l,m) g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `field_extension (k:A ring,m:C ring) ((g:B->C) o (f:A->B))`
  ASSUME_TAC THENL [ASM_MESON_TAC[FIELD_EXTENSION_TRANS]; ALL_TAC] THEN
  ASM_CASES_TAC
   `finite_extension (k:A ring,l:B ring) f /\
    finite_extension (l:B ring,m:C ring) g`
  THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[FINITE_EXTENSION_BASIS] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:C->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`]
      RING_BASIS_EXISTS) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
      DISCH_THEN(X_CHOOSE_TAC `d:C->bool`)] THEN
    MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                   `b:B->bool`; `c:C->bool`; `d:C->bool`]
      FIELD_EXTENSION_TOWER_LAW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(d:C->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CARD_MUL_FINITE; CARD_FINITE_CONG]; ALL_TAC] THEN
    SUBGOAL_THEN
     `extension_degree (k,l) (f:A->B) = CARD(b:B->bool) /\
      extension_degree (l,m) (g:B->C) = CARD(c:C->bool) /\
      extension_degree (k,m) ((g:B->C) o (f:A->B)) = CARD(d:C->bool)`
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC EXTENSION_DEGREE_EQ_CARD_BASIS THEN
      ASM_MESON_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
      ASM_MESON_TAC[CARD_MUL_C; CARD_EQ_CARD_IMP; CARD_MUL_FINITE]];
    MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
      FINITE_EXTENSION_TRANS_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `extension_degree (k:A ring,m:C ring) ((g:B->C) o (f:A->B)) = 0`
    SUBST1_TAC THENL [ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[MULT_EQ_0] THEN
    ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0]]);;

let EXTENSION_DEGREE_ISOMORPHISM = prove
 (`!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism(k,l) f
        ==> extension_degree(k,l) f = 1`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `field(k:A ring) /\ field(l:B ring)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ISOMORPHIC_RING_FIELDNESS; isomorphic_ring]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `{ring_1 l:B}`]
    EXTENSION_DEGREE_EQ_CARD_BASIS) THEN
  ASM_REWRITE_TAC[FINITE_SING; CARD_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ring_basis; ring_spanning; RING_INDEPENDENT_SING; SING_SUBSET;
               RING_1; FIELD_NONTRIVIAL; RING_SPAN_SING] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [ring_epimorphism] o
    MATCH_MP RING_ISOMORPHISM_IMP_EPIMORPHISM) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[RING_MUL_RID; RING_HOMOMORPHISM_IN_CARRIER]);;

let EXTENSION_DEGREE_REFL = prove
 (`!k:A ring. field k ==> extension_degree(k,k) I = 1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EXTENSION_DEGREE_ISOMORPHISM THEN
  ASM_REWRITE_TAC[RING_ISOMORPHISM_I]);;

let EXTENSION_DEGREE_EQ_1 = prove
 (`!(h:A->B) k l.
        field_extension (k,l) h
        ==> (extension_degree (k,l) h = 1 <=>
             IMAGE h (ring_carrier k) = ring_carrier l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC EXTENSION_DEGREE_ISOMORPHISM THEN
    ASM_REWRITE_TAC[GSYM RING_MONOMORPHISM_EPIMORPHISM; ring_epimorphism]] THEN
  REWRITE_TAC[extension_degree] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_basis (k,l) (h:A->B) {ring_1 l}` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_MATROID_BASIS] THEN
    MATCH_MP_TAC MATROID_BASIS_LARGE_INDEPENDENT THEN
    ASM_SIMP_TAC[RING_MATROID_INDEPENDENT; RING_INDEPENDENT_SING; RING_1;
                 FIELD_NONTRIVIAL; CARD_SING; LE_REFL];
    ASM_SIMP_TAC[ring_basis; ring_spanning; RING_SPAN_SING; RING_1]] THEN
  DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[RING_MUL_RID; FIELD_EXTENSION_CARRIER]);;

let EXTENSION_DEGREE_EQ_IMAGE = prove
 (`!(h1:A->B) (h2:C->B) k1 k2 l.
        IMAGE h1 (ring_carrier k1) = IMAGE h2 (ring_carrier k2)
        ==> extension_degree (k1,l) h1 = extension_degree (k2,l) h2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[extension_degree; ring_matroid] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_SPAN_EQ_IMAGE th]));;

(* For a homomorphism h : k -> l of fields, h maps the prime subfield of k   *)
(* onto that of l (PRIME_SUBFIELD_MONOMORPHIC_IMAGE), so the tower laws for  *)
(* finiteness and degrees (FINITE_EXTENSION_TRANS_EQ,                        *)
(* EXTENSION_DEGREE_TOWER_LAW) apply to Q_k -> k -> l, where Q_k is the      *)
(* prime subfield of k, and [l:Q_k] = [l:Q_l] (EXTENSION_DEGREE_EQ_IMAGE).   *)
let PRIME_SUBFIELD_TOWER_LAW = prove
 (`!(h:A->B) k l.
        field k /\ field l /\ ring_homomorphism(k,l) h
        ==> ring_char k = ring_char l /\
            (finite_extension(subfield_generated l {ring_0 l},l) I <=>
             finite_extension(subfield_generated k {ring_0 k},k) I /\
             finite_extension(k,l) h) /\
            extension_degree(subfield_generated l {ring_0 l},l) I =
            extension_degree(subfield_generated k {ring_0 k},k) I *
            extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_monomorphism(k:A ring,l:B ring) h` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_RING_HOMOMORPHISM_MONOMORPHISM;
                 FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `h:A->B`; `subfield_generated k {ring_0 k:A}`;
                 `k:A ring`; `l:B ring`] EXTENSION_DEGREE_TOWER_LAW) THEN
  MP_TAC(ISPECL [`I:A->A`; `h:A->B`; `subfield_generated k {ring_0 k:A}`;
                 `k:A ring`; `l:B ring`] FINITE_EXTENSION_TRANS_EQ) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `subfield_generated k {ring_0 k:A}`;
                 `subfield_generated l {ring_0 l:B}`; `l:B ring`]
    FINITE_EXTENSION_EQ_IMAGE) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `subfield_generated k {ring_0 k:A}`;
                 `subfield_generated l {ring_0 l:B}`; `l:B ring`]
    EXTENSION_DEGREE_EQ_IMAGE) THEN
  MP_TAC(ISPECL [`I:A->A`; `h:A->B`; `subfield_generated k {ring_0 k:A}`;
                 `k:A ring`; `l:B ring`] FIELD_EXTENSION_TRANS) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; field_extension;
               PRIME_SUBFIELD_MONOMORPHIC_IMAGE; IMAGE_I; I_O_ID]);;

let EXTENSION_DEGREE_EQ_TOWER = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g /\
        finite_extension (k,m) (g o f)
        ==> (extension_degree (k,l) f = extension_degree (k,m) (g o f) <=>
             IMAGE g (ring_carrier l) = ring_carrier m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    EXTENSION_DEGREE_TOWER_LAW) THEN
  MP_TAC(ISPECL [`g:B->C`; `l:B ring`; `m:C ring`] EXTENSION_DEGREE_EQ_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(extension_degree (k,l) (f:A->B) = 0)` MP_TAC THENL
   [ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0; FINITE_EXTENSION_TRANS_EQ];
    REWRITE_TAC[ARITH_RULE `a = a * b <=> a * b = a * 1`] THEN
    REWRITE_TAC[EQ_MULT_LCANCEL] THEN CONV_TAC TAUT]);;

let EXTENSION_DEGREE_SUBFIELD_GENERATED_DIVIDES = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h /\ IMAGE h (ring_carrier k) SUBSET s
        ==> extension_degree(k,subfield_generated l s) h divides
            extension_degree(k,l) h /\
            extension_degree(subfield_generated l s,l) I divides
            extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                 `subfield_generated l (s:B->bool)`; `l:B ring`]
    EXTENSION_DEGREE_TOWER_LAW) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_INTO_SUBFIELD_GENERATED;
               FIELD_EXTENSION_SUBFIELD_GENERATED; I_O_ID] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL]);;

let FINITE_EXTENSION_HOMOMORPHIC_IMAGE = prove
 (`!(h:A->B) (j:B->C) k l m.
        finite_extension(k,l) h /\ field m /\ ring_homomorphism(l,m) j
        ==> finite_extension
             (k,subfield_generated m (IMAGE j (ring_carrier l))) (j o h) /\
            extension_degree
             (k,subfield_generated m (IMAGE j (ring_carrier l))) (j o h) =
            extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`j:B->C`; `l:B ring`; `m:C ring`]
    RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = IMAGE (j:B->C) (ring_carrier l)` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `finite_extension(l:B ring,subfield_generated m s) (j:B->C)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_EXTENSION_ISOMORPHISM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_EXTENSION_TRANS THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`h:A->B`; `j:B->C`; `k:A ring`; `l:B ring`;
                   `subfield_generated m (s:C->bool)`]
      EXTENSION_DEGREE_TOWER_LAW) THEN
    ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION; EXTENSION_DEGREE_ISOMORPHISM;
                 MULT_CLAUSES]]);;

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

let FINITE_EXTENSION_SUBFIELD_GENERATORS = prove
 (`!(h:A->B) k l s.
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s /\
        finite_extension(k,subfield_generated l s) h
        ==> ?b. FINITE b /\ b SUBSET s /\
                ring_carrier(subfield_generated l
                              (IMAGE h (ring_carrier k) UNION b)) = s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_FINITELY_GENERATED_EXTENSION) THEN
  REWRITE_TAC[finitely_generated_extension] THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC o last o CONJUNCTS)
  THEN EXISTS_TAC `b:B->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:B ring`; `IMAGE (h:A->B) (ring_carrier k) UNION b`;
                 `s:B->bool`] SUBFIELD_GENERATED_IDEMPOT_GEN) THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; UNION_SUBSET] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD]);;

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

(* Every element x of the field generated over h(k) by one more element f is *)
(* a quotient of polynomial values: x q(f) = p(f) for polynomials p and q    *)
(* over k with q(f) nonzero (SUBFIELD_GENERATED_INSERT_FRACTIONS).           *)
let SUBFIELD_GENERATED_INSERT_FRACTIONS = prove
 (`!(h:A->B) k l f x.
        field_extension(k,l) h /\ f IN ring_carrier l /\
        x IN ring_carrier
              (subfield_generated l (f INSERT IMAGE h (ring_carrier k)))
        ==> ?p q. p IN ring_carrier(poly_ring k (:1)) /\
                  q IN ring_carrier(poly_ring k (:1)) /\
                  ~(poly_extend(k,l) h (\u. f) q = ring_0 l) /\
                  ring_mul l x (poly_extend(k,l) h (\u. f) q) =
                  poly_extend(k,l) h (\u. f) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[field_extension] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`l:B ring`; `(f:B) INSERT IMAGE (h:A->B) (ring_carrier k)`]
    RING_CARRIER_SUBFIELD_GENERATED_SUBRING_QUOTIENTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING; FIELD_UNIT] THEN
    MESON_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET; SUBSET];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `f:B`]
    IMAGE_POLY_EXTEND_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE
   [IN_ELIM_THM; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(1->num)->A` (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`p:(1->num)->A`; `q:(1->num)->A`] THEN
  ASM_SIMP_TAC[ring_div; GSYM RING_MUL_ASSOC; RING_INV; POLY_EXTEND;
               FIELD_MUL_LINV; RING_MUL_RID]);;

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
  REWRITE_TAC[coeff] THEN ASM_REWRITE_TAC[] THEN
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
  REWRITE_TAC[coeff] THEN
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
  REWRITE_TAC[coeff] THEN
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
(* Minimal polynomial of an element algebraic over a field (poly_0 for an    *)
(* element that is not algebraic).                                           *)
(* ------------------------------------------------------------------------- *)

let minimal_polynomial = new_definition
 `minimal_polynomial (k,l) (h:A->B) (x:B) =
    if algebraic_over (k,l) h x
    then (@p. p IN ring_carrier(poly_ring k (:1)) /\
              ~(p = poly_0 k) /\
              monic k p /\
              ring_irreducible (poly_ring k (:1)) p /\
              poly_extend (k,l) h (\v. x) p = ring_0 l)
    else poly_0 k`;;

let ALGEBRAIC_OVER_EXISTS_MONIC_IRREDUCIBLE = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\
        algebraic_over (k,l) h x
        ==> ?p. p IN ring_carrier(poly_ring k (:1)) /\
                ~(p = poly_0 k) /\
                monic k p /\
                ring_irreducible (poly_ring k (:1)) p /\
                1 <= poly_deg k p /\
                poly_extend (k,l) h (\v. x) p = ring_0 l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [algebraic_over]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `p0:(1->num)->A` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `ev = poly_extend (k,l) (h:A->B) (\v:1. x)` THEN
  SUBGOAL_THEN `ring_homomorphism(poly_ring k (:1),l) (ev:((1->num)->A)->B)`
  ASSUME_TAC THENL
   [EXPAND_TAC "ev" THEN MATCH_MP_TAC RING_HOMOMORPHISM_POLY_EXTEND THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `l:B ring`;
                 `ev:((1->num)->A)->B`; `{ring_0 l:B}`]
    PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[PRIME_IDEAL_0; FIELD_IMP_INTEGRAL_DOMAIN; IN_SING] THEN
  DISCH_TAC THEN MP_TAC(ISPEC `k:A ring` PID_POLY_RING) THEN
  ASM_REWRITE_TAC[PID; principal_ideal] THEN
  DISCH_THEN(MP_TAC o SPEC
   `{q | q IN ring_carrier(poly_ring k (:1)) /\
         (ev:((1->num)->A)->B) q = ring_0 l}` o CONJUNCT2) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:(1->num)->A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_irreducible (poly_ring k (:1)) (m:(1->num)->A) /\
                (ev:((1->num)->A)->B) m = ring_0 l`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN] THEN
      ASM_REWRITE_TAC[RING_PRIME_IDEAL] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IDEAL_GENERATED_0]) THEN ASM SET_TAC[];
      SUBGOAL_THEN `(m:(1->num)->A) IN ideal_generated (poly_ring k (:1)) {m}`
      MP_TAC THENL
       [MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_SING];
        ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_ELIM_THM]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `m:(1->num)->A`]
    FIELD_MONIC_IRREDUCIBLE_ASSOCIATE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `q:(1->num)->A` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; LE_1; IRREDUCIBLE_IMP_POLY_DEG_NZ] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[ring_irreducible; POLY_RING_CLAUSES]; ALL_TAC] THEN
  MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `l:B ring`;
                 `ev:((1->num)->A)->B`; `m:(1->num)->A`; `q:(1->num)->A`]
    RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
  ASM_MESON_TAC[ring_associates; RING_DIVIDES_ZERO]);;

let MINIMAL_POLYNOMIAL = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\
        algebraic_over (k,l) h x
        ==> minimal_polynomial (k,l) h x IN ring_carrier(poly_ring k (:1)) /\
            ~(minimal_polynomial (k,l) h x = poly_0 k) /\
            monic k (minimal_polynomial (k,l) h x) /\
            ring_irreducible (poly_ring k (:1))
                             (minimal_polynomial (k,l) h x) /\
            poly_extend (k,l) h (\v. x) (minimal_polynomial (k,l) h x) =
            ring_0 l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[minimal_polynomial] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    ALGEBRAIC_OVER_EXISTS_MONIC_IRREDUCIBLE) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MINIMAL_POLYNOMIAL_IN_CARRIER = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> minimal_polynomial (k,l) h x IN ring_carrier(poly_ring k (:1))`,
  MESON_TAC[MINIMAL_POLYNOMIAL]);;

let MINIMAL_POLYNOMIAL_NONZERO = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> ~(minimal_polynomial (k,l) h x = poly_0 k)`,
  MESON_TAC[MINIMAL_POLYNOMIAL]);;

let MINIMAL_POLYNOMIAL_MONIC = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> monic k (minimal_polynomial (k,l) h x)`,
  MESON_TAC[MINIMAL_POLYNOMIAL]);;

let MINIMAL_POLYNOMIAL_IRREDUCIBLE = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> ring_irreducible (poly_ring k (:1)) (minimal_polynomial (k,l) h x)`,
  MESON_TAC[MINIMAL_POLYNOMIAL]);;

let MINIMAL_POLYNOMIAL_VANISHES = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> poly_extend (k,l) h (\v. x) (minimal_polynomial (k,l) h x) =
            ring_0 l`,
  MESON_TAC[MINIMAL_POLYNOMIAL]);;

let MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m a.
        field_extension(k,l) f /\ algebraic_over(k,l) f a /\
        ring_homomorphism(l,m) g
        ==> poly_eval m ((g o f) o minimal_polynomial(k,l) f a) (g a) =
            ring_0 m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `a:B`]
    MINIMAL_POLYNOMIAL_VANISHES) THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `a:B`]
    MINIMAL_POLYNOMIAL_IN_CARRIER) THEN
  ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `a:B`; `g:B->C`;
                 `(f:A->B) o minimal_polynomial (k,l) f a`]
    POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[o_ASSOC] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[ALGEBRAIC_OVER_IN_CARRIER;
                  IN_RING_POLYNOMIAL_CARRIER_COMPOSE];
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let MINIMAL_POLYNOMIAL_DIVIDES = prove
 (`!(h:A->B) k l x p.
        field_extension (k,l) h /\
        algebraic_over (k,l) h x /\
        p IN ring_carrier(poly_ring k (:1))
        ==> (ring_divides (poly_ring k (:1))
                          (minimal_polynomial (k,l) h x) p <=>
             poly_extend (k,l) h (\v. x) p = ring_0 l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = minimal_polynomial (k:A ring,l:B ring) h x` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  SUBGOAL_THEN
   `!r. r IN ring_carrier(poly_ring k (:1))
        ==> poly_extend (k,l) h (\v. x) r = poly_eval l ((h:A->B) o r) x`
  ASSUME_TAC THENL [ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; poly_eval]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MP_TAC(ISPECL
     [`poly_ring (k:A ring) (:1)`; `l:B ring`;
      `poly_extend (k,l) (h:A->B) (\v:1. x)`; `q:(1->num)->A`;
      `p:(1->num)->A`] RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_EXTEND; RING_DIVIDES_ZERO];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `q:(1->num)->A`;
                   `p:(1->num)->A`] COPRIME_POLY_NO_COMMON_ROOT) THEN
    ASM_SIMP_TAC[RING_IRREDUCIBLE_COPRIME_EQ] THEN ASM_MESON_TAC[]]);;

let MINIMAL_POLYNOMIAL_UNIQUE = prove
 (`!(h:A->B) k l x q.
        field_extension (k,l) h /\
        algebraic_over (k,l) h x /\
        monic k q /\
        ring_irreducible (poly_ring k (:1)) q /\
        poly_extend (k,l) h (\v. x) q = ring_0 l
        ==> minimal_polynomial (k,l) h x = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `q IN ring_carrier(poly_ring (k:A ring) (:1))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IRREDUCIBLE_IN_CARRIER]; ALL_TAC] THEN
  ABBREV_TAC `mp = minimal_polynomial (k:A ring,l:B ring) h x` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_divides (poly_ring (k:A ring) (:1)) mp q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`; `q:(1->num)->A`]
      MINIMAL_POLYNOMIAL_DIVIDES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_associates (poly_ring (k:A ring) (:1)) mp q` MP_TAC THENL
   [MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `mp:(1->num)->A`;
                   `q:(1->num)->A`]
      RING_IRREDUCIBLES_COPRIME_OR_ASSOCIATES) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `mp:(1->num)->A`;
                   `q:(1->num)->A`] RING_IRREDUCIBLE_COPRIME_EQ) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ASM_MESON_TAC[MONIC_ASSOCIATES_EQ; INTEGRAL_DOMAIN_POLY_RING;
                  FIELD_IMP_INTEGRAL_DOMAIN; field_extension]]);;

let MINIMAL_POLYNOMIAL_ROOTS_IRREDUCIBLE = prove
 (`!(h:A->B) k l p a.
        field_extension(k,l) h /\ ring_irreducible(poly_ring k (:1)) p /\
        a IN ring_carrier l /\ poly_eval l (h o p) a = ring_0 l
        ==> {x | x IN ring_carrier l /\
                 poly_eval l (h o minimal_polynomial(k,l) h a) x = ring_0 l} =
            {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
  SUBGOAL_THEN `poly_extend (k,l) (h:A->B) (\v:1. a) p = ring_0 l`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval]; ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) a` ASSUME_TAC THENL
   [REWRITE_TAC[algebraic_over] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `p:(1->num)->A` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ring_irreducible];
    ALL_TAC] THEN
  ABBREV_TAC `q = minimal_polynomial (k,l) (h:A->B) a` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_divides (poly_ring k (:1)) (q:(1->num)->A) p`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`; `p:(1->num)->A`]
      MINIMAL_POLYNOMIAL_DIVIDES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_divides (poly_ring k (:1)) (p:(1->num)->A) q`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `ring_associates (poly_ring k (:1)) (q:(1->num)->A) p`
     (fun th -> MESON_TAC[th; ring_associates]) THEN
    MATCH_MP_TAC RING_NONUNIT_DIVIDES_IRREDUCIBLE THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ring_irreducible];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. ring_divides (poly_ring k (:1)) u v
          ==> !x. x IN ring_carrier l /\ poly_eval l ((h:A->B) o u) x = ring_0 l
                  ==> poly_eval l (h o v) x = ring_0 l`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RING_DIVIDES_HOMOMORPHIC_IMAGE o CONJ
     (ISPEC `(:1)` (MATCH_MP RING_HOMOMORPHISM_POLY_RINGS
       (ASSUME `ring_homomorphism(k:A ring,l:B ring) h`)))) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `x:B`; `(h:A->B) o (v:(1->num)->A)`]
      POLY_DIVIDES_X_MINUS_ROOT_EQ) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[ring_divides]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_DIVIDES_TRANS THEN
    EXISTS_TAC `(h:A->B) o (u:(1->num)->A)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:B ring`; `x:B`; `(h:A->B) o (u:(1->num)->A)`]
      POLY_DIVIDES_X_MINUS_ROOT_EQ) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ring_divides];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MINIMAL_POLYNOMIAL_ASSOCIATES_IRREDUCIBLE = prove
 (`!(h:A->B) k l p x.
        field_extension(k,l) h /\ ring_irreducible(poly_ring k (:1)) p /\
        x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l
        ==> algebraic_over(k,l) h x /\
            ring_associates (poly_ring k (:1))
              (minimal_polynomial(k,l) h x) p /\
            poly_deg k (minimal_polynomial(k,l) h x) = poly_deg k p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
  SUBGOAL_THEN `poly_extend (k,l) (h:A->B) (\v:1. x) p = ring_0 l`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval]; ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [REWRITE_TAC[algebraic_over] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `p:(1->num)->A` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ring_irreducible];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_NONUNIT_DIVIDES_IRREDUCIBLE THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_DIVIDES] THEN
    ASM_MESON_TAC[MINIMAL_POLYNOMIAL_IRREDUCIBLE; ring_irreducible];
    DISCH_TAC THEN MATCH_MP_TAC POLY_DEG_ASSOCIATES THEN
    EXISTS_TAC `(:1)` THEN
    ASM_MESON_TAC[field_extension; FIELD_IMP_INTEGRAL_DOMAIN]]);;

let RING_DIVIDES_IRREDUCIBLE_ROOT = prove
 (`!(h:A->B) k l p q x.
        field_extension(k,l) h /\ ring_irreducible(poly_ring k (:1)) p /\
        x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l /\
        q IN ring_carrier(poly_ring k (:1))
        ==> (ring_divides (poly_ring k (:1)) p q <=>
             poly_eval l (h o q) x = ring_0 l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`; `x:B`]
    MINIMAL_POLYNOMIAL_ASSOCIATES_IRREDUCIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`poly_ring k (:1):((1->num)->A)ring`;
                 `minimal_polynomial(k,l) (h:A->B) x`; `q:(1->num)->A`;
                 `p:(1->num)->A`; `q:(1->num)->A`] RING_ASSOCIATES_DIVIDES) THEN
  ASM_REWRITE_TAC[RING_ASSOCIATES_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_DIVIDES] THEN
  ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval;
               FIELD_EXTENSION_IMP_HOMOMORPHISM]);;

let MINIMAL_POLYNOMIAL_DEG_LE = prove
 (`!(h:A->B) k l x p.
        field_extension (k,l) h /\
        algebraic_over (k,l) h x /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = poly_0 k) /\
        poly_extend (k,l) h (\v. x) p = ring_0 l
        ==> poly_deg k (minimal_polynomial (k,l) h x) <= poly_deg k p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC POLY_DEG_DIVIDES_LE THEN
  EXISTS_TAC `(:1)` THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN;
               field_extension] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FIELD_IMP_INTEGRAL_DOMAIN; field_extension]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`; `p:(1->num)->A`]
    MINIMAL_POLYNOMIAL_DIVIDES) THEN
  ASM_REWRITE_TAC[]);;

let EXTENSION_DEGREE_SIMPLE = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> extension_degree
              (k,subring_generated l (x INSERT IMAGE h (ring_carrier k))) h =
            poly_deg k (minimal_polynomial (k,l) h x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = minimal_polynomial (k:A ring,l:B ring) h x` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `K = subring_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `(x:B) IN ring_carrier K /\
    !p. p IN ring_carrier(poly_ring k (:1))
        ==> (poly_extend (k,K) h (\v. x) p = ring_0 K <=>
             poly_extend (k:A ring,l:B ring) h (\v. x) p = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
      ASM_REWRITE_TAC[IN_INSERT];
      REPEAT STRIP_TAC THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC POLY_EXTEND_INTO_SUBRING_GENERATED THEN
      EXISTS_TAC `(:1)` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `s = {ring_pow K (x:B) n | n | n < poly_deg k (m:(1->num)->A)}` THEN
  SUBGOAL_THEN `ring_span (k:A ring,K:B ring) h s = ring_carrier K`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`; `m:(1->num)->A`; `x:B`]
      RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN) THEN
    ASM_SIMP_TAC[POLY_RING_CLAUSES] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "K" THEN
    SIMP_TAC[SUBRING_GENERATED_IDEMPOT; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE s /\ s SUBSET ring_carrier K /\
    CARD(s:B->bool) <= poly_deg k (m:(1->num)->A)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [SIMP_TAC[RING_POW; ASSUME `(x:B) IN ring_carrier K`];
      W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_LE o lhand o snd) THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`] RING_BASIS_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `b:B->bool`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ring_basis; ring_spanning]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`; `b:B->bool`; `s:B->bool`]
    RING_INDEPENDENT_LE_SPAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`; `b:B->bool`]
    EXTENSION_DEGREE_EQ_CARD_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`; `x:B`; `b:B->bool`;
                 `CARD(b:B->bool)`]
    FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT) THEN
  ASM_REWRITE_TAC[HAS_SIZE; SUBSET_REFL; CONJUNCT2 POLY_RING_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(1->num)->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`; `p:(1->num)->A`]
    MINIMAL_POLYNOMIAL_DEG_LE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC]);;

let MINIMAL_POLYNOMIAL_DEG_EQ_1 = prove
 (`!(h:A->B) k l x.
        field_extension(k,l) h /\ algebraic_over(k,l) h x
        ==> (poly_deg k (minimal_polynomial(k,l) h x) = 1 <=>
             x IN IMAGE h (ring_carrier k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    EXTENSION_DEGREE_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  ASM_SIMP_TAC[EXTENSION_DEGREE_EQ_1] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET o
    check (fun th -> concl th = `field_extension(k:A ring,l:B ring) h`)) THEN
  EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC THEN ASM SET_TAC[];
    DISCH_TAC THEN
    ASM_SIMP_TAC[SET_RULE `(x:B) IN s ==> x INSERT s = s`] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] SUBRING_RING_IMAGE) THEN
    REWRITE_TAC[ring_image] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]]);;

let MINIMAL_POLYNOMIAL_DEG_DIVIDES_EXTENSION_DEGREE = prove
 (`!(h:A->B) k l x.
        finite_extension (k,l) h /\ x IN ring_carrier l
        ==> poly_deg k (minimal_polynomial (k,l) h x) divides
            extension_degree (k,l) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `algebraic_over (k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION; algebraic_extension];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`h:A->B`; `I:B->B`; `k:A ring`;
    `subring_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))`;
    `l:B ring`] EXTENSION_DEGREE_TOWER_LAW) THEN
  ASM_SIMP_TAC[I_O_ID; EXTENSION_DEGREE_SIMPLE] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION;
                 FINITE_SIMPLE_ALGEBRAIC_EXTENSION] THEN
    MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_REFL; FIELD_SIMPLE_ALGEBRAIC_EXTENSION] THEN
    ASM_MESON_TAC[field_extension];
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL]]);;

let MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE = prove
 (`!(h:A->B) k l x.
        finite_extension (k,l) h /\ x IN ring_carrier l
        ==> poly_deg k (minimal_polynomial (k,l) h x) <=
            extension_degree (k,l) h`,
  MESON_TAC[MINIMAL_POLYNOMIAL_DEG_DIVIDES_EXTENSION_DEGREE; DIVIDES_LE;
            EXTENSION_DEGREE_EQ_0; FINITE_IMP_FIELD_EXTENSION]);;

(* ------------------------------------------------------------------------- *)
(* The power basis of a simple algebraic extension: if d is the degree of    *)
(* the minimal polynomial of x, the powers x^n with n < d form a basis of    *)
(* k(x) over k.                                                              *)
(* ------------------------------------------------------------------------- *)

let RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> ring_basis
              (k,subring_generated l (x INSERT IMAGE h (ring_carrier k))) h
              {ring_pow l x n | n |
               n < poly_deg k (minimal_polynomial (k,l) h x)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    EXTENSION_DEGREE_SIMPLE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = minimal_polynomial (k:A ring,l:B ring) h x` THEN
  ABBREV_TAC
   `K = subring_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  ABBREV_TAC
   `s = {ring_pow l (x:B) n | n | n < poly_deg k (m:(1->num)->A)}` THEN
  SUBGOAL_THEN `(s:B->bool) SUBSET ring_carrier K` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "K"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_POW_IN_SUBRING_GENERATED THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_span (k,K) (h:A->B) s = ring_carrier K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`;
                   `s:B->bool`] RING_SPAN_HOMOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_I; I_O_ID] THEN ANTS_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[I_DEF; RING_HOMOMORPHISM_INCLUSION];
      DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXPAND_TAC ["s"; "K"] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RING_MATROID_BASIS] THEN
  MATCH_MP_TAC MATROID_BASIS_SMALL_SPANNING THEN
  ASM_SIMP_TAC[RING_MATROID_SPANNING; RING_MATROID_FINITE_DIMENSIONAL] THEN
  ASM_REWRITE_TAC[ring_spanning] THEN
  UNDISCH_TAC
   `extension_degree (k,K) (h:A->B) = poly_deg k (m:(1->num)->A)` THEN
  ASM_SIMP_TAC[extension_degree; RING_MATROID_FINITE_DIMENSIONAL] THEN
  DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "s" THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_LE o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT]);;

let MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> {ring_pow l x n | n |
             n < poly_deg k (minimal_polynomial (k,l) h x)}
            HAS_SIZE poly_deg k (minimal_polynomial (k,l) h x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    EXTENSION_DEGREE_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXTENSION_DEGREE_EQ_CARD_BASIS THEN
  ASM_SIMP_TAC[RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS] THEN
  ASM_MESON_TAC[field_extension; FIELD_EXTENSION_IMP_HOMOMORPHISM;
                FINITE_IMP_FIELD_EXTENSION;
                FINITE_SIMPLE_ALGEBRAIC_EXTENSION]);;

let RING_INDEPENDENT_MINIMAL_POLYNOMIAL_POWERS = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> ring_independent (k,l) h
              {ring_pow l x n | n |
               n < poly_deg k (minimal_polynomial (k,l) h x)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS) THEN
  ASM_REWRITE_TAC[ring_basis] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL
   [`h:A->B`; `I:B->B`; `k:A ring`;
    `subring_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))`;
    `l:B ring`;
    `{ring_pow l (x:B) n | n |
      n < poly_deg k (minimal_polynomial (k,l) (h:A->B) x)}`]
    RING_INDEPENDENT_MONOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[IMAGE_I; I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[I_DEF; RING_MONOMORPHISM_INCLUSION] THEN
  ASM_MESON_TAC[RING_INDEPENDENT_IMP_SUBSET; FIELD_EXTENSION_IMP_HOMOMORPHISM;
                FINITE_IMP_FIELD_EXTENSION;
                FINITE_SIMPLE_ALGEBRAIC_EXTENSION]);;

let MINIMAL_POLYNOMIAL_POWERS_INDEPENDENT = prove
 (`!(h:A->B) k l x c.
        field_extension (k,l) h /\ algebraic_over (k,l) h x /\
        (!i. i < poly_deg k (minimal_polynomial (k,l) h x)
             ==> c i IN ring_carrier k) /\
        ring_sum l {i | i < poly_deg k (minimal_polynomial (k,l) h x)}
          (\i. ring_mul l (h(c i)) (ring_pow l x i)) = ring_0 l
        ==> !i. i < poly_deg k (minimal_polynomial (k,l) h x)
                ==> c i = ring_0 k`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `d = poly_deg k (minimal_polynomial (k,l) (h:A->B) x)` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    RING_INDEPENDENT_MINIMAL_POLYNOMIAL_POWERS) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RING_INDEPENDENT_FINITE] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`\n. ring_pow l (x:B) n`; `{n:num | n < d}`]
    CARD_IMAGE_EQ_INJ) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP RING_SUM_IMAGE th] THEN
    MP_TAC(REWRITE_RULE[INJECTIVE_ON_LEFT_INVERSE; IN_ELIM_THM] th)) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->num`) THEN
  DISCH_THEN(MP_TAC o SPEC `(c:num->A) o (g:B->num)`) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_DEF] THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC
   `ring_sum l {i | i < d}
      (\i. ring_mul l ((h:A->B) (c i)) (ring_pow l x i)) = ring_0 l` THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let POWER_INJECTIVE_BELOW_MINPOLY_DEG = prove
 (`!(k:A ring) (l:B ring) (h:A->B) x i j.
        field_extension (k,l) h /\
        algebraic_over (k,l) h x /\
        i < poly_deg k (minimal_polynomial (k,l) h x) /\
        j < poly_deg k (minimal_polynomial (k,l) h x)
        ==> (ring_pow l x i = ring_pow l x j <=> i = j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[HAS_SIZE; ETA_AX] THEN
  ABBREV_TAC `d = poly_deg k (minimal_polynomial (k,l) (h:A->B) x)` THEN
  MP_TAC(ISPECL [`ring_pow (l:B ring) x`; `{n:num | n < d}`]
    CARD_IMAGE_EQ_INJ) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

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

let ALGEBRAIC_OVER_POW_EQ = prove
 (`!(h:A->B) k l x n.
        field_extension (k,l) h /\ x IN ring_carrier l /\ ~(n = 0)
        ==> (algebraic_over (k,l) h (ring_pow l x n) <=>
             algebraic_over (k,l) h x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[ALGEBRAIC_OVER_POW] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_pow l x n:B`]
    FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_pow l x n:B`]
    FIELD_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = subring_generated l
     (ring_pow l x n INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`;
                 `x:B`] ALGEBRAIC_OVER_TRANS) THEN
  REWRITE_TAC[I_O_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION] THEN
  SUBGOAL_THEN `field_extension (K,l) (I:B->B)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
    ASM_REWRITE_TAC[FIELD_EXTENSION_REFL] THEN ASM_MESON_TAC[field_extension];
    ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  ASM_SIMP_TAC[ALGEBRAIC_OVER_ALT; FIELD_EXTENSION_IMP_MONOMORPHISM] THEN
  EXISTS_TAC `poly_sub K (poly_pow K (poly_var K one) n)
               (poly_const K (ring_pow l x n)):(1->num)->B` THEN
  SUBGOAL_THEN `ring_pow l (x:B) n IN ring_carrier K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    ASM_SIMP_TAC[RING_POW; IN_INSERT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
               RING_POLYNOMIAL_CONST; POLY_DEG_SUB_CONST; POLY_DEG_VAR_POW;
               FIELD_NONTRIVIAL; POLY_EXTEND_SUB; POLY_EXTEND_VARPOW;
               POLY_EXTEND_CONST; I_THM; RING_SUB_REFL; RING_POW]);;

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

let FIELD_EXTENSION_SUBRING_GENERATED_FINITE = prove
 (`!(l:A ring) s.
        field l /\ FINITE(ring_carrier l)
        ==> field_extension(subring_generated l s,l) I`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[field_extension] THEN
  ASM_REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] RING_MONOMORPHISM_INCLUSION] THEN
  MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN
  ASM_SIMP_TAC[FINITE_SUBRING_GENERATED; INTEGRAL_DOMAIN_SUBRING_GENERATED;
               FIELD_IMP_INTEGRAL_DOMAIN]);;

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

let FINITE_FIELD_PRIMITIVE_ELEMENT = prove
 (`!(h:A->B) k l.
        field l /\ FINITE(ring_carrier l)
        ==> ?a. a IN ring_carrier l /\
                subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:B ring` FINITE_INTEGRAL_DOMAIN_CYCLIC) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SUBRING_GENERATED_SUPERSET; SUBSET] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:B = ring_0 l` THEN
  ASM_REWRITE_TAC[RING_0_IN_SUBRING_GENERATED] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC RING_POW_IN_SUBRING_GENERATED THEN
  MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN ASM_REWRITE_TAC[IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* Finite fields and their subfields. In a finite integral domain with q     *)
(* elements x^q = x for all x, and for a finite field k with q elements and  *)
(* a homomorphism h from k into a ring l the maps x |-> x^(q^i) are          *)
(* endomorphisms of l fixing the image of k. In an integral domain x^m = x   *)
(* has at most m solutions when m >= 2, so a finite subfield s of a domain   *)
(* is the set of solutions of x^q = x, q the number of elements of s. A      *)
(* finite extension l of a finite field k has |k|^[l:k] elements; hence an   *)
(* intermediate field s of a finite extension of finite fields is the set of *)
(* solutions of x^(|k|^d) = x with d = [s:k], so it is determined by d.      *)
(* ------------------------------------------------------------------------- *)

let FINITE_INTEGRAL_DOMAIN_POW_CARD = prove
 (`!r x:A.
        integral_domain r /\ FINITE(ring_carrier r) /\ x IN ring_carrier r
        ==> ring_pow r x (CARD(ring_carrier r)) = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `field(r:A ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_INTEGRAL_DOMAIN_IMP_FIELD]; ALL_TAC] THEN
  ASM_CASES_TAC `x:A = ring_0 r` THENL
   [ASM_SIMP_TAC[RING_POW_ZERO; CARD_EQ_0; RING_CARRIER_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(ring_carrier r:A->bool) = CARD(ring_carrier r DELETE ring_0 r) + 1`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE; RING_0] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n = n - 1 + 1`) THEN
    ASM_SIMP_TAC[CARD_EQ_0; RING_CARRIER_NONEMPTY];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_POW_ADD; RING_POW_1] THEN
  SUBGOAL_THEN
   `ring_pow r x (CARD(ring_carrier(r:A ring) DELETE ring_0 r)) = ring_1 r`
   (fun th -> ASM_SIMP_TAC[th; RING_MUL_LID]) THEN
  MATCH_MP_TAC(ISPEC `r:A ring` INTEGRAL_DOMAIN_MUL_RCANCEL) THEN
  EXISTS_TAC `ring_product r (ring_carrier r DELETE ring_0 r) (\y:A. y)` THEN
  ASM_SIMP_TAC[RING_PRODUCT; RING_POW; RING_1; RING_MUL_LID; FINITE_DELETE;
               INTEGRAL_DOMAIN_PRODUCT_EQ_0; GSYM RING_PRODUCT_LMUL;
               IN_DELETE] THEN
  CONJ_TAC THENL
   [MESON_TAC[]; MATCH_MP_TAC RING_PRODUCT_EQ_GENERAL_INVERSES] THEN
  EXISTS_TAC `\y:A. ring_mul r x y` THEN
  EXISTS_TAC `\y:A. ring_mul r (ring_inv r x) y` THEN
  ASM_SIMP_TAC[IN_DELETE; RING_MUL; RING_INV; FIELD_MUL_EQ_0; FIELD_INV_EQ_0;
               RING_MUL_ASSOC; FIELD_MUL_LINV; FIELD_MUL_RINV; RING_MUL_LID]);;

let RING_ENDOMORPHISM_POW_CARD = prove
 (`!k:A ring l:B ring h i.
        field k /\ FINITE(ring_carrier k) /\ ring_homomorphism(k,l) h
        ==> ring_endomorphism l
              (\x. ring_pow l x (CARD(ring_carrier k) EXP i)) /\
            !a. a IN ring_carrier k
                ==> ring_pow l (h a) (CARD(ring_carrier k) EXP i) = h a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW th)]) THEN
    AP_TERM_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[EXP; RING_POW_1] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[GSYM RING_POW_POW; FINITE_INTEGRAL_DOMAIN_POW_CARD;
                 FIELD_IMP_INTEGRAL_DOMAIN]] THEN
  ASM_CASES_TAC `trivial_ring(l:B ring)` THENL
   [ASM_SIMP_TAC[ring_endomorphism; RING_HOMOMORPHISM_FROM_TRIVIAL_RING] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `z:B` o GEN_REWRITE_RULE I [TRIVIAL_RING]) THEN
    MP_TAC(ISPEC `l:B ring` RING_0) THEN
    MP_TAC(ISPECL [`l:B ring`; `z:B`;
                   `CARD(ring_carrier(k:A ring)) EXP i`] RING_POW) THEN
    ASM_REWRITE_TAC[IN_SING; IMAGE_CLAUSES] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_char(l:B ring) = ring_char(k:A ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE;
                  FIELD_RING_HOMOMORPHISM_MONOMORPHISM];
    ALL_TAC] THEN
  SUBGOAL_THEN `prime(ring_char(k:A ring))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_INTEGRAL_DOMAIN_CHAR; FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:A ring` FINITE_INTEGRAL_DOMAIN_SIZE) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `m:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p = ring_char(l:B ring)` SUBST1_TAC THENL
   [MP_TAC(ISPEC `k:A ring` RING_CHAR_DIVIDES_ORDER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP PRIME_DIVEXP o
      CONJ (ASSUME `prime(ring_char(k:A ring))`)) THEN
    ASM_SIMP_TAC[DIVIDES_PRIME_PRIME] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    REWRITE_TAC[EXP_EXP] THEN
    MATCH_MP_TAC RING_ENDOMORPHISM_FROBENIUS_ITERATE THEN ASM_REWRITE_TAC[]]);;

(* In an integral domain a nonzero solution of x^m = x has x^(m - 1) = 1.    *)
let RING_POW_FIXPOINTS_BOUND = prove
 (`!(r:A ring) m.
        integral_domain r /\ 2 <= m
        ==> FINITE {x | x IN ring_carrier r /\ ring_pow r x m = x} /\
            CARD {x | x IN ring_carrier r /\ ring_pow r x m = x} <= m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `m - 1`] ROOTS_OF_UNITY_BOUND) THEN
  ABBREV_TAC
   `u = {x:A | x IN ring_carrier r /\ ring_pow r x (m - 1) = ring_1 r}` THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC(MESON[FINITE_SUBSET; CARD_SUBSET; LE_TRANS]
   `!t:A->bool. s SUBSET t /\ FINITE t /\ CARD t <= m
                ==> FINITE s /\ CARD s <= m`) THEN
  EXISTS_TAC `ring_0 r INSERT u:A->bool` THEN
  ASM_SIMP_TAC[FINITE_INSERT; CARD_CLAUSES] THEN CONJ_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x:A = ring_0 r` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPEC `r:A ring` INTEGRAL_DOMAIN_MUL_LCANCEL) THEN
    EXISTS_TAC `x:A` THEN
    ASM_SIMP_TAC[RING_POW; RING_1; RING_MUL_RID; GSYM(CONJUNCT2 ring_pow);
                 ARITH_RULE `2 <= m ==> SUC(m - 1) = m`];
    COND_CASES_TAC THEN ASM_ARITH_TAC]);;

(* The elements of s satisfy x^|s| = x, and there are at most |s| solutions. *)
let FINITE_SUBFIELD_EXPLICIT = prove
 (`!(l:A ring) s.
        integral_domain l /\ s subfield_of l /\ FINITE s
        ==> s = {x | x IN ring_carrier l /\ ring_pow l x (CARD s) = x}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SUBFIELD_OF_IMP_10) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [subfield_of]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [subring_of]) THEN
  SUBGOAL_THEN `!x:A. x IN s ==> ring_pow l x (CARD s) = x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subring_generated l (s:A->bool)`; `x:A`]
      FINITE_INTEGRAL_DOMAIN_POW_CARD) THEN
    ASM_SIMP_TAC[RING_POW_SUBRING_GENERATED; FIELD_IMP_INTEGRAL_DOMAIN;
                 CARRIER_SUBRING_GENERATED_SUBRING];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= CARD(s:A->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{ring_0 l:A,ring_1 l}`; `s:A->bool`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:A ring`; `CARD(s:A->bool)`] RING_POW_FIXPOINTS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[];
    DISCH_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
    ASM_SIMP_TAC[CARD_SUBSET]]);;

let CARD_EXTENSION_DEGREE = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> CARD(ring_carrier l) =
            CARD(ring_carrier k) EXP extension_degree(k,l) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `finite_extension(k,l) (h:A->B)` MP_TAC THENL
   [ASM_SIMP_TAC[FINITE_EQ_FIELD_EXTENSION]; ALL_TAC] THEN
  REWRITE_TAC[FINITE_EXTENSION_BASIS] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B->bool`]
    EXTENSION_DEGREE_EQ_CARD_BASIS) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CARD_FINITE_EXTENSION THEN
  ASM_MESON_TAC[FINITE_RING_MONOMORPHIC_PREIMAGE]);;

(* An intermediate field s has |k|^[s:k] elements (CARD_EXTENSION_DEGREE).   *)
let FINITE_FIELD_INTERMEDIATE_FIELD_EXPLICIT = prove
 (`!(h:A->B) k l s.
        field_extension(k,l) h /\ FINITE(ring_carrier l) /\
        s subfield_of l /\ IMAGE h (ring_carrier k) SUBSET s
        ==> s = {x | x IN ring_carrier l /\
                     ring_pow l x
                      (CARD(ring_carrier k) EXP
                       extension_degree(k,subfield_generated l s) h) = x}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `subfield_generated l (s:B->bool)`]
    CARD_EXTENSION_DEGREE) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_INTO_SUBFIELD_GENERATED;
               CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  SUBGOAL_THEN `FINITE(s:B->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; SUBFIELD_OF_IMP_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC FINITE_SUBFIELD_EXPLICIT THEN
  ASM_MESON_TAC[field_extension; FIELD_IMP_INTEGRAL_DOMAIN]);;

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

let MINIMAL_POLYNOMIAL_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m x.
        x IN ring_carrier l /\
        ring_homomorphism(k,l) f /\
        ring_monomorphism(l,m) g
        ==> minimal_polynomial (k,m) (g o f) (g x) =
            minimal_polynomial (k,l) f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[minimal_polynomial] THEN
  ASM_SIMP_TAC[ALGEBRAIC_OVER_MONOMORPHIC_IMAGE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `p:(1->num)->A` THEN
  ASM_CASES_TAC `p IN ring_carrier(poly_ring (k:A ring) (:1))` THEN
  ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 3 AP_TERM_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:C ring`; `f:A->B`; `(:1)`;
                 `(\v:1. x:B)`; `g:B->C`; `p:(1->num)->A`]
    POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE;
               IN_UNIV] THEN
  SUBGOAL_THEN `(g:B->C) o (\v:1. x) = (\v. g x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; POLY_EXTEND]);;

let MINIMAL_POLYNOMIAL_SUBRING_GENERATED = prove
 (`!(h:A->B) k l s x.
        ring_homomorphism(k,l) h /\ IMAGE h (ring_carrier k) SUBSET s /\
        x IN ring_carrier l /\ x IN s
        ==> minimal_polynomial (k,subring_generated l s) h x =
            minimal_polynomial (k,l) h x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                 `subring_generated l (s:B->bool)`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL_MONOMORPHIC_IMAGE) THEN
  REWRITE_TAC[I_O_ID; I_THM] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_SIMP_TAC[SUBRING_GENERATED_INC_GEN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] RING_MONOMORPHISM_INCLUSION]]);;

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
          ==> ?f. (!n:num. f n IN s) /\ (!n. P (f n) {f i | i < n})`,
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
              (IMAGE (f:A->B) (ring_carrier k) UNION
               {(y:num->B) i | i < n}))` THEN
    SUBGOAL_THEN
     `(!n. A n subfield_of (l:B ring)) /\
      (!n. IMAGE (f:A->B) (ring_carrier k) SUBSET A n) /\
      (!m n:num. m < n ==> A m PSUBSET A n)`
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
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET)) THEN
      ASM SET_TAC[];
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

(* ------------------------------------------------------------------------- *)
(* Algebraically closed fields and algebraic closures.                       *)
(* ------------------------------------------------------------------------- *)

let algebraically_closed_field = new_definition
 `algebraically_closed_field(k:A ring) <=>
        field k /\
        !p. p IN ring_carrier(poly_ring k (:1)) /\ ~(poly_deg k p = 0)
            ==> ?x. x IN ring_carrier k /\ poly_eval k p x = ring_0 k`;;

let ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD = prove
 (`!k:A ring. algebraically_closed_field k ==> field k`,
  SIMP_TAC[algebraically_closed_field]);;

let ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE = prove
 (`!(k:A ring) (l:B ring) f.
        ring_isomorphism(k,l) f /\ algebraically_closed_field k
        ==> algebraically_closed_field l`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g:B->A` MP_TAC o
    GEN_REWRITE_RULE I [ring_isomorphism]) THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN STRIP_TAC THEN
  REWRITE_TAC[algebraically_closed_field] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ISOMORPHIC_RING_FIELDNESS; isomorphic_ring]; ALL_TAC] THEN
  X_GEN_TAC `p:(1->num)->B` THEN STRIP_TAC THEN SUBGOAL_THEN
   `(g:B->A) o (p:(1->num)->B) IN ring_carrier(poly_ring k (:1)) /\
    poly_deg (k:A ring) ((g:B->A) o (p:(1->num)->B)) =
    poly_deg (l:B ring) p` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_RING_POLYNOMIAL_CARRIER_COMPOSE;
      RING_ISOMORPHISM_IMP_HOMOMORPHISM; POLY_DEG_MONOMORPHIC_IMAGE;
      RING_POLYNOMIAL; RING_ISOMORPHISM_IMP_MONOMORPHISM]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g:B->A) o (p:(1->num)->B)`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:A->B) y` THEN
  SUBGOAL_THEN `(f:A->B) y IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM;
                   ring_homomorphism; SUBSET; FUN_IN_IMAGE];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(f:A->B) o (g:B->A) o (p:(1->num)->B) = p` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    X_GEN_TAC `m:1->num` THEN FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC
     `(p:(1->num)->B) IN ring_carrier(poly_ring (l:B ring) (:1))` THEN
    REWRITE_TAC[POLY_RING; IN_ELIM_THM; SUBSET_UNIV;
                ring_polynomial; ring_powerseries] THEN
    MESON_TAC[]; ALL_TAC] THEN MP_TAC(ISPECL
   [`k:A ring`; `l:B ring`; `y:A`; `f:A->B`; `(g:B->A) o (p:(1->num)->B)`]
   POLY_EVAL_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `ring_isomorphism(k:A ring,l:B ring) (f:A->B)` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0
      (MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM th)]));;

let ISOMORPHIC_RING_ALGEBRAICALLY_CLOSED_FIELD = prove
 (`!(k:A ring) (l:B ring).
        k isomorphic_ring l
        ==> (algebraically_closed_field k <=> algebraically_closed_field l)`,
  REWRITE_TAC[isomorphic_ring] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:B->A` o
    GEN_REWRITE_RULE I [ring_isomorphism]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [RING_ISOMORPHISMS_ISOMORPHISM]) THEN
  ASM_MESON_TAC[ALGEBRAICALLY_CLOSED_FIELD_ISOMORPHIC_IMAGE]);;

let ALGEBRAICALLY_CLOSED_FIELD_IMP_INFINITE = prove
 (`!k:A ring. algebraically_closed_field k ==> INFINITE(ring_carrier k)`,
  GEN_TAC THEN REWRITE_TAC[algebraically_closed_field] THEN
  STRIP_TAC THEN REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~trivial_ring (k:A ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_IMP_NONTRIVIAL_RING]; ALL_TAC] THEN
  ABBREV_TAC `P = ring_product (poly_ring (k:A ring) (:1)) (ring_carrier k)
        (\a. poly_sub k (poly_var k one) (poly_const k a))` THEN SUBGOAL_THEN
   `P IN ring_carrier(poly_ring (k:A ring) (:1))` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[RING_PRODUCT]; ALL_TAC] THEN SUBGOAL_THEN
   `~(P = ring_0(poly_ring (k:A ring) (:1)))` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRODUCT_EQ_0;
                 INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN] THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    X_GEN_TAC `a:A` THEN DISCH_TAC THEN REWRITE_TAC[POLY_RING_CLAUSES] THEN
    ASM_SIMP_TAC[POLY_X_MINUS_A_NONZERO]; ALL_TAC] THEN SUBGOAL_THEN
   `!x:A. x IN ring_carrier k ==> poly_eval k P x = ring_0 k` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    ASM_SIMP_TAC[POLY_EVAL_RING_PRODUCT; POLY_X_MINUS_A_IN_CARRIER] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRODUCT_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[POLY_EVAL_SUB; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST;
                 POLY_EVAL_VAR; POLY_EVAL_CONST; RING_SUB_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `~(poly_deg (k:A ring) (P:(1->num)->A) = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `P:(1->num)->A`] POLY_DEG_EQ_0) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(c:A) = ring_0 k` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `ring_0 (k:A ring)`) THEN
      REWRITE_TAC[RING_0] THEN ASM_SIMP_TAC[POLY_EVAL_CONST];
      ASM_MESON_TAC[POLY_CONST_0; POLY_RING_CLAUSES]]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `poly_add (k:A ring) P (poly_1 k:(1->num)->A)`) THEN
  REWRITE_TAC[NOT_IMP; NOT_EXISTS_THM] THEN CONJ_TAC THENL [CONJ_TAC THENL
     [REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN MATCH_MP_TAC
        RING_POLYNOMIAL_ADD THEN ASM_REWRITE_TAC[RING_POLYNOMIAL;
          RING_POLYNOMIAL_1];
      MP_TAC(ISPECL [`k:A ring`; `P:(1->num)->A`;
                     `poly_1 (k:A ring):(1->num)->A`] POLY_DEG_ADD) THEN
      ASM_REWRITE_TAC[RING_POLYNOMIAL; RING_POLYNOMIAL_1; POLY_DEG_1] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `x:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[POLY_EVAL_ADD; RING_POLYNOMIAL; RING_POLYNOMIAL_1;
                 POLY_EVAL_1; RING_ADD_LZERO; RING_1;
                 GSYM TRIVIAL_RING_10]]);;

let ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION = prove
 (`!(k:A ring) (l:B ring) (f:A->B).
        algebraically_closed_field k /\ algebraic_extension(k,l) f
        ==> ring_isomorphism(k,l) f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[algebraically_closed_field; ALGEBRAIC_EXTENSION_ALT] THEN
  STRIP_TAC THEN SUBGOAL_THEN
    `ring_monomorphism(k:A ring,l:B ring) (f:A->B) /\ field(l:B ring) /\
     ring_homomorphism(k:A ring,l:B ring) (f:A->B)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[field_extension;
     RING_MONOMORPHISM_IMP_HOMOMORPHISM]; ALL_TAC] THEN SUBGOAL_THEN
   `ring_homomorphism(poly_ring (k:A ring) (:1), poly_ring (l:B ring) (:1))
                      (\p:(1->num)->A. (f:A->B) o p)` ASSUME_TAC THENL
  [MATCH_MP_TAC RING_HOMOMORPHISM_POLY_RINGS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RING_ISOMORPHISM_MONOMORPHISM_ALT] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n (x:B) (p:(1->num)->A). x IN ring_carrier l /\
      p IN ring_carrier(poly_ring (k:A ring) (:1)) /\
      ~(p = ring_0(poly_ring k (:1))) /\
      poly_eval (l:B ring) ((f:A->B) o p) x = ring_0 l /\ poly_deg k p = n
      ==> x IN IMAGE f (ring_carrier k)` MP_TAC THENL
  [MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   MAP_EVERY X_GEN_TAC [`x:B`; `p:(1->num)->A`] THEN STRIP_TAC THEN
   SUBGOAL_THEN `ring_polynomial (k:A ring) (p:(1->num)->A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN ASM_CASES_TAC `n = 0` THENL
   [(* Base case: n = 0, p is nonzero constant, contradiction *)
    FIRST_ASSUM(MP_TAC o MATCH_MP POLY_DEG_EQ_0) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(c = ring_0 (k:A ring))` ASSUME_TAC THENL
     [ASM_MESON_TAC[POLY_CONST_0; POLY_RING_CLAUSES]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:A->B) c = ring_0 (l:B ring)` ASSUME_TAC THENL
    [UNDISCH_TAC `poly_eval (l:B ring) ((f:A->B) o (p:(1->num)->A)) (x:B) =
       ring_0 l` THEN SUBGOAL_THEN
       `(f:A->B) c IN ring_carrier (l:B ring)` ASSUME_TAC THENL
      [ASM_MESON_TAC[ring_homomorphism; SUBSET; IN_IMAGE]; ALL_TAC] THEN
     SUBGOAL_THEN
       `(f:A->B) o (poly_const (k:A ring) c:(1->num)->A) =
        (poly_const (l:B ring) (f c):(1->num)->B)` ASSUME_TAC THENL
      [MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_CONST THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
     ASM_SIMP_TAC[POLY_EVAL_CONST];
     ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `f:A->B`; `c:A`]
      RING_MONOMORPHISM_EQ_0) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN (* Inductive step: n >= 1 *) (* Get root from ACF *)
   FIRST_ASSUM(MP_TAC o SPEC `p:(1->num)->A`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
   (* Factor p = (X-y) * q *) SUBGOAL_THEN `?q:(1->num)->A.
       q IN ring_carrier(poly_ring (k:A ring) (:1)) /\
       p:(1->num)->A = poly_mul k
           (poly_sub k (poly_var k one) (poly_const k (y:A))) q`
    (X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`k:A ring`; `y:A`; `p:(1->num)->A`]
      POLY_DIVIDES_X_MINUS_ROOT) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ring_divides; POLY_RING_CLAUSES;
                IN_ELIM_THM; SUBSET_UNIV] THEN
    MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `ring_polynomial (k:A ring) (q:(1->num)->A) /\
    poly_sub k (poly_var k one) (poly_const k (y:A)):(1->num)->A
     IN ring_carrier(poly_ring (k:A ring) (:1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[RING_POLYNOMIAL];
     MATCH_MP_TAC POLY_X_MINUS_A_IN_CARRIER THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `~(q:(1->num)->A = poly_0 (k:A ring))` ASSUME_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN
     `(p:(1->num)->A) = poly_0 (k:A ring)` MP_TAC THENL
     [ASM_REWRITE_TAC[POLY_CLAUSES] THEN
      MATCH_MP_TAC RING_MUL_RZERO THEN MATCH_MP_TAC RING_SUB THEN
      REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST];
      REWRITE_TAC[POLY_CLAUSES] THEN ASM_MESON_TAC[]]; ALL_TAC] THEN
   SUBGOAL_THEN `poly_deg (k:A ring) (q:(1->num)->A) < n` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `y:A`; `q:(1->num)->A`]
      POLY_DEG_MUL_X_MINUS_A) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    UNDISCH_TAC `poly_deg (k:A ring) (p:(1->num)->A) = n` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(f:A->B) o (p:(1->num)->A) = poly_mul (l:B ring)
       (f o poly_sub k (poly_var k one) (poly_const k (y:A)))
       (f o (q:(1->num)->A))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_MUL THEN
    ASM_SIMP_TAC[RING_POWERSERIES_SUB; RING_POWERSERIES_VAR;
                 RING_POWERSERIES_CONST;
                 RING_POLYNOMIAL_IMP_POWERSERIES]; ALL_TAC] THEN
   (* f o (X-y) = X_l - const_l(f y) *)
   SUBGOAL_THEN `(f:A->B) o poly_sub (k:A ring) (poly_var k one)
                            (poly_const k (y:A)) =
     poly_sub (l:B ring) (poly_var l one)
                          (poly_const l ((f:A->B) y))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `f:A->B`;
      `poly_var k one:(1->num)->A`; `poly_const k (y:A):(1->num)->A`]
     POLY_COMPOSE_HOMOMORPHISM_SUB) THEN
    ASM_SIMP_TAC[RING_POWERSERIES_VAR; RING_POWERSERIES_CONST] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
      `((f:A->B) o (poly_var (k:A ring) one:(1->num)->A) =
        (poly_var (l:B ring) one:(1->num)->B)) /\
       ((f:A->B) o (poly_const (k:A ring) (y:A):(1->num)->A) =
        (poly_const (l:B ring) (f y):(1->num)->B))`
      (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_VAR THEN
     ASM_REWRITE_TAC[];
     MATCH_MP_TAC POLY_COMPOSE_HOMOMORPHISM_CONST THEN
     ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   SUBGOAL_THEN `(f:A->B) y IN ring_carrier (l:B ring) /\
    ring_polynomial (l:B ring) ((f:A->B) o (q:(1->num)->A))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ring_homomorphism; SUBSET; IN_IMAGE;
     RING_POLYNOMIAL; IN_RING_POLYNOMIAL_CARRIER_COMPOSE]; ALL_TAC] THEN
   SUBGOAL_THEN `ring_sub (l:B ring) (x:B) ((f:A->B) y) = ring_0 l \/
     poly_eval (l:B ring) ((f:A->B) o (q:(1->num)->A)) (x:B) = ring_0 l`
    MP_TAC THENL [MP_TAC(ISPECL [`l:B ring`;
      `ring_sub (l:B ring) (x:B) ((f:A->B) y)`;
      `poly_eval (l:B ring) ((f:A->B) o (q:(1->num)->A)) (x:B)`]
     FIELD_MUL_EQ_0) THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
    [CONJ_TAC THENL [MATCH_MP_TAC RING_SUB THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[POLY_EVAL]]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN UNDISCH_TAC
     `poly_eval (l:B ring) ((f:A->B) o (p:(1->num)->A)) (x:B) =
      ring_0 l` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[POLY_EVAL_MUL; POLY_EVAL_SUB; POLY_EVAL_VAR;
                  POLY_EVAL_CONST; RING_POLYNOMIAL_VAR;
                  RING_POLYNOMIAL_CONST; RING_POLYNOMIAL_SUB;
                  RING_POLYNOMIAL_MUL]; ALL_TAC] THEN
   (* Case split *) DISCH_THEN(DISJ_CASES_TAC) THENL
   [(* Case 1: ring_sub l x (f y) = 0, so x = f y *)
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RING_SUB_EQ_0];
    FIRST_X_ASSUM(MP_TAC o SPEC `poly_deg (k:A ring) (q:(1->num)->A)`) THEN
      ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:B`; `q:(1->num)->A`]) THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES]]; DISCH_TAC THEN
   REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `p0:(1->num)->A` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPECL
    [`poly_deg (k:A ring) (p0:(1->num)->A)`; `x:B`; `p0:(1->num)->A`]) THEN
   ASM_REWRITE_TAC[]]);;

let ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES = prove
 (`!k:A ring.
        algebraically_closed_field k <=>
        field k /\
        !p. ring_irreducible (poly_ring k (:1)) p ==> poly_deg k p = 1`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[algebraically_closed_field] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IRREDUCIBLE_ROOT_IMP_DEG_EQ_1 THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:(1->num)->A`) THEN
    ASM_MESON_TAC[FIELD_POLY_DEG_EQ_0; ring_irreducible; POLY_RING;
                  FIELD_IMP_INTEGRAL_DOMAIN];
    STRIP_TAC THEN ASM_REWRITE_TAC[algebraically_closed_field] THEN
    X_GEN_TAC `p:(1->num)->A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `integral_domain (k:A ring) /\
      ~((p:(1->num)->A) = ring_0 (poly_ring k (:1)))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN];
        ASM_MESON_TAC[POLY_DEG_0; POLY_RING_CLAUSES]]; ALL_TAC] THEN
    SUBGOAL_THEN `~ring_unit (poly_ring (k:A ring) (:1)) (p:(1->num)->A)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[RING_UNIT_POLY_DOMAIN] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(poly_deg (k:A ring) (p:(1->num)->A) = 0)` THEN
      ASM_REWRITE_TAC[POLY_DEG_CONST]; ALL_TAC] THEN
    MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `p:(1->num)->A`]
      NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_POLY_RING] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN MATCH_MP_TAC PID_IMP_UFD THEN
      ASM_SIMP_TAC[PID_POLY_RING]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:A ring`; `q:(1->num)->A`] POLY_DEG_1_ROOT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ring_irreducible; RING_POLYNOMIAL;
                     POLY_RING_CLAUSES; IN_ELIM_THM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `k:A ring`;
      `\(pp:(1->num)->A). poly_eval (k:A ring) pp (x:A)`;
      `q:(1->num)->A`; `p:(1->num)->A`] RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_EVAL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[RING_DIVIDES_ZERO]]);;

let IRREDUCIBLE_ALGEBRAICALLY_CLOSED_FIELD = prove
 (`!(k:A ring) p.
        algebraically_closed_field k
        ==> (ring_irreducible (poly_ring k (:1)) p <=>
             p IN ring_carrier (poly_ring k (:1)) /\ poly_deg k p = 1)`,
  MESON_TAC[POLY_DEG_1_IMP_IRREDUCIBLE; RING_IRREDUCIBLE_IN_CARRIER;
            ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES]);;

let ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS = prove
 (`!(k:A ring) p.
        algebraically_closed_field k /\
        p IN ring_carrier(poly_ring k (:1))
        ==> poly_splits k p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `p:(1->num)->A = poly_0 k` THEN
  ASM_REWRITE_TAC[POLY_SPLITS_0] THEN
  SUBGOAL_THEN `field(k:A ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:(1->num)->A`] POLY_SPLITS_EQ_IRREDUCIBLES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES]) THEN
  MESON_TAC[]);;

let ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY = prove
 (`!(k:A ring) n.
        algebraically_closed_field k /\ ~(ring_char k divides n)
        ==> {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} HAS_SIZE n /\
            ?z. z IN ring_carrier k /\ ring_order k z = n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC PRIMITIVE_ROOT_OF_UNITY_EXISTS THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
               FIELD_IMP_INTEGRAL_DOMAIN] THEN
  MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
  ASM_REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
  SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
           RING_POLYNOMIAL_1]);;

(* In an algebraically closed field every element has an n-th root for n     *)
(* nonzero (ALGEBRAICALLY_CLOSED_FIELD_NTH_ROOT).                            *)
let ALGEBRAICALLY_CLOSED_FIELD_NTH_ROOT = prove
 (`!(k:A ring) c n.
        algebraically_closed_field k /\ c IN ring_carrier k /\ ~(n = 0)
        ==> ?d. d IN ring_carrier k /\ ring_pow k d n = c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN
   `ring_polynomial k (poly_pow k (poly_var k one) n:(1->num)->A) /\
    ring_polynomial k (poly_const k (ring_neg k c):(1->num)->A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_CONST; RING_NEG];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `poly_add k (poly_pow k (poly_var k one) n)
               (poly_const k (ring_neg k c)):(1->num)->A` o
    CONJUNCT2 o GEN_REWRITE_RULE I [algebraically_closed_field]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_ADD] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_ADD o
      lhand o rand o snd) THEN
    ASM_SIMP_TAC[POLY_DEG_VAR_POW; FIELD_NONTRIVIAL; POLY_DEG_CONST] THEN
    DISCH_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:A` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th))) THEN
    ASM_SIMP_TAC[POLY_EVAL_ADD; POLY_EVAL_POW; POLY_EVAL_VAR;
                 POLY_EVAL_CONST; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_CONST; RING_NEG] THEN
    REWRITE_TAC[GSYM ring_sub] THEN
    ASM_SIMP_TAC[RING_SUB_EQ_0; RING_POW]]);;

(* If the characteristic of an algebraically closed field k does not divide  *)
(* n, a monomorphism from k into a field l maps the n-th roots of unity of k *)
(* onto those of l (ALGEBRAICALLY_CLOSED_FIELD_ROOTS_OF_UNITY_IMAGE).        *)
let ALGEBRAICALLY_CLOSED_FIELD_ROOTS_OF_UNITY_IMAGE = prove
 (`!(k:A ring) (l:B ring) f n.
        algebraically_closed_field k /\ ~(ring_char k divides n) /\
        field l /\ ring_monomorphism(k,l) f
        ==> IMAGE f {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} =
            {y | y IN ring_carrier l /\ ring_pow l y n = ring_1 l}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `u = {x:A | x IN ring_carrier k /\ ring_pow k x n = ring_1 k}` THEN
  SUBGOAL_THEN `~(n:num = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`]
    ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`l:B ring`; `n:num`] ROOTS_OF_UNITY_BOUND) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; LE_1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:A->B) u HAS_SIZE n` MP_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[ring_monomorphism];
    REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET_LE THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "u" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW
   (ASSUME `ring_homomorphism(k:A ring,l:B ring) f`))] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_HOMOMORPHISM_1]);;

let ALGEBRAICALLY_CLOSED_FIELD_EQ_POLY_SPLITS = prove
 (`!k:A ring.
        algebraically_closed_field k <=>
        field k /\
        !p. p IN ring_carrier(poly_ring k (:1)) ==> poly_splits k p`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
              ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS];
    STRIP_TAC THEN
    REWRITE_TAC[ALGEBRAICALLY_CLOSED_FIELD_EQ_IRREDUCIBLES] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:(1->num)->A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `q IN ring_carrier(poly_ring (k:A ring) (:1)) /\ ~(q = poly_0 k)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ring_irreducible; RING_IRREDUCIBLE_IN_CARRIER;
                    POLY_RING_CLAUSES];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:(1->num)->A`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `q:(1->num)->A`]
      POLY_SPLITS_EQ_IRREDUCIBLES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_MESON_TAC[RING_DIVIDES_REFL; ring_irreducible]]);;

let ALGEBRAICALLY_CLOSED_FIELD_EQ_POLY_SPLITS_ALT = prove
 (`!k:A ring.
        algebraically_closed_field k <=>
        field k /\
        (!p. p IN ring_carrier (poly_ring k (:1)) /\ ~(poly_deg k p = 0)
             ==> poly_splits k p)`,
  REWRITE_TAC[ALGEBRAICALLY_CLOSED_FIELD_EQ_POLY_SPLITS] THEN
  MESON_TAC[POLY_DEG_0_IMP_SPLITS]);;

let ALGEBRAICALLY_CLOSED_FIELD_DECOMPOSE = prove
 (`!(k:A ring) p.
     algebraically_closed_field k /\
     p IN ring_carrier(poly_ring k (:1)) /\ ~(poly_deg k p = 0)
     ==> ?a q. a IN ring_carrier k /\
               q IN ring_carrier(poly_ring k (:1)) /\
               p = poly_mul k
                 (poly_sub k (poly_var k one) (poly_const k a)) q /\
               poly_deg k q + 1 = poly_deg k p`,
  REWRITE_TAC[algebraically_closed_field] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:(1->num)->A`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:(1->num)->A`; `a:A`]
        POLY_ROOT_DECOMPOSE) THEN
  ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN MESON_TAC[]);;

let ALGEBRAICALLY_CLOSED_FIELD_SPLITS = prove
 (`!(k:A ring) p.
        algebraically_closed_field k /\
        p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k)
        ==> ?c a. c IN ring_carrier k /\ ~(c = ring_0 k) /\
                  (!i. 1 <= i /\ i <= poly_deg k p
                       ==> a(i) IN ring_carrier k) /\
                  p = poly_mul k (poly_const k c)
                        (ring_product (poly_ring k (:1)) (1..poly_deg k p)
                           (\i. poly_sub k (poly_var k one)
                                           (poly_const k (a i))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:(1->num)->A`]
    ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS) THEN
  ASM_REWRITE_TAC[POLY_SPLITS_CASES]);;

let ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS = prove
 (`!k:A ring.
     algebraically_closed_field k <=>
     field k /\
     !p. p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k)
         ==> ?c a. c IN ring_carrier k /\ ~(c = ring_0 k) /\
                   (!i. 1 <= i /\ i <= poly_deg k p
                        ==> a(i) IN ring_carrier k) /\
                   p = poly_mul k (poly_const k c)
                         (ring_product (poly_ring k (:1)) (1..poly_deg k p)
                           (\i. poly_sub k (poly_var k one)
                                           (poly_const k (a i))))`,
  REWRITE_TAC[ALGEBRAICALLY_CLOSED_FIELD_EQ_POLY_SPLITS; POLY_SPLITS_CASES] THEN
  REWRITE_TAC[TAUT `p /\ ~q ==> r <=> p ==> q \/ r`]);;

let ALGEBRAICALLY_CLOSED_FIELD_EQ_SPLITS_ALT = prove
 (`!k:A ring.
     algebraically_closed_field k <=>
     field k /\
     !p. p IN ring_carrier(poly_ring k (:1)) /\ ~(poly_deg k p = 0)
         ==> ?c a. c IN ring_carrier k /\ ~(c = ring_0 k) /\
                   (!i. 1 <= i /\ i <= poly_deg k p
                        ==> a(i) IN ring_carrier k) /\
                   p = poly_mul k (poly_const k c)
                         (ring_product (poly_ring k (:1)) (1..poly_deg k p)
                           (\i. poly_sub k (poly_var k one)
                                           (poly_const k (a i))))`,
  REWRITE_TAC[ALGEBRAICALLY_CLOSED_FIELD_EQ_POLY_SPLITS_ALT] THEN
  SIMP_TAC[POLY_NONCONSTANT_IMP_NZ; POLY_SPLITS_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Extending a homomorphism g from k to k(a): a can be sent to any root b    *)
(* of the image under g of its minimal polynomial, in any ring. In an        *)
(* algebraically closed field such a root exists.                            *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT = prove
 (`!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C) a b.
        field_extension(k,l) f /\ algebraic_over(k,l) f a /\
        ring_homomorphism(k,l') g /\ b IN ring_carrier l' /\
        poly_eval l' (g o minimal_polynomial(k,l) f a) b = ring_0 l'
        ==> ?h. ring_homomorphism
                 (subring_generated l (a INSERT IMAGE f (ring_carrier k)),
                  l') h /\
                (!x. x IN ring_carrier k ==> h(f x) = g x) /\
                h a = b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL
   [`poly_ring (k:A ring) (:1)`;
    `subring_generated l (a INSERT IMAGE (f:A->B) (ring_carrier k))`;
    `l':C ring`; `poly_extend (k,l) (f:A->B) (\v:1. a)`;
    `poly_extend (k,l') (g:A->C) (\v:1. b)`]
   RING_HOMOMORPHISM_EPIMORPHISM_FACTOR) THEN
  ASM_SIMP_TAC[ring_epimorphism; RING_HOMOMORPHISM_INTO_SUBRING_EQ_GEN;
               RING_HOMOMORPHISM_POLY_EXTEND; IMAGE_POLY_EXTEND_1;
               SUBSET_REFL] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; ring_kernel; IN_ELIM_THM; SUBRING_GENERATED] THEN
    X_GEN_TAC `p:(1->num)->A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `a:B`; `p:(1->num)->A`]
      MINIMAL_POLYNOMIAL_DIVIDES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `l':C ring`;
                   `poly_extend (k,l') (g:A->C) (\v:1. b)`;
                   `minimal_polynomial (k,l) (f:A->B) a`; `p:(1->num)->A`]
      RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_EXTEND; POLY_EXTEND_EVALUATE;
                 GSYM poly_eval; RING_DIVIDES_ZERO];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:B->C` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `poly_const k (x:A):(1->num)->A`) THEN
      ASM_SIMP_TAC[POLY_CONST; POLY_EXTEND_CONST];
      FIRST_X_ASSUM(MP_TAC o SPEC `poly_var k (one:1):(1->num)->A`) THEN
      ASM_SIMP_TAC[POLY_VAR_UNIV; POLY_EXTEND_VAR]]]);;

let SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM = prove
 (`!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C) a.
        field k /\ integral_domain l /\
        ring_monomorphism(k,l) f /\ a IN ring_carrier l /\
        algebraic_over(k,l) f a /\ algebraically_closed_field l' /\
        ring_monomorphism(k,l') g
        ==> ?h. ring_homomorphism
                 (subring_generated l (a INSERT IMAGE f (ring_carrier k)),
                  l') h /\
                (!x. x IN ring_carrier k ==> h(f x) = g x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `field_extension
     (k,subring_generated l (a INSERT IMAGE (f:A->B) (ring_carrier k))) f`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[field_extension; FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN;
                 RING_MONOMORPHISM_IMP_HOMOMORPHISM;
                 RING_MONOMORPHISM_INTO_SUBRING;
                 SET_RULE `!a:B s. s SUBSET a INSERT s`];
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension])] THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`;
     `subring_generated l (a INSERT IMAGE (f:A->B) (ring_carrier k))`; `a:B`]
    FIELD_SIMPLE_ALGEBRAIC_EXTENSION_EQ) THEN
  ASM_SIMP_TAC[SUBRING_GENERATED_IDEMPOT; SUBSET_REFL; IN_INSERT;
               SUBRING_GENERATED_INC_GEN; FIELD_IMP_INTEGRAL_DOMAIN;
               RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `k:A ring`;
     `subring_generated l (a INSERT IMAGE (f:A->B) (ring_carrier k))`; `a:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = minimal_polynomial
    (k,subring_generated l (a INSERT IMAGE (f:A->B) (ring_carrier k))) f a` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(g:A->C) o (m:(1->num)->A)` o CONJUNCT2 o
    GEN_REWRITE_RULE I [algebraically_closed_field]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[IN_RING_POLYNOMIAL_CARRIER_COMPOSE; RING_POLYNOMIAL;
                  POLY_DEG_MONOMORPHIC_IMAGE; IRREDUCIBLE_IMP_POLY_DEG_NZ;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    DISCH_THEN(X_CHOOSE_THEN `b:C` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`k:A ring`;
     `subring_generated l (a INSERT IMAGE (f:A->B) (ring_carrier k))`;
     `l':C ring`; `f:A->B`; `g:A->C`; `a:B`; `b:C`]
    SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT) THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; SUBRING_GENERATED_IDEMPOT;
               SUBSET_REFL] THEN
  MESON_TAC[]);;

let ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM = prove
 (`!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C).
        algebraic_extension(k,l) f /\ algebraically_closed_field l' /\
        ring_homomorphism(k,l') g
        ==> ?h. ring_homomorphism(l,l') h /\
                (!x. x IN ring_carrier k ==> h(f x) = g x)`,
  let SUBRING_OF_G0_FROM_CH_P =
   MATCH_MP_TAC SUBFIELD_IMP_SUBRING_OF THEN USE_THEN "CH_P" (fun ch_p ->
     FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o
       CONJUNCT2 o REWRITE_RULE[] o
       MATCH_MP (SPEC `G0:(B#C)->bool` ch_p))) in
  let HOM_CONST_TAC thm =
   USE_THEN "HOM_U" (fun hom_u -> USE_THEN "GW" (fun gw ->
       MP_TAC(REWRITE_RULE[CONJUNCT2 SUBRING_GENERATED]
         (MATCH_MP thm (MATCH_MP hom_u gw))))) THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[] in
  let G0_X0_IN_CC_TAC : tactic =
   SUBGOAL_THEN `?G0:(B#C)->bool. G0 IN cc /\ x0:B IN IMAGE FST G0`
     STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[IN_IMAGE; IN_UNIONS]; ALL_TAC] THEN
   SUBGOAL_THEN `IMAGE FST (G0:(B#C)->bool) subring_of (l:B ring)`
     ASSUME_TAC THENL [SUBRING_OF_G0_FROM_CH_P; ALL_TAC] THEN
   SUBGOAL_THEN
     `x0:B IN ring_carrier
       (subring_generated (l:B ring) (IMAGE FST (G0:(B#C)->bool)))`
     ASSUME_TAC THENL
    [ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING]; ALL_TAC] in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `field (k:A ring) /\ field (l:B ring) /\ field (l':C ring) /\
     ring_monomorphism(k:A ring,l:B ring) f /\ integral_domain (l:B ring) /\
     ring_monomorphism(k:A ring,l':C ring) g /\
     ring_homomorphism(k:A ring,l:B ring) (f:A->B)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension; field_extension;
     ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD; FIELD_IMP_INTEGRAL_DOMAIN;
     FIELD_RING_HOMOMORPHISM_MONOMORPHISM; FIELD_IMP_NONTRIVIAL_RING;
     ring_monomorphism]; ALL_TAC] THEN
  (* Apply Zorn's lemma on graphs (subsets of B x C) encoding partial
     homomorphisms. P(G) says G is a functional relation whose domain is
     a subfield of l containing IMAGE f (carrier k), and the induced
     function is a ring homomorphism extending g. *)
  MP_TAC(ISPEC `\G:(B#C)->bool.
       G SUBSET (ring_carrier l CROSS ring_carrier l') /\
       (!x:B y1:C y2:C. (x,y1) IN G /\ (x,y2) IN G ==> y1 = y2) /\
       (IMAGE FST G) subfield_of (l:B ring) /\
       IMAGE (f:A->B) (ring_carrier k) SUBSET IMAGE FST G /\ ring_homomorphism
         (subring_generated l (IMAGE FST G), l':C ring)
         (\x:B. @y:C. (x,y) IN G) /\ (!x:A. x IN ring_carrier k
              ==> (@y:C. ((f:A->B) x,y) IN G) = g x)`
    ZL_SUBSETS_UNIONS_NONEMPTY) THEN ANTS_TAC THENL [CONJ_TAC THENL
     [(* Existence: the graph {(f x, g x) | x in carrier k} works *) ABBREV_TAC
        `G0 = {((f:A->B) x, (g:A->C) x) | x IN ring_carrier k}` THEN
      EXISTS_TAC `G0:(B#C)->bool` THEN
      SUBGOAL_THEN `!a1 a2:A. a1 IN ring_carrier k /\ a2 IN ring_carrier k /\
                   (f:A->B) a1 = f a2 ==> a1 = a2`
        (LABEL_TAC "INJ") THENL [ASM_MESON_TAC[ring_monomorphism];
          ALL_TAC] THEN
      SUBGOAL_THEN `!a:A. a IN ring_carrier k
               ==> (@y:C. ((f:A->B) a, y) IN G0) = (g:A->C) a`
        (LABEL_TAC "SELECT") THENL [X_GEN_TAC `a:A` THEN DISCH_TAC THEN
        MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `c:C` THEN
        EXPAND_TAC "G0" THEN REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
        ASM_MESON_TAC[]; ALL_TAC] THEN SUBGOAL_THEN
        `IMAGE FST (G0:(B#C)->bool) = IMAGE (f:A->B) (ring_carrier k)`
        ASSUME_TAC THENL [EXPAND_TAC "G0" THEN
        REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM;
                    EXISTS_PAIR_THM; PAIR_EQ; FST] THEN
        MESON_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [(* G0 SUBSET carrier l CROSS carrier l' *)
        EXPAND_TAC "G0" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CROSS] THEN
        X_GEN_TAC `p:B#C` THEN
        DISCH_THEN(X_CHOOSE_THEN `a0:A` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[FST; SND; IN_CROSS] THEN CONJ_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
          CONJUNCT1 o GEN_REWRITE_RULE I [ring_homomorphism]) THEN
        ASM_REWRITE_TAC[]; EXPAND_TAC "G0" THEN
        REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
        EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[CARRIER_SUBFIELD_OF];
          SET_TAC[];
        MP_TAC(ISPECL [`k:A ring`; `subring_generated (l:B ring)
              (IMAGE (f:A->B) (ring_carrier k))`; `l':C ring`;
           `f:A->B`; `g:A->C`]
          RING_HOMOMORPHISM_EPIMORPHISM_FACTOR) THEN ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [(* ring_epimorphism(k, subring_generated l (IMAGE f carrier_k)) f
             *)
            REWRITE_TAC[ring_epimorphism] THEN CONJ_TAC THENL
             [MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN
              ASM_REWRITE_TAC[SUBSET_REFL];
              SUBGOAL_THEN `(IMAGE (f:A->B) (ring_carrier k)) subring_of l`
                (fun th -> SIMP_TAC[th;
                  CARRIER_SUBRING_GENERATED_SUBRING]) THEN
              MATCH_MP_TAC SUBFIELD_IMP_SUBRING_OF THEN
              MATCH_MP_TAC SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
              EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[CARRIER_SUBFIELD_OF]];
            (* ring_homomorphism(k, l') g *) ASM_REWRITE_TAC[];
            REWRITE_TAC[RING_KERNEL_TO_SUBRING_GENERATED] THEN SUBGOAL_THEN
              `ring_kernel(k:A ring,l:B ring) f = {ring_0 k}`
              SUBST1_TAC THENL [ASM_MESON_TAC[RING_MONOMORPHISM]; ALL_TAC] THEN
            REWRITE_TAC[SING_SUBSET] THEN MATCH_MP_TAC RING_KERNEL_0 THEN
              ASM_REWRITE_TAC[]];
          ALL_TAC] THEN (* Continuation: transfer from h' to the @-function *)
        DISCH_THEN(X_CHOOSE_THEN `h':B->C` STRIP_ASSUME_TAC) THEN
        MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN
        EXISTS_TAC `h':B->C` THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN
          `(IMAGE (f:A->B) (ring_carrier k)) subring_of l` ASSUME_TAC THENL
         [MATCH_MP_TAC SUBFIELD_IMP_SUBRING_OF THEN MATCH_MP_TAC
            SUBFIELD_OF_MONOMORPHIC_IMAGE THEN
          EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[CARRIER_SUBFIELD_OF];
            ALL_TAC] THEN
        ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING] THEN
        REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(@y:C. ((f:A->B) a,y) IN G0) = (g:A->C) a`
          SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_MESON_TAC[]];
      X_GEN_TAC `cc:((B#C)->bool)->bool` THEN BETA_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `G_w:(B#C)->bool` (LABEL_TAC "GW"))
        (CONJUNCTS_THEN2 (LABEL_TAC "CH_P") (LABEL_TAC "CH_ORD"))) THEN
      SUBGOAL_THEN `!G:(B#C)->bool. G IN cc ==>
           !x:B y1:C y2:C. (x,y1) IN G /\ (x,y2) IN G ==> y1 = y2`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `!x:B y1:C y2:C.
           (x,y1) IN UNIONS cc /\ (x,y2) IN UNIONS cc ==> y1 = y2`
        (LABEL_TAC "UFUNC") THENL
       [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `!G:(B#C)->bool. G IN cc ==> !x:B. x IN IMAGE FST G ==>
             (@y:C. (x,y) IN UNIONS cc) = (@y. (x,y) IN G)`
        (LABEL_TAC "SELECT_UNION") THENL
       [X_GEN_TAC `G0:(B#C)->bool` THEN DISCH_TAC THEN
        X_GEN_TAC `x0:B` THEN DISCH_TAC THEN SUBGOAL_THEN
          `!y0:C. (x0:B,y0) IN UNIONS cc <=>
                  (x0,y0) IN (G0:(B#C)->bool)` (fun th -> REWRITE_TAC[th]) THEN
        X_GEN_TAC `y0:C` THEN EQ_TAC THENL [DISCH_TAC THEN
          SUBGOAL_THEN `?y':C. (x0:B,y') IN (G0:(B#C)->bool)`
            STRIP_ASSUME_TAC THENL
           [MP_TAC(ASSUME `x0:B IN IMAGE FST (G0:(B#C)->bool)`) THEN
            REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; FST; PAIR_EQ] THEN
            MESON_TAC[]; ALL_TAC] THEN ASM_MESON_TAC[IN_UNIONS];
          ASM_MESON_TAC[IN_UNIONS]]; ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE FST (UNIONS cc:(B#C)->bool) subring_of (l:B ring)`
        (LABEL_TAC "SR") THENL [REWRITE_TAC[IMAGE_UNIONS] THEN
        MATCH_MP_TAC SUBRING_OF_UNIONS THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN USE_THEN "GW" (fun gw ->
            EXISTS_TAC `G_w:(B#C)->bool` THEN ACCEPT_TAC gw);
          REWRITE_TAC[FORALL_IN_IMAGE] THEN
          X_GEN_TAC `G0:(B#C)->bool` THEN DISCH_TAC THEN
          SUBRING_OF_G0_FROM_CH_P; REWRITE_TAC[IN_IMAGE] THEN
          MAP_EVERY X_GEN_TAC [`s1:B->bool`; `s2:B->bool`] THEN
          DISCH_THEN(CONJUNCTS_THEN2
            (X_CHOOSE_THEN `G1:(B#C)->bool` STRIP_ASSUME_TAC)
            (X_CHOOSE_THEN `G2:(B#C)->bool` STRIP_ASSUME_TAC)) THEN
          FIRST_X_ASSUM SUBST1_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
          USE_THEN "CH_ORD" (fun ch_ord -> DISJ_CASES_TAC(MATCH_MP
              (SPECL [`G1:(B#C)->bool`; `G2:(B#C)->bool`] ch_ord)
              (CONJ (ASSUME `(G1:(B#C)->bool) IN cc`)
                    (ASSUME `(G2:(B#C)->bool) IN cc`)))) THENL
           [DISJ1_TAC; DISJ2_TAC] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
             ASM_REWRITE_TAC[]];
        ALL_TAC] THEN REPEAT CONJ_TAC THENL
       [(* 1. UNIONS cc SUBSET carrier l CROSS carrier l' *)
        REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[];
        (* 2. Functional *) USE_THEN "UFUNC" ACCEPT_TAC; (* 3. subfield_of *)
        REWRITE_TAC[subfield_of] THEN CONJ_TAC THENL [USE_THEN "SR" ACCEPT_TAC;
          ASM_SIMP_TAC[field; CONJUNCT2 SUBRING_GENERATED;
                        CARRIER_SUBRING_GENERATED_SUBRING] THEN
          CONJ_TAC THENL [ASM_MESON_TAC[FIELD_NONTRIVIAL]; ALL_TAC] THEN
          X_GEN_TAC `x0:B` THEN STRIP_TAC THEN
          SUBGOAL_THEN `?G0. (G0:(B#C)->bool) IN cc /\ (x0:B) IN IMAGE FST G0`
            STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_IMAGE; IN_UNIONS];
            ALL_TAC] THEN
          SUBGOAL_THEN `IMAGE FST (G0:(B#C)->bool) subfield_of (l:B ring)`
            ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN SUBGOAL_THEN
            `ring_inv (l:B ring) (x0:B) IN IMAGE FST (G0:(B#C)->bool)`
            ASSUME_TAC THENL [MATCH_MP_TAC IN_SUBFIELD_INV THEN
              ASM_REWRITE_TAC[]; ALL_TAC] THEN
          SUBGOAL_THEN `(x0:B) IN ring_carrier (l:B ring)`
            ASSUME_TAC THENL [ASM_MESON_TAC[subring_of; SUBSET]; ALL_TAC] THEN
          EXISTS_TAC `ring_inv (l:B ring) (x0:B)` THEN CONJ_TAC THENL
           [ASM_MESON_TAC[IN_IMAGE; IN_UNIONS]; ASM_SIMP_TAC[FIELD_MUL_RINV]]];
        USE_THEN "CH_P" (fun ch_p -> USE_THEN "GW" (fun gw ->
            STRIP_ASSUME_TAC(MATCH_MP (SPEC `G_w:(B#C)->bool` ch_p) gw))) THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE FST (G_w:(B#C)->bool)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_UNIONS] THEN
        USE_THEN "GW" (fun th -> MESON_TAC[th]);
        (* 5. ring_homomorphism (per-G and for UNIONS) *)
        SUBGOAL_THEN `!G. G IN cc ==> ring_homomorphism
                 (subring_generated (l:B ring) (IMAGE FST G), l':C ring)
                 (\x:B. @y:C. (x,y) IN UNIONS cc)` (LABEL_TAC "HOM_U") THENL
         [X_GEN_TAC `G0:(B#C)->bool` THEN DISCH_TAC THEN SUBGOAL_THEN
            `IMAGE FST (G0:(B#C)->bool) subring_of (l:B ring)`
            ASSUME_TAC THENL [SUBRING_OF_G0_FROM_CH_P; ALL_TAC] THEN
          MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN
          EXISTS_TAC `\x:B. @y:C. (x,y) IN (G0:(B#C)->bool)` THEN
            CONJ_TAC THENL
           [ASM_MESON_TAC[];
            ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING] THEN
            X_GEN_TAC `x0:B` THEN DISCH_TAC THEN
            CONV_TAC(DEPTH_CONV BETA_CONV) THEN
            USE_THEN "SELECT_UNION" (fun su ->
              FIRST_ASSUM(fun gin -> MP_TAC(SPEC `x0:B`
                  (MATCH_MP (SPEC `G0:(B#C)->bool` su) gin)))) THEN
            ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        REWRITE_TAC[ring_homomorphism; CONJUNCT2 SUBRING_GENERATED] THEN
        USE_THEN "SR" (fun sr ->
          REWRITE_TAC[MATCH_MP CARRIER_SUBRING_GENERATED_SUBRING sr]) THEN
        CONJ_TAC THENL
         [(* 5a. IMAGE subset *) REWRITE_TAC[SUBSET] THEN X_GEN_TAC `c0:C` THEN
          GEN_REWRITE_TAC LAND_CONV [IN_IMAGE] THEN
          DISCH_THEN(X_CHOOSE_THEN `x0:B`
            (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
          CONV_TAC(DEPTH_CONV BETA_CONV) THEN G0_X0_IN_CC_TAC THEN
          USE_THEN "HOM_U" (fun hom_u ->
            FIRST_ASSUM(fun gin -> FIRST_ASSUM(fun xin ->
                MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
                  (MP (SPEC `x0:B` (CONJUNCT1(REWRITE_RULE
                      [ring_homomorphism; SUBSET; FORALL_IN_IMAGE]
                      (MATCH_MP hom_u gin))))
                  xin))))) THEN SIMP_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [HOM_CONST_TAC RING_HOMOMORPHISM_0; ALL_TAC] THEN
        CONJ_TAC THENL [HOM_CONST_TAC RING_HOMOMORPHISM_1; ALL_TAC] THEN
        CONJ_TAC THENL [(* 5d: ring_neg *)
          X_GEN_TAC `x0:B` THEN DISCH_TAC THEN G0_X0_IN_CC_TAC THEN
          USE_THEN "HOM_U" (fun hom_u ->
            FIRST_ASSUM(fun gin -> FIRST_ASSUM(fun xin ->
                MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
                  (REWRITE_RULE[CONJUNCT2 SUBRING_GENERATED]
                    (MATCH_MP (SPEC `x0:B` (MATCH_MP RING_HOMOMORPHISM_NEG
                          (MATCH_MP hom_u gin)))
                      xin)))))) THEN REWRITE_TAC[]; ALL_TAC] THEN
        (let chain_binop_tac ring_hom_op =
          MAP_EVERY X_GEN_TAC [`x0:B`; `y0:B`] THEN STRIP_TAC THEN SUBGOAL_THEN
            `?G0:(B#C)->bool. G0 IN cc /\
               x0:B IN IMAGE FST G0 /\ y0:B IN IMAGE FST G0`
            STRIP_ASSUME_TAC THENL [SUBGOAL_THEN
              `(?G1:(B#C)->bool. G1 IN cc /\ x0:B IN IMAGE FST G1) /\
               (?G2:(B#C)->bool. G2 IN cc /\ y0:B IN IMAGE FST G2)`
              (CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) THENL
             [CONJ_TAC THEN ASM_MESON_TAC[IN_IMAGE; IN_UNIONS]; ALL_TAC] THEN
            USE_THEN "CH_ORD" (fun ch_ord -> DISJ_CASES_TAC(MATCH_MP
                (SPECL [`G1:(B#C)->bool`; `G2:(B#C)->bool`] ch_ord)
                (CONJ (ASSUME `G1:(B#C)->bool IN cc`)
                      (ASSUME `G2:(B#C)->bool IN cc`)))) THENL
             [EXISTS_TAC `G2:(B#C)->bool` THEN ASM_REWRITE_TAC[] THEN
               ASM_MESON_TAC[SUBSET; IN_IMAGE];
              EXISTS_TAC `G1:(B#C)->bool` THEN ASM_REWRITE_TAC[] THEN
                ASM_MESON_TAC[SUBSET; IN_IMAGE]];
            ALL_TAC] THEN SUBGOAL_THEN
            `IMAGE FST (G0:(B#C)->bool) subring_of (l:B ring)`
            ASSUME_TAC THENL [SUBRING_OF_G0_FROM_CH_P; ALL_TAC] THEN
          SUBGOAL_THEN `x0:B IN ring_carrier (subring_generated (l:B ring)
                (IMAGE FST (G0:(B#C)->bool))) /\
             y0:B IN ring_carrier (subring_generated (l:B ring)
                (IMAGE FST (G0:(B#C)->bool)))`
            ASSUME_TAC THENL [ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING];
              ALL_TAC] THEN
          USE_THEN "HOM_U" (fun hom_u ->
            FIRST_ASSUM(fun gin -> FIRST_ASSUM(fun xyin ->
                MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
                  (REWRITE_RULE[CONJUNCT2 SUBRING_GENERATED]
                    (MATCH_MP (SPECL [`x0:B`; `y0:B`]
                        (MATCH_MP ring_hom_op (MATCH_MP hom_u gin)))
                      xyin)))))) THEN REWRITE_TAC[] in
        CONJ_TAC THENL [chain_binop_tac RING_HOMOMORPHISM_ADD; ALL_TAC] THEN
        chain_binop_tac RING_HOMOMORPHISM_MUL); (* 6. extends g *)
        X_GEN_TAC `a0:A` THEN DISCH_TAC THEN USE_THEN "CH_P" (fun ch_p ->
          USE_THEN "GW" (fun gw -> STRIP_ASSUME_TAC(MATCH_MP
              (SPEC `G_w:(B#C)->bool` ch_p) gw))) THEN
        SUBGOAL_THEN `(f:A->B) a0 IN IMAGE FST (G_w:(B#C)->bool)`
          ASSUME_TAC THENL [FIRST_X_ASSUM(MATCH_MP_TAC o
            REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
          ASM_REWRITE_TAC[]; ALL_TAC] THEN USE_THEN "SELECT_UNION" (fun su ->
          USE_THEN "GW" (fun gw -> MP_TAC(SPEC `(f:A->B) a0`
              (MATCH_MP (SPEC `G_w:(B#C)->bool` su) gw)))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_MESON_TAC[]]]; (* end chain closure *)
    DISCH_THEN(X_CHOOSE_THEN `G:(B#C)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `IMAGE FST (G:(B#C)->bool) = ring_carrier (l:B ring)`
      ASSUME_TAC THENL [(* Proof: IMAGE FST G = ring_carrier l *)
      REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
       [(* Easy: IMAGE FST G SUBSET ring_carrier l *)
        ASM_MESON_TAC[SUBFIELD_OF_IMP_SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `a:B` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(a:B) IN IMAGE FST (G:(B#C)->bool)` THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN SUBGOAL_THEN
        `field(subring_generated (l:B ring) (IMAGE FST (G:(B#C)->bool))) /\
         IMAGE FST (G:(B#C)->bool) subring_of (l:B ring) /\
         ring_monomorphism (subring_generated (l:B ring)
              (IMAGE FST (G:(B#C)->bool)), l) I` STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[subfield_of]; ASM_MESON_TAC[SUBFIELD_IMP_SUBRING_OF];
          REWRITE_TAC[I_DEF; RING_MONOMORPHISM_INCLUSION]]; ALL_TAC] THEN
      SUBGOAL_THEN `ring_carrier(subring_generated (l:B ring)
          (IMAGE FST (G:(B#C)->bool))) = IMAGE FST G` ASSUME_TAC THENL
       [ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING]; ALL_TAC] THEN
      SUBGOAL_THEN `algebraic_over (subring_generated (l:B ring)
            (IMAGE FST (G:(B#C)->bool)), l) I (a:B)` ASSUME_TAC THENL
       [MATCH_MP_TAC ALGEBRAIC_OVER_SUBRING_GENERATED_MONO THEN
        EXISTS_TAC `IMAGE (f:A->B) (ring_carrier k)` THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `l:B ring`; `a:B`]
            ALGEBRAIC_OVER_RANGE) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
          ASM_MESON_TAC[algebraic_extension]; ASM_MESON_TAC[]]; ALL_TAC] THEN
      (* Monomorphism of h_G *) SUBGOAL_THEN `ring_monomorphism
          (subring_generated (l:B ring) (IMAGE FST (G:(B#C)->bool)), l':C ring)
          (\x:B. @y:C. (x,y) IN G)` ASSUME_TAC THENL
       [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
         ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[FIELD_IMP_NONTRIVIAL_RING]; ALL_TAC] THEN MP_TAC(ISPECL
        [`subring_generated (l:B ring) (IMAGE FST (G:(B#C)->bool))`;
         `l:B ring`; `l':C ring`; `I:B->B`;
         `(\x:B. @y:C. (x,y) IN (G:(B#C)->bool)):B->C`; `a:B`]
        SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[IMAGE_I; I_DEF] THEN
      DISCH_THEN(X_CHOOSE_THEN `h':B->C` STRIP_ASSUME_TAC) THEN
      ABBREV_TAC `S' = ring_carrier(subring_generated (l:B ring)
        ((a:B) INSERT IMAGE FST (G:(B#C)->bool)))` THEN
      SUBGOAL_THEN `field(subring_generated (l:B ring)
          ((a:B) INSERT IMAGE FST (G:(B#C)->bool)))` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`I:B->B`;
           `subring_generated (l:B ring) (IMAGE FST (G:(B#C)->bool))`;
           `l:B ring`; `a:B`] FIELD_SIMPLE_ALGEBRAIC_EXTENSION_GEN) THEN
        ASM_REWRITE_TAC[IMAGE_I] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_MESON_TAC[ring_monomorphism]; ALL_TAC] THEN
      SUBGOAL_THEN `(S':B->bool) subfield_of (l:B ring) /\
        (a:B) IN (S':B->bool)` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "S'" THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[subfield_of; SUBRING_SUBRING_GENERATED;
                          SUBRING_GENERATED_BY_SUBRING_GENERATED];
          MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
          ASM_REWRITE_TAC[IN_INSERT]]; ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE FST (G:(B#C)->bool) SUBSET (S':B->bool) /\
         (S':B->bool) SUBSET ring_carrier (l:B ring)` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "S'" THEN CONJ_TAC THENL [MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `(a:B) INSERT IMAGE FST (G:(B#C)->bool)` THEN
          CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC SUBRING_GENERATED_SUBSET_CARRIER_SUBSET THEN
          REWRITE_TAC[INSERT_SUBSET] THEN
          ASM_MESON_TAC[SUBFIELD_OF_IMP_SUBSET; SUBSET];
          REWRITE_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET]]; ALL_TAC] THEN
      SUBGOAL_THEN `(!x:B y1:C y2:C.
           (x,y1) IN (G:(B#C)->bool) /\ (x,y2) IN G ==> y1 = y2) /\
         (!x:A. x IN ring_carrier k
               ==> (@y:C. ((f:A->B) x,y) IN (G:(B#C)->bool)) =
                   (g:A->C) x)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE FST (IMAGE (\x:B. (x, (h':B->C) x)) (S':B->bool))
         = (S':B->bool)` ASSUME_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; FST; PAIR_EQ] THEN
        MESON_TAC[]; ALL_TAC] THEN SUBGOAL_THEN `!b:B. b IN S'
               ==> (@c:C. (b,c) IN IMAGE (\x:B. (x, (h':B->C) x))
                                          (S':B->bool)) = h' b` ASSUME_TAC
                                            THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
        X_GEN_TAC `c':C` THEN
        REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      (* Apply maximality: G = IMAGE (\x. (x, h' x)) S' *) SUBGOAL_THEN
        `(G:(B#C)->bool) = IMAGE (\x:B. (x, (h':B->C) x)) (S':B->bool)`
        ASSUME_TAC THENL [FIRST_X_ASSUM(MP_TAC o SPEC
          `IMAGE (\x:B. (x, (h':B->C) x)) (S':B->bool)`) THEN
            REWRITE_TAC[] THEN
        ANTS_TAC THENL [CONJ_TAC THENL [(* P(G') - 6 conditions *)
            ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
             [(* 1 *) REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CROSS] THEN
              X_GEN_TAC `b':B` THEN DISCH_TAC THEN CONJ_TAC THENL
               [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN EXPAND_TAC "S'" THEN
              ASM_MESON_TAC[ring_homomorphism; SUBSET; IN_IMAGE];
              (* 2 *) REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN MESON_TAC[];
              (* 4 *) ASM_MESON_TAC[SUBSET_TRANS]; (* 5: ring_homomorphism *)
              SUBGOAL_THEN `subring_generated (l:B ring) (S':B->bool) =
                 subring_generated l
                   ((a:B) INSERT IMAGE FST (G:(B#C)->bool))` SUBST1_TAC THENL
               [UNDISCH_TAC `ring_carrier (subring_generated (l:B ring)
                    ((a:B) INSERT IMAGE FST (G:(B#C)->bool))) = S'` THEN
                DISCH_THEN(SUBST1_TAC o SYM) THEN
                REWRITE_TAC[SUBRING_GENERATED_BY_SUBRING_GENERATED];
                  ALL_TAC] THEN
              MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN EXISTS_TAC `h':B->C` THEN
              CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
              ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
              CONV_TAC BETA_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
              ASM_REWRITE_TAC[]; X_GEN_TAC `x0:A` THEN DISCH_TAC THEN
              SUBGOAL_THEN `(f:A->B) x0 IN (S':B->bool) /\
                (f:A->B) x0 IN IMAGE FST (G:(B#C)->bool)` STRIP_ASSUME_TAC
                  THENL
               [CONJ_TAC THEN ASM_MESON_TAC[SUBSET; IN_IMAGE]; ALL_TAC] THEN
              SUBGOAL_THEN `(@y:C. ((f:A->B) x0,y) IN
                  IMAGE (\x:B. (x,(h':B->C) x)) (S':B->bool)) =
                 (h':B->C) ((f:A->B) x0)` SUBST1_TAC THENL [ASM_MESON_TAC[];
                   ALL_TAC] THEN
              ASM_MESON_TAC[]]; (* G SUBSET G' *)
            REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_IMAGE; PAIR_EQ] THEN
            MAP_EVERY X_GEN_TAC [`x0:B`; `y0:C`] THEN DISCH_TAC THEN
            SUBGOAL_THEN `(x0:B) IN (S':B->bool)` ASSUME_TAC THENL
             [ASM_MESON_TAC[SUBSET; IN_IMAGE; FST]; ALL_TAC] THEN
            EXISTS_TAC `x0:B` THEN ASM_REWRITE_TAC[] THEN
            SUBGOAL_THEN `(h':B->C) x0 =
              (@y:C. (x0,y) IN (G:(B#C)->bool))` SUBST1_TAC THENL
             [ASM_MESON_TAC[IN_IMAGE; FST]; ALL_TAC] THEN
            CONV_TAC SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
            X_GEN_TAC `z:C` THEN ASM_MESON_TAC[]];
          DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `\x:B. @y:C. (x,y) IN (G:(B#C)->bool)` THEN
    ASM_MESON_TAC[SUBRING_GENERATED_RING_CARRIER]]);;

let ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT = prove
 (`!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C) a b.
        algebraic_extension(k,l) f /\ algebraically_closed_field l' /\
        ring_homomorphism(k,l') g /\ a IN ring_carrier l /\
        b IN ring_carrier l' /\
        poly_eval l' (g o minimal_polynomial(k,l) f a) b = ring_0 l'
        ==> ?h. ring_homomorphism(l,l') h /\
                (!x. x IN ring_carrier k ==> h(f x) = g x) /\
                h a = b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [algebraic_extension]) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `l':C ring`; `f:A->B`; `g:A->C`;
                 `a:B`; `b:C`] SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC
   `K = subring_generated l (a INSERT IMAGE (f:A->B) (ring_carrier k))` THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:B->C` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:B ring`; `l:B ring`; `l':C ring`; `I:B->B`; `h0:B->C`]
    ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[I_THM] THEN
  SUBGOAL_THEN
   `field_extension (k,K) (f:A->B) /\ field_extension (K,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SIMPLE_ALGEBRAIC_EXTENSION;
                    FINITE_IMP_FIELD_EXTENSION];
      MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
      ASM_MESON_TAC[FIELD_EXTENSION_REFL; FIELD_SIMPLE_ALGEBRAIC_EXTENSION;
                    field_extension]];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`f:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
      ALGEBRAIC_EXTENSION_TRANS_EQ) THEN
    ASM_REWRITE_TAC[I_O_ID] THEN SIMP_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:B->C` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(a:B) IN ring_carrier K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ASM_MESON_TAC[FIELD_EXTENSION_CARRIER]]);;

let POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT = prove
 (`!(k:A ring) p.
      algebraically_closed_field k /\
      p IN ring_carrier(poly_ring k (:1)) /\
      ~(p = ring_0(poly_ring k (:1))) /\
      (!a. a IN ring_carrier k /\ poly_eval k p a = ring_0 k
           ==> ~(ring_divides (poly_ring k (:1))
                  (poly_pow k (poly_sub k (poly_var k one) (poly_const k a)) 2)
                  p))
      ==> CARD {x | x IN ring_carrier k /\ poly_eval k p x = ring_0 k} =
          poly_deg k p`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 POLY_RING_CLAUSES)] THEN STRIP_TAC THEN
  MATCH_MP_TAC POLY_SPLITS_SQUAREFREE_ROOT_COUNT_EXPLICIT THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD; FIELD_IMP_INTEGRAL_DOMAIN;
               ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS]);;

let POLY_SQUAREFREE_ROOT_COUNT = prove
 (`!(k:A ring) p.
      algebraically_closed_field k /\
      ring_squarefree (poly_ring k (:1)) p
      ==> CARD {x | x IN ring_carrier k /\ poly_eval k p x = ring_0 k} =
          poly_deg k p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT THEN
  ASM_SIMP_TAC[RING_SQUAREFREE_IN_CARRIER; RING_SQUAREFREE_IMP_NONZERO;
               FIELD_IMP_NONTRIVIAL_RING; ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
               TRIVIAL_POLY_RING] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `poly_sub k (poly_var k one) (poly_const k (a:A))`) o
    REWRITE_RULE[ring_squarefree]) THEN
  ASM_REWRITE_TAC[CONJUNCT2 POLY_RING_CLAUSES; NOT_IMP] THEN
  ASM_SIMP_TAC[POLY_CLAUSES; RING_SUB; POLY_CONST; POLY_VAR_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        POLY_DEG_UNIT)) THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD; FIELD_IMP_INTEGRAL_DOMAIN;
               FIELD_IMP_NONTRIVIAL_RING; ARITH_EQ;
              CONJUNCT2 POLY_RING_CLAUSES;  POLY_DEG_X_MINUS_A]);;

let POLY_SQUAREFREE_ROOT_COUNT_EQ = prove
 (`!(k:A ring) p.
      algebraically_closed_field k
      ==> (ring_squarefree (poly_ring k (:1)) p <=>
           p IN ring_carrier (poly_ring k (:1)) /\
           ~(p = ring_0 (poly_ring k (:1))) /\
           CARD {x | x IN ring_carrier k /\ poly_eval k p x = ring_0 k} =
           poly_deg k p)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_SIMP_TAC[POLY_SQUAREFREE_ROOT_COUNT; RING_SQUAREFREE_IN_CARRIER;
                 RING_SQUAREFREE_IMP_NONZERO; FIELD_IMP_NONTRIVIAL_RING;
                 ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD; TRIVIAL_POLY_RING];
    ASM_SIMP_TAC[POLY_ROOT_COUNT_IMP_SQUAREFREE;
                 ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD]]);;

let POLY_SQUAREFREE_EXPLICIT_EQ = prove
 (`!(k:A ring) p.
      algebraically_closed_field k
      ==> (ring_squarefree (poly_ring k (:1)) p <=>
           p IN ring_carrier (poly_ring k (:1)) /\
           ~(p = ring_0 (poly_ring k (:1))) /\
           (!a. a IN ring_carrier k /\ poly_eval k p a = ring_0 k
                ==> ~(ring_divides (poly_ring k (:1))
                  (poly_pow k (poly_sub k (poly_var k one) (poly_const k a)) 2)
                  p)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    ASM_SIMP_TAC[RING_SQUAREFREE_IN_CARRIER; RING_SQUAREFREE_IMP_NONZERO;
                 FIELD_IMP_NONTRIVIAL_RING; TRIVIAL_POLY_RING;
                 ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
    X_GEN_TAC `a:A` THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
        (MP_TAC o SPEC `poly_sub k (poly_var k one) (poly_const k (a:A))`) o
      REWRITE_RULE[ring_squarefree]) THEN
    ASM_REWRITE_TAC[CONJUNCT2 POLY_RING_CLAUSES; NOT_IMP] THEN
    ASM_SIMP_TAC[POLY_CLAUSES; RING_SUB; POLY_CONST; POLY_VAR_UNIV] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          POLY_DEG_UNIT)) THEN
    ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD; POLY_DEG_X_MINUS_A;
                 FIELD_IMP_INTEGRAL_DOMAIN; FIELD_IMP_NONTRIVIAL_RING; ARITH_EQ;
                 CONJUNCT2 POLY_RING_CLAUSES];
    STRIP_TAC THEN MATCH_MP_TAC POLY_ROOT_COUNT_IMP_SQUAREFREE THEN
    ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
    MATCH_MP_TAC POLY_SQUAREFREE_ROOT_COUNT_EXPLICIT THEN ASM_REWRITE_TAC[]]);;

let ALGEBRAIC_CLOSURE_EXISTS_ID = prove
 (`!k:A ring.
        ring_carrier k <_c (:A) /\ (:num) <_c (:A) /\ field k
        ==> ?l. algebraic_extension (k,l) I /\ algebraically_closed_field l`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC
   `\(l:A ring) (l':A ring). algebraic_extension(k,l) I /\
                algebraic_extension(k,l') I /\
                field_extension(l,l') I` ZL_STRONG) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(p /\ (p ==> (q ==> r) ==> s)) ==> (p /\ q ==> r) ==> s`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC QOSET_RESTRICT THEN REWRITE_TAC[qoset; IN_FLD] THEN
    MESON_TAC[FIELD_EXTENSION_REFL; field_extension; I_O_ID;
              FIELD_EXTENSION_TRANS];
    SIMP_TAC[QOSET_FLD; IN_ELIM_THM] THEN DISCH_THEN(K ALL_TAC)] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN REWRITE_TAC[chain; GSYM CONJ_ASSOC] THEN
  ANTS_TAC THENL [X_GEN_TAC `c:A ring->bool` THEN
    ASM_CASES_TAC `c:A ring->bool = {}` THENL
     [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN EXISTS_TAC `k:A ring` THEN
      ASM_REWRITE_TAC[ALGEBRAIC_EXTENSION_REFL; FIELD_EXTENSION_REFL];
      STRIP_TAC] THEN
    MP_TAC(ISPEC `c:A ring->bool` RING_DIRECT_LIMIT) THEN ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[field_extension]) THEN
      ASM_MESON_TAC[RING_MONOMORPHISM_I];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:A ring` THEN STRIP_TAC] THEN
    REWRITE_TAC[FIELD_EXTENSION_REFL] THEN SUBGOAL_THEN `!f:A ring. f IN c
                 ==> field f /\ ring_monomorphism(k,f) I /\
                     algebraic_extension(k,f) I` ASSUME_TAC THENL
     [ASM_MESON_TAC[ALGEBRAIC_EXTENSION; field_extension];
      FIRST_X_ASSUM(K ALL_TAC o SPECL [`k:A ring`; `k:A ring`])] THEN
    SUBGOAL_THEN `field(l:A ring)` ASSUME_TAC THENL
     [REWRITE_TAC[field; GSYM TRIVIAL_RING_10] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MEMBER_NOT_EMPTY;
            FIELD_IMP_NONTRIVIAL_RING; TRIVIAL_RING_MONOMORPHIC_IMAGE_EQ];
        ASM_REWRITE_TAC[IMP_CONJ; FORALL_IN_UNIONS; EXISTS_IN_UNIONS;
                        RIGHT_FORALL_IMP_THM; RIGHT_EXISTS_AND_THM;
                        FORALL_IN_GSPEC; EXISTS_IN_GSPEC]] THEN
      X_GEN_TAC `f:A ring` THEN DISCH_TAC THEN
      X_GEN_TAC `a:A` THEN REPEAT DISCH_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `f:A ring`)) THEN
      ASM_REWRITE_TAC[ring_monomorphism; ring_homomorphism; I_THM] THEN
      STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[field] THEN DISCH_THEN(MP_TAC o SPEC `a:A` o CONJUNCT2) THEN
      ASM_MESON_TAC[]; ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN `field_extension (k,l) (I:A->A)` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM I_O_ID] THEN
      MATCH_MP_TAC FIELD_EXTENSION_TRANS THEN
        ASM_REWRITE_TAC[field_extension] THEN
      FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN(X_CHOOSE_TAC `f0:A ring`) THEN
      EXISTS_TAC `f0:A ring` THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ALGEBRAIC_EXTENSION; field_extension];
      ASM_REWRITE_TAC[ALGEBRAIC_EXTENSION]] THEN
    REWRITE_TAC[UNIONS_GSPEC; FORALL_IN_GSPEC] THEN X_GEN_TAC `z:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `f:A ring` STRIP_ASSUME_TAC) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `f:A ring`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ALGEBRAIC_EXTENSION]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `z:A`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `p:(1->num)->A` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `I:A->A`) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL
     [`k:A ring`; `f:A ring`; `l:A ring`; `I:A->A`; `(:1)`;
      `(\v. z):1->A`; `I:A->A`; `p:(1->num)->A`]
        POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[I_O_ID] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[I_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ring_monomorphism; ring_homomorphism; I_THM]) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:A ring` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[algebraically_closed_field] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ALGEBRAIC_EXTENSION; field_extension]; ALL_TAC]] THEN
  SUBGOAL_THEN `ring_carrier(l:A ring) <_c (:A)` ASSUME_TAC THENL
    [MP_TAC(ISPECL
     [`I:A->A`; `k:A ring`; `l:A ring`;
       `(ring_carrier k:A->bool) CROSS (:num)`]
     CARD_LE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC[INFINITE; FINITE_CROSS_EQ; UNIV_NOT_EMPTY] THEN
    ANTS_TAC THENL [REWRITE_TAC[REWRITE_RULE[INFINITE] num_INFINITE;
                  RING_CARRIER_NONEMPTY] THEN
      TRANS_TAC CARD_LE_TRANS `(ring_carrier k:A->bool) *_c {0}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_EQ_IMP_LE THEN MESON_TAC[CARD_EQ_SYM; CARD_MUL_RID];
        REWRITE_TAC[CROSS; GSYM mul_c] THEN MATCH_MP_TAC CARD_LE_MUL THEN
        REWRITE_TAC[CARD_LE_UNIV; CARD_LE_REFL]];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LET_TRANS) THEN
      REWRITE_TAC[CROSS; GSYM mul_c] THEN
      MATCH_MP_TAC CARD_MUL_LT_INFINITE THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[INFINITE_CARD_LE; CARD_LT_IMP_LE]]; ALL_TAC] THEN
  X_GEN_TAC `p:(1->num)->A` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:A ring`; `p:(1->num)->A`]
   KRONECKER_SIMPLE_FIELD_EXTENSION) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`m:(((1->num)->A)->bool)ring`; `h:A->((1->num)->A)->bool`;
    `z:((1->num)->A)->bool`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL
    [`h:A->((1->num)->A)->bool`; `l:A ring`; `m:(((1->num)->A)->bool)ring`;
     `z:((1->num)->A)->bool`] FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[algebraic_over] THEN EXISTS_TAC `p:(1->num)->A` THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval] THEN
    ASM_MESON_TAC[POLY_DEG_0; POLY_RING]; DISCH_TAC] THEN SUBGOAL_THEN
   `?h':(((1->num)->A)->bool)->A.
        (!x y. x IN ring_carrier m /\ y IN ring_carrier m /\ h' x = h' y
               ==> x = y) /\
        (!x. x IN ring_carrier l ==> h'(h x) = x)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `ring_carrier(m:(((1->num)->A)->bool)ring) <=_c (:A) DIFF ring_carrier l`
    MP_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) CARD_DIFF_ABSORB o rand o snd) THEN
      ASM_SIMP_TAC[INFINITE_CARD_LE; CARD_LT_IMP_LE] THEN
      GEN_REWRITE_TAC LAND_CONV [CARD_EQ_SYM] THEN
      DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_IMP_LE) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CARD_LE_TRANS) THEN MP_TAC(ISPECL
       [`(h:A->((1->num)->A)->bool) o (I:A->A)`;
        `k:A ring`; `m:(((1->num)->A)->bool)ring`; `(:A)`]
       CARD_LE_ALGEBRAIC_EXTENSION) THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[INFINITE_CARD_LE; CARD_LT_IMP_LE] THEN
      MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN
      ASM_MESON_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION];
      REWRITE_TAC[le_c; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `h'':(((1->num)->A)->bool)->A` THEN
    REWRITE_TAC[IN_DIFF; INJECTIVE_ON_ALT] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_monomorphism]) THEN
    REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN
    DISCH_THEN(X_CHOOSE_TAC `h':(((1->num)->A)->bool)->A`) THEN EXISTS_TAC
     `\x. if x IN IMAGE (h:A->((1->num)->A)->bool) (ring_carrier l)
          then (h':(((1->num)->A)->bool)->A) x else h'' x` THEN
    SIMP_TAC[] THEN REPEAT STRIP_TAC THEN TRY EQ_TAC THEN SIMP_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ring_homomorphism]) THEN ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ISOMORPHIC_TRANSPORT_OF_RING)] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:A ring`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:A ring`) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `algebraic_extension(l,n) (I:A->A)` MP_TAC THENL
     [MATCH_MP_TAC ALGEBRAIC_EXTENSION_EQ THEN EXISTS_TAC
       `(h':(((1->num)->A)->bool)->A) o (h:A->((1->num)->A)->bool)` THEN
      ASM_SIMP_TAC[o_THM; I_THM] THEN
      MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN
      EXISTS_TAC `m:(((1->num)->A)->bool)ring` THEN
      ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION;
                   ALGEBRAIC_EXTENSION_ISOMORPHISM];
      ASM_MESON_TAC[I_O_ID; algebraic_extension; ALGEBRAIC_EXTENSION_TRANS]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; I_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(h':(((1->num)->A)->bool)->A) z`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_IMAGE]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC`(h':(((1->num)->A)->bool)->A) z`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
     [field_extension; finite_extension; RING_ISOMORPHISM;
      ring_monomorphism; IMAGE_I; ring_homomorphism]) THEN ASM SET_TAC[]);;

let ALGEBRAIC_CLOSURE_EXISTS = prove
 (`!k:A ring.
        INFINITE(:B) /\ ring_carrier k <=_c (:B) /\ field k
        ==> ?l (f:A->B). algebraic_extension (k,l) f /\
                         algebraically_closed_field l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(:A) <_c (:A#num->bool) /\ (:num) <_c (:A#num->bool)`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN
    TRANS_TAC CARD_LET_TRANS `(:A#num)` THEN
    REWRITE_TAC[CANTOR_THM_UNIV] THENL
     [TRANS_TAC CARD_LE_TRANS `(:A) *_c {one}`;
      TRANS_TAC CARD_LE_TRANS `{one} *_c (:num)`] THEN
     SIMP_TAC[GSYM MUL_C_UNIV; CARD_LE_MUL; CARD_SING_LE; UNIV_NOT_EMPTY;
              CARD_LE_REFL] THEN
     MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
     REWRITE_TAC[CARD_MUL_LID; CARD_MUL_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `(:A#num->bool)`] ISOMORPHIC_SUBCOPY_OF_RING) THEN
  ANTS_TAC THENL [TRANS_TAC CARD_LE_TRANS `(:A)` THEN
    ASM_SIMP_TAC[CARD_LE_SUBSET; CARD_LT_IMP_LE; SUBSET_UNIV];
    REWRITE_TAC[SUBSET_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `k':(A#num->bool)ring` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISOMORPHIC_RING_FIELDNESS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k':(A#num->bool)ring` ALGEBRAIC_CLOSURE_EXISTS_ID) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [TRANS_TAC CARD_LET_TRANS `(:A)` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC CARD_LE_TRANS `ring_carrier(k:A ring)` THEN
    ASM_SIMP_TAC[CARD_LE_SUBSET; SUBSET_UNIV] THEN
    MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    MATCH_MP_TAC ISOMORPHIC_RING_CARD_EQ THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `l':(A#num->bool)ring`
      (STRIP_ASSUME_TAC o REWRITE_RULE[algebraically_closed_field]))] THEN
  MP_TAC(ISPECL [`l':(A#num->bool)ring`; `(:B)`]
    ISOMORPHIC_SUBCOPY_OF_RING) THEN
  REWRITE_TAC[SUBSET_UNIV] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`I:(A#num->bool)->(A#num->bool)`;
                   `k':(A#num->bool)ring`; `l':(A#num->bool)ring`; `(:B)`]
        CARD_LE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    TRANS_TAC CARD_LE_TRANS `ring_carrier(k:A ring)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    MATCH_MP_TAC ISOMORPHIC_RING_CARD_EQ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MONO_EXISTS] THEN X_GEN_TAC `l:B ring` THEN DISCH_TAC THEN
  SUBGOAL_THEN `field(l:B ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ALGEBRAIC_EXTENSION; field_extension;
                  ISOMORPHIC_RING_FIELDNESS]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `f:A->A#num->bool` o
    GEN_REWRITE_RULE I [isomorphic_ring]) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:(A#num->bool)->B` o
    GEN_REWRITE_RULE I [isomorphic_ring]) THEN
  EXISTS_TAC `(g:(A#num->bool)->B) o (f:A->A#num->bool)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN
    EXISTS_TAC `l':(A#num->bool)ring` THEN
    ASM_SIMP_TAC[ALGEBRAIC_EXTENSION_ISOMORPHISM] THEN
    GEN_REWRITE_TAC RAND_CONV [SYM(CONJUNCT1(SPEC_ALL I_O_ID))] THEN
    MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN
    EXISTS_TAC `k':(A#num->bool)ring` THEN
    ASM_SIMP_TAC[ALGEBRAIC_EXTENSION_ISOMORPHISM];
    ASM_REWRITE_TAC[algebraically_closed_field] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `g':B->A#num->bool` MP_TAC o
        GEN_REWRITE_RULE I [ring_isomorphism]) THEN
    REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN STRIP_TAC THEN
    X_GEN_TAC `p:(1->num)->B` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g':B->A#num->bool) o (p:(1->num)->B)`) THEN
    MP_TAC(ISPECL
     [`l:B ring`; `l':(A#num->bool)ring`; `g':B->A#num->bool`; `(:1)`]
     IN_RING_POLYNOMIAL_CARRIER_COMPOSE) THEN
    ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM] THEN
    DISCH_THEN(K ALL_TAC) THEN MP_TAC(ISPECL
      [`l:B ring`; `l':(A#num->bool)ring`; `g':B->A#num->bool`;
        `p:(1->num)->B`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_MONOMORPHISM; RING_POLYNOMIAL] THEN
    DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A#num->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g:(A#num->bool)->B) w` THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[RING_ISOMORPHISM]) THEN ASM SET_TAC[];
      DISCH_TAC] THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `g:(A#num->bool)->B`) THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[RING_ISOMORPHISM; RING_HOMOMORPHISM_0]] THEN
    MP_TAC(ISPECL [`l':(A#num->bool)ring`; `l:B ring`; `w:A#num->bool`;
     `g:(A#num->bool)->B`; `(g':B->A#num->bool) o (p:(1->num)->B)`]
        POLY_EVAL_HOMOMORPHIC_IMAGE) THEN MP_TAC(ISPECL
     [`l:B ring`; `l':(A#num->bool)ring`; `g':B->A#num->bool`; `(:1)`]
     IN_RING_POLYNOMIAL_CARRIER_COMPOSE) THEN
    ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM] THEN
    DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [POLY_RING; IN_ELIM_THM; ring_polynomial; ring_powerseries]) THEN
    ASM_SIMP_TAC[]]);;

let ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH = prove
 (`!k:A ring.
        field k
        ==> ?l (f:A->A#num). algebraic_extension (k,l) f /\
                             algebraically_closed_field l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALGEBRAIC_CLOSURE_EXISTS THEN
  ASM_REWRITE_TAC[INFINITE; GSYM MUL_C_UNIV; CARD_MUL_FINITE_EQ; UNIV_NOT_EMPTY;
                  REWRITE_RULE[INFINITE] num_INFINITE] THEN
  TRANS_TAC CARD_LE_TRANS `(:A)` THEN REWRITE_TAC[CARD_LE_UNIV] THEN
  REWRITE_TAC[le_c; IN_UNIV] THEN EXISTS_TAC `\a:A. (a, 0)` THEN
  REWRITE_TAC[PAIR_EQ; IN_UNIV; MUL_C_UNIV]);;

let ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT = prove
 (`!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C).
        algebraic_extension(k,l) f /\ algebraically_closed_field l /\
        algebraic_extension(k,l') g /\ algebraically_closed_field l'
        ==> ?h. ring_isomorphism(l,l') h /\
                (!x. x IN ring_carrier k ==> h(f x) = g x)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `field (l:B ring) /\ field (l':C ring) /\
     ring_homomorphism(k:A ring,l':C ring) g /\
     field_extension(k:A ring,l:B ring) f` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_MESON_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
     algebraic_extension; field_extension; ring_monomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `l':C ring`; `f:A->B`; `g:A->C`]
    ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:B->C` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h:B->C` THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `ring_monomorphism(l:B ring,l':C ring) (h:B->C)` ASSUME_TAC
    THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `field_extension(l:B ring,l':C ring) (h:B->C)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[field_extension]; ALL_TAC] THEN
  MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_NO_PROPER_ALGEBRAIC_EXTENSION THEN
  ASM_REWRITE_TAC[algebraic_extension] THEN X_GEN_TAC `x:C` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `h:B->C`; `k:A ring`; `l:B ring`; `l':C ring`;
    `x:C`] ALGEBRAIC_OVER_ALGEBRAIC_EXTENSION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ISPECL [`k:A ring`; `l':C ring`; `x:C`;
    `g:A->C`; `((h:B->C) o (f:A->B)):A->C`] ALGEBRAIC_OVER_EQ) THEN
  ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[algebraic_extension]);;

let ALGEBRAIC_CLOSURE_UNIQUE = prove
 (`!(k:A ring) (l:B ring) (l':C ring) (f:A->B) (g:A->C).
        algebraic_extension(k,l) f /\ algebraically_closed_field l /\
        algebraic_extension(k,l') g /\ algebraically_closed_field l'
        ==> l isomorphic_ring l'`,
  REWRITE_TAC[isomorphic_ring] THEN
  MESON_TAC[ALGEBRAIC_CLOSURE_UNIQUE_EXPLICIT]);;

(* ------------------------------------------------------------------------- *)
(* Splitting extensions.                                                     *)
(* ------------------------------------------------------------------------- *)

let poly_splits_over = new_definition
 `poly_splits_over (k:A ring,l:B ring) (h:A->B) (p:(1->num)->A) <=>
        poly_splits l ((h:A->B) o p)`;;

let POLY_SPLITS_OVER_EQ_IRREDUCIBLES = prove
 (`!(h:A->B) k l p.
        field_extension (k,l) h /\
        p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k)
        ==> (poly_splits_over (k,l) h p <=>
             !q. ring_irreducible(poly_ring l (:1)) q /\
                 ring_divides(poly_ring l (:1)) q (h o p)
                 ==> poly_deg l q = 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poly_splits_over] THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_polynomial k (p:(1->num)->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_POLYNOMIAL; POLY_RING]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:A->B) o (p:(1->num)->A)) IN ring_carrier(poly_ring l (:1))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    ASM_MESON_TAC[ring_monomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `~((h:A->B) o (p:(1->num)->A) = poly_0 l)` ASSUME_TAC THENL
   [ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o (p:(1->num)->A)`]
    POLY_SPLITS_EQ_IRREDUCIBLES) THEN
  ASM_REWRITE_TAC[]);;

let POLY_SPLITS_OVER_EXPLICIT = prove
 (`!(h:A->B) k l p.
        field_extension (k,l) h /\
        p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k)
        ==> (poly_splits_over (k,l) h p <=>
             ?c a. c IN ring_carrier l /\ ~(c = ring_0 l) /\
                   (!i. 1 <= i /\ i <= poly_deg k p
                        ==> a i IN ring_carrier l) /\
                   (h o p) = poly_mul l (poly_const l c)
                         (ring_product (poly_ring l (:1)) (1..poly_deg k p)
                            (\i. poly_sub l (poly_var l one)
                                            (poly_const l (a i)))))`,
  REWRITE_TAC[poly_splits_over] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_polynomial k (p:(1->num)->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_POLYNOMIAL; POLY_RING]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:A->B) o (p:(1->num)->A)) IN ring_carrier(poly_ring l (:1))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    ASM_MESON_TAC[ring_monomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `~((h:A->B) o (p:(1->num)->A) = poly_0 l)` ASSUME_TAC THENL
   [ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg l ((h:A->B) o (p:(1->num)->A)) = poly_deg k p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC POLY_DEG_MONOMORPHIC_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o (p:(1->num)->A)`]
    POLY_SPLITS_CASES) THEN
  ASM_REWRITE_TAC[]);;

let POLY_SPLITS_OVER_EXTENSION = prove
 (`!(f:A->B) (g:B->C) k l m p.
        ring_homomorphism(l,m) g /\ poly_splits_over (k,l) f p
        ==> poly_splits_over (k,m) (g o f) p`,
  REWRITE_TAC[poly_splits_over; GSYM o_ASSOC] THEN
  MESON_TAC[POLY_SPLITS_HOMOMORPHIC_IMAGE]);;

let POLY_ROOT_BOUND_EXTENSION = prove
 (`!(h:A->B) k l p.
        field_extension(k,l) h /\
        p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k)
        ==> FINITE {x | x IN ring_carrier l /\
                        poly_eval l (h o p) x = ring_0 l} /\
            CARD {x | x IN ring_carrier l /\
                      poly_eval l (h o p) x = ring_0 l} <= poly_deg k p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `ring_polynomial k (p:(1->num)->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_POLY_RING_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) o p IN ring_carrier(poly_ring l (:1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o (p:(1->num)->A)`]
    POLY_ROOT_BOUND) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:(1->num)->A`]
    POLY_DEG_MONOMORPHIC_IMAGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:(1->num)->A`]
    POLY_EQ_0_MONOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN;
               CONJUNCT1(CONJUNCT2 POLY_RING_CLAUSES)]);;

let POLY_SPLITS_OVER_SQUAREFREE_ROOT_COUNT = prove
 (`!(h:A->B) k l p.
        field_extension (k,l) h /\ p IN ring_carrier(poly_ring k (:1)) /\
        poly_splits_over (k,l) h p /\
        ring_squarefree (poly_ring l (:1)) (h o p)
        ==> CARD {x | x IN ring_carrier l /\
                      poly_eval l (h o p) x = ring_0 l} =
            poly_deg k p`,
  REWRITE_TAC[field_extension; poly_splits_over] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o (p:(1->num)->A)`]
    POLY_SPLITS_SQUAREFREE_ROOT_COUNT) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC POLY_DEG_MONOMORPHIC_IMAGE THEN
  ASM_MESON_TAC[RING_POLYNOMIAL]);;

let POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT = prove
 (`!(h:A->B) k l p.
        field_extension (k,l) h /\ p IN ring_carrier(poly_ring k (:1)) /\
        poly_splits_over (k,l) h p /\ poly_separable k p
        ==> CARD {x | x IN ring_carrier l /\
                      poly_eval l (h o p) x = ring_0 l} =
            poly_deg k p`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC POLY_SPLITS_OVER_SQUAREFREE_ROOT_COUNT THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POLY_SEPARABLE_IMP_SQUAREFREE THEN
  MATCH_MP_TAC POLY_SEPARABLE_MONOMORPHIC_IMAGE THEN
  ASM_MESON_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* Splitting extensions of a polynomial p over k: p splits in l and l is     *)
(* generated over k by the roots of p. The zero polynomial is excluded: it   *)
(* splits and every element is a root of it. Nonzero constants are allowed;  *)
(* their splitting extensions are the trivial ones (h an isomorphism).       *)
(* ------------------------------------------------------------------------- *)

let splitting_extension = new_definition
 `splitting_extension (k:A ring,l:B ring) (h:A->B) (p:(1->num)->A) <=>
        field_extension(k,l) h /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = poly_0 k) /\
        poly_splits_over (k,l) h p /\
        subfield_generated l
          (IMAGE h (ring_carrier k) UNION
           {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}) = l`;;

let SPLITTING_EXTENSION_I = prove
 (`!(k:A ring) l p.
        splitting_extension(k,l) I p <=>
        field_extension(k,l) I /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = poly_0 k) /\
        poly_splits l p /\
        subfield_generated l
          (ring_carrier k UNION
           {x | x IN ring_carrier l /\ poly_eval l p x = ring_0 l}) = l`,
  REWRITE_TAC[splitting_extension; poly_splits_over; I_O_ID; IMAGE_I]);;

let SPLITTING_IMP_FIELD_EXTENSION = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p
        ==> field_extension(k,l) h`,
  SIMP_TAC[splitting_extension]);;

let SPLITTING_EXTENSION_IN_POLY_RING = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p
        ==> p IN ring_carrier(poly_ring k (:1))`,
  SIMP_TAC[splitting_extension]);;

let SPLITTING_EXTENSION_NONZERO = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p
        ==> ~(p = poly_0 k)`,
  SIMP_TAC[splitting_extension]);;

let SPLITTING_EXTENSION_SPLITS = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p
        ==> poly_splits_over (k,l) h p`,
  SIMP_TAC[splitting_extension]);;

let SPLITTING_EXTENSION_GENERATED = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p
        ==> subfield_generated l
              (IMAGE h (ring_carrier k) UNION
               {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}) =
            l`,
  SIMP_TAC[splitting_extension]);;

let SPLITTING_IMP_FINITELY_GENERATED_EXTENSION = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p
        ==> finitely_generated_extension(k,l) h`,
  REWRITE_TAC[splitting_extension; finitely_generated_extension] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC
   `{x | x IN ring_carrier l /\ poly_eval l ((h:A->B) o p) x = ring_0 l}` THEN
  ASM_REWRITE_TAC[SUBSET_RESTRICT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_ROOT_BOUND o snd) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[field_extension; FIELD_IMP_INTEGRAL_DOMAIN];
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    ASM_MESON_TAC[field_extension; ring_monomorphism];
    REWRITE_TAC[POLY_RING] THEN
    ASM_MESON_TAC[field_extension; POLY_EQ_0_MONOMORPHIC_IMAGE;
                  RING_POLYNOMIAL]]);;

let SPLITTING_IMP_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p
        ==> algebraic_extension(k,l) h`,
  REWRITE_TAC[splitting_extension; algebraic_extension] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
        [SYM th]) THEN
  MATCH_MP_TAC ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `y:B` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[algebraic_over] THEN
  EXISTS_TAC `p:(1->num)->A` THEN ASM_REWRITE_TAC[CONJUNCT2 POLY_RING] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_EXTEND_EVALUATE o lhand o snd) THEN
  ASM_REWRITE_TAC[GSYM poly_eval] THEN
  ASM_MESON_TAC[field_extension; ring_monomorphism]);;

let SPLITTING_IMP_FINITE_EXTENSION = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p
        ==> finite_extension(k,l) h`,
  REWRITE_TAC[FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION] THEN
  MESON_TAC[SPLITTING_IMP_FINITELY_GENERATED_EXTENSION;
            SPLITTING_IMP_ALGEBRAIC_EXTENSION]);;

let SPLITTING_EXTENSION_GENERATED_BY_ROOTS = prove
 (`!(h:A->B) k l p.
        field_extension(k,l) h /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = poly_0 k) /\
        poly_splits_over (k,l) h p
        ==> splitting_extension
              (k,subfield_generated l
                   (IMAGE h (ring_carrier k) UNION
                    {x | x IN ring_carrier l /\
                         poly_eval l (h o p) x = ring_0 l}))
              h p`,
  REWRITE_TAC[poly_splits_over] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  ASM_REWRITE_TAC[splitting_extension] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN ASM SET_TAC[];
    REWRITE_TAC[poly_splits_over] THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC POLY_SPLITS_IN_SUBRING THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[COEFF_COMPOSE] THEN
      MATCH_MP_TAC SUBFIELD_GENERATED_INC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [RING_POLYNOMIAL_COEFF; GSYM RING_POLYNOMIAL;
      ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(MESON[SUBFIELD_GENERATED_IDEMPOT]
     `(s:B->bool) = t ==> subfield_generated (subfield_generated r s) t =
                          subfield_generated r s`) THEN
    MATCH_MP_TAC(SET_RULE
     `l' SUBSET l /\ (!x:B. x IN l' ==> (P' x <=> P x)) /\
      (!x. x IN l /\ P x ==> x IN l')
      ==> k UNION {x | x IN l /\ P x} = k UNION {x | x IN l' /\ P' x}`) THEN
    REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
    SIMP_TAC[SUBFIELD_GENERATED_INC_GEN; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    REWRITE_TAC[SUBRING_GENERATED] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC POLY_EVAL_SUBRING_GENERATED THEN
    ASM_REWRITE_TAC[SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ring_monomorphism; ring_homomorphism]) THEN
    ASM SET_TAC[]]);;

let SPLITTING_EXTENSION_LIFT = prove
 (`!(h:A->B) k l p s t.
        field l /\ s subfield_of l /\ t subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET t /\
        splitting_extension(k,subfield_generated l s) h p
        ==> splitting_extension
              (subfield_generated l t,subfield_generated l (s UNION t)) I
              (h o p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [splitting_extension]) THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; poly_splits_over;
               CONJUNCT1(CONJUNCT2 SUBFIELD_GENERATED)] THEN
  ABBREV_TAC
   `r = {x | x IN s /\
             poly_eval (subfield_generated l s) ((h:A->B) o (p:(1->num)->A)) x =
             ring_0 l}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier k) SUBSET s` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ring_homomorphism] o
      MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `ring_carrier:B ring->B->bool` o
    check (fun th -> is_eq(concl th) &&
                     rand(concl th) = `subfield_generated l (s:B->bool)`)) THEN
  SUBGOAL_THEN `IMAGE (h:A->B) (ring_carrier k) UNION r SUBSET s` ASSUME_TAC
  THENL [EXPAND_TAC "r" THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUBFIELD_GENERATED_IDEMPOT_GEN;
               CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!u. IMAGE (h:A->B) (ring_carrier k) SUBSET u
        ==> field_extension(k,subfield_generated l u) h /\
            h o p IN ring_carrier(poly_ring (subfield_generated l u) (:1))`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:B->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                     `subfield_generated l (s:B->bool)`; `l:B ring`]
        FIELD_EXTENSION_TRANS) THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; I_O_ID];
      DISCH_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC `k:A ring` THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(s:B->bool) SUBSET ring_carrier(subfield_generated l (s UNION t)) /\
    (t:B->bool) SUBSET ring_carrier(subfield_generated l (s UNION t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[SUBFIELD_OF_IMP_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. (u:B->bool) subfield_of l /\ u SUBSET s UNION t
        ==> field_extension
             (subfield_generated l u,subfield_generated l (s UNION t)) I`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; IMAGE_I;
                 CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  REWRITE_TAC[splitting_extension; poly_splits_over; I_O_ID; IMAGE_I] THEN
  SUBGOAL_THEN `ring_carrier(subfield_generated l t) = (t:B->bool)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
                    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_UNION];
    ASM_SIMP_TAC[];
    ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE; RING_POLYNOMIAL; POLY_RING;
                  FIELD_EXTENSION_IMP_MONOMORPHISM];
    SUBST1_TAC(SYM(CONJUNCT1(ISPEC `(h:A->B) o (p:(1->num)->A)` I_O_ID))) THEN
    MATCH_MP_TAC POLY_SPLITS_HOMOMORPHIC_IMAGE THEN
    EXISTS_TAC `subfield_generated l (s:B->bool)` THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM; SUBSET_UNION];
    ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 SUBFIELD_GENERATED)] THEN
  ABBREV_TAC
   `r' = {x | x IN ring_carrier(subfield_generated l (s UNION t)) /\
              poly_eval (subfield_generated l (s UNION t))
                        ((h:A->B) o (p:(1->num)->A)) x = ring_0 l}` THEN
  SUBGOAL_THEN `(r:B->bool) SUBSET r'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "r'"] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier(subfield_generated l (s UNION t))`
    ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN
     `(h:A->B) o (p:(1->num)->A) IN
      ring_carrier(poly_ring (subfield_generated l (s UNION t)) (:1))`
    ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_UNION; SUBSET_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `s UNION t:B->bool`;
                   `(h:A->B) o (p:(1->num)->A)`; `x:B`]
      POLY_EVAL_SUBFIELD_GENERATED) THEN
    MP_TAC(ISPECL [`l:B ring`; `s:B->bool`;
                   `(h:A->B) o (p:(1->num)->A)`; `x:B`]
      POLY_EVAL_SUBFIELD_GENERATED) THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `t UNION r' SUBSET ring_carrier(subfield_generated l (s UNION t:B->bool))`
  ASSUME_TAC THENL [EXPAND_TAC "r'" THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBFIELD_GENERATED_SUPERSET] THEN
  ASM_SIMP_TAC[SUBFIELD_GENERATED_IDEMPOT_GEN] THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN
  ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED; UNION_SUBSET] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o
      check (fun th -> is_eq(concl th) && rand(concl th) = `s:B->bool`)) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_CARRIER_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[SUBFIELD_OF_IMP_SUBSET] THEN SET_TAC[]]);;

(* A splitting extension of a product p * q is a tower: the subfield         *)
(* generated by the roots of p is a splitting extension of p, and l is a     *)
(* splitting extension of q over it. Hence (by induction on the degree, via  *)
(* the field generated by one root in the irreducible case) the degree of a  *)
(* splitting extension of p divides (deg p)!.                                *)

let SPLITTING_EXTENSION_FACTOR = prove
 (`!(h:A->B) k l p q.
        splitting_extension(k,l) h (poly_mul k p q) /\
        p IN ring_carrier(poly_ring k (:1)) /\
        q IN ring_carrier(poly_ring k (:1))
        ==> splitting_extension
             (k,subfield_generated l
                  (IMAGE h (ring_carrier k) UNION
                   {x | x IN ring_carrier l /\
                        poly_eval l (h o p) x = ring_0 l}))
             h p /\
            splitting_extension
             (subfield_generated l
                  (IMAGE h (ring_carrier k) UNION
                   {x | x IN ring_carrier l /\
                        poly_eval l (h o p) x = ring_0 l}),
              l) I (h o q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o REWRITE_RULE[splitting_extension; poly_splits_over])
   STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `ring_polynomial k (p:(1->num)->A) /\ ring_polynomial k (q:(1->num)->A) /\
    ring_polynomial l ((h:A->B) o p) /\ ring_polynomial l ((h:A->B) o q)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN CONJ_TAC THEN
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:A->B) o poly_mul k (p:(1->num)->A) q = poly_mul l (h o p) (h o q)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `poly_ring (l:B ring) (:1)`;
                   `\p:(1->num)->A. (h:A->B) o p`] RING_HOMOMORPHISM_MUL) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_RINGS; POLY_RING_CLAUSES;
                 IN_ELIM_THM; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:(1->num)->A = poly_0 k) /\ ~(q:(1->num)->A = poly_0 k)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[POLY_MUL_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_splits l ((h:A->B) o (p:(1->num)->A)) /\
    poly_splits l ((h:A->B) o (q:(1->num)->A))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC POLY_SPLITS_DIVISOR THEN
    EXISTS_TAC `(h:A->B) o poly_mul k (p:(1->num)->A) q` THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        lhand(concl th) = `(h:A->B) o poly_mul k (p:(1->num)->A) q`)) THEN
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`;
                     `poly_mul k (p:(1->num)->A) q`]
        POLY_EQ_0_MONOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL_MUL];
      REWRITE_TAC[ring_divides; POLY_RING_CLAUSES; IN_ELIM_THM;
                  SUBSET_UNIV] THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL_MUL] THEN
      ASM_MESON_TAC[POLY_MUL_SYM; RING_POLYNOMIAL_IMP_POWERSERIES]]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SPLITTING_EXTENSION_GENERATED_BY_ROOTS THEN
    ASM_REWRITE_TAC[poly_splits_over];
    ALL_TAC] THEN
  ABBREV_TAC
   `s = IMAGE (h:A->B) (ring_carrier k) UNION
        {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}` THEN
  SUBGOAL_THEN `field_extension(k,subfield_generated l s) (h:A->B)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[splitting_extension; poly_splits_over; I_O_ID; IMAGE_I] THEN
  ASM_REWRITE_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM];
    REWRITE_TAC[poly_0; POLY_CONST_SUBFIELD_GENERATED;
                CONJUNCT1(CONJUNCT2 SUBFIELD_GENERATED)] THEN
    REWRITE_TAC[GSYM poly_0] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `q:(1->num)->A`]
      POLY_EQ_0_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBFIELD_GENERATED_UNION_LEFT] THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
      check (fun th -> rand(concl th) = `l:B ring`)) THEN
    AP_TERM_TAC THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:B` THEN ASM_CASES_TAC `(x:B) IN ring_carrier l` THEN
    ASM_SIMP_TAC[POLY_EVAL_MUL; INTEGRAL_DOMAIN_MUL_EQ_0;
                 FIELD_IMP_INTEGRAL_DOMAIN; POLY_EVAL] THEN
    CONV_TAC TAUT]);;

let SPLITTING_EXTENSION_DEGREE_DIVIDES_FACT =
  let lemma = prove
   (`!n (k:B ring) l p.
        splitting_extension(k,l) I p /\ poly_deg k p = n
        ==> extension_degree(k,l) I divides FACT n`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
    DISCH_THEN(LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`k:B ring`; `l:B ring`; `p:(1->num)->B`] THEN
    STRIP_TAC THEN
    MP_TAC(ASSUME `splitting_extension(k,l) (I:B->B) p`) THEN
    REWRITE_TAC[splitting_extension; poly_splits_over; I_O_ID; IMAGE_I] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_IMP_FINITE_EXTENSION) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET_I) THEN
    ABBREV_TAC
     `R = {x | x IN ring_carrier l /\
               poly_eval l (p:(1->num)->B) x = ring_0 l}` THEN
    ASM_CASES_TAC `(R:B->bool) SUBSET ring_carrier k` THENL
     [SUBGOAL_THEN `extension_degree(k,l) (I:B->B) = 1`
       (fun th -> REWRITE_TAC[th; DIVIDES_1]) THEN
      ASM_SIMP_TAC[EXTENSION_DEGREE_EQ_1; IMAGE_I] THEN
      MP_TAC(ISPECL [`I:B->B`; `k:B ring`; `l:B ring`]
        RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE) THEN
      ASM_REWRITE_TAC[IMAGE_I] THEN
      DISCH_THEN(ASSUME_TAC o MATCH_MP CARRIER_SUBFIELD_GENERATED_SUBFIELD o
        CONJUNCT1) THEN
      FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
        [SYM th]) o check (fun th -> rand(concl th) = `l:B ring`)) THEN
      ASM_SIMP_TAC[SET_RULE `(r:B->bool) SUBSET s ==> s UNION r = s`];
      ALL_TAC] THEN
    UNDISCH_TAC `~((R:B->bool) SUBSET ring_carrier k)` THEN
    EXPAND_TAC "R" THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `algebraic_over(k,l) (I:B->B) a` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION; algebraic_extension];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`I:B->B`; `k:B ring`; `l:B ring`; `a:B`]
      MINIMAL_POLYNOMIAL_DEG_EQ_1) THEN
    MP_TAC(ISPECL [`I:B->B`; `k:B ring`; `l:B ring`; `a:B`; `p:(1->num)->B`]
      MINIMAL_POLYNOMIAL_DIVIDES) THEN
    MP_TAC(ISPECL [`I:B->B`; `k:B ring`; `l:B ring`; `a:B`]
      MINIMAL_POLYNOMIAL) THEN
    ASM_REWRITE_TAC[IMAGE_I] THEN
    ABBREV_TAC `f = minimal_polynomial (k,l) (I:B->B) a` THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval; I_O_ID] THEN
    REWRITE_TAC[ring_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(1->num)->B` STRIP_ASSUME_TAC o
      CONJUNCT2 o CONJUNCT2) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[POLY_RING_CLAUSES] o
      check (fun th -> lhand(concl th) = `p:(1->num)->B` &&
                       is_eq(concl th))) THEN
    SUBGOAL_THEN
     `ring_polynomial k (f:(1->num)->B) /\ ring_polynomial k (g:(1->num)->B) /\
      ~(g = poly_0 k)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(p:(1->num)->B = poly_0 k)` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[POLY_MUL_0; RING_POLYNOMIAL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `poly_deg k (poly_mul k (f:(1->num)->B) g) =
      poly_deg k (f:(1->num)->B) + poly_deg k (g:(1->num)->B)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC POLY_DEG_MUL THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN];
      ALL_TAC] THEN
    SUBGOAL_THEN `2 <= poly_deg k (f:(1->num)->B)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:B ring`; `f:(1->num)->B`]
        IRREDUCIBLE_IMP_POLY_DEG_NZ) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `poly_deg k (f:(1->num)->B) + poly_deg k (g:(1->num)->B) = n`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        lhand(concl th) = `poly_deg k (poly_mul k (f:(1->num)->B) g)`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        lhand(concl th) = `p:(1->num)->B` && is_eq(concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `poly_deg k (g:(1->num)->B) = 0` THENL
     [ALL_TAC;
      MP_TAC(ISPECL [`I:B->B`; `k:B ring`; `l:B ring`; `f:(1->num)->B`;
                     `g:(1->num)->B`] SPLITTING_EXTENSION_FACTOR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          lhand(concl th) = `p:(1->num)->B` && is_eq(concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[I_O_ID; IMAGE_I] THEN
      ABBREV_TAC
       `L = subfield_generated l
              (ring_carrier k UNION
               {x | x IN ring_carrier l /\
                    poly_eval l (f:(1->num)->B) x = ring_0 l})` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `field_extension(k,L) (I:B->B) /\ field_extension(L,l) (I:B->B)`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[SPLITTING_IMP_FIELD_EXTENSION]; ALL_TAC] THEN
      MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
       [`I:B->B`; `I:B->B`; `k:B ring`; `L:B ring`; `l:B ring`]
       EXTENSION_DEGREE_TOWER_LAW)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      TRANS_TAC DIVIDES_TRANS
       `FACT(poly_deg k (f:(1->num)->B)) *
        FACT(poly_deg k (g:(1->num)->B))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DIVIDES_MUL2 THEN CONJ_TAC THENL
         [REMOVE_THEN "ih" (MP_TAC o SPEC `poly_deg k (f:(1->num)->B)`) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
          EXISTS_TAC `f:(1->num)->B` THEN ASM_REWRITE_TAC[];
          REMOVE_THEN "ih" (MP_TAC o SPEC `poly_deg k (g:(1->num)->B)`) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
          EXISTS_TAC `g:(1->num)->B` THEN ASM_REWRITE_TAC[] THEN
          EXPAND_TAC "L" THEN REWRITE_TAC[POLY_DEG_SUBFIELD_GENERATED] THEN
          MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
           [`k:B ring`; `l:B ring`; `I:B->B`; `g:(1->num)->B`]
           POLY_DEG_MONOMORPHIC_IMAGE)) THEN
          ASM_REWRITE_TAC[]];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          rand(concl th) = `n:num` && is_comb(lhand(concl th)) &&
          fst(dest_const(fst(strip_comb(lhand(concl th))))) = "+")) THEN
        REWRITE_TAC[divides] THEN
        EXISTS_TAC
         `binom(poly_deg k (f:(1->num)->B) + poly_deg k (g:(1->num)->B),
                poly_deg k g)` THEN
        REWRITE_TAC[GSYM MULT_ASSOC; BINOM_FACT]]] THEN
    SUBGOAL_THEN `poly_deg k (f:(1->num)->B) = n` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`I:B->B`; `k:B ring`; `l:B ring`; `a:B`]
      EXTENSION_DEGREE_SIMPLE) THEN
    MP_TAC(ISPECL [`I:B->B`; `k:B ring`; `l:B ring`; `a:B`]
      FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    MP_TAC(ISPECL [`I:B->B`; `k:B ring`; `l:B ring`; `a:B`]
      FIELD_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC[IMAGE_I] THEN
    ABBREV_TAC `K = subring_generated l ((a:B) INSERT ring_carrier k)` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `field_extension(K,l) (I:B->B) /\ (a:B) IN ring_carrier K /\
      ring_carrier K subfield_of l /\ subfield_generated l (ring_carrier K) = K`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "K" THEN
        MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
        ASM_REWRITE_TAC[FIELD_EXTENSION_REFL] THEN ASM_MESON_TAC[];
        EXPAND_TAC "K" THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
        ASM_REWRITE_TAC[IN_INSERT];
        EXPAND_TAC "K" THEN REWRITE_TAC[subfield_of] THEN
        REWRITE_TAC[SUBRING_SUBRING_GENERATED;
                    SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "K" THEN
        MP_TAC(ISPECL [`l:B ring`; `(a:B) INSERT ring_carrier k`]
          SUBRING_EQ_SUBFIELD_GENERATED) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
      lhand(concl th) = `p:(1->num)->B` && is_eq(concl th))) THEN
    SUBGOAL_THEN `ring_carrier k SUBSET ring_carrier(K:B ring)` ASSUME_TAC THENL
     [MATCH_MP_TAC FIELD_EXTENSION_IMP_SUBSET_I THEN
      ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION];
      ALL_TAC] THEN
    SUBGOAL_THEN `splitting_extension(K,l) (I:B->B) p` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`I:B->B`; `k:B ring`; `l:B ring`; `p:(1->num)->B`;
                     `ring_carrier l:B->bool`; `ring_carrier K:B->bool`]
        SPLITTING_EXTENSION_LIFT) THEN
      ASM_REWRITE_TAC[SUBFIELD_GENERATED_RING_CARRIER; CARRIER_SUBFIELD_OF;
                      IMAGE_I; I_O_ID] THEN
      SUBGOAL_THEN
       `ring_carrier l UNION ring_carrier K:B->bool = ring_carrier l`
      SUBST1_TAC THENL
       [ASM_MESON_TAC[FIELD_EXTENSION_IMP_SUBSET_I; SET_RULE
         `(t:B->bool) SUBSET s ==> s UNION t = s`];
        REWRITE_TAC[SUBFIELD_GENERATED_RING_CARRIER]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      concl th = `subfield_generated l (ring_carrier K) = (K:B ring)`)) THEN
    SUBGOAL_THEN `(p:(1->num)->B) IN ring_carrier(poly_ring K (:1))`
    ASSUME_TAC THENL
     [SUBST1_TAC(SYM(CONJUNCT1(ISPEC `p:(1->num)->B` I_O_ID))) THEN
      MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC `k:B ring` THEN
      ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION;
                   FIELD_EXTENSION_IMP_HOMOMORPHISM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`K:B ring`; `a:B`; `p:(1->num)->B`]
      POLY_DIVIDES_X_MINUS_ROOT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
      W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_SUBRING_GENERATED o
        lhand o snd) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED];
      ALL_TAC] THEN
    REWRITE_TAC[ring_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->B` STRIP_ASSUME_TAC o
      CONJUNCT2 o CONJUNCT2) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o REWRITE_RULE[POLY_RING_CLAUSES] o
      check (fun th -> lhand(concl th) = `p:(1->num)->B` &&
                       is_eq(concl th))) THEN
    MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`;
                   `poly_sub K (poly_var K one) (poly_const K (a:B))`;
                   `q:(1->num)->B`] SPLITTING_EXTENSION_FACTOR) THEN
    ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER; I_O_ID; IMAGE_I] THEN
    ABBREV_TAC
     `L = subfield_generated l
           (ring_carrier K UNION
            {x | x IN ring_carrier l /\
                 poly_eval l (poly_sub K (poly_var K one) (poly_const K (a:B)))
                   x = ring_0 l})` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `poly_deg K (p:(1->num)->B) = n` ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[POLY_DEG_SUBRING_GENERATED] THEN
      MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
       [`k:B ring`; `l:B ring`; `I:B->B`; `p:(1->num)->B`]
       POLY_DEG_MONOMORPHIC_IMAGE)) THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_polynomial K (poly_sub K (poly_var K one) (poly_const K (a:B))) /\
      ring_polynomial K (q:(1->num)->B) /\
      poly_deg K (poly_sub K (poly_var K one) (poly_const K (a:B))) = 1 /\
      ~(poly_sub K (poly_var K one) (poly_const K (a:B)) = poly_0 K) /\
      ~(q = poly_0 K)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RING_POLYNOMIAL; POLY_X_MINUS_A_IN_CARRIER;
                   POLY_DEG_X_MINUS_A; POLY_X_MINUS_A_NONZERO;
                   FIELD_IMP_NONTRIVIAL_RING] THEN
      DISCH_TAC THEN UNDISCH_TAC `poly_deg K (p:(1->num)->B) = n` THEN
      UNDISCH_TAC
       `poly_mul K (poly_sub K (poly_var K one) (poly_const K (a:B))) q =
        (p:(1->num)->B)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[POLY_MUL_0; RING_POLYNOMIAL; POLY_X_MINUS_A_IN_CARRIER;
                   POLY_DEG_0] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `poly_deg K (q:(1->num)->B) = n - 1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`K:B ring`;
                     `poly_sub K (poly_var K one) (poly_const K (a:B))`;
                     `q:(1->num)->B`] POLY_DEG_MUL) THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `poly_deg L (q:(1->num)->B) = n - 1` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[POLY_DEG_SUBFIELD_GENERATED] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `poly_deg K (q:(1->num)->B) = n - 1`)) THEN
      EXPAND_TAC "K" THEN REWRITE_TAC[POLY_DEG_SUBRING_GENERATED];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `field_extension(K,L) (I:B->B) /\ field_extension(L,l) (I:B->B)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SPLITTING_IMP_FIELD_EXTENSION]; ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
     [`I:B->B`; `I:B->B`; `k:B ring`; `K:B ring`; `l:B ring`]
     EXTENSION_DEGREE_TOWER_LAW)) THEN
    MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
     [`I:B->B`; `I:B->B`; `K:B ring`; `L:B ring`; `l:B ring`]
     EXTENSION_DEGREE_TOWER_LAW)) THEN
    ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `FACT n = n * FACT(n - 1)` SUBST1_TAC THENL
     [MP_TAC(SPEC `n - 1` (CONJUNCT2 FACT)) THEN
      SUBGOAL_THEN `SUC(n - 1) = n` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC DIVIDES_MUL2 THEN REWRITE_TAC[DIVIDES_REFL] THEN
    MATCH_MP_TAC(MESON[DIVIDES_MUL2; MULT_CLAUSES]
     `a divides 1 /\ b divides c ==> (a * b) divides c`) THEN
    CONJ_TAC THENL
     [REMOVE_THEN "ih" (MP_TAC o SPEC `1`) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_FACT_CONV) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
      EXISTS_TAC `poly_sub K (poly_var K one) (poly_const K (a:B))` THEN
      ASM_REWRITE_TAC[];
      REMOVE_THEN "ih" (MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL
       [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
      EXISTS_TAC `q:(1->num)->B` THEN ASM_REWRITE_TAC[]]) in
  prove
   (`!(h:A->B) k l p.
        splitting_extension(k,l) h p
        ==> extension_degree(k,l) h divides FACT(poly_deg k p)`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
      RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`;
                   `ring_carrier l:B->bool`; `IMAGE (h:A->B) (ring_carrier k)`]
      SPLITTING_EXTENSION_LIFT) THEN
    ASM_REWRITE_TAC[SUBFIELD_GENERATED_RING_CARRIER; CARRIER_SUBFIELD_OF;
                    SUBSET_REFL] THEN
    SUBGOAL_THEN
     `ring_carrier l UNION IMAGE (h:A->B) (ring_carrier k) = ring_carrier l`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[FIELD_EXTENSION_IMP_SUBSET; SET_RULE
       `(t:B->bool) SUBSET s ==> s UNION t = s`];
      REWRITE_TAC[SUBFIELD_GENERATED_RING_CARRIER] THEN DISCH_TAC] THEN
    MP_TAC(ISPECL [`poly_deg k (p:(1->num)->A)`;
                   `subfield_generated l (IMAGE (h:A->B) (ring_carrier k))`;
                   `l:B ring`; `(h:A->B) o (p:(1->num)->A)`] lemma) THEN
    ASM_REWRITE_TAC[POLY_DEG_SUBFIELD_GENERATED] THEN ANTS_TAC THENL
     [MATCH_MP_TAC POLY_DEG_MONOMORPHIC_IMAGE THEN
      ASM_MESON_TAC[splitting_extension; RING_POLYNOMIAL];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC EXTENSION_DEGREE_EQ_IMAGE THEN
      ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; IMAGE_I]]);;

let SPLITTING_EXTENSION_EXISTS_ID = prove
 (`!(k:A ring) p.
        field k /\ p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k) /\
        ring_carrier k <_c (:A) /\ (:num) <_c (:A)
        ==> ?l. splitting_extension(k,l) I p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_ID) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `om:A ring` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `field_extension(k:A ring,om) I` ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  EXISTS_TAC
   `subfield_generated om
       (IMAGE (I:A->A) (ring_carrier k) UNION
        {x | x IN ring_carrier om /\
             poly_eval om ((I:A->A) o p) x = ring_0 om}):A ring` THEN
  MATCH_MP_TAC SPLITTING_EXTENSION_GENERATED_BY_ROOTS THEN
  ASM_REWRITE_TAC[poly_splits_over] THEN
  MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
  EXISTS_TAC `k:A ring` THEN
  ASM_MESON_TAC[field_extension; ring_monomorphism]);;

let SPLITTING_EXTENSION_EXISTS = prove
 (`!(k:A ring) p.
        field k /\ p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k) /\
        INFINITE(:B) /\ ring_carrier k <=_c (:B)
        ==> ?(l:B ring) h. splitting_extension(k,l) h p`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS) THEN
  ASM_REWRITE_TAC[algebraic_extension; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`om:B ring`; `h:A->B`] THEN STRIP_TAC THEN
  EXISTS_TAC `subfield_generated om
       (IMAGE (h:A->B) (ring_carrier k) UNION
        {x | x IN ring_carrier om /\ poly_eval om (h o p) x = ring_0 om})` THEN
  EXISTS_TAC `h:A->B` THEN
  MATCH_MP_TAC SPLITTING_EXTENSION_GENERATED_BY_ROOTS THEN
  ASM_REWRITE_TAC[poly_splits_over] THEN
  MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
  ASM_MESON_TAC[IN_RING_POLYNOMIAL_CARRIER_COMPOSE;
                FIELD_EXTENSION_IMP_HOMOMORPHISM]);;

let SPLITTING_EXTENSION_EXISTS_BIGENOUGH = prove
 (`!(k:A ring) p.
        field k /\ p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k)
        ==> ?l (h:A->A#num). splitting_extension(k,l) h p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[algebraic_extension; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`om:(A#num)ring`; `h:A->A#num`] THEN STRIP_TAC THEN
  EXISTS_TAC `subfield_generated om
       (IMAGE (h:A->A#num) (ring_carrier k) UNION
        {x | x IN ring_carrier om /\ poly_eval om (h o p) x = ring_0 om})` THEN
  EXISTS_TAC `h:A->A#num` THEN
  MATCH_MP_TAC SPLITTING_EXTENSION_GENERATED_BY_ROOTS THEN
  ASM_REWRITE_TAC[poly_splits_over] THEN
  MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
  ASM_MESON_TAC[IN_RING_POLYNOMIAL_CARRIER_COMPOSE;
                FIELD_EXTENSION_IMP_HOMOMORPHISM]);;

let SPLITTING_EXTENSION_IMAGE = prove
 (`!(h:A->B) (f:B->C) k l m p.
        splitting_extension(k,l) h p /\ field_extension(l,m) f
        ==> IMAGE f (ring_carrier l) =
            ring_carrier(subfield_generated m
              (IMAGE (f o h) (ring_carrier k) UNION
               {x | x IN ring_carrier m /\
                    poly_eval m ((f o h) o p) x = ring_0 m}))`,
  REWRITE_TAC[splitting_extension; poly_splits_over; field_extension] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`l:B ring`; `m:C ring`; `f:B->C`;
    `IMAGE (h:A->B) (ring_carrier k) UNION
     {x | x IN ring_carrier l /\ poly_eval l ((h:A->B) o p) x = ring_0 l}`]
   SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[UNION_SUBSET; SUBSET_RESTRICT] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ring_monomorphism; ring_homomorphism]) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[IMAGE_UNION; IMAGE_o; GSYM o_ASSOC] THEN
  REPEAT AP_TERM_TAC THEN MATCH_MP_TAC POLY_ROOTS_MONOMORPHIC_IMAGE THEN
  ASM_MESON_TAC[FIELD_IMP_INTEGRAL_DOMAIN; POLY_EQ_0_MONOMORPHIC_IMAGE;
                RING_POLYNOMIAL]);;

let SPLITTING_EXTENSION_IMAGES_EQ = prove
 (`!(h:A->B) (h':A->C) (f:B->D) (f':C->D) k l l' m p.
        splitting_extension(k,l) h p /\ splitting_extension(k,l') h' p /\
        field_extension(l,m) f /\ field_extension(l',m) f' /\
        (!x. x IN ring_carrier k ==> f(h x) = f'(h' x))
        ==> IMAGE f (ring_carrier l) = IMAGE f' (ring_carrier l')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h':A->C`; `f':C->D`; `k:A ring`; `l':C ring`; `m:D ring`;
                 `p:(1->num)->A`] SPLITTING_EXTENSION_IMAGE) THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->D`; `k:A ring`; `l:B ring`; `m:D ring`;
                 `p:(1->num)->A`] SPLITTING_EXTENSION_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `((f:B->D) o (h:A->B)) o (p:(1->num)->A) =
                ((f':C->D) o (h':A->C)) o p`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP SPLITTING_EXTENSION_IN_POLY_RING) THEN
    REWRITE_TAC[IN_POLY_RING_CARRIER; ring_polynomial; ring_powerseries] THEN
    ASM_SIMP_TAC[FUN_EQ_THM; o_THM];
    REPEAT AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC IMAGE_EQ THEN ASM_REWRITE_TAC[o_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of splitting extensions, by an isomorphism compatible with the *)
(* maps from k. Proof: extend the map from k to an embedding of the first    *)
(* extension in an algebraic closure of the second; the images of both       *)
(* coincide by SPLITTING_EXTENSION_IMAGES_EQ.                                *)
(* ------------------------------------------------------------------------- *)

let SPLITTING_EXTENSION_UNIQUE_EXPLICIT = prove
 (`!(h:A->B) (h':A->C) k l l' p.
        splitting_extension(k,l) h p /\ splitting_extension(k,l') h' p
        ==> ?j. ring_isomorphism(l,l') j /\
                !x. x IN ring_carrier k ==> j(h x) = h' x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `algebraic_extension(k:A ring,l:B ring) h /\
                field_extension(k:A ring,l':C ring) h' /\
                field(l:B ring) /\ field(l':C ring)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SPLITTING_IMP_ALGEBRAIC_EXTENSION;
                  SPLITTING_IMP_FIELD_EXTENSION; field_extension];
    ALL_TAC] THEN
  MP_TAC(ISPEC `l':C ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[algebraic_extension] THEN
  DISCH_THEN(X_CHOOSE_THEN `om:(C#num)ring`
    (X_CHOOSE_THEN `g:C->C#num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `om:(C#num)ring`; `h:A->B`;
                 `(g:C->C#num) o (h':A->C)`]
    ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_TRANS; FIELD_EXTENSION_IMP_HOMOMORPHISM];
    DISCH_THEN(X_CHOOSE_THEN `f:B->C#num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `field_extension(l:B ring,om:(C#num)ring) f` ASSUME_TAC THENL
   [ASM_MESON_TAC[field_extension; FIELD_RING_HOMOMORPHISM_MONOMORPHISM;
                  FIELD_IMP_NONTRIVIAL_RING;
                  ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `h':A->C`; `f:B->C#num`; `g:C->C#num`;
                 `k:A ring`; `l:B ring`; `l':C ring`; `om:(C#num)ring`;
                 `p:(1->num)->A`] SPLITTING_EXTENSION_IMAGES_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:C->C#num`; `l':C ring`; `om:(C#num)ring`]
    RING_ISOMORPHISM_ONTO_IMAGE) THEN
  MP_TAC(ISPECL [`f:B->C#num`; `l:B ring`; `om:(C#num)ring`]
    RING_ISOMORPHISM_ONTO_IMAGE) THEN
  ASM_SIMP_TAC[ring_image; FIELD_EXTENSION_IMP_MONOMORPHISM] THEN
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `g':C#num->C` MP_TAC o
    GEN_REWRITE_RULE I [ring_isomorphism]) THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN STRIP_TAC THEN
  EXISTS_TAC `(g':C#num->C) o (f:B->C#num)` THEN
  ASM_MESON_TAC[RING_ISOMORPHISM_COMPOSE; FIELD_EXTENSION_CARRIER; o_THM]);;

let SPLITTING_EXTENSION_EXTEND_HOMOMORPHISM = prove
 (`!(h:A->B) (g:A->C) k l m p.
        splitting_extension(k,l) h p /\ field_extension(k,m) g /\
        poly_splits_over(k,m) g p
        ==> ?e. ring_homomorphism(l,m) e /\
                !x. x IN ring_carrier k ==> e(h x) = g x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_IN_POLY_RING) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_EXTENSION_NONZERO) THEN
  MP_TAC(ISPECL [`g:A->C`; `k:A ring`; `m:C ring`; `p:(1->num)->A`]
    SPLITTING_EXTENSION_GENERATED_BY_ROOTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `t = IMAGE (g:A->C) (ring_carrier k) UNION
        {x | x IN ring_carrier m /\ poly_eval m (g o p) x = ring_0 m}` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`;
                 `subfield_generated m (t:C->bool)`; `p:(1->num)->A`]
    SPLITTING_EXTENSION_UNIQUE_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `e:B->C` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
  DISCH_THEN(MP_TAC o C CONJ (ISPECL [`m:C ring`; `t:C->bool`]
    RING_HOMOMORPHISM_SUBFIELD_INCLUSION)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_HOMOMORPHISM_COMPOSE) THEN
  REWRITE_TAC[I_O_ID]);;

let SPLITTING_EXTENSION_UNIQUE = prove
 (`!(h:A->B) (h':A->C) k l l' p.
        splitting_extension(k,l) h p /\ splitting_extension(k,l') h' p
        ==> l isomorphic_ring l'`,
  REWRITE_TAC[isomorphic_ring] THEN
  MESON_TAC[SPLITTING_EXTENSION_UNIQUE_EXPLICIT]);;

(* ------------------------------------------------------------------------- *)
(* Normal extensions: algebraic extensions such that every irreducible       *)
(* polynomial over k with a root in l splits over l.                         *)
(* ------------------------------------------------------------------------- *)

let normal_extension = new_definition
 `normal_extension (k:A ring,l:B ring) (h:A->B) <=>
        algebraic_extension (k,l) h /\
        (!p. ring_irreducible(poly_ring k (:1)) p /\
             (?a. a IN ring_carrier l /\ poly_eval l (h o p) a = ring_0 l)
             ==> poly_splits_over (k,l) h p)`;;

let NORMAL_IMP_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l.
        normal_extension (k,l) h ==> algebraic_extension (k,l) h`,
  SIMP_TAC[normal_extension]);;

let NORMAL_IMP_FIELD_EXTENSION = prove
 (`!(h:A->B) k l. normal_extension (k,l) h ==> field_extension (k,l) h`,
  SIMP_TAC[normal_extension; ALGEBRAIC_IMP_FIELD_EXTENSION]);;

let NORMAL_EXTENSION_I = prove
 (`!(k:A ring) l.
        normal_extension (k,l) I <=>
        algebraic_extension (k,l) I /\
        (!p. ring_irreducible(poly_ring k (:1)) p /\
             (?a. a IN ring_carrier l /\ poly_eval l p a = ring_0 l)
             ==> poly_splits l p)`,
  REWRITE_TAC[normal_extension; poly_splits_over; I_O_ID]);;

let NORMAL_EXTENSION_ISOMORPHISM = prove
 (`!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism (k,l) f
        ==> normal_extension (k,l) f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[normal_extension; poly_splits_over;
               ALGEBRAIC_EXTENSION_ISOMORPHISM] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FIELD_EXTENSION_ISOMORPHISM) THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [RING_ISOMORPHISM] o
    CONJUNCT2) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  X_GEN_TAC `p:(1->num)->A` THEN ASM_REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
  MATCH_MP_TAC POLY_DEG_1_IMP_SPLITS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `f:A->B`; `p:(1->num)->A`]
    POLY_DEG_MONOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `n = 1 ==> n <= 1`) THEN
  MATCH_MP_TAC IRREDUCIBLE_ROOT_IMP_DEG_EQ_1 THEN
  EXISTS_TAC `b:A` THEN ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `f:A->B`; `poly_eval k p (b:A)`]
    RING_MONOMORPHISM_EQ_0) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `b:A`; `f:A->B`; `p:(1->num)->A`]
    POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[POLY_EVAL]);;

let NORMAL_EXTENSION_REFL = prove
 (`!k:A ring. normal_extension (k,k) I <=> field k`,
  MESON_TAC[NORMAL_IMP_FIELD_EXTENSION; FIELD_EXTENSION_REFL;
            NORMAL_EXTENSION_ISOMORPHISM; RING_ISOMORPHISM_I]);;

let ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION = prove
 (`!(h:A->B) k l.
        algebraic_extension(k,l) h /\ algebraically_closed_field l
        ==> normal_extension(k,l) h`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[normal_extension; poly_splits_over] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
  EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[RING_IRREDUCIBLE_IN_CARRIER] THEN
  ASM_MESON_TAC[ALGEBRAIC_IMP_FIELD_EXTENSION; field_extension;
                RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

let NORMAL_EXTENSION_EQ_MINIMAL_POLYNOMIALS_SPLIT = prove
 (`!(h:A->B) k l.
        normal_extension(k,l) h <=>
        algebraic_extension(k,l) h /\
        !x. x IN ring_carrier l
            ==> poly_splits_over (k,l) h (minimal_polynomial(k,l) h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[normal_extension] THEN
  ASM_CASES_TAC `algebraic_extension(k:A ring,l:B ring) h` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
     [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IRREDUCIBLE] THEN
    EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `l:B ring`; `l:B ring`;
                   `x:B`] MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_I; I_O_ID; I_THM];
    ALL_TAC] THEN
  X_GEN_TAC `p:(1->num)->A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) a` ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
  ABBREV_TAC `q = minimal_polynomial (k,l) (h:A->B) a` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_divides (poly_ring k (:1)) (p:(1->num)->A) q`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`; `a:B`]
      MINIMAL_POLYNOMIAL_ASSOCIATES_IRREDUCIBLE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[ring_associates];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_splits l ((h:A->B) o (q:(1->num)->A))` ASSUME_TAC THENL
   [ASM_MESON_TAC[poly_splits_over]; ALL_TAC] THEN
  REWRITE_TAC[poly_splits_over] THEN MATCH_MP_TAC POLY_SPLITS_DIVISOR THEN
  EXISTS_TAC `(h:A->B) o (q:(1->num)->A)` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE; RING_POLYNOMIAL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_DIVIDES_HOMOMORPHIC_IMAGE o CONJ
   (ISPEC `(:1)` (MATCH_MP RING_HOMOMORPHISM_POLY_RINGS
     (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM
       (ASSUME `ring_monomorphism(k:A ring,l:B ring) h`))))) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Characterization by embeddings: homomorphisms from a normal extension l   *)
(* into an integral domain that agree on k have the same image, and this     *)
(* characterizes normality when the target is algebraically closed.          *)
(* ------------------------------------------------------------------------- *)

let NORMAL_EXTENSION_IMAGES_EQ = prove
 (`!(h:A->B) (f:B->C) f' k l m.
        normal_extension(k,l) h /\ integral_domain m /\
        ring_homomorphism(l,m) f /\ ring_homomorphism(l,m) f' /\
        (!x. x IN ring_carrier k ==> f(h x) = f'(h x))
        ==> IMAGE f (ring_carrier l) = IMAGE f' (ring_carrier l)`,
  SUBGOAL_THEN
   `!(h:A->B) (f:B->C) f' k l m.
        normal_extension(k,l) h /\ integral_domain m /\
        ring_homomorphism(l,m) f /\ ring_homomorphism(l,m) f' /\
        (!x. x IN ring_carrier k ==> f(h x) = f'(h x))
        ==> IMAGE f (ring_carrier l) SUBSET IMAGE f' (ring_carrier l)`
  (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
             CONJ_TAC THEN MATCH_MP_TAC th THEN
             MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `m:C ring`] THEN
             ASM_SIMP_TAC[]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [normal_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `algebraic_over (k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  ABBREV_TAC `p = minimal_polynomial (k,l) (h:A->B) x` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `l:B ring`; `l:B ring`;
                 `x:B`] MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `x:B`] MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_I; I_O_ID; I_THM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `poly_eval m ((f':B->C) o (h:A->B) o p) ((f:B->C) x) = ring_0 m`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(f':B->C) o (h:A->B) o (p:(1->num)->A) = (f o h) o p`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `(p:(1->num)->A) IN ring_carrier(poly_ring k (:1))` THEN
    REWRITE_TAC[IN_POLY_RING_CARRIER; ring_polynomial; ring_powerseries] THEN
    ASM_SIMP_TAC[FUN_EQ_THM; o_THM];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_MONOMORPHISM) THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `f':B->C`;
                 `(h:A->B) o (p:(1->num)->A)`]
    POLY_ROOTS_MONOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING] THEN
      ASM_MESON_TAC[field_extension];
      ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE; RING_POLYNOMIAL];
      FIRST_X_ASSUM(MP_TAC o SPEC `p:(1->num)->A`) THEN
      ASM_REWRITE_TAC[poly_splits_over] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:B->C) x IN ring_carrier m` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:B->C) x`) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let NORMAL_EXTENSION_EQ_EMBEDDINGS = prove
 (`!(h:A->B) (j:B->C) k l m.
        algebraically_closed_field m /\ ring_homomorphism(l,m) j
        ==> (normal_extension(k,l) h <=>
             algebraic_extension(k,l) h /\
             !g. ring_homomorphism(l,m) g /\
                 (!x. x IN ring_carrier k ==> g(h x) = j(h x))
                 ==> IMAGE g (ring_carrier l) = IMAGE j (ring_carrier l))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[NORMAL_IMP_ALGEBRAIC_EXTENSION] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NORMAL_EXTENSION_IMAGES_EQ THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `m:C ring`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[normal_extension; poly_splits_over] THEN
  X_GEN_TAC `p:(1->num)->A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `ring_homomorphism(k,m) ((j:B->C) o (h:A->B))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `j:B->C`;
                 `(h:A->B) o (p:(1->num)->A)`]
    POLY_SPLITS_MONOMORPHIC_PREIMAGE) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
    ASM_REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    X_GEN_TAC `b:C` THEN STRIP_TAC] THEN
  SUBGOAL_THEN `algebraic_over (k,l) (h:A->B) a` ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  ABBREV_TAC `q = minimal_polynomial (k,l) (h:A->B) a` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:C ring`; `h:A->B`;
                 `(j:B->C) o (h:A->B)`; `a:B`; `b:C`]
    ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT) THEN
  ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `g:B->C` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:B->C`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[]] THEN
  SUBGOAL_THEN `ring_divides (poly_ring k (:1)) (p:(1->num)->A) q`
  MP_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`; `a:B`]
      MINIMAL_POLYNOMIAL_ASSOCIATES_IRREDUCIBLE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[ring_associates];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_DIVIDES_HOMOMORPHIC_IMAGE o CONJ
   (ISPEC `(:1)` (MATCH_MP RING_HOMOMORPHISM_POLY_RINGS
     (ASSUME `ring_homomorphism(k,m) ((j:B->C) o (h:A->B))`)))) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((j:B->C) o (h:A->B)) o (p:(1->num)->A) IN ring_carrier(poly_ring m (:1)) /\
    ((j:B->C) o (h:A->B)) o (q:(1->num)->A) IN ring_carrier(poly_ring m (:1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_divides (poly_ring m (:1))
      (poly_sub m (poly_var m one) (poly_const m (b:C)))
      (((j:B->C) o (h:A->B)) o (p:(1->num)->A))`
  MP_TAC THENL
   [ASM_SIMP_TAC[POLY_DIVIDES_X_MINUS_ROOT_EQ] THEN
    ASM_REWRITE_TAC[GSYM o_ASSOC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP RING_DIVIDES_TRANS o C CONJ (ASSUME
   `ring_divides (poly_ring m (:1)) (((j:B->C) o (h:A->B)) o p)
                 ((j o h) o (q:(1->num)->A))`)) THEN
  ASM_SIMP_TAC[POLY_DIVIDES_X_MINUS_ROOT_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The finite normal extensions are exactly the splitting extensions.        *)
(* ------------------------------------------------------------------------- *)

let SPLITTING_EXTENSION_IMP_NORMAL = prove
 (`!(h:A->B) k l p.
        splitting_extension(k,l) h p ==> normal_extension(k,l) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SPLITTING_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SPLITTING_IMP_FIELD_EXTENSION) THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:(B#num)ring`; `j:B->B#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->B#num`; `k:A ring`; `l:B ring`;
                 `m:(B#num)ring`] NORMAL_EXTENSION_EQ_EMBEDDINGS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `g:B->B#num` THEN STRIP_TAC THEN
  MATCH_MP_TAC SPLITTING_EXTENSION_IMAGES_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`h:A->B`; `h:A->B`; `k:A ring`; `m:(B#num)ring`; `p:(1->num)->A`] THEN
  ASM_REWRITE_TAC[field_extension] THEN
  MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
  ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING]);;

let NORMAL_EXTENSION_GENERATED_BY_ROOTS = prove
 (`!(h:A->B) k l p.
        field_extension(k,l) h /\
        p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = poly_0 k) /\
        poly_splits_over (k,l) h p
        ==> normal_extension
              (k,subfield_generated l
                   (IMAGE h (ring_carrier k) UNION
                    {x | x IN ring_carrier l /\
                         poly_eval l (h o p) x = ring_0 l}))
              h`,
  MESON_TAC[SPLITTING_EXTENSION_GENERATED_BY_ROOTS;
            SPLITTING_EXTENSION_IMP_NORMAL]);;

let SPLITTING_EQ_FINITE_NORMAL_EXTENSION = prove
 (`!(h:A->B) k l.
        (?p. splitting_extension(k,l) h p) <=>
        finite_extension(k,l) h /\ normal_extension(k,l) h`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[SPLITTING_IMP_FINITE_EXTENSION; SPLITTING_EXTENSION_IMP_NORMAL];
    STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [FINITE_EQ_FINITELY_GENERATED_ALGEBRAIC_EXTENSION]) THEN
  REWRITE_TAC[finitely_generated_extension] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `!x:B. x IN b ==> algebraic_over (k,l) (h:A->B) x`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[algebraic_extension]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `ring_product (poly_ring k (:1)) b
                (minimal_polynomial (k,l) (h:A->B))` THEN
  SUBGOAL_THEN
   `(h:A->B) o ring_product (poly_ring k (:1)) b (minimal_polynomial (k,l) h) =
    ring_product (poly_ring l (:1)) b (\x. h o minimal_polynomial (k,l) h x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`minimal_polynomial (k,l) (h:A->B)`; `b:B->bool`]
     (MATCH_MP RING_HOMOMORPHISM_PRODUCT (ISPEC `(:1)`
       (MATCH_MP RING_HOMOMORPHISM_POLY_RINGS
         (ASSUME `ring_homomorphism (k,l) (h:A->B)`))))) THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:B. x IN b
          ==> poly_eval l ((h:A->B) o minimal_polynomial (k,l) h x) x =
              ring_0 l`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `l:B ring`; `l:B ring`;
                   `x:B`] MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_I; I_O_ID; I_THM];
    ALL_TAC] THEN
  REWRITE_TAC[splitting_extension; poly_splits_over] THEN
  ASM_REWRITE_TAC[RING_PRODUCT] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `b:B->bool`;
                   `minimal_polynomial (k,l) (h:A->B)`]
      INTEGRAL_DOMAIN_PRODUCT_EQ_0) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN;
                 POLY_RING_CLAUSES] THEN
    DISCH_THEN(K ALL_TAC) THEN ASM_MESON_TAC[MINIMAL_POLYNOMIAL_NONZERO];
    MATCH_MP_TAC POLY_SPLITS_PRODUCT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [normal_extension]) THEN
    DISCH_THEN(MP_TAC o SPEC `minimal_polynomial (k,l) (h:A->B) x` o
      CONJUNCT2) THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IRREDUCIBLE; poly_splits_over] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `x:B` THEN ASM SET_TAC[];
    REWRITE_TAC[SUBFIELD_GENERATED_EQ; GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET t ==> (k:B->bool) UNION s SUBSET k UNION t`) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier l` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`\y:B. (h:A->B) o minimal_polynomial (k,l) h y`;
                   `b:B->bool`]
     (MATCH_MP RING_HOMOMORPHISM_PRODUCT (ISPEC `(:1)`
       (MATCH_MP RING_HOMOMORPHISM_POLY_EVAL
         (ASSUME `(x:B) IN ring_carrier l`))))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER];
      DISCH_THEN(SUBST1_TAC o BETA_RULE)] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRODUCT_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN;
                 o_THM] THEN
    EXISTS_TAC `x:B` THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Invariance under isomorphism, intermediate fields and composita.          *)
(* ------------------------------------------------------------------------- *)

let NORMAL_EXTENSION_ISOMORPHIC_IMAGE = prove
 (`!(h:A->B) (h':C->D) (f:A->C) (g:B->D) k l k' l'.
        normal_extension(k,l) h /\
        ring_isomorphism(k,k') f /\ ring_isomorphism(l,l') g /\
        (!x. x IN ring_carrier k ==> h'(f x) = g(h x))
        ==> normal_extension(k',l') h'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `f':C->A` MP_TAC o
    GEN_REWRITE_RULE I [ring_isomorphism]) THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NORMAL_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `field(l':D ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_ISOMORPHISM; field_extension]; ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_extension(k',l') (h':C->D)` ASSUME_TAC THENL
   [MATCH_MP_TAC ALGEBRAIC_EXTENSION_EQ THEN
    EXISTS_TAC `((g:B->D) o (h:A->B)) o (f':C->A)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN EXISTS_TAC `k:A ring` THEN
      ASM_SIMP_TAC[ALGEBRAIC_EXTENSION_ISOMORPHISM] THEN
      MATCH_MP_TAC ALGEBRAIC_EXTENSION_TRANS THEN EXISTS_TAC `l:B ring` THEN
      ASM_SIMP_TAC[ALGEBRAIC_EXTENSION_ISOMORPHISM];
      REWRITE_TAC[o_THM] THEN
      ASM_MESON_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM;
                    RING_HOMOMORPHISM_IN_CARRIER]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `l':D ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:(D#num)ring`; `j:D->D#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`h':C->D`; `j:D->D#num`; `k':C ring`; `l':D ring`;
                 `n:(D#num)ring`] NORMAL_EXTENSION_EQ_EMBEDDINGS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `g':D->D#num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN ring_carrier k
        ==> (g':D->D#num) (g((h:A->B) x)) = j (g (h x))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_ISOMORPHISM_IMP_HOMOMORPHISM;
                  RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `l':D ring`; `g:B->D`] RING_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC NORMAL_EXTENSION_IMAGES_EQ THEN
  MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`; `n:(D#num)ring`] THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
               o_THM] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE]);;

let NORMAL_EXTENSION_INTERMEDIATE = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension(k,l) f /\ field_extension(l,m) g /\
        normal_extension(k,m) (g o f)
        ==> normal_extension(l,m) g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `field(m:C ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
  MP_TAC(ISPEC `m:C ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:(C#num)ring`; `j:C->C#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`g:B->C`; `j:C->C#num`; `l:B ring`; `m:C ring`;
                 `n:(C#num)ring`] NORMAL_EXTENSION_EQ_EMBEDDINGS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
      ALGEBRAIC_EXTENSION_TRANS_EQ) THEN
    ASM_MESON_TAC[NORMAL_IMP_ALGEBRAIC_EXTENSION];
    X_GEN_TAC `g':C->C#num` THEN STRIP_TAC] THEN
  MATCH_MP_TAC NORMAL_EXTENSION_IMAGES_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(g:B->C) o (f:A->B)`; `k:A ring`; `n:(C#num)ring`] THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
               o_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[FIELD_EXTENSION_CARRIER]);;

let NORMAL_EXTENSION_COMPOSITUM = prove
 (`!(h:A->B) (h':A->C) (f:B->D) (f':C->D) k l l' m.
        normal_extension(k,l) h /\ normal_extension(k,l') h' /\
        field_extension(l,m) f /\ field_extension(l',m) f' /\
        (!x. x IN ring_carrier k ==> f(h x) = f'(h' x))
        ==> normal_extension
             (k,subfield_generated m
                  (IMAGE f (ring_carrier l) UNION IMAGE f' (ring_carrier l')))
             (f o h)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = IMAGE (f:B->D) (ring_carrier l) UNION
                  IMAGE (f':C->D) (ring_carrier l')` THEN
  ABBREV_TAC `c = subfield_generated m (s:D->bool)` THEN
  SUBGOAL_THEN `field(m:D ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:D->bool) SUBSET ring_carrier m` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[UNION_SUBSET] THEN
    ASM_MESON_TAC[FIELD_EXTENSION_IMP_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `field_extension(l,c) (f:B->D) /\ field_extension(l',c) (f':C->D)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THEN
    MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `field(c:D ring) /\ (s:D->bool) SUBSET ring_carrier c /\
                subfield_generated c s = c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; SUBFIELD_GENERATED_IDEMPOT;
                 SUBFIELD_GENERATED_SUBSET_CARRIER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `field_extension(k,c) ((f:B->D) o (h:A->B))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_TRANS; NORMAL_IMP_FIELD_EXTENSION];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:D ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:(D#num)ring`; `j:D->D#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`(f:B->D) o (h:A->B)`; `j:D->D#num`; `k:A ring`; `c:D ring`;
                 `n:(D#num)ring`] NORMAL_EXTENSION_EQ_EMBEDDINGS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[algebraic_extension] THEN
    SUBGOAL_THEN
     `!x. x IN (s:D->bool) ==> algebraic_over (k,c) ((f:B->D) o (h:A->B)) x`
    ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `y:B` THEN DISCH_TAC;
        X_GEN_TAC `y:C` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`k:A ring`; `c:D ring`; `(f':C->D) y`;
                       `(f':C->D) o (h':A->C)`; `(f:B->D) o (h:A->B)`]
          ALGEBRAIC_OVER_EQ_EQ) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[o_THM] THEN
          ASM_MESON_TAC[FIELD_EXTENSION_TRANS; NORMAL_IMP_FIELD_EXTENSION;
                        FIELD_EXTENSION_IMP_HOMOMORPHISM];
          DISCH_THEN(SUBST1_TAC o SYM)]] THEN
      MATCH_MP_TAC ALGEBRAIC_OVER_TRANS THENL
       [EXISTS_TAC `l:B ring`; EXISTS_TAC `l':C ring`] THEN
      ASM_SIMP_TAC[ALGEBRAIC_OVER_IMAGE; NORMAL_IMP_ALGEBRAIC_EXTENSION];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(f:B->D) o (h:A->B)`; `k:A ring`; `c:D ring`; `s:D->bool`]
      ALGEBRAIC_OVER_SUBFIELD_GENERATED_ALGEBRAIC) THEN
    SUBGOAL_THEN
     `IMAGE ((f:B->D) o (h:A->B)) (ring_carrier k) UNION s = s`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
      FIELD_EXTENSION_IMP_SUBSET) THEN
    ASM_SIMP_TAC[NORMAL_IMP_FIELD_EXTENSION] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[IMAGE_o] THEN SET_TAC[];
    X_GEN_TAC `g:D->D#num` THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `ring_monomorphism (c,n) (g:D->D#num) /\
    ring_monomorphism (c,n) (j:D->D#num)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_EXTENSION_IMP_MONOMORPHISM] THEN
    MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING;
                 ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism(l,n) ((g:D->D#num) o (f:B->D)) /\
    ring_homomorphism(l,n) ((j:D->D#num) o f) /\
    ring_homomorphism(l',n) (g o (f':C->D)) /\
    ring_homomorphism(l',n) (j o f')`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `c:D ring` THEN ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN ring_carrier k
         ==> ((g:D->D#num) o (f:B->D)) ((h:A->B) x) = (j o f) (h x)) /\
    (!x. x IN ring_carrier k
         ==> (g o (f':C->D)) ((h':A->C) x) = (j o f') (h' x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[o_THM] THEN RULE_ASSUM_TAC(REWRITE_RULE[o_THM]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:D ring`; `n:(D#num)ring`; `j:D->D#num`; `s:D->bool`]
    SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE) THEN
  MP_TAC(ISPECL [`c:D ring`; `n:(D#num)ring`; `g:D->D#num`; `s:D->bool`]
    SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REPEAT AP_TERM_TAC THEN EXPAND_TAC "s" THEN
  REWRITE_TAC[IMAGE_UNION; GSYM IMAGE_o] THEN BINOP_TAC THEN
  MATCH_MP_TAC NORMAL_EXTENSION_IMAGES_EQ THENL
   [EXISTS_TAC `h:A->B`; EXISTS_TAC `h':A->C`] THEN
  MAP_EVERY EXISTS_TAC [`k:A ring`; `n:(D#num)ring`] THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN;
               ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Perfect fields: characteristic 0, or the Frobenius map is surjective.     *)
(* ------------------------------------------------------------------------- *)

let perfect_field = new_definition
 `perfect_field (k:A ring) <=>
        field k /\
        (ring_char k = 0 \/
         (!x. x IN ring_carrier k
              ==> ?y. y IN ring_carrier k /\
                      ring_pow k y (ring_char k) = x))`;;

let PERFECT_FIELD_IMP_FIELD = prove
 (`!k:A ring. perfect_field k ==> field k`,
  SIMP_TAC[perfect_field]);;

let PERFECT_FIELD_CHAR_0 = prove
 (`!k:A ring. ring_char k = 0 ==> (perfect_field k <=> field k)`,
  SIMP_TAC[perfect_field]);;

let PERFECT_FIELD_POLY_DERIV_EQ_0 = prove
 (`!(k:A ring) p.
        perfect_field k /\ prime(ring_char k) /\
        p IN ring_carrier(poly_ring k (:1)) /\
        poly_deriv k p = poly_0 k
        ==> ?q. q IN ring_carrier(poly_ring k (:1)) /\
                p = ring_pow (poly_ring k (:1)) q (ring_char k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [perfect_field]) THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `rt:A->A` THEN DISCH_TAC THEN
  ABBREV_TAC `c = ring_char(k:A ring)` THEN
  ABBREV_TAC `d = poly_deg (k:A ring) (p:(1->num)->A)` THEN
  SUBGOAL_THEN `ring_polynomial k (p:(1->num)->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (rt:A->A)(coeff (c * j) (p:(1->num)->A)) IN ring_carrier k /\
        ring_pow k (rt(coeff (c * j) p)) c = coeff (c * j) p`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT];
    ALL_TAC] THEN
  EXISTS_TAC
   `ring_sum (poly_ring (k:A ring) (:1)) {j | j < d + 1}
      (\j. ring_mul (poly_ring k (:1))
             (poly_const k (rt(coeff (c * j) (p:(1->num)->A))))
             (ring_pow (poly_ring k (:1)) (poly_var k one) j))` THEN
  REWRITE_TAC[RING_SUM] THEN
  MP_TAC(ISPECL
   [`poly_ring (k:A ring) (:1)`; `1`;
    `\j. ring_mul (poly_ring (k:A ring) (:1))
           (poly_const k (rt(coeff (c * j) (p:(1->num)->A))))
           (ring_pow (poly_ring k (:1)) (poly_var k one) j)`;
    `d + 1`] FROBENIUS_SUM_POWER) THEN
  ASM_SIMP_TAC[RING_CHAR_POLY_RING; EXP_1; RING_MUL; POLY_CONST; RING_POW;
               POLY_VAR_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RING_MUL_POW; POLY_CONST; RING_POW; POLY_VAR_UNIV; RING_POW_POW;
               GSYM(MATCH_MP RING_HOMOMORPHISM_POW
                 (SPEC_ALL RING_HOMOMORPHISM_POLY_CONST))] THEN
  REWRITE_TAC[POLY_RING_CLAUSES; MULT_SYM; GSYM FUN_EQ_COEFF] THEN
  X_GEN_TAC `n:num` THEN
  W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_SUM o rand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_POLYNOMIAL_MUL THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_CONST; COEFF_IN_CARRIER_ALT;
                 RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[COEFF_POLY_LMUL; COEFF_IN_CARRIER_ALT; COEFF_POLY_VARPOW;
               RING_POLYNOMIAL_IMP_POWERSERIES; RING_POLYNOMIAL_POW;
               RING_POLYNOMIAL_VAR] THEN
  REWRITE_TAC[COND_RAND] THEN
  ASM_SIMP_TAC[RING_MUL_RID; RING_MUL_RZERO; COEFF_IN_CARRIER_ALT] THEN
  ASM_CASES_TAC `(c:num) divides n` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
      REWRITE_RULE[divides]) THEN
    TRANS_TAC EQ_TRANS
     `ring_sum k {j | j < d + 1}
        (\j. if j = m then coeff (c * m) (p:(1->num)->A) else ring_0 k)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM; COEFF_IN_CARRIER_ALT] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `m:num` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m = 1 * m`] THEN
      MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= c ==> 1 <= c`];
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[EQ_MULT_LCANCEL; PRIME_IMP_NZ] THEN
      ASM_CASES_TAC `j:num = m` THEN ASM_REWRITE_TAC[]];
    TRANS_TAC EQ_TRANS `ring_0 k:A` THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLY_DERIV_EQ_0_COEFF THEN ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
      X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_MESON_TAC[divides]]]);;

let PERFECT_FIELD_IMP_SEPARABLE = prove
 (`!(k:A ring) p.
        perfect_field k /\ ring_irreducible (poly_ring k (:1)) p
        ==> poly_separable k p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PERFECT_FIELD_IMP_FIELD) THEN
  ASM_SIMP_TAC[POLY_SEPARABLE_EQ_DERIV_NONZERO] THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP INTEGRAL_DOMAIN_CHAR o
    MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THENL
   [MP_TAC(ISPECL [`k:A ring`; `p:(1->num)->A`] POLY_DERIV_NONZERO_CHAR0) THEN
    MP_TAC(ISPECL [`k:A ring`; `p:(1->num)->A`]
      IRREDUCIBLE_IMP_POLY_DEG_NZ) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_POLYNOMIAL;
                 RING_IRREDUCIBLE_IN_CARRIER] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:(1->num)->A`]
    PERFECT_FIELD_POLY_DERIV_EQ_0) THEN
  ASM_SIMP_TAC[RING_IRREDUCIBLE_IN_CARRIER; NOT_EXISTS_THM] THEN
  X_GEN_TAC `q:(1->num)->A` THEN STRIP_TAC THEN
  UNDISCH_TAC `ring_irreducible (poly_ring k (:1)) (p:(1->num)->A)` THEN
  ASM_REWRITE_TAC[ring_irreducible] THEN
  ASM_SIMP_TAC[RING_UNIT_POW_EQ; PRIME_IMP_NZ; RING_POW] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`q:(1->num)->A`;
    `ring_pow (poly_ring (k:A ring) (:1)) q (ring_char k - 1)`]) THEN
  ASM_SIMP_TAC[RING_POW; RING_UNIT_POW_EQ; NOT_IMP] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `ring_char(k:A ring) = SUC(ring_char k - 1)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
  THENL [ASM_ARITH_TAC; REWRITE_TAC[ring_pow]]);;

let PERFECT_FIELD_SEPARABLE_EQ_SQUAREFREE = prove
 (`!(k:A ring) p.
        perfect_field k
        ==> (poly_separable k p <=> ring_squarefree (poly_ring k (:1)) p)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[POLY_SEPARABLE_IMP_SQUAREFREE] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PERFECT_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_SQUAREFREE_IN_CARRIER) THEN
  SUBGOAL_THEN `UFD(poly_ring (k:A ring) (:1))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PID_IMP_UFD; PID_POLY_RING]; ALL_TAC] THEN
  ASM_SIMP_TAC[poly_separable; UFD_COPRIME; POLY_DERIV_IN_CARRIER] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[RING_SQUAREFREE_IMP_NONZERO; TRIVIAL_POLY_RING;
                  FIELD_IMP_NONTRIVIAL_RING];
    X_GEN_TAC `q:(1->num)->A` THEN REPEAT STRIP_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_PRIME_IN_CARRIER) THEN
  UNDISCH_TAC `ring_divides (poly_ring k (:1)) q (p:(1->num)->A)` THEN
  REWRITE_TAC[ring_divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(1->num)->A` STRIP_ASSUME_TAC o
    CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `ring_coprime (poly_ring (k:A ring) (:1)) (q,s) /\
                poly_separable k (q:(1->num)->A)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
        GEN_REWRITE_RULE I [RING_SQUAREFREE_COPRIME]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRIME_IMP_IRREDUCIBLE;
                   INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_divides (poly_ring k (:1)) q
      (ring_mul (poly_ring (k:A ring) (:1)) (poly_deriv k q) s)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `ring_mul (poly_ring (k:A ring) (:1)) (poly_deriv k q) s =
      ring_sub (poly_ring k (:1)) (poly_deriv k p)
               (ring_mul (poly_ring k (:1)) q (poly_deriv k s))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[CONJUNCT2 POLY_RING_CLAUSES] THEN
      ASM_SIMP_TAC[POLY_DERIV_MUL; RING_POLYNOMIAL_IMP_POWERSERIES;
                   RING_POLYNOMIAL] THEN
      REWRITE_TAC[POLY_CLAUSES] THEN
      MATCH_MP_TAC(RING_RULE
       `(x:(1->num)->A) IN ring_carrier r /\ y IN ring_carrier r
        ==> x = ring_sub r (ring_add r x y) y`) THEN
      ASM_SIMP_TAC[RING_MUL; POLY_DERIV_IN_CARRIER];
      MATCH_MP_TAC RING_DIVIDES_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RING_DIVIDES_RMUL THEN
      ASM_SIMP_TAC[RING_DIVIDES_REFL; POLY_DERIV_IN_CARRIER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `poly_deriv k (q:(1->num)->A)`;
                 `s:(1->num)->A`; `q:(1->num)->A`]
    RING_COPRIME_DIVPROD_RIGHT) THEN
  ASM_SIMP_TAC[POLY_DERIV_IN_CARRIER; RING_COPRIME_SYM] THEN
  UNDISCH_TAC `poly_separable k (q:(1->num)->A)` THEN
  REWRITE_TAC[poly_separable; ring_coprime] THEN
  ASM_MESON_TAC[RING_DIVIDES_REFL; ring_prime]);;

let PERFECT_FIELD_EQ_FROBENIUS_AUTOMORPHISM = prove
 (`!(k:A ring).
        prime(ring_char k)
        ==> (perfect_field k <=>
             field k /\ ring_automorphism k (\x. ring_pow k x (ring_char k)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[perfect_field] THEN
  ASM_CASES_TAC `field(k:A ring)` THEN ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
  REWRITE_TAC[ring_automorphism; GSYM RING_MONOMORPHISM_EPIMORPHISM] THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_FROBENIUS; FIELD_IMP_INTEGRAL_DOMAIN] THEN
  REWRITE_TAC[ring_epimorphism] THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; RING_MONOMORPHISM_FROBENIUS;
               FIELD_IMP_INTEGRAL_DOMAIN] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN
  SIMP_TAC[RING_POW] THEN MESON_TAC[]);;

let PERFECT_FIELD_EQ_FROBENIUS_AUTOMORPHISM_GEN = prove
 (`!k:A ring.
        perfect_field k <=>
        field k /\
        (ring_char k = 0 \/
         ring_automorphism k (\x. ring_pow k x (ring_char k)))`,
  GEN_TAC THEN ASM_CASES_TAC `field(k:A ring)` THEN
  ASM_REWRITE_TAC[perfect_field] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP INTEGRAL_DOMAIN_CHAR o
    MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
  MP_TAC(ISPEC `k:A ring` PERFECT_FIELD_EQ_FROBENIUS_AUTOMORPHISM) THEN
  ASM_SIMP_TAC[perfect_field; PRIME_IMP_NZ]);;

let PERFECT_FIELD_EPIMORPHIC_IMAGE = prove
 (`!(r:A ring) (r':B ring) f.
        ring_epimorphism (r,r') f /\ perfect_field r /\ ~trivial_ring r'
        ==> perfect_field r'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[perfect_field] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `ring_monomorphism(r:A ring,r':B ring) f` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_RING_HOMOMORPHISM_MONOMORPHISM;
                  RING_EPIMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FIELD_EPIMORPHIC_IMAGE]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_CHAR_MONOMORPHIC_IMAGE) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th]) ASSUME_TAC) THEN
  DISJ2_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [ring_epimorphism]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_POW; RING_EPIMORPHISM_IMP_HOMOMORPHISM]);;

let PERFECT_FIELD_ISOMORPHIC_IMAGE = prove
 (`!(r:A ring) (r':B ring) f.
        ring_isomorphism (r,r') f /\ perfect_field r ==> perfect_field r'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERFECT_FIELD_EPIMORPHIC_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`r:A ring`; `f:A->B`] THEN
  ASM_SIMP_TAC[RING_ISOMORPHISM_IMP_EPIMORPHISM] THEN
  ASM_MESON_TAC[ISOMORPHIC_RING_TRIVIALITY; isomorphic_ring;
                FIELD_IMP_NONTRIVIAL_RING; PERFECT_FIELD_IMP_FIELD]);;

let ISOMORPHIC_RING_PERFECT_FIELD = prove
 (`!(r:A ring) (r':B ring).
        r isomorphic_ring r' ==> (perfect_field r <=> perfect_field r')`,
  REWRITE_TAC[isomorphic_ring] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:B->A` o
    GEN_REWRITE_RULE I [ring_isomorphism]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [RING_ISOMORPHISMS_ISOMORPHISM]) THEN
  ASM_MESON_TAC[PERFECT_FIELD_ISOMORPHIC_IMAGE]);;

let FINITE_FIELD_IMP_PERFECT = prove
 (`!(k:A ring). field k /\ FINITE(ring_carrier k) ==> perfect_field k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `prime(ring_char(k:A ring))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_CHAR THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
  ASM_SIMP_TAC[PERFECT_FIELD_EQ_FROBENIUS_AUTOMORPHISM] THEN
  MATCH_MP_TAC RING_AUTOMORPHISM_FROBENIUS THEN ASM_REWRITE_TAC[]);;

let ALGEBRAICALLY_CLOSED_FIELD_IMP_PERFECT = prove
 (`!k:A ring. algebraically_closed_field k ==> perfect_field k`,
  GEN_TAC THEN REWRITE_TAC[algebraically_closed_field; perfect_field] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ring_char(k:A ring) = 0` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `poly_sub k (poly_pow k (poly_var k one) (ring_char k)) (poly_const k a)
    :(1->num)->A`) THEN
  REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
               RING_POLYNOMIAL_CONST; POLY_DEG_SUB_CONST; POLY_DEG_VAR_POW;
               FIELD_NONTRIVIAL; POLY_EVAL_SUB; POLY_EVAL_CONST] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[POLY_EVAL_POW; POLY_EVAL_VAR; RING_POLYNOMIAL_VAR; RING_POW;
               RING_SUB_EQ_0]);;

let PERFECT_FIELD_EQ_SEPARABLE_IRREDUCIBLES = prove
 (`!k:A ring.
        perfect_field k <=>
        field k /\
        !p. ring_irreducible (poly_ring k (:1)) p ==> poly_separable k p`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[PERFECT_FIELD_IMP_FIELD; PERFECT_FIELD_IMP_SEPARABLE];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[perfect_field] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP INTEGRAL_DOMAIN_CHAR o
    MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  ASM_SIMP_TAC[PRIME_IMP_NZ] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[algebraic_extension; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`l:(A#num)ring`; `h:A->A#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP RING_CHAR_MONOMORPHIC_IMAGE) THEN
  SUBGOAL_THEN
   `!w. w IN ring_carrier l
        ==> poly_extend (k,l) (h:A->A#num) (\v. w)
              (poly_sub k (poly_pow k (poly_var k one) (ring_char k))
                          (poly_const k a)) =
            ring_sub l (ring_pow l w (ring_char k)) (h a)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLY_EXTEND_SUB; POLY_EXTEND_VARPOW; POLY_EXTEND_CONST;
                 RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_CONST];
    ALL_TAC] THEN
  ABBREV_TAC
   `f = poly_sub k (poly_pow k (poly_var k one) (ring_char k))
                   (poly_const k a):(1->num)->A` THEN
  SUBGOAL_THEN
   `f IN ring_carrier(poly_ring k (:1)) /\
    poly_deg k (f:(1->num)->A) = ring_char k`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_CONST; POLY_DEG_SUB_CONST; POLY_DEG_VAR_POW;
                 FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `f:(1->num)->A`]
    NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN;
               PID_POLY_RING; PID_IMP_UFD] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONJUNCT2 POLY_RING_CLAUSES] THEN
    ASM_MESON_TAC[POLY_DEG_UNIT; POLY_DEG_0; FIELD_IMP_INTEGRAL_DOMAIN;
                  PRIME_IMP_NZ];
    DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IRREDUCIBLE_IN_CARRIER) THEN
  SUBGOAL_THEN
   `!w. w IN ring_carrier l /\ poly_eval l ((h:A->A#num) o q) w = ring_0 l
        ==> ring_pow l w (ring_char(k:A ring)) = h a`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:A#num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `l:(A#num)ring`;
                   `poly_extend (k,l) (h:A->A#num) (\v:1. w)`;
                   `q:(1->num)->A`; `f:(1->num)->A`]
      RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_EXTEND] THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval] THEN
    REWRITE_TAC[RING_DIVIDES_ZERO] THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
    MATCH_MP_TAC RING_SUB_EQ_0 THEN
    ASM_MESON_TAC[RING_POW; RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg k (q:(1->num)->A) = 1` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) /\ n <= 1 ==> n = 1`) THEN
    ASM_SIMP_TAC[IRREDUCIBLE_IMP_POLY_DEG_NZ] THEN
    MP_TAC(ISPECL [`l:(A#num)ring`; `(h:A->A#num) o (q:(1->num)->A)`]
      POLY_SQUAREFREE_ROOT_COUNT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POLY_SEPARABLE_IMP_SQUAREFREE THEN
      MATCH_MP_TAC POLY_SEPARABLE_MONOMORPHIC_IMAGE THEN
      EXISTS_TAC `k:A ring` THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `h:A->A#num`;
                     `q:(1->num)->A`] POLY_DEG_MONOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL] THEN DISCH_THEN SUBST1_TAC THEN
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC(MESON[CARD_LE_1]
     `(?a:A#num. s SUBSET {a}) ==> CARD s <= 1`) THEN
    MATCH_MP_TAC(SET_RULE
     `(!x y:A#num. x IN s /\ y IN s ==> x = y) ==> ?a. s SUBSET {a}`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`w1:A#num`; `w2:A#num`] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `l:(A#num)ring` RING_MONOMORPHISM_FROBENIUS) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:(A#num)ring`; `l:(A#num)ring`;
                   `\x:A#num. ring_pow l x (ring_char(k:A ring))`;
                   `w1:A#num`; `w2:A#num`] RING_MONOMORPHISM_INJECTIVE_EQ) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `q:(1->num)->A`] POLY_DEG_1_ROOT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `h:A->A#num`;
                 `ring_pow k (y:A) (ring_char k)`; `a:A`]
    RING_MONOMORPHISM_INJECTIVE_EQ) THEN
  ASM_SIMP_TAC[RING_POW] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:(A#num)ring`; `y:A`; `h:A->A#num`;
                 `q:(1->num)->A`] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_0]);;

let PERFECT_FIELD_EQ_IRREDUCIBLE_DERIV_NONZERO = prove
 (`!k:A ring.
        perfect_field k <=>
        field k /\
        !p. ring_irreducible (poly_ring k (:1)) p
            ==> ~(poly_deriv k p = poly_0 k)`,
  GEN_TAC THEN REWRITE_TAC[PERFECT_FIELD_EQ_SEPARABLE_IRREDUCIBLES] THEN
  ASM_CASES_TAC `field(k:A ring)` THEN
  ASM_SIMP_TAC[POLY_SEPARABLE_EQ_DERIV_NONZERO]);;

(* ------------------------------------------------------------------------- *)
(* Separable extensions: algebraic extensions in which every element is      *)
(* separable, i.e. its minimal polynomial is separable.                      *)
(* ------------------------------------------------------------------------- *)

let separable_element = new_definition
 `separable_element (k:A ring,l:B ring) (h:A->B) (x:B) <=>
        poly_separable k (minimal_polynomial (k,l) h x)`;;

let separable_extension = new_definition
 `separable_extension (k:A ring,l:B ring) (h:A->B) <=>
        algebraic_extension (k,l) h /\
        !x. x IN ring_carrier l ==> separable_element (k,l) h x`;;

let SEPARABLE_IMP_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l.
        separable_extension (k,l) h ==> algebraic_extension (k,l) h`,
  SIMP_TAC[separable_extension]);;

let SEPARABLE_IMP_FIELD_EXTENSION = prove
 (`!(h:A->B) k l. separable_extension (k,l) h ==> field_extension (k,l) h`,
  SIMP_TAC[separable_extension; ALGEBRAIC_IMP_FIELD_EXTENSION]);;

let SEPARABLE_ELEMENT_IMP_ALGEBRAIC = prove
 (`!(h:A->B) k l x.
        field k /\ separable_element (k,l) h x ==> algebraic_over (k,l) h x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[separable_element; minimal_polynomial] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[poly_separable; POLY_DERIV_0] THEN
  MP_TAC(ISPEC `poly_ring (k:A ring) (:1)` RING_COPRIME_00) THEN
  REWRITE_TAC[POLY_RING_CLAUSES; TRIVIAL_POLY_RING] THEN
  MESON_TAC[FIELD_IMP_NONTRIVIAL_RING]);;

let PERFECT_FIELD_IMP_SEPARABLE_ELEMENT = prove
 (`!(h:A->B) k l x.
        perfect_field k /\ field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> separable_element (k,l) h x`,
  SIMP_TAC[separable_element; PERFECT_FIELD_IMP_SEPARABLE;
           MINIMAL_POLYNOMIAL_IRREDUCIBLE]);;

let PERFECT_FIELD_IMP_SEPARABLE_EXTENSION = prove
 (`!(h:A->B) k l.
        perfect_field k /\ algebraic_extension (k,l) h
        ==> separable_extension (k,l) h`,
  SIMP_TAC[separable_extension; algebraic_extension;
           PERFECT_FIELD_IMP_SEPARABLE_ELEMENT]);;

let SEPARABLE_ELEMENT_CHAR0 = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ ring_char k = 0 /\ algebraic_over (k,l) h x
        ==> separable_element (k,l) h x`,
  MESON_TAC[PERFECT_FIELD_IMP_SEPARABLE_ELEMENT; PERFECT_FIELD_CHAR_0;
            field_extension]);;

let SEPARABLE_EXTENSION_CHAR0 = prove
 (`!(h:A->B) k l.
        algebraic_extension (k,l) h /\ ring_char k = 0
        ==> separable_extension (k,l) h`,
  MESON_TAC[PERFECT_FIELD_IMP_SEPARABLE_EXTENSION; PERFECT_FIELD_CHAR_0;
            ALGEBRAIC_IMP_FIELD_EXTENSION; field_extension]);;

let SEPARABLE_ELEMENT_IMAGE = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ x IN ring_carrier k
        ==> separable_element (k,l) h (h x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[separable_element] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `(h:A->B) x IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_CARRIER]; ALL_TAC] THEN
  MATCH_MP_TAC POLY_SEPARABLE_DIVISOR THEN
  EXISTS_TAC `poly_sub k (poly_var k one) (poly_const k (x:A))` THEN
  SUBGOAL_THEN
   `poly_sub k (poly_var k one) (poly_const k (x:A)) IN
    ring_carrier(poly_ring k (:1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM POLY_CLAUSES; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_CONST];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_SEPARABLE_X_MINUS_A; MINIMAL_POLYNOMIAL_IN_CARRIER;
               MINIMAL_POLYNOMIAL_DIVIDES; ALGEBRAIC_OVER_IMAGE] THEN
  ASM_SIMP_TAC[POLY_EXTEND_SUB; POLY_EXTEND_VAR; POLY_EXTEND_CONST;
               RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST; RING_SUB_REFL]);;

let SEPARABLE_EXTENSION_ISOMORPHISM = prove
 (`!(f:A->B) k l.
        (field k \/ field l) /\ ring_isomorphism (k,l) f
        ==> separable_extension (k,l) f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[separable_extension; ALGEBRAIC_EXTENSION_ISOMORPHISM] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [RING_ISOMORPHISM] o
    CONJUNCT2) THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SEPARABLE_ELEMENT_IMAGE THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_ISOMORPHISM]);;

let SEPARABLE_EXTENSION_REFL = prove
 (`!k:A ring. separable_extension (k,k) I <=> field k`,
  MESON_TAC[SEPARABLE_IMP_FIELD_EXTENSION; FIELD_EXTENSION_REFL;
            SEPARABLE_EXTENSION_ISOMORPHISM; RING_ISOMORPHISM_I]);;

let SEPARABLE_EXTENSION_SUBFIELD = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g /\
        separable_extension (k,m) (g o f)
        ==> separable_extension (k,l) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    ALGEBRAIC_EXTENSION_TRANS_EQ) THEN
  ASM_REWRITE_TAC[separable_extension; separable_element] THEN
  DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g:B->C) x`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_CARRIER];
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_MONOMORPHIC_IMAGE;
                 FIELD_EXTENSION_IMP_HOMOMORPHISM;
                 FIELD_EXTENSION_IMP_MONOMORPHISM]]);;

let SEPARABLE_ELEMENT_INTERMEDIATE = prove
 (`!(f:A->B) (g:B->C) k l m x.
        field_extension (k,l) f /\ field_extension (l,m) g /\
        separable_element (k,m) (g o f) x
        ==> separable_element (l,m) g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `field k /\ field l /\ ring_homomorphism (k,l) (f:A->B) /\
    field_extension (k,m) ((g:B->C) o f)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[field_extension; FIELD_EXTENSION_IMP_HOMOMORPHISM;
                  FIELD_EXTENSION_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `algebraic_over (k,m) ((g:B->C) o (f:A->B)) x /\ algebraic_over (l,m) g x`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SEPARABLE_ELEMENT_IMP_ALGEBRAIC;
                  ALGEBRAIC_OVER_FIELD_EXTENSION];
    ALL_TAC] THEN
  UNDISCH_TAC `separable_element (k,m) ((g:B->C) o (f:A->B)) x` THEN
  REWRITE_TAC[separable_element] THEN
  ABBREV_TAC `p = minimal_polynomial (k,m) ((g:B->C) o (f:A->B)) x` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`; `x:C`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC POLY_SEPARABLE_DIVISOR THEN
  EXISTS_TAC `(f:A->B) o (p:(1->num)->A)` THEN
  SUBGOAL_THEN `(f:A->B) o (p:(1->num)->A) IN ring_carrier(poly_ring l (:1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER; MINIMAL_POLYNOMIAL_DIVIDES] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC
     `poly_extend (k,m) ((g:B->C) o (f:A->B)) (\v:1. x) p = ring_0 m` THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; FIELD_EXTENSION_IMP_HOMOMORPHISM;
                 o_ASSOC];
    MATCH_MP_TAC POLY_SEPARABLE_MONOMORPHIC_IMAGE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[]]);;

let SEPARABLE_EXTENSION_INTERMEDIATE = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g /\
        separable_extension (k,m) (g o f)
        ==> separable_extension (l,m) g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    ALGEBRAIC_EXTENSION_TRANS_EQ) THEN
  ASM_REWRITE_TAC[separable_extension] THEN
  DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SEPARABLE_ELEMENT_INTERMEDIATE]);;

(* ------------------------------------------------------------------------- *)
(* A nonzero polynomial is separable iff its image has as many distinct      *)
(* roots as its degree, in an algebraically closed field or in any field     *)
(* where it splits; an inseparable one has fewer roots in every field.       *)
(* ------------------------------------------------------------------------- *)

let POLY_SEPARABLE_ROOT_COUNT_EQ = prove
 (`!(h:A->B) k l p.
        field_extension (k,l) h /\ algebraically_closed_field l
        ==> (poly_separable k p <=>
             p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k) /\
             CARD {x | x IN ring_carrier l /\
                       poly_eval l (h o p) x = ring_0 l} =
             poly_deg k p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_CASES_TAC `(p:(1->num)->A) IN ring_carrier(poly_ring k (:1))` THENL
   [ALL_TAC; ASM_MESON_TAC[poly_separable; ring_coprime]] THEN
  TRANS_TAC EQ_TRANS `poly_separable l ((h:A->B) o p)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[POLY_SEPARABLE_MONOMORPHIC_IMAGE;
                  POLY_SEPARABLE_FROM_MONOMORPHIC_IMAGE];
    ASM_SIMP_TAC[PERFECT_FIELD_SEPARABLE_EQ_SQUAREFREE;
                 ALGEBRAICALLY_CLOSED_FIELD_IMP_PERFECT;
                 POLY_SQUAREFREE_ROOT_COUNT_EQ]] THEN
  SUBGOAL_THEN
   `(h:A->B) o (p:(1->num)->A) IN ring_carrier(poly_ring l (:1)) /\
    (h o p = poly_0 l <=> p = poly_0 k) /\ poly_deg l (h o p) = poly_deg k p`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_RING_POLYNOMIAL_CARRIER_COMPOSE; RING_POLYNOMIAL;
                  POLY_EQ_0_MONOMORPHIC_IMAGE; POLY_DEG_MONOMORPHIC_IMAGE];
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2 POLY_RING_CLAUSES)]]);;

let POLY_INSEPARABLE_ROOTS_LT_DEG = prove
 (`!(h:A->B) k l p.
        field_extension (k,l) h /\ p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = poly_0 k) /\ ~poly_separable k p
        ==> CARD {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l}
            < poly_deg k p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:(B#num)ring`; `j:B->B#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `field_extension(k,m) ((j:B->B#num) o (h:A->B))`
  ASSUME_TAC THENL [ASM_MESON_TAC[FIELD_EXTENSION_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(j:B->B#num) o (h:A->B)`; `k:A ring`; `m:(B#num)ring`;
                 `p:(1->num)->A`] POLY_SEPARABLE_ROOT_COUNT_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_polynomial k (p:(1->num)->A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [field_extension] o
    check (fun t -> rand(concl t) = th)))
   [`h:A->B`; `j:B->B#num`; `(j:B->B#num) o (h:A->B)`] THEN
  MP_TAC(ISPECL [`k:A ring`; `m:(B#num)ring`; `(j:B->B#num) o (h:A->B)`;
                 `p:(1->num)->A`] POLY_EQ_0_MONOMORPHIC_IMAGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `m:(B#num)ring`; `(j:B->B#num) o (h:A->B)`;
                 `p:(1->num)->A`] POLY_DEG_MONOMORPHIC_IMAGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:(1->num)->A`]
    POLY_EQ_0_MONOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(h:A->B) o (p:(1->num)->A) IN ring_carrier(poly_ring l (:1)) /\
    ((j:B->B#num) o (h:A->B)) o p IN ring_carrier(poly_ring m (:1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(B#num)ring`;
                 `((j:B->B#num) o (h:A->B)) o (p:(1->num)->A)`]
    POLY_ROOT_BOUND) THEN
  MP_TAC(ISPECL [`l:B ring`; `(h:A->B) o (p:(1->num)->A)`] POLY_ROOT_BOUND) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN;
               CONJUNCT1(CONJUNCT2 POLY_RING_CLAUSES)] THEN
  REPEAT STRIP_TAC THEN TRANS_TAC LET_TRANS
   `CARD {x | x IN ring_carrier m /\
             poly_eval m (((j:B->B#num) o (h:A->B)) o (p:(1->num)->A)) x =
             ring_0 m}` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  TRANS_TAC LE_TRANS
   `CARD(IMAGE (j:B->B#num) {x | x IN ring_carrier l /\
                             poly_eval l ((h:A->B) o (p:(1->num)->A)) x =
                             ring_0 l})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [ring_monomorphism] o
      check (fun th -> rand(concl th) = `j:B->B#num`)) THEN
    MESON_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
      check (fun th -> rand(concl th) = `j:B->B#num`)) THEN
    MP_TAC(ISPECL [`l:B ring`; `m:(B#num)ring`; `x:B`; `j:B->B#num`;
                   `(h:A->B) o (p:(1->num)->A)`]
      POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[GSYM o_ASSOC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC `l:B ring`;
      MATCH_MP_TAC RING_HOMOMORPHISM_0] THEN
    ASM_REWRITE_TAC[]]);;

let POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT_EQ = prove
 (`!(h:A->B) k l p.
        field_extension (k,l) h /\ p IN ring_carrier(poly_ring k (:1)) /\
        ~(p = poly_0 k) /\ poly_splits_over (k,l) h p
        ==> (poly_separable k p <=>
             CARD {x | x IN ring_carrier l /\
                       poly_eval l (h o p) x = ring_0 l} =
             poly_deg k p)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT];
    ASM_MESON_TAC[POLY_INSEPARABLE_ROOTS_LT_DEG; LT_REFL]]);;

let POLY_SPLITS_OVER_DISTINCT_ROOTS = prove
 (`!(h:A->B) k l p s.
        field_extension(k,l) h /\
        p IN ring_carrier(poly_ring k (:1)) /\ ~(p = poly_0 k) /\
        s HAS_SIZE poly_deg k p /\
        (!x. x IN s
             ==> x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l)
        ==> {x | x IN ring_carrier l /\ poly_eval l (h o p) x = ring_0 l} = s /\
            poly_splits_over(k,l) h p /\ poly_separable k p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
    POLY_ROOT_BOUND_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `R = {x | x IN ring_carrier l /\
             poly_eval l ((h:A->B) o (p:(1->num)->A)) x = ring_0 l}` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [HAS_SIZE]) THEN
  SUBGOAL_THEN `(s:B->bool) SUBSET R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `R:B->bool = s` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:B->bool`; `R:B->bool`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  SUBGOAL_THEN `ring_polynomial k (p:(1->num)->A)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[poly_splits_over] THEN
    MATCH_MP_TAC POLY_ROOT_COUNT_IMP_SPLITS THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:(1->num)->A`]
      POLY_EQ_0_MONOMORPHIC_IMAGE) THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:(1->num)->A`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`]
      POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT_EQ) THEN
    ASM_REWRITE_TAC[]]);;

(* At a root of a separable polynomial its derivative does not vanish        *)
(* (POLY_SEPARABLE_ROOT_DERIV): evaluate a Bezout relation u p + v p' = 1    *)
(* there.                                                                    *)
let POLY_SEPARABLE_ROOT_DERIV = prove
 (`!(h:A->B) k l p x.
        field_extension(k,l) h /\ p IN ring_carrier(poly_ring k (:1)) /\
        poly_separable k p /\ x IN ring_carrier l /\
        poly_eval l (h o p) x = ring_0 l
        ==> ~(poly_eval l (h o poly_deriv k p) x = ring_0 l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `field(k:A ring) /\ field(l:B ring)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `p:(1->num)->A`;
                 `poly_deriv k (p:(1->num)->A)`] BEZOUT_RING_COPRIME) THEN
  ASM_SIMP_TAC[PID_IMP_BEZOUT_RING; PID_POLY_RING] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[poly_separable]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(1->num)->A` (X_CHOOSE_THEN `v:(1->num)->A`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `(:1)`; `h:A->B`; `\v:1. (x:B)`]
    RING_HOMOMORPHISM_POLY_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!q. poly_extend (k,l) (h:A->B) (\v:1. x) q = poly_eval l (h o q) x`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; poly_eval]; ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC
   `ring_add (poly_ring k (:1))
      (ring_mul (poly_ring k (:1)) p (u:(1->num)->A))
      (ring_mul (poly_ring k (:1)) (poly_deriv k p) v) =
    ring_1 (poly_ring k (:1))` THEN
  DISCH_THEN(MP_TAC o AP_TERM `poly_extend (k,l) (h:A->B) (\v:1. x)`) THEN
  FIRST_ASSUM((fun th -> ASM_SIMP_TAC[RING_ADD; RING_MUL;
    POLY_DERIV_IN_CARRIER; MATCH_MP RING_HOMOMORPHISM_ADD th;
    MATCH_MP RING_HOMOMORPHISM_MUL th; MATCH_MP RING_HOMOMORPHISM_1 th]) o
    check (fun th -> rator(concl th) =
     `ring_homomorphism (poly_ring (k:A ring) (:1),l:B ring)`)) THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_ADD_LZERO; POLY_EVAL; RING_0] THEN
  MP_TAC(ASSUME `field(l:B ring)`) THEN REWRITE_TAC[field] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Linear independence of ring homomorphisms (Dedekind and Artin): distinct  *)
(* homomorphisms into an integral domain are linearly independent over it.   *)
(* ------------------------------------------------------------------------- *)

let RING_HOMOMORPHISMS_INDEPENDENT =
  let lemma = prove
   (`!(f:K->A->B) k l s d a y.
        FINITE s /\ (!i. i IN s ==> ring_homomorphism(k,l) (f i)) /\
        (!i. i IN s ==> d i IN ring_carrier l) /\
        a IN s /\ y IN ring_carrier k /\
        (!x. x IN ring_carrier k
             ==> ring_sum l s (\i. ring_mul l (d i) (f i x)) = ring_0 l)
        ==> !x. x IN ring_carrier k
                ==> ring_sum l s
                     (\i. ring_mul l
                           (ring_mul l (d i) (ring_sub l (f i y) (f a y)))
                           (f i x)) = ring_0 l`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!i x. i IN s /\ x IN ring_carrier k
            ==> (f:K->A->B) i x IN ring_carrier l /\
                ring_mul l (d i) (f i x) IN ring_carrier l`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_mul k (y:A) x IN ring_carrier k` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum l s
        (\i. ring_sub l (ring_mul l (d i) ((f:K->A->B) i (ring_mul k y x)))
                        (ring_mul l (f a y) (ring_mul l (d i) (f i x))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `ring_homomorphism(k,l) ((f:K->A->B) i)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
      MATCH_MP_TAC(RING_RULE
       `!r c u v w:B.
          c IN ring_carrier r /\ u IN ring_carrier r /\
          v IN ring_carrier r /\ w IN ring_carrier r
          ==> ring_mul r (ring_mul r c (ring_sub r u v)) w =
              ring_sub r (ring_mul r c (ring_mul r u w))
                         (ring_mul r v (ring_mul r c w))`) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[RING_SUM_SUB; RING_SUM_LMUL; RING_MUL; RING_MUL_RZERO;
                   RING_SUB_REFL; RING_0]]) in
  prove
   (`!(f:K->A->B) k l s c.
        integral_domain l /\ FINITE s /\
        (!i. i IN s ==> ring_homomorphism(k,l) (f i)) /\
        (!i j. i IN s /\ j IN s /\ ~(i = j)
               ==> ?x. x IN ring_carrier k /\ ~(f i x = f j x)) /\
        (!i. i IN s ==> c i IN ring_carrier l) /\
        (!x. x IN ring_carrier k
             ==> ring_sum l s (\i. ring_mul l (c i) (f i x)) = ring_0 l)
        ==> !i. i IN s ==> c i = ring_0 l`,
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!t. FINITE t
          ==> t SUBSET (s:K->bool)
              ==> !d. (!i. i IN t ==> d i IN ring_carrier l) /\
                      (!x. x IN ring_carrier k
                           ==> ring_sum l t
                                 (\i. ring_mul l (d i) ((f:K->A->B) i x)) =
                               ring_0 l)
                      ==> !i. i IN t ==> d i = ring_0 l`
     (fun th -> MP_TAC(SPEC `s:K->bool` th) THEN
                ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
                ASM_REWRITE_TAC[]) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[NOT_IN_EMPTY; INSERT_SUBSET] THEN
    MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN(fun ih -> STRIP_TAC THEN X_GEN_TAC `d:K->B` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sum")) THEN
      MP_TAC(MP ih (ASSUME `(t:K->bool) SUBSET s`))) THEN
    SUBGOAL_THEN
     `!i. i IN a INSERT t ==> ring_homomorphism(k,l) ((f:K->A->B) i)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!i x. i IN a INSERT t /\ x IN ring_carrier k
            ==> (f:K->A->B) i x IN ring_carrier l`
    ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    DISCH_THEN(fun ih ->
      SUBGOAL_THEN `!i. i IN t ==> (d:K->B) i = ring_0 l` ASSUME_TAC THENL
       [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`i:K`; `a:K`]) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
        MP_TAC(SPEC
         `\j. ring_mul l (d j) (ring_sub l ((f:K->A->B) j y) (f a y))` ih) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[RING_MUL; RING_SUB; IN_INSERT] THEN
          X_GEN_TAC `x:A` THEN DISCH_TAC THEN
          MP_TAC(ISPECL [`f:K->A->B`; `k:A ring`; `l:B ring`;
                         `(a:K) INSERT t`; `d:K->B`; `a:K`; `y:A`] lemma) THEN
          ASM_SIMP_TAC[FINITE_INSERT; IN_INSERT] THEN
          DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
          ASM_SIMP_TAC[RING_SUM_CLAUSES; RING_MUL; RING_SUB; RING_0; IN_INSERT;
                       RING_SUB_REFL; RING_MUL_LZERO; RING_MUL_RZERO;
                       RING_ADD_LZERO; RING_SUM];
          DISCH_THEN(MP_TAC o SPEC `i:K`) THEN
          ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; RING_SUB; RING_SUB_EQ_0;
                       IN_INSERT]];
        ALL_TAC]) THEN
    ASM_REWRITE_TAC[FORALL_IN_INSERT] THEN
    SUBGOAL_THEN
     `ring_sum l t (\i. ring_mul l (d i) ((f:K->A->B) i (ring_1 k))) =
      ring_0 l`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ_0 THEN
      ASM_SIMP_TAC[RING_MUL_LZERO; RING_1; IN_INSERT];
      ALL_TAC] THEN
    REMOVE_THEN "sum" (MP_TAC o SPEC `ring_1 k:A`) THEN
    SUBGOAL_THEN `ring_homomorphism(k,l) ((f:K->A->B) a)` MP_TAC THENL
     [ASM_SIMP_TAC[IN_INSERT]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASM_SIMP_TAC[RING_SUM_CLAUSES; RING_MUL; RING_1;
      IN_INSERT; RING_MUL_LZERO; RING_SUM_0; RING_ADD_RZERO; RING_MUL_RID;
      MATCH_MP RING_HOMOMORPHISM_1 th]));;

let RING_HOMOMORPHISMS_INDEPENDENT_SET = prove
 (`!k:A ring l:B ring s c.
        integral_domain l /\ FINITE s /\
        (!f. f IN s ==> ring_homomorphism(k,l) f) /\
        (!f g. f IN s /\ g IN s /\ ~(f = g)
               ==> ?x. x IN ring_carrier k /\ ~(f x = g x)) /\
        (!f. f IN s ==> c f IN ring_carrier l) /\
        (!x. x IN ring_carrier k
             ==> ring_sum l s (\f. ring_mul l (c f) (f x)) = ring_0 l)
        ==> !f. f IN s ==> c f = ring_0 l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\f:A->B. f`; `k:A ring`; `l:B ring`; `s:(A->B)->bool`;
                 `c:(A->B)->B`] RING_HOMOMORPHISMS_INDEPENDENT) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The extensions of a homomorphism g from k to a ring m along h from k to   *)
(* l, as homomorphisms from l to m, normalized to be EXTENSIONAL so that     *)
(* they form a set of the right size. For a finite extension there are at    *)
(* most [l:k] of them into an integral domain, and exactly [l:k] when l is   *)
(* separable and m is algebraically closed; for an algebraic extension and   *)
(* algebraically closed m their number depends neither on m nor on g.        *)
(* ------------------------------------------------------------------------- *)

let ring_homomorphism_extensions = new_definition
 `ring_homomorphism_extensions (k:A ring,l:B ring,m:C ring) (h:A->B,g:A->C) =
        {f | f IN EXTENSIONAL (ring_carrier l) /\
             ring_homomorphism (l,m) f /\
             !x. x IN ring_carrier k ==> f(h x) = g x}`;;

let RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS = prove
 (`!(h:A->B) (g:A->C) f k l m.
        ring_homomorphism (k,l) h /\ ring_homomorphism (l,m) f /\
        (!x. x IN ring_carrier k ==> f(h x) = g x)
        ==> RESTRICTION (ring_carrier l) f IN
            ring_homomorphism_extensions (k,l,m) (h,g)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM;
              RESTRICTION_IN_EXTENSIONAL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN EXISTS_TAC `f:B->C` THEN
    ASM_SIMP_TAC[RESTRICTION];
    ASM_MESON_TAC[RESTRICTION; RING_HOMOMORPHISM_IN_CARRIER]]);;

let RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY = prove
 (`!(h:A->B) (g:A->C) k l m.
        algebraic_extension (k,l) h /\ algebraically_closed_field m /\
        ring_homomorphism (k,m) g
        ==> ~(ring_homomorphism_extensions (k,l,m) (h,g) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:C ring`; `h:A->B`; `g:A->C`]
    ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:B->C` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `RESTRICTION (ring_carrier l) (f:B->C)` THEN
  MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
  ASM_MESON_TAC[ALGEBRAIC_IMP_FIELD_EXTENSION;
                FIELD_EXTENSION_IMP_HOMOMORPHISM]);;

let RING_HOMOMORPHISM_EXTENSIONS_ROOT = prove
 (`!(h:A->B) (g:A->C) f k l m x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x /\
        f IN ring_homomorphism_extensions (k,l,m) (h,g)
        ==> poly_eval m (g o minimal_polynomial (k,l) h x) (f x) = ring_0 m`,
  REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `f:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `x:B`] MINIMAL_POLYNOMIAL_VANISHES_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `i:1->num` THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC POLY_MONOMIAL_IN_CARRIER THEN
  EXISTS_TAC `(:1)` THEN ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER]);;

let RING_HOMOMORPHISM_EXTENSIONS_SIMPLE = prove
 (`!(h:A->B) (g:A->C) k l m a.
        field_extension (k,l) h /\ algebraic_over (k,l) h a /\
        ring_homomorphism (k,m) g
        ==> ring_homomorphism_extensions
             (k,subring_generated l (a INSERT IMAGE h (ring_carrier k)),m)
             (h,g) =_c
            {b | b IN ring_carrier m /\
                 poly_eval m (g o minimal_polynomial (k,l) h a) b = ring_0 m}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [algebraic_over]) THEN
  SUBGOAL_THEN
   `IMAGE (h:A->B) (ring_carrier k) SUBSET a INSERT IMAGE h (ring_carrier k)`
  ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `K = subring_generated l ((a:B) INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  SUBGOAL_THEN
   `field_extension (k,K) (h:A->B) /\ a IN ring_carrier K /\
    algebraic_over (k,K) h a /\
    minimal_polynomial (k,K) h a = minimal_polynomial (k,l) h a`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    ASM_SIMP_TAC[FINITE_SIMPLE_ALGEBRAIC_EXTENSION; FINITE_IMP_FIELD_EXTENSION;
                 ALGEBRAIC_OVER_SUBRING_GENERATED; SUBRING_GENERATED_INC_GEN;
                 MINIMAL_POLYNOMIAL_SUBRING_GENERATED; IN_INSERT;
                 FIELD_EXTENSION_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  REWRITE_TAC[eq_c] THEN EXISTS_TAC `\f:B->C. f a` THEN CONJ_TAC THENL
   [X_GEN_TAC `f:B->C` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o
        REWRITE_RULE[ring_homomorphism_extensions; IN_ELIM_THM]) THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        lhand(concl th) = `minimal_polynomial (k,K) (h:A->B) a`)) THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_EXTENSIONS_ROOT THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `b:C` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM; ring_homomorphism_extensions;
                IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:C ring`; `h:A->B`; `g:A->C`;
                     `a:B`; `b:C`]
        SIMPLE_ALGEBRAIC_EXTEND_HOMOMORPHISM_ROOT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:B->C` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `RESTRICTION (ring_carrier K) (f:B->C)` THEN
      MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `f:B->C`; `k:A ring`; `K:B ring`;
                     `m:C ring`]
        RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS) THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
      REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[RESTRICTION];
      MAP_EVERY X_GEN_TAC [`f1:B->C`; `f2:B->C`] THEN STRIP_TAC THEN
      MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier K:B->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`f1:B->C`; `f2:B->C`; `K:B ring`; `m:C ring`;
                     `(a:B) INSERT IMAGE (h:A->B) (ring_carrier k)`]
        RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED) THEN
      EXPAND_TAC "K" THEN
      REWRITE_TAC[MATCH_MP SUBRING_GENERATED_IDEMPOT (ISPEC
       `(a:B) INSERT IMAGE (h:A->B) (ring_carrier k)` SUBSET_REFL)] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE; IN_INSERT; IN_IMAGE] THEN
      ASM_MESON_TAC[]]]);;

let FINITE_EXTENSION_NORMAL_CLOSURE = prove
 (`!(h:A->B) (j:B->C) k l m.
     finite_extension(k,l) h /\
     algebraically_closed_field m /\ ring_homomorphism(l,m) j
     ==> ?s. FINITE s /\
             (!x. x IN s
                  ==> ?e. ring_homomorphism(l,m) e /\
                          (!y. y IN ring_carrier k ==> e(h y) = j(h y)) /\
                          x IN IMAGE e (ring_carrier l)) /\
             (!e. ring_homomorphism(l,m) e /\
                  (!y. y IN ring_carrier k ==> e(h y) = j(h y))
                  ==> IMAGE e (ring_carrier l) SUBSET
                      ring_carrier(subfield_generated m
                        (IMAGE (j o h) (ring_carrier k) UNION s))) /\
             finite_extension
              (k,subfield_generated m (IMAGE (j o h) (ring_carrier k) UNION s))
              (j o h) /\
             normal_extension
              (k,subfield_generated m (IMAGE (j o h) (ring_carrier k) UNION s))
              (j o h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    check (fun th -> concl th = `field_extension(k:A ring,l:B ring) h`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `ring_homomorphism(k:A ring,m:C ring) ((j:B->C) o (h:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `field_extension(k:A ring,m:C ring) ((j:B->C) o (h:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_TRANS THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[field_extension] THEN
    MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_IMP_FINITELY_GENERATED_EXTENSION) THEN
  REWRITE_TAC[finitely_generated_extension] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l"))) o CONJUNCT2) THEN
  SUBGOAL_THEN `!x. x IN b ==> algebraic_over(k,l) (h:A->B) x`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_product (poly_ring k (:1)) b (minimal_polynomial(k,l) (h:A->B))
    IN ring_carrier(poly_ring k (:1)) /\
    ~(ring_product (poly_ring k (:1)) b (minimal_polynomial(k,l) (h:A->B)) =
      poly_0 k)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RING_PRODUCT] THEN MATCH_MP_TAC MONIC_IMP_NONZERO THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING; RING_POLYNOMIAL; RING_PRODUCT] THEN
    MATCH_MP_TAC MONIC_POLY_PRODUCT THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_MONIC; RING_POLYNOMIAL;
                 MINIMAL_POLYNOMIAL_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ring_carrier m
        ==> (poly_eval m (((j:B->C) o (h:A->B)) o
               ring_product (poly_ring k (:1)) b (minimal_polynomial(k,l) h))
               x = ring_0 m <=>
             ?y. y IN b /\
                 poly_eval m ((j o h) o minimal_polynomial(k,l) h y) x =
                 ring_0 m)`
  (LABEL_TAC "roots") THENL
   [REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_RING_PRODUCT_EQ_0 o
      lhand o snd) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; MINIMAL_POLYNOMIAL_IN_CARRIER];
    ALL_TAC] THEN
  ABBREV_TAC
   `P = ring_product (poly_ring k (:1)) b
          (minimal_polynomial(k,l) (h:A->B))` THEN
  EXISTS_TAC
   `{x | x IN ring_carrier m /\
         poly_eval m (((j:B->C) o (h:A->B)) o P) x = ring_0 m}` THEN
  SUBGOAL_THEN `poly_splits_over (k,m) ((j:B->C) o (h:A->B)) P`
  ASSUME_TAC THENL
   [REWRITE_TAC[poly_splits_over] THEN
    MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(j:B->C) o (h:A->B)`; `k:A ring`; `m:C ring`;
                   `P:(1->num)->A`] POLY_ROOT_BOUND_EXTENSION) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:C` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    USE_THEN "roots" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(r:C) IN ring_carrier m`)]) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:C ring`; `h:A->B`;
                   `(j:B->C) o (h:A->B)`; `y:B`; `r:C`]
      ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM_ROOT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[o_THM]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:B->C` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC;
    MATCH_MP_TAC SPLITTING_IMP_FINITE_EXTENSION THEN
    EXISTS_TAC `P:(1->num)->A` THEN
    MATCH_MP_TAC SPLITTING_EXTENSION_GENERATED_BY_ROOTS THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC NORMAL_EXTENSION_GENERATED_BY_ROOTS THEN
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `e:B->C` THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_monomorphism(l:B ring,m:C ring) e` ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  USE_THEN "l" (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `e:B->C`;
                 `IMAGE (h:A->B) (ring_carrier k) UNION b`]
    SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; UNION_SUBSET] THEN
    ASM_MESON_TAC[FIELD_EXTENSION_IMP_SUBSET];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN
  REWRITE_TAC[IMAGE_UNION; UNION_SUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN DISJ1_TAC THEN
    ASM_SIMP_TAC[] THEN
    SUBST1_TAC(SYM(ISPECL [`j:B->C`; `h:A->B`; `x:A`] o_THM)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  MATCH_MP_TAC(SET_RULE `(x:C) IN t ==> x IN s UNION t`) THEN
  SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:B->C) y IN ring_carrier m` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "roots" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(e:B->C) y IN ring_carrier m`)]) THEN
  EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `(j:B->C) o (h:A->B)`;
                 `RESTRICTION (ring_carrier l) (e:B->C)`;
                 `k:A ring`; `l:B ring`; `m:C ring`; `y:B`]
    RING_HOMOMORPHISM_EXTENSIONS_ROOT) THEN
  ASM_SIMP_TAC[RESTRICTION] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
  ASM_SIMP_TAC[o_THM]);;

let RING_HOMOMORPHISM_EXTENSIONS_TOWER = prove
 (`!(f:A->B) (g:B->C) (j:A->D) k l m n.
        ring_homomorphism (k,l) f /\ ring_homomorphism (l,m) g
        ==> ring_homomorphism_extensions (k,m,n) (g o f,j) =
            UNIONS {ring_homomorphism_extensions (l,m,n) (g,t) | t |
                    t IN ring_homomorphism_extensions (k,l,n) (f,j)} /\
            pairwise (\t t'. DISJOINT
                               (ring_homomorphism_extensions (l,m,n) (g,t))
                               (ring_homomorphism_extensions (l,m,n) (g,t')))
                     (ring_homomorphism_extensions (k,l,n) (f,j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pairwise; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
              UNIONS_GSPEC; ring_homomorphism_extensions; IN_ELIM_THM;
              o_THM] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:C->D` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      EXISTS_TAC `RESTRICTION (ring_carrier l) ((s:C->D) o (g:B->C))` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[RESTRICTION; o_THM]] THEN
      MP_TAC(ISPECL [`f:A->B`; `j:A->D`; `(s:C->D) o (g:B->C)`;
                     `k:A ring`; `l:B ring`; `n:D ring`]
        RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS) THEN
      REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM; o_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE];
      DISCH_THEN(X_CHOOSE_THEN `t:B->D` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f:A->B) x IN ring_carrier l` ASSUME_TAC THENL
       [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
        EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]]];
    MAP_EVERY X_GEN_TAC [`t:B->D`; `t':B->D`] THEN STRIP_TAC THEN
    X_GEN_TAC `s:C->D` THEN STRIP_TAC THEN
    UNDISCH_TAC `~(t:B->D = t')` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
    ASM_MESON_TAC[]]);;

let CARD_RING_HOMOMORPHISM_EXTENSIONS_LE,
    HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS =
  let lemma = prove
   (`!(h:A->B) (g:A->C) k l m a.
        field_extension (k,l) h /\ algebraic_over (k,l) h a /\
        integral_domain m /\ ring_homomorphism (k,m) g
        ==> FINITE(ring_homomorphism_extensions
                    (k,subring_generated l (a INSERT IMAGE h (ring_carrier k)),
                     m) (h,g)) /\
            CARD(ring_homomorphism_extensions
                  (k,subring_generated l (a INSERT IMAGE h (ring_carrier k)),
                   m) (h,g)) <=
            extension_degree
             (k,subring_generated l (a INSERT IMAGE h (ring_carrier k))) h /\
            (separable_element (k,l) h a /\ algebraically_closed_field m
             ==> CARD(ring_homomorphism_extensions
                       (k,subring_generated l
                            (a INSERT IMAGE h (ring_carrier k)),m) (h,g)) =
                 extension_degree
                  (k,subring_generated l (a INSERT IMAGE h (ring_carrier k)))
                  h)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                   `a:B`] RING_HOMOMORPHISM_EXTENSIONS_SIMPLE) THEN
    ASM_SIMP_TAC[EXTENSION_DEGREE_SIMPLE] THEN
    ABBREV_TAC `p = minimal_polynomial (k,l) (h:A->B) a` THEN
    ABBREV_TAC `R = {b | b IN ring_carrier m /\
                         poly_eval m ((g:A->C) o (p:(1->num)->A)) b =
                         ring_0 m}` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
      MINIMAL_POLYNOMIAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ring_monomorphism(k:A ring,m:C ring) g` ASSUME_TAC THENL
     [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING] THEN
      ASM_MESON_TAC[field_extension];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(g:A->C) o (p:(1->num)->A) IN ring_carrier(poly_ring m (:1)) /\
      ~(g o p = poly_0 m) /\ poly_deg m (g o p) = poly_deg k p`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
        EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE; RING_POLYNOMIAL];
        ASM_MESON_TAC[POLY_DEG_MONOMORPHIC_IMAGE; RING_POLYNOMIAL]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m:C ring`; `(g:A->C) o (p:(1->num)->A)`]
      POLY_ROOT_BOUND) THEN
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2 POLY_RING_CLAUSES)] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CARD_EQ_CARD_IMP o
      CONJ (ASSUME `FINITE(R:C->bool)`)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CARD_FINITE_CONG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "R" THEN
    MATCH_MP_TAC POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT THEN
    ASM_SIMP_TAC[field_extension; ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[separable_element]] THEN
    REWRITE_TAC[poly_splits_over] THEN
    MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
    ASM_REWRITE_TAC[]) in
  (CONJ_PAIR o prove)
   (`(!(h:A->B) (g:A->C) k l m.
          finite_extension (k,l) h /\ integral_domain m /\
          ring_homomorphism (k,m) g
          ==> FINITE(ring_homomorphism_extensions (k,l,m) (h,g)) /\
              CARD(ring_homomorphism_extensions (k,l,m) (h,g)) <=
              extension_degree (k,l) h) /\
     (!(h:A->B) (g:A->C) k l m.
          finite_extension (k,l) h /\ separable_extension (k,l) h /\
          algebraically_closed_field m /\ ring_homomorphism (k,m) g
          ==> ring_homomorphism_extensions (k,l,m) (h,g) HAS_SIZE
              extension_degree (k,l) h)`,
    SUBGOAL_THEN
     `!(h:A->B) (g:A->C) k l m.
          finite_extension (k,l) h /\ integral_domain m /\
          ring_homomorphism (k,m) g
          ==> FINITE(ring_homomorphism_extensions (k,l,m) (h,g)) /\
              CARD(ring_homomorphism_extensions (k,l,m) (h,g)) <=
              extension_degree (k,l) h /\
              (separable_extension (k,l) h /\ algebraically_closed_field m
               ==> CARD(ring_homomorphism_extensions (k,l,m) (h,g)) =
                   extension_degree (k,l) h)`
     (fun th -> CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
                MP_TAC(SPEC_ALL th) THEN
                ASM_SIMP_TAC[HAS_SIZE; FIELD_IMP_INTEGRAL_DOMAIN;
                             ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD]) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    SUBGOAL_THEN
     `!s. FINITE s
          ==> s SUBSET ring_carrier l
              ==> FINITE(ring_homomorphism_extensions
                   (k,subring_generated l (IMAGE (h:A->B) (ring_carrier k)
                                           UNION s),m) (h,g:A->C)) /\
                  CARD(ring_homomorphism_extensions
                   (k,subring_generated l (IMAGE h (ring_carrier k) UNION s),
                    m) (h,g)) <=
                  extension_degree
                   (k,subring_generated l (IMAGE h (ring_carrier k) UNION s))
                   h /\
                  (separable_extension (k,l) h /\ algebraically_closed_field m
                   ==> CARD(ring_homomorphism_extensions
                        (k,subring_generated l
                             (IMAGE h (ring_carrier k) UNION s),m) (h,g)) =
                       extension_degree
                        (k,subring_generated l
                             (IMAGE h (ring_carrier k) UNION s)) h)`
    MP_TAC THENL
     [ALL_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_EXTENSION] o check
       (fun th -> concl th = `finite_extension(k:A ring,l:B ring) h`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o SPEC `b:B->bool`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `subring_generated l (IMAGE (h:A->B) (ring_carrier k) UNION b) = l`
       (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[RINGS_EQ; CONJUNCT2 SUBRING_GENERATED] THEN
      REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ;
                  RING_CARRIER_SUBRING_GENERATED_SUBSET] THEN
      ASM_MESON_TAC[SUBSET_TRANS; RING_SPAN_SUBSET_SUBRING_GENERATED]] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[UNION_EMPTY] THEN
      SUBGOAL_THEN
       `IMAGE (h:A->B) (ring_carrier k) =
        ring_1 l INSERT IMAGE h (ring_carrier k)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE `(a:B) IN s ==> s = a INSERT s`) THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `ring_1 k:A` THEN
        ASM_MESON_TAC[RING_HOMOMORPHISM_1; RING_1;
                      FIELD_EXTENSION_IMP_HOMOMORPHISM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                     `ring_1 l:B`] lemma) THEN
      ASM_SIMP_TAC[ALGEBRAIC_OVER_1] THEN
      ASM_MESON_TAC[separable_extension; RING_1];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:B`; `s:B->bool`] THEN
    REWRITE_TAC[INSERT_SUBSET] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC
     `K = subring_generated l (IMAGE (h:A->B) (ring_carrier k) UNION s)` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `subring_generated l (IMAGE (h:A->B) (ring_carrier k) UNION x INSERT s) =
      subring_generated l (x INSERT IMAGE I (ring_carrier K))`
    SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN
      REWRITE_TAC[IMAGE_I; SUBRING_GENERATED_INSERT] THEN
      AP_TERM_TAC THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `field K /\ field_extension(k,K) (h:A->B) /\ field_extension(K,l) I`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `p /\ (p ==> r) /\ (r ==> q) ==> p /\ q /\ r`) THEN
      REPEAT CONJ_TAC THENL
       [EXPAND_TAC "K" THEN MATCH_MP_TAC FIELD_ALGEBRAIC_EXTENSION THEN
        ASM_MESON_TAC[algebraic_extension; SUBSET];
        DISCH_TAC THEN EXPAND_TAC "K" THEN
        MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
        ASM_REWRITE_TAC[FIELD_EXTENSION_REFL] THEN
        ASM_MESON_TAC[field_extension];
        DISCH_TAC THEN MATCH_MP_TAC FIELD_EXTENSION_INTO_INTERMEDIATE THEN
        EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "K" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
        ASM_SIMP_TAC[IN_UNION; FUN_IN_IMAGE] THEN
        ASM_MESON_TAC[FIELD_EXTENSION_CARRIER]];
      ALL_TAC] THEN
    SUBGOAL_THEN `algebraic_over (K,l) I (x:B)` ASSUME_TAC THENL
     [MATCH_MP_TAC ALGEBRAIC_OVER_FIELD_EXTENSION THEN
      MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN
      ASM_REWRITE_TAC[I_O_ID] THEN ASM_MESON_TAC[algebraic_extension];
      ALL_TAC] THEN
    ABBREV_TAC
     `K' = subring_generated l ((x:B) INSERT IMAGE I (ring_carrier K))` THEN
    SUBGOAL_THEN `field_extension(K,K') (I:B->B)` ASSUME_TAC THENL
     [EXPAND_TAC "K'" THEN MATCH_MP_TAC FINITE_IMP_FIELD_EXTENSION THEN
      MATCH_MP_TAC FINITE_SIMPLE_ALGEBRAIC_EXTENSION THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
     [`h:A->B`; `I:B->B`; `g:A->C`; `k:A ring`; `K:B ring`; `K':B ring`;
      `m:C ring`] RING_HOMOMORPHISM_EXTENSIONS_TOWER)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
     [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `K':B ring`]
     EXTENSION_DEGREE_TOWER_LAW)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `!t:B->C.
        t IN ring_homomorphism_extensions (k,K,m) (h:A->B,g:A->C)
        ==> FINITE(ring_homomorphism_extensions (K,K',m) (I,t)) /\
            CARD(ring_homomorphism_extensions (K,K',m) (I,t)) <=
            extension_degree (K,K') I /\
            (separable_extension (k,l) h /\ algebraically_closed_field m
             ==> CARD(ring_homomorphism_extensions (K,K',m) (I,t)) =
                 extension_degree (K,K') I)`
    ASSUME_TAC THENL
     [X_GEN_TAC `t:B->C` THEN
      REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`I:B->B`; `t:B->C`; `K:B ring`; `l:B ring`; `m:C ring`;
                     `x:B`] lemma) THEN
      ASM_REWRITE_TAC[GSYM ring_homomorphism_extensions] THEN
      MATCH_MP_TAC(TAUT
       `(s2 ==> s1) ==> (a /\ b /\ (s1 /\ c ==> d)) ==>
                        (a /\ b /\ (s2 /\ c ==> d))`) THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
        SEPARABLE_EXTENSION_INTERMEDIATE) THEN
      ASM_REWRITE_TAC[I_O_ID] THEN REWRITE_TAC[separable_extension] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_CARD_LE_UNIONS THEN ASM_SIMP_TAC[];
      STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_CARD THEN
      MATCH_MP_TAC HAS_SIZE_UNIONS THEN
      ASM_SIMP_TAC[HAS_SIZE; GSYM pairwise; ETA_AX]]);;

let CARD_EQ_RING_HOMOMORPHISM_EXTENSIONS =
  let lemma = prove
   (`!(h:A->B) (g:A->C) (i:A->D) k l m n.
        algebraic_extension (k,l) h /\ algebraic_extension (k,n) i /\
        algebraically_closed_field n /\
        algebraically_closed_field m /\ ring_homomorphism (k,m) g
        ==> ring_homomorphism_extensions (k,l,m) (h,g) =_c
            ring_homomorphism_extensions (k,l,n) (h,i)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `n:D ring`; `m:C ring`; `i:A->D`; `g:A->C`]
      ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:D->C` STRIP_ASSUME_TAC) THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(fun th ->
      let th' = MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION
       (check (fun th -> rand(concl th) = t) th) in
      ASSUME_TAC th' THEN
      STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [field_extension] th')))
     [`h:A->B`; `i:A->D`] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD o
      check (fun th -> concl th = `algebraically_closed_field(m:C ring)`)) THEN
    SUBGOAL_THEN `ring_monomorphism(n:D ring,m:C ring) f` ASSUME_TAC THENL
     [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
      ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!s:B->C. s IN ring_homomorphism_extensions (k,l,m) (h:A->B,g:A->C)
              ==> IMAGE s (ring_carrier l) SUBSET
                  IMAGE (f:D->C) (ring_carrier n)`
    ASSUME_TAC THENL
     [X_GEN_TAC `s:B->C` THEN
      DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC
        (REWRITE_RULE[ring_homomorphism_extensions; IN_ELIM_THM] th)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN `algebraic_over (k,l) (h:A->B) y` ASSUME_TAC THENL
       [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
      MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `s:B->C`; `k:A ring`; `l:B ring`;
                     `m:C ring`; `y:B`] RING_HOMOMORPHISM_EXTENSIONS_ROOT) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `y:B`]
        MINIMAL_POLYNOMIAL) THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `p = minimal_polynomial (k,l) (h:A->B) y` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(g:A->C) o (p:(1->num)->A) = f o (i:A->D) o p`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `j:1->num` THEN
        CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC POLY_MONOMIAL_IN_CARRIER THEN EXISTS_TAC `(:1)` THEN
        ASM_REWRITE_TAC[];
        DISCH_TAC] THEN
      MP_TAC(ISPECL [`n:D ring`; `m:C ring`; `f:D->C`;
                     `(i:A->D) o (p:(1->num)->A)`]
        POLY_ROOTS_MONOMORPHIC_IMAGE) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[POLY_EQ_0_MONOMORPHIC_IMAGE; RING_POLYNOMIAL];
          MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
          EXISTS_TAC `k:A ring` THEN
          ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(s:B->C) y IN ring_carrier m` ASSUME_TAC THENL
       [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
        EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `(s:B->C) y`) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_homomorphism_extensions (k,l,m) (h:A->B,g:A->C) =
      IMAGE (\s. RESTRICTION (ring_carrier l) ((f:D->C) o s))
            (ring_homomorphism_extensions (k,l,n) (h,i))`
    SUBST1_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC CARD_EQ_IMAGE THEN
      REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM;
                  RESTRICTION_EXTENSION; o_THM] THEN
      MAP_EVERY X_GEN_TAC [`s1:B->D`; `s2:B->D`] THEN STRIP_TAC THEN
      MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RING_MONOMORPHISM_INJECTIVE_EQ;
                    RING_HOMOMORPHISM_IN_CARRIER]] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `s:B->C` THEN EQ_TAC THENL
     [DISCH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `s0:B->D` (CONJUNCTS_THEN2 SUBST1_TAC
       (STRIP_ASSUME_TAC o
        REWRITE_RULE[ring_homomorphism_extensions; IN_ELIM_THM]))) THEN
      MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
      ASM_REWRITE_TAC[o_THM] THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE;
                    RING_MONOMORPHISM_IMP_HOMOMORPHISM]] THEN
    UNDISCH_TAC
     `(s:B->C) IN ring_homomorphism_extensions (k,l,m) (h:A->B,g:A->C)` THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[ring_homomorphism_extensions; IN_ELIM_THM]
        th)) THEN
    MP_TAC(ISPECL [`f:D->C`; `n:D ring`; `m:C ring`]
      RING_ISOMORPHISM_ONTO_IMAGE) THEN
    ASM_REWRITE_TAC[ring_isomorphism; ring_image; ring_isomorphisms] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':C->D` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `ring_carrier(subring_generated m (IMAGE (f:D->C) (ring_carrier n))) =
      IMAGE f (ring_carrier n)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CARRIER_SUBRING_GENERATED_SUBRING THEN
      MP_TAC(ISPECL [`n:D ring`; `m:C ring`; `f:D->C`] SUBRING_RING_IMAGE) THEN
      ASM_REWRITE_TAC[ring_image];
      ALL_TAC] THEN
    EXISTS_TAC `RESTRICTION (ring_carrier l) ((f':C->D) o (s:B->C))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
      ASM_REWRITE_TAC[RESTRICTION_IN_EXTENSIONAL] THEN
      ASM_SIMP_TAC[RESTRICTION; o_THM] THEN
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET; FUN_IN_IMAGE];
      MATCH_MP_TAC RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS THEN
      ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; o_THM] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
        EXISTS_TAC `subring_generated m (IMAGE (f:D->C) (ring_carrier n))` THEN
        ASM_SIMP_TAC[RING_HOMOMORPHISM_INTO_SUBRING];
        ASM_MESON_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM;
                      RING_HOMOMORPHISM_IN_CARRIER]]]) in
  prove
   (`!(h:A->B) (g:A->C) (g':A->D) k l m m'.
        algebraic_extension (k,l) h /\
        algebraically_closed_field m /\ ring_homomorphism (k,m) g /\
        algebraically_closed_field m' /\ ring_homomorphism (k,m') g'
        ==> ring_homomorphism_extensions (k,l,m) (h,g) =_c
            ring_homomorphism_extensions (k,l,m') (h,g')`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ALGEBRAIC_IMP_FIELD_EXTENSION; field_extension];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`n:(A#num)ring`; `i:A->A#num`] THEN STRIP_TAC THEN
    TRANS_TAC CARD_EQ_TRANS
     `ring_homomorphism_extensions (k,l,n) (h:A->B,i:A->A#num)` THEN
    CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[CARD_EQ_SYM]] THEN
    MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The separable degree [l:k]_s: the number of extensions to l of the        *)
(* embedding of k in an algebraic closure of l, and 0 if there are           *)
(* infinitely many (as for extension_degree). For an algebraic extension     *)
(* it is the number of extensions of any g from k into any algebraically     *)
(* closed field (SEPARABLE_DEGREE). It is multiplicative in towers, and for  *)
(* a finite extension it is at most [l:k], with equality exactly when l is   *)
(* separable; hence separability is transitive, and finitely many separable  *)
(* elements generate a separable extension.                                  *)
(* ------------------------------------------------------------------------- *)

let separable_degree = new_definition
 `separable_degree (k:A ring,l:B ring) (h:A->B) =
        @n. ?m (j:B->B#num).
              algebraic_extension (l,m) j /\ algebraically_closed_field m /\
              n = if FINITE(ring_homomorphism_extensions (k,l,m) (h,j o h))
                  then CARD(ring_homomorphism_extensions (k,l,m) (h,j o h))
                  else 0`;;

let SEPARABLE_DEGREE = prove
 (`!(h:A->B) (g:A->C) k l m.
        algebraic_extension (k,l) h /\ algebraically_closed_field m /\
        ring_homomorphism (k,m) g
        ==> separable_degree (k,l) h =
            if FINITE(ring_homomorphism_extensions (k,l,m) (h,g))
            then CARD(ring_homomorphism_extensions (k,l,m) (h,g)) else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[separable_degree] THEN
  MATCH_MP_TAC(MESON[]
   `(?n:num. P n) /\ (!n. P n ==> n = a) ==> (@n. P n) = a`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ALGEBRAIC_IMP_FIELD_EXTENSION; field_extension];
      MESON_TAC[]];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`m':(B#num)ring`; `j:B->B#num`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `g:A->C`;
                   `k:A ring`; `l:B ring`; `m':(B#num)ring`; `m:C ring`]
      CARD_EQ_RING_HOMOMORPHISM_EXTENSIONS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
      EXISTS_TAC `l:B ring` THEN
      ASM_MESON_TAC[ALGEBRAIC_IMP_FIELD_EXTENSION;
                    FIELD_EXTENSION_IMP_HOMOMORPHISM];
      DISCH_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP CARD_FINITE_CONG) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CARD_EQ_CARD_IMP]]);;

let HAS_SIZE_SEPARABLE_DEGREE = prove
 (`!(h:A->B) (g:A->C) k l m.
        finite_extension (k,l) h /\ algebraically_closed_field m /\
        ring_homomorphism (k,m) g
        ==> ring_homomorphism_extensions (k,l,m) (h,g) HAS_SIZE
            separable_degree (k,l) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    CARD_RING_HOMOMORPHISM_EXTENSIONS_LE) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    SEPARABLE_DEGREE) THEN
  ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION; FIELD_IMP_INTEGRAL_DOMAIN;
               ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
  SIMP_TAC[HAS_SIZE]);;

let SEPARABLE_DEGREE_LE_EXTENSION_DEGREE = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h
        ==> separable_degree (k,l) h <= extension_degree (k,l) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_FIELD_EXTENSION; field_extension];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`m:(A#num)ring`; `g:A->A#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `l:B ring`;
                 `m:(A#num)ring`] CARD_RING_HOMOMORPHISM_EXTENSIONS_LE) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `l:B ring`;
                 `m:(A#num)ring`] HAS_SIZE_SEPARABLE_DEGREE) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
               HAS_SIZE]);;

let SEPARABLE_DEGREE_TOWER = prove
 (`!(f:A->B) (g:B->C) k l m.
        algebraic_extension (k,l) f /\ algebraic_extension (l,m) g
        ==> separable_degree (k,m) (g o f) =
            separable_degree (k,l) f * separable_degree (l,m) g`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION o
    check (fun th -> rand(concl th) = t)))
   [`f:A->B`; `g:B->C`] THEN
  MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ALGEBRAIC_IMP_FIELD_EXTENSION; field_extension];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`n:(A#num)ring`; `j:A->A#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION o
    check (fun th -> rand(concl th) = `j:A->A#num`)) THEN
  MP_TAC(ISPECL [`f:A->B`; `j:A->A#num`; `k:A ring`; `l:B ring`;
                 `n:(A#num)ring`] RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:B->A#num` (fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[ring_homomorphism_extensions; IN_ELIM_THM]
                       th))) THEN
  SUBGOAL_THEN `algebraic_extension (k,m) ((g:B->C) o (f:A->B))`
  ASSUME_TAC THENL [ASM_MESON_TAC[ALGEBRAIC_EXTENSION_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `j:A->A#num`; `k:A ring`;
                 `m:C ring`; `n:(A#num)ring`] SEPARABLE_DEGREE) THEN
  MP_TAC(ISPECL [`f:A->B`; `j:A->A#num`; `k:A ring`; `l:B ring`;
                 `n:(A#num)ring`] SEPARABLE_DEGREE) THEN
  MP_TAC(ISPECL [`g:B->C`; `t0:B->A#num`; `l:B ring`; `m:C ring`;
                 `n:(A#num)ring`] SEPARABLE_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ABBREV_TAC `X = ring_homomorphism_extensions (k,l,n) (f:A->B,j:A->A#num)` THEN
  ABBREV_TAC `Y = ring_homomorphism_extensions (l,m,n)
                    (g:B->C,t0:B->A#num)` THEN
  SUBGOAL_THEN
   `!t:B->A#num.
        t IN X
        ==> ring_homomorphism_extensions (l,m,n) (g:B->C,t) =_c
            (Y:(C->A#num)->bool) /\
            ~(ring_homomorphism_extensions (l,m,n) (g,t) = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:B->A#num` THEN EXPAND_TAC "X" THEN
    REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN STRIP_TAC THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[GSYM ring_homomorphism_extensions] THEN
    ASM_SIMP_TAC[CARD_EQ_RING_HOMOMORPHISM_EXTENSIONS;
                 RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism_extensions (k,m,n) ((g:B->C) o (f:A->B),j:A->A#num) =_c
    (X:(B->A#num)->bool) *_c (Y:(C->A#num)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `j:A->A#num`; `k:A ring`; `l:B ring`;
                   `m:C ring`; `n:(A#num)ring`]
      RING_HOMOMORPHISM_EXTENSIONS_TOWER) THEN
    ASM_REWRITE_TAC[SIMPLE_IMAGE; pairwise] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    TRANS_TAC CARD_EQ_TRANS
     `IMAGE (\t. ring_homomorphism_extensions (l,m,n) (g:B->C,t:B->A#num))
            X *_c (Y:(C->A#num)->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_EQ_DISJOINT_UNIONS THEN
      REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                  FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC CARD_MUL_CONG THEN REWRITE_TAC[CARD_EQ_REFL] THEN
      MATCH_MP_TAC CARD_EQ_IMAGE THEN
      MAP_EVERY X_GEN_TAC [`t:B->A#num`; `t':B->A#num`] THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:B->A#num`; `t':B->A#num`] o
        check (fun th -> is_forall(concl th) &&
                         is_forall(snd(dest_forall(concl th))))) THEN
      ASM_REWRITE_TAC[DISJOINT; INTER_IDEMPOT] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CARD_FINITE_CONG) THEN
  SUBGOAL_THEN `~((X:(B->A#num)->bool) = {}) /\ ~((Y:(C->A#num)->bool) = {})`
  STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_REWRITE_TAC[CARD_MUL_FINITE_EQ]] THEN
  ASM_CASES_TAC `FINITE(X:(B->A#num)->bool)` THEN
  ASM_CASES_TAC `FINITE(Y:(C->A#num)->bool)` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  TRANS_TAC EQ_TRANS `CARD((X:(B->A#num)->bool) *_c (Y:(C->A#num)->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_CARD_IMP THEN ASM_SIMP_TAC[CARD_MUL_FINITE];
    ASM_SIMP_TAC[CARD_MUL_C]]);;

let SEPARABLE_DEGREE_SIMPLE = prove
 (`!(h:A->B) (g:A->C) k l m a.
        field_extension (k,l) h /\ algebraic_over (k,l) h a /\
        algebraically_closed_field m /\ ring_homomorphism (k,m) g
        ==> separable_degree
             (k,subring_generated l (a INSERT IMAGE h (ring_carrier k))) h =
            CARD {b | b IN ring_carrier m /\
                      poly_eval m (g o minimal_polynomial (k,l) h a) b =
                      ring_0 m}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `a:B`] RING_HOMOMORPHISM_EXTENSIONS_SIMPLE) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`;
                 `subring_generated l
                    ((a:B) INSERT IMAGE (h:A->B) (ring_carrier k))`;
                 `m:C ring`] HAS_SIZE_SEPARABLE_DEGREE) THEN
  ASM_SIMP_TAC[FINITE_SIMPLE_ALGEBRAIC_EXTENSION] THEN
  MESON_TAC[CARD_HAS_SIZE_CONG; HAS_SIZE]);;

let SEPARABLE_DEGREE_SIMPLE_LT = prove
 (`!(h:A->B) k l a.
        field_extension (k,l) h /\ algebraic_over (k,l) h a /\
        ~separable_element (k,l) h a
        ==> separable_degree
             (k,subring_generated l (a INSERT IMAGE h (ring_carrier k))) h <
            extension_degree
             (k,subring_generated l (a INSERT IMAGE h (ring_carrier k))) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:(A#num)ring`; `g:A->A#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `l:B ring`;
                 `m:(A#num)ring`; `a:B`] SEPARABLE_DEGREE_SIMPLE) THEN
  ASM_SIMP_TAC[EXTENSION_DEGREE_SIMPLE; FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC POLY_INSEPARABLE_ROOTS_LT_DEG THEN
  ASM_MESON_TAC[MINIMAL_POLYNOMIAL; separable_element]);;

let SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h
        ==> (separable_degree (k,l) h = extension_degree (k,l) h <=>
             separable_extension (k,l) h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  EQ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:(A#num)ring`; `g:A->A#num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM o
      MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `l:B ring`;
                   `m:(A#num)ring`] HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS) THEN
    MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `l:B ring`;
                   `m:(A#num)ring`] HAS_SIZE_SEPARABLE_DEGREE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[HAS_SIZE]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  ASM_REWRITE_TAC[separable_extension; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `algebraic_over (k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    SEPARABLE_DEGREE_SIMPLE_LT) THEN
  ABBREV_TAC
   `K = subring_generated l ((x:B) INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `finite_extension (k,K) (h:A->B) /\ field_extension (K,l) I`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SIMPLE_ALGEBRAIC_EXTENSION THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
      REWRITE_TAC[FIELD_EXTENSION_REFL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[field_extension];
        MATCH_MP_TAC FIELD_SIMPLE_ALGEBRAIC_EXTENSION THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
   [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
   FINITE_EXTENSION_TRANS_EQ)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
   [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
   EXTENSION_DEGREE_TOWER_LAW)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
   [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
   SEPARABLE_DEGREE_TOWER)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `a:num < b ==> ~(a = b)`) THEN
  TRANS_TAC LET_TRANS
   `separable_degree(k,K) (h:A->B) * extension_degree (K,l) (I:B->B)` THEN
  ASM_SIMP_TAC[LT_MULT_RCANCEL; LE_MULT_LCANCEL; EXTENSION_DEGREE_EQ_0;
               SEPARABLE_DEGREE_LE_EXTENSION_DEGREE]);;

let SEPARABLE_EXTENSION_SIMPLE = prove
 (`!(h:A->B) k l a.
        field_extension (k,l) h /\ algebraic_over (k,l) h a
        ==> (separable_extension
              (k,subring_generated l (a INSERT IMAGE h (ring_carrier k))) h <=>
             separable_element (k,l) h a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [algebraic_over]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `IMAGE (h:A->B) (ring_carrier k) SUBSET a INSERT IMAGE h (ring_carrier k)`
  ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
    FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `(a:B) INSERT IMAGE (h:A->B) (ring_carrier k)`; `a:B`]
    MINIMAL_POLYNOMIAL_SUBRING_GENERATED) THEN
  ASM_SIMP_TAC[GSYM SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE; IN_INSERT] THEN
  ABBREV_TAC
   `K = subring_generated l ((a:B) INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  REPEAT DISCH_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:(A#num)ring`; `g:A->A#num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `l:B ring`;
                   `m:(A#num)ring`; `a:B`] SEPARABLE_DEGREE_SIMPLE) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
      EXTENSION_DEGREE_SIMPLE) THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MATCH_MP_TAC POLY_SPLITS_OVER_SEPARABLE_ROOT_COUNT THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER; GSYM separable_element;
                 poly_splits_over] THEN
    MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FIELD_POLY_SPLITS THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `k:A ring` THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER;
                 FIELD_EXTENSION_IMP_HOMOMORPHISM]] THEN
  ASM_SIMP_TAC[SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE] THEN
  REWRITE_TAC[separable_extension] THEN
  DISCH_THEN(MP_TAC o SPEC `a:B` o CONJUNCT2) THEN ANTS_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ASM_REWRITE_TAC[separable_element]]);;

let SEPARABLE_EXTENSION_TRANS =
  let lemma = prove
   (`!(f:A->B) (g:B->C) k l m.
        finite_extension (k,l) f /\ finite_extension (l,m) g /\
        separable_extension (k,l) f /\ separable_extension (l,m) g
        ==> separable_extension (k,m) (g o f)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
      FINITE_EXTENSION_TRANS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
      EXTENSION_DEGREE_TOWER_LAW) THEN
    MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
      SEPARABLE_DEGREE_TOWER) THEN
    SUBGOAL_THEN
     `separable_degree (k,l) (f:A->B) = extension_degree (k,l) f /\
      separable_degree (l,m) (g:B->C) = extension_degree (l,m) g`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE;
                 FINITE_IMP_ALGEBRAIC_EXTENSION;
                 FINITE_IMP_FIELD_EXTENSION]) in
  prove
   (`!(f:A->B) (g:B->C) k l m.
        separable_extension (k,l) f /\ separable_extension (l,m) g
        ==> separable_extension (k,m) (g o f)`,
    REPEAT STRIP_TAC THEN
    MAP_EVERY (fun t -> FIRST_ASSUM(fun th ->
      let th' = MATCH_MP SEPARABLE_IMP_ALGEBRAIC_EXTENSION
       (check (fun th -> rand(concl th) = t) th) in
      ASSUME_TAC th' THEN
      ASSUME_TAC(MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION th')))
     [`f:A->B`; `g:B->C`] THEN
    REWRITE_TAC[separable_extension] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ALGEBRAIC_EXTENSION_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `z:C` THEN DISCH_TAC THEN
    SUBGOAL_THEN `algebraic_over (l,m) (g:B->C) z /\
                  algebraic_over (k,m) (g o (f:A->B)) z`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[algebraic_extension; ALGEBRAIC_EXTENSION_TRANS];
      ALL_TAC] THEN
    ABBREV_TAC `q = minimal_polynomial (l,m) (g:B->C) z` THEN
    MP_TAC(ISPECL [`g:B->C`; `l:B ring`; `m:C ring`; `z:C`]
      MINIMAL_POLYNOMIAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `poly_separable l (q:(1->num)->B)` ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC[GSYM separable_element] THEN
      ASM_MESON_TAC[separable_extension];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `ring_carrier l:B->bool`; `(:1)`;
                   `q:(1->num)->B`]
      IN_POLY_RING_SUBRING_GENERATED_FINITARY) THEN
    ASM_REWRITE_TAC[SUBRING_GENERATED_RING_CARRIER] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC
     `K = subring_generated l (IMAGE (f:A->B) (ring_carrier k) UNION t)` THEN
    SUBGOAL_THEN
     `finite_extension (k,K) (f:A->B) /\ field_extension (K,l) I /\
      q IN ring_carrier(poly_ring K (:1))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION THEN
        ASM_MESON_TAC[algebraic_extension; SUBSET];
        MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
        REWRITE_TAC[FIELD_EXTENSION_REFL] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
        MATCH_MP_TAC FIELD_ALGEBRAIC_EXTENSION THEN
        ASM_MESON_TAC[algebraic_extension; SUBSET];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `(p:A) IN s ==> s SUBSET t ==> p IN t`)) THEN
        MATCH_MP_TAC RING_CARRIER_POLY_SUBRING_GENERATED_MONO THEN
        SET_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
    SUBGOAL_THEN
     `separable_extension (k,K) (f:A->B) /\ field_extension (K,m) (g:B->C)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(ISPECL [`f:A->B`; `I:B->B`]
          SEPARABLE_EXTENSION_SUBFIELD) THEN
        EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[I_O_ID];
        MP_TAC(ISPECL [`I:B->B`; `g:B->C`; `K:B ring`; `l:B ring`; `m:C ring`]
          FIELD_EXTENSION_TRANS) THEN
        ASM_REWRITE_TAC[I_O_ID]];
      ALL_TAC] THEN
    SUBGOAL_THEN `algebraic_over (K,m) (g:B->C) z` ASSUME_TAC THENL
     [MATCH_MP_TAC ALGEBRAIC_OVER_FIELD_EXTENSION THEN
      MAP_EVERY EXISTS_TAC [`f:A->B`; `k:A ring`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `separable_element (K,m) (g:B->C) z` ASSUME_TAC THENL
     [REWRITE_TAC[separable_element] THEN
      MATCH_MP_TAC POLY_SEPARABLE_DIVISOR THEN
      EXISTS_TAC `q:(1->num)->B` THEN
      ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER;
                   MINIMAL_POLYNOMIAL_DIVIDES] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "K" THEN ASM_REWRITE_TAC[POLY_EXTEND_FROM_SUBRING_GENERATED];
        MATCH_MP_TAC POLY_SEPARABLE_FROM_MONOMORPHIC_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`l:B ring`; `I:B->B`] THEN
        ASM_REWRITE_TAC[I_O_ID] THEN
        ASM_MESON_TAC[field_extension]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:B->C`; `K:B ring`; `m:C ring`; `z:C`]
      SEPARABLE_EXTENSION_SIMPLE) THEN
    MP_TAC(ISPECL [`g:B->C`; `K:B ring`; `m:C ring`; `z:C`]
      FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC
     `L = subring_generated m
            ((z:C) INSERT IMAGE (g:B->C) (ring_carrier K))` THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `K:B ring`; `L:C ring`]
      lemma) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `minimal_polynomial (k,L) ((g:B->C) o (f:A->B)) z =
      minimal_polynomial (k,m) (g o f) z /\ z IN ring_carrier L`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN CONJ_TAC THENL
       [MATCH_MP_TAC MINIMAL_POLYNOMIAL_SUBRING_GENERATED THEN
        ASM_REWRITE_TAC[IN_INSERT; IMAGE_o] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE;
                        FIELD_EXTENSION_IMP_HOMOMORPHISM];
          MP_TAC(ISPECL [`f:A->B`; `k:A ring`; `K:B ring`]
            FIELD_EXTENSION_IMP_SUBSET) THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[]];
        MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
        ASM_REWRITE_TAC[IN_INSERT]];
      ALL_TAC] THEN
    REWRITE_TAC[separable_extension; separable_element] THEN
    ASM_MESON_TAC[]);;

let SEPARABLE_EXTENSION_TRANS_EQ = prove
 (`!(f:A->B) (g:B->C) k l m.
        field_extension (k,l) f /\ field_extension (l,m) g
        ==> (separable_extension (k,m) (g o f) <=>
             separable_extension (k,l) f /\ separable_extension (l,m) g)`,
  MESON_TAC[SEPARABLE_EXTENSION_TRANS; SEPARABLE_EXTENSION_SUBFIELD;
            SEPARABLE_EXTENSION_INTERMEDIATE]);;

let SEPARABLE_EXTENSION_GENERATED_BY_SEPARABLE = prove
 (`!(h:A->B) k l b.
        field_extension(k,l) h /\ FINITE b /\
        (!x. x IN b ==> separable_element(k,l) h x)
        ==> separable_extension
             (k,subring_generated l (IMAGE h (ring_carrier k) UNION b)) h`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNION_EMPTY; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SEPARABLE_EXTENSION_ISOMORPHISM THEN
    ASM_MESON_TAC[field_extension; RING_ISOMORPHISM_ONTO_IMAGE; ring_image];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `b:B->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
  STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `s UNION ((y:B) INSERT t) = y INSERT (s UNION t)`] THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_INSERT] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B->bool`]
    FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SEPARABLE_ELEMENT_IMP_ALGEBRAIC; field_extension];
    ALL_TAC] THEN
  UNDISCH_TAC
   `separable_extension
     (k,subring_generated l (IMAGE (h:A->B) (ring_carrier k) UNION b)) h` THEN
  ABBREV_TAC
   `K = subring_generated l (IMAGE (h:A->B) (ring_carrier k) UNION b)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `field_extension (K,l) (I:B->B)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
    ASM_MESON_TAC[FINITE_IMP_FIELD_EXTENSION; field_extension;
                  FIELD_EXTENSION_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `separable_element (K,l) (I:B->B) y` ASSUME_TAC THENL
   [MATCH_MP_TAC SEPARABLE_ELEMENT_INTERMEDIATE THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN
    ASM_SIMP_TAC[I_O_ID; FINITE_IMP_FIELD_EXTENSION];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`; `y:B`]
    SEPARABLE_EXTENSION_SIMPLE) THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SEPARABLE_ELEMENT_IMP_ALGEBRAIC; field_extension];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`;
                 `subring_generated l ((y:B) INSERT ring_carrier K)`]
    SEPARABLE_EXTENSION_TRANS) THEN
  ASM_REWRITE_TAC[I_O_ID]);;

(* ------------------------------------------------------------------------- *)
(* The separable closure of k in l, the set of elements of l separable over  *)
(* k: a subfield of l containing the image of k and separable over k; when   *)
(* l is algebraic over k it is purely inseparable over the closure. Purely   *)
(* inseparable extensions are algebraic, with no separable elements outside  *)
(* the image of k: in characteristic p those where each x has a power        *)
(* x^(p^n) coming from k (e.g. l over its subfield of p-th powers), over a   *)
(* perfect field just the trivial ones. The inseparable degree [l:k]_i is    *)
(* the degree of l over the separable closure. For finite l, [l:k] =         *)
(* [l:k]_s * [l:k]_i, with [l:k]_s the degree of the separable closure over  *)
(* k; [l:k]_i is a power of the characteristic and multiplicative in         *)
(* towers.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Separability is preserved by monomorphic images. In characteristic c, a   *)
(* separable x some x^(c^n) of which comes from k lies in k, and some        *)
(* x^(c^n) of each algebraic x is separable. Hence if x is not in k but x^c  *)
(* is, its minimal polynomial has degree c.                                  *)

let SEPARABLE_ELEMENT_MONOMORPHIC_IMAGE = prove
 (`!(f:A->B) (g:B->C) k l m x.
        x IN ring_carrier l /\
        ring_homomorphism(k,l) f /\ ring_monomorphism(l,m) g
        ==> (separable_element (k,m) (g o f) (g x) <=>
             separable_element (k,l) f x)`,
  SIMP_TAC[separable_element; MINIMAL_POLYNOMIAL_MONOMORPHIC_IMAGE]);;

let SEPARABLE_ELEMENT_POW_IN_IMAGE = prove
 (`!(h:A->B) k l x n.
        field_extension(k,l) h /\ prime(ring_char k) /\
        separable_element(k,l) h x /\
        ring_pow l x (ring_char k EXP n) IN IMAGE h (ring_carrier k)
        ==> x IN IMAGE h (ring_carrier k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[SEPARABLE_ELEMENT_IMP_ALGEBRAIC]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL_DEG_EQ_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `separable_element(k,l) (h:A->B) x` THEN
  REWRITE_TAC[separable_element] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `f = minimal_polynomial (k,l) (h:A->B) x` THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `~(n = 0) /\ n <= 1 ==> n = 1`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IRREDUCIBLE_IMP_POLY_DEG_NZ]; ALL_TAC] THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:(B#num)ring`; `j:B->B#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `field_extension(k,m) ((j:B->B#num) o (h:A->B))`
  ASSUME_TAC THENL [ASM_MESON_TAC[FIELD_EXTENSION_TRANS]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    concl th = `field_extension(l:B ring,m:(B#num)ring) j`)) THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> rand(concl th) = `j:B->B#num`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  ABBREV_TAC `N = ring_char(k:A ring) EXP n` THEN
  MP_TAC(ISPECL [`(j:B->B#num) o (h:A->B)`; `k:A ring`; `m:(B#num)ring`;
                 `f:(1->num)->A`] POLY_SEPARABLE_ROOT_COUNT_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(MESON[CARD_SING; CARD_SUBSET; FINITE_SING]
   `(?a:B#num. s SUBSET {a}) ==> CARD s <= 1`) THEN
  EXISTS_TAC `(j:B->B#num) x` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `z:B#num` THEN STRIP_TAC THEN
  ABBREV_TAC
   `g = poly_sub k (poly_pow k (poly_var k one) N) (poly_const k (a:A))` THEN
  SUBGOAL_THEN `(g:(1->num)->A) IN ring_carrier(poly_ring k (:1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) a IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_divides (poly_ring k (:1)) (f:(1->num)->A) g`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`; `g:(1->num)->A`]
      MINIMAL_POLYNOMIAL_DIVIDES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[POLY_EXTEND_SUB; POLY_EXTEND_VARPOW; POLY_EXTEND_CONST;
                 RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_CONST; RING_SUB_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `m:(B#num)ring`;
                 `poly_extend (k,m) ((j:B->B#num) o (h:A->B)) (\v:1. z)`;
                 `f:(1->num)->A`; `g:(1->num)->A`]
    RING_DIVIDES_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_EXTEND; FIELD_EXTENSION_IMP_HOMOMORPHISM;
               POLY_EXTEND_EVALUATE; GSYM poly_eval; RING_DIVIDES_ZERO] THEN
  SUBGOAL_THEN
   `poly_eval m (((j:B->B#num) o (h:A->B)) o g) z =
    ring_sub m (ring_pow m z N) (j(h(a:A)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[poly_eval] THEN
    MP_TAC(ISPECL [`k:A ring`; `m:(B#num)ring`; `(j:B->B#num) o (h:A->B)`;
                   `\v:1. (z:B#num)`; `g:(1->num)->A`]
      POLY_EXTEND_EVALUATE) THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[POLY_EXTEND_SUB; POLY_EXTEND_VARPOW; POLY_EXTEND_CONST;
                 RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR; o_THM;
                 FIELD_EXTENSION_IMP_HOMOMORPHISM; RING_POLYNOMIAL_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:B->B#num)(h(a:A)) = ring_pow m (j x) N` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      lhand(concl th) = `ring_pow l (x:B) N`)) THEN
    MP_TAC(ISPECL [`l:B ring`; `m:(B#num)ring`; `j:B->B#num`]
      RING_HOMOMORPHISM_POW) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:B->B#num) x IN ring_carrier m` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_SUB_EQ_0; RING_POW] THEN
  MP_TAC(ISPECL [`m:(B#num)ring`; `n:num`]
    RING_MONOMORPHISM_FROBENIUS_ITERATE) THEN
  SUBGOAL_THEN `ring_char(m:(B#num)ring) = ring_char(k:A ring)`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE; field_extension]; ALL_TAC] THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:B#num`; `(j:B->B#num) x`] o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] RING_MONOMORPHISM_INJECTIVE_EQ)) THEN
  ASM_SIMP_TAC[]);;

let SEPARABLE_ELEMENT_POW_EXISTS = prove
 (`!(h:A->B) k l x.
        field_extension(k,l) h /\ prime(ring_char k) /\ algebraic_over(k,l) h x
        ==> ?n. separable_element(k,l) h (ring_pow l x (ring_char k EXP n))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ABBREV_TAC `c = ring_char(k:A ring)` THEN
  SUBGOAL_THEN
   `!d y. algebraic_over(k,l) (h:A->B) y /\
          poly_deg k (minimal_polynomial(k,l) h y) = d
          ==> ?n. separable_element(k,l) h (ring_pow l y (c EXP n))`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  ASM_CASES_TAC `separable_element(k,l) (h:A->B) y` THENL
   [EXISTS_TAC `0` THEN ASM_SIMP_TAC[EXP; RING_POW_1]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `y:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `f = minimal_polynomial (k,l) (h:A->B) y` THEN STRIP_TAC THEN
  SUBGOAL_THEN `poly_deriv k (f:(1->num)->A) = poly_0 k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `f:(1->num)->A`]
      POLY_SEPARABLE_EQ_DERIV_NONZERO) THEN
    UNDISCH_TAC `~separable_element(k,l) (h:A->B) y` THEN
    ASM_REWRITE_TAC[separable_element] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `f:(1->num)->A`] POLY_DERIV_EQ_0_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `poly_extend (k,l) (h:A->B) (\v:1. ring_pow l y c) (q:(1->num)->A) =
    ring_0 l`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`h:A->B`; `l:B ring`; `y:B`]) THEN
    UNDISCH_TAC
     `poly_extend (k,l) (h:A->B) (\v:1. y) (f:(1->num)->A) = ring_0 l` THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; GSYM poly_eval];
    ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) (ring_pow l y c)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[ALGEBRAIC_OVER_POW]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `ring_pow l (y:B) c`;
                 `q:(1->num)->A`] MINIMAL_POLYNOMIAL_DEG_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `poly_deg k (minimal_polynomial(k,l) (h:A->B) (ring_pow l y c))`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `poly_deg k (q:(1->num)->A)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `f:(1->num)->A`]
      IRREDUCIBLE_IMP_POLY_DEG_NZ) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `e < c * e <=> 1 * e < c * e`; LT_MULT_RCANCEL] THEN
    REWRITE_TAC[MULT_EQ_0] THEN ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `ring_pow l (y:B) c`)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  EXISTS_TAC `SUC n` THEN ASM_SIMP_TAC[EXP; GSYM RING_POW_POW]);;

let MINIMAL_POLYNOMIAL_DEG_EQ_CHAR = prove
 (`!(h:A->B) k l x.
        field_extension(k,l) h /\ prime(ring_char k) /\ x IN ring_carrier l /\
        ring_pow l x (ring_char k) IN IMAGE h (ring_carrier k) /\
        ~(x IN IMAGE h (ring_carrier k))
        ==> poly_deg k (minimal_polynomial(k,l) h x) = ring_char k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`;
                   `ring_char(k:A ring)`] ALGEBRAIC_OVER_POW_EQ) THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `ring_pow l (x:B) (ring_char(k:A ring)) IN
      IMAGE (h:A->B) (ring_carrier k)` THEN
    REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ALGEBRAIC_OVER_IMAGE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [IN_IMAGE] o check (fun th ->
      concl th = `ring_pow l (x:B) (ring_char(k:A ring)) IN
                  IMAGE (h:A->B) (ring_carrier k)`)) THEN
  ABBREV_TAC `c = ring_char(k:A ring)` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `f = minimal_polynomial (k,l) (h:A->B) x` THEN STRIP_TAC THEN
  ABBREV_TAC
   `g = poly_sub k (poly_pow k (poly_var k one) c) (poly_const k (a:A))` THEN
  SUBGOAL_THEN
   `(g:(1->num)->A) IN ring_carrier(poly_ring k (:1)) /\ poly_deg k g = c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                 RING_POLYNOMIAL_CONST; POLY_DEG_SUB_CONST; POLY_DEG_VAR_POW;
                 FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg k (f:(1->num)->A) <= c` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `poly_deg k (g:(1->num)->A) = c`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      lhand(concl th) = `minimal_polynomial (k,l) (h:A->B) x`)) THEN
    MATCH_MP_TAC MINIMAL_POLYNOMIAL_DEG_LE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `poly_deg k (g:(1->num)->A) = c` THEN
      ASM_REWRITE_TAC[POLY_DEG_0] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
      EXPAND_TAC "g" THEN
      ASM_SIMP_TAC[POLY_EXTEND_SUB; POLY_EXTEND_VARPOW; POLY_EXTEND_CONST;
                   RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                   RING_POLYNOMIAL_CONST] THEN
      MATCH_MP_TAC RING_SUB_REFL THEN ASM_MESON_TAC[FIELD_EXTENSION_CARRIER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~poly_separable k (f:(1->num)->A)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((x:B) IN IMAGE (h:A->B) (ring_carrier k))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SEPARABLE_ELEMENT_POW_IN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:B ring`; `1`] THEN
    ASM_REWRITE_TAC[separable_element; EXP_1; IN_IMAGE] THEN
    EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `f:(1->num)->A`] POLY_DERIV_EQ_0_EXPLICIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `f:(1->num)->A`]
      POLY_SEPARABLE_EQ_DERIV_NONZERO) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `f:(1->num)->A`] IRREDUCIBLE_IMP_POLY_DEG_NZ) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `poly_deg k (f:(1->num)->A) <= c` THEN
  ASM_REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN
  SUBGOAL_THEN `c <= c * poly_deg k (q:(1->num)->A) \/ poly_deg k q = 0`
  MP_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ARITH_RULE `c = c * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ARITH_TAC;
    ARITH_TAC]);;

(* The separable closure.                                                    *)

let separable_closure = new_definition
 `separable_closure (k:A ring,l:B ring) (h:A->B) =
        {x | x IN ring_carrier l /\ separable_element (k,l) h x}`;;

let IN_SEPARABLE_CLOSURE = prove
 (`!(h:A->B) k l x.
        x IN separable_closure (k,l) h <=>
        x IN ring_carrier l /\ separable_element (k,l) h x`,
  REWRITE_TAC[separable_closure; IN_ELIM_THM]);;

let SUBFIELD_OF_SEPARABLE_CLOSURE = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h
        ==> separable_closure (k,l) h subfield_of l /\
            IMAGE h (ring_carrier k) SUBSET separable_closure (k,l) h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SEPARABLE_CLOSURE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[SEPARABLE_ELEMENT_IMAGE] THEN
    ASM_MESON_TAC[FIELD_EXTENSION_CARRIER];
    DISCH_TAC] THEN
  ABBREV_TAC `s = separable_closure (k,l) (h:A->B)` THEN
  SUBGOAL_THEN
   `!x y. x IN s /\ y IN s
          ==> ring_carrier(subring_generated l
                (IMAGE (h:A->B) (ring_carrier k) UNION {x,y})) subfield_of l /\
              ring_carrier(subring_generated l
                (IMAGE (h:A->B) (ring_carrier k) UNION {x,y})) SUBSET s /\
              x IN ring_carrier(subring_generated l
                (IMAGE (h:A->B) (ring_carrier k) UNION {x,y})) /\
              y IN ring_carrier(subring_generated l
                (IMAGE (h:A->B) (ring_carrier k) UNION {x,y}))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `{x:B,y}`]
      SEPARABLE_EXTENSION_GENERATED_BY_SEPARABLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                      NOT_IN_EMPTY] THEN
      EXPAND_TAC "s" THEN ASM_MESON_TAC[IN_SEPARABLE_CLOSURE];
      ALL_TAC] THEN
    ABBREV_TAC
     `K = subring_generated l
            (IMAGE (h:A->B) (ring_carrier k) UNION {x,y})` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `x IN ring_carrier K /\ (y:B) IN ring_carrier K`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN CONJ_TAC THEN
      MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
      REWRITE_TAC[IN_UNION; IN_INSERT] THEN
      EXPAND_TAC "s" THEN ASM_MESON_TAC[IN_SEPARABLE_CLOSURE];
      ASM_REWRITE_TAC[]] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEPARABLE_IMP_FIELD_EXTENSION) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[subfield_of] THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[SUBRING_SUBRING_GENERATED;
                  SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[field_extension];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[IN_SEPARABLE_CLOSURE] THEN
    SUBGOAL_THEN `(z:B) IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET; SUBSET];
      ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`;
                   `z:B`] SEPARABLE_ELEMENT_MONOMORPHIC_IMAGE) THEN
    REWRITE_TAC[I_O_ID; I_THM] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] RING_MONOMORPHISM_INCLUSION];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_MESON_TAC[separable_extension];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBFIELD_OF_FIELD_INV THEN ASM_REWRITE_TAC[subring_of] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[SUBSET; IN_SEPARABLE_CLOSURE] THEN
    SIMP_TAC[];
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_HOMOMORPHISM_0) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
      check (fun th -> rand(concl th) = `s:B->bool`)) THEN
    REWRITE_TAC[RING_0];
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP RING_HOMOMORPHISM_1) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
      check (fun th -> rand(concl th) = `s:B->bool`)) THEN
    REWRITE_TAC[RING_1];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:B`; `x:B`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[IN_SUBFIELD_NEG; SUBSET];
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:B`; `y:B`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[IN_SUBFIELD_ADD; SUBSET];
    MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:B`; `y:B`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[IN_SUBFIELD_MUL; SUBSET];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:B`; `x:B`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[IN_SUBFIELD_INV; SUBSET]]);;

let SEPARABLE_EXTENSION_SEPARABLE_CLOSURE = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h
        ==> separable_extension
              (k,subfield_generated l (separable_closure (k,l) h)) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    SUBFIELD_OF_SEPARABLE_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = separable_closure (k,l) (h:A->B)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `field_extension(k,subfield_generated l s) (h:A->B)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[separable_extension; algebraic_extension] THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; AND_FORALL_THM] THEN
  X_GEN_TAC `x:B` THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `x IN ring_carrier l /\ separable_element(k,l) (h:A->B) x`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_MESON_TAC[IN_SEPARABLE_CLOSURE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALGEBRAIC_OVER_SUBFIELD_GENERATED THEN
    ASM_MESON_TAC[SEPARABLE_ELEMENT_IMP_ALGEBRAIC; field_extension];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`;
                 `subfield_generated l (s:B->bool)`; `l:B ring`; `x:B`]
    SEPARABLE_ELEMENT_MONOMORPHIC_IMAGE) THEN
  REWRITE_TAC[I_O_ID; I_THM] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD;
                 FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    MATCH_MP_TAC FIELD_EXTENSION_IMP_MONOMORPHISM THEN
    ASM_MESON_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; field_extension];
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]);;

let SEPARABLE_EXTENSION_EQ_SEPARABLE_CLOSURE = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h
        ==> (separable_extension(k,l) h <=>
             separable_closure (k,l) h = ring_carrier l)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[separable_extension; algebraic_extension; EXTENSION;
                  IN_SEPARABLE_CLOSURE] THEN
  ASM_MESON_TAC[SEPARABLE_ELEMENT_IMP_ALGEBRAIC; field_extension]);;

(* Purely inseparable extensions.                                            *)

let purely_inseparable_extension = new_definition
 `purely_inseparable_extension (k:A ring,l:B ring) (h:A->B) <=>
        algebraic_extension (k,l) h /\
        !x. x IN separable_closure (k,l) h ==> x IN IMAGE h (ring_carrier k)`;;

let PURELY_INSEPARABLE_IMP_ALGEBRAIC_EXTENSION = prove
 (`!(h:A->B) k l.
        purely_inseparable_extension (k,l) h ==> algebraic_extension (k,l) h`,
  SIMP_TAC[purely_inseparable_extension]);;

let PURELY_INSEPARABLE_IMP_FIELD_EXTENSION = prove
 (`!(h:A->B) k l.
        purely_inseparable_extension (k,l) h ==> field_extension (k,l) h`,
  SIMP_TAC[purely_inseparable_extension; ALGEBRAIC_IMP_FIELD_EXTENSION]);;

let PURELY_INSEPARABLE_OVER_SEPARABLE_CLOSURE = prove
 (`!(h:A->B) k l.
        algebraic_extension(k,l) h
        ==> purely_inseparable_extension
              (subfield_generated l (separable_closure (k,l) h),l) I`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    SUBFIELD_OF_SEPARABLE_CLOSURE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    SEPARABLE_EXTENSION_SEPARABLE_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = separable_closure (k,l) (h:A->B)` THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = subfield_generated l (s:B->bool)` THEN
  SUBGOAL_THEN `ring_carrier K = (s:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `field_extension(k,K) (h:A->B) /\ field_extension(K,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[SEPARABLE_IMP_FIELD_EXTENSION];
      EXPAND_TAC "K" THEN
      ASM_MESON_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; field_extension]];
    ALL_TAC] THEN
  REWRITE_TAC[purely_inseparable_extension; algebraic_extension; IMAGE_I] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_OVER_FIELD_EXTENSION THEN
    MAP_EVERY EXISTS_TAC [`h:A->B`; `k:A ring`] THEN
    ASM_REWRITE_TAC[I_O_ID] THEN ASM_MESON_TAC[algebraic_extension];
    ALL_TAC] THEN
  X_GEN_TAC `x:B` THEN REWRITE_TAC[IN_SEPARABLE_CLOSURE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`; `x:B`]
    SEPARABLE_EXTENSION_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEPARABLE_ELEMENT_IMP_ALGEBRAIC THEN
    ASM_MESON_TAC[field_extension];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN DISCH_TAC THEN
  ABBREV_TAC `L = subring_generated l ((x:B) INSERT s)` THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `L:B ring`]
    SEPARABLE_EXTENSION_TRANS) THEN
  ASM_REWRITE_TAC[I_O_ID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `separable_closure (k,l) (h:A->B) = s`)) THEN
  REWRITE_TAC[IN_SEPARABLE_CLOSURE] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `L:B ring`; `l:B ring`;
                 `x:B`] SEPARABLE_ELEMENT_MONOMORPHIC_IMAGE) THEN
  REWRITE_TAC[I_O_ID; I_THM] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM;
                 SEPARABLE_IMP_FIELD_EXTENSION] THEN
    EXPAND_TAC "L" THEN
    REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] RING_MONOMORPHISM_INCLUSION];
    DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[separable_extension]]);;

let PURELY_INSEPARABLE_EXTENSION_PERFECT = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h /\ perfect_field k
        ==> (purely_inseparable_extension(k,l) h <=>
             IMAGE h (ring_carrier k) = ring_carrier l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[purely_inseparable_extension; IN_SEPARABLE_CLOSURE] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_SUBSET] THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE_ELEMENT THEN
    ASM_MESON_TAC[algebraic_extension];
    DISCH_TAC THEN ASM_REWRITE_TAC[algebraic_extension] THEN
    REWRITE_TAC[TAUT `p /\ q ==> p`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[ALGEBRAIC_OVER_IMAGE]]);;

let PURELY_INSEPARABLE_EXTENSION_EQ_POW = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h /\ prime(ring_char k)
        ==> (purely_inseparable_extension(k,l) h <=>
             !x. x IN ring_carrier l
                 ==> ?n. ring_pow l x (ring_char k EXP n) IN
                         IMAGE h (ring_carrier k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[purely_inseparable_extension; IN_SEPARABLE_CLOSURE] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
      SEPARABLE_ELEMENT_POW_EXISTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_POW];
    DISCH_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[algebraic_extension] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `a:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`;
                   `ring_char(k:A ring) EXP n`] ALGEBRAIC_OVER_POW_EQ) THEN
    ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[ALGEBRAIC_OVER_IMAGE];
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    MATCH_MP_TAC SEPARABLE_ELEMENT_POW_IN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:B ring`; `n:num`] THEN ASM_REWRITE_TAC[]]);;

let PURELY_INSEPARABLE_EXTENSION_TRANS = prove
 (`!(f:A->B) (g:B->C) k l m.
        purely_inseparable_extension(k,l) f /\
        purely_inseparable_extension(l,m) g
        ==> purely_inseparable_extension(k,m) (g o f)`,
  REWRITE_TAC[purely_inseparable_extension; IN_SEPARABLE_CLOSURE] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[ALGEBRAIC_EXTENSION_TRANS]; ALL_TAC] THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION o
    check (fun th -> rand(concl th) = t)))
   [`f:A->B`; `g:B->C`] THEN
  SUBGOAL_THEN `x IN IMAGE (g:B->C) (ring_carrier l)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SEPARABLE_ELEMENT_INTERMEDIATE THEN
    MAP_EVERY EXISTS_TAC [`f:A->B`; `k:A ring`] THEN
    ASM_MESON_TAC[ALGEBRAIC_IMP_FIELD_EXTENSION];
    REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `y IN IMAGE (f:A->B) (ring_carrier k)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                   `y:B`] SEPARABLE_ELEMENT_MONOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_IMAGE; o_THM] THEN ASM_MESON_TAC[]]);;

let PURELY_INSEPARABLE_OVER_FROBENIUS_IMAGE = prove
 (`!l:A ring.
        field l /\ prime(ring_char l)
        ==> purely_inseparable_extension
              (subfield_generated l
                 {ring_pow l x (ring_char l) | x IN ring_carrier l},l) I`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `K = subfield_generated l
          {ring_pow l x (ring_char l) | x IN ring_carrier (l:A ring)}` THEN
  SUBGOAL_THEN `field_extension(K,l) (I:A->A)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN ASM_REWRITE_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:A->A`; `K:A ring`; `l:A ring`]
    PURELY_INSEPARABLE_EXTENSION_EQ_POW) THEN
  SUBGOAL_THEN `ring_char(K:A ring) = ring_char(l:A ring)` SUBST1_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[RING_CHAR_SUBFIELD_GENERATED]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[EXP_1] THEN EXPAND_TAC "K" THEN
  MATCH_MP_TAC(SET_RULE `!s t. s SUBSET t /\ (x:A) IN s ==> x IN t`) THEN
  EXISTS_TAC `ring_carrier l INTER
              {ring_pow l x (ring_char l) | x IN ring_carrier (l:A ring)}` THEN
  REWRITE_TAC[SUBFIELD_GENERATED_SUBSET_CARRIER; IN_INTER; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[RING_POW] THEN ASM_MESON_TAC[]);;

let PURELY_INSEPARABLE_EXTENSION_DEGREE = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h /\ purely_inseparable_extension(k,l) h
        ==> ?e. extension_degree(k,l) h = ring_char k EXP e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP INTEGRAL_DOMAIN_CHAR o
    MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN o
    check (fun th -> concl th = `field(k:A ring)`)) THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[EXP] THEN
    ASM_SIMP_TAC[EXTENSION_DEGREE_EQ_1] THEN
    ASM_MESON_TAC[PURELY_INSEPARABLE_EXTENSION_PERFECT; PERFECT_FIELD_CHAR_0];
    ALL_TAC] THEN
  ABBREV_TAC `c = ring_char(k:A ring)` THEN
  SUBGOAL_THEN
   `!d (K:B ring).
        finite_extension(K,l) I /\ ring_char K = c /\
        (!x. x IN ring_carrier l
             ==> ?n. ring_pow l x (c EXP n) IN ring_carrier K) /\
        extension_degree(K,l) I = d
        ==> ?e. d = c EXP e`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL
     [`extension_degree(k,l) (h:A->B)`;
      `subfield_generated l (IMAGE (h:A->B) (ring_carrier k))`]) THEN
    REWRITE_TAC[EQ_SYM_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
      RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP CARRIER_SUBFIELD_GENERATED_SUBFIELD) THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                     `IMAGE (h:A->B) (ring_carrier k)`]
        FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
      ASM_SIMP_TAC[SUBSET_REFL];
      REWRITE_TAC[RING_CHAR_SUBFIELD_GENERATED] THEN
      EXPAND_TAC "c" THEN ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
        PURELY_INSEPARABLE_EXTENSION_EQ_POW) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXTENSION_DEGREE_EQ_IMAGE THEN
      ASM_REWRITE_TAC[IMAGE_I]]] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `K:B ring` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_SUBSET_I) THEN
  ASM_CASES_TAC `ring_carrier K:B->bool = ring_carrier l` THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[EXP] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rand(concl th) = `d:num`)) THEN
    ASM_SIMP_TAC[EXTENSION_DEGREE_EQ_1; IMAGE_I];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:B. z IN ring_carrier l /\ ~(z IN ring_carrier K)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `s SUBSET t /\ ~(s = t) ==> ?z:B. z IN t /\ ~(z IN s)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. ring_pow l (z:B) (c EXP n) IN ring_carrier K` MP_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "min"))) THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~((z:B) IN ring_carrier K)` THEN
    UNDISCH_TAC `ring_pow l (z:B) (c EXP 0) IN ring_carrier K` THEN
    ASM_SIMP_TAC[EXP; RING_POW_1];
    ALL_TAC] THEN
  ABBREV_TAC `x = ring_pow l (z:B) (c EXP (m - 1))` THEN
  SUBGOAL_THEN
   `(x:B) IN ring_carrier l /\ ~(x IN ring_carrier K) /\
    ring_pow l x c IN ring_carrier K`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[RING_POW; ASSUME `(z:B) IN ring_carrier l`];
      REMOVE_THEN "min" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[MATCH_MP RING_POW_POW (ASSUME `(z:B) IN ring_carrier l`)] THEN
      SUBGOAL_THEN `c EXP (m - 1) * c = c EXP m` SUBST1_TAC THENL
       [SUBGOAL_THEN `m = SUC(m - 1)`
         (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
         [ASM_ARITH_TAC; REWRITE_TAC[EXP; MULT_SYM]];
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over(K,l) (I:B->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION; algebraic_extension];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL_DEG_EQ_CHAR) THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`; `x:B`]
    EXTENSION_DEGREE_SIMPLE) THEN
  MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`; `x:B`]
    FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`; `x:B`]
    FIELD_SIMPLE_ALGEBRAIC_EXTENSION) THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN
  ABBREV_TAC `K1 = subring_generated l ((x:B) INSERT ring_carrier K)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `field_extension(K1,l) (I:B->B)` ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN
    MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
    ASM_REWRITE_TAC[FIELD_EXTENSION_REFL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
   [`I:B->B`; `I:B->B`; `K:B ring`; `K1:B ring`; `l:B ring`]
   EXTENSION_DEGREE_TOWER_LAW)) THEN
  MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
   [`I:B->B`; `I:B->B`; `K:B ring`; `K1:B ring`; `l:B ring`]
   FINITE_EXTENSION_TRANS_EQ)) THEN
  ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION] THEN DISCH_TAC THEN
  DISCH_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `extension_degree(K1,l) (I:B->B)`) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      lhand(concl th) = `d:num`)) THEN
    SUBGOAL_THEN `~(extension_degree(K1,l) (I:B->B) = 0)` MP_TAC THENL
     [ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    SPEC_TAC(`extension_degree(K1,l) (I:B->B)`,`e:num`) THEN
    GEN_TAC THEN
    SUBST1_TAC(ARITH_RULE `e < c * e <=> 1 * e < c * e`) THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `K1:B ring`)] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "K1" THEN REWRITE_TAC[RING_CHAR_SUBRING_GENERATED] THEN
      ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE; field_extension];
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:B` o check (fun th ->
        is_forall(concl th) && free_in `K:B ring` (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:B) IN s ==> x IN t`) THEN
      MATCH_MP_TAC FIELD_EXTENSION_IMP_SUBSET_I THEN
      ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION]];
    DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST1_TAC) THEN
    EXISTS_TAC `SUC e` THEN REWRITE_TAC[EXP]]);;

let SEPARABLE_DEGREE_EQ_1 = prove
 (`!(h:A->B) k l.
        algebraic_extension(k,l) h
        ==> (separable_degree(k,l) h = 1 <=>
             purely_inseparable_extension(k,l) h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    ASM_REWRITE_TAC[purely_inseparable_extension; IN_SEPARABLE_CLOSURE] THEN
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
     [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
      MINIMAL_POLYNOMIAL_DEG_EQ_1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
      EXTENSION_DEGREE_SIMPLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
      SEPARABLE_EXTENSION_SIMPLE) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
      FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
      FIELD_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC
     `K = subring_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `field_extension(K,l) (I:B->B)` ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN
      MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
      ASM_REWRITE_TAC[FIELD_EXTENSION_REFL] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
     [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
     SEPARABLE_DEGREE_TOWER)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION] THEN
      MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
       [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
       ALGEBRAIC_EXTENSION_TRANS_EQ)) THEN
      ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE] THEN
    DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[MULT_EQ_1] THEN
    SUBGOAL_THEN `separable_degree(k,K) (h:A->B) = extension_degree(k,K) h`
    (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE];
      SIMP_TAC[MULT_CLAUSES]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:(A#num)ring`; `g:A->A#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION o
    check (fun th -> rand(concl th) = `g:A->A#num`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> rand(concl th) = `g:A->A#num`)) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `l:B ring`;
                 `m:(A#num)ring`] SEPARABLE_DEGREE) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `l:B ring`;
                 `m:(A#num)ring`] RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  ABBREV_TAC
   `E = ring_homomorphism_extensions (k,l,m) (h:A->B,g:A->A#num)` THEN
  DISCH_THEN(X_CHOOSE_TAC `s0:B->A#num`) THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `E = {s0:B->A#num}`
   (fun th -> REWRITE_TAC[th; FINITE_SING; CARD_SING]) THEN
  MATCH_MP_TAC(SET_RULE
   `(a:B->A#num) IN s /\ (!x y. x IN s /\ y IN s ==> x = y) ==> s = {a}`) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:B->A#num`; `t:B->A#num`] THEN
  EXPAND_TAC "E" THEN
  REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP INTEGRAL_DOMAIN_CHAR o
    MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN o
    check (fun th -> concl th = `field(k:A ring)`)) THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
      PURELY_INSEPARABLE_EXTENSION_PERFECT) THEN
    ASM_SIMP_TAC[PERFECT_FIELD_CHAR_0] THEN
    DISCH_THEN(MP_TAC o SPEC `x:B` o REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    PURELY_INSEPARABLE_EXTENSION_EQ_POW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:B`) THEN
  ASM_REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `a:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(A#num)ring`; `n:num`]
    RING_MONOMORPHISM_FROBENIUS_ITERATE) THEN
  SUBGOAL_THEN `ring_char(m:(A#num)ring) = ring_char(k:A ring)`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  DISCH_THEN(MP_TAC o SPECL [`(s:B->A#num) x`; `(t:B->A#num) x`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] RING_MONOMORPHISM_INJECTIVE_EQ)) THEN
  SUBGOAL_THEN
   `(s:B->A#num) x IN ring_carrier m /\ (t:B->A#num) x IN ring_carrier m`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`l:B ring`; `m:(A#num)ring`; `s:B->A#num`]
    RING_HOMOMORPHISM_POW) THEN
  MP_TAC(ISPECL [`l:B ring`; `m:(A#num)ring`; `t:B->A#num`]
    RING_HOMOMORPHISM_POW) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
    (ASSUME `(x:B) IN ring_carrier l`))])) THEN
  ASM_SIMP_TAC[]);;

let SEPARABLE_DEGREE_SEPARABLE_CLOSURE = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h
        ==> separable_degree(k,l) h =
            extension_degree
             (k,subfield_generated l (separable_closure (k,l) h)) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    SUBFIELD_OF_SEPARABLE_CLOSURE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    SEPARABLE_EXTENSION_SEPARABLE_CLOSURE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    PURELY_INSEPARABLE_OVER_SEPARABLE_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = separable_closure (k,l) (h:A->B)` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
    FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = subfield_generated l (s:B->bool)` THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
   [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
   SEPARABLE_DEGREE_TOWER)) THEN
  ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `separable_degree(K,l) (I:B->B) = 1` SUBST1_TAC THENL
   [ASM_MESON_TAC[SEPARABLE_DEGREE_EQ_1;
                  PURELY_INSEPARABLE_IMP_ALGEBRAIC_EXTENSION];
    REWRITE_TAC[MULT_CLAUSES]] THEN
  ASM_MESON_TAC[SEPARABLE_DEGREE_EQ_EXTENSION_DEGREE]);;

(* The inseparable degree.                                                   *)

let inseparable_degree = new_definition
 `inseparable_degree (k:A ring,l:B ring) (h:A->B) =
        extension_degree
         (subfield_generated l (separable_closure (k,l) h),l) I`;;

let EXTENSION_DEGREE_SEPARABLE_INSEPARABLE = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h
        ==> extension_degree(k,l) h =
            separable_degree(k,l) h * inseparable_degree(k,l) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  ASM_SIMP_TAC[SEPARABLE_DEGREE_SEPARABLE_CLOSURE; inseparable_degree] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    SUBFIELD_OF_SEPARABLE_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = separable_closure (k,l) (h:A->B)` THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[I_O_ID] (ISPECL
   [`h:A->B`; `I:B->B`; `k:A ring`; `subfield_generated l (s:B->bool)`;
    `l:B ring`] EXTENSION_DEGREE_TOWER_LAW)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_INTO_SUBFIELD_GENERATED] THEN
  ASM_MESON_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; field_extension]);;

let INSEPARABLE_DEGREE_EQ_1 = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h
        ==> (inseparable_degree(k,l) h = 1 <=> separable_extension(k,l) h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    SUBFIELD_OF_SEPARABLE_CLOSURE) THEN
  ASM_SIMP_TAC[inseparable_degree;
               SEPARABLE_EXTENSION_EQ_SEPARABLE_CLOSURE] THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EXTENSION_DEGREE_EQ_1 o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; field_extension];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[IMAGE_I; CARRIER_SUBFIELD_GENERATED_SUBFIELD]);;

let INSEPARABLE_DEGREE_CHAR_POWER = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h
        ==> ?e. inseparable_degree(k,l) h = ring_char k EXP e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inseparable_degree] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    SUBFIELD_OF_SEPARABLE_CLOSURE) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    PURELY_INSEPARABLE_OVER_SEPARABLE_CLOSURE) THEN
  ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION] THEN
  ABBREV_TAC `s = separable_closure (k,l) (h:A->B)` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`I:B->B`; `subfield_generated l (s:B->bool)`; `l:B ring`]
    PURELY_INSEPARABLE_EXTENSION_DEGREE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
      FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[RING_CHAR_SUBFIELD_GENERATED] THEN
    ASM_MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE; field_extension]]);;

let INSEPARABLE_DEGREE_TOWER =
  let lemma = prove
   (`!i bs bi cs ci:num.
        ~((bs * cs) * i = 0) /\ (bs * cs) * i = (bs * bi) * (cs * ci)
        ==> i = bi * ci`,
    REPEAT GEN_TAC THEN
    SUBST1_TAC(ARITH_RULE
     `(bs * bi) * (cs * ci) = (bs * cs) * (bi * ci):num`) THEN
    REWRITE_TAC[EQ_MULT_LCANCEL; MULT_EQ_0] THEN CONV_TAC TAUT) in
  prove
   (`!(f:A->B) (g:B->C) k l m.
        finite_extension(k,l) f /\ finite_extension(l,m) g
        ==> inseparable_degree(k,m) (g o f) =
            inseparable_degree(k,l) f * inseparable_degree(l,m) g`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `finite_extension(k,m) ((g:B->C) o (f:A->B))`
    ASSUME_TAC THENL [ASM_MESON_TAC[FINITE_EXTENSION_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
      EXTENSION_DEGREE_TOWER_LAW) THEN
    MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
      SEPARABLE_DEGREE_TOWER) THEN
    ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION; FINITE_IMP_FIELD_EXTENSION;
                 EXTENSION_DEGREE_SEPARABLE_INSEPARABLE] THEN
    SUBGOAL_THEN `~(extension_degree(k,m) ((g:B->C) o (f:A->B)) = 0)` MP_TAC
    THENL
     [ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0; FINITE_IMP_FIELD_EXTENSION];
      ASM_SIMP_TAC[EXTENSION_DEGREE_SEPARABLE_INSEPARABLE]] THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC lemma THEN
    MAP_EVERY EXISTS_TAC [`separable_degree(k,l) (f:A->B)`;
                          `separable_degree(l,m) (g:B->C)`] THEN
    ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Norm and trace of a field extension: algebra_trace and algebra_norm of    *)
(* Library/ring_det.ml, the trace and the determinant of the matrix of       *)
(* multiplication in a free basis. Over a field the free bases are the       *)
(* injective enumerations of the bases in the sense of ring_basis            *)
(* (FREE_BASIS_FIELD, via FREE_BASIS_SPANNING_EQ and                         *)
(* FREE_BASIS_INDEPENDENT_EQ), so a finite extension has a free basis of     *)
(* size [l:k] (FINITE_EXTENSION_FREE_BASIS), every free basis has that size  *)
(* (FREE_BASIS_EXTENSION_DEGREE), and n spanning elements of an extension of *)
(* degree n are a free basis (FREE_BASIS_SPANNING_DEGREE). Over a field a    *)
(* finite projective basis exists exactly when a finite free basis does      *)
(* (PROJECTIVE_BASIS_EXISTS_FIELD), so an infinite extension has neither     *)
(* (PROJECTIVE_BASIS_IMP_FINITE_EXTENSION), and there the trace and the norm *)
(* are the constants 0 and 1.                                                *)
(* ------------------------------------------------------------------------- *)

let FREE_BASIS_SPANNING_EQ = prove
 (`!(h:A->B) k l n (g:num->B).
        ring_homomorphism(k,l) h /\
        (!i. i < n ==> g i IN ring_carrier l) /\
        (!i j. i < n /\ j < n /\ g i = g j ==> i = j)
        ==> (ring_spanning (k,l) h (IMAGE g {i | i < n}) <=>
             !x. x IN ring_carrier l
                 ==> ?c. (!i. i < n ==> c i IN ring_carrier k) /\
                         x = ring_sum l {i | i < n}
                               (\i. ring_mul l (h(c i)) (g i)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (g:num->B) {i:num | i < n} SUBSET ring_carrier l`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ring_spanning; GSYM SUBSET_ANTISYM_EQ;
                  RING_SPAN_SUBSET] THEN
  REWRITE_TAC[SUBSET] THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `IMAGE (g:num->B) {i:num | i < n}`] RING_SPAN_FINITE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP FREE_BASIS_RING_SUM_IMAGE th]) THEN
  REWRITE_TAC[IN_ELIM_THM; FORALL_IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:B->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\i. (c:B->A)((g:num->B) i)` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC)] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ginv:B->num` o GEN_REWRITE_RULE I
   [REWRITE_RULE[IN_ELIM_THM] (ISPECL [`g:num->B`; `{i:num | i < n}`]
      INJECTIVE_ON_LEFT_INVERSE)]) THEN
  EXISTS_TAC `\y:B. (c:num->A)(ginv y)` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let FREE_BASIS_INDEPENDENT_EQ = prove
 (`!(h:A->B) k l n (g:num->B).
        field k /\ ring_homomorphism(k,l) h /\
        (!i. i < n ==> g i IN ring_carrier l) /\
        (!i j. i < n /\ j < n /\ g i = g j ==> i = j)
        ==> (ring_independent (k,l) h (IMAGE g {i | i < n}) <=>
             !c. (!i. i < n ==> c i IN ring_carrier k) /\
                 ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (g i)) =
                 ring_0 l
                 ==> !i. i < n ==> c i = ring_0 k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `IMAGE (g:num->B) {i:num | i < n}`]
    RING_INDEPENDENT_FINITE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP FREE_BASIS_RING_SUM_IMAGE th]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ginv:B->num` o GEN_REWRITE_RULE I
   [REWRITE_RULE[IN_ELIM_THM] (ISPECL [`g:num->B`; `{i:num | i < n}`]
      INJECTIVE_ON_LEFT_INVERSE)]) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `c:num->A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\y:B. (c:num->A)(ginv y)`) THEN
    SUBGOAL_THEN
     `ring_sum l {i:num | i < n}
        (\i. ring_mul l ((h:A->B)(c(ginv((g:num->B) i)))) (g i)) =
      ring_sum l {i | i < n} (\i. ring_mul l (h((c:num->A) i)) (g i))`
    MP_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
      ASM_SIMP_TAC[]];
    X_GEN_TAC `c:B->A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i. (c:B->A)((g:num->B) i)`) THEN
    ASM_REWRITE_TAC[]]);;

let FREE_BASIS_FIELD = prove
 (`!(h:A->B) k l n g.
        field k /\ ring_homomorphism(k,l) h
        ==> (free_basis (k,l) h n g <=>
             ring_basis (k,l) h (IMAGE g {i | i < n}) /\
             (!i j. i < n /\ j < n /\ g i = g j ==> i = j))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!i j. i < n /\ j < n /\ (g:num->B) i = g j ==> i = j` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                   `i:num`; `i:num`] BASIS_COORDINATES_BASIS) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`;
                   `i:num`; `j:num`] BASIS_COORDINATES_BASIS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FIELD_NONTRIVIAL]] THEN
  ASM_CASES_TAC `!i. i < n ==> (g:num->B) i IN ring_carrier l` THENL
   [REWRITE_TAC[ring_basis; free_basis] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
      FREE_BASIS_SPANNING_EQ) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
      FREE_BASIS_INDEPENDENT_EQ) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    CONV_TAC TAUT;
    ASM_REWRITE_TAC[free_basis; ring_basis; ring_independent; SUBSET;
                    FORALL_IN_IMAGE; IN_ELIM_THM]]);;

let FREE_BASIS_SIMPLE_EXTENSION = prove
 (`!(k:A ring) (l:B ring) h x.
        field_extension(k,l) h /\ algebraic_over (k,l) h x
        ==> free_basis
             (k,subring_generated l (x INSERT IMAGE h (ring_carrier k))) h
             (poly_deg k (minimal_polynomial (k,l) h x)) (ring_pow l x)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) FREE_BASIS_FIELD o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FINITE_SIMPLE_ALGEBRAIC_EXTENSION;
                  FINITE_IMP_FIELD_EXTENSION;
                  FIELD_EXTENSION_IMP_HOMOMORPHISM; field_extension];
    DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (ring_pow l (x:B))
            {i | i < poly_deg k (minimal_polynomial (k,l) (h:A->B) x)} =
      {ring_pow l x n | n | n < poly_deg k (minimal_polynomial (k,l) h x)}`
    SUBST1_TAC THENL
     [SET_TAC[]; ASM_SIMP_TAC[RING_SIMPLE_ALGEBRAIC_EXTENSION_BASIS]];
    ASM_MESON_TAC[POWER_INJECTIVE_BELOW_MINPOLY_DEG]]);;

let FREE_BASIS_EXTENSION_DEGREE = prove
 (`!(h:A->B) k l n g.
        field k /\ ring_homomorphism(k,l) h /\ free_basis (k,l) h n g
        ==> n = extension_degree (k,l) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
    FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `IMAGE (g:num->B) {i:num | i < n}`]
    EXTENSION_DEGREE_EQ_CARD_BASIS) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS `CARD {i:num | i < n}` THEN CONJ_TAC THENL
   [REWRITE_TAC[CARD_NUMSEG_LT];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]]);;

(* Over a field, n spanning elements of an extension of degree n form a free *)
(* basis.                                                                    *)
let FREE_BASIS_SPANNING_DEGREE = prove
 (`!(h:A->B) k l n g.
        field k /\ ring_homomorphism(k,l) h /\
        extension_degree (k,l) h = n /\
        (!i. i < n ==> g i IN ring_carrier l) /\
        (!x. x IN ring_carrier l
             ==> ?c. (!i. i < n ==> c i IN ring_carrier k) /\
                     x = ring_sum l {i | i < n}
                           (\i. ring_mul l (h(c i)) (g i)))
        ==> free_basis (k,l) h n g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_spanning (k,l) (h:A->B) (IMAGE (g:num->B) {i | i < n})`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_SPANNING_ALT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_SPAN_SUM THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC RING_SPAN_MUL THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
      MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  MP_TAC(INST [`IMAGE (g:num->B) {i | i < n}`,`b:B->bool`]
   (ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
     RING_SPANNING_CONTAINS_BASIS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:B->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `FINITE(IMAGE (g:num->B) {i | i < n}) /\
    CARD(IMAGE (g:num->B) {i | i < n}) <= n`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    MESON_TAC[CARD_IMAGE_LE; FINITE_NUMSEG_LT; CARD_NUMSEG_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `c:B->bool`]
    EXTENSION_DEGREE_EQ_CARD_BASIS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; DISCH_TAC] THEN
  SUBGOAL_THEN `c = IMAGE (g:num->B) {i | i < n}` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_LE THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[FREE_BASIS_FIELD] THEN
  MP_TAC(ISPECL [`g:num->B`; `{i:num | i < n}`] CARD_IMAGE_EQ_INJ) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_ARITH_TAC);;

let FREE_BASIS_FROM_RING_BASIS = prove
 (`!k:A ring l:B ring h b.
        field k /\ ring_homomorphism(k,l) h /\ ring_basis (k,l) h b /\ FINITE b
        ==> ?g. free_basis (k,l) h (CARD b) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:B->bool`; `CARD(b:B->bool)`] HAS_SIZE_INDEX) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:num->B` THEN ASM_SIMP_TAC[FREE_BASIS_FIELD] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `IMAGE (g:num->B) {i | i < CARD(b:B->bool)} = b`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let FREE_BASIS_EXISTS = prove
 (`!k:A ring l:B ring h s.
        field k /\ ring_homomorphism(k,l) h /\
        FINITE s /\ ring_spanning (k,l) h s
        ==> ?g. free_basis (k,l) h (extension_degree (k,l) h) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`s:B->bool`,`b:B->bool`]
   (ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
     RING_SPANNING_CONTAINS_BASIS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE(b:B->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B->bool`]
    EXTENSION_DEGREE_EQ_CARD_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC FREE_BASIS_FROM_RING_BASIS THEN ASM_REWRITE_TAC[]);;

let FINITE_EXTENSION_FREE_BASIS = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h
        ==> ?g. free_basis (k,l) h (extension_degree(k,l) h) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FINITE_EXTENSION_BASIS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC FREE_BASIS_EXISTS THEN EXISTS_TAC `b:B->bool` THEN
  ASM_MESON_TAC[field_extension; ring_monomorphism; ring_basis]);;

let FREE_BASIS_IMP_FINITE_EXTENSION = prove
 (`!(h:A->B) k l n g.
        field_extension(k,l) h /\ free_basis (k,l) h n g
        ==> finite_extension(k,l) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `g:num->B`]
    FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `IMAGE (g:num->B) {i:num | i < n}`] FINITE_EXTENSION_ANY) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT]);;

let FREE_BASIS_IMP_ALGEBRAIC = prove
 (`!k (l:B ring) (h:A->B) n g x.
        field_extension(k,l) h /\ free_basis (k,l) h n g /\
        x IN ring_carrier l
        ==> algebraic_over (k,l) h x`,
  MESON_TAC[FREE_BASIS_IMP_FINITE_EXTENSION; FINITE_IMP_ALGEBRAIC_EXTENSION;
            algebraic_extension]);;

(* Over a field a finite projective basis exists exactly when a finite free  *)
(* basis does.                                                               *)
let PROJECTIVE_BASIS_EXISTS_FIELD = prove
 (`!(h:A->B) k l.
        field k /\ ring_homomorphism(k,l) h
        ==> ((?n e f. projective_basis (k,l) h n e f) <=>
             (?n g. free_basis (k,l) h n g))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `e:num->B`; `f:num->B->A`] THEN
    DISCH_TAC THEN EXISTS_TAC `extension_degree (k,l) (h:A->B)` THEN
    MATCH_MP_TAC FREE_BASIS_EXISTS THEN
    EXISTS_TAC `IMAGE (e:num->B) {i:num | i < n}` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PROJECTIVE_BASIS_IN_CARRIER) THEN
    ASM_SIMP_TAC[RING_SPANNING_ALT; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `e:num->B`;
                   `f:num->B->A`; `x:B`] PROJECTIVE_BASIS_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_SPAN_SUM THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC RING_SPAN_MUL THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
      MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ASM_MESON_TAC[FREE_BASIS_PROJECTIVE]]);;

let PROJECTIVE_BASIS_IMP_FINITE_EXTENSION = prove
 (`!(h:A->B) k l n e f.
        field_extension(k,l) h /\ projective_basis (k,l) h n e f
        ==> finite_extension(k,l) h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    PROJECTIVE_BASIS_EXISTS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[FREE_BASIS_IMP_FINITE_EXTENSION]]);;

(* ------------------------------------------------------------------------- *)
(* The trace and the norm of elements of the base field, and the norm        *)
(* vanishes only at 0.                                                       *)
(* ------------------------------------------------------------------------- *)

let ALGEBRA_TRACE_NORM_BASE = prove
 (`!(h:A->B) k l a.
        field_extension(k,l) h /\ a IN ring_carrier k
        ==> algebra_trace(k,l) h (h a) =
            ring_mul k (ring_of_num k (extension_degree(k,l) h)) a /\
            algebra_norm(k,l) h (h a) = ring_pow k a (extension_degree(k,l) h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  ASM_CASES_TAC `finite_extension(k,l) (h:A->B)` THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `g:num->B` o
      MATCH_MP FINITE_EXTENSION_FREE_BASIS) THEN
    MATCH_MP_TAC ALGEBRA_TRACE_NORM_BASE_FREE_BASIS THEN
    EXISTS_TAC `g:num->B` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(?n e f. projective_basis (k,l) (h:A->B) n e f)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[PROJECTIVE_BASIS_IMP_FINITE_EXTENSION]; ALL_TAC] THEN
    SUBGOAL_THEN `extension_degree(k,l) (h:A->B) = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0]; ALL_TAC] THEN
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS; ring_pow;
                 RING_OF_NUM_0; RING_MUL_LZERO]]);;

let ALGEBRA_NORM_EQ_0 = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ x IN ring_carrier l
        ==> (algebra_norm(k,l) h x = ring_0 k <=> x = ring_0 l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:num->B` o
    MATCH_MP FINITE_EXTENSION_FREE_BASIS) THEN
  MATCH_MP_TAC ALGEBRA_NORM_EQ_0_FREE_BASIS THEN
  MAP_EVERY EXISTS_TAC [`extension_degree(k,l) (h:A->B)`; `g:num->B`] THEN
  ASM_SIMP_TAC[LT_NZ; EXTENSION_DEGREE_EQ_0] THEN
  ASM_MESON_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* Elements of an intermediate field: in the product basis of a tower k, l,  *)
(* m the matrix of g(y), y in l, is the Kronecker product of the matrix of y *)
(* over k with the identity of size [m:l]; for infinite extensions both      *)
(* sides are the constants.                                                  *)
(* ------------------------------------------------------------------------- *)

let ALGEBRA_TRACE_NORM_INTERMEDIATE = prove
 (`!(f:A->B) (g:B->C) k l m y.
        field_extension(k,l) f /\ field_extension(l,m) g /\
        y IN ring_carrier l
        ==> algebra_trace(k,m) (g o f) (g y) =
            ring_mul k (ring_of_num k (extension_degree(l,m) g))
                       (algebra_trace(k,l) f y) /\
            algebra_norm(k,m) (g o f) (g y) =
            ring_pow k (algebra_norm(k,l) f y) (extension_degree(l,m) g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(k,l) (f:A->B) /\ ring_homomorphism(l,m) (g:B->C) /\
    field_extension(k,m) (g o f)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM; FIELD_EXTENSION_TRANS];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `finite_extension(k,l) (f:A->B) /\ finite_extension(l,m) (g:B->C)` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `b:num->B` o MATCH_MP FINITE_EXTENSION_FREE_BASIS)
     (X_CHOOSE_TAC `c:num->C` o MATCH_MP FINITE_EXTENSION_FREE_BASIS)) THEN
    MATCH_MP_TAC ALGEBRA_TRACE_NORM_INTERMEDIATE_FREE_BASIS THEN
    MAP_EVERY EXISTS_TAC
     [`extension_degree(k,l) (f:A->B)`; `b:num->B`; `c:num->C`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(?n d e. projective_basis (k,m) ((g:B->C) o (f:A->B)) n d e)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[PROJECTIVE_BASIS_IMP_FINITE_EXTENSION;
                  FINITE_EXTENSION_TRANS_EQ];
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS]] THEN
  ASM_CASES_TAC `finite_extension(k,l) (f:A->B)` THENL
   [SUBGOAL_THEN `extension_degree(l,m) (g:B->C) = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0]; ALL_TAC] THEN
    SIMP_TAC[ring_pow; RING_OF_NUM_0; RING_MUL_LZERO;
             ALGEBRA_TRACE_NORM_IN_CARRIER];
    SUBGOAL_THEN `~(?n b e. projective_basis (k,l) (f:A->B) n b e)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[PROJECTIVE_BASIS_IMP_FINITE_EXTENSION]; ALL_TAC] THEN
    ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS; RING_MUL_RZERO;
                 RING_OF_NUM; RING_POW_ONE]]);;

let FIELD_CHARPOLY_INTERMEDIATE = prove
 (`!(f:A->B) (g:B->C) k l m p b n d y.
        finite_extension(k,l) f /\ finite_extension(l,m) g /\
        free_basis (k,l) f p b /\ free_basis (k,m) (g o f) n d /\
        y IN ring_carrier l
        ==> ring_charpoly k {i | i < n} (mul_matrix (k,m) (g o f) n d (g y)) =
            poly_pow k (ring_charpoly k {i | i < p} (mul_matrix (k,l) f p b y))
                     (extension_degree(l,m) g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(k,l) (f:A->B) /\ ring_homomorphism(l,m) (g:B->C)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM;
                  FINITE_IMP_FIELD_EXTENSION];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(k,m) ((g:B->C) o (f:A->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `c:num->C` o MATCH_MP FINITE_EXTENSION_FREE_BASIS o
    check (fun th -> concl th = `finite_extension(l,m) (g:B->C)`)) THEN
  ABBREV_TAC `q = extension_degree(l,m) (g:B->C)` THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `p:num`; `q:num`; `b:num->B`; `c:num->C`]
    FREE_BASIS_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `k:A ring`; `m:C ring`; `(p:num) * q`;
                 `n:num`;
                 `\t. ring_mul m ((g:B->C)(b(t MOD p))) ((c:num->C)(t DIV p))`;
                 `d:num->C`; `(g:B->C) y`] MUL_MATRIX_CHARPOLY_BASIS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MUL_MATRIX_CHARPOLY_INTERMEDIATE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The characteristic polynomial of the multiplication by x has x as a root  *)
(* (MUL_MATRIX_CHARPOLY_ROOT); on k(x) it is the minimal polynomial p, and   *)
(* on l it is p^[l:k(x)]. The coefficients of p give the trace and the norm  *)
(* of x over k(x) (RING_CHARPOLY_COEFF_TRACE, RING_CHARPOLY_COEFF_0), and    *)
(* the intermediate field formula the general case.                          *)
(* ------------------------------------------------------------------------- *)

let FIELD_CHARPOLY_SIMPLE = prove
 (`!(h:A->B) k l x n c.
        field_extension(k,l) h /\ algebraic_over(k,l) h x /\
        free_basis (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)))
                   h n c
        ==> ring_charpoly k {i | i < n}
              (mul_matrix
                (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)))
                h n c x) =
            minimal_polynomial(k,l) h x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `K = subfield_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  SUBGOAL_THEN
   `subring_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k)) = K`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBRING_EQ_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[FIELD_SIMPLE_ALGEBRAIC_EXTENSION];
    ALL_TAC] THEN
  SUBGOAL_THEN `finite_extension(k,K) (h:A->B)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[FINITE_SIMPLE_ALGEBRAIC_EXTENSION];
    ALL_TAC] THEN
  SUBGOAL_THEN `field_extension(k,K) (h:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_FIELD_EXTENSION]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(k,K) (h:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBRING_GENERATED_INC_GEN THEN
    ASM_MESON_TAC[IN_INSERT; ALGEBRAIC_OVER_IN_CARRIER];
    ALL_TAC] THEN
  ABBREV_TAC
   `q = ring_charpoly k {i:num | i < n} (mul_matrix (k,K) (h:A->B) n c x)` THEN
  SUBGOAL_THEN `q IN ring_carrier(poly_ring (k:A ring) (:1))` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[RING_CHARPOLY]; ALL_TAC] THEN
  SUBGOAL_THEN `poly_extend (k,l) (h:A->B) (\v:1. x) (q:(1->num)->A) = ring_0 l`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`; `n:num`; `c:num->B`;
                   `x:B`] MUL_MATRIX_CHARPOLY_ROOT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ring_0 K = ring_0 (l:B ring)` SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[SUBRING_GENERATED]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`;
                   `x INSERT IMAGE (h:A->B) (ring_carrier k)`; `h:A->B`;
                   `(:1)`; `\v:1. (x:B)`; `q:(1->num)->A`]
      POLY_EXTEND_INTO_SUBRING_GENERATED) THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    check (fun th -> concl th = `field_extension(k:A ring,l:B ring) h`)) THEN
  SUBGOAL_THEN `extension_degree(k,K) (h:A->B) = n` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FREE_BASIS_EXTENSION_DEGREE THEN
    EXISTS_TAC `c:num->B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    EXTENSION_DEGREE_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`;
    `mul_matrix (k,K) (h:A->B) n c x`] RING_CHARPOLY_MONIC) THEN
  ASM_SIMP_TAC[FIELD_NONTRIVIAL; FINITE_NUMSEG_LT; IN_ELIM_THM;
               MUL_MATRIX_IN_CARRIER; CARD_NUMSEG_LT] THEN
  STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MONIC_DIVIDES_EQ THEN
  EXISTS_TAC `k:A ring` THEN
  ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_MONIC; MINIMAL_POLYNOMIAL_DIVIDES] THEN
  ASM_MESON_TAC[LE_REFL]);;

let FIELD_CHARPOLY_MINIMAL_POLYNOMIAL = prove
 (`!(h:A->B) k l n g x.
        finite_extension(k,l) h /\ free_basis (k,l) h n g /\
        x IN ring_carrier l
        ==> ring_charpoly k {i | i < n} (mul_matrix (k,l) h n g x) =
            poly_pow k (minimal_polynomial(k,l) h x)
             (extension_degree
               (subfield_generated l (x INSERT IMAGE h (ring_carrier k)),l)
               I)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION; algebraic_extension];
    ALL_TAC] THEN
  ABBREV_TAC
   `K = subfield_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `x INSERT IMAGE (h:A->B) (ring_carrier k)`]
    FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `c:num->B` o MATCH_MP FINITE_EXTENSION_FREE_BASIS o
    check (fun th -> concl th = `finite_extension(k,K) (h:A->B)`)) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`;
                 `extension_degree(k,K) (h:A->B)`; `c:num->B`; `n:num`;
                 `g:num->B`; `x:B`]
    FIELD_CHARPOLY_INTERMEDIATE) THEN
  ASM_REWRITE_TAC[I_O_ID; I_THM] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "K" THEN
  MATCH_MP_TAC FIELD_CHARPOLY_SIMPLE THEN ASM_REWRITE_TAC[]);;

let ALGEBRA_TRACE_NORM_SIMPLE = prove
 (`!(h:A->B) k l x.
        field_extension(k,l) h /\ algebraic_over(k,l) h x
        ==> algebra_trace
             (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k))) h x =
            ring_neg k (coeff (poly_deg k (minimal_polynomial(k,l) h x) - 1)
                              (minimal_polynomial(k,l) h x)) /\
            algebra_norm
             (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k))) h x =
            ring_mul k
             (ring_pow k (ring_neg k (ring_1 k))
                (poly_deg k (minimal_polynomial(k,l) h x)))
             (coeff 0 (minimal_polynomial(k,l) h x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `K = subfield_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  SUBGOAL_THEN `finite_extension(k,K) (h:A->B)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    SUBGOAL_THEN
     `subfield_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k)) =
      subring_generated l (x INSERT IMAGE h (ring_carrier k))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUBRING_EQ_SUBFIELD_GENERATED THEN
      ASM_SIMP_TAC[FIELD_SIMPLE_ALGEBRAIC_EXTENSION];
      ASM_SIMP_TAC[FINITE_SIMPLE_ALGEBRAIC_EXTENSION]];
    ALL_TAC] THEN
  SUBGOAL_THEN `field_extension(k,K) (h:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_FIELD_EXTENSION]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(k,K) (h:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `c:num->B` o MATCH_MP FINITE_EXTENSION_FREE_BASIS o
    check (fun th -> concl th = `finite_extension(k,K) (h:A->B)`)) THEN
  ABBREV_TAC `n = extension_degree(k,K) (h:A->B)` THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    ASM_MESON_TAC[IN_INSERT; ALGEBRAIC_OVER_IN_CARRIER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`; `n:num`; `c:num->B`]
    FIELD_CHARPOLY_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ISPECL [`h:A->B`; `k:A ring`; `K:B ring`; `n:num`; `c:num->B`]
                 ALGEBRA_TRACE_FREE_BASIS;
               ISPECL [`h:A->B`; `k:A ring`; `K:B ring`; `n:num`; `c:num->B`]
                 ALGEBRA_NORM_FREE_BASIS] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    check (fun th -> concl th = `field_extension(k:A ring,l:B ring) h`)) THEN
  SUBGOAL_THEN `~({i:num | i < n} = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `0` THEN
    SUBGOAL_THEN `~(n:num = 0)` MP_TAC THENL
     [EXPAND_TAC "n" THEN ASM_MESON_TAC[EXTENSION_DEGREE_EQ_0]; ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`;
    `mul_matrix (k,K) (h:A->B) n c x`] RING_CHARPOLY_MONIC) THEN
  MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`;
    `mul_matrix (k,K) (h:A->B) n c x`] RING_CHARPOLY_COEFF_TRACE) THEN
  MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`;
    `mul_matrix (k,K) (h:A->B) n c x`] RING_CHARPOLY_COEFF_0) THEN
  ASM_SIMP_TAC[FIELD_NONTRIVIAL; FINITE_NUMSEG_LT; IN_ELIM_THM;
               MUL_MATRIX_IN_CARRIER; CARD_NUMSEG_LT] THEN
  REPEAT(DISCH_THEN(ASSUME_TAC o SYM o check (is_eq o concl)) ORELSE
         DISCH_TAC) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rand(concl th) = `coeff (n - 1)
                              (minimal_polynomial (k,l) (h:A->B) x)`)) THEN
    ASM_SIMP_TAC[RING_NEG_NEG; RING_SUM];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rand(concl th) = `coeff 0 (minimal_polynomial (k,l) (h:A->B) x)`)) THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC; RING_POW; RING_NEG; RING_1; RING_DET;
                 GSYM RING_MUL_POW] THEN
    REWRITE_TAC[RING_RULE
     `ring_mul r (ring_neg r (ring_1 r)) (ring_neg r (ring_1 r)) =
      ring_1(r:A ring)`; RING_POW_ONE] THEN
    ASM_SIMP_TAC[RING_MUL_LID; RING_DET]]);;

let ALGEBRA_TRACE_NORM_MINIMAL_POLYNOMIAL = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ x IN ring_carrier l
        ==> algebra_trace(k,l) h x =
            ring_neg k
             (ring_mul k
               (ring_of_num k
                 (extension_degree
                   (subfield_generated l (x INSERT IMAGE h (ring_carrier k)),l)
                   I))
               (coeff (poly_deg k (minimal_polynomial(k,l) h x) - 1)
                      (minimal_polynomial(k,l) h x))) /\
            algebra_norm(k,l) h x =
            ring_pow k
             (ring_mul k
               (ring_pow k (ring_neg k (ring_1 k))
                  (poly_deg k (minimal_polynomial(k,l) h x)))
               (coeff 0 (minimal_polynomial(k,l) h x)))
             (extension_degree
               (subfield_generated l (x INSERT IMAGE h (ring_carrier k)),l) I)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION; algebraic_extension];
    ALL_TAC] THEN
  ABBREV_TAC
   `K = subfield_generated l (x INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `x INSERT IMAGE (h:A->B) (ring_carrier k)`]
    FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `field_extension(k,K) (h:A->B) /\ field_extension(K,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_FIELD_EXTENSION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`;
                 `x:B`] ALGEBRA_TRACE_NORM_INTERMEDIATE) THEN
  ASM_REWRITE_TAC[I_O_ID; I_THM] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    ALGEBRA_TRACE_NORM_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RING_MUL_RNEG THEN
  REWRITE_TAC[RING_OF_NUM] THEN MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN
  REWRITE_TAC[RING_POLYNOMIAL] THEN
  MATCH_MP_TAC MINIMAL_POLYNOMIAL_IN_CARRIER THEN ASM_REWRITE_TAC[]);;

let ALGEBRA_NORM_MINIMAL_POLYNOMIAL = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ x IN ring_carrier l
        ==> algebra_norm(k,l) h x =
            ring_pow k
             (ring_mul k
               (ring_pow k (ring_neg k (ring_1 k))
                  (poly_deg k (minimal_polynomial(k,l) h x)))
               (coeff 0 (minimal_polynomial(k,l) h x)))
             (extension_degree
               (subfield_generated l (x INSERT IMAGE h (ring_carrier k)),l) I)`,
  SIMP_TAC[ALGEBRA_TRACE_NORM_MINIMAL_POLYNOMIAL]);;

let ALGEBRA_TRACE_MINIMAL_POLYNOMIAL = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ x IN ring_carrier l
        ==> algebra_trace(k,l) h x =
            ring_neg k
             (ring_mul k
               (ring_of_num k
                 (extension_degree
                   (subfield_generated l (x INSERT IMAGE h (ring_carrier k)),l)
                   I))
               (coeff (poly_deg k (minimal_polynomial(k,l) h x) - 1)
                      (minimal_polynomial(k,l) h x)))`,
  SIMP_TAC[ALGEBRA_TRACE_NORM_MINIMAL_POLYNOMIAL]);;

(* ------------------------------------------------------------------------- *)
(* Norm and trace by embeddings. Let x be algebraic over k, with minimal     *)
(* polynomial p, K = k(x) and g a homomorphism from k into an algebraically  *)
(* closed field m. Then g o p is the product of (X - t x)^e over the         *)
(* extensions t of g to K, with e = [K:k]_i: each (X - t x)^e divides g o p  *)
(* since over the separable closure S of k in K the minimal polynomial of x  *)
(* has t x as its only root (K is purely inseparable over S), and the        *)
(* degrees agree. Hence g(N(x)) is the product of the s x over the           *)
(* extensions s of g to l, raised to the inseparable degree [l:k]_i, and     *)
(* g(Tr(x)) is [l:k]_i times their sum; for l separable these are the        *)
(* product and the sum of the conjugates of x, for l purely inseparable the  *)
(* norm and trace are x^[l:k] and [l:k] * x. The norm and the trace are      *)
(* transitive in towers.                                                     *)
(* ------------------------------------------------------------------------- *)

(* A monic polynomial over an algebraically closed field with only the root  *)
(* b is (X - b)^n.                                                           *)

let ALGEBRAICALLY_CLOSED_FIELD_SINGLE_ROOT = prove
 (`!(m:C ring) q b.
        algebraically_closed_field m /\ q IN ring_carrier(poly_ring m (:1)) /\
        monic m q /\ b IN ring_carrier m /\
        (!y. y IN ring_carrier m /\ poly_eval m q y = ring_0 m ==> y = b)
        ==> q = poly_pow m (poly_sub m (poly_var m one) (poly_const m b))
                  (poly_deg m q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING) THEN
  SUBGOAL_THEN `ring_polynomial m (q:(1->num)->C)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:C ring`; `q:(1->num)->C`]
    ALGEBRAICALLY_CLOSED_FIELD_SPLITS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MONIC_IMP_NONZERO]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  ABBREV_TAC `n = poly_deg m (q:(1->num)->C)` THEN
  MAP_EVERY X_GEN_TAC [`c:C`; `a:num->C`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= n ==> (a:num->C) i = b` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(ASSUME
     `!y:C. y IN ring_carrier m /\ poly_eval m q y = ring_0 m ==> y = b`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check ((=) `q:(1->num)->C` o lhs o concl)) THEN
    MP_TAC(ISPECL [`m:C ring`; `c:C`; `a:num->C`; `n:num`; `(a:num->C) i`]
      POLY_ROOTS_SPLIT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[];
    UNDISCH_THEN
     `!y:C. y IN ring_carrier m /\ poly_eval m q y = ring_0 m ==> y = b`
     (K ALL_TAC)] THEN
  SUBGOAL_THEN
   `ring_product (poly_ring m (:1)) (1..n)
      (\i. poly_sub m (poly_var m one) (poly_const m ((a:num->C) i))) =
    poly_pow m (poly_sub m (poly_var m one) (poly_const m b)) n`
  (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
   [TRANS_TAC EQ_TRANS
     `ring_product (poly_ring m (:1)) (1..n)
        (\i. poly_sub m (poly_var m one) (poly_const m (b:C)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_PRODUCT_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`poly_ring (m:C ring) (:1)`;
                     `poly_sub m (poly_var m one) (poly_const m (b:C))`;
                     `1..n`] RING_PRODUCT_CONST) THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; POLY_X_MINUS_A_IN_CARRIER;
                   POLY_RING_CLAUSES]];
    ALL_TAC] THEN
  ABBREV_TAC `P = poly_pow m (poly_sub m (poly_var m one) (poly_const m b))
                    n:(1->num)->C` THEN
  SUBGOAL_THEN `ring_polynomial m (P:(1->num)->C) /\ monic m P /\
                poly_deg m P = n`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    SUBGOAL_THEN
     `ring_polynomial m (poly_sub m (poly_var m one) (poly_const m (b:C)))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[RING_POLYNOMIAL_X_MINUS_A]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_POW; MONIC_POLY_POW; MONIC_X_MINUS_A;
                 POLY_DEG_POW; POLY_DEG_X_MINUS_A; MULT_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `c:C = ring_1 m` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `monic m (q:(1->num)->C)` THEN
    ASM_REWRITE_TAC[monic] THEN
    ASM_SIMP_TAC[COEFF_POLY_LMUL; RING_POLYNOMIAL_IMP_POWERSERIES] THEN
    UNDISCH_TAC `monic m (P:(1->num)->C)` THEN ASM_REWRITE_TAC[monic] THEN
    ASM_SIMP_TAC[RING_MUL_RID];
    ASM_SIMP_TAC[POLY_CONST_1; POLY_MUL_LID;
                 RING_POLYNOMIAL_IMP_POWERSERIES]]);;

(* The subfield generated by an algebraic x over k is the subring generated  *)
(* and a finite extension of k, of degree the degree of the minimal          *)
(* polynomial of x.                                                          *)

let SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC = prove
 (`!(h:A->B) k l x.
        field_extension (k,l) h /\ algebraic_over (k,l) h x
        ==> subring_generated l (x INSERT IMAGE h (ring_carrier k)) =
            subfield_generated l (x INSERT IMAGE h (ring_carrier k)) /\
            finite_extension
             (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k))) h /\
            x IN ring_carrier
             (subfield_generated l (x INSERT IMAGE h (ring_carrier k))) /\
            minimal_polynomial
             (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k))) h x =
            minimal_polynomial (k,l) h x /\
            extension_degree
             (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k))) h =
            poly_deg k (minimal_polynomial (k,l) h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBRING_EQ_SUBFIELD_GENERATED;
                  FIELD_SIMPLE_ALGEBRAIC_EXTENSION];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_OVER_IN_CARRIER) THEN
  ASM_SIMP_TAC[FINITE_SIMPLE_ALGEBRAIC_EXTENSION; EXTENSION_DEGREE_SIMPLE;
               SUBRING_GENERATED_INC_GEN; IN_INSERT] THEN
  MATCH_MP_TAC MINIMAL_POLYNOMIAL_SUBRING_GENERATED THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM; IN_INSERT] THEN SET_TAC[]);;

(* An extension to k(x) is determined by its value at x.                     *)

let RING_HOMOMORPHISM_EXTENSIONS_SIMPLE_EQ = prove
 (`!(h:A->B) (g:A->C) k l m x s t.
        field l /\
        s IN ring_homomorphism_extensions
              (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)),m)
              (h,g) /\
        t IN ring_homomorphism_extensions
              (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)),m)
              (h,g)
        ==> (s = t <=> s x = t x)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `X = (x:B) INSERT IMAGE (h:A->B) (ring_carrier k)` THEN
  REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN STRIP_TAC THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC EXTENSIONAL_EQ THEN
  EXISTS_TAC `ring_carrier(subfield_generated l (X:B->bool))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:B->C`; `t:B->C`; `subfield_generated l (X:B->bool)`;
                 `m:C ring`; `X:B->bool`]
    RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED) THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; SUBFIELD_GENERATED_IDEMPOT] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "X" THEN
  REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* Products and sums over the extensions to m of j along a tower are         *)
(* iterated products and sums over the extensions to l and then to m.        *)

let RING_HOMOMORPHISM_EXTENSIONS_TOWER_PRODUCT,
    RING_HOMOMORPHISM_EXTENSIONS_TOWER_SUM = (CONJ_PAIR o prove)
 (`(!(f:A->B) (g:B->C) (j:A->D) k l m n (r:E ring) u.
        finite_extension(k,l) f /\ finite_extension(l,m) g /\
        integral_domain n /\ ring_homomorphism(k,n) j
        ==> ring_product r (ring_homomorphism_extensions (k,m,n) (g o f,j)) u =
            ring_product r (ring_homomorphism_extensions (k,l,n) (f,j))
             (\t. ring_product r (ring_homomorphism_extensions (l,m,n) (g,t))
                    u)) /\
   (!(f:A->B) (g:B->C) (j:A->D) k l m n (r:E ring) u.
        finite_extension(k,l) f /\ finite_extension(l,m) g /\
        integral_domain n /\ ring_homomorphism(k,n) j
        ==> ring_sum r (ring_homomorphism_extensions (k,m,n) (g o f,j)) u =
            ring_sum r (ring_homomorphism_extensions (k,l,n) (f,j))
             (\t. ring_sum r (ring_homomorphism_extensions (l,m,n) (g,t))
                    u))`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `j:A->D`; `k:A ring`; `l:B ring`;
                 `m:C ring`; `n:D ring`]
    RING_HOMOMORPHISM_EXTENSIONS_TOWER) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM;
               FINITE_IMP_FIELD_EXTENSION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  (MATCH_MP_TAC RING_PRODUCT_UNIONS_PAIRWISE_DISJOINT ORELSE
   MATCH_MP_TAC RING_SUM_UNIONS_PAIRWISE_DISJOINT) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CARD_RING_HOMOMORPHISM_EXTENSIONS_LE] THEN
  REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ring_homomorphism_extensions] THEN
  ASM_SIMP_TAC[CARD_RING_HOMOMORPHISM_EXTENSIONS_LE]);;

(* The minimal polynomial over an algebraically closed field, by the         *)
(* extensions to k(x), with multiplicity the inseparable degree; its         *)
(* constant and subleading coefficients.                                     *)

let MINIMAL_POLYNOMIAL_EMBEDDING_DIVIDES = prove
 (`!(h:A->B) (g:A->C) k l m x t.
        field_extension(k,l) h /\ algebraic_over(k,l) h x /\
        algebraically_closed_field m /\
        t IN ring_homomorphism_extensions
              (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)),m)
              (h,g)
        ==> ring_divides (poly_ring m (:1))
             (poly_pow m (poly_sub m (poly_var m one) (poly_const m (t x)))
                (inseparable_degree
                  (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)))
                  h))
             (g o minimal_polynomial(k,l) h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `K = subfield_generated l
          ((x:B) INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  ABBREV_TAC `p = minimal_polynomial (k,l) (h:A->B) x` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
  SUBGOAL_THEN `field(K:B ring) /\ algebraic_over (k,K) (h:A->B) x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `algebraic_extension (k,K) (h:A->B)` THEN
    REWRITE_TAC[algebraic_extension; field_extension] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  UNDISCH_TAC
   `(t:B->C) IN ring_homomorphism_extensions (k,K,m) (h:A->B,g:A->C)` THEN
  REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`]
    SUBFIELD_OF_SEPARABLE_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[inseparable_degree] THEN
  ABBREV_TAC `S = subfield_generated K (separable_closure (k,K) (h:A->B))` THEN
  SUBGOAL_THEN `ring_carrier S = separable_closure (k,K) (h:A->B)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `field_extension(S,K) (I:B->B) /\ field_extension(k,S) (h:A->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED];
      MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `purely_inseparable_extension(S,K) (I:B->B)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    MATCH_MP_TAC PURELY_INSEPARABLE_OVER_SEPARABLE_CLOSURE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP PURELY_INSEPARABLE_IMP_ALGEBRAIC_EXTENSION) THEN
  SUBGOAL_THEN `separable_degree(S,K) (I:B->B) = 1` ASSUME_TAC THENL
   [ASM_MESON_TAC[SEPARABLE_DEGREE_EQ_1]; ALL_TAC] THEN
  SUBGOAL_THEN `algebraic_over(S,K) (I:B->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  SUBGOAL_THEN
   `subring_generated K ((x:B) INSERT IMAGE (I:B->B) (ring_carrier S)) = K`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`I:B->B`; `S:B ring`; `K:B ring`; `x:B`]
      SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[SUBFIELD_GENERATED_EQ; GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
    TRANS_TAC SUBSET_TRANS
     `ring_carrier(subfield_generated K
        ((x:B) INSERT IMAGE (h:A->B) (ring_carrier k)))` THEN
    CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `subfield_generated l
             ((x:B) INSERT IMAGE (h:A->B) (ring_carrier k)) = K`)) THEN
      REWRITE_TAC[SUBFIELD_GENERATED_IDEMPOT; SUBSET_REFL];
      MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN REWRITE_TAC[IMAGE_I] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `mu = minimal_polynomial(S,K) (I:B->B) x` THEN
  SUBGOAL_THEN `extension_degree(S,K) (I:B->B) = poly_deg S (mu:(1->num)->B)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`I:B->B`; `S:B ring`; `K:B ring`; `x:B`]
      EXTENSION_DEGREE_SIMPLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(S,m) (t:B->C)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_monomorphism(S,m) (t:B->C)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_MESON_TAC[field_extension; FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `t:B->C`; `S:B ring`; `K:B ring`; `m:C ring`;
                 `x:B`] SEPARABLE_DEGREE_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`I:B->B`; `t:B->C`; `t:B->C`; `S:B ring`; `K:B ring`;
                 `m:C ring`; `x:B`] RING_HOMOMORPHISM_EXTENSIONS_ROOT) THEN
  ASM_REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM; I_THM] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`I:B->B`; `S:B ring`; `K:B ring`; `x:B`]
    MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_polynomial S (mu:(1->num)->B)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_POLYNOMIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:B->C) x IN ring_carrier m` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`K:B ring`; `m:C ring`; `t:B->C`]
      RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(t:B->C) o mu IN ring_carrier(poly_ring m (:1)) /\
    poly_deg m ((t:B->C) o mu) = poly_deg S (mu:(1->num)->B) /\
    ~((t:B->C) o mu = poly_0 m) /\ monic m ((t:B->C) o mu)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:B ring`; `m:C ring`; `t:B->C`; `mu:(1->num)->B`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    MP_TAC(ISPECL [`S:B ring`; `m:C ring`; `t:B->C`; `mu:(1->num)->B`]
      POLY_EQ_0_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC `S:B ring` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `monic S (mu:(1->num)->B)` THEN
      ASM_REWRITE_TAC[monic; COEFF_COMPOSE] THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(ISPECL [`S:B ring`; `m:C ring`; `t:B->C`]
        RING_HOMOMORPHISM_1) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier m /\ poly_eval m ((t:B->C) o mu) y = ring_0 m
        ==> y = t x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:C ring`; `(t:B->C) o (mu:(1->num)->B)`]
      POLY_ROOT_BOUND) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; POLY_RING_CLAUSES] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `{b | b IN ring_carrier m /\
                       poly_eval m ((t:B->C) o (mu:(1->num)->B)) b =
                       ring_0 m}` CARD_LE_1) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    UNDISCH_TAC `poly_eval m ((t:B->C) o mu) (t x) = ring_0 m` THEN
    UNDISCH_TAC `(t:B->C) x IN ring_carrier m` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:C ring`; `(t:B->C) o (mu:(1->num)->B)`; `(t:B->C) x`]
    ALGEBRAICALLY_CLOSED_FIELD_SINGLE_ROOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(p:(1->num)->A) IN ring_carrier(poly_ring k (:1)) /\
                (h:A->B) o p IN ring_carrier(poly_ring S (:1))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `minimal_polynomial (k,l) (h:A->B) x = p`)) THEN
      MATCH_MP_TAC MINIMAL_POLYNOMIAL_IN_CARRIER THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC `k:A ring` THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_divides (poly_ring S (:1)) mu ((h:A->B) o (p:(1->num)->A))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`I:B->B`; `S:B ring`; `K:B ring`; `x:B`;
                   `(h:A->B) o (p:(1->num)->A)`]
      MINIMAL_POLYNOMIAL_DIVIDES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`; `x:B`]
      MINIMAL_POLYNOMIAL_VANISHES) THEN
    ASM_SIMP_TAC[POLY_EXTEND_EVALUATE; FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN
    REWRITE_TAC[I_O_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_divides (poly_ring m (:1))
      ((\q:(1->num)->B. (t:B->C) o q) mu)
      ((\q:(1->num)->B. (t:B->C) o q) ((h:A->B) o (p:(1->num)->A)))`
  MP_TAC THENL
   [MATCH_MP_TAC RING_DIVIDES_HOMOMORPHIC_IMAGE THEN
    EXISTS_TAC `poly_ring (S:B ring) (:1)` THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_POLY_RINGS];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `i:1->num` THEN
  MATCH_MP_TAC(ASSUME
   `!y. y IN ring_carrier k ==> (t:B->C) ((h:A->B) y) = (g:A->C) y`) THEN
  UNDISCH_TAC `(p:(1->num)->A) IN ring_carrier(poly_ring k (:1))` THEN
  REWRITE_TAC[POLY_RING_CLAUSES; IN_ELIM_THM; ring_polynomial;
              ring_powerseries] THEN
  SIMP_TAC[]);;

let MINIMAL_POLYNOMIAL_EMBEDDINGS = prove
 (`!(h:A->B) (g:A->C) k l m x.
        field_extension(k,l) h /\ algebraic_over(k,l) h x /\
        algebraically_closed_field m /\ ring_homomorphism(k,m) g
        ==> g o minimal_polynomial(k,l) h x =
            ring_product (poly_ring m (:1))
             (ring_homomorphism_extensions
               (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)),m)
               (h,g))
             (\s. poly_pow m (poly_sub m (poly_var m one) (poly_const m (s x)))
                   (inseparable_degree
                     (k,subfield_generated l
                          (x INSERT IMAGE h (ring_carrier k)))
                     h))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `x:B`] MINIMAL_POLYNOMIAL_EMBEDDING_DIVIDES) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `x:B`] RING_HOMOMORPHISM_EXTENSIONS_SIMPLE_EQ) THEN
  MP_TAC(SPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `K = subfield_generated l
          ((x:B) INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  ABBREV_TAC `p = minimal_polynomial (k,l) (h:A->B) x` THEN
  ABBREV_TAC `E = ring_homomorphism_extensions (k,K,m) (h:A->B,g:A->C)` THEN
  ABBREV_TAC `e = inseparable_degree (k,K) (h:A->B)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `field(l:B ring)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[field_extension]; DISCH_TAC THEN DISCH_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `K:B ring`; `m:C ring`]
    HAS_SIZE_SEPARABLE_DEGREE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`]
    EXTENSION_DEGREE_SEPARABLE_INSEPARABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s:B->C. s IN E ==> s x IN ring_carrier m` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:B->C. s IN E
      ==> ring_polynomial m
           (poly_pow m (poly_sub m (poly_var m one) (poly_const m (s x))) e) /\
          monic m
           (poly_pow m (poly_sub m (poly_var m one) (poly_const m (s x))) e) /\
          poly_deg m
           (poly_pow m (poly_sub m (poly_var m one) (poly_const m (s x))) e) =
          e`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:B->C` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:B->C) x IN ring_carrier m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_polynomial m
        (poly_sub m (poly_var m one) (poly_const m ((s:B->C) x)))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[RING_POLYNOMIAL_X_MINUS_A]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_POW; MONIC_POLY_POW; MONIC_X_MINUS_A;
                 POLY_DEG_POW; POLY_DEG_X_MINUS_A; MULT_CLAUSES;
                 INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_polynomial m (ring_product (poly_ring m (:1)) E
         (\s:B->C. poly_pow m (poly_sub m (poly_var m one)
                                 (poly_const m (s x))) e)) /\
    monic m (ring_product (poly_ring m (:1)) E
         (\s:B->C. poly_pow m (poly_sub m (poly_var m one)
                                 (poly_const m (s x))) e)) /\
    poly_deg m (ring_product (poly_ring m (:1)) E
         (\s:B->C. poly_pow m (poly_sub m (poly_var m one)
                                 (poly_const m (s x))) e)) =
    poly_deg k (p:(1->num)->A)`
  MP_TAC THENL
   [ASM_SIMP_TAC[MONIC_POLY_PRODUCT; POLY_DEG_PRODUCT_MONIC] THEN
    REWRITE_TAC[RING_POLYNOMIAL; RING_PRODUCT] THEN
    ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `P = ring_product (poly_ring m (:1)) E
         (\s:B->C. poly_pow m (poly_sub m (poly_var m one)
                                 (poly_const m (s x))) e)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(p:(1->num)->A) IN ring_carrier(poly_ring k (:1)) /\
                monic k p`
  STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `minimal_polynomial (k,l) (h:A->B) x = p`)) THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER; MINIMAL_POLYNOMIAL_MONIC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_monomorphism(k,m) (g:A->C)` ASSUME_TAC THENL
   [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_MESON_TAC[field_extension; FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g:A->C) o p IN ring_carrier(poly_ring m (:1)) /\
    poly_deg m ((g:A->C) o p) = poly_deg k (p:(1->num)->A) /\
    monic m ((g:A->C) o p)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `m:C ring`; `g:A->C`; `p:(1->num)->A`]
      POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
      EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `monic k (p:(1->num)->A)` THEN
      ASM_REWRITE_TAC[monic; COEFF_COMPOSE] THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(ISPECL [`k:A ring`; `m:C ring`; `g:A->C`]
        RING_HOMOMORPHISM_1) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UFD(poly_ring (m:C ring) (:1))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PID_IMP_UFD; PID_POLY_RING]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t:B->C.
      s IN E /\ t IN E /\ ~(s = t)
      ==> ring_coprime (poly_ring m (:1))
           (poly_pow m (poly_sub m (poly_var m one) (poly_const m (s x))) e,
            poly_pow m (poly_sub m (poly_var m one) (poly_const m (t x))) e)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:B->C`; `t:B->C`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((s:B->C) x = t x)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(s:B->C) x IN ring_carrier m /\ (t:B->C) x IN ring_carrier m`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `poly_pow (m:C ring) = ring_pow (poly_ring m (:1))`
    SUBST1_TAC THENL [REWRITE_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
    MATCH_MP_TAC RING_COPRIME_LPOW THEN
    ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER; RING_POW] THEN
    MATCH_MP_TAC RING_COPRIME_RPOW THEN
    ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER] THEN
    MATCH_MP_TAC RING_COPRIME_DISTINCT_MONIC_IRREDUCIBLES THEN
    ASM_SIMP_TAC[MONIC_X_MINUS_A; RING_IRREDUCIBLE_X_MINUS_A] THEN
    DISCH_THEN(MP_TAC o AP_TERM `coeff 0:((1->num)->C)->C`) THEN
    REWRITE_TAC[COEFF_POLY_SUB; COEFF_POLY_VAR; COEFF_POLY_CONST; ARITH] THEN
    ASM_SIMP_TAC[RING_SUB_LZERO; RING_NEG_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_divides (poly_ring m (:1)) P ((g:A->C) o p)`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_COPRIME_PRODUCT_DIVIDES o
      snd) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN ASM_SIMP_TAC[];
        REWRITE_TAC[pairwise] THEN ASM_SIMP_TAC[]];
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MONIC_DIVIDES_EQ THEN
  EXISTS_TAC `m:C ring` THEN ASM_REWRITE_TAC[LE_REFL]);;

let MINIMAL_POLYNOMIAL_COEFF_EMBEDDINGS = prove
 (`!(h:A->B) (g:A->C) k l m x.
        field_extension(k,l) h /\ algebraic_over(k,l) h x /\
        algebraically_closed_field m /\ ring_homomorphism(k,m) g
        ==> g(ring_mul k
               (ring_pow k (ring_neg k (ring_1 k))
                  (poly_deg k (minimal_polynomial(k,l) h x)))
               (coeff 0 (minimal_polynomial(k,l) h x))) =
            ring_pow m
             (ring_product m
               (ring_homomorphism_extensions
                 (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)),m)
                 (h,g))
               (\s. s x))
             (inseparable_degree
               (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)))
               h) /\
            g(ring_neg k
               (coeff (poly_deg k (minimal_polynomial(k,l) h x) - 1)
                      (minimal_polynomial(k,l) h x))) =
            ring_mul m
             (ring_of_num m
               (inseparable_degree
                 (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)))
                 h))
             (ring_sum m
               (ring_homomorphism_extensions
                 (k,subfield_generated l (x INSERT IMAGE h (ring_carrier k)),m)
                 (h,g))
               (\s. s x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `x:B`] MINIMAL_POLYNOMIAL_EMBEDDINGS) THEN
  MP_TAC(SPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `K = subfield_generated l
          ((x:B) INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  ABBREV_TAC `p = minimal_polynomial (k,l) (h:A->B) x` THEN
  ABBREV_TAC `E = ring_homomorphism_extensions (k,K,m) (h:A->B,g:A->C)` THEN
  ABBREV_TAC `e = inseparable_degree (k,K) (h:A->B)` THEN
  STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `K:B ring`; `m:C ring`]
    HAS_SIZE_SEPARABLE_DEGREE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`]
    EXTENSION_DEGREE_SEPARABLE_INSEPARABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(E:(B->C)->bool = {}) /\ ~(e = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "E" THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY THEN
      ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `K:B ring`]
        EXTENSION_DEGREE_EQ_0) THEN
      ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION; MULT_CLAUSES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:B->C. s IN E ==> s x IN ring_carrier m` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:(1->num)->A) IN ring_carrier(poly_ring k (:1))`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `minimal_polynomial (k,l) (h:A->B) x = p`)) THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. coeff i (p:(1->num)->A) IN ring_carrier k`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC COEFF_IN_CARRIER THEN
    MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. (g:A->C)(coeff i (p:(1->num)->A)) =
                    coeff i (ring_product (poly_ring m (:1)) E
                      (\s. poly_pow m (poly_sub m (poly_var m one)
                                         (poly_const m ((s:B->C) x))) e))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBST1_TAC(SYM(ASSUME
     `(g:A->C) o (p:(1->num)->A) =
      ring_product (poly_ring m (:1)) E
       (\s. poly_pow m (poly_sub m (poly_var m one)
                          (poly_const m ((s:B->C) x))) e)`)) THEN
    REWRITE_TAC[COEFF_COMPOSE];
    ALL_TAC] THEN
  (let th = ASSUME `ring_homomorphism(k,m) (g:A->C)` in
   ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
                MATCH_MP RING_HOMOMORPHISM_POW th;
                MATCH_MP RING_HOMOMORPHISM_NEG th;
                MATCH_MP RING_HOMOMORPHISM_1 th;
                RING_POW; RING_NEG; RING_1]) THEN
  SUBGOAL_THEN
   `!s:B->C. s IN E
      ==> poly_pow m (poly_sub m (poly_var m one) (poly_const m (s x))) e IN
          ring_carrier(poly_ring m (:1)) /\
          monic m
           (poly_pow m (poly_sub m (poly_var m one) (poly_const m (s x))) e) /\
          poly_deg m
           (poly_pow m (poly_sub m (poly_var m one) (poly_const m (s x))) e) =
          e`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:B->C` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:B->C) x IN ring_carrier m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_polynomial m
        (poly_sub m (poly_var m one) (poly_const m ((s:B->C) x)))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[RING_POLYNOMIAL_X_MINUS_A]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_POW; MONIC_POLY_POW;
                 MONIC_X_MINUS_A; POLY_DEG_POW; POLY_DEG_X_MINUS_A;
                 MULT_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `separable_degree (k,K) (h:A->B) * e = e * CARD(E:(B->C)->bool)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:C ring`; `(:1)`] POLY_RING_HOMOMORPHISM_COEFF_0) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\s:B->C. poly_pow m (poly_sub m (poly_var m one)
                                       (poly_const m (s x))) e`;
      `E:(B->C)->bool`]
     (MATCH_MP RING_HOMOMORPHISM_PRODUCT (ASSUME
       `ring_homomorphism (poly_ring (m:C ring) (:1),m) (coeff 0)`))) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_mul m
       (ring_pow m (ring_neg m (ring_1 m)) (e * CARD(E:(B->C)->bool)))
       (ring_product m E (\s:B->C. ring_pow m (ring_neg m (s x)) e))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RING_PRODUCT_EQ THEN
      X_GEN_TAC `s:B->C` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `ring_pow (poly_ring (m:C ring) (:1)) = poly_pow m`
      (SUBST1_TAC o SYM) THENL [REWRITE_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand)
        (MATCH_MP RING_HOMOMORPHISM_POW (ASSUME
          `ring_homomorphism (poly_ring (m:C ring) (:1),m) (coeff 0)`)) o
        lhand o snd) THEN
      ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[COEFF_POLY_SUB; COEFF_POLY_VAR; COEFF_POLY_CONST; ARITH] THEN
      ASM_SIMP_TAC[RING_SUB_LZERO];
      MATCH_MP_TAC RING_PRODUCT_POW_NEG THEN ASM_SIMP_TAC[]];
    MP_TAC(ISPECL [`m:C ring`;
                   `\s:B->C. poly_pow m (poly_sub m (poly_var m one)
                                           (poly_const m (s x))) e`;
                   `E:(B->C)->bool`] COEFF_RING_PRODUCT_MONIC_SUBLEADING) THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL; NSUM_CONST] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    DISCH_THEN SUBST1_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_neg m (ring_sum m E
        (\s:B->C. ring_neg m (ring_mul m (ring_of_num m e) (s x))))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
      ASM_SIMP_TAC[COEFF_POLY_POW_X_MINUS_A_SUBLEADING];
      MP_TAC(ISPECL [`m:C ring`; `\s:B->C. ring_mul m (ring_of_num m e) (s x)`;
                     `E:(B->C)->bool`] RING_SUM_NEG) THEN
      ASM_SIMP_TAC[RING_MUL; RING_OF_NUM] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[RING_NEG_NEG; RING_SUM; RING_SUM_LMUL; RING_OF_NUM]]]);;

(* The norm and the trace by the extensions to an algebraically closed       *)
(* field, of any homomorphism g from k                                       *)
(* (ALGEBRA_TRACE_NORM_EMBEDDINGS_GEN) or of the composite of h with a       *)
(* homomorphism j from l (ALGEBRA_TRACE_NORM_EMBEDDINGS); the separable and  *)
(* purely inseparable cases.                                                 *)

let ALGEBRA_TRACE_NORM_EMBEDDINGS_GEN = prove
 (`!(h:A->B) (g:A->C) k l m x.
        finite_extension(k,l) h /\ algebraically_closed_field m /\
        ring_homomorphism(k,m) g /\ x IN ring_carrier l
        ==> g(algebra_norm(k,l) h x) =
            ring_pow m
             (ring_product m (ring_homomorphism_extensions(k,l,m) (h,g))
                (\s. s x))
             (inseparable_degree(k,l) h) /\
            g(algebra_trace(k,l) h x) =
            ring_mul m (ring_of_num m (inseparable_degree(k,l) h))
             (ring_sum m (ring_homomorphism_extensions(k,l,m) (h,g))
                (\s. s x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION; algebraic_extension];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    ALGEBRA_NORM_MINIMAL_POLYNOMIAL) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    ALGEBRA_TRACE_MINIMAL_POLYNOMIAL) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `x:B`] MINIMAL_POLYNOMIAL_COEFF_EMBEDDINGS) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `(x:B) INSERT IMAGE (h:A->B) (ring_carrier k)`]
    FINITE_EXTENSION_SUBFIELD_GENERATED) THEN
  MP_TAC(SPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[SET_RULE `s SUBSET (x:B) INSERT s`] THEN
  ABBREV_TAC
   `K = subfield_generated l
          ((x:B) INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  ABBREV_TAC `p = minimal_polynomial (k,l) (h:A->B) x` THEN
  ABBREV_TAC `E = ring_homomorphism_extensions (k,K,m) (h:A->B,g:A->C)` THEN
  ABBREV_TAC `e = inseparable_degree (k,K) (h:A->B)` THEN
  ABBREV_TAC `r = extension_degree (K,l) (I:B->B)` THEN
  ABBREV_TAC `d = poly_deg k (p:(1->num)->A)` THEN
  REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o
    check (is_conj o concl))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `g:A->C`; `k:A ring`; `K:B ring`;
                 `l:B ring`; `m:C ring`; `m:C ring`; `\s:B->C. s x`]
    RING_HOMOMORPHISM_EXTENSIONS_TOWER_PRODUCT) THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `g:A->C`; `k:A ring`; `K:B ring`;
                 `l:B ring`; `m:C ring`; `m:C ring`; `\s:B->C. s x`]
    RING_HOMOMORPHISM_EXTENSIONS_TOWER_SUM) THEN
  ASM_REWRITE_TAC[I_O_ID] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!t:B->C. t IN E
      ==> ring_product m (ring_homomorphism_extensions (K,l,m) (I,t))
                         (\s. s x) =
          ring_pow m (t x) (separable_degree (K,l) (I:B->B)) /\
          ring_sum m (ring_homomorphism_extensions (K,l,m) (I,t)) (\s. s x) =
          ring_mul m (ring_of_num m (separable_degree (K,l) (I:B->B))) (t x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:B->C` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_homomorphism (K,m) (t:B->C) /\ t x IN ring_carrier m`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t:B->C) IN E` THEN EXPAND_TAC "E" THEN
      REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPECL [`K:B ring`; `m:C ring`; `t:B->C`]
        RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`I:B->B`; `t:B->C`; `K:B ring`; `l:B ring`; `m:C ring`]
      HAS_SIZE_SEPARABLE_DEGREE) THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!s:B->C. s IN ring_homomorphism_extensions (K,l,m) (I,t) ==> s x = t x`
    ASSUME_TAC THENL
     [REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM; I_THM] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ring_product m (ring_homomorphism_extensions (K,l,m) (I,t))
                       (\s:B->C. (t:B->C) x)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC[];
                      ALL_TAC];
      TRANS_TAC EQ_TRANS
       `ring_sum m (ring_homomorphism_extensions (K,l,m) (I,t))
                   (\s:B->C. (t:B->C) x)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[];
                      ALL_TAC]] THEN
    ASM_SIMP_TAC[RING_PRODUCT_CONST; RING_SUM_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `K:B ring`; `m:C ring`]
    HAS_SIZE_SEPARABLE_DEGREE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t:B->C. t IN E ==> t x IN ring_carrier m` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
    INSEPARABLE_DEGREE_TOWER) THEN
  MP_TAC(ISPECL [`I:B->B`; `K:B ring`; `l:B ring`]
    EXTENSION_DEGREE_SEPARABLE_INSEPARABLE) THEN
  ASM_REWRITE_TAC[I_O_ID] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sl = separable_degree (K,l) (I:B->B)` THEN
  ABBREV_TAC `il = inseparable_degree (K,l) (I:B->B)` THEN
  SUBGOAL_THEN `!i. coeff i (p:(1->num)->A) IN ring_carrier k` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC COEFF_IN_CARRIER THEN
    MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THEN
    REWRITE_TAC[RING_POLYNOMIAL] THEN
    SUBST1_TAC(SYM(ASSUME `minimal_polynomial (k,l) (h:A->B) x = p`)) THEN
    ASM_SIMP_TAC[MINIMAL_POLYNOMIAL_IN_CARRIER];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `ring_product m E
       (\t. ring_product m (ring_homomorphism_extensions (K,l,m) (I,t))
                           (\s. s x)) =
      ring_pow m (ring_product m E (\t:B->C. t x)) sl`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS `ring_product m E (\t:B->C. ring_pow m (t x) sl)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_PRODUCT_EQ THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC RING_PRODUCT_POW THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul k (ring_pow k (ring_neg k (ring_1 k)) d)
                 (coeff 0 (p:(1->num)->A)) IN ring_carrier k`
    ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL; RING_POW; RING_NEG; RING_1];
                      ALL_TAC] THEN
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW
     (ASSUME `ring_homomorphism(k,m) (g:A->C)`)] THEN
    ASM_SIMP_TAC[RING_POW_POW; RING_PRODUCT] THEN AP_TERM_TAC THEN ARITH_TAC;
    SUBGOAL_THEN
     `ring_sum m E
        (\t. ring_sum m (ring_homomorphism_extensions (K,l,m) (I,t))
                        (\s. s x)) =
      ring_mul m (ring_of_num m sl) (ring_sum m E (\t:B->C. t x))`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ring_sum m E (\t:B->C. ring_mul m (ring_of_num m sl) (t x))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC RING_SUM_LMUL THEN ASM_SIMP_TAC[RING_OF_NUM]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_neg k (ring_mul k (ring_of_num k (sl * il))
                             (coeff (d - 1) (p:(1->num)->A))) =
      ring_mul k (ring_of_num k (sl * il)) (ring_neg k (coeff (d - 1) p))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_MUL_RNEG THEN
      ASM_SIMP_TAC[RING_OF_NUM];
      ALL_TAC] THEN
    (let th = ASSUME `ring_homomorphism(k,m) (g:A->C)` in
     ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
                  MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th;
                  RING_OF_NUM; RING_NEG]) THEN
    REWRITE_TAC[RING_OF_NUM_MUL] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul r (ring_mul r a b) (ring_mul r c d) =
      ring_mul r (ring_mul r c b) (ring_mul r a (d:A))`) THEN
    ASM_SIMP_TAC[RING_OF_NUM; RING_SUM]]);;

let ALGEBRA_TRACE_NORM_EMBEDDINGS = prove
 (`!(h:A->B) (j:B->C) k l m x.
        finite_extension(k,l) h /\ algebraically_closed_field m /\
        ring_homomorphism(l,m) j /\ x IN ring_carrier l
        ==> j(h(algebra_norm(k,l) h x)) =
            ring_pow m
             (ring_product m (ring_homomorphism_extensions(k,l,m) (h,j o h))
                (\s. s x))
             (inseparable_degree(k,l) h) /\
            j(h(algebra_trace(k,l) h x)) =
            ring_mul m (ring_of_num m (inseparable_degree(k,l) h))
             (ring_sum m (ring_homomorphism_extensions(k,l,m) (h,j o h))
                (\s. s x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `(j:B->C) o (h:A->B)`; `k:A ring`; `l:B ring`;
                 `m:C ring`; `x:B`] ALGEBRA_TRACE_NORM_EMBEDDINGS_GEN) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM; FINITE_IMP_FIELD_EXTENSION]);;

let ALGEBRA_TRACE_NORM_EMBEDDINGS_SEPARABLE = prove
 (`!(h:A->B) (g:A->C) k l m x.
        finite_extension(k,l) h /\ separable_extension(k,l) h /\
        algebraically_closed_field m /\ ring_homomorphism(k,m) g /\
        x IN ring_carrier l
        ==> g(algebra_norm(k,l) h x) =
            ring_product m (ring_homomorphism_extensions(k,l,m) (h,g))
              (\s. s x) /\
            g(algebra_trace(k,l) h x) =
            ring_sum m (ring_homomorphism_extensions(k,l,m) (h,g))
              (\s. s x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `x:B`] ALGEBRA_TRACE_NORM_EMBEDDINGS_GEN) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] INSEPARABLE_DEGREE_EQ_1) THEN
  ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION] THEN
  SIMP_TAC[RING_POW_1; RING_PRODUCT; RING_OF_NUM_1; RING_MUL_LID; RING_SUM]);;

let ALGEBRA_TRACE_NORM_PURELY_INSEPARABLE = prove
 (`!(h:A->B) k l x.
        finite_extension(k,l) h /\ purely_inseparable_extension(k,l) h /\
        x IN ring_carrier l
        ==> h(algebra_norm(k,l) h x) = ring_pow l x (extension_degree(k,l) h) /\
            h(algebra_trace(k,l) h x) =
            ring_mul l (ring_of_num l (extension_degree(k,l) h)) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:(B#num)ring`; `j:B->B#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> rand(concl th) = `j:B->B#num`)) THEN
  SUBGOAL_THEN `ring_homomorphism(k,n) ((j:B->B#num) o (h:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `separable_degree(k,l) (h:A->B) = 1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] SEPARABLE_DEGREE_EQ_1) THEN
    ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism_extensions (k,l,n) (h,(j:B->B#num) o (h:A->B)) =
    {RESTRICTION (ring_carrier l) j}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `k:A ring`;
                   `l:B ring`; `n:(B#num)ring`] HAS_SIZE_SEPARABLE_DEGREE) THEN
    MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `j:B->B#num`;
                   `k:A ring`; `l:B ring`; `n:(B#num)ring`]
      RESTRICTION_IN_RING_HOMOMORPHISM_EXTENSIONS) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `j:B->B#num`; `k:A ring`; `l:B ring`;
                 `n:(B#num)ring`; `x:B`] ALGEBRA_TRACE_NORM_EMBEDDINGS) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    EXTENSION_DEGREE_SEPARABLE_INSEPARABLE) THEN
  ASM_SIMP_TAC[SEPARABLE_DEGREE_EQ_1; FINITE_IMP_ALGEBRAIC_EXTENSION;
               MULT_CLAUSES; RING_PRODUCT_SING; RING_SUM_SING;
               RESTRICTION] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `(j:B->B#num) x IN ring_carrier n` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`l:B ring`; `n:(B#num)ring`; `j:B->B#num`]
      RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (let th = ASSUME `ring_homomorphism(l,n) (j:B->B#num)` in
   REWRITE_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th)] THEN
   ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW th);
                GSYM(MATCH_MP RING_HOMOMORPHISM_MUL th); RING_OF_NUM]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`]
    ALGEBRA_TRACE_NORM_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  STRIP_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC(CONJUNCT2(REWRITE_RULE[ring_monomorphism]
   (ASSUME `ring_monomorphism(l,n) (j:B->B#num)`))) THEN
  ASM_SIMP_TAC[RING_POW; RING_MUL; RING_OF_NUM] THEN
  MATCH_MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_IN_CARRIER) THEN
  ASM_REWRITE_TAC[]);;

(* For a finite separable extension the trace is the sum of the distinct     *)
(* embeddings into an algebraic closure, which are linearly independent by   *)
(* Dedekind, so it is a nonzero linear map over k from l to k, hence onto.   *)

let ALGEBRA_TRACE_SURJECTIVE = prove
 (`!(h:A->B) k l.
        finite_extension(k,l) h /\ separable_extension(k,l) h
        ==> IMAGE (algebra_trace(k,l) h) (ring_carrier l) = ring_carrier k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `?x:B. x IN ring_carrier l /\ ~(algebra_trace(k,l) (h:A->B) x = ring_0 k)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:(B#num)ring`; `j:B->B#num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
      MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
      check (fun th -> rand(concl th) = `j:B->B#num`)) THEN
    SUBGOAL_THEN `ring_homomorphism(k,n) ((j:B->B#num) o (h:A->B))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `k:A ring`;
                   `l:B ring`; `n:(B#num)ring`]
      HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS) THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN
    ABBREV_TAC `E = ring_homomorphism_extensions (k,l,n)
                      (h:A->B,(j:B->B#num) o h)` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(E:(B->B#num)->bool = {})` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_EXTENSIONS_NONEMPTY THEN
      ASM_SIMP_TAC[FINITE_IMP_ALGEBRAIC_EXTENSION];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!f. f IN E ==> ring_homomorphism(l,n) (f:B->B#num)) /\
      (!f g. f IN E /\ g IN E /\ ~(f = g)
             ==> ?x. x IN ring_carrier l /\ ~((f:B->B#num) x = g x))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN
      SIMP_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`f:B->B#num`; `g:B->B#num`] THEN STRIP_TAC THEN
      ASM_MESON_TAC[EXTENSIONAL_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[]
     `~(!x:B. x IN ring_carrier l ==> algebra_trace(k,l) (h:A->B) x = ring_0 k)
      ==> ?x. x IN ring_carrier l /\ ~(algebra_trace(k,l) h x = ring_0 k)`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `n:(B#num)ring`; `E:(B->B#num)->bool`;
                   `\f:B->B#num. ring_1(n:(B#num)ring)`]
      RING_HOMOMORPHISMS_INDEPENDENT_SET) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_1] THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> ~(p ==> q)`) THEN CONJ_TAC THENL
     [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      TRANS_TAC EQ_TRANS `ring_sum n E (\f:B->B#num. f x)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `f:B->B#num` THEN DISCH_TAC THEN
        REWRITE_TAC[] THEN MATCH_MP_TAC RING_MUL_LID THEN
        ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
        MP_TAC(ISPECL [`h:A->B`; `(j:B->B#num) o (h:A->B)`; `k:A ring`;
                       `l:B ring`; `n:(B#num)ring`; `x:B`]
          ALGEBRA_TRACE_NORM_EMBEDDINGS_SEPARABLE) THEN
        ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
        MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[FIELD_NONTRIVIAL] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER];
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `a:A` THEN DISCH_TAC] THEN
  ABBREV_TAC `t = algebra_trace(k,l) (h:A->B) x` THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier k` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_mul k (a:A) (ring_inv k t) IN ring_carrier k`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL; RING_INV]; ALL_TAC] THEN
  EXISTS_TAC `ring_mul l ((h:A->B)(ring_mul k a (ring_inv k t))) x` THEN
  ASM_SIMP_TAC[ALGEBRA_TRACE_SCALAR] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_INV; FIELD_MUL_LINV; RING_MUL_RID];
    ASM_MESON_TAC[RING_MUL; RING_HOMOMORPHISM_IN_CARRIER]]);;

(* Transitivity in towers, by the embedding formula over an algebraic        *)
(* closure of m and the injectivity of the base embedding.                   *)

let ALGEBRA_TRACE_NORM_TOWER = prove
 (`!(f:A->B) (g:B->C) k l m x.
        field_extension(k,l) f /\ field_extension(l,m) g /\
        x IN ring_carrier m
        ==> algebra_trace(k,m) (g o f) x =
            algebra_trace(k,l) f (algebra_trace(l,m) g x) /\
            algebra_norm(k,m) (g o f) x =
            algebra_norm(k,l) f (algebra_norm(l,m) g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `finite_extension(k,l) (f:A->B) /\ finite_extension(l,m) (g:B->C)` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC);
    SUBGOAL_THEN
     `ring_homomorphism(k,l) (f:A->B) /\ ring_homomorphism(l,m) (g:B->C) /\
      field_extension(k,m) (g o f)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FIELD_EXTENSION_IMP_HOMOMORPHISM; FIELD_EXTENSION_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(?n d e. projective_basis (k,m) ((g:B->C) o (f:A->B)) n d e)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[PROJECTIVE_BASIS_IMP_FINITE_EXTENSION;
                    FINITE_EXTENSION_TRANS_EQ];
      ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS]] THEN
    ASM_CASES_TAC `finite_extension(l,m) (g:B->C)` THENL
     [SUBGOAL_THEN `~(?n b e. projective_basis (k,l) (f:A->B) n b e)`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[PROJECTIVE_BASIS_IMP_FINITE_EXTENSION];
        ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS]];
      SUBGOAL_THEN `~(?n c e. projective_basis (l,m) (g:B->C) n c e)`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[PROJECTIVE_BASIS_IMP_FINITE_EXTENSION];
        ASM_SIMP_TAC[ALGEBRA_TRACE_NORM_NO_PROJECTIVE_BASIS; ALGEBRA_TRACE_0;
                     ALGEBRA_NORM_1]]]] THEN
  SUBGOAL_THEN `finite_extension(k,m) ((g:B->C) o (f:A->B))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_EXTENSION_TRANS]; ALL_TAC] THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP FINITE_IMP_FIELD_EXTENSION o
    check (fun th -> rand(concl th) = t)))
   [`f:A->B`; `g:B->C`] THEN
  MP_TAC(ISPEC `m:C ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:(C#num)ring`; `j:C->C#num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  ABBREV_TAC `G = (j:C->C#num) o (g:B->C) o (f:A->B)` THEN
  SUBGOAL_THEN `ring_monomorphism(k,n) (G:A->C#num)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN
    EXISTS_TAC `m:C ring` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN
    EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  MP_TAC(ISPECL [`(g:B->C) o (f:A->B)`; `G:A->C#num`; `k:A ring`; `m:C ring`;
                 `n:(C#num)ring`; `x:C`] ALGEBRA_TRACE_NORM_EMBEDDINGS_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`g:B->C`; `l:B ring`; `m:C ring`; `x:C`]
    ALGEBRA_TRACE_NORM_IN_CARRIER) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `G:A->C#num`; `k:A ring`; `l:B ring`;
                 `n:(C#num)ring`; `algebra_norm(l,m) (g:B->C) x`]
    ALGEBRA_TRACE_NORM_EMBEDDINGS_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`f:A->B`; `G:A->C#num`; `k:A ring`; `l:B ring`;
                 `n:(C#num)ring`; `algebra_trace(l,m) (g:B->C) x`]
    ALGEBRA_TRACE_NORM_EMBEDDINGS_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `G:A->C#num`; `k:A ring`; `l:B ring`;
                 `m:C ring`; `n:(C#num)ring`; `n:(C#num)ring`;
                 `\s:C->C#num. s x`]
    RING_HOMOMORPHISM_EXTENSIONS_TOWER_PRODUCT) THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `G:A->C#num`; `k:A ring`; `l:B ring`;
                 `m:C ring`; `n:(C#num)ring`; `n:(C#num)ring`;
                 `\s:C->C#num. s x`]
    RING_HOMOMORPHISM_EXTENSIONS_TOWER_SUM) THEN
  MP_TAC(ISPECL [`f:A->B`; `g:B->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    INSEPARABLE_DEGREE_TOWER) THEN
  MP_TAC(ISPECL [`f:A->B`; `G:A->C#num`; `k:A ring`; `l:B ring`;
                 `n:(C#num)ring`] CARD_RING_HOMOMORPHISM_EXTENSIONS_LE) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
  ABBREV_TAC
   `Ekl = ring_homomorphism_extensions (k,l,n) (f:A->B,G:A->C#num)` THEN
  ABBREV_TAC `Ekm = ring_homomorphism_extensions (k,m,n)
                      ((g:B->C) o (f:A->B),G:A->C#num)` THEN
  REPEAT DISCH_TAC THEN
  UNDISCH_THEN
   `FINITE(Ekl:(B->C#num)->bool) /\ CARD Ekl <= extension_degree (k,l) (f:A->B)`
   STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
   `!t:B->C#num. t IN Ekl
      ==> t(algebra_norm(l,m) (g:B->C) x) =
          ring_pow n
           (ring_product n (ring_homomorphism_extensions(l,m,n) (g,t))
              (\s. s x))
           (inseparable_degree(l,m) g) /\
          t(algebra_trace(l,m) g x) =
          ring_mul n (ring_of_num n (inseparable_degree(l,m) g))
           (ring_sum n (ring_homomorphism_extensions(l,m,n) (g,t))
              (\s. s x))`
  (LABEL_TAC "emb") THENL
   [X_GEN_TAC `t:B->C#num` THEN EXPAND_TAC "Ekl" THEN
    DISCH_THEN(STRIP_ASSUME_TAC o
      REWRITE_RULE[ring_homomorphism_extensions; IN_ELIM_THM]) THEN
    MATCH_MP_TAC ALGEBRA_TRACE_NORM_EMBEDDINGS_GEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC(CONJUNCT2(REWRITE_RULE[ring_monomorphism]
   (ASSUME `ring_monomorphism(k,n) (G:A->C#num)`))) THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
    SUBGOAL_THEN
     `ring_sum n Ekl (\s:B->C#num. s (algebra_trace (l,m) (g:B->C) x)) =
      ring_mul n (ring_of_num n (inseparable_degree (l,m) g))
       (ring_sum n Ekl
         (\t. ring_sum n (ring_homomorphism_extensions (l,m,n) (g,t))
                (\s. s x)))`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ring_sum n Ekl
         (\t:B->C#num. ring_mul n (ring_of_num n (inseparable_degree (l,m) g))
           (ring_sum n (ring_homomorphism_extensions (l,m,n) ((g:B->C),t))
              (\s. s x)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `t:B->C#num` THEN
        DISCH_TAC THEN REWRITE_TAC[] THEN
        REMOVE_THEN "emb" (MP_TAC o SPEC `t:B->C#num`) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        MATCH_MP_TAC RING_SUM_LMUL THEN ASM_REWRITE_TAC[RING_OF_NUM; RING_SUM]];
      ALL_TAC] THEN
    REWRITE_TAC[RING_OF_NUM_MUL] THEN
    MATCH_MP_TAC(GSYM RING_MUL_ASSOC) THEN
    REWRITE_TAC[RING_OF_NUM; RING_SUM];
    REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
    SUBGOAL_THEN
     `ring_product n Ekl (\s:B->C#num. s (algebra_norm (l,m) (g:B->C) x)) =
      ring_pow n
       (ring_product n Ekl
         (\t. ring_product n (ring_homomorphism_extensions (l,m,n) (g,t))
                (\s. s x)))
       (inseparable_degree (l,m) g)`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ring_product n Ekl
         (\t:B->C#num. ring_pow n
           (ring_product n
              (ring_homomorphism_extensions (l,m,n) ((g:B->C),t))
              (\s. s x))
           (inseparable_degree (l,m) g))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `t:B->C#num` THEN
        DISCH_TAC THEN REWRITE_TAC[] THEN
        REMOVE_THEN "emb" (MP_TAC o SPEC `t:B->C#num`) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        MATCH_MP_TAC RING_PRODUCT_POW THEN ASM_REWRITE_TAC[RING_PRODUCT]];
      ALL_TAC] THEN
    SIMP_TAC[RING_POW_POW; RING_PRODUCT] THEN AP_TERM_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The primitive element theorem: a finite separable extension is simple. In *)
(* such an extension an element a generates l over k exactly when the        *)
(* extensions to l of a homomorphism from k into an algebraically closed     *)
(* field take distinct values at a. Hence for a and b in a separable         *)
(* extension, a + c * b generates the same subfield as a and b for all but   *)
(* finitely many c in k, and over an infinite field a generator of the       *)
(* subfield generated by a finite set b can be found in the span of b. For   *)
(* finite fields see FINITE_FIELD_PRIMITIVE_ELEMENT.                         *)
(* ------------------------------------------------------------------------- *)

let PRIMITIVE_ELEMENT_EQ_SEPARATING_EMBEDDINGS = prove
 (`!(h:A->B) (g:A->C) k l m a.
        finite_extension (k,l) h /\ separable_extension (k,l) h /\
        algebraically_closed_field m /\ ring_homomorphism (k,m) g /\
        a IN ring_carrier l
        ==> (subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l <=>
             !f f'. f IN ring_homomorphism_extensions (k,l,m) (h,g) /\
                    f' IN ring_homomorphism_extensions (k,l,m) (h,g) /\
                    f a = f' a
                    ==> f = f')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:B->C`; `f':B->C`] THEN STRIP_TAC THEN
    MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier l:B->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `ring_carrier l =
      ring_carrier(subring_generated l
                    ((a:B) INSERT IMAGE (h:A->B) (ring_carrier k)))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED THEN
    EXISTS_TAC `m:C ring` THEN ASM_REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN
    ASM_MESON_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `algebraic_over (k,l) (h:A->B) a` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [algebraic_extension] o
      MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `K = subring_generated l ((a:B) INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
  SUBGOAL_THEN
   `finite_extension (k,K) (h:A->B) /\ field_extension (K,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SIMPLE_ALGEBRAIC_EXTENSION THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
      REWRITE_TAC[FIELD_EXTENSION_REFL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[field_extension];
        MATCH_MP_TAC FIELD_SIMPLE_ALGEBRAIC_EXTENSION THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[I_O_ID; IMAGE_I] (ISPECL
   [`h:A->B`; `I:B->B`; `k:A ring`; `K:B ring`; `l:B ring`]
   EXTENSION_DEGREE_EQ_TOWER)) THEN
  ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[SUBRING_GENERATED_SUPERSET] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]] THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
      EXTENSION_DEGREE_SIMPLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MINIMAL_POLYNOMIAL_DEG_LE_EXTENSION_DEGREE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`]
    HAS_SIZE_RING_HOMOMORPHISM_EXTENSIONS) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `K:B ring`; `m:C ring`]
    CARD_RING_HOMOMORPHISM_EXTENSIONS_LE) THEN
  MP_TAC(ISPECL [`h:A->B`; `g:A->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                 `a:B`] RING_HOMOMORPHISM_EXTENSIONS_SIMPLE) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
               HAS_SIZE] THEN
  ABBREV_TAC
   `R = {b | b IN ring_carrier m /\
             poly_eval m ((g:A->C) o minimal_polynomial (k,l) (h:A->B) a) b =
             ring_0 m}` THEN
  ABBREV_TAC `E = ring_homomorphism_extensions (k,l,m) (h:A->B,g:A->C)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE(R:C->bool) /\
    CARD R = CARD(ring_homomorphism_extensions (k,K,m) (h:A->B,g:A->C))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[CARD_FINITE_CONG; CARD_EQ_CARD_IMP; CARD_EQ_SYM]
     `!s:(B->C)->bool t:C->bool.
        s =_c t /\ FINITE s ==> FINITE t /\ CARD t = CARD s`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(IMAGE (\f:B->C. f a) E) = CARD(E:(B->C)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\f:B->C. f a) E SUBSET R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `f:B->C` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(f:B->C) IN E` THEN EXPAND_TAC "E" THEN
      REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
      STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC `l:B ring` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RING_HOMOMORPHISM_EXTENSIONS_ROOT THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\f:B->C. f a) E`; `R:C->bool`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PRIMITIVE_ELEMENT_TWO_GENERATORS =
  let lemma = prove
   (`!f x y u v w:A.
        field f /\ x IN ring_carrier f /\ y IN ring_carrier f /\
        u IN ring_carrier f /\ v IN ring_carrier f /\ w IN ring_carrier f /\
        ring_add f x (ring_mul f w u) = ring_add f y (ring_mul f w v) /\
        ~(w = ring_div f (ring_sub f y x) (ring_sub f u v))
        ==> x = y /\ u = v`,
    FIELD_TAC) in
  prove
   (`!(h:A->B) k l a b.
        separable_extension (k,l) h /\
        a IN ring_carrier l /\ b IN ring_carrier l
        ==> FINITE {c | c IN ring_carrier k /\
                        ~(subring_generated l
                           (ring_add l a (ring_mul l (h c) b) INSERT
                            IMAGE h (ring_carrier k)) =
                          subring_generated l
                           (a INSERT b INSERT IMAGE h (ring_carrier k)))}`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEPARABLE_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_EXTENSION_IMP_HOMOMORPHISM) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `{a:B,b}`]
      FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                      NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[SEPARABLE_IMP_ALGEBRAIC_EXTENSION; algebraic_extension];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (h:A->B) (ring_carrier k) UNION {a,b} =
      a INSERT b INSERT IMAGE h (ring_carrier k)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    ABBREV_TAC
     `L = subring_generated l
            ((a:B) INSERT b INSERT IMAGE (h:A->B) (ring_carrier k))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `ring_add L = ring_add (l:B ring) /\ ring_mul L = ring_mul l /\
      field_extension (L,l) (I:B->B)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[SUBRING_GENERATED] THEN
      MATCH_MP_TAC FIELD_EXTENSION_FROM_SUBRING_GENERATED THEN
      REWRITE_TAC[FIELD_EXTENSION_REFL] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[field_extension; FINITE_IMP_FIELD_EXTENSION];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(a:B) IN ring_carrier L /\ (b:B) IN ring_carrier L /\
      IMAGE (h:A->B) (ring_carrier k) SUBSET ring_carrier L /\
      subring_generated L (a INSERT b INSERT IMAGE h (ring_carrier k)) = L`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`l:B ring`;
                     `(a:B) INSERT b INSERT IMAGE (h:A->B) (ring_carrier k)`]
        SUBRING_GENERATED_SUBSET_CARRIER) THEN
      MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
        FIELD_EXTENSION_IMP_SUBSET) THEN
      MP_TAC(ISPECL [`l:B ring`;
                     `(a:B) INSERT b INSERT IMAGE (h:A->B) (ring_carrier k)`;
                     `(a:B) INSERT b INSERT IMAGE (h:A->B) (ring_carrier k)`]
        SUBRING_GENERATED_IDEMPOT) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `separable_extension (k,L) (h:A->B)` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`h:A->B`; `I:B->B`]
        SEPARABLE_EXTENSION_SUBFIELD) THEN
      EXISTS_TAC `l:B ring` THEN
      ASM_SIMP_TAC[I_O_ID; FINITE_IMP_FIELD_EXTENSION];
      ALL_TAC] THEN
    MP_TAC(ISPEC `k:A ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[field_extension]; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:(A#num)ring`; `g:A->A#num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
      MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `L:B ring`;
                   `m:(A#num)ring`] CARD_RING_HOMOMORPHISM_EXTENSIONS_LE) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN STRIP_TAC THEN
    ABBREV_TAC
     `E = ring_homomorphism_extensions (k,L,m) (h:A->B,g:A->A#num)` THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{c | c IN ring_carrier k /\
           (g:A->A#num) c IN
           {ring_div m (ring_sub m ((f':B->A#num) a) (f a))
                       (ring_sub m (f b) (f' b)) |
            f IN E /\ f' IN E}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ_GENERAL THEN CONJ_TAC THENL
       [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT2 o
          GEN_REWRITE_RULE I [ring_monomorphism]);
        MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `c:A` THEN
    ASM_CASES_TAC `(c:A) IN ring_carrier k` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(LABEL_TAC "good") THEN
    SUBGOAL_THEN
     `(h:A->B) c IN ring_carrier L /\
      ring_mul l ((h:A->B) c) b IN ring_carrier L /\
      ring_add l a (ring_mul l ((h:A->B) c) b) IN ring_carrier L`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `p /\ (p ==> q) /\ (q ==> r) ==> p /\ q /\ r`) THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MP_TAC(ISPECL [`L:B ring`; `(h:A->B) c`; `b:B`] RING_MUL);
        MP_TAC(ISPECL [`L:B ring`; `a:B`; `ring_mul l ((h:A->B) c) b`]
          RING_ADD)] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!f:B->A#num.
        f IN E
        ==> f(ring_add l a (ring_mul l ((h:A->B) c) b)) =
            ring_add m (f a) (ring_mul m (g c) (f b)) /\
            f a IN ring_carrier m /\ f b IN ring_carrier m`
    (LABEL_TAC "eval") THENL
     [EXPAND_TAC "E" THEN
      REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
      X_GEN_TAC `f:B->A#num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`L:B ring`; `m:(A#num)ring`; `f:B->A#num`]
        RING_HOMOMORPHISM_ADD) THEN
      MP_TAC(ISPECL [`L:B ring`; `m:(A#num)ring`; `f:B->A#num`]
        RING_HOMOMORPHISM_MUL) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      ASM_SIMP_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC `L:B ring` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`;
                   `ring_add l a (ring_mul l ((h:A->B) c) b) INSERT
                    IMAGE (h:A->B) (ring_carrier k)`;
                   `(a:B) INSERT b INSERT IMAGE (h:A->B) (ring_carrier k)`]
      SUBRING_GENERATED_IDEMPOT_GEN) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`h:A->B`; `g:A->A#num`; `k:A ring`; `L:B ring`;
                   `m:(A#num)ring`; `ring_add l a (ring_mul l ((h:A->B) c) b)`]
      PRIMITIVE_ELEMENT_EQ_SEPARATING_EMBEDDINGS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY X_GEN_TAC [`f:B->A#num`; `f':B->A#num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:(A#num)ring`; `(f:B->A#num) a`; `(f':B->A#num) a`;
                   `(f:B->A#num) b`; `(f':B->A#num) b`; `(g:A->A#num) c`]
      lemma) THEN
    REMOVE_THEN "good" (MP_TAC o SPECL [`f:B->A#num`; `f':B->A#num`]) THEN
    REMOVE_THEN "eval" (fun th ->
      MP_TAC(SPEC `f':B->A#num` th) THEN MP_TAC(SPEC `f:B->A#num` th)) THEN
    REWRITE_TAC[ASSUME `(f:B->A#num) IN E`; ASSUME `(f':B->A#num) IN E`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC)) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN
     `ring_homomorphism (L,m) (f:B->A#num) /\
      ring_homomorphism (L,m) (f':B->A#num) /\
      f IN EXTENSIONAL (ring_carrier L) /\
      f' IN EXTENSIONAL (ring_carrier L) /\
      (!x. x IN ring_carrier k ==> f((h:A->B) x) = (g:A->A#num) x) /\
      (!x. x IN ring_carrier k ==> f'((h:A->B) x) = (g:A->A#num) x)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(f:B->A#num) IN E` THEN
      UNDISCH_TAC `(f':B->A#num) IN E` THEN
      EXPAND_TAC "E" THEN
      REWRITE_TAC[ring_homomorphism_extensions; IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EXTENSIONAL_EQ THEN EXISTS_TAC `ring_carrier L:B->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `ring_carrier L =
      ring_carrier(subring_generated L
        ((a:B) INSERT b INSERT IMAGE (h:A->B) (ring_carrier k)))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED THEN
    EXISTS_TAC `m:(A#num)ring` THEN ASM_REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let PRIMITIVE_ELEMENT_INFINITE = prove
 (`!(h:A->B) k l b.
        separable_extension (k,l) h /\ INFINITE(ring_carrier k) /\
        FINITE b /\ b SUBSET ring_carrier l
        ==> ?a. a IN ring_span (k,l) h b /\
                subring_generated l (a INSERT IMAGE h (ring_carrier k)) =
                subring_generated l (IMAGE h (ring_carrier k) UNION b)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEPARABLE_IMP_FIELD_EXTENSION) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `ring_0 l:B` THEN
    REWRITE_TAC[RING_SPAN_0; SUBRING_GENERATED_INSERT_ZERO; UNION_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `s:B->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_SPAN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `x:B`; `y:B`]
    PRIMITIVE_ELEMENT_TWO_GENERATORS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY o
    MATCH_MP INFINITE_DIFF_FINITE o
    CONJ (ASSUME `INFINITE(ring_carrier k:A->bool)`)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_ELIM_THM;
              TAUT `p /\ ~(p /\ ~q) <=> p /\ q`] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ring_add l x (ring_mul l ((h:A->B) c) y)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_SPAN_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_SPAN_INC THEN ASM_REWRITE_TAC[IN_INSERT];
      MATCH_MP_TAC RING_SPAN_MUL THEN ASM_REWRITE_TAC[]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FIELD_EXTENSION_CARRIER THEN EXISTS_TAC `k:A ring` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `!y:B t u. y IN t /\ t SUBSET u ==> y IN u`) THEN
      EXISTS_TAC `ring_span (k,l) (h:A->B) s` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RING_SPAN_MONO THEN SET_TAC[]];
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_INSERT] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBRING_GENERATED_INSERT] THEN
    AP_TERM_TAC THEN SET_TAC[]]);;

let PRIMITIVE_ELEMENT_GENSET = prove
 (`!(h:A->B) k l b.
        separable_extension (k,l) h /\ FINITE b /\ b SUBSET ring_carrier l
        ==> ?a. a IN ring_carrier l /\
                subring_generated l (a INSERT IMAGE h (ring_carrier k)) =
                subring_generated l (IMAGE h (ring_carrier k) UNION b)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `FINITE(ring_carrier k:A->bool)` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B->bool`]
      PRIMITIVE_ELEMENT_INFINITE) THEN
    ASM_REWRITE_TAC[INFINITE] THEN MESON_TAC[RING_SPAN_SUBSET; SUBSET]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEPARABLE_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B->bool`]
    FINITE_FINITELY_GENERATED_ALGEBRAIC_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SEPARABLE_IMP_ALGEBRAIC_EXTENSION; algebraic_extension;
                  SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `IMAGE (h:A->B) (ring_carrier k) UNION b`]
    SUBRING_GENERATED_SUBSET_CARRIER) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
    FIELD_EXTENSION_IMP_SUBSET) THEN
  ABBREV_TAC
   `L = subring_generated l (IMAGE (h:A->B) (ring_carrier k) UNION b)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `L:B ring`]
    FINITE_FIELD_PRIMITIVE_ELEMENT) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[FINITE_FINITE_FIELD_EXTENSION; field_extension];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:B` THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `(a:B) INSERT IMAGE (h:A->B) (ring_carrier k)`;
                 `IMAGE (h:A->B) (ring_carrier k) UNION b`]
    SUBRING_GENERATED_IDEMPOT_GEN) THEN
  ASM_REWRITE_TAC[INSERT_SUBSET] THEN ANTS_TAC THENL
   [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_MESON_TAC[RING_CARRIER_SUBRING_GENERATED_SUBSET; SUBSET]);;

let PRIMITIVE_ELEMENT_THEOREM = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h /\ separable_extension (k,l) h
        ==> ?a. a IN ring_carrier l /\
                subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_EXTENSION]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `b:B->bool`]
    PRIMITIVE_ELEMENT_GENSET) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_REWRITE_TAC[SUBRING_GENERATED_SUPERSET] THEN
  ASM_MESON_TAC[RING_SPAN_SUBSET_SUBRING_GENERATED; SUBSET_TRANS]);;

let PRIMITIVE_ELEMENT_THEOREM_EQ = prove
 (`!(h:A->B) k l.
        finite_extension (k,l) h /\ separable_extension (k,l) h <=>
        field_extension (k,l) h /\
        ?a. separable_element (k,l) h a /\
            subring_generated l (a INSERT IMAGE h (ring_carrier k)) = l`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_SIMP_TAC[FINITE_IMP_FIELD_EXTENSION] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`]
      PRIMITIVE_ELEMENT_THEOREM) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ASM_MESON_TAC[separable_extension];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `algebraic_over (k,l) (h:A->B) a` ASSUME_TAC THENL
     [ASM_MESON_TAC[SEPARABLE_ELEMENT_IMP_ALGEBRAIC; field_extension];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
      SEPARABLE_EXTENSION_SIMPLE) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
      FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let SEPARABLE_EXTENSION_BOUNDED_DEGREE = prove
 (`!(h:A->B) k l n.
        separable_extension(k,l) h /\
        (!x. x IN ring_carrier l
             ==> poly_deg k (minimal_polynomial(k,l) h x) <= n)
        ==> finite_extension(k,l) h /\ extension_degree(k,l) h <= n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SEPARABLE_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `!s. FINITE s /\ ring_independent(k,l) (h:A->B) s ==> CARD s <= n`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:B->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_INDEPENDENT_IMP_SUBSET) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`]
      PRIMITIVE_ELEMENT_GENSET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:B` (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o AP_TERM `ring_carrier:B ring->B->bool`))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `algebraic_over(k,l) (h:A->B) a` ASSUME_TAC THENL
     [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
      MINIMAL_POLYNOMIAL) THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `a:B`]
      MINIMAL_POLYNOMIAL_POWERS_HAS_SIZE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `!x. x IN ring_carrier l
          ==> poly_deg k (minimal_polynomial(k,l) (h:A->B) x) <= n` THEN
    DISCH_THEN(MP_TAC o SPEC `a:B`) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `p = minimal_polynomial (k,l) (h:A->B) a` THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`; `a:B`]
      RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN) THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES] THEN DISCH_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `poly_deg k (p:(1->num)->A)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_SIZE] o
                  check (is_binary "HAS_SIZE" o concl)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MP_TAC(ISPECL
     [`h:A->B`; `k:A ring`; `l:B ring`; `s:B->bool`;
      `{ring_pow l (a:B) i | i < poly_deg k (p:(1->num)->A)}`]
     RING_INDEPENDENT_LE_SPAN) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[RING_POW];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `IMAGE (h:A->B) (ring_carrier k) UNION s`]
      SUBRING_GENERATED_SUBSET_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. ring_independent(k,l) (h:A->B) s ==> FINITE s /\ CARD s <= n`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:B->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `FINITE(s:B->bool)` THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`n + 1`; `s:B->bool`] CHOOSE_SUBSET_STRONG) THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:B->bool`) THEN
    ASM_MESON_TAC[RING_INDEPENDENT_MONO; ARITH_RULE `~(n + 1 <= n)`];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_EXTENSION_BASIS] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] RING_BASIS_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ring_basis];
    MATCH_MP_TAC EXTENSION_DEGREE_LE_INDEPENDENT_BOUND THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Existence and uniqueness of finite fields. In an algebraically closed     *)
(* field of prime characteristic p the solutions of x^(p^n) = x form a       *)
(* subfield with p^n elements: the fixed points of an iterate of the         *)
(* Frobenius map, namely 0 and the (p^n - 1)-th roots of unity. So for every *)
(* prime p and n >= 1 there is a field with p^n elements, on any set of that *)
(* size. A finite field l with q elements is a splitting extension of the    *)
(* separable polynomial X^q - X over every subfield, since all its elements  *)
(* are roots; applied over the prime subfields, two finite fields with the   *)
(* same number of elements are isomorphic.                                   *)
(* ------------------------------------------------------------------------- *)

(* The fixed points of x |-> x^(p^n) are 0 and the (p^n - 1)-th roots of     *)
(* unity, of which there are p^n - 1 since p does not divide p^n - 1.        *)
let ALGEBRAICALLY_CLOSED_FIELD_FINITE_SUBFIELD = prove
 (`!(r:A ring) n.
        algebraically_closed_field r /\ prime(ring_char r) /\ ~(n = 0)
        ==> {x | x IN ring_carrier r /\ ring_pow r x (ring_char r EXP n) = x}
            subfield_of r /\
            {x | x IN ring_carrier r /\ ring_pow r x (ring_char r EXP n) = x}
            HAS_SIZE (ring_char r EXP n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `\x:A. ring_pow r x (ring_char r EXP n)`]
      SUBFIELD_OF_FIXPOINTS) THEN
    ASM_SIMP_TAC[RING_ENDOMORPHISM_FROBENIUS_ITERATE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ring_char(r:A ring) EXP n - 1`]
    ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY) THEN
  ABBREV_TAC `p = ring_char(r:A ring)` THEN
  SUBGOAL_THEN `~(p divides p EXP n - 1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIVIDES_SUB_1; EXP_EQ_0; PRIME_IMP_NZ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p divides 1` MP_TAC THENL
     [MATCH_MP_TAC(NUMBER_RULE
       `!x. (x:num == 1) (mod p) /\ p divides x ==> p divides 1`) THEN
      EXISTS_TAC `p EXP n` THEN ASM_SIMP_TAC[DIVIDES_REXP; DIVIDES_REFL];
      ASM_MESON_TAC[DIVIDES_ONE; PRIME_1]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `p EXP n = SUC(p EXP n - 1)` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(m = 0) ==> m = SUC(m - 1)`) THEN
    ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ];
    ABBREV_TAC `m = p EXP n - 1` THEN DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(MESON[HAS_SIZE_CLAUSES]
   `!s t (a:A) m. ~(a IN t) /\ s = a INSERT t
                  ==> t HAS_SIZE m ==> s HAS_SIZE SUC m`) THEN
  EXISTS_TAC `ring_0 r:A` THEN
  REWRITE_TAC[IN_ELIM_THM; RING_POW_ZERO; EXTENSION; IN_INSERT] THEN
  CONJ_TAC THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[FIELD_NONTRIVIAL] THEN
    ASM_MESON_TAC[DIVIDES_0];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `x:A = ring_0 r` THEN
  ASM_REWRITE_TAC[RING_0; RING_POW_ZERO; NOT_SUC] THEN
  ASM_CASES_TAC `(x:A) IN ring_carrier r` THEN ASM_REWRITE_TAC[ring_pow] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[RING_MUL_RID] THEN
  MATCH_MP_TAC(ISPEC `r:A ring` INTEGRAL_DOMAIN_MUL_LCANCEL) THEN
  EXISTS_TAC `x:A` THEN
  ASM_SIMP_TAC[RING_POW; RING_1; RING_MUL_RID; FIELD_IMP_INTEGRAL_DOMAIN]);;

(* The field is built inside an algebraic closure of integer_mod_ring p.     *)
let FINITE_FIELD_EXISTS = prove
 (`!p n. prime p /\ ~(n = 0)
         ==> ?k:(int#num)ring. field k /\ ring_carrier k HAS_SIZE (p EXP n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `integer_mod_ring p` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:(int#num)ring`; `f:int->int#num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ring_char(r:(int#num)ring) = p` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP ALGEBRAIC_IMP_FIELD_EXTENSION) THEN
    REWRITE_TAC[field_extension] THEN
    MESON_TAC[RING_CHAR_MONOMORPHIC_IMAGE; INTEGER_MOD_RING_CHAR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:(int#num)ring`; `n:num`]
    ALGEBRAICALLY_CLOSED_FIELD_FINITE_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC
   `subfield_generated r
     {x:int#num | x IN ring_carrier r /\ ring_pow r x (p EXP n) = x}` THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; CARRIER_SUBFIELD_GENERATED_SUBFIELD;
               ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD]);;

(* Any set with p^n elements carries a field structure (an isomorphic copy,  *)
(* ISOMORPHIC_COPY_OF_RING).                                                 *)
let FINITE_FIELD_EXISTS_GEN = prove
 (`!p n (s:A->bool).
        prime p /\ ~(n = 0) /\ s HAS_SIZE p EXP n
        ==> ?k. field k /\ ring_carrier k = s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `n:num`] FINITE_FIELD_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:(int#num)ring` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:(int#num)ring`; `s:A->bool`] ISOMORPHIC_COPY_OF_RING) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[CARD_EQ_CARD] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[ISOMORPHIC_RING_FIELDNESS]);;

(* The polynomial X^n - X: for n >= 2 a nonzero polynomial of degree n; its  *)
(* values under a homomorphism.                                              *)
let POLY_VAR_POW_SUB_VAR = prove
 (`!(r:A ring) n.
        ~(ring_1 r = ring_0 r) /\ 2 <= n
        ==> poly_sub r (poly_pow r (poly_var r one) n) (poly_var r one) IN
            ring_carrier(poly_ring r (:1)) /\
            poly_deg r (poly_sub r (poly_pow r (poly_var r one) n)
                                   (poly_var r one)) = n /\
            ~(poly_sub r (poly_pow r (poly_var r one) n) (poly_var r one) =
              poly_0 r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
  SUBGOAL_THEN
   `poly_deg r (poly_sub r (poly_pow r (poly_var r one) n) (poly_var r one)
                :(1->num)->A) = n`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_SUB o lhand o snd) THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
                 POLY_DEG_VAR_POW; POLY_DEG_VAR] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW;
                 RING_POLYNOMIAL_VAR] THEN
    DISCH_THEN(MP_TAC o AP_TERM `poly_deg (r:A ring):((1->num)->A)->num`) THEN
    ASM_REWRITE_TAC[POLY_DEG_0] THEN ASM_ARITH_TAC]);;

let POLY_EVAL_VAR_POW_SUB_VAR = prove
 (`!(h:A->B) k l n x.
        ring_homomorphism(k,l) h /\ x IN ring_carrier l
        ==> poly_eval l (h o poly_sub k (poly_pow k (poly_var k one) n)
                                        (poly_var k one)) x =
            ring_sub l (ring_pow l x n) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_eval] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP POLY_EXTEND_EVALUATE th)]) THEN
  ASM_SIMP_TAC[POLY_EXTEND_SUB; POLY_EXTEND_VARPOW; POLY_EXTEND_VAR;
               RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR]);;

let MONIC_VAR_POW_SUB_VAR = prove
 (`!(r:A ring) n.
        ~(ring_1 r = ring_0 r) /\ 2 <= n
        ==> monic r (poly_sub r (poly_pow r (poly_var r one) n)
                                (poly_var r one))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[monic] THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`] POLY_VAR_POW_SUB_VAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COEFF_POLY_SUB; COEFF_POLY_VARPOW; COEFF_POLY_VAR] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[RING_SUB_RZERO; RING_1]);;

let POLY_SEPARABLE_VAR_POW_SUB_VAR = prove
 (`!(r:A ring) n.
        ring_char r divides n
        ==> poly_separable r
              (poly_sub r (poly_pow r (poly_var r one) n) (poly_var r one))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poly_separable] THEN
  SIMP_TAC[POLY_DERIV_SUB; RING_POWERSERIES_POW; RING_POWERSERIES_VAR] THEN
  ASM_SIMP_TAC[POLY_DERIV_VAR_POW_ZERO; POLY_DERIV_VAR; POLY_CONST_1] THEN
  MATCH_MP_TAC(CONJUNCT2 RING_COPRIME_UNIT) THEN
  REWRITE_TAC[POLY_CLAUSES] THEN
  SIMP_TAC[RING_SUB_LZERO; RING_1; RING_UNIT_NEG; RING_UNIT_1] THEN
  REWRITE_TAC[GSYM POLY_CLAUSES; GSYM RING_POLYNOMIAL] THEN
  SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR]);;

let POLY_SEPARABLE_VAR_POW_SUB_CONST = prove
 (`!(r:A ring) n c.
        field r /\ ~(ring_char r divides n) /\
        c IN ring_carrier r /\ ~(c = ring_0 r)
        ==> poly_separable r
             (poly_sub r (poly_pow r (poly_var r one) n) (poly_const r c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[DIVIDES_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_of_num r n:A = ring_0 r)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_NUM_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[poly_separable] THEN
  MP_TAC(ISPECL [`poly_ring (r:A ring) (:1)`] BEZOUT_RING_COPRIME) THEN
  ASM_SIMP_TAC[PID_POLY_RING; PID_IMP_BEZOUT_RING] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `!p q. poly_sub (r:A ring) p q = ring_sub (poly_ring r (:1)) p q`
  ASSUME_TAC THENL
   [REWRITE_TAC[ring_sub; POLY_RING; POLY_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_deriv r (poly_sub r (poly_pow r (poly_var r one) n) (poly_const r c))
    = ring_mul (poly_ring r (:1)) (poly_const r (ring_of_num r n))
               (ring_pow (poly_ring r (:1)) (poly_var r one) (n - 1)):
      (1->num)->A`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) POLY_DERIV_SUB o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THENL
       [MP_TAC(ISPECL [`poly_ring (r:A ring) (:1)`; `poly_var (r:A ring) one`;
                       `n:num`] RING_POW) THEN
        REWRITE_TAC[POLY_VAR_UNIV; GSYM POLY_POW_ALT] THEN
        SIMP_TAC[POLY_RING; IN_ELIM_THM];
        ASM_REWRITE_TAC[RING_POLYNOMIAL_CONST]];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[POLY_DERIV_VAR_POW; POLY_DERIV_CONST; POLY_POW_ALT] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SYM(ISPECL [`r:A ring`; `(:1)`] (el 5 (CONJUNCTS POLY_RING)));
                SYM(ISPECL [`r:A ring`; `(:1)`] (el 1 (CONJUNCTS POLY_RING)))]
    THEN MATCH_MP_TAC RING_SUB_RZERO THEN MATCH_MP_TAC RING_MUL THEN
    SIMP_TAC[RING_POW; POLY_VAR_UNIV; POLY_CONST; RING_OF_NUM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[POLY_POW_ALT] THEN
  SUBGOAL_THEN
   `!a b:A. a IN ring_carrier r /\ b IN ring_carrier r /\
            ring_mul r a b = ring_1 r
            ==> ring_mul (poly_ring r (:1)) (poly_const r a) (poly_const r b) =
                ring_1 (poly_ring r (:1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[ISPECL [`r:A ring`; `(:1)`] (el 5 (CONJUNCTS POLY_RING));
                ISPECL [`r:A ring`; `(:1)`] (el 2 (CONJUNCTS POLY_RING))] THEN
    ASM_SIMP_TAC[GSYM POLY_CONST_MUL; POLY_CONST_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_pow (poly_ring r (:1)) (poly_var r one) n:(1->num)->A =
    ring_mul (poly_ring r (:1))
     (ring_pow (poly_ring r (:1)) (poly_var r one) (n - 1)) (poly_var r one)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`poly_ring (r:A ring) (:1)`; `poly_var (r:A ring) one`;
                   `n - 1`; `1`] RING_POW_ADD) THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1; POLY_VAR_UNIV; RING_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:A. a IN ring_carrier r
          ==> poly_const r a IN ring_carrier(poly_ring r (:1))`
  ASSUME_TAC THENL [REWRITE_TAC[POLY_CONST]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_SUB; RING_MUL; RING_POW; POLY_VAR_UNIV];
    ASM_SIMP_TAC[RING_MUL; RING_POW; POLY_VAR_UNIV; RING_OF_NUM];
    ALL_TAC] THEN
  EXISTS_TAC
   `ring_neg (poly_ring r (:1)) (poly_const r (ring_inv r c)):(1->num)->A` THEN
  EXISTS_TAC
   `ring_mul (poly_ring r (:1))
     (ring_mul (poly_ring r (:1)) (poly_const r (ring_inv r c))
       (poly_const r (ring_inv r (ring_of_num r n)))) (poly_var r one):
    (1->num)->A` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RING_NEG THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_INV];
    MATCH_MP_TAC RING_MUL THEN REWRITE_TAC[POLY_VAR_UNIV] THEN
    MATCH_MP_TAC RING_MUL THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_INV; RING_OF_NUM];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (GEN_ALL (RING_RULE
     `ring_mul (R:Z ring) a b = ring_1 R /\ ring_mul R m w = ring_1 R
      ==> ring_add R (ring_mul R (ring_sub R (ring_mul R y x) a)
                                  (ring_neg R b))
                     (ring_mul R (ring_mul R m y)
                                 (ring_mul R (ring_mul R b w) x)) =
          ring_1 R`))) THEN
    REPEAT CONJ_TAC THEN ASM_SIMP_TAC[RING_POW; POLY_VAR_UNIV] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_INV; RING_OF_NUM; FIELD_MUL_RINV]]);;

let KUMMER_ROOTS_SEPARABLY_CLOSED = prove
 (`!(h:A->B) k l n.
        field_extension(k,l) h /\
        {x | x IN ring_carrier k /\ ring_pow k x n = ring_1 k} HAS_SIZE n /\
        (!p. p IN ring_carrier(poly_ring l (:1)) /\ poly_separable l p /\
             ~(poly_deg l p = 0)
             ==> ?x. x IN ring_carrier l /\ poly_eval l p x = ring_0 l)
        ==> ~(n = 0) /\
            !a. a IN ring_carrier k /\ ~(a = ring_0 k)
                ==> ?b. b IN ring_carrier l /\ ring_pow l b n = h a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ring_monomorphism]) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ROOTS_OF_UNITY_HAS_SIZE_NONZERO]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `~(ring_char(l:B ring) divides n)` ASSUME_TAC THENL
   [SUBGOAL_THEN `ring_char(l:B ring) = ring_char(k:A ring)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_CHAR_MONOMORPHIC_IMAGE THEN
      EXISTS_TAC `h:A->B` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ROOTS_OF_UNITY_HAS_SIZE_IMP_CHAR THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]];
    ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:A->B) a IN ring_carrier l /\ ~(h a = ring_0 l)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_HOMOMORPHISM_0; RING_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `poly_sub l (poly_pow l (poly_var l one) n) (poly_const l ((h:A->B) a))`)
  THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[POLY_SEPARABLE_VAR_POW_SUB_CONST] THEN
    MP_TAC(ISPECL [`l:B ring`; `n:num`; `(h:A->B) a`]
                  POLY_VAR_POW_SUB_CONST) THEN
    ASM_SIMP_TAC[FIELD_NONTRIVIAL];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:B` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`I:B->B`; `l:B ring`; `l:B ring`; `n:num`; `(h:A->B) a`;
                   `b:B`] POLY_EVAL_VAR_POW_SUB_CONST) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_I; I_O_ID; I_THM] THEN
    DISCH_THEN(MP_TAC o SYM) THEN ASM_SIMP_TAC[RING_SUB_EQ_0; RING_POW]]);;

let FINITE_FIELD_SPLITTING_EXTENSION = prove
 (`!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> splitting_extension(k,l) h
              (poly_sub k (poly_pow k (poly_var k one) (CARD(ring_carrier l)))
                          (poly_var k one)) /\
            poly_separable k
              (poly_sub k (poly_pow k (poly_var k one) (CARD(ring_carrier l)))
                          (poly_var k one))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ABBREV_TAC `q = CARD(ring_carrier(l:B ring))` THEN
  ABBREV_TAC
   `p = poly_sub k (poly_pow k (poly_var k one) q) (poly_var k one)
        :(1->num)->A` THEN
  SUBGOAL_THEN `2 <= q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[FINITE_FIELD_CARD_GE_2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `q:num`] POLY_VAR_POW_SUB_VAR) THEN
  ASM_SIMP_TAC[FIELD_NONTRIVIAL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `p:(1->num)->A`;
                 `ring_carrier l:B->bool`] POLY_SPLITS_OVER_DISTINCT_ROOTS) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN ANTS_TAC THENL
   [EXPAND_TAC "p" THEN ASM_SIMP_TAC[POLY_EVAL_VAR_POW_SUB_VAR] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:B ring`; `x:B`] FINITE_INTEGRAL_DOMAIN_POW_CARD) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_SUB_REFL];
    STRIP_TAC THEN ASM_REWRITE_TAC[splitting_extension]] THEN
  MATCH_MP_TAC(MESON[SUBFIELD_GENERATED_RING_CARRIER]
   `s = ring_carrier l ==> subfield_generated l s = l:B ring`) THEN
  MATCH_MP_TAC(SET_RULE `(s:B->bool) SUBSET t ==> s UNION t = t`) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]);;

(* Both fields are splitting extensions of X^q - X over the prime subfield   *)
(* of k, embedded in l by PRIME_SUBFIELD_HOMOMORPHISM_EXISTS.                *)
let ISOMORPHIC_FINITE_FIELDS = prove
 (`!(k:A ring) (l:B ring).
        field k /\ field l /\
        FINITE(ring_carrier k) /\ FINITE(ring_carrier l) /\
        CARD(ring_carrier k) = CARD(ring_carrier l)
        ==> k isomorphic_ring l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_char(k:A ring) = ring_char(l:B ring)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:A ring` FINITE_INTEGRAL_DOMAIN_SIZE) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `m:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_char(k:A ring) divides p EXP m /\
      ring_char(l:B ring) divides p EXP m`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_CHAR_DIVIDES_ORDER]; ALL_TAC] THEN
    SUBGOAL_THEN `prime(ring_char(k:A ring)) /\ prime(ring_char(l:B ring))`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[FINITE_INTEGRAL_DOMAIN_CHAR; FIELD_IMP_INTEGRAL_DOMAIN];
      ALL_TAC] THEN
    SUBGOAL_THEN `ring_char(k:A ring) = p /\ ring_char(l:B ring) = p`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_PRIME_PRIME];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`]
    PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `j:A->B`) THEN
  ABBREV_TAC `k0 = subfield_generated k {ring_0 k:A}` THEN
  MP_TAC(ISPECL
   [`I:A->A`; `j:A->B`; `k0:A ring`; `k:A ring`; `l:B ring`;
    `poly_sub k0 (poly_pow k0 (poly_var k0 one) (CARD(ring_carrier(k:A ring))))
                 (poly_var k0 one):(1->num)->A`]
   SPLITTING_EXTENSION_UNIQUE) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`I:A->A`; `k0:A ring`; `k:A ring`]
      FINITE_FIELD_SPLITTING_EXTENSION) THEN
    EXPAND_TAC "k0" THEN ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED];
    MP_TAC(ISPECL [`j:A->B`; `k0:A ring`; `l:B ring`]
      FINITE_FIELD_SPLITTING_EXTENSION) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    SUBGOAL_THEN `field(k0:A ring)` ASSUME_TAC THENL
     [EXPAND_TAC "k0" THEN ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[field_extension] THEN
    MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING]]);;
