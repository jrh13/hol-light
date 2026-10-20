(* ========================================================================= *)
(* 4CT/part_converse.ml                                                      *)
(*                                                                           *)
(* part.v, the FitConversePart section: FITP_CONVERSE (Gonthier              *)
(* part.v:1157).  A part fitting exactly at a hub x yields, via              *)
(* converse_part, a (range, part) pair fitting tightly at the reflected hub  *)
(* inv_face2 (edge (face (face x))) across the third spoke; discharge.ml     *)
(* (DBOUND2_LEQ) uses it.                                                    *)
(*                                                                           *)
(* Method: all dart and arity identities of the proof are consequences of    *)
(* the hypermap relations e^2 = 1, n^3 = 1, e n f = 1 (which hold            *)
(* universally, since the maps fix the non-darts) plus one orbit relation    *)
(* f^a s = s (a = arity s) per spoke.  Eliminating f (f = n n e) gives a     *)
(* confluent rewrite system (normal forms of the free product of Z2 and Z3), *)
(* so NORM_TAC decides the universal identities; the orbit relation enters   *)
(* through ITER_EN_FACE_SUBN (k backward steps = a-k forward steps).         *)
(* ========================================================================= *)

needs "4CT/embed_prelim.ml";;    (* CUBIC_EQ_U *)
needs "4CT/part_mirror.ml";;

(* inv_face2 is the inverse of f o f: both compositions cancel               *)
(* unconditionally (faceK, nodeK).                                           *)
let INV_FACE2_FF = prove
 (`!(G:(A)hypermap) z. inv_face2 G (face_map G (face_map G z)) = z`,
  REWRITE_TAC[inv_face2; faceK]);;
let FF_INV_FACE2 = prove
 (`!(G:(A)hypermap) z. face_map G (face_map G (inv_face2 G z)) = z`,
  REWRITE_TAC[inv_face2; nodeK]);;
(* inv_face2 keeps the dart set.                                             *)
let INV_FACE2_IN_DART = prove
 (`!(G:(A)hypermap) x. x IN dart G ==> inv_face2 G x IN dart G`,
  REWRITE_TAC[inv_face2] THEN MESON_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART]);;

(* pentagonal gives every dart arity >= 5 = mem_range Pr59.                  *)
let PENTA_PR59 = prove
 (`!(G:(A)hypermap) w. pentagonal G /\ w IN dart G ==>
 mem_range Pr59 (arity G w)`,
  REWRITE_TAC[pentagonal; mem_range] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The maps of a hypermap permute the darts, so they fix the non-darts       *)
(* (MAPS_OUTSIDE_DART), and the plain and cubic identities hold              *)
(* unconditionally (CFT_PLAIN_EE, CFT_PLAIN_NF, CUBIC_EQ_U and the lemmas    *)
(* below), without an IN dart hypothesis: this is what makes pure rewriting  *)
(* decide the dart identities.                                               *)
(* ------------------------------------------------------------------------- *)

(* f(e x) = n(n x) (GSYM CUBIC_EQ', unconditional).                          *)
let FE_NN_U = prove
 (`!(G:(A)hypermap). cubic_hypermap G
     ==> !x. face_map G (edge_map G x) = node_map G (node_map G x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:A) IN dart G` THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CUBIC_EQ' THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MAPS_OUTSIDE_DART]]);;
(* f-elimination: f = n n e (Gonthier's fEnne).                              *)
let F_NNE_U = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G
     ==> !x. face_map G x = node_map G (node_map G (edge_map G x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `edge_map G (x:A)` o MATCH_MP FE_NN_U) THEN
  ASM_SIMP_TAC[CFT_PLAIN_EE]);;
let ARITY_FACE_U = prove
 (`!(G:(A)hypermap) x. arity G (face_map G x) = arity G x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(x:A) IN dart G` THEN
  ASM_SIMP_TAC[ARITY_FACE; MAPS_OUTSIDE_DART]);;
(* e o n = f^-1 preserves arity.                                             *)
let ARITY_EN_U = prove
 (`!(G:(A)hypermap) x. arity G (edge_map G (node_map G x)) = arity G x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(x:A) IN dart G` THEN
  ASM_SIMP_TAC[ARITY_EN; MAPS_OUTSIDE_DART]);;
(* n n = f e, so arity (n (n w)) = arity (e w).                              *)
let ARITY_NN_E_U = prove
 (`!(G:(A)hypermap). cubic_hypermap G
     ==> !w. arity G (node_map G (node_map G w)) = arity G (edge_map G w)`,
  SIMP_TAC[GSYM FE_NN_U; ARITY_FACE_U]);;

(* ------------------------------------------------------------------------- *)
(* Dart membership through map chains, unconditionally (the maps permute     *)
(* dart and fix non-darts), so a membership goal of any depth rewrites to `x *)
(* IN dart G` -- unlike ASM_SIMP's conditional rewriting which gives out.    *)
(* ------------------------------------------------------------------------- *)

let EDGE_IN_DART_EQ = prove
 (`!(G:(A)hypermap) w. edge_map G w IN dart G <=> w IN dart G`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(w:A) IN dart G` THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART; MAPS_OUTSIDE_DART]);;
let NODE_IN_DART_EQ = prove
 (`!(G:(A)hypermap) w. node_map G w IN dart G <=> w IN dart G`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(w:A) IN dart G` THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; MAPS_OUTSIDE_DART]);;
let FACE_IN_DART_EQ = prove
 (`!(G:(A)hypermap) w. face_map G w IN dart G <=> w IN dart G`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(w:A) IN dart G` THEN
  ASM_SIMP_TAC[FACE_MAP_IN_DART; MAPS_OUTSIDE_DART]);;
let ITER_FACE_IN_DART_EQ = prove
 (`!(G:(A)hypermap) k w. ITER k (face_map G) w IN dart G <=> w IN dart G`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; FACE_IN_DART_EQ]);;
let IN_DART_EQS =
  [EDGE_IN_DART_EQ; NODE_IN_DART_EQ; FACE_IN_DART_EQ; ITER_FACE_IN_DART_EQ;
   INV_FACE2_IN_DART];;

(* Close `mem_range Pr59 (arity G w)` for any map-chain w over a dart.       *)
let PENTA_TAC = MATCH_MP_TAC PENTA_PR59 THEN ASM_REWRITE_TAC IN_DART_EQS;;

(* NORM_TAC: a confluent rewriting normaliser for e/n/f words and arity      *)
(* atoms, requiring plain_hypermap G and cubic_hypermap G among the          *)
(* assumptions.  Rules: ITER numerals 1..8; o; inv_face2; f z -> n (n (e z)) *)
(* (F_NNE_U); e (e z) -> z; n (n (n z)) -> z; arity (n (n w)) -> arity (e    *)
(* w); arity (e (n w)) -> arity w.  The dart words become normal forms of    *)
(* the free product of Z2 and Z3, so two words denote the same dart in all   *)
(* plain cubic hypermaps iff they normalise identically, and arity atoms are *)
(* reduced to a canonical representative of their f-coset.  Both the goal    *)
(* and the assumptions are normalised.                                       *)
let NORM_TAC =
  FIRST_ASSUM(fun pl -> FIRST_ASSUM(fun cu ->
    let rls = [ITER_1; ITER2; ITER3; ITER4; ITER5; ITER6; ITER7; ITER8; o_THM;
               inv_face2; MATCH_MP F_NNE_U (CONJ pl cu);
               MATCH_MP CUBIC_EQ_U cu; MATCH_MP CFT_PLAIN_EE pl;
               MATCH_MP ARITY_NN_E_U cu; ARITY_EN_U] in
    RULE_ASSUM_TAC(REWRITE_RULE rls) THEN REWRITE_TAC rls));;

(* ------------------------------------------------------------------------- *)
(* The orbit relation: k backward steps around the face of s equal arity s - *)
(* k forward steps (f^-1 = e o n). This is the ONLY non-universal ingredient *)
(* (Gonthier's iter_face_subn).                                              *)
(* ------------------------------------------------------------------------- *)

let ITER_EN_FACE_CANCEL = prove
 (`!(G:(A)hypermap) k y.
     ITER k (edge_map G o node_map G) (ITER k (face_map G) y) = y`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM ITER_COMMUTE] THEN REWRITE_TAC[o_THM; faceK] THEN
  ASM_REWRITE_TAC[]);;
let ITER_EN_FACE_SUBN = prove
 (`!(G:(A)hypermap) s k. s IN dart G /\ k <= arity G s
     ==> ITER k (edge_map G o node_map G) s =
     ITER (arity G s - k) (face_map G) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
 `ITER k (face_map G) (ITER (arity G s - k) (face_map G) (s:A)) = s`
 MP_TAC THENL
   [REWRITE_TAC[ITER_ADD] THEN
    SUBGOAL_THEN `k + (arity G (s:A) - k) = arity G s` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[ITER_FACE_ARITY]]; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[ITER_EN_FACE_CANCEL]);;

(* ------------------------------------------------------------------------- *)
(* The two wraparound identities of FITP_CONVERSE. Writing s for the spoke   *)
(* dart (e (f x) resp. e (f (f (f x)))), the reflected hat atom is f^-1 of e *)
(* ((e o n)^k s), i.e. of e (f^(arity s - k) s): converting the k backward   *)
(* steps with ITER_EN_FACE_SUBN makes the identity universal, so NORM_TAC    *)
(* closes it.                                                                *)
(* ------------------------------------------------------------------------- *)

let WRAP_H45 = prove
 (`!(G:(A)hypermap) x. plain_hypermap G /\ cubic_hypermap G /\ x IN dart G /\
       3 <= arity G (edge_map G (face_map G x))
     ==>
 arity G (edge_map G (face_map G (face_map G (edge_map G
                                              (face_map G (face_map G
                   (edge_map G (face_map G (face_map G x))))))))) =
         arity G (edge_map G (ITER (arity G (edge_map G (face_map G x)) - 3)
                              (face_map G)
                   (edge_map G (face_map G x))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `edge_map G (face_map G (x:A))`; `3`]
         ITER_EN_FACE_SUBN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART; FACE_MAP_IN_DART]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ITER3; o_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ARITY_FACE_U] THEN NORM_TAC);;

let WRAP_H34 = prove
 (`!(G:(A)hypermap) x. plain_hypermap G /\ cubic_hypermap G /\ x IN dart G /\
       2 <= arity G (edge_map G (face_map G (face_map G (face_map G x))))
     ==>
 arity G (edge_map G (face_map G (face_map G (edge_map G
                                              (face_map G (face_map G
                   (face_map G (face_map G x)))))))) =
         arity G (edge_map G (ITER (arity G (edge_map G
                                 (face_map G (face_map G (face_map G x)))) - 2)
                   (face_map G)
                   (edge_map G (face_map G (face_map G (face_map G x))))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`G:(A)hypermap`;
                `edge_map G (face_map G (face_map G (face_map G (x:A))))`; `2`]
         ITER_EN_FACE_SUBN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC IN_DART_EQS; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ITER2; o_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ARITY_FACE_U] THEN NORM_TAC);;

(* ------------------------------------------------------------------------- *)
(* The uniform atom closer. After the part case analysis every goal is a     *)
(* single fitp atom (mem_range r (arity G w), or fitp q G w) with the        *)
(* x-frame atoms as assumptions. WRAP_CLOSE weqs: expand ranges/sizes/ITER   *)
(* numerals, rewrite with the wraparound equations, substitute the one known *)
(* arity numeral (so ITER (n - k) becomes a numeral), normalize everything   *)
(* and close by assumption matching, pentagonality, or range evaluation.     *)
(* ------------------------------------------------------------------------- *)

let NUM_SUBST_TAC =
  TRY(FIRST_ASSUM(fun th -> let t = concl th in
        if is_eq t && is_numeral (rand t) && not(is_numeral(lhs t))
        then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
        ASSUME_TAC th
        else failwith "no"));;
let WRAP_CLOSE weqs =
  RULE_ASSUM_TAC(REWRITE_RULE[mem_range; size_part; ITER_1; ITER2; ITER3;
                              ITER4; ITER5]) THEN
  REWRITE_TAC[ITER_1; ITER2; ITER3; ITER4; ITER5] THEN
  RULE_ASSUM_TAC(REWRITE_RULE weqs) THEN REWRITE_TAC weqs THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  NUM_SUBST_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  NORM_TAC THEN
  FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC; PENTA_TAC THEN NO_TAC;
         ASM_REWRITE_TAC[mem_range] THEN NO_TAC];;

(* ------------------------------------------------------------------------- *)
(* Gonthier's first `have` (conv_part4): the reflected spoke 3 (= x's spoke  *)
(* 1 reversed) with its hat (x's spoke 0) and fans (x's hat/fan1 at f x),    *)
(* and the range h45 of the reflected hat 4 (wraparound WRAP_H45).           *)
(* ------------------------------------------------------------------------- *)

let CONV4_SPEC = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G /\ pentagonal G
    ==> !p1 (x:A). x IN dart G /\ fitp p1 G x
        ==> mem_range (FST (conv_part4 p1))
              (arity G (edge_map G (face_map G (face_map G
                                            (edge_map G (face_map G (face_map G
                 (edge_map G (face_map G (face_map G x)))))))))) /\
            !q5. fitp q5 G
            (face_map G (face_map G (edge_map G (face_map G (face_map G x)))))
                 ==> fitp (SND (conv_part4 p1) q5) G
                          (face_map G (edge_map G (face_map G
                                                   (face_map G x))))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN
   `arity G (edge_map G (face_map G (face_map G (edge_map G
                                                 (face_map G (face_map G
                 (edge_map G (face_map G (face_map G (x:A)))))))))) =
    arity G (edge_map G (ITER (arity G (edge_map G (face_map G x)) - 3)
                         (face_map G)
                   (edge_map G (face_map G x))))`
  MP_TAC THENL
   [MATCH_MP_TAC WRAP_H45 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`G:(A)hypermap`;
                  `edge_map G (face_map G (x:A))`] PENTA_PR59) THEN
    ASM_REWRITE_TAC IN_DART_EQS THEN REWRITE_TAC[mem_range] THEN
    ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun weq ->
    STRUCT_CASES_TAC(ISPEC `p1:part` (cases "part")) THEN
    REWRITE_TAC[conv_part4; FST; SND; fitp] THENL
     [REPEAT STRIP_TAC THEN PENTA_TAC;
      STRUCT_CASES_TAC(ISPEC `a2:part` (cases "part")) THEN
      REWRITE_TAC[cp4_aux; fitp] THEN REPEAT COND_CASES_TAC THEN
      ASM_REWRITE_TAC[FST; SND; fitp; subpart_loc_move] THEN
      REPEAT STRIP_TAC THEN WRAP_CLOSE [weq];
      REPEAT STRIP_TAC THEN PENTA_TAC;
      REPEAT STRIP_TAC THEN PENTA_TAC;
      REPEAT STRIP_TAC THEN PENTA_TAC]));;

(* ------------------------------------------------------------------------- *)
(* CONV5_SPEC (Gonthier's second `have`): the reflected hub range u (x's     *)
(* spoke 2) and the reflected spokes 4.. (x's hat/fans at f (f x)): all      *)
(* atoms are syntactically identical after unfolding, no normalization       *)
(* needed.                                                                   *)
(* ------------------------------------------------------------------------- *)

let CONV5_SPEC = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G /\ pentagonal G
    ==> !p3 h45 (x:A). x IN dart G /\
        fitp p3 G (face_map G (face_map G x)) /\
        mem_range h45 (arity G (edge_map G (face_map G (face_map G
          (edge_map G (face_map G (face_map G (edge_map G
                                            (face_map G (face_map G x))))))))))
        ==> mem_range (FST (conv_part5 h45 p3))
              (arity G (edge_map G (face_map G (face_map G x)))) /\
            fitp (SND (conv_part5 h45 p3)) G
              (face_map G (face_map G (edge_map G (face_map G
                                                   (face_map G x)))))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p3:part` (cases "part")) THEN
  REWRITE_TAC[conv_part5; fitp; subpart_loc_move; ITER2; ITER3; ITER4; ITER5;
              pcons_s] THEN
  REWRITE_TAC[FST; SND; fitp; subpart_loc_move; ITER2; ITER3;
              ITER4; ITER5] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST[FIRST_ASSUM MATCH_ACCEPT_TAC;
        MATCH_MP_TAC PENTA_PR59 THEN ASM_REWRITE_TAC[] THEN dart_tac]);;

(* ------------------------------------------------------------------------- *)
(* Gonthier's third `have` (conv_part12): the reflected spokes 0 and 1 (x's  *)
(* hat 3 and spoke 3 reversed), with the range h23 of the reflected hat 2 (= *)
(* x's spoke 4) and wraparound WRAP_H34 for x's hat 4.                       *)
(* ------------------------------------------------------------------------- *)

let CONV12_SPEC = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G /\ pentagonal G
    ==> !p4 (x:A). x IN dart G /\
    fitp p4 G (face_map G (face_map G (face_map G x)))
        ==> mem_range (FST (conv_part12 p4))
              (arity G (edge_map G (face_map G (face_map G
                                                (edge_map G (edge_map G
                 (face_map G (face_map G x)))))))) /\
            !q3. fitp q3 G (edge_map G (face_map G (face_map G x)))
                 ==> fitp (SND (conv_part12 p4) q3) G
                          (inv_face2 G
                          (edge_map G (face_map G (face_map G x))))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN
   `arity G (edge_map G (face_map G (face_map G (edge_map G
                                                 (face_map G (face_map G
                   (face_map G (face_map G (x:A))))))))) =
    arity G (edge_map G (ITER (arity G (edge_map G (face_map G
                                             (face_map G (face_map G x)))) - 2)
                   (face_map G)
                   (edge_map G (face_map G (face_map G (face_map G x))))))`
  MP_TAC THENL
   [MATCH_MP_TAC WRAP_H34 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`G:(A)hypermap`;
                  `edge_map G (face_map G (face_map G (face_map G (x:A))))`]
                 PENTA_PR59) THEN
    ASM_REWRITE_TAC IN_DART_EQS THEN REWRITE_TAC[mem_range] THEN
    ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun weq ->
    let inner v =
      STRUCT_CASES_TAC(ISPEC v (cases "part")) THEN
      REWRITE_TAC[cp12_auxA; cp12_auxB; cp12_auxC; fitp; pcons_s] THEN
      REPEAT COND_CASES_TAC THEN
      ASM_REWRITE_TAC[FST; SND; fitp; subpart_loc_move; pcons_s] THEN
      REPEAT STRIP_TAC THEN WRAP_CLOSE [weq] in
    STRUCT_CASES_TAC(ISPEC `p4:part` (cases "part")) THEN
    REWRITE_TAC[conv_part12; FST; SND; fitp] THENL
     [REPEAT STRIP_TAC THEN PENTA_TAC;
      inner `a2:part`; inner `a2:part`; inner `a3:part`;
      REPEAT STRIP_TAC THEN PENTA_TAC]));;

(* ------------------------------------------------------------------------- *)
(* All atoms are universal.                                                  *)
(* ------------------------------------------------------------------------- *)

let CP3_3_SPEC = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G /\ pentagonal G
    ==> !p9 h23 f31 f32 f33 q (x:A).
        x IN dart G /\
        fitp p9 G (face_map G (face_map G (face_map G
                                           (ITER 5 (face_map G) x)))) /\
        arity G x = 8 + size_part p9 /\
        mem_range h23
        (arity G (edge_map G (face_map G (face_map G (edge_map G (edge_map G
                         (face_map G (face_map G x)))))))) /\
        mem_range f31 (arity G (edge_map G (ITER 5 (face_map G) x))) /\
        mem_range f32
        (arity G (edge_map G (face_map G (ITER 5 (face_map G) x)))) /\
        mem_range f33
    (arity G (edge_map G (face_map G (face_map G (ITER 5 (face_map G) x))))) /\
        fitp q G (face_map G (edge_map G (face_map G (face_map G x))))
        ==> fitp (cp3_3 h23 f31 f32 f33 p9 q) G
        (edge_map G (face_map G (face_map G x)))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p9:part` (cases "part")) THEN
  REWRITE_TAC[cp3_3; fitp; subpart_loc_move] THEN REPEAT STRIP_TAC THEN
  WRAP_CLOSE []);;

let CP3_2_SPEC = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G /\ pentagonal G
    ==> !p8 h23 f31 f32 q (x:A).
        x IN dart G /\
        fitp p8 G (face_map G (face_map G (ITER 5 (face_map G) x))) /\
        arity G x = 7 + size_part p8 /\
        mem_range h23
        (arity G (edge_map G (face_map G (face_map G (edge_map G (edge_map G
                         (face_map G (face_map G x)))))))) /\
        mem_range f31 (arity G (edge_map G (ITER 5 (face_map G) x))) /\
        mem_range f32
        (arity G (edge_map G (face_map G (ITER 5 (face_map G) x)))) /\
        fitp q G (face_map G (edge_map G (face_map G (face_map G x))))
        ==> fitp (cp3_2 h23 f31 f32 p8 q) G
        (edge_map G (face_map G (face_map G x)))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p8:part` (cases "part")) THEN
  REWRITE_TAC[cp3_2; fitp; subpart_loc_move] THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[fitp; subpart_loc_move] THEN REPEAT STRIP_TAC THEN
  FIRST [WRAP_CLOSE [];
         MP_TAC(ISPEC `G:(A)hypermap` CP3_3_SPEC) THEN ASM_REWRITE_TAC[] THEN
         DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[size_part] THEN
         ARITH_TAC]);;

let CP3_1_SPEC = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G /\ pentagonal G
    ==> !p7 h23 f31 q (x:A).
        x IN dart G /\
        fitp p7 G (face_map G (ITER 5 (face_map G) x)) /\
        arity G x = 6 + size_part p7 /\
        mem_range h23
        (arity G (edge_map G (face_map G (face_map G (edge_map G (edge_map G
                         (face_map G (face_map G x)))))))) /\
        mem_range f31 (arity G (edge_map G (ITER 5 (face_map G) x))) /\
        fitp q G (face_map G (edge_map G (face_map G (face_map G x))))
        ==> fitp (cp3_1 h23 f31 p7 q) G
        (edge_map G (face_map G (face_map G x)))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p7:part` (cases "part")) THEN
  REWRITE_TAC[cp3_1; fitp; subpart_loc_move] THEN REPEAT STRIP_TAC THEN
  FIRST [WRAP_CLOSE [];
         MP_TAC(ISPEC `G:(A)hypermap` CP3_2_SPEC) THEN ASM_REWRITE_TAC[] THEN
         DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[size_part] THEN
         ARITH_TAC]);;

let CONV3_SPEC = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G /\ pentagonal G
    ==> !p6 h23 q (x:A).
        x IN dart G /\ fitp p6 G (ITER 5 (face_map G) x) /\
        arity G x = 5 + size_part p6 /\
        mem_range h23
        (arity G (edge_map G (face_map G (face_map G (edge_map G (edge_map G
                         (face_map G (face_map G x)))))))) /\
        fitp q G (face_map G (edge_map G (face_map G (face_map G x))))
        ==> fitp (conv_part3 h23 p6 q) G
        (edge_map G (face_map G (face_map G x)))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p6:part` (cases "part")) THEN
  REWRITE_TAC[conv_part3; fitp; subpart_loc_move] THEN REPEAT STRIP_TAC THEN
  FIRST [WRAP_CLOSE [];
         MP_TAC(ISPEC `G:(A)hypermap` CP3_1_SPEC) THEN ASM_REWRITE_TAC[] THEN
         DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[size_part] THEN
         ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Coq FITP_CONVERSE (part.v:1157): assembly of the four layers along the    *)
(* let-structure of converse_part.                                           *)
(* ------------------------------------------------------------------------- *)

let FITP_CONVERSE = prove
 (`!(G:(A)hypermap) p x.
     plain_cubic_pentagonal G /\ x IN dart G /\ exact_fitp G x p
     ==> tight_fitp G (inv_face2 G (edge_map G (face_map G (face_map G x))))
                    (converse_part p)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[plain_cubic_pentagonal; plain_cubic; exact_fitp] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `G:(A)hypermap` CONV4_SPEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL[`p:part`;`x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q4")) THEN
  MP_TAC(ISPECL[`2`;`p:part`;`G:(A)hypermap`;`x:A`] FITP_DROP) THEN
  ASM_REWRITE_TAC[ITER2] THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`3`;`p:part`;`G:(A)hypermap`;`x:A`] FITP_DROP) THEN
  ASM_REWRITE_TAC[ITER3] THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`5`;`p:part`;`G:(A)hypermap`;`x:A`] FITP_DROP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `G:(A)hypermap` CONV5_SPEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL[`drop_part 2 p`;`FST (conv_part4 p)`;`x:A`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REMOVE_THEN "q4"
   (MP_TAC o SPEC `SND (conv_part5 (FST (conv_part4 p)) (drop_part 2 p))`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `G:(A)hypermap` CONV12_SPEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL[`drop_part 3 p`;`x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q12")) THEN
  MP_TAC(ISPEC `G:(A)hypermap` CONV3_SPEC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o
    SPECL[`drop_part 5 p`;`FST (conv_part12 (drop_part 3 p))`;
      `SND (conv_part4 p)
       (SND (conv_part5 (FST (conv_part4 p)) (drop_part 2 p)))`;`x:A`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[SIZE_DROP_PART] THEN
    MP_TAC(ISPECL[`G:(A)hypermap`;`x:A`] PENTA_PR59) THEN
    ASM_REWRITE_TAC[mem_range] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  REMOVE_THEN "q12" (MP_TAC o SPEC
    `conv_part3 (FST (conv_part12 (drop_part 3 p))) (drop_part 5 p)
       (SND (conv_part4 p)
       (SND (conv_part5 (FST (conv_part4 p)) (drop_part 2 p))))`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[tight_fitp; converse_part] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[] THEN NORM_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

