(* ========================================================================= *)
(* 4CT/part_mirror.ml                                                        *)
(*                                                                           *)
(* part.v, the FitMirrorPart section: the mirror correspondence for parts.   *)
(* FITP_MIRROR (exact_fitp of mirror_part p at G is exact_fitp of p at       *)
(* mirror G), together with the definitions of the converse part (inv_face2, *)
(* conv_part12, conv_part3, conv_part4, conv_part5, converse_part) whose     *)
(* fitting lemma is in part_converse.ml.                                     *)
(* ========================================================================= *)

needs "4CT/part.ml";;

(* Mirror bridge lemmas: the maps of mirror G are e' = f o n, n' = f o e and *)
(* f' = e o n (MIRROR_COMPONENTS).                                           *)

let FEF_NE = prove
 (`!(G:(A)hypermap) x. plain_hypermap G /\ cubic_hypermap G /\ x IN dart G
     ==> face_map G (edge_map G (face_map G x)) = node_map G (edge_map G x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `face_map G (edge_map G (face_map G (x:A))) =
                node_map G (node_map G (face_map G x))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CUBIC_EQ' THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART]; ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PLAIN_EQ' THEN ASM_REWRITE_TAC[]);;

let EDGE_MIRROR_FACE = prove
 (`!(G:(A)hypermap) x. plain_hypermap G /\ x IN dart G
     ==> edge_map (mirror G) (face_map G x) = face_map G (edge_map G x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MIRROR_COMPONENTS; o_THM] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PLAIN_EQ' THEN ASM_REWRITE_TAC[]);;

let ARITY_EN = prove
 (`!(G:(A)hypermap) x. x IN dart G
     ==> arity G (edge_map G (node_map G x)) = arity G x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `arity G (x:A) = arity G (face_map G (edge_map G (node_map G x)))`
    SUBST1_TAC THENL [REWRITE_TAC[nodeK]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ARITY_FACE THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART]);;

let DART_MIRROR = prove
 (`!G:(A)hypermap. dart(mirror G) = dart G`,
  REWRITE_TAC[MIRROR_COMPONENTS]);;

(* The mirror block of FitMirrorPart: FITP_MIRROR.                           *)
let FACE_MIRROR_LINV = prove
 (`!(G:(A)hypermap) z. face_map (mirror G) (face_map G z) = z`,
  REWRITE_TAC[MIRROR_COMPONENTS; o_THM; faceK]);;
let dart_tac =
  ASM_MESON_TAC[FACE_MAP_IN_DART; NODE_MAP_IN_DART; EDGE_MAP_IN_DART];;
(* Gonthier's Ears2: the mirror-hat at any dart has the arity of the G-hat.  *)
let ARS2_MIRROR = prove
 (`!(G:(A)hypermap) x. plain_hypermap G /\ cubic_hypermap G /\ x IN dart G
    ==> arity (mirror G)
          (edge_map (mirror G)
          (ITER 2 (face_map (mirror G)) (edge_map (mirror G) x))) =
        arity G (edge_map G (ITER 2 (face_map G) (edge_map G x)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; ITER] THEN
  REWRITE_TAC[MIRROR_COMPONENTS; o_THM] THEN
  SUBGOAL_THEN
    `node_map G (face_map G (node_map G (x:A))) = edge_map G (node_map G x)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC PLAIN_EQ' THEN ASM_SIMP_TAC[NODE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map G (edge_map G (node_map G (x:A))) = node_map G x`
    SUBST1_TAC THENL
   [MATCH_MP_TAC PLAIN_EQ THEN ASM_SIMP_TAC[NODE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map G (node_map G (x:A)) = face_map G (edge_map G x)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC CUBIC_EQ' THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `arity (mirror G)
     (face_map G (node_map G (edge_map G (face_map G (edge_map G (x:A)))))) =
   arity G (face_map G (node_map G (edge_map G (face_map G (edge_map G x)))))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ARITY_MIRROR THEN dart_tac; ALL_TAC] THEN
  SUBGOAL_THEN
 `arity G (face_map G (node_map G (edge_map G (face_map G
                                               (edge_map G (x:A)))))) =
                arity G (node_map G (edge_map G (face_map G (edge_map G x))))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ARITY_FACE THEN dart_tac; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map G (face_map G (edge_map G (x:A))) =
                node_map G (face_map G (face_map G (edge_map G x)))`
    SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PLAIN_EQ' THEN
   ASM_REWRITE_TAC[] THEN dart_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `node_map G (node_map G (face_map G (face_map G (edge_map G (x:A))))) =
                face_map G (edge_map G (face_map G (face_map G
                                                    (edge_map G x))))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC CUBIC_EQ' THEN ASM_REWRITE_TAC[] THEN dart_tac; ALL_TAC] THEN
  MATCH_MP_TAC ARITY_FACE THEN dart_tac);;
let ITER_FACE_MIRROR_CANCEL = prove
 (`!(G:(A)hypermap) k z. ITER k (face_map (mirror G))
 (ITER k (face_map G) z) = z`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ITER_COMMUTE] THEN
  ASM_REWRITE_TAC[FACE_MIRROR_LINV]);;
let ITER_MIRROR_FACE_SHIFT = prove
 (`!(G:(A)hypermap) n m z. ITER m (face_map G) z = z /\ n <= m
     ==> ITER n (face_map (mirror G)) z = ITER (m - n) (face_map G) z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th)
    then GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th] else NO_TAC) THEN
  SUBGOAL_THEN `ITER m (face_map G) (z:A) =
                ITER n (face_map G) (ITER (m - n) (face_map G) z)`
                SUBST1_TAC THENL
   [REWRITE_TAC[ITER_ADD] THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ITER_FACE_MIRROR_CANCEL]);;
(* Gonthier's Earsf: the n-th arity-position of the mirror-spoke at (face x) *)
(* is the (m-n)-th position of the G-spoke at x (m = spoke arity).           *)
let EARSF_MIRROR = prove
 (`!(G:(A)hypermap) x n. plain_hypermap G /\ cubic_hypermap G /\ x IN dart G /\
     1 <= n /\ n <= arity G (edge_map G x)
     ==> arity (mirror G) (edge_map (mirror G) (ITER n (face_map (mirror G))
           (edge_map (mirror G) (face_map G x)))) =
         arity G (edge_map G (ITER (arity G (edge_map G x) - n) (face_map G)
                              (edge_map G x)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ms = arity G (edge_map G (x:A))` THEN
  SUBGOAL_THEN
    `edge_map (mirror G) (face_map G (x:A)) = face_map G (edge_map G x)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EDGE_MIRROR_FACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ITER n (face_map (mirror G)) (face_map G (edge_map G (x:A))) =
                ITER (n - 1) (face_map (mirror G)) (edge_map G x)`
                SUBST1_TAC THENL
   [SUBGOAL_THEN `n = SUC(n - 1)` (fun th -> GEN_REWRITE_TAC
      (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ITER_SUC_INNER; FACE_MIRROR_LINV]; ALL_TAC] THEN
  SUBGOAL_THEN `ITER (n - 1) (face_map (mirror G)) (edge_map G (x:A)) =
                ITER (ms - (n - 1)) (face_map G) (edge_map G x)`
                SUBST1_TAC THENL
   [MATCH_MP_TAC ITER_MIRROR_FACE_SHIFT THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_eq(concl th) then SUBST1_TAC (SYM th)
     else NO_TAC) THEN
      REWRITE_TAC[ITER_FACE_ARITY_GEN];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ms - (n - 1) = SUC(ms - n)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ITER] THEN REWRITE_TAC[MIRROR_COMPONENTS; o_THM] THEN
  SUBGOAL_THEN
    `node_map G (face_map G (ITER (ms - n) (face_map G) (edge_map G (x:A)))) =
                edge_map G (ITER (ms - n) (face_map G) (edge_map G x))`
                SUBST1_TAC THENL
   [MATCH_MP_TAC PLAIN_EQ' THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ITER_PERMUTES_IN THEN
    ASM_SIMP_TAC[FACE_MAP_PERMUTES; EDGE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
    `edge_map G (ITER (ms - n) (face_map G) (edge_map G (x:A))) IN dart G`
    ASSUME_TAC THENL
   [MATCH_MP_TAC EDGE_MAP_IN_DART THEN MATCH_MP_TAC ITER_PERMUTES_IN THEN
    ASM_SIMP_TAC[FACE_MAP_PERMUTES; EDGE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN
 `arity (mirror G)
  (face_map G (edge_map G (ITER (ms - n) (face_map G) (edge_map G (x:A))))) =
                arity G (face_map G (edge_map G (ITER (ms - n) (face_map G)
                                                 (edge_map G x))))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC ARITY_MIRROR THEN ASM_SIMP_TAC[FACE_MAP_IN_DART];
    ALL_TAC] THEN
  MATCH_MP_TAC ARITY_FACE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* FITP_MIRROR.  The invariant of the induction over mirror_part_rec, for u  *)
(* in the darts:                                                             *)
(*                                                                           *)
(*   fitp (rec p h0 Pnil) G u /\ HAT (next_hat h0 p) @ ITER (size p) f u     *)
(*   <=> fitp p (mirror G) (ITER (size p) f u) /\ HAT h0 @ u                 *)
(*                                                                           *)
(* with a boundary hat atom on both sides.  In the cons step the mirror side *)
(* exchanges the hat atom of its frame for the hat of frame 0 of the other   *)
(* side (ARS2_MIRROR at f v), the spokes align by SPOKE_MIRROR_REL and       *)
(* FACE_MIRROR_LINV, and the fans by EARSF_MIRROR at n = 3, 4, 5 after a     *)
(* case split on the spoke arity (6, 7 or 8; otherwise both sides are        *)
(* false).  Final assembly: when arity x = size p (otherwise both exact_fitp *)
(* are false) and p is not Pnil, the invariant at (p, get_hat p, x) with     *)
(* next_hat h0 p = get_hat p (NEXT_HAT_NONNIL); both sides imply the shared  *)
(* boundary hat atom (FITP_HEAD_HAT with NEXT_HAT_MIRROR_REC, resp.          *)
(* FITP_HEAD_HAT at mirror G with ARS2_MIRROR), which TAUT then cancels.     *)
(* ------------------------------------------------------------------------- *)
let NEXT_HAT_NONNIL = prove
 (`!p h0. ~(p = Pnil) ==> next_hat h0 p = get_hat p`,
  MATCH_MP_TAC part_INDUCT THEN
  REWRITE_TAC[next_hat; get_hat; distinctness "part"]);;
let SIZE_PART_EQ_0 = prove
 (`!p. size_part p = 0 <=> p = Pnil`,
  MATCH_MP_TAC part_INDUCT THEN
  REWRITE_TAC[size_part; NOT_SUC; distinctness "part"]);;
let CAT_PART_ASSOC = prove
 (`!a b c. cat_part (cat_part a b) c = cat_part a (cat_part b c)`,
  MATCH_MP_TAC part_INDUCT THEN REWRITE_TAC[cat_part] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let MIRROR_REC_CAT = prove
 (`!p h0 q. mirror_part_rec p h0 q = cat_part (mirror_part_rec p h0 Pnil) q`,
  MATCH_MP_TAC part_INDUCT THEN REWRITE_TAC[mirror_part_rec; cat_part] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun ih -> GEN_REWRITE_TAC LAND_CONV [ih]) THEN
  FIRST_ASSUM(fun ih -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ih]) THEN
  REWRITE_TAC[CAT_PART_ASSOC; cat_part]);;
let SPOKE_MIRROR_REL = prove
 (`!(G:(A)hypermap) w. plain_hypermap G /\ w IN dart G
     ==> arity (mirror G) (edge_map (mirror G) w) =
         arity G (edge_map G (face_map (mirror G) w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `arity (mirror G) (edge_map (mirror G) (w:A)) =
                arity G (edge_map (mirror G) w)` SUBST1_TAC THENL
   [MATCH_MP_TAC ARITY_MIRROR THEN
    ASM_MESON_TAC[EDGE_MAP_IN_DART; DART_MIRROR]; ALL_TAC] THEN
  REWRITE_TAC[MIRROR_COMPONENTS; o_THM] THEN
  SUBGOAL_THEN `edge_map G (edge_map G (node_map G (w:A))) = node_map G w`
    SUBST1_TAC THENL
   [MATCH_MP_TAC PLAIN_EQ THEN ASM_MESON_TAC[NODE_MAP_IN_DART]; ALL_TAC] THEN
  MATCH_MP_TAC ARITY_FACE THEN ASM_MESON_TAC[NODE_MAP_IN_DART]);;
let FITP_HEAD_HAT = prove
 (`!p (G:(A)hypermap) u h1. ~(p = Pnil) /\ fitp p G u
     ==> mem_range (next_hat h1 p) (arity G (subpart_loc_move Phat G u))`,
  MATCH_MP_TAC part_INDUCT THEN
  REWRITE_TAC[fitp; next_hat; distinctness "part"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let NEXT_HAT_MIRROR_REC = prove
 (`!p h0 q h1. next_hat h1 (mirror_part_rec p h0 q) =
     (if p = Pnil then next_hat h1 q else h0)`,
  MATCH_MP_TAC part_INDUCT THEN
  REWRITE_TAC[mirror_part_rec; distinctness "part"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[next_hat]);;
let mstep_prefix (tl:term) =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(IN):A->(A->bool)->bool`,
      list_mk_comb(`ITER:num->(A->A)->A->A`,
        [mk_comb(`size_part`,tl); `face_map (G:(A)hypermap)`; `u:A`])),
      `dart (G:(A)hypermap)`)) ASSUME_TAC THENL
   [MATCH_MP_TAC ITER_PERMUTES_IN THEN
   ASM_REWRITE_TAC[FACE_MAP_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(IN):A->(A->bool)->bool`,
      mk_comb(`face_map (G:(A)hypermap)`,
        list_mk_comb(`ITER:num->(A->A)->A->A`,
          [mk_comb(`size_part`,tl); `face_map (G:(A)hypermap)`; `u:A`]))),
      `dart (G:(A)hypermap)`)) ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_MAP_IN_DART]; ALL_TAC] THEN
  REWRITE_TAC[mirror_part_rec; size_part; next_hat] THEN
  ONCE_REWRITE_TAC[MIRROR_REC_CAT] THEN
  REWRITE_TAC[FITP_CAT; SIZE_MIRROR_REC; size_part; ADD_CLAUSES] THEN
  REWRITE_TAC[fitp; ITER] THEN REWRITE_TAC[FACE_MIRROR_LINV] THEN
  REWRITE_TAC[subpart_loc_move] THEN
  MP_TAC(SPECL [`G:(A)hypermap`;
     mk_comb(`face_map (G:(A)hypermap)`,
       list_mk_comb(`ITER:num->(A->A)->A->A`,
         [mk_comb(`size_part`,tl); `face_map (G:(A)hypermap)`; `u:A`]))]
           ARS2_MIRROR) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[subpart_loc_move] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`G:(A)hypermap`;
     mk_comb(`face_map (G:(A)hypermap)`,
       list_mk_comb(`ITER:num->(A->A)->A->A`,
         [mk_comb(`size_part`,tl); `face_map (G:(A)hypermap)`; `u:A`]))]
           SPOKE_MIRROR_REL) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[FACE_MIRROR_LINV] THEN
  DISCH_THEN SUBST1_TAC;;
let mstep_ih =
  USE_THEN "IH" (fun ih ->
    MP_TAC(REWRITE_RULE[subpart_loc_move]
      (MP (SPECL [`h0:prange`; `u:A`] ih) (ASSUME `(u:A) IN dart G`)))) THEN
  CONV_TAC TAUT;;
let mstep_fans (tl:term) (spk:term) (ms:int) (ns:int list) =
  let vterm = list_mk_comb(`ITER:num->(A->A)->A->A`,
    [mk_comb(`size_part`,tl); `face_map (G:(A)hypermap)`; `u:A`]) in
  let aterm = mk_comb(mk_comb(`arity:(A)hypermap->A->num`,`G:(A)hypermap`),
                      mk_comb(`edge_map (G:(A)hypermap)`,vterm)) in
  let case_eq = mk_eq(aterm, mk_small_numeral ms) in
  ASM_CASES_TAC case_eq THENL
   [EVERY(map (fun n ->
      MP_TAC(SPECL [`G:(A)hypermap`; vterm;
                    mk_small_numeral n] EARSF_MIRROR) THEN
      ASM_REWRITE_TAC[ARITH_RULE(mk_conj(
        mk_binary "<=" (`1`,mk_small_numeral n),
        mk_binary "<=" (mk_small_numeral n,mk_small_numeral ms)))] THEN
      CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC) ns) THEN
    mstep_ih;
    SUBGOAL_THEN (mk_eq(list_mk_comb(`mem_range`,[spk; aterm]),`F`))
      SUBST1_TAC THENL
     [REWRITE_TAC[mem_range] THEN ASM_REWRITE_TAC[]; REWRITE_TAC[]]];;
let MIRROR_FITP_INVARIANT = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G
    ==> !p h0 (u:A). u IN dart G
        ==> (fitp (mirror_part_rec p h0 Pnil) G u /\
             mem_range (next_hat h0 p)
               (arity G (subpart_loc_move Phat G (ITER (size_part p)
                                                  (face_map G) u)))
             <=>
             fitp p (mirror G) (ITER (size_part p) (face_map G) u) /\
             mem_range h0 (arity G (subpart_loc_move Phat G u)))`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC part_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[mirror_part_rec; fitp; size_part; ITER; next_hat];
    mstep_prefix `a2:part` THEN mstep_ih;
    mstep_prefix `a2:part` THEN mstep_fans `a2:part` `Pr66` 6 [3];
    mstep_prefix `a3:part` THEN mstep_fans `a3:part` `Pr77` 7 [3;4];
    mstep_prefix `a4:part` THEN mstep_fans `a4:part` `Pr88` 8 [3;4;5]]);;
let FITP_MIRROR = prove
 (`!(G:(A)hypermap). plain_hypermap G /\ cubic_hypermap G
    ==> !p (x:A). x IN dart G
        ==> (exact_fitp G x (mirror_part p) <=> exact_fitp (mirror G) x p)`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[exact_fitp; SIZE_MIRROR_PART] THEN
  SUBGOAL_THEN `arity (mirror G) (x:A) = arity G x` SUBST1_TAC THENL
   [MATCH_MP_TAC ARITY_MIRROR THEN ASM_REWRITE_TAC[DART_MIRROR]; ALL_TAC] THEN
  ASM_CASES_TAC `arity G (x:A) = size_part p` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p = Pnil` THENL
   [ASM_REWRITE_TAC[mirror_part; mirror_part_rec; fitp]; ALL_TAC] THEN
  SUBGOAL_THEN `ITER (size_part p) (face_map G) (x:A) = x` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
       (try rand(concl th) = `size_part p` with _ -> false)
     then SUBST1_TAC (SYM th) else NO_TAC) THEN
    REWRITE_TAC[ITER_FACE_ARITY_GEN]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:part`; `get_hat p`; `x:A`]
    (MATCH_MP MIRROR_FITP_INVARIANT
      (CONJ (ASSUME `plain_hypermap (G:(A)hypermap)`)
            (ASSUME `cubic_hypermap (G:(A)hypermap)`)))) THEN
  ASM_SIMP_TAC[NEXT_HAT_NONNIL] THEN
  REWRITE_TAC[GSYM mirror_part] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `fitp (mirror_part p) G (x:A)
    ==> mem_range (get_hat p) (arity G (subpart_loc_move Phat G x))`
    ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`mirror_part p`; `G:(A)hypermap`; `x:A`; `Pr59`
    ] FITP_HEAD_HAT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(mirror_part p = Pnil)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN(MP_TAC o AP_TERM `size_part`) THEN
      REWRITE_TAC[SIZE_MIRROR_PART; size_part] THEN
      ASM_REWRITE_TAC[SIZE_PART_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[mirror_part; NEXT_HAT_MIRROR_REC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fitp p (mirror G) (x:A)
    ==> mem_range (get_hat p) (arity G (subpart_loc_move Phat G x))`
    ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`p:part`; `mirror (G:(A)hypermap)`; `x:A`; `Pr59`
    ] FITP_HEAD_HAT) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[NEXT_HAT_NONNIL] THEN
    MP_TAC(SPECL [`G:(A)hypermap`; `x:A`] ARS2_MIRROR) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[subpart_loc_move] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC TAUT);;

(* The converse part: definitions, layered into auxiliary functions          *)
(* following the nested Coq pattern (as for good_split in part.ml).          *)
let inv_face2 = new_definition
 `inv_face2 (G:(A)hypermap) x =
  edge_map G (node_map G (edge_map G (node_map G x)))`;;
let tight_fitp = new_definition
 `tight_fitp (G:(A)hypermap) (x:A) up <=>
    mem_range (FST up) (arity G x) /\ fitp (SND up) G x`;;
let cp12_auxA = new_recursive_definition part_RECURSION
 `(cp12_auxA s2 s1 Pnil = (Pr59, (\q:part. Pnil))) /\
  (cp12_auxA s2 s1 (Pcons h23 f2 p) =
     (if f2 = Pr59 then (h23, \q. pcons_s s1 (pcons_s s2 q))
      else if s2 = Pr55 then (h23, \q. pcons_s s1 (Pcons Pr55 f2 q))
      else if s2 = Pr66 then (h23, \q. pcons_s s1 (Pcons6 Pr59 f2 q))
      else if s2 = Pr77 then (h23, \q. pcons_s s1 (Pcons7 Pr59 Pr59 f2 q))
      else (Pr59, \q. Pnil))) /\
  (cp12_auxA s2 s1 (Pcons6 h f1 p) = (Pr59, \q. Pnil)) /\
  (cp12_auxA s2 s1 (Pcons7 h f1 f2 p) = (Pr59, \q. Pnil)) /\
  (cp12_auxA s2 s1 (Pcons8 h f1 f2 f3 p) = (Pr59, \q. Pnil))`;;
let cp12_auxB = new_recursive_definition part_RECURSION
 `(cp12_auxB s1 h12 Pnil = (Pr59, (\q:part. Pnil))) /\
  (cp12_auxB s1 h12 (Pcons h23 f21 p) =
  (h23, \q. pcons_s s1 (Pcons6 h12 f21 q))) /\
  (cp12_auxB s1 h12 (Pcons6 h f1 p) = (Pr59, \q. Pnil)) /\
  (cp12_auxB s1 h12 (Pcons7 h f1 f2 p) = (Pr59, \q. Pnil)) /\
  (cp12_auxB s1 h12 (Pcons8 h f1 f2 f3 p) = (Pr59, \q. Pnil))`;;
let cp12_auxC = new_recursive_definition part_RECURSION
 `(cp12_auxC s1 h12 f21 Pnil = (Pr59, (\q:part. Pnil))) /\
  (cp12_auxC s1 h12 f21 (Pcons h23 f22 p) =
  (h23, \q. pcons_s s1 (Pcons7 h12 f21 f22 q))) /\
  (cp12_auxC s1 h12 f21 (Pcons6 h f1 p) = (Pr59, \q. Pnil)) /\
  (cp12_auxC s1 h12 f21 (Pcons7 h f1 f2 p) = (Pr59, \q. Pnil)) /\
  (cp12_auxC s1 h12 f21 (Pcons8 h f1 f2 f3 p) = (Pr59, \q. Pnil))`;;
let conv_part12 = new_recursive_definition part_RECURSION
 `(conv_part12 Pnil = (Pr59, (\q:part. Pnil))) /\
  (conv_part12 (Pcons s2 s1 p) = cp12_auxA s2 s1 p) /\
  (conv_part12 (Pcons6 s1 h12 p) = cp12_auxB s1 h12 p) /\
  (conv_part12 (Pcons7 s1 h12 f21 p) = cp12_auxC s1 h12 f21 p) /\
  (conv_part12 (Pcons8 h f1 f2 f3 p) = (Pr59, \q. Pnil))`;;
let cp3_3 = new_recursive_definition part_RECURSION
 `(cp3_3 h23 f31 f32 f33 Pnil = Pcons8 h23 f31 f32 f33) /\
  (cp3_3 h23 f31 f32 f33 (Pcons s h p) = (\q:part. Pnil)) /\
  (cp3_3 h23 f31 f32 f33 (Pcons6 h f1 p) = (\q. Pnil)) /\
  (cp3_3 h23 f31 f32 f33 (Pcons7 h f1 f2 p) = (\q. Pnil)) /\
  (cp3_3 h23 f31 f32 f33 (Pcons8 h f1 f2 f3 p) = (\q. Pnil))`;;
let cp3_2 = new_recursive_definition part_RECURSION
 `(cp3_2 h23 f31 f32 Pnil =
     (if f31 = Pr59 /\ f32 = Pr59 then Pcons Pr77 h23 else Pcons7 h23 f31 f32))
     /\
  (cp3_2 h23 f31 f32 (Pcons f33 h p) = cp3_3 h23 f31 f32 f33 p) /\
  (cp3_2 h23 f31 f32 (Pcons6 h f1 p) = (\q:part. Pnil)) /\
  (cp3_2 h23 f31 f32 (Pcons7 h f1 f2 p) = (\q. Pnil)) /\
  (cp3_2 h23 f31 f32 (Pcons8 h f1 f2 f3 p) = (\q. Pnil))`;;
let cp3_1 = new_recursive_definition part_RECURSION
 `(cp3_1 h23 f31 Pnil = Pcons Pr66 h23) /\
  (cp3_1 h23 f31 (Pcons f32 h p) = cp3_2 h23 f31 f32 p) /\
  (cp3_1 h23 f31 (Pcons6 h f1 p) = (\q:part. Pnil)) /\
  (cp3_1 h23 f31 (Pcons7 h f1 f2 p) = (\q. Pnil)) /\
  (cp3_1 h23 f31 (Pcons8 h f1 f2 f3 p) = (\q. Pnil))`;;
let conv_part3 = new_recursive_definition part_RECURSION
 `(conv_part3 h23 Pnil = Pcons Pr55 h23) /\
  (conv_part3 h23 (Pcons f31 h p) = cp3_1 h23 f31 p) /\
  (conv_part3 h23 (Pcons6 h f1 p) = (\q:part. Pnil)) /\
  (conv_part3 h23 (Pcons7 h f1 f2 p) = (\q. Pnil)) /\
  (conv_part3 h23 (Pcons8 h f1 f2 f3 p) = (\q. Pnil))`;;
let cp4_aux = new_recursive_definition part_RECURSION
 `(cp4_aux h34 Pnil = (Pr59, (\q:part. Pnil))) /\
  (cp4_aux h34 (Pcons s4 f41 p) =
     (if f41 = Pr59 then (Pr59, Pcons s4 h34)
      else if s4 = Pr55 then (f41, Pcons Pr55 h34)
      else if s4 = Pr66 then (Pr59, Pcons6 h34 f41)
      else if s4 = Pr77 then (Pr59, Pcons7 h34 f41 Pr59)
      else (Pr59, \q. Pnil))) /\
  (cp4_aux h34 (Pcons6 f41 h45 p) = (h45, Pcons6 h34 f41)) /\
  (cp4_aux h34 (Pcons7 f41 f42 h45 p) = (h45, Pcons7 h34 f41 f42)) /\
  (cp4_aux h34 (Pcons8 h f1 f2 f3 p) = (Pr59, \q. Pnil))`;;
let conv_part4 = new_recursive_definition part_RECURSION
 `(conv_part4 Pnil = (Pr59, (\q:part. Pnil))) /\
  (conv_part4 (Pcons h34 h p) = cp4_aux h34 p) /\
  (conv_part4 (Pcons6 h f1 p) = (Pr59, \q. Pnil)) /\
  (conv_part4 (Pcons7 h f1 f2 p) = (Pr59, \q. Pnil)) /\
  (conv_part4 (Pcons8 h f1 f2 f3 p) = (Pr59, \q. Pnil))`;;
let conv_part5 = new_recursive_definition part_RECURSION
 `(conv_part5 h45 Pnil = (Pr59, Pnil)) /\
  (conv_part5 h45 (Pcons u s5 p) = (u, Pcons s5 h45 Pnil)) /\
  (conv_part5 h45 (Pcons6 h f1 p) = (Pr59, Pnil)) /\
  (conv_part5 h45 (Pcons7 s5 s6 s7 p) =
     (Pr77, Pcons s5 h45 (pcons_s s6 (pcons_s s7 Pnil)))) /\
  (conv_part5 h45 (Pcons8 h f1 f2 f3 p) = (Pr59, Pnil))`;;
let converse_part = new_definition
 `converse_part p1 =
    let h45q4 = conv_part4 p1 in
    let uq5 = conv_part5 (FST h45q4) (drop_part 2 p1) in
    let h23q12 = conv_part12 (drop_part 3 p1) in
    let q3 = conv_part3 (FST h23q12) (drop_part 5 p1) in
    (FST uq5, SND h23q12 (q3 (SND h45q4 (SND uq5))))`;;

