(* ========================================================================= *)
(* 4CT/part.ml                                                               *)
(*                                                                           *)
(* part.v: the pattern language of the discharging proofs.  A part describes *)
(* the second neighbourhood of a hub dart (an arity range for each spoke,    *)
(* its hat and, for spokes of arity 6, 7 or 8, its fans) and is checked      *)
(* against a hypermap by fitp and exact_fitp.  The file has the datatypes    *)
(* prange, subpart_loc and part with mem_range and size_part; the list       *)
(* operations drop_part, take_part, cat_part, catrev_part, rev_part and      *)
(* rot_part with FITP_CAT, FITP_DROP, FITP_CATREV and FITP_ROT; the          *)
(* accessors and mirror_part (SIZE_MIRROR_PART, MIRROR_MIRROR_PART); the     *)
(* comparison cmp_range, cmp_part (MEM_CMP_RANGE, FITP_CMP) and the meet     *)
(* meet_range, meet_part (MEM_MEET_RANGE, SIZE_MEET_PART, FITP_MEET,         *)
(* EXACT_FITP_MEET); part_update with its update lemmas and pcons_           *)
(* (FITP_PCONS_); and the split operations good_split, split_part with       *)
(* SIZE_SPLIT_PART, FIT_SPLIT_RANGE and FITP_SPLIT.  discharge.ml,           *)
(* redpart.ml and hubcap.ml build on it.                                     *)
(* ========================================================================= *)

needs "4CT/geometry.ml";;
needs "4CT/color.ml";;
needs "4CT/coloring.ml";;

let prange_INDUCT,prange_RECURSION = define_type
  "prange = Pr55 | Pr66 | Pr77 | Pr88 | Pr99 | Pr56 | Pr67 | Pr78 | Pr89 | \
   Pr57 | Pr68 | Pr79 | Pr58 | Pr69 | Pr59";;
let subpart_loc_INDUCT,subpart_loc_RECURSION = define_type
  "subpart_loc = Pspoke | Phat | Pfan1 | Pfan2 | Pfan3";;
let part_INDUCT,part_RECURSION = define_type
  "part = Pnil
        | Pcons prange prange part
        | Pcons6 prange prange part
        | Pcons7 prange prange prange part
        | Pcons8 prange prange prange prange part";;

(* mem_range r n <=> the arity n is in the range r (Pr55: exactly 5, Pr59:   *)
(* at least 5, Pr69: at least 6, Pr56: 5 or 6, and so on); the constructors  *)
(* are in Coq's order.                                                       *)
let mem_range = new_recursive_definition prange_RECURSION
 `(mem_range Pr55 = (\n. n = 5)) /\ (mem_range Pr66 = (\n. n = 6)) /\
  (mem_range Pr77 = (\n. n = 7)) /\ (mem_range Pr88 = (\n. n = 8)) /\
  (mem_range Pr99 = (\n. 9 <= n)) /\
  (mem_range Pr56 = (\n. n = 5 \/ n = 6)) /\
  (mem_range Pr67 = (\n. n = 6 \/ n = 7)) /\
  (mem_range Pr78 = (\n. n = 7 \/ n = 8)) /\ (mem_range Pr89 = (\n. 8 <= n)) /\
  (mem_range Pr57 = (\n. n = 5 \/ n = 6 \/ n = 7)) /\
  (mem_range Pr68 = (\n. n = 6 \/ n = 7 \/ n = 8)) /\
  (mem_range Pr79 = (\n. 7 <= n)) /\
  (mem_range Pr58 = (\n. n = 5 \/ n = 6 \/ n = 7 \/ n = 8)) /\
  (mem_range Pr69 = (\n. 6 <= n)) /\ (mem_range Pr59 = (\n. 5 <= n))`;;

let size_part = new_recursive_definition part_RECURSION
 `(size_part Pnil = 0) /\
  (size_part (Pcons s h p) = SUC(size_part p)) /\
  (size_part (Pcons6 h f1 p) = SUC(size_part p)) /\
  (size_part (Pcons7 h f1 f2 p) = SUC(size_part p)) /\
  (size_part (Pcons8 h f1 f2 f3 p) = SUC(size_part p))`;;

(* List-like operations; drop_part and take_part recurse on n with a match   *)
(* on the part.                                                              *)
let drop_part = define
 `(drop_part 0 p = p) /\
  (drop_part (SUC n) Pnil = Pnil) /\
  (drop_part (SUC n) (Pcons s h p) = drop_part n p) /\
  (drop_part (SUC n) (Pcons6 h f1 p) = drop_part n p) /\
  (drop_part (SUC n) (Pcons7 h f1 f2 p) = drop_part n p) /\
  (drop_part (SUC n) (Pcons8 h f1 f2 f3 p) = drop_part n p)`;;
let take_part = define
 `(take_part 0 p = Pnil) /\
  (take_part (SUC n) Pnil = Pnil) /\
  (take_part (SUC n) (Pcons s h p) = Pcons s h (take_part n p)) /\
  (take_part (SUC n) (Pcons6 h f1 p) = Pcons6 h f1 (take_part n p)) /\
  (take_part (SUC n) (Pcons7 h f1 f2 p) = Pcons7 h f1 f2 (take_part n p)) /\
  (take_part (SUC n) (Pcons8 h f1 f2 f3 p) =
  Pcons8 h f1 f2 f3 (take_part n p))`;;
let cat_part = new_recursive_definition part_RECURSION
 `(cat_part Pnil q = q) /\
  (cat_part (Pcons s h p) q = Pcons s h (cat_part p q)) /\
  (cat_part (Pcons6 h f1 p) q = Pcons6 h f1 (cat_part p q)) /\
  (cat_part (Pcons7 h f1 f2 p) q = Pcons7 h f1 f2 (cat_part p q)) /\
  (cat_part (Pcons8 h f1 f2 f3 p) q = Pcons8 h f1 f2 f3 (cat_part p q))`;;
let catrev_part = new_recursive_definition part_RECURSION
 `(catrev_part Pnil p2 = p2) /\
  (catrev_part (Pcons s h p1) p2 = catrev_part p1 (Pcons s h p2)) /\
  (catrev_part (Pcons6 h f1 p1) p2 = catrev_part p1 (Pcons6 h f1 p2)) /\
  (catrev_part (Pcons7 h f1 f2 p1) p2 = catrev_part p1 (Pcons7 h f1 f2 p2)) /\
  (catrev_part (Pcons8 h f1 f2 f3 p1) p2 =
  catrev_part p1 (Pcons8 h f1 f2 f3 p2))`;;
let rev_part = new_definition `rev_part p = catrev_part p Pnil`;;
let rot_part = new_definition
  `rot_part n p = cat_part (drop_part n p) (take_part n p)`;;

let SIZE_CAT_PART = prove
 (`!p1 p2. size_part(cat_part p1 p2) = size_part p1 + size_part p2`,
  MATCH_MP_TAC part_INDUCT THEN REWRITE_TAC[cat_part; size_part] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let SIZE_DROP_PART = prove
 (`!n p. size_part(drop_part n p) = size_part p - n`,
  INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[drop_part; size_part; SUB_0] THEN
  STRUCT_CASES_TAC(ISPEC `p:part` (cases "part")) THEN
  ASM_REWRITE_TAC[drop_part; size_part] THEN ARITH_TAC);;
let CAT_TAKE_DROP_PART = prove
 (`!n p. cat_part (take_part n p) (drop_part n p) = p`,
  INDUCT_TAC THEN GEN_TAC THEN REWRITE_TAC[take_part; drop_part; cat_part] THEN
  STRUCT_CASES_TAC(ISPEC `p:part` (cases "part")) THEN
  ASM_REWRITE_TAC[take_part; drop_part; cat_part]);;
let SIZE_ROT_PART = prove
 (`!n p. size_part(rot_part n p) = size_part p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rot_part; SIZE_CAT_PART] THEN
  MP_TAC(SPECL [`n:num`; `p:part`] CAT_TAKE_DROP_PART) THEN
  DISCH_THEN(MP_TAC o AP_TERM `size_part`) THEN REWRITE_TAC[SIZE_CAT_PART] THEN
  ARITH_TAC);;
let SIZE_CATREV_PART = prove
 (`!p1 p2. size_part(catrev_part p1 p2) = size_part p1 + size_part p2`,
  MATCH_MP_TAC part_INDUCT THEN REWRITE_TAC[catrev_part; size_part] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[size_part] THEN ARITH_TAC);;
let SIZE_REV_PART = prove
 (`!p. size_part(rev_part p) = size_part p`,
  REWRITE_TAC[rev_part; SIZE_CATREV_PART; size_part] THEN ARITH_TAC);;

(* The semantics: subpart_loc_move i H x is the dart at relative position i  *)
(* (spoke: edge x; hat: edge (face^2 (edge x)); fan k: edge (face^(k+2)      *)
(* (edge x))), and fitp recurses on the part, the hub dart advancing by face *)
(* at each spoke.                                                            *)
let subpart_loc_move = new_recursive_definition subpart_loc_RECURSION
 `(subpart_loc_move Pspoke H x = edge_map H x) /\
  (subpart_loc_move Phat H x = edge_map H (ITER 2 (face_map H) (edge_map H x)))
  /\
  (subpart_loc_move Pfan1 H x =
  edge_map H (ITER 3 (face_map H) (edge_map H x))) /\
  (subpart_loc_move Pfan2 H x =
  edge_map H (ITER 4 (face_map H) (edge_map H x))) /\
  (subpart_loc_move Pfan3 H x =
  edge_map H (ITER 5 (face_map H) (edge_map H x)))`;;
let fitp = new_recursive_definition part_RECURSION
 `(fitp Pnil H x = T) /\
  (fitp (Pcons s h p) H x =
     (mem_range s (arity H (subpart_loc_move Pspoke H x)) /\
      mem_range h (arity H (subpart_loc_move Phat H x)) /\
      fitp p H (face_map H x))) /\
  (fitp (Pcons6 h f1 p) H x =
     (mem_range Pr66 (arity H (subpart_loc_move Pspoke H x)) /\
      mem_range h (arity H (subpart_loc_move Phat H x)) /\
      mem_range f1 (arity H (subpart_loc_move Pfan1 H x)) /\
      fitp p H (face_map H x))) /\
  (fitp (Pcons7 h f1 f2 p) H x =
     (mem_range Pr77 (arity H (subpart_loc_move Pspoke H x)) /\
      mem_range h (arity H (subpart_loc_move Phat H x)) /\
      mem_range f1 (arity H (subpart_loc_move Pfan1 H x)) /\
      mem_range f2 (arity H (subpart_loc_move Pfan2 H x)) /\
      fitp p H (face_map H x))) /\
  (fitp (Pcons8 h f1 f2 f3 p) H x =
     (mem_range Pr88 (arity H (subpart_loc_move Pspoke H x)) /\
      mem_range h (arity H (subpart_loc_move Phat H x)) /\
      mem_range f1 (arity H (subpart_loc_move Pfan1 H x)) /\
      mem_range f2 (arity H (subpart_loc_move Pfan2 H x)) /\
      mem_range f3 (arity H (subpart_loc_move Pfan3 H x)) /\
      fitp p H (face_map H x)))`;;
let exact_fitp = new_definition
 `exact_fitp H x p <=> (arity H x = size_part p) /\ fitp p H x`;;
(* Fitting a concatenation (Gonthier fitp_cat).                              *)
let FITP_CAT = prove
 (`!p1 p2 H x. fitp (cat_part p1 p2) H x <=>
     fitp p1 H x /\ fitp p2 H (ITER (size_part p1) (face_map H) x)`,
  MATCH_MP_TAC part_INDUCT THEN
  REWRITE_TAC[cat_part; fitp; size_part; ITER] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ITER_COMMUTE] THEN REWRITE_TAC[CONJ_ACI]);;

(* Fitting through drop, catrev and rot.                                     *)
let FITP_DROP = prove
 (`!n p H x. fitp p H x ==> fitp (drop_part n p) H (ITER n (face_map H) x)`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[drop_part; ITER];
    GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `p:part` (cases "part")) THEN
    REWRITE_TAC[drop_part; fitp] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[ITER; GSYM ITER_COMMUTE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;
let FACE_FIXES_OFF = prove
 (`!H:(A)hypermap x. ~(x IN dart H) ==> face_map H x = x`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `H:(A)hypermap` FACE_MAP_PERMUTES) THEN
  REWRITE_TAC[permutes] THEN ASM_MESON_TAC[]);;
let ARITY_ITER_FACE_GEN = prove
 (`!H:(A)hypermap x n. arity H (ITER n (face_map H) x) = arity H x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x IN dart(H:(A)hypermap)` THENL
   [ASM_SIMP_TAC[ARITY_ITER_FACE];
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ETA_AX] o MATCH_MP ITER_FIXED o
                MATCH_MP FACE_FIXES_OFF) THEN ASM_REWRITE_TAC[]]);;
let ITER_FACE_ARITY_GEN = prove
 (`!H:(A)hypermap x. ITER (arity H x) (face_map H) x = x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x IN dart(H:(A)hypermap)` THENL
   [ASM_SIMP_TAC[ITER_FACE_ARITY];
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ETA_AX] o MATCH_MP ITER_FIXED o
                MATCH_MP FACE_FIXES_OFF) THEN ASM_REWRITE_TAC[]]);;
let cat_part_cons = end_itlist CONJ (tl(CONJUNCTS cat_part));;
let CATREV_CAT_PART = prove
 (`!p1 p2 p3. catrev_part p1 (cat_part p2 p3) =
 cat_part (catrev_part p1 p2) p3`,
  MATCH_MP_TAC part_INDUCT THEN REWRITE_TAC[catrev_part] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM cat_part_cons] THEN ASM_REWRITE_TAC[]);;
let CATREV_PART_EQ = prove
 (`!p1 p2. catrev_part p1 p2 = cat_part (rev_part p1) p2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rev_part] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(CONJUNCT1 cat_part)] THEN
  REWRITE_TAC[CATREV_CAT_PART]);;
let FITP_CATREV = prove
 (`!p1 p2 H x. fitp (catrev_part p1 p2) H x <=>
     fitp (rev_part p1) H x /\ fitp p2 H (ITER (size_part p1) (face_map H) x)`,
  REWRITE_TAC[CATREV_PART_EQ; FITP_CAT; SIZE_REV_PART]);;
let FITP_ROT = prove
 (`!n p. n <= size_part p ==>
     !H:(A)hypermap x:A. exact_fitp H x p <=>
     exact_fitp H (ITER n (face_map H) x) (rot_part n p)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[exact_fitp; SIZE_ROT_PART; ARITY_ITER_FACE_GEN] THEN
  ASM_CASES_TAC `arity H (x:A) = size_part p` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `size_part(take_part n p) = n` ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `p:part`] CAT_TAKE_DROP_PART) THEN
    DISCH_THEN(MP_TAC o AP_TERM `size_part`) THEN
    REWRITE_TAC[SIZE_CAT_PART;
                SIZE_DROP_PART] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
 `ITER (size_part(drop_part n p)) (face_map H) (ITER n (face_map H) (x:A)) = x`
   ASSUME_TAC THENL
   [REWRITE_TAC[SIZE_DROP_PART; ITER_ADD] THEN
    SUBGOAL_THEN `size_part p - n + n = arity H (x:A)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
     MATCH_ACCEPT_TAC ITER_FACE_ARITY_GEN; ALL_TAC] THEN
  MP_TAC(ISPECL [`take_part n p`; `drop_part n p`; `H:(A)hypermap`; `x:A`
  ] FITP_CAT) THEN
  REWRITE_TAC[CAT_TAKE_DROP_PART] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rot_part; FITP_CAT] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONJ_ACI]);;

(* Accessors and the mirror part.                                            *)
let get_spoke = new_recursive_definition part_RECURSION
 `(get_spoke Pnil = Pr59) /\ (get_spoke (Pcons s h p) = s) /\
  (get_spoke (Pcons6 h f1 p) = Pr66) /\
  (get_spoke (Pcons7 h f1 f2 p) = Pr77) /\
  (get_spoke (Pcons8 h f1 f2 f3 p) = Pr88)`;;
let next_hat = new_recursive_definition part_RECURSION
 `(next_hat h0 Pnil = h0) /\ (next_hat h0 (Pcons s h p) = h) /\
  (next_hat h0 (Pcons6 h f1 p) = h) /\ (next_hat h0 (Pcons7 h f1 f2 p) = h) /\
  (next_hat h0 (Pcons8 h f1 f2 f3 p) = h)`;;
let get_hat = new_definition `get_hat p = next_hat Pr59 p`;;
let get_fan1r = new_recursive_definition part_RECURSION
 `(get_fan1r Pnil = Pr59) /\ (get_fan1r (Pcons s h p) = Pr59) /\
  (get_fan1r (Pcons6 h f1 p) = f1) /\ (get_fan1r (Pcons7 h f1 f2 p) = f1) /\
  (get_fan1r (Pcons8 h f1 f2 f3 p) = f1)`;;
let get_fan2r = new_recursive_definition part_RECURSION
 `(get_fan2r Pnil = Pr59) /\ (get_fan2r (Pcons s h p) = Pr59) /\
  (get_fan2r (Pcons6 h f1 p) = Pr59) /\ (get_fan2r (Pcons7 h f1 f2 p) = f2) /\
  (get_fan2r (Pcons8 h f1 f2 f3 p) = f2)`;;
let get_fan3r = new_recursive_definition part_RECURSION
 `(get_fan3r Pnil = Pr59) /\ (get_fan3r (Pcons s h p) = Pr59) /\
  (get_fan3r (Pcons6 h f1 p) = Pr59) /\
  (get_fan3r (Pcons7 h f1 f2 p) = Pr59) /\
  (get_fan3r (Pcons8 h f1 f2 f3 p) = f3)`;;
let get_fan1l = new_recursive_definition part_RECURSION
 `(get_fan1l Pnil = Pr59) /\ (get_fan1l (Pcons s h p) = Pr59) /\
  (get_fan1l (Pcons6 h f1 p) = f1) /\ (get_fan1l (Pcons7 h f1 f2 p) = f2) /\
  (get_fan1l (Pcons8 h f1 f2 f3 p) = f3)`;;
let get_fan2l = new_recursive_definition part_RECURSION
 `(get_fan2l Pnil = Pr59) /\ (get_fan2l (Pcons s h p) = Pr59) /\
  (get_fan2l (Pcons6 h f1 p) = Pr59) /\ (get_fan2l (Pcons7 h f1 f2 p) = f1) /\
  (get_fan2l (Pcons8 h f1 f2 f3 p) = f2)`;;
let get_fan3l = new_recursive_definition part_RECURSION
 `(get_fan3l Pnil = Pr59) /\ (get_fan3l (Pcons s h p) = Pr59) /\
  (get_fan3l (Pcons6 h f1 p) = Pr59) /\
  (get_fan3l (Pcons7 h f1 f2 p) = Pr59) /\
  (get_fan3l (Pcons8 h f1 f2 f3 p) = f1)`;;
let mirror_part_rec = new_recursive_definition part_RECURSION
 `(mirror_part_rec Pnil h0 rp = rp) /\
  (mirror_part_rec (Pcons s h p) h0 rp =
  mirror_part_rec p h0 (Pcons s (next_hat h0 p) rp)) /\
  (mirror_part_rec (Pcons6 h f1 p) h0 rp =
  mirror_part_rec p h0 (Pcons6 (next_hat h0 p) f1 rp)) /\
  (mirror_part_rec (Pcons7 h f1 f2 p) h0 rp =
  mirror_part_rec p h0 (Pcons7 (next_hat h0 p) f2 f1 rp)) /\
  (mirror_part_rec (Pcons8 h f1 f2 f3 p) h0 rp =
  mirror_part_rec p h0 (Pcons8 (next_hat h0 p) f3 f2 f1 rp))`;;
let mirror_part = new_definition
  `mirror_part p = mirror_part_rec p (get_hat p) Pnil`;;
let SIZE_MIRROR_REC = prove
 (`!p h0 rp. size_part(mirror_part_rec p h0 rp) = size_part p + size_part rp`,
  MATCH_MP_TAC part_INDUCT THEN REWRITE_TAC[mirror_part_rec] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[size_part] THEN ARITH_TAC);;
let SIZE_MIRROR_PART = prove
 (`!p. size_part(mirror_part p) = size_part p`,
  REWRITE_TAC[mirror_part; SIZE_MIRROR_REC; size_part] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Comparison of parts.  FITP_CMP and FITP_MEET need only MEM_CMP_RANGE and  *)
(* MEM_MEET_RANGE, not the exact table values, so cmp_range is defined       *)
(* semantically (subset, disjoint or straddle), with the same values as      *)
(* Gonthier's explicit table.                                                *)
(* ------------------------------------------------------------------------- *)
let part_rel_INDUCT,part_rel_RECURSION = define_type
  "part_rel = Pdisjoint | Pstraddle | Psubset";;
let apply_part_rel = new_recursive_definition part_rel_RECURSION
 `(apply_part_rel Pdisjoint b = F) /\ (apply_part_rel Pstraddle b = b) /\
  (apply_part_rel Psubset b = T)`;;
let notPsubset = new_recursive_definition part_rel_RECURSION
 `(notPsubset Pdisjoint = Pdisjoint) /\ (notPsubset Pstraddle = Pstraddle) /\
  (notPsubset Psubset = Pstraddle)`;;
let meet_prel = new_recursive_definition part_rel_RECURSION
 `(meet_prel Pdisjoint c' = Pdisjoint) /\
  (meet_prel Pstraddle c' = notPsubset c') /\
  (meet_prel Psubset c' = c')`;;
let cmp_range = new_definition
 `cmp_range r1 r2 =
    if (!n. mem_range r1 n ==> mem_range r2 n) then Psubset
    else if (!n. mem_range r1 n ==> ~(mem_range r2 n)) then Pdisjoint
    else Pstraddle`;;
let MEM_CMP_RANGE = prove
 (`!r1 n. mem_range r1 n
     ==> !r2. mem_range r2 n =
     apply_part_rel (cmp_range r1 r2) (mem_range r2 n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_range] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[apply_part_rel] THEN
  ASM_MESON_TAC[]);;
let cmp_part = define
 `(cmp_part p Pnil = Psubset) /\
  (cmp_part Pnil (Pcons sq hq q) = Pstraddle) /\
  (cmp_part Pnil (Pcons6 hq g1 q) = Pstraddle) /\
  (cmp_part Pnil (Pcons7 hq g1 g2 q) = Pstraddle) /\
  (cmp_part Pnil (Pcons8 hq g1 g2 g3 q) = Pstraddle) /\
  (cmp_part (Pcons sp hp p) (Pcons sq hq q) =
     meet_prel (cmp_range sp sq) (meet_prel (cmp_range hp hq) (cmp_part p q)))
     /\
  (cmp_part (Pcons6 hp f1 p) (Pcons sq hq q) =
     meet_prel (cmp_range Pr66 sq)
     (meet_prel (cmp_range hp hq) (cmp_part p q))) /\
  (cmp_part (Pcons7 hp f1 f2 p) (Pcons sq hq q) =
     meet_prel (cmp_range Pr77 sq)
     (meet_prel (cmp_range hp hq) (cmp_part p q))) /\
  (cmp_part (Pcons8 hp f1 f2 f3 p) (Pcons sq hq q) =
     meet_prel (cmp_range Pr88 sq)
     (meet_prel (cmp_range hp hq) (cmp_part p q))) /\
  (cmp_part (Pcons sp hp p) (Pcons6 hq f1q q) =
     meet_prel (notPsubset (cmp_range sp Pr66))
     (meet_prel (cmp_range hp hq) (cmp_part p q))) /\
  (cmp_part (Pcons6 hp f1p p) (Pcons6 hq f1q q) =
     meet_prel (cmp_range hp hq)
     (meet_prel (cmp_range f1p f1q) (cmp_part p q))) /\
  (cmp_part (Pcons7 hp a1 a2 p) (Pcons6 hq f1q q) = Pdisjoint) /\
  (cmp_part (Pcons8 hp a1 a2 a3 p) (Pcons6 hq f1q q) = Pdisjoint) /\
  (cmp_part (Pcons sp hp p) (Pcons7 hq f1q f2q q) =
     meet_prel (notPsubset (cmp_range sp Pr77))
     (meet_prel (cmp_range hp hq) (cmp_part p q))) /\
  (cmp_part (Pcons7 hp f1p f2p p) (Pcons7 hq f1q f2q q) =
     meet_prel (cmp_range hp hq)
 (meet_prel (cmp_range f1p f1q)
 (meet_prel (cmp_range f2p f2q) (cmp_part p q)))) /\
  (cmp_part (Pcons6 hp a1 p) (Pcons7 hq f1q f2q q) = Pdisjoint) /\
  (cmp_part (Pcons8 hp a1 a2 a3 p) (Pcons7 hq f1q f2q q) = Pdisjoint) /\
  (cmp_part (Pcons sp hp p) (Pcons8 hq f1q f2q f3q q) =
     meet_prel (notPsubset (cmp_range sp Pr88))
     (meet_prel (cmp_range hp hq) (cmp_part p q))) /\
  (cmp_part (Pcons8 hp f1p f2p f3p p) (Pcons8 hq f1q f2q f3q q) =
     meet_prel (cmp_range hp hq)
 (meet_prel (cmp_range f1p f1q)
 (meet_prel (cmp_range f2p f2q)
 (meet_prel (cmp_range f3p f3q) (cmp_part p q))))) /\
  (cmp_part (Pcons6 hp a1 p) (Pcons8 hq f1q f2q f3q q) = Pdisjoint) /\
  (cmp_part (Pcons7 hp a1 a2 p) (Pcons8 hq f1q f2q f3q q) = Pdisjoint)`;;

(* ------------------------------------------------------------------------- *)
(* part_update and pcons_.  Gonthier's part_update quantifies over all maps  *)
(* G inside the definition; a HOL definition cannot bind the dart type, so   *)
(* the hypermap H is an explicit argument, instantiated at the use sites.    *)
(* ------------------------------------------------------------------------- *)
let pcons_s = new_definition `pcons_s s = \p. Pcons s Pr59 p`;;
let pcons_ = new_definition `pcons_ n = ITER n (Pcons Pr59 Pr59) Pnil`;;
let part_update = new_definition
 `part_update (H:(A)hypermap) (fp:prange->part->part) i <=>
    !r p. size_part(fp r p) = SUC(size_part p) /\
          (!x. fitp (fp r p) H x
             ==> mem_range r (arity H (subpart_loc_move i H x)) /\
                 (!r'. mem_range r' (arity H (subpart_loc_move i H x)) ==>
                 fitp (fp r' p) H x))`;;
let upd_tac = REWRITE_TAC[part_update] THEN REPEAT GEN_TAC THEN BETA_TAC THEN
              REWRITE_TAC[size_part; fitp] THEN REPEAT STRIP_TAC THEN
              ASM_REWRITE_TAC[];;
let UPDATEPS =
 prove(`!(H:(A)hypermap) h. part_update H (\r p. Pcons r h p) Pspoke`
 , upd_tac);;
let UPDATEPH =
 prove(`!(H:(A)hypermap) s. part_update H (\r p. Pcons s r p) Phat`, upd_tac);;
let UPDATEP6H =
 prove(`!(H:(A)hypermap) f1. part_update H (\r p. Pcons6 r f1 p) Phat`
 , upd_tac);;
let UPDATEP6F1 =
 prove(`!(H:(A)hypermap) h. part_update H (\r p. Pcons6 h r p) Pfan1`
 , upd_tac);;
let UPDATEP7H =
 prove(`!(H:(A)hypermap) f1 f2. part_update H (\r p. Pcons7 r f1 f2 p) Phat`
 , upd_tac);;
let UPDATEP7F1 =
 prove(`!(H:(A)hypermap) h f2. part_update H (\r p. Pcons7 h r f2 p) Pfan1`
 , upd_tac);;
let UPDATEP7F2 =
 prove(`!(H:(A)hypermap) h f1. part_update H (\r p. Pcons7 h f1 r p) Pfan2`
 , upd_tac);;
let UPDATEP8H =
 prove(`!(H:(A)hypermap) f1 f2 f3. part_update H (\r p. Pcons8 r f1 f2 f3 p)
 Phat`, upd_tac);;
let UPDATEP8F1 =
 prove(`!(H:(A)hypermap) h f2 f3. part_update H (\r p. Pcons8 h r f2 f3 p)
 Pfan1`, upd_tac);;
let UPDATEP8F2 =
 prove(`!(H:(A)hypermap) h f1 f3. part_update H (\r p. Pcons8 h f1 r f3 p)
 Pfan2`, upd_tac);;
let UPDATEP8F3 =
 prove(`!(H:(A)hypermap) h f1 f2. part_update H (\r p. Pcons8 h f1 f2 r p)
 Pfan3`, upd_tac);;
let PCONS__CLAUSES = prove
 (`pcons_ 0 = Pnil /\ (!n. pcons_ (SUC n) = Pcons Pr59 Pr59 (pcons_ n))`,
  REWRITE_TAC[pcons_; ITER]);;
let SIZE_PCONS_ = prove
 (`!n. size_part(pcons_ n) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[PCONS__CLAUSES; size_part]);;
let FITP_PCONS_ = prove
 (`!H:(A)hypermap. pentagonal H ==> !n x. x IN dart H ==> fitp (pcons_ n) H x`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN X_GEN_TAC `x:A` THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[PCONS__CLAUSES; fitp; mem_range; subpart_loc_move] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `4 < n ==> 5 <= n`) THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[pentagonal]) THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART];
    MATCH_MP_TAC(ARITH_RULE `4 < n ==> 5 <= n`) THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[pentagonal]) THEN
    MATCH_MP_TAC EDGE_MAP_IN_DART THEN MATCH_MP_TAC ITER_PERMUTES_IN THEN
    ASM_SIMP_TAC[FACE_MAP_PERMUTES; EDGE_MAP_IN_DART];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[FACE_MAP_IN_DART]]);;
let EXACT_FITP_PCONS_ = prove
 (`!H:(A)hypermap x. pentagonal H /\ x IN dart H ==>
 exact_fitp H x (pcons_ (arity H x))`,
  REWRITE_TAC[exact_fitp; SIZE_PCONS_] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[FITP_PCONS_]);;

(* ------------------------------------------------------------------------- *)
(* The meet of parts.  meet_range goes through interval bounds: every prange *)
(* is an interval [rlo, rhi] (rbounded is false for the five unbounded ones, *)
(* whose rhi is then unused), and the meet is the intersection of the        *)
(* intervals mapped back by prange_of_bounds.  It agrees with Gonthier's     *)
(* table on all nonempty intersections; the empty ones are irrelevant        *)
(* (MEM_MEET_RANGE is vacuous there).  MEM_MEET_RANGE is an exhaustive 15 x  *)
(* 15 case analysis.                                                         *)
(* ------------------------------------------------------------------------- *)
let rlo = new_recursive_definition prange_RECURSION
 `(rlo Pr55 = 5) /\ (rlo Pr66 = 6) /\ (rlo Pr77 = 7) /\ (rlo Pr88 = 8) /\
  (rlo Pr99 = 9) /\
  (rlo Pr56 = 5) /\ (rlo Pr67 = 6) /\ (rlo Pr78 = 7) /\ (rlo Pr89 = 8) /\
  (rlo Pr57 = 5) /\ (rlo Pr68 = 6) /\ (rlo Pr79 = 7) /\
  (rlo Pr58 = 5) /\ (rlo Pr69 = 6) /\ (rlo Pr59 = 5)`;;
let rhi = new_recursive_definition prange_RECURSION
 `(rhi Pr55 = 5) /\ (rhi Pr66 = 6) /\ (rhi Pr77 = 7) /\ (rhi Pr88 = 8) /\
  (rhi Pr99 = 0) /\
  (rhi Pr56 = 6) /\ (rhi Pr67 = 7) /\ (rhi Pr78 = 8) /\ (rhi Pr89 = 0) /\
  (rhi Pr57 = 7) /\ (rhi Pr68 = 8) /\ (rhi Pr79 = 0) /\
  (rhi Pr58 = 8) /\ (rhi Pr69 = 0) /\ (rhi Pr59 = 0)`;;
let rbounded = new_recursive_definition prange_RECURSION
 `(rbounded Pr55 = T) /\ (rbounded Pr66 = T) /\ (rbounded Pr77 = T) /\
  (rbounded Pr88 = T) /\
  (rbounded Pr99 = F) /\ (rbounded Pr56 = T) /\ (rbounded Pr67 = T) /\
  (rbounded Pr78 = T) /\
  (rbounded Pr89 = F) /\ (rbounded Pr57 = T) /\ (rbounded Pr68 = T) /\
  (rbounded Pr79 = F) /\
  (rbounded Pr58 = T) /\ (rbounded Pr69 = F) /\ (rbounded Pr59 = F)`;;
let prange_of_bounds = new_definition
 `prange_of_bounds lo b hi =
    if b then
      if lo = 5 then
 (if hi = 5 then Pr55 else if hi = 6 then Pr56
 else if hi = 7 then Pr57 else Pr58)
      else if lo = 6
      then (if hi = 6 then Pr66 else if hi = 7 then Pr67 else Pr68)
      else if lo = 7 then (if hi = 7 then Pr77 else Pr78)
      else if lo = 8 then Pr88
      else Pr99
    else
      if lo = 5 then Pr59 else if lo = 6 then Pr69 else if lo = 7 then Pr79
      else if lo = 8 then Pr89 else Pr99`;;
let meet_range = new_definition
 `meet_range r r' =
    prange_of_bounds (MAX (rlo r) (rlo r'))
                     (rbounded r \/ rbounded r')
                     (if rbounded r
                     then (if rbounded r' then MIN (rhi r) (rhi r') else rhi r)
                      else rhi r')`;;
let MEM_MEET_RANGE = prove
 (`!r1 r2 n. mem_range r1 n /\ mem_range r2 n ==>
 mem_range (meet_range r1 r2) n`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r1:prange` (cases "prange")) THEN
  STRUCT_CASES_TAC(ISPEC `r2:prange` (cases "prange")) THEN
  REWRITE_TAC[meet_range; rlo; rhi; rbounded] THEN
  REWRITE_TAC[MAX; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[prange_of_bounds] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mem_range] THEN ARITH_TAC);;
let meet_part = define
 `(meet_part p Pnil = p) /\
  (meet_part Pnil (Pcons sq hq q) = Pnil) /\
  (meet_part Pnil (Pcons6 hq g1 q) = Pnil) /\
  (meet_part Pnil (Pcons7 hq g1 g2 q) = Pnil) /\
  (meet_part Pnil (Pcons8 hq g1 g2 g3 q) = Pnil) /\
  (meet_part (Pcons sp hp p) (Pcons sq hq q) =
     Pcons (meet_range sp sq) (meet_range hp hq) (meet_part p q)) /\
  (meet_part (Pcons6 hp f1 p) (Pcons sq hq q) =
     Pcons6 (meet_range hp hq) f1 (meet_part p q)) /\
  (meet_part (Pcons7 hp f1 f2 p) (Pcons sq hq q) =
     Pcons7 (meet_range hp hq) f1 f2 (meet_part p q)) /\
  (meet_part (Pcons8 hp f1 f2 f3 p) (Pcons sq hq q) =
     Pcons8 (meet_range hp hq) f1 f2 f3 (meet_part p q)) /\
  (meet_part (Pcons sp hp p) (Pcons6 hq f1q q) =
     Pcons6 (meet_range hp hq) f1q (meet_part p q)) /\
  (meet_part (Pcons6 hp f1p p) (Pcons6 hq f1q q) =
     Pcons6 (meet_range hp hq) (meet_range f1p f1q) (meet_part p q)) /\
  (meet_part (Pcons7 hp a1 a2 p) (Pcons6 hq f1q q) = Pcons7 hp a1 a2 p) /\
  (meet_part (Pcons8 hp a1 a2 a3 p) (Pcons6 hq f1q q) = Pcons8 hp a1 a2 a3 p)
  /\
  (meet_part (Pcons sp hp p) (Pcons7 hq f1q f2q q) =
     Pcons7 (meet_range hp hq) f1q f2q (meet_part p q)) /\
  (meet_part (Pcons7 hp f1p f2p p) (Pcons7 hq f1q f2q q) =
     Pcons7 (meet_range hp hq) (meet_range f1p f1q) (meet_range f2p f2q)
     (meet_part p q)) /\
  (meet_part (Pcons6 hp a1 p) (Pcons7 hq f1q f2q q) = Pcons6 hp a1 p) /\
  (meet_part (Pcons8 hp a1 a2 a3 p) (Pcons7 hq f1q f2q q) =
  Pcons8 hp a1 a2 a3 p) /\
  (meet_part (Pcons sp hp p) (Pcons8 hq f1q f2q f3q q) =
     Pcons8 (meet_range hp hq) f1q f2q f3q (meet_part p q)) /\
  (meet_part (Pcons8 hp f1p f2p f3p p) (Pcons8 hq f1q f2q f3q q) =
     Pcons8 (meet_range hp hq) (meet_range f1p f1q) (meet_range f2p f2q)
     (meet_range f3p f3q) (meet_part p q)) /\
  (meet_part (Pcons6 hp a1 p) (Pcons8 hq f1q f2q f3q q) = Pcons6 hp a1 p) /\
  (meet_part (Pcons7 hp a1 a2 p) (Pcons8 hq f1q f2q f3q q) =
  Pcons7 hp a1 a2 p)`;;
let SIZE_MEET_PART = prove
 (`!q p. size_part(meet_part p q) = size_part p`,
  MATCH_MP_TAC part_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p:part` (cases "part")) THEN
  ASM_REWRITE_TAC[meet_part; size_part]);;
(* The Pnil case is handled separately: its premise is not an induction      *)
(* hypothesis.                                                               *)
let FITP_MEET = prove
 (`!q p (H:(A)hypermap) (x:A).
     fitp p H x /\ fitp q H x ==> fitp (meet_part p q) H x`,
  MATCH_MP_TAC part_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[meet_part] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p:part` (cases "part")) THEN
  REWRITE_TAC[meet_part; fitp] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST[MATCH_MP_TAC MEM_MEET_RANGE THEN ASM_REWRITE_TAC[];
        REMOVE_THEN "IH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;
let EXACT_FITP_MEET = prove
 (`!p q (H:(A)hypermap) (x:A).
     exact_fitp H x p /\ fitp q H x ==> exact_fitp H x (meet_part p q)`,
  REWRITE_TAC[exact_fitp; SIZE_MEET_PART] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FITP_MEET THEN ASM_REWRITE_TAC[]);;

let APPLY_MEET_CONS = prove
 (`!a b u v. u = apply_part_rel a u /\ v = apply_part_rel b v
     ==> (u /\ v) = apply_part_rel (meet_prel a b) (u /\ v)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a:part_rel` (cases "part_rel")) THEN
  STRUCT_CASES_TAC(ISPEC `b:part_rel` (cases "part_rel")) THEN
  REWRITE_TAC[meet_prel; notPsubset; apply_part_rel] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;
let LEAF_CONS3 = prove
 (`!a b c u v w.
     u = apply_part_rel a u /\ v = apply_part_rel b v /\ w = apply_part_rel c w
     ==>
 (u /\ v /\ w <=> apply_part_rel (meet_prel a (meet_prel b c)) (u /\ v /\ w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1")
    (CONJUNCTS_THEN2 (LABEL_TAC "C2") (LABEL_TAC "C3"))) THEN
  USE_THEN "C1" (fun c1 -> USE_THEN "C2" (fun c2 -> USE_THEN "C3" (fun c3 ->
    ACCEPT_TAC(MATCH_MP APPLY_MEET_CONS
      (CONJ c1 (MATCH_MP APPLY_MEET_CONS (CONJ c2 c3))))))));;
let LEAF_CONS4 = prove
 (`!a b c d u v w t.
     u = apply_part_rel a u /\ v = apply_part_rel b v /\
     w = apply_part_rel c w /\
     t = apply_part_rel d t
     ==> (u /\ v /\ w /\ t <=>
          apply_part_rel (meet_prel a (meet_prel b (meet_prel c d)))
          (u /\ v /\ w /\ t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "C2")
    (CONJUNCTS_THEN2 (LABEL_TAC "C3") (LABEL_TAC "C4")))) THEN
  USE_THEN "C1"
 (fun c1 -> USE_THEN "C2"
   (fun c2 -> USE_THEN "C3" (fun c3 -> USE_THEN "C4" (fun c4 ->
    ACCEPT_TAC(MATCH_MP APPLY_MEET_CONS (CONJ c1 (MATCH_MP APPLY_MEET_CONS
      (CONJ c2 (MATCH_MP APPLY_MEET_CONS (CONJ c3 c4)))))))))));;
let LEAF_CONS5 = prove
 (`!a b c d e u v w t s.
     u = apply_part_rel a u /\ v = apply_part_rel b v /\
     w = apply_part_rel c w /\
     t = apply_part_rel d t /\ s = apply_part_rel e s
     ==> (u /\ v /\ w /\ t /\ s <=>
          apply_part_rel
          (meet_prel a (meet_prel b (meet_prel c (meet_prel d e))))
                         (u /\ v /\ w /\ t /\ s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    match CONJUNCTS th with
    | [c1;c2;c3;c4;c5] ->
       ACCEPT_TAC(MATCH_MP APPLY_MEET_CONS (CONJ c1 (MATCH_MP APPLY_MEET_CONS
         (CONJ c2 (MATCH_MP APPLY_MEET_CONS (CONJ c3
                                  (MATCH_MP APPLY_MEET_CONS (CONJ c4 c5))))))))
    | _ -> failwith "LEAF_CONS5"));;
(* The cases where q has more locations than the plain pattern p compares:   *)
(* the extra fan conjuncts are unconstrained and the notPsubset head never   *)
(* yields Psubset, so the result is Pstraddle (reflexive case) or Pdisjoint  *)
(* (some conjunct false).                                                    *)
let LEAF_NS = prove
 (`!a b c u v w t.
     u = apply_part_rel a u /\ v = apply_part_rel b v /\
     t = apply_part_rel c t /\
     (w ==> t)
     ==> (u /\ v /\ w <=>
          apply_part_rel (meet_prel (notPsubset a) (meet_prel b c))
          (u /\ v /\ w))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a:part_rel` (cases "part_rel")) THEN
  STRUCT_CASES_TAC(ISPEC `b:part_rel` (cases "part_rel")) THEN
  STRUCT_CASES_TAC(ISPEC `c:part_rel` (cases "part_rel")) THEN
  REWRITE_TAC[meet_prel; notPsubset; apply_part_rel] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let ns_derive =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC LEAF_NS THEN
  EXISTS_TAC `t:bool` THEN REPEAT CONJ_TAC THEN
  FIRST[FIRST_ASSUM MATCH_ACCEPT_TAC; CONV_TAC TAUT];;
let LEAF_NS1 = prove
 (`!a b c u v f t.
     u = apply_part_rel a u /\ v = apply_part_rel b v /\ t = apply_part_rel c t
     ==> (u /\ v /\ f /\ t <=>
          apply_part_rel (meet_prel (notPsubset a) (meet_prel b c))
          (u /\ v /\ f /\ t))`,
  ns_derive);;
let LEAF_NS2 = prove
 (`!a b c u v f1 f2 t.
     u = apply_part_rel a u /\ v = apply_part_rel b v /\ t = apply_part_rel c t
     ==> (u /\ v /\ f1 /\ f2 /\ t <=>
          apply_part_rel (meet_prel (notPsubset a) (meet_prel b c))
          (u /\ v /\ f1 /\ f2 /\ t))`,
  ns_derive);;
let LEAF_NS3 = prove
 (`!a b c u v f1 f2 f3 t.
     u = apply_part_rel a u /\ v = apply_part_rel b v /\ t = apply_part_rel c t
     ==> (u /\ v /\ f1 /\ f2 /\ f3 /\ t <=>
          apply_part_rel (meet_prel (notPsubset a) (meet_prel b c))
          (u /\ v /\ f1 /\ f2 /\ f3 /\ t))`,
  ns_derive);;
let LEAF_TAC lemma : tactic = fun (asl,w) ->
  let l,r = dest_iff w in
  let conjs = conjuncts l in
  let rel = rand(rator r) in
  let rec dest_meet t =
    try let f,args = strip_comb t in
        if fst(dest_const f) = "meet_prel"
        then hd args :: dest_meet (hd(tl args))
        else [t]
    with _ -> [t] in
  let rels0 = dest_meet rel in
  let rels = map (fun t ->
      try let f,args = strip_comb t in
          if fst(dest_const f) = "notPsubset" then hd args else t
      with _ -> t) rels0 in
  (MP_TAC(ISPECL (rels @ conjs) lemma) THEN DISCH_THEN MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THEN ASM_MESON_TAC[MEM_CMP_RANGE]) (asl,w);;
let disj_leaf =
  REWRITE_TAC[apply_part_rel; mem_range] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mem_range]) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;
let branch_prefix =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[fitp] THEN DISCH_THEN STRIP_ASSUME_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `q:part` (cases "part")) THEN
  REWRITE_TAC[cmp_part; fitp];;
let FITP_CMP = prove
 (`!p (H:(A)hypermap) (x:A). fitp p H x
     ==> !q. fitp q H x <=> apply_part_rel (cmp_part p q) (fitp q H x)`,
  MATCH_MP_TAC part_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[fitp] THEN GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC `q:part` (cases "part")) THEN
    REWRITE_TAC[cmp_part; fitp; apply_part_rel];
    branch_prefix THENL
     [REWRITE_TAC[apply_part_rel]; LEAF_TAC LEAF_CONS3;
      LEAF_TAC LEAF_NS1; LEAF_TAC LEAF_NS2; LEAF_TAC LEAF_NS3];
    branch_prefix THENL
     [REWRITE_TAC[apply_part_rel]; LEAF_TAC LEAF_CONS3;
      ASM_REWRITE_TAC[] THEN LEAF_TAC LEAF_CONS3; disj_leaf; disj_leaf];
    branch_prefix THENL
     [REWRITE_TAC[apply_part_rel]; LEAF_TAC LEAF_CONS3;
      disj_leaf; ASM_REWRITE_TAC[] THEN LEAF_TAC LEAF_CONS4; disj_leaf];
    branch_prefix THENL
     [REWRITE_TAC[apply_part_rel]; LEAF_TAC LEAF_CONS3;
      disj_leaf; disj_leaf; ASM_REWRITE_TAC[] THEN LEAF_TAC LEAF_CONS5]]);;

(* ------------------------------------------------------------------------- *)
(* Splitting parts: definitions and sizes.  Gonthier's good_split and        *)
(* split_part are large matches on (i, drop_part j p) with literal Pr66,     *)
(* Pr77, Pr88 sub-patterns; here they are layered into per-location          *)
(* auxiliary functions (gsplit_spoke, ..., ssplit_fan3 by part_RECURSION,    *)
(* the prange literals tested by conditionals) and a top level by            *)
(* subpart_loc_RECURSION.  Gonthier's default result p is cat_part (take j   *)
(* p) (drop j p), so the auxiliary functions return the frame unchanged in   *)
(* the default case, the same value.  CMP_RANGE_CONV evaluates the semantic  *)
(* cmp_range on literals by deciding its two universally quantified          *)
(* conditions (true by ARITH_RULE, false by a witness in 5..12).             *)
(* ------------------------------------------------------------------------- *)
let DECIDE_FORALL_CONV tm =
  if is_forall tm then
    (try EQT_INTRO(ARITH_RULE tm)
     with _ ->
       let rec tryk k =
         if k > 12 then failwith "DECIDE_FORALL_CONV" else
         try EQF_INTRO(prove(mk_neg tm,
               REWRITE_TAC[NOT_FORALL_THM] THEN
               EXISTS_TAC(mk_small_numeral k) THEN ARITH_TAC))
         with _ -> tryk (k+1) in
       tryk 5)
  else failwith "DECIDE_FORALL_CONV";;
let CMP_RANGE_CONV : conv =
  REWRITE_CONV[cmp_range; mem_range] THENC
  ONCE_DEPTH_CONV DECIDE_FORALL_CONV THENC REWRITE_CONV[];;
let prange_lo = new_definition
 `prange_lo k = if k = 5 then Pr55 else if k = 6 then Pr56 else
                if k = 7 then Pr57 else if k = 8 then Pr58 else Pr59`;;
let prange_hi = new_definition
 `prange_hi k = if k = 5 then Pr69 else if k = 6 then Pr79 else
                if k = 7 then Pr89 else if k = 8 then Pr99 else Pr59`;;
let good_rsplit = new_definition
 `good_rsplit k r <=> cmp_range r (prange_lo k) = Pstraddle`;;
let split_range = new_definition
 `split_range k lo r =
  meet_range ((if lo then prange_lo else prange_hi) k) r`;;
let gsplit_spoke = new_recursive_definition part_RECURSION
 `(gsplit_spoke k Pnil = F) /\
  (gsplit_spoke k (Pcons s h p) = good_rsplit k s) /\
  (gsplit_spoke k (Pcons6 h f1 p) = F) /\
  (gsplit_spoke k (Pcons7 h f1 f2 p) = F) /\
  (gsplit_spoke k (Pcons8 h f1 f2 f3 p) = F)`;;
let gsplit_hat = new_recursive_definition part_RECURSION
 `(gsplit_hat k Pnil = F) /\
  (gsplit_hat k (Pcons s h p) = good_rsplit k h) /\
  (gsplit_hat k (Pcons6 h f1 p) = good_rsplit k h) /\
  (gsplit_hat k (Pcons7 h f1 f2 p) = good_rsplit k h) /\
  (gsplit_hat k (Pcons8 h f1 f2 f3 p) = good_rsplit k h)`;;
let gsplit_fan1 = new_recursive_definition part_RECURSION
 `(gsplit_fan1 k Pnil = F) /\
  (gsplit_fan1 k (Pcons s h p) =
     (if s = Pr66 \/ s = Pr77 \/ s = Pr88 then good_rsplit k Pr59 else F)) /\
  (gsplit_fan1 k (Pcons6 h f1 p) = good_rsplit k f1) /\
  (gsplit_fan1 k (Pcons7 h f1 f2 p) = good_rsplit k f1) /\
  (gsplit_fan1 k (Pcons8 h f1 f2 f3 p) = good_rsplit k f1)`;;
let gsplit_fan2 = new_recursive_definition part_RECURSION
 `(gsplit_fan2 k Pnil = F) /\
  (gsplit_fan2 k (Pcons s h p) =
     (if s = Pr77 \/ s = Pr88 then good_rsplit k Pr59 else F)) /\
  (gsplit_fan2 k (Pcons6 h f1 p) = F) /\
  (gsplit_fan2 k (Pcons7 h f1 f2 p) = good_rsplit k f2) /\
  (gsplit_fan2 k (Pcons8 h f1 f2 f3 p) = good_rsplit k f2)`;;
let gsplit_fan3 = new_recursive_definition part_RECURSION
 `(gsplit_fan3 k Pnil = F) /\
  (gsplit_fan3 k (Pcons s h p) =
     (if s = Pr88 then good_rsplit k Pr59 else F)) /\
  (gsplit_fan3 k (Pcons6 h f1 p) = F) /\
  (gsplit_fan3 k (Pcons7 h f1 f2 p) = F) /\
  (gsplit_fan3 k (Pcons8 h f1 f2 f3 p) = good_rsplit k f3)`;;
let good_split = new_recursive_definition subpart_loc_RECURSION
 `(good_split Pspoke j k p = gsplit_spoke k (drop_part j p)) /\
  (good_split Phat j k p = gsplit_hat k (drop_part j p)) /\
  (good_split Pfan1 j k p = gsplit_fan1 k (drop_part j p)) /\
  (good_split Pfan2 j k p = gsplit_fan2 k (drop_part j p)) /\
  (good_split Pfan3 j k p = gsplit_fan3 k (drop_part j p))`;;
let ssplit_spoke = new_recursive_definition part_RECURSION
 `(ssplit_spoke k lo Pnil = Pnil) /\
  (ssplit_spoke k lo (Pcons s h p) = Pcons (split_range k lo s) h p) /\
  (ssplit_spoke k lo (Pcons6 h f1 p) = Pcons6 h f1 p) /\
  (ssplit_spoke k lo (Pcons7 h f1 f2 p) = Pcons7 h f1 f2 p) /\
  (ssplit_spoke k lo (Pcons8 h f1 f2 f3 p) = Pcons8 h f1 f2 f3 p)`;;
let ssplit_hat = new_recursive_definition part_RECURSION
 `(ssplit_hat k lo Pnil = Pnil) /\
  (ssplit_hat k lo (Pcons s h p) = Pcons s (split_range k lo h) p) /\
  (ssplit_hat k lo (Pcons6 h f1 p) = Pcons6 (split_range k lo h) f1 p) /\
  (ssplit_hat k lo (Pcons7 h f1 f2 p) = Pcons7 (split_range k lo h) f1 f2 p) /\
  (ssplit_hat k lo (Pcons8 h f1 f2 f3 p) =
  Pcons8 (split_range k lo h) f1 f2 f3 p)`;;
let ssplit_fan1 = new_recursive_definition part_RECURSION
 `(ssplit_fan1 k lo Pnil = Pnil) /\
  (ssplit_fan1 k lo (Pcons s h p) =
     (if s = Pr66 then Pcons6 h (split_range k lo Pr59) p
      else if s = Pr77 then Pcons7 h (split_range k lo Pr59) Pr59 p
      else if s = Pr88 then Pcons8 h (split_range k lo Pr59) Pr59 Pr59 p
      else Pcons s h p)) /\
  (ssplit_fan1 k lo (Pcons6 h f1 p) = Pcons6 h (split_range k lo f1) p) /\
  (ssplit_fan1 k lo (Pcons7 h f1 f2 p) = Pcons7 h (split_range k lo f1) f2 p)
  /\
  (ssplit_fan1 k lo (Pcons8 h f1 f2 f3 p) =
  Pcons8 h (split_range k lo f1) f2 f3 p)`;;
let ssplit_fan2 = new_recursive_definition part_RECURSION
 `(ssplit_fan2 k lo Pnil = Pnil) /\
  (ssplit_fan2 k lo (Pcons s h p) =
     (if s = Pr77 then Pcons7 h Pr59 (split_range k lo Pr59) p
      else if s = Pr88 then Pcons8 h Pr59 (split_range k lo Pr59) Pr59 p
      else Pcons s h p)) /\
  (ssplit_fan2 k lo (Pcons6 h f1 p) = Pcons6 h f1 p) /\
  (ssplit_fan2 k lo (Pcons7 h f1 f2 p) = Pcons7 h f1 (split_range k lo f2) p)
  /\
  (ssplit_fan2 k lo (Pcons8 h f1 f2 f3 p) =
  Pcons8 h f1 (split_range k lo f2) f3 p)`;;
let ssplit_fan3 = new_recursive_definition part_RECURSION
 `(ssplit_fan3 k lo Pnil = Pnil) /\
  (ssplit_fan3 k lo (Pcons s h p) =
     (if s = Pr88 then Pcons8 h Pr59 Pr59 (split_range k lo Pr59) p
      else Pcons s h p)) /\
  (ssplit_fan3 k lo (Pcons6 h f1 p) = Pcons6 h f1 p) /\
  (ssplit_fan3 k lo (Pcons7 h f1 f2 p) = Pcons7 h f1 f2 p) /\
  (ssplit_fan3 k lo (Pcons8 h f1 f2 f3 p) =
  Pcons8 h f1 f2 (split_range k lo f3) p)`;;
let split_part = new_recursive_definition subpart_loc_RECURSION
 `(split_part Pspoke j k lo p =
  cat_part (take_part j p) (ssplit_spoke k lo (drop_part j p))) /\
  (split_part Phat j k lo p =
  cat_part (take_part j p) (ssplit_hat k lo (drop_part j p))) /\
  (split_part Pfan1 j k lo p =
  cat_part (take_part j p) (ssplit_fan1 k lo (drop_part j p))) /\
  (split_part Pfan2 j k lo p =
  cat_part (take_part j p) (ssplit_fan2 k lo (drop_part j p))) /\
  (split_part Pfan3 j k lo p =
  cat_part (take_part j p) (ssplit_fan3 k lo (drop_part j p)))`;;
let SIZE_SSPLIT = prove
 (`(!k lo q. size_part(ssplit_spoke k lo q) = size_part q) /\
   (!k lo q. size_part(ssplit_hat k lo q) = size_part q) /\
   (!k lo q. size_part(ssplit_fan1 k lo q) = size_part q) /\
   (!k lo q. size_part(ssplit_fan2 k lo q) = size_part q) /\
   (!k lo q. size_part(ssplit_fan3 k lo q) = size_part q)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `q:part` (cases "part")) THEN
  REWRITE_TAC[ssplit_spoke; ssplit_hat; ssplit_fan1; ssplit_fan2;
              ssplit_fan3] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[size_part]);;
let SIZE_SPLIT_PART = prove
 (`!i j k lo p. size_part(split_part i j k lo p) = size_part p`,
  MATCH_MP_TAC subpart_loc_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[split_part; SIZE_CAT_PART; SIZE_SSPLIT] THEN
  MP_TAC(SPECL [`j:num`; `p:part`] CAT_TAKE_DROP_PART) THEN
  DISCH_THEN(MP_TAC o AP_TERM `size_part`) THEN
  REWRITE_TAC[SIZE_CAT_PART] THEN ARITH_TAC);;
(* Every range starts at 5 or above.                                         *)
let MEM_RANGE_GE5 = prove
 (`!r n. mem_range r n ==> 5 <= n`,
  MATCH_MP_TAC prange_INDUCT THEN REWRITE_TAC[mem_range] THEN ARITH_TAC);;
let part_rel_DISTINCT = distinctness "part_rel";;
let GOOD_RSPLIT_K = prove
 (`!k r. good_rsplit k r ==> k = 5 \/ k = 6 \/ k = 7 \/ k = 8`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_rsplit; prange_lo] THEN
  ASM_CASES_TAC `k = 5` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 6` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 7` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 8` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cmp_range r Pr59 = Psubset` SUBST1_TAC THENL
   [REWRITE_TAC[cmp_range] THEN
    SUBGOAL_THEN `!n. mem_range r n ==> mem_range Pr59 n`
    (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[mem_range] THEN MESON_TAC[MEM_RANGE_GE5];
    REWRITE_TAC[part_rel_DISTINCT]]);;
let GUARDED_CMP_CONV tm =
  match strip_comb tm with
  | c,[_;_] when (try fst(dest_const c) = "cmp_range" with _ -> false) ->
    CMP_RANGE_CONV tm
  | _ -> failwith "GUARDED_CMP_CONV";;
let FIT_SPLIT_RANGE = prove
 (`!k r. good_rsplit k r
     ==> !lo a. mem_range (split_range k lo r) a <=>
                (if lo then a <= k else k < a) /\ mem_range r a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
    GOOD_RSPLIT_K) THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:prange` (cases "prange")) THEN
  REWRITE_TAC[good_rsplit; prange_lo] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV GUARDED_CMP_CONV) THEN
  REWRITE_TAC[part_rel_DISTINCT; GSYM part_rel_DISTINCT] THEN
  GEN_TAC THEN BOOL_CASES_TAC `lo:bool` THEN GEN_TAC THEN
  REWRITE_TAC[split_range] THEN
  REWRITE_TAC[prange_lo; prange_hi] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[meet_range; rlo; rhi; rbounded] THEN
  REWRITE_TAC[MAX; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[prange_of_bounds] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[mem_range] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Towards FITP_SPLIT: fitc, arities off the darts, the pentagonal           *)
(* conversions and FITP_SPLIT_CORE.  A point outside the dart set has arity  *)
(* 1 (the face map fixes it) and no prange accepts 1, so no cons part fits   *)
(* at a hub off the darts; hence the pentagonal fan conversions hold         *)
(* unconditionally (Gonthier's pentaG argument over a total map splits into  *)
(* the pentagonal case on the darts and the case off the darts, where both   *)
(* sides are false).                                                         *)
(* ------------------------------------------------------------------------- *)
let fitc = new_definition
 `fitc i j k (H:(A)hypermap) x <=>
    k < arity H (subpart_loc_move i H (ITER j (face_map H) x))`;;
let EDGE_FIXES_OFF = prove
 (`!H:(A)hypermap x. ~(x IN dart H) ==> edge_map H x = x`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `H:(A)hypermap` EDGE_MAP_PERMUTES) THEN
  REWRITE_TAC[permutes] THEN ASM_MESON_TAC[]);;
let ARITY_OFF_DART = prove
 (`!H:(A)hypermap x. ~(x IN dart H) ==> arity H x = 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arity; orbit_size] THEN
  SUBGOAL_THEN `orbit_map (face_map H) (x:A) = {x}` SUBST1_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ETA_AX] o MATCH_MP ITER_FIXED o
                MATCH_MP FACE_FIXES_OFF) THEN
    REWRITE_TAC[orbit_map; EXTENSION; IN_ELIM_THM; IN_SING] THEN
    ASM_MESON_TAC[];
    SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY] THEN ARITH_TAC]);;
let SIZE_TAKE_PART_LE = prove
 (`!j p. j <= size_part p ==> size_part(take_part j p) = j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`j:num`; `p:part`] CAT_TAKE_DROP_PART) THEN
  DISCH_THEN(MP_TAC o AP_TERM `size_part`) THEN
  REWRITE_TAC[SIZE_CAT_PART; SIZE_DROP_PART] THEN ASM_ARITH_TAC);;
let SPOKE_MEM_IN_DART = prove
 (`!(H:(A)hypermap) r y.
     mem_range r (arity H (subpart_loc_move Pspoke H y)) ==> y IN dart H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subpart_loc_move] THEN
  ASM_CASES_TAC `y IN dart(H:(A)hypermap)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP EDGE_FIXES_OFF) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP ARITY_OFF_DART) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEM_RANGE_GE5) THEN ARITH_TAC);;
let PENTA_FAN_MEM = prove
 (`!H:(A)hypermap. pentagonal H
     ==> !i y. y IN dart H ==>
     mem_range Pr59 (arity H (subpart_loc_move i H y))`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC subpart_loc_INDUCT THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[subpart_loc_move; mem_range] THEN
  MATCH_MP_TAC(ARITH_RULE `4 < n ==> 5 <= n`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[pentagonal]) THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART] THEN
  MATCH_MP_TAC EDGE_MAP_IN_DART THEN MATCH_MP_TAC ITER_PERMUTES_IN THEN
  ASM_SIMP_TAC[FACE_MAP_PERMUTES; EDGE_MAP_IN_DART]);;
let conv_tac =
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[fitp] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(MATCH_MP SPOKE_MEM_IN_DART th) ORELSE NO_TAC) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(fun pent ->
    if (try fst(dest_const(fst(strip_comb(concl pent)))) = "pentagonal"
        with _ -> false)
    then MP_TAC(MATCH_MP PENTA_FAN_MEM pent) else NO_TAC) THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[th]);;
let FITP_PCONS66 = prove
 (`!H:(A)hypermap. pentagonal H
     ==> !h p1 y. fitp (Pcons Pr66 h p1) H y <=> fitp (Pcons6 h Pr59 p1) H y`,
  conv_tac);;
let FITP_PCONS77 = prove
 (`!H:(A)hypermap. pentagonal H
     ==> !h p1 y. fitp (Pcons Pr77 h p1) H y <=>
     fitp (Pcons7 h Pr59 Pr59 p1) H y`,
  conv_tac);;
let FITP_PCONS88 = prove
 (`!H:(A)hypermap. pentagonal H
     ==> !h p1 y. fitp (Pcons Pr88 h p1) H y <=>
     fitp (Pcons8 h Pr59 Pr59 Pr59 p1) H y`,
  conv_tac);;
let FITP_SPLIT_CORE = prove
 (`!(H:(A)hypermap) pc i j k p q r lo (x:A).
   part_update H pc i /\
   size_part(drop_part j p) = size_part (pc r q) /\
   (!y. fitp (drop_part j p) H y <=> fitp (pc r q) H y) /\
   good_rsplit k r
   ==> (fitp (cat_part (take_part j p) (pc (split_range k lo r) q)) H x <=>
        (if lo
        then ~(k < arity H (subpart_loc_move i H (ITER j (face_map H) x)))
         else (k < arity H (subpart_loc_move i H (ITER j (face_map H) x)))) /\
        fitp p H x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "upd")
    (CONJUNCTS_THEN2 (LABEL_TAC "Esz")
    (CONJUNCTS_THEN2 (LABEL_TAC "Efit") (LABEL_TAC "gsp")))) THEN
  SUBGOAL_THEN `size_part(take_part j p) = j` ASSUME_TAC THENL
   [MATCH_MP_TAC SIZE_TAKE_PART_LE THEN
    USE_THEN "upd" (MP_TAC o CONJUNCT1 o SPECL [`r:prange`; `q:part`] o
                    REWRITE_RULE[part_update]) THEN
    USE_THEN "Esz" MP_TAC THEN REWRITE_TAC[SIZE_DROP_PART] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fitp p H (x:A) <=>
     fitp (take_part j p) H x /\
     fitp ((pc:prange->part->part) r q) H (ITER j (face_map H) x)`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`take_part j p`; `drop_part j p`; `H:(A)hypermap`; `x:A`
   ] FITP_CAT) THEN
    REWRITE_TAC[CAT_TAKE_DROP_PART] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FITP_CAT] THEN
  SUBGOAL_THEN
   `fitp ((pc:prange->part->part) (split_range k lo r) q) H
    (ITER j (face_map H) (x:A)) <=>
    (if lo then ~(k < arity H (subpart_loc_move i H (ITER j (face_map H) x)))
     else k < arity H (subpart_loc_move i H (ITER j (face_map H) x))) /\
    fitp (pc r q) H (ITER j (face_map H) x)`
   (fun th -> REWRITE_TAC[th] THEN CONV_TAC TAUT) THEN
  USE_THEN "gsp" (fun g ->
    MP_TAC(REWRITE_RULE[GSYM NOT_LT]
      (SPECL [`lo:bool`;
              `arity (H:(A)hypermap)
               (subpart_loc_move i H (ITER j (face_map H) (x:A)))`]
             (MATCH_MP FIT_SPLIT_RANGE g)))) THEN
  DISCH_THEN(LABEL_TAC "fsr") THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "upd" (MP_TAC o SPEC `ITER j (face_map H) (x:A)` o CONJUNCT2 o
                    SPECL [`split_range k lo r`; `q:part`
                    ] o REWRITE_RULE[part_update]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "trans")) THEN
    USE_THEN "fsr" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "trans" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    USE_THEN "upd" (MP_TAC o SPEC `ITER j (face_map H) (x:A)` o CONJUNCT2 o
                    SPECL [`r:prange`;
                           `q:part`] o REWRITE_RULE[part_update]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "memr") (LABEL_TAC "trans")) THEN
    USE_THEN "trans" MATCH_MP_TAC THEN
    USE_THEN "fsr" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* FITP_SPLIT.  The goal-directed tactic CORE_TAC reads the instance of      *)
(* FITP_SPLIT_CORE off each leaf goal (the context pc is rebuilt from the    *)
(* computed cons with rr at the split_range position and qq at the tail; r0, *)
(* k and lo come from the split_range arguments, the location from the       *)
(* subpart_loc_move on the right-hand side, j, p, H and x from their         *)
(* positions), then discharges the four hypotheses of FITP_SPLIT_CORE by     *)
(* rewriting with the update lemmas and size_part (and the pentagonal        *)
(* conversions FITP_PCONS66, FITP_PCONS77, FITP_PCONS88 for the fan leaves   *)
(* of a spoke without fans); fake_tac splits the plain spoke variable a0     *)
(* over Pr66, Pr77 and Pr88.                                                 *)
(* ------------------------------------------------------------------------- *)
let CORE_TAC : tactic = fun (asl,w) ->
  let l = lhand w in
  let _,fargs = strip_comb l in
  let cat = hd fargs and hh = hd(tl fargs) and xx = hd(tl(tl fargs)) in
  let _,catargs = strip_comb cat in
  let tk = hd catargs and xterm = hd(tl catargs) in
  let _,tkargs = strip_comb tk in
  let jj = hd tkargs and pp = hd(tl tkargs) in
  let ctor,cargs = strip_comb xterm in
  let is_sr t =
 (try fst(dest_const(fst(strip_comb t))) = "split_range" with
 Failure _ -> false) in
  let rec posn pr ls i = match ls with
    | [] -> failwith "posn"
    | h::t -> if pr h then i else posn pr t (i+1) in
  let idx = posn is_sr cargs 0 in
  let sr = el idx cargs in
  let _,srargs = strip_comb sr in
  let kk = hd srargs and lolo = hd(tl srargs) and r0 = hd(tl(tl srargs)) in
  let n = length cargs in
  let qarg = last cargs in
  let rv = mk_var("rr",`:prange`) and qv = mk_var("qq",`:part`) in
  let newargs = map2
    (fun t i -> if i = idx then rv else if i = n-1 then qv else t)
                     cargs (map (fun i -> i) (0--(n-1))) in
  let pc = mk_abs(rv, mk_abs(qv, list_mk_comb(ctor,newargs))) in
  let locterm = find_term (fun t ->
      (try fst(dest_const(fst(strip_comb t))) = "subpart_loc_move" with
      Failure _ -> false)) w in
  let loc = hd(snd(strip_comb locterm)) in
  (MP_TAC(ISPECL [hh; pc; loc; jj; kk; pp; qarg; r0; lolo;
                  xx] FITP_SPLIT_CORE) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[UPDATEPS; UPDATEPH; UPDATEP6H; UPDATEP6F1;
                     UPDATEP7H; UPDATEP7F1;
                     UPDATEP7F2; UPDATEP8H; UPDATEP8F1; UPDATEP8F2; UPDATEP8F3;
                     size_part] THEN
     FIRST_ASSUM(fun pent ->
       if (try fst(dest_const(fst(strip_comb(concl pent)))) = "pentagonal" with
           Failure _ -> false)
       then REWRITE_TAC[MATCH_MP FITP_PCONS66 pent; MATCH_MP FITP_PCONS77 pent;
                        MATCH_MP FITP_PCONS88 pent]
       else NO_TAC);
     DISCH_THEN(fun th -> REWRITE_TAC[BETA_RULE th])]) (asl,w);;
let prange_DISTINCT = distinctness "prange";;
let fake_tac =
  ASM_CASES_TAC `a0 = Pr66` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[prange_DISTINCT; GSYM prange_DISTINCT] THEN
    DISCH_TAC THEN CORE_TAC;
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `a0 = Pr77` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[prange_DISTINCT; GSYM prange_DISTINCT] THEN
      DISCH_TAC THEN CORE_TAC;
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `a0 = Pr88` THENL
       [POP_ASSUM SUBST_ALL_TAC THEN
        REWRITE_TAC[prange_DISTINCT; GSYM prange_DISTINCT] THEN
        DISCH_TAC THEN CORE_TAC;
        ASM_REWRITE_TAC[]]]];;
let leaf = FIRST[DISCH_TAC THEN CORE_TAC; fake_tac];;
let FITP_SPLIT = prove
 (`!H:(A)hypermap. pentagonal H
    ==> !i j k p. good_split i j k p
        ==> !lo (x:A). exact_fitp H x (split_part i j k lo p) <=>
                       (if lo then ~(fitc i j k H x) else fitc i j k H x) /\
                       exact_fitp H x p`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[exact_fitp; SIZE_SPLIT_PART; fitc] THEN
  SUBGOAL_THEN
   `fitp (split_part i j k lo p) H (x:A) <=>
    (if lo then ~(k < arity H (subpart_loc_move i H (ITER j (face_map H) x)))
     else k < arity H (subpart_loc_move i H (ITER j (face_map H) x))) /\
    fitp p H x`
   (fun th -> REWRITE_TAC[th] THEN CONV_TAC TAUT) THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `i:subpart_loc` (cases "subpart_loc")) THEN
  REWRITE_TAC[good_split; split_part] THEN
  REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN ASSUME_TAC)
    (ISPEC `drop_part j p` (cases "part")) THEN
  ASM_REWRITE_TAC[gsplit_spoke; gsplit_hat; gsplit_fan1; gsplit_fan2;
                  gsplit_fan3;
                  ssplit_spoke; ssplit_hat; ssplit_fan1; ssplit_fan2;
                  ssplit_fan3] THEN
  leaf);;
(* ------------------------------------------------------------------------- *)
(* MIRROR_MIRROR_PART.  The invariant: mirror_part_rec is an involution with *)
(* the roles of the processed part and the accumulator swapped, mirror (rec  *)
(* p h0 q) = rec q h0 p whenever next_hat h0 q = next_hat h0 p (the heads    *)
(* carry each other's hats).  The premise of the induction hypothesis holds  *)
(* by construction (the hat of the pushed frame is next_hat h0 of the tail), *)
(* and mirror_mirror is the instance q = Pnil, h0 = get_hat p.               *)
(* ------------------------------------------------------------------------- *)
let MIR_TAC : tactic = fun (asl,w) ->
  let l = lhand w in
  let rec_t = rand l in
  let _,rargs = strip_comb rec_t in
  let h0 = hd(tl rargs) and q' = hd(tl(tl rargs)) in
  (FIRST_ASSUM(fun ih -> MP_TAC(SPECL [q'; h0] ih)) THEN
   REWRITE_TAC[next_hat] THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[mirror_part_rec] THEN ASM_REWRITE_TAC[]) (asl,w);;
let MIRROR_REC_INVOL = prove
 (`!p q h0. next_hat h0 q = next_hat h0 p
     ==> mirror_part (mirror_part_rec p h0 q) = mirror_part_rec q h0 p`,
  MATCH_MP_TAC part_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[mirror_part_rec; next_hat] THEN
    STRUCT_CASES_TAC(ISPEC `q:part` (cases "part")) THEN
    REWRITE_TAC[next_hat] THEN TRY(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[mirror_part; get_hat; next_hat; mirror_part_rec];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "IH") THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[next_hat] THEN DISCH_TAC THEN
  REWRITE_TAC[mirror_part_rec] THEN MIR_TAC);;
let MIRROR_MIRROR_PART = prove
 (`!p. mirror_part (mirror_part p) = p`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [mirror_part] THEN
  MP_TAC(SPECL [`p:part`; `Pnil`; `get_hat p`] MIRROR_REC_INVOL) THEN
  ANTS_TAC THENL
   [STRUCT_CASES_TAC(ISPEC `p:part` (cases "part")) THEN
    REWRITE_TAC[next_hat; get_hat];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mirror_part_rec]]);;
