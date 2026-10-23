(* ========================================================================= *)
(* 4CT/hubcap.ml                                                             *)
(*                                                                           *)
(* hubcap.v: ruling out a part by discharging and reducibility.  The score   *)
(* bound checkers check_dbound1, check_dbound2 and check_2dbound2, the       *)
(* hubcap cover and fit checks hubcap_cover and hubcap_fit, and the          *)
(* soundness theorem HUBCAP_FIT_BOUND: a part whose hubcap is covered and    *)
(* fits cannot fit at a dart of positive score.  The reducibility predicate  *)
(* redp on parts is a parameter, assumed never to hold on a fitting part.    *)
(*                                                                           *)
(* Coq's section variables nhub, redp and rf are explicit arguments, the     *)
(* drule fork rf being the pair (rs, rt) of discharge.ml; the bounds are     *)
(* integers and Coq's test `if (..)%R isn't Posz nt then false` becomes a    *)
(* sign test with num_of_int.  The recursions run, as in Coq, on a fuel      *)
(* argument m, with HD/TL access in place of list patterns.  Note that the   *)
(* HOL `+` binds less tightly than `-`, so Coq's a + b - c is written        *)
(* (a + b) - c.                                                              *)
(* ========================================================================= *)

needs "4CT/discharge.ml";;

let hubcap_INDUCT,hubcap_RECURSION = define_type
  "hubcap = Hubcap0
          | Hubcap1 num int hubcap
          | Hubcap2 num num int hubcap";;

(* ------------------------------------------------------------------------- *)
(* Source bound checking.                                                    *)
(* ------------------------------------------------------------------------- *)

let check_dbound1_rec = new_recursive_definition num_RECURSION
 `(check_dbound1_rec (redp:part->bool) p (rs:(part)list) ns 0 = F) /\
  (check_dbound1_rec redp p rs ns (SUC m) =
     (if rs = [] then T
      else if LENGTH (TL rs) < ns then T
      else let p' = meet_part p (HD rs) in
           let sd = sort_drules p' (TL rs) in
           (if ns - FST sd = 0 then redp p'
            else check_dbound1_rec redp p' (SND sd) (ns - FST sd - 1) m) /\
           check_dbound1_rec redp p (TL rs) ns m))`;;

let check_dbound1 = new_definition
 `check_dbound1 (redp:part->bool) (rf:(part)list#(part)list) p ns =
    check_dbound1_rec redp p (FST rf) ns (LENGTH (FST rf) + 1)`;;

let check_unfit = new_recursive_definition list_RECURSION
 `(check_unfit p [] = F) /\
  (check_unfit p (CONS r ru') =
  (if cmp_part p r = Psubset then T else check_unfit p ru'))`;;

(* ------------------------------------------------------------------------- *)
(* Single target bound checking.                                             *)
(* ------------------------------------------------------------------------- *)

let check_dbound2_rec = new_recursive_definition num_RECURSION
 `(check_dbound2_rec (redp:part->bool) p (rt:(part)list) (rs:(part)list)
  (ru:(part)list) nt 0 = F) /\
  (check_dbound2_rec redp p rt rs ru nt (SUC m) =
     (if rt = [] then T
      else if LENGTH (TL rt) < nt then T
      else let p' = meet_part p (HD rt) in
           (if check_unfit p' ru then T
            else let sdt = sort_drules p' (TL rt)
            and sds = sort_drules p' rs in
                 if (FST sds + nt) - FST sdt = 0 then redp p'
                 else check_dbound2_rec redp p' (SND sdt) (SND sds) ru
                 ((FST sds + nt) - FST sdt - 1) m) /\
           check_dbound2_rec redp p (TL rt) rs (CONS (HD rt) ru) nt m))`;;

let check_dbound2 = new_definition
 `check_dbound2 (redp:part->bool) (rf:(part)list#(part)list) p (b:int) =
    let sdt = sort_drules p (SND rf) and sds = sort_drules p (FST rf) in
    let v = &(FST sds) - &(FST sdt) + b in
    if v < &0 then F
    else check_dbound2_rec redp p (SND sdt) (SND sds) [] (num_of_int v)
    (LENGTH (SND sdt) + 2)`;;

(* ------------------------------------------------------------------------- *)
(* Dual target bound check.                                                  *)
(* ------------------------------------------------------------------------- *)

let check_2dbound2_rec = new_recursive_definition num_RECURSION
 `(check_2dbound2_rec nhub (redp:part->bool) p1 p2 (rt1:(part)list)
  (rs1:(part)list) (ru1:(part)list)
                      (rt2:(part)list) (rs2:(part)list) (ru2:(part)list) i
                      nt 0 = F) /\
  (check_2dbound2_rec nhub redp p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt (SUC m) =
     (if rt1 = [] then
        (if rt2 = [] then T
         else check_2dbound2_rec nhub redp p2 p1 rt2 rs2 ru2 [] rs1 ru1
         (nhub - i) nt m)
      else if LENGTH (TL rt1) + LENGTH rt2 < nt then T
      else let p1' = meet_part p1 (HD rt1) in
           let p2' = rot_part i p1' in
           (if check_unfit p1' ru1 \/ check_unfit p2' ru2 then T
            else let sd1t = sort_drules p1' (TL rt1)
            and sd1s = sort_drules p1' rs1 and
                     sd2t = sort_drules p2' rt2
                     and sd2s = sort_drules p2' rs2 in
                 if (FST sd1s + (FST sd2s + nt)) - (FST sd1t + FST sd2t) = 0
                 then redp p1'
                 else check_2dbound2_rec nhub redp p1' p2' (SND sd1t)
                 (SND sd1s) ru1 (SND sd2t) (SND sd2s) ru2 i
                        ((FST sd1s + (FST sd2s + nt)) -
                        (FST sd1t + FST sd2t) - 1) m) /\
           check_2dbound2_rec nhub redp p1 p2 (TL rt1) rs1 (CONS (HD rt1) ru1)
           rt2 rs2 ru2 i nt m))`;;

let check_2dbound2 = new_definition
 `check_2dbound2 nhub (redp:part->bool) (rf:(part)list#(part)list)
  p1 i (b:int) =
    let p2 = rot_part i p1 in
    let sd1t = sort_drules p1 (SND rf) and sd1s = sort_drules p1 (FST rf) and
        sd2t = sort_drules p2 (SND rf) and sd2s = sort_drules p2 (FST rf) in
    let v = &(FST sd1s + FST sd2s) - &(FST sd1t + FST sd2t) + b in
    if v < &0 then F
    else check_2dbound2_rec nhub redp p1 p2 (SND sd1t) (SND sd1s) [] (SND sd2t)
    (SND sd2s) [] i
           (num_of_int v) (LENGTH (SND sd1t) + (LENGTH (SND sd2t) + 3))`;;

(* ------------------------------------------------------------------------- *)
(* Cover checking.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Coq incr_nth: bump the i-th entry (0-padding to length i+1).              *)
let incr_nth = new_recursive_definition list_RECURSION
 `(incr_nth [] i = APPEND (REPLICATE i 0) [1]) /\
  (incr_nth (CONS n v') i =
  (if i = 0 then CONS (SUC n) v' else CONS n (incr_nth v' (i - 1))))`;;

(* Coq nth 0 v i                                                             *)
let nth0 = new_definition
  `nth0 (v:(num)list) i = if i < LENGTH v then EL i v else 0`;;

let tally_hubcap = new_recursive_definition hubcap_RECURSION
 `(tally_hubcap Hubcap0 = []) /\
  (tally_hubcap (Hubcap1 i b hc') = incr_nth (tally_hubcap hc') i) /\
  (tally_hubcap (Hubcap2 i j b hc') =
  incr_nth (incr_nth (tally_hubcap hc') i) j)`;;

let hubcap_cover_rec = new_recursive_definition hubcap_RECURSION
 `(hubcap_cover_rec v (b:int) Hubcap0 = ~(&0 < b)) /\
  (hubcap_cover_rec v b (Hubcap1 i b' hc') =
     (nth0 v i = 1 /\ hubcap_cover_rec v (&2 * b' + b) hc')) /\
  (hubcap_cover_rec v b (Hubcap2 i j b' hc') =
     (let n_i = nth0 v i and n_j = nth0 v j in
      n_i = n_j /\ n_i <= 2 /\
      hubcap_cover_rec v (b' * (if n_i = 1 then &2 else &1) + b) hc'))`;;

let hubcap_cover = new_definition
 `hubcap_cover nhub hc <=>
    let b = dboundK nhub * &2 - &1 in
    let v = tally_hubcap hc in
    LENGTH v = nhub /\ ~(MEM 0 v) /\ hubcap_cover_rec v b hc`;;

(* hubcap_rot nhub j p: rotation aligning with the rules at position j.      *)
let hubcap_rot = new_definition
 `hubcap_rot nhub j p =
  rot_part (if 2 <= j then j - 2 else (nhub + j) - 2) p`;;

let hub_subn = new_definition
 `hub_subn nhub i j = (if j <= i then i else i + nhub) - j`;;

let hubcap_fit = new_recursive_definition hubcap_RECURSION
 `(hubcap_fit (redp:part->bool) (rf:(part)list#(part)list) nhub p Hubcap0 = T)
  /\
  (hubcap_fit redp rf nhub p (Hubcap1 j b hc') =
     (check_dbound2 redp rf (hubcap_rot nhub j p) b /\
     hubcap_fit redp rf nhub p hc')) /\
  (hubcap_fit redp rf nhub p (Hubcap2 j1 j2 b hc') =
     (check_2dbound2 nhub redp rf (hubcap_rot nhub j1 p)
     (hub_subn nhub j2 j1) b /\
      hubcap_fit redp rf nhub p hc'))`;;

(* ------------------------------------------------------------------------- *)
(* Soundness lemmas. Hypotheses throughout:                                  *)
(*   plain_cubic_pentagonal G, drule_fork_values nhub (FST rf) (SND rf),     *)
(*   redpP: !x p. x IN dart G /\ redp p ==> ~exact_fitp G x p.               *)
(* ------------------------------------------------------------------------- *)

let DBOUND1_NIL = prove
 (`!(G:(A)hypermap) x. dbound1 G [] x = 0`,
  REWRITE_TAC[dbound1; FILTER; LENGTH]);;
let DBOUND1_LE_LENGTH = prove
 (`!(G:(A)hypermap) r x. dbound1 G r x <= LENGTH r`,
  REWRITE_TAC[dbound1; LENGTH_FILTER]);;

(* In the soundness proofs of the recursive checks, CHECK_IH_TAC applies the *)
(* induction hypothesis !v. A1 /\ ... /\ Ak /\ check v ==> C to the          *)
(* recursive check in the antecedent of the goal, finding v by matching.  A  *)
(* variable of the hypothesis that the check does not mention (the base dart *)
(* x1 of CHECK_2DBOUND2_REC) keeps its name.                                 *)
let CHECK_IH_TAC =
  DISCH_THEN(fun ck -> ASSUME_TAC ck THEN
    FIRST_X_ASSUM(MP_TAC o C (PART_MATCH (last o conjuncts o lhand))
                              (concl ck)));;

(* The fuel-indexed recursion is sound for any fuel m (induction on m, then  *)
(* cases on the rule list).                                                  *)
let CHECK_DBOUND1_REC = prove
 (`!(G:(A)hypermap) (redp:part->bool) x.
     (!p. redp p ==> ~exact_fitp G x p)
     ==> !m ns rs p. exact_fitp G x p /\ check_dbound1_rec redp p rs ns m
                     ==> dbound1 G rs x <= ns`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[check_dbound1_rec] THEN X_GEN_TAC `ns:num` THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `rs:(part)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL; DBOUND1_NIL; DBOUND1_CONS; LE_0] THEN
  X_GEN_TAC `p:part` THEN
  ASM_CASES_TAC `LENGTH(t:(part)list) < ns` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `t:(part)list`; `x:A`]
           DBOUND1_LE_LENGTH) THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_CASES_TAC `fitp (h:part) G (x:A)` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
   [ALL_TAC;
    UNDISCH_TAC `check_dbound1_rec redp p t ns m` THEN CHECK_IH_TAC THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `exact_fitp G (x:A) (meet_part p h)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EXACT_FITP_MEET]; ALL_TAC] THEN
  (* ONCE: the decomposition of SORT_DBOUND1_EQ applies to its own result. *)
  SUBGOAL_THEN `fitp (meet_part p h) G (x:A)`
   (fun th -> ONCE_REWRITE_TAC[MATCH_MP SORT_DBOUND1_EQ th]) THENL
   [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[]; CHECK_IH_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CHECK_DBOUND1P = prove
 (`!(G:(A)hypermap) nhub (redp:part->bool) rf x p ns.
     plain_cubic_pentagonal G /\ drule_fork_values nhub (FST rf) (SND rf) /\
     (!x p. x IN dart G /\ redp p ==> ~exact_fitp G x p) /\
     x IN dart G /\ arity G x = nhub /\ exact_fitp G x p /\
     check_dbound1 redp rf p ns
     ==> dbound1 G (FST rf) x <= ns`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `redp:part->bool`; `x:A`]
         CHECK_DBOUND1_REC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `check_dbound1 redp rf p ns` THEN REWRITE_TAC[check_dbound1] THEN
  CHECK_IH_TAC THEN ASM_REWRITE_TAC[]);;

let CHECK_UNFITP = prove
 (`!(G:(A)hypermap) x p ru.
     fitp p G x /\ dbound1 G ru x = 0 ==> ~(check_unfit p ru)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`ru:(part)list`, `ru:(part)list`) THEN LIST_INDUCT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[dbound1]) THEN
  REWRITE_TAC[check_unfit; dbound1; FILTER; LENGTH] THEN
  ASM_CASES_TAC `fitp (h:part) G (x:A)` THEN
  ASM_REWRITE_TAC[LENGTH; NOT_SUC] THEN
  ASM_CASES_TAC `cmp_part p (h:part) = Psubset` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL[`p:part`; `G:(A)hypermap`; `x:A`] FITP_CMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `h:part`) THEN
  ASM_REWRITE_TAC[apply_part_rel]);;

(* The invariant of the target-bound recursion: with the excluded rules ru   *)
(* not fitting, dbound1 rt x <= nt + dbound1 rs x.                           *)
let CHECK_DBOUND2_REC = prove
 (`!(G:(A)hypermap) (redp:part->bool) x.
     (!p. redp p ==> ~exact_fitp G x p)
     ==> !m nt rt rs ru p. exact_fitp G x p /\ dbound1 G ru x = 0 /\
                           check_dbound2_rec redp p rt rs ru nt m
                           ==> dbound1 G rt x <= nt + dbound1 G rs x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[check_dbound2_rec] THEN X_GEN_TAC `nt:num` THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `rt:(part)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL; DBOUND1_NIL; DBOUND1_CONS; LE_0] THEN
  MAP_EVERY X_GEN_TAC [`rs:(part)list`; `ru:(part)list`; `p:part`] THEN
  ASM_CASES_TAC `LENGTH(t:(part)list) < nt` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `t:(part)list`; `x:A`]
           DBOUND1_LE_LENGTH) THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_CASES_TAC `fitp (h:part) G (x:A)` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
   [ALL_TAC;
    UNDISCH_TAC `check_dbound2_rec redp p t rs (CONS h ru) nt m` THEN
    CHECK_IH_TAC THEN ASM_REWRITE_TAC[DBOUND1_CONS; ADD_CLAUSES]] THEN
  SUBGOAL_THEN `exact_fitp G (x:A) (meet_part p h)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EXACT_FITP_MEET]; ALL_TAC] THEN
  SUBGOAL_THEN `fitp (meet_part p h) G (x:A)`
   (fun th -> ASSUME_TAC th THEN
              ONCE_REWRITE_TAC[MATCH_MP SORT_DBOUND1_EQ th]) THENL
   [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `x:A`; `meet_part p h`; `ru:(part)list`]
         CHECK_UNFITP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[]; CHECK_IH_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CHECK_DBOUND2P = prove
 (`!(G:(A)hypermap) nhub (redp:part->bool) rf x p b.
     plain_cubic_pentagonal G /\ drule_fork_values nhub (FST rf) (SND rf) /\
     (!x p. x IN dart G /\ redp p ==> ~exact_fitp G x p) /\
     x IN dart G /\ arity G x = nhub /\ exact_fitp G x p /\
     check_dbound2 redp rf p b
     ==> dbound2 G (SND rf) (FST rf) x <= b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `redp:part->bool`; `x:A`]
         CHECK_DBOUND2_REC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `fitp p G (x:A)`
   (fun th -> REWRITE_TAC[dbound2] THEN
              ONCE_REWRITE_TAC[MATCH_MP SORT_DBOUND1_EQ th])
  THENL [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  UNDISCH_TAC `check_dbound2 redp rf p b` THEN REWRITE_TAC[check_dbound2] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN CHECK_IH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_NOT_LT]) THEN
  ASM_SIMP_TAC[DBOUND1_NIL; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD;
               INT_OF_NUM_OF_INT] THEN
  INT_ARITH_TAC);;

(* The dual recursion: generalized over the base dart x1 and the offset i so *)
(* that the role swap (rt1 = [] => continue from x2 = f^i x1 with offset     *)
(* nhub - i) is an instance of the induction hypothesis.                     *)
let CHECK_2DBOUND2_REC = prove
 (`!(G:(A)hypermap) nhub (redp:part->bool).
     (!x p. x IN dart G /\ redp p ==> ~exact_fitp G x p)
     ==> !m nt rt1 rs1 ru1 rt2 rs2 ru2 i p1 p2 (x1:A).
           x1 IN dart G /\ arity G x1 = nhub /\ i <= nhub /\
           exact_fitp G x1 p1 /\ exact_fitp G (ITER i (face_map G) x1) p2 /\
           dbound1 G ru1 x1 = 0 /\
           dbound1 G ru2 (ITER i (face_map G) x1) = 0 /\
           check_2dbound2_rec nhub redp p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt m
           ==> dbound1 G rt1 x1 + dbound1 G rt2 (ITER i (face_map G) x1) <=
               nt +
               (dbound1 G rs1 x1 + dbound1 G rs2 (ITER i (face_map G) x1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[check_2dbound2_rec] THEN X_GEN_TAC `nt:num` THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `rt1:(part)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL; DBOUND1_NIL; DBOUND1_CONS;
              ADD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC
   [`rs1:(part)list`; `ru1:(part)list`; `rt2:(part)list`; `rs2:(part)list`;
    `ru2:(part)list`; `i:num`; `p1:part`; `p2:part`; `x1:A`] THEN
  STRIP_TAC THENL
   [(* rt1 exhausted: swap the roles of x1 and x2 = f^i x1.                *)
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[DBOUND1_NIL; LE_0] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`nt:num`; `rt2:(part)list`; `rs2:(part)list`; `ru2:(part)list`;
      `[]:(part)list`; `rs1:(part)list`; `ru1:(part)list`; `nhub - i`;
      `p2:part`; `p1:part`; `ITER i (face_map G) (x1:A)`]) THEN
    SUBGOAL_THEN
     `ITER (nhub - i) (face_map G) (ITER i (face_map G) (x1:A)) = x1`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[ITER_ADD; SUB_ADD] THEN ASM_MESON_TAC[ITER_FACE_ARITY];
      ASM_REWRITE_TAC(IN_DART_EQS @ [ARITY_ITER_FACE_GEN; DBOUND1_NIL;
                                     ARITH_RULE `n - i <= n`]) THEN
      ARITH_TAC];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  ASM_CASES_TAC `LENGTH(t:(part)list) + LENGTH(rt2:(part)list) < nt` THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `t:(part)list`; `x1:A`]
           DBOUND1_LE_LENGTH) THEN
    MP_TAC(ISPECL [`G:(A)hypermap`; `rt2:(part)list`;
                   `ITER i (face_map G) (x1:A)`] DBOUND1_LE_LENGTH) THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_CASES_TAC `fitp (h:part) G (x1:A)` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THENL
   [ALL_TAC;
    UNDISCH_TAC `check_2dbound2_rec nhub redp p1 p2 t rs1 (CONS h ru1)
                                    rt2 rs2 ru2 i nt m` THEN
    CHECK_IH_TAC THEN ASM_REWRITE_TAC[DBOUND1_CONS; ADD_CLAUSES]] THEN
  (* h fits at x1: meet it into p1, and rotate to x2 = f^i x1.              *)
  SUBGOAL_THEN `exact_fitp G (x1:A) (meet_part p1 h)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EXACT_FITP_MEET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `exact_fitp G (ITER i (face_map G) (x1:A)) (rot_part i (meet_part p1 h))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`i:num`; `meet_part p1 (h:part)`] FITP_ROT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fitp (meet_part p1 h) G (x1:A) /\
    fitp (rot_part i (meet_part p1 h)) G (ITER i (face_map G) x1)`
  (fun th -> STRIP_ASSUME_TAC th THEN
             ONCE_REWRITE_TAC(map (MATCH_MP SORT_DBOUND1_EQ) (CONJUNCTS th)))
  THENL [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `x1:A`; `meet_part p1 h`; `ru1:(part)list`]
         CHECK_UNFITP) THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `ITER i (face_map G) (x1:A)`;
                 `rot_part i (meet_part p1 h)`; `ru2:(part)list`]
         CHECK_UNFITP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[]; CHECK_IH_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CHECK_2DBOUND2P = prove
 (`!(G:(A)hypermap) nhub (redp:part->bool) rf x1 p i b.
     plain_cubic_pentagonal G /\ drule_fork_values nhub (FST rf) (SND rf) /\
     (!x p. x IN dart G /\ redp p ==> ~exact_fitp G x p) /\
     x1 IN dart G /\ arity G x1 = nhub /\ exact_fitp G x1 p /\ i <= nhub /\
     check_2dbound2 nhub redp rf p i b
     ==> dbound2 G (SND rf) (FST rf) x1 +
         dbound2 G (SND rf) (FST rf) (ITER i (face_map G) x1) <= b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `nhub:num`; `redp:part->bool`]
         CHECK_2DBOUND2_REC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `exact_fitp G (ITER i (face_map G) (x1:A)) (rot_part i p)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`i:num`; `p:part`] FITP_ROT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fitp p G (x1:A) /\ fitp (rot_part i p) G (ITER i (face_map G) x1)`
   (fun th -> REWRITE_TAC[dbound2] THEN
              ONCE_REWRITE_TAC(map (MATCH_MP SORT_DBOUND1_EQ) (CONJUNCTS th)))
  THENL [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  UNDISCH_TAC `check_2dbound2 nhub redp rf p i b` THEN
  REWRITE_TAC[check_2dbound2] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN CHECK_IH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_NOT_LT]) THEN
  ASM_SIMP_TAC[DBOUND1_NIL; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD;
               INT_OF_NUM_OF_INT] THEN
  INT_ARITH_TAC);;

let ARITY_INV_FACE2 = prove
 (`!(G:(A)hypermap) x. arity G (inv_face2 G x) = arity G x`,
  REWRITE_TAC[inv_face2; ARITY_EN_U]);;

let FIT_HUBCAP_ROT = prove
 (`!(G:(A)hypermap) nhub x p j.
     plain_cubic_pentagonal G /\ x IN dart G /\ arity G x = nhub /\
     exact_fitp G x p /\ j < nhub
     ==> exact_fitp G (ITER j (face_map G) (inv_face2 G x))
                      (hubcap_rot nhub j p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[plain_cubic_pentagonal; hubcap_rot] THEN
  STRIP_TAC THEN ABBREV_TAC `k = if 2 <= j then j - 2 else (nhub + j) - 2` THEN
  SUBGOAL_THEN `k <= size_part p /\ (k + 2 = j \/ k + 2 = j + nhub)`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `x:A`] PENTA_PR59) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[exact_fitp]) THEN
    ASM_REWRITE_TAC[mem_range] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* f^j (inv_face2 x) = f^(k+2) (inv_face2 x) = f^k x, with f^nhub = I.    *)
  SUBGOAL_THEN
   `ITER j (face_map G) (inv_face2 G x) = ITER k (face_map G) (x:A)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `ITER k (face_map G) x =
                  ITER (k + 2) (face_map G) (inv_face2 G (x:A))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM ITER_ADD; ITER2; FF_INV_FACE2]; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM ITER_ADD] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`G:(A)hypermap`; `inv_face2 G (x:A)`] ITER_FACE_ARITY) THEN
    ASM_SIMP_TAC[INV_FACE2_IN_DART; ARITY_INV_FACE2];
    MP_TAC(SPECL [`k:num`; `p:part`] FITP_ROT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th])]);;

let HUB_SUBN_HUB = prove
 (`!nhub i j. i < nhub ==> hub_subn nhub i j <= nhub`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hub_subn] THEN COND_CASES_TAC THEN
  ASM_ARITH_TAC);;

let ITER_HUB_SUBN = prove
 (`!(G:(A)hypermap) nhub i j x.
     j < nhub /\ x IN dart G /\ arity G x = nhub
     ==> ITER (hub_subn nhub i j) (face_map G) (ITER j (face_map G) x) =
     ITER i (face_map G) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ITER_ADD; hub_subn] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `i - j + j = i` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REFL_TAC];
    SUBGOAL_THEN `(i + nhub) - j + j = i + nhub` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM ITER_ADD] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[ITER_FACE_ARITY]]);;

(* ------------------------------------------------------------------------- *)
(* The cover argument (Coq hubcap_fit_bound).  Instead of Coq's              *)
(* findex-indexed weights over cface, index the face of x1 = inv_face2 x by  *)
(* i < nhub (dart f^i x1) and define the weighted sum                        *)
(*   hcwsum v w = sum over i of hcw v w i times dbound2 (f^i x1),            *)
(* where the weight hcw of index i is 2 once the partial tally w reaches the *)
(* full tally v there (and 0 before, 1 half-way for v_i = 2).                *)
(* HUBCAP_INVARIANT: for every suffix hc of the hubcap with accumulated      *)
(* bound b, b + hcwsum v (tally hc) <= 0.  At the top the weights are all    *)
(* 2, so 2 dboundK - 1 + 2 (sum over i of dbound2 (f^i x1)) <= 0,            *)
(* contradicting DSCORE_CAP2 (0 < dboundK + sum) by parity.                  *)
(* ------------------------------------------------------------------------- *)

let NTH0_NIL = prove
 (`!j. nth0 [] j = 0`,
  REWRITE_TAC[nth0; LENGTH; LT]);;
let NTH0_CONS = prove
 (`!n v j. nth0 (CONS n v) j = if j = 0 then n else nth0 v (j - 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nth0; LENGTH; EL_CONS] THEN
  ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[LT_0] THEN
  SUBGOAL_THEN `j < SUC (LENGTH (v:(num)list)) <=> j - 1 < LENGTH v`
    SUBST1_TAC THENL
   [ASM_ARITH_TAC; REFL_TAC]);;
let NTH0_POS_LT = prove
 (`!v i. ~(nth0 v i = 0) ==> i < LENGTH v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nth0] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[]);;
let NTH0_INCR_NIL = prove
 (`!i j. nth0 (incr_nth [] i) j = if j = i then 1 else 0`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[incr_nth; REPLICATE; APPEND; NTH0_CONS; NTH0_NIL];
    RULE_ASSUM_TAC(REWRITE_RULE[incr_nth]) THEN
    REWRITE_TAC[incr_nth; REPLICATE; APPEND; NTH0_CONS] THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `j = 0` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(0 = SUC i)`] THEN
    SUBGOAL_THEN `(j - 1 = i) <=> (j = SUC i)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REFL_TAC]]);;
let NTH0_INCR_NTH = prove
 (`!v i j. nth0 (incr_nth v i) j = nth0 v j + (if j = i then 1 else 0)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[incr_nth; NTH0_INCR_NIL; NTH0_NIL; ADD_CLAUSES] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[NTH0_CONS] THEN
  ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  TRY(SUBGOAL_THEN `(j - 1 = i - 1) <=> (j = i)` SUBST1_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC]) THEN
  ARITH_TAC);;
let NTH0_GE1 = prove
 (`!v i. ~(MEM 0 v) /\ i < LENGTH v ==> 1 <= nth0 v i`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[nth0] THEN
  SUBGOAL_THEN `~(EL i (v:(num)list) = 0)` MP_TAC THENL
   [ASM_MESON_TAC[MEM_EL]; ARITH_TAC]);;
let NTH0_INCR_LE = prove
 (`!v w i. (!j. nth0 (incr_nth w i) j <= nth0 v j)
           ==> nth0 w i < nth0 v i /\ (!j. nth0 w j <= nth0 v j)`,
  REWRITE_TAC[NTH0_INCR_NTH] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`);
    X_GEN_TAC `j:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num`)] THEN
  ARITH_TAC);;

(* Weight of index i for partial tally w against the full tally v.           *)
let hcw = new_definition
 `hcw (v:(num)list) (w:(num)list) i =
    if 1 < nth0 w i then 2 else if nth0 w i < 1 then 0
    else if nth0 v i = 1 then 2 else 1`;;
let hcwsum = new_definition
 `hcwsum (G:(A)hypermap) rt rs (x1:A) nhub v w =
    isum {i | i < nhub}
    (\i. &(hcw v w i) * dbound2 G rt rs (ITER i (face_map G) x1))`;;

let HCW_INCR_NE = prove
 (`!v w i j. ~(j = i) ==> hcw v (incr_nth w i) j = hcw v w j`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[hcw; NTH0_INCR_NTH; ADD_CLAUSES]);;
let HCW_INCR = prove
 (`!v w i. nth0 w i < nth0 v i /\ nth0 v i <= 2
     ==> hcw v (incr_nth w i) i = hcw v w i + (if nth0 v i = 1 then 2 else 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hcw; NTH0_INCR_NTH] THEN
  SUBGOAL_THEN `nth0 v i = 1 /\ nth0 w i = 0 \/ nth0 v i = 2 /\ nth0 w i = 0 \/
                nth0 v i = 2 /\ nth0 w i = 1` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]);;
let HCW_FULL = prove
 (`!v i. 1 <= nth0 v i ==> hcw v v i = 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hcw] THEN ASM_CASES_TAC `1 < nth0 v i` THEN
  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `nth0 v i = 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[ARITH]]);;
let HCWSUM_NIL = prove
 (`!(G:(A)hypermap) rt rs x1 nhub v. hcwsum G rt rs x1 nhub v [] = &0`,
  REWRITE_TAC[hcwsum; hcw; NTH0_NIL] THEN REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[INT_MUL_LZERO; ISUM_0]);;
let HCWSUM_FULL = prove
 (`!(G:(A)hypermap) rt rs x1 nhub v.
     (!i. i < nhub ==> 1 <= nth0 v i)
     ==> hcwsum G rt rs x1 nhub v v =
         &2 * isum {i | i < nhub}
         (\i. dbound2 G rt rs (ITER i (face_map G) x1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hcwsum; GSYM ISUM_LMUL] THEN
  MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN ASM_SIMP_TAC[HCW_FULL]);;
let HCWSUM_INCR = prove
 (`!(G:(A)hypermap) rt rs x1 nhub v w i.
     i < nhub /\ nth0 w i < nth0 v i /\ nth0 v i <= 2
     ==> hcwsum G rt rs x1 nhub v (incr_nth w i) =
         hcwsum G rt rs x1 nhub v w +
         &(if nth0 v i = 1 then 2 else 1) * dbound2 G rt rs
         (ITER i (face_map G) x1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hcwsum] THEN
  SUBGOAL_THEN
   `isum {k | k < nhub}
         (\k. &(hcw v (incr_nth w i) k) *
              dbound2 G rt rs (ITER k (face_map G) (x1:A))) =
    isum {k | k < nhub}
         (\k. &(hcw v w k) * dbound2 G rt rs (ITER k (face_map G) x1) +
              (if k = i
               then &(if nth0 v i = 1 then 2 else 1) *
                    dbound2 G rt rs (ITER i (face_map G) x1)
               else &0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_CASES_TAC `k:num = i` THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[HCW_INCR] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_ADD_RDISTRIB];
      ASM_SIMP_TAC[HCW_INCR_NE; INT_ADD_RID]];
    ALL_TAC] THEN
  SIMP_TAC[ISUM_ADD; FINITE_NUMSEG_LT] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ISUM_DELTA; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]);;

(* The face of x1 is indexed by i < arity x1 via f^i x1.                     *)
let FACE_ISUM_INDEX = prove
 (`!(G:(A)hypermap) x1 (d:A->int).
     x1 IN dart G
     ==> isum (face G x1) d =
     isum {i | i < arity G x1} (\i. d (ITER i (face_map G) x1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arity; face] THEN
  MP_TAC(ISPECL[`face_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`; `x1:A`]
         ORBIT_SIZE_DIVIDES) THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`face_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`; `x1:A`]
         ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN DISCH_TAC THEN
  SUBGOAL_THEN `orbit_map (face_map G) (x1:A) =
                IMAGE (\i. ITER i (face_map G) x1)
                      {i | i < orbit_size (face_map G) x1}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_PERIOD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL[`\i. ITER i (face_map G) (x1:A)`; `d:A->int`;
                `{i | i < orbit_size (face_map (G:(A)hypermap)) x1}`]
         ISUM_IMAGE) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL[`face_map (G:(A)hypermap)`; `x1:A`;
                `orbit_size (face_map (G:(A)hypermap)) x1`; `a:num`; `b:num`]
         ORBIT_ITER_DISTINCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL[`face_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`]
         PERMUTES_INJECTIVE) THEN
  REWRITE_TAC[FACE_MAP_PERMUTES] THEN MESON_TAC[]);;

let CFACE_INV_FACE2 = prove
 (`!(G:(A)hypermap) x. x IN dart G ==> cface G x (inv_face2 G x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CFACE_SYM THEN
  ASM_SIMP_TAC[INV_FACE2_IN_DART] THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `inv_face2 G (x:A)`; `inv_face2 G (x:A)`]
         CFACE_FF) THEN
  REWRITE_TAC[CFACE_REFL; FF_INV_FACE2]);;
let FACE_INV_FACE2 = prove
 (`!(G:(A)hypermap) x. x IN dart G ==> face G (inv_face2 G x) = face G x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[face] THEN MATCH_MP_TAC ORBIT_MAP_EQ THEN
  EXISTS_TAC `dart (G:(A)hypermap)` THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
  MP_TAC(ISPECL[`G:(A)hypermap`; `x:A`] CFACE_INV_FACE2) THEN
  ASM_REWRITE_TAC[cface; face]);;

(* The invariant, by induction on the hubcap: NTH0_INCR_LE peels the tally   *)
(* bound, and the new constraint is bounded by CHECK_DBOUND2P or             *)
(* CHECK_2DBOUND2P at the rotation FIT_HUBCAP_ROT of p.                      *)
let HUBCAP_INVARIANT = prove
 (`!(G:(A)hypermap) nhub (redp:part->bool) rf x p v.
     plain_cubic_pentagonal G /\ drule_fork_values nhub (FST rf) (SND rf) /\
     (!x p. x IN dart G /\ redp p ==> ~exact_fitp G x p) /\
     x IN dart G /\ arity G x = nhub /\ exact_fitp G x p /\ LENGTH v = nhub
     ==> !hc b. hubcap_cover_rec v b hc /\ hubcap_fit redp rf nhub p hc /\
                (!i. nth0 (tally_hubcap hc) i <= nth0 v i)
                ==> b + hcwsum G (SND rf) (FST rf) (inv_face2 G x) nhub v
                (tally_hubcap hc) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv_face2 G (x:A) IN dart G /\ arity G (inv_face2 G x) = nhub`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INV_FACE2_IN_DART; ARITY_INV_FACE2]; ALL_TAC] THEN
  MATCH_MP_TAC hubcap_INDUCT THEN
  REWRITE_TAC[hubcap_cover_rec; hubcap_fit; tally_hubcap; HCWSUM_NIL] THEN
  REPEAT CONJ_TAC THENL
   [INT_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`i:num`; `b1:int`; `hc:hubcap`] THEN DISCH_TAC THEN
    X_GEN_TAC `b:int` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTH0_INCR_LE) THEN
    SUBGOAL_THEN `i < nhub` ASSUME_TAC THENL
     [ASM_MESON_TAC[NTH0_POS_LT; ARITH_RULE `~(1 = 0)`]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&2 * b1 + b:int`) THEN
    MP_TAC(ISPECL [`G:(A)hypermap`; `nhub:num`; `redp:part->bool`;
                   `rf:(part)list#(part)list`;
                   `ITER i (face_map G) (inv_face2 G (x:A))`;
                   `hubcap_rot nhub i p`; `b1:int`] CHECK_DBOUND2P) THEN
    ASM_SIMP_TAC(IN_DART_EQS @ [ARITY_ITER_FACE_GEN; FIT_HUBCAP_ROT;
                                HCWSUM_INCR; ARITH]) THEN
    INT_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `b1:int`; `hc:hubcap`] THEN
    DISCH_TAC THEN X_GEN_TAC `b:int` THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTH0_INCR_LE) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NTH0_INCR_LE) THEN
    SUBGOAL_THEN `i < nhub /\ j < nhub /\ nth0 v j <= 2` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[NTH0_POS_LT; ARITH_RULE `a < b ==> ~(b = 0)`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `b1 * (if nth0 v i = 1 then &2 else &1) + b:int`) THEN
    MP_TAC(ISPECL [`G:(A)hypermap`; `nhub:num`; `redp:part->bool`;
                   `rf:(part)list#(part)list`;
                   `ITER i (face_map G) (inv_face2 G (x:A))`;
                   `hubcap_rot nhub i p`; `hub_subn nhub j i`; `b1:int`]
          CHECK_2DBOUND2P) THEN
    UNDISCH_TAC `nth0 v i = nth0 v j` THEN
    DISCH_THEN(fun th ->
      ASM_SIMP_TAC(IN_DART_EQS @
                   [ARITY_ITER_FACE_GEN; FIT_HUBCAP_ROT; HUB_SUBN_HUB;
                    ITER_HUB_SUBN; HCWSUM_INCR]) THEN
      REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `nth0 v j = 1` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(* Coq HUBCAP_FIT_BOUND: a part of size nhub whose hubcap is covered and     *)
(* fits cannot fit at a dart of positive score.                              *)
let HUBCAP_FIT_BOUND = prove
 (`!(G:(A)hypermap) nhub (redp:part->bool) rf x p hc.
     plain_cubic_pentagonal G /\ drule_fork_values nhub (FST rf) (SND rf) /\
     (!x p. x IN dart G /\ redp p ==> ~exact_fitp G x p) /\
     x IN dart G /\ size_part p = nhub /\ (&0 : int) < dscore G x /\
     hubcap_cover nhub hc /\ hubcap_fit redp rf nhub p hc
     ==> ~(exact_fitp G x p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `arity G (x:A) = nhub` ASSUME_TAC THENL
   [ASM_MESON_TAC[exact_fitp]; ALL_TAC] THEN
  UNDISCH_TAC `hubcap_cover nhub hc` THEN REWRITE_TAC[hubcap_cover] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  (* The invariant for the whole hubcap, where all the weights are 2.      *)
  MP_TAC(ISPECL [`G:(A)hypermap`; `nhub:num`; `redp:part->bool`;
                 `rf:(part)list#(part)list`; `x:A`; `p:part`;
                 `tally_hubcap hc`] HUBCAP_INVARIANT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`hc:hubcap`; `dboundK nhub * &2 - &1`]) THEN
  ASM_SIMP_TAC[LE_REFL; HCWSUM_FULL; NTH0_GE1] THEN
  (* Contradiction with DSCORE_CAP2 by parity.  The sums agree only up to  *)
  (* the bound variables of their index sets, so INT_ARITH is used through  *)
  (* matching.                                                               *)
  MATCH_MP_TAC(INT_ARITH
   `!k s s':int. &0 < k + s' /\ s' = s ==> ~(k * &2 - &1 + &2 * s <= &0)`) THEN
  EXISTS_TAC `isum (face G x)
                   (\y. dbound2 G (SND (rf:(part)list#(part)list)) (FST rf)
                                (y:A))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DSCORE_CAP2 THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`G:(A)hypermap`; `inv_face2 G (x:A)`;
                   `dbound2 (G:(A)hypermap) (SND (rf:(part)list#(part)list))
                            (FST rf)`]
           FACE_ISUM_INDEX) THEN
    ASM_SIMP_TAC[INV_FACE2_IN_DART; ARITY_INV_FACE2; FACE_INV_FACE2;
                 ETA_AX]]);;

