let assign = new_definition
  `Assign (f:S->S) (q:S->bool) = q o f`;;

parse_as_infix(";;",(18,"right"));;

let sequence = new_definition
 `(c1:(S->bool)->(S->bool)) ;; (c2:(S->bool)->(S->bool)) = c1 o c2`;;

let if_def = new_definition
 `If e (c:(S->bool)->(S->bool)) q = {s | if e s then c q s else q s}`;;

let ite_def = new_definition
 `Ite e (c1:(S->bool)->(S->bool)) c2 q =
    {s | if e s then c1 q s else c2 q s}`;;

let while_RULES,while_INDUCT,while_CASES = new_inductive_definition
         `!q s. If e (c ;; while e c) q s ==> while e c q s`;;

let while_def = new_definition
 `While e c q =
    {s | !w. (!s:S. (if e(s) then c w s else q s) ==> w s) ==> w s}`;;

let monotonic = new_definition
 `monotonic c <=> !q q'. q SUBSET q' ==> (c q) SUBSET (c q')`;;

let MONOTONIC_ASSIGN = prove
 (`monotonic (Assign f)`,
  SIMP_TAC[monotonic; assign; SUBSET; o_THM; IN]);;

let MONOTONIC_IF = prove
 (`monotonic c ==> monotonic (If e c)`,
  REWRITE_TAC[monotonic; if_def] THEN SET_TAC[]);;

let MONOTONIC_ITE = prove
 (`monotonic c1 /\ monotonic c2 ==> monotonic (Ite e c1 c2)`,
  REWRITE_TAC[monotonic; ite_def] THEN SET_TAC[]);;

let MONOTONIC_SEQ = prove
 (`monotonic c1 /\ monotonic c2 ==> monotonic (c1 ;; c2)`,
  REWRITE_TAC[monotonic; sequence; o_THM] THEN SET_TAC[]);;

let MONOTONIC_WHILE = prove
 (`monotonic c ==> monotonic(While e c)`,
  REWRITE_TAC[monotonic; while_def] THEN SET_TAC[]);;

let WHILE_THM = prove
 (`!e c q:S->bool.
    monotonic c
    ==> (!s. If e (c ;; While e c) q s ==> While e c q s) /\
        (!w'. (!s. If e (c ;; (\q. w')) q s ==> w' s)
              ==> (!a. While e c q a ==> w' a)) /\
        (!s. While e c q s <=> If e (c ;; While e c) q s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  (MP_TAC o GEN_ALL o DISCH_ALL o derive_nonschematic_inductive_relations)
   `!s:S. (if e s then c w s else q s) ==> w s` THEN
  REWRITE_TAC[if_def; sequence; o_THM; IN_ELIM_THM; IMP_IMP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; while_def; IN_ELIM_THM] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[monotonic] THEN SET_TAC[]);;

let WHILE_FIX = prove
 (`!e c. monotonic c ==> (While e c = If e (c ;; While e c))`,
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[WHILE_THM]);;

let correct = new_definition
 `correct p c q <=> p SUBSET (c q)`;;

let CORRECT_PRESTRENGTH = prove
 (`!p p' c q. p SUBSET p' /\ correct p' c q ==> correct p c q`,
  REWRITE_TAC[correct; SUBSET_TRANS]);;

let CORRECT_POSTWEAK = prove
 (`!p c q q'. monotonic c /\ correct p c q' /\ q' SUBSET q ==> correct p c q`,
  REWRITE_TAC[correct; monotonic] THEN SET_TAC[]);;

let CORRECT_ASSIGN = prove
 (`!p f q. (p SUBSET (q o f)) ==> correct p (Assign f) q`,
  REWRITE_TAC[correct; assign]);;

let CORRECT_SEQ = prove
 (`!p q r c1 c2.
        monotonic c1 /\ correct p c1 r /\ correct r c2 q
        ==> correct p (c1 ;; c2) q`,
  REWRITE_TAC[correct; sequence; monotonic; o_THM] THEN SET_TAC[]);;

let CORRECT_ITE = prove
 (`!p e c1 c2 q.
       correct (p INTER e) c1 q /\ correct (p INTER (UNIV DIFF e)) c2 q
       ==> correct p (Ite e c1 c2) q`,
  REWRITE_TAC[correct; ite_def] THEN SET_TAC[]);;

let CORRECT_IF = prove
 (`!p e c q.
       correct (p INTER e) c q /\ p INTER (UNIV DIFF e) SUBSET q
       ==> correct p (If e c) q`,
  REWRITE_TAC[correct; if_def] THEN SET_TAC[]);;

let CORRECT_WHILE = prove
 (`!(<<) p c q e invariant.
      monotonic c /\
      WF(<<) /\
      p SUBSET invariant /\
      (UNIV DIFF e) INTER invariant SUBSET q /\
      (!X:S. correct (invariant INTER e INTER (\s. X = s)) c
                     (invariant INTER (\s. s << X)))
      ==> correct p (While e c) q`,
  REWRITE_TAC[correct; SUBSET; IN_INTER; IN_UNIV; IN_DIFF; IN] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:S. invariant s ==> While e c q s` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[WF_IND]) THEN
  X_GEN_TAC `s:S` THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP WHILE_FIX th]) THEN
  REWRITE_TAC[if_def; sequence; o_THM; IN_ELIM_THM] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:S`; `s:S`]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [monotonic]) THEN
  REWRITE_TAC[SUBSET; IN; RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[INTER; IN_ELIM_THM; IN]);;

let assert_def = new_definition
 `assert (p:S->bool) (q:S->bool) = q`;;

let variant_def = new_definition
 `variant ((<<):S->S->bool) (q:S->bool) = q`;;

let CORRECT_SEQ_VC = prove
 (`!p q r c1 c2.
        monotonic c1 /\ correct p c1 r /\ correct r c2 q
        ==> correct p (c1 ;; assert r ;; c2) q`,
  REWRITE_TAC[correct; sequence; monotonic; assert_def; o_THM] THEN SET_TAC[]);;

let CORRECT_WHILE_VC = prove
 (`!(<<) p c q e invariant.
      monotonic c /\
      WF(<<) /\
      p SUBSET invariant /\
      (UNIV DIFF e) INTER invariant SUBSET q /\
      (!X:S. correct (invariant INTER e INTER (\s. X = s)) c
                     (invariant INTER (\s. s << X)))
      ==> correct p (While e (assert invariant ;; variant(<<) ;; c)) q`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sequence; variant_def; assert_def; o_DEF; ETA_AX] THEN
  ASM_MESON_TAC[CORRECT_WHILE]);;

let MONOTONIC_ASSERT = prove
 (`monotonic (assert p)`,
  REWRITE_TAC[assert_def; monotonic]);;

let MONOTONIC_VARIANT = prove
 (`monotonic (variant p)`,
  REWRITE_TAC[variant_def; monotonic]);;

let MONO_TAC =
  REPEAT(MATCH_MP_TAC MONOTONIC_WHILE ORELSE
         (MAP_FIRST MATCH_MP_TAC
           [MONOTONIC_SEQ; MONOTONIC_IF; MONOTONIC_ITE] THEN CONJ_TAC)) THEN
  MAP_FIRST MATCH_ACCEPT_TAC
   [MONOTONIC_ASSIGN; MONOTONIC_ASSERT; MONOTONIC_VARIANT];;

let VC_TAC =
  FIRST
   [MATCH_MP_TAC CORRECT_SEQ_VC THEN CONJ_TAC THENL [MONO_TAC; CONJ_TAC];
    MATCH_MP_TAC CORRECT_ITE THEN CONJ_TAC;
    MATCH_MP_TAC CORRECT_IF THEN CONJ_TAC;
    MATCH_MP_TAC CORRECT_WHILE_VC THEN REPEAT CONJ_TAC THENL
     [MONO_TAC; TRY(MATCH_ACCEPT_TAC WF_MEASURE); ALL_TAC; ALL_TAC;
      REWRITE_TAC[FORALL_PAIR_THM; MEASURE] THEN REPEAT GEN_TAC];
    MATCH_MP_TAC CORRECT_ASSIGN];;

needs "Library/prime.ml";;

(* ------------------------------------------------------------------------- *)
(* x = m, y = n;                                                             *)
(* while (!(x == 0 || y == 0))                                               *)
(*  { if (x < y) y = y - x;                                                  *)
(*    else x = x - y;                                                        *)
(*  }                                                                        *)
(* if (x == 0) x = y;                                                        *)
(* ------------------------------------------------------------------------- *)

g `correct
    (\(m,n,x,y). T)
    (Assign (\(m,n,x,y). m,n,m,n) ;;         // x,y := m,n
     assert (\(m,n,x,y). x = m /\ y = n) ;;
     While (\(m,n,x,y). ~(x = 0 \/ y = 0))
      (assert (\(m,n,x,y). gcd(x,y) = gcd(m,n)) ;;
       variant(MEASURE(\(m,n,x,y). x + y)) ;;
       Ite (\(m,n,x,y). x < y)
           (Assign (\(m,n,x,y). m,n,x,y - x))
           (Assign (\(m,n,x,y). m,n,x - y,y))) ;;
     assert (\(m,n,x,y). (x = 0 \/ y = 0) /\ gcd(x,y) = gcd(m,n)) ;;
     If (\(m,n,x,y). x = 0) (Assign (\(m,n,x,y). (m,n,y,y))))
  (\(m,n,x,y). gcd(m,n) = x)`;;

e(REPEAT VC_TAC);;

b();;
e(REPEAT VC_TAC THEN REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:num`; `y:num`] THEN
  REWRITE_TAC[IN; INTER; UNIV; DIFF; o_DEF; IN_ELIM_THM; PAIR_EQ] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC[]);;

e(SIMP_TAC[GCD_SUB; LT_IMP_LE]);;
e ARITH_TAC;;

e(SIMP_TAC[GCD_SUB; NOT_LT] THEN ARITH_TAC);;

e(MESON_TAC[GCD_0]);;

e(MESON_TAC[GCD_0; GCD_SYM]);;

parse_as_infix("refines",(12,"right"));;

let refines = new_definition
 `c2 refines c1 <=> !q. c1(q) SUBSET c2(q)`;;

let REFINES_REFL = prove
 (`!c. c refines c`,
  REWRITE_TAC[refines; SUBSET_REFL]);;

let REFINES_TRANS = prove
 (`!c1 c2 c3. c3 refines c2 /\ c2 refines c1 ==> c3 refines c1`,
  REWRITE_TAC[refines] THEN MESON_TAC[SUBSET_TRANS]);;

let REFINES_CORRECT = prove
 (`correct p c1 q /\ c2 refines c1 ==> correct p c2 q`,
  REWRITE_TAC[correct; refines] THEN MESON_TAC[SUBSET_TRANS]);;

let REFINES_WHILE = prove
 (`c' refines c ==> While e c' refines While e c`,
  REWRITE_TAC[refines; while_def; SUBSET; IN_ELIM_THM; IN] THEN MESON_TAC[]);;

let specification = new_definition
 `specification(p,q) r = if q SUBSET r then p else {}`;;

let REFINES_SPECIFICATION = prove
 (`c refines specification(p,q) ==> correct p c q`,
  REWRITE_TAC[specification; correct; refines] THEN
  MESON_TAC[SUBSET_REFL; SUBSET_EMPTY]);;
