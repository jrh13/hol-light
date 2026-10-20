(* ========================================================================= *)
(* 4CT/kempe.ml                                                              *)
(*                                                                           *)
(* kempe.v: the Kempe closure of the ring traces of a planar plain           *)
(* quasicubic hypermap.  The chromogram transformers gram_neg, gram_flip and *)
(* gram_rot with their matching lemmas, list rotation (rot1, rotr1), and the *)
(* main theorem KEMPE_MAP (Gonthier's Kempe_map): the ring traces are        *)
(* Kempe-closed.  It is proved by induction on the number of darts,          *)
(* contracting the ring at a leaf of the Euler tree of jordan.ml by a double *)
(* Walkup step.                                                              *)
(* ========================================================================= *)

needs "4CT/jordan.ml";;
needs "4CT/chromogram.ml";;
needs "4CT/coloring.ml";;

(* ------------------------------------------------------------------------- *)
(* Chromogram transformers. gram_neg negates the parity bit of the first     *)
(* unmatched Gpop; gram_flip turns it into a Gpush (adjusting the next one); *)
(* gram_rot matches the left rotation of the traces matched by a balanced    *)
(* chromogram.  The counter n is the depth of pending Gpush symbols.         *)
(* ------------------------------------------------------------------------- *)

let gram_neg_rec = define
 `(gram_neg_rec n ([] : gram_symbol list) = ([] : gram_symbol list)) /\
  (gram_neg_rec n (CONS s w) =
    if s = Gpush then CONS Gpush (gram_neg_rec (n + 1) w)
    else if s = Gskip then CONS Gskip (gram_neg_rec n w)
    else if n = 0 then
      (if s = Gpop0 then CONS Gpop1 w else CONS Gpop0 w)
    else CONS s (gram_neg_rec (n - 1) w))`;;

let gram_neg = new_definition
  `gram_neg (w:gram_symbol list) = gram_neg_rec 0 w`;;

let gram_flip_rec = define
 `(gram_flip_rec n ([] : gram_symbol list) = [Gpush]) /\
  (gram_flip_rec n (CONS s w) =
    if s = Gpush then CONS Gpush (gram_flip_rec (n + 1) w)
    else if s = Gskip then CONS Gskip (gram_flip_rec n w)
    else if n = 0 then
      (if s = Gpop0 then CONS Gpush (gram_neg w) else CONS Gpush w)
    else CONS s (gram_flip_rec (n - 1) w))`;;

let gram_flip = new_definition
  `gram_flip (w:gram_symbol list) = gram_flip_rec 0 w`;;

let rot1 = new_definition
  `rot1 (l:A list) = if l = [] then [] else APPEND (TL l) [HD l]`;;

let gram_rot = new_definition
  `gram_rot (w : gram_symbol list) =
    if (?b. gram_balanced 0 b w) then
      (if w = [] then w
       else if HD w = Gpush then gram_flip (APPEND (TL w) [Gpop1])
       else if HD w = Gskip then APPEND (TL w) [Gskip]
       else w)
    else w`;;

let rotr1 = new_definition
 `rotr1 (l:(A)list) = if l = [] then [] else CONS (LAST l) (BUTLAST l)`;;

(* ------------------------------------------------------------------------- *)
(* Basic facts about rot1.                                                   *)
(* ------------------------------------------------------------------------- *)

let ROT1_NIL = prove
 (`rot1 ([]:(A)list) = []`,
  REWRITE_TAC[rot1]);;

let ROT1_CONS = prove
 (`!x:A l. rot1 (CONS x l) = APPEND l [x]`,
  REWRITE_TAC[rot1; NOT_CONS_NIL; HD; TL]);;

let LENGTH_ROT1 = prove
 (`!l:(A)list. LENGTH(rot1 l) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ROT1_NIL; ROT1_CONS; LENGTH; LENGTH_APPEND] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Colours and the clausal form of matchg.                                   *)
(* ------------------------------------------------------------------------- *)

let COLOR_TAC =
  REPEAT CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC color_INDUCT THEN REPEAT CONJ_TAC) THEN
  REWRITE_TAC[addc_DEF; cbit0; cbit1; ccons; distinctness "color"];;

let CBIT0_COLOR23_EQ = prove
 (`!x y:color.
   ~(x = Color0) /\ ~(x = Color1) /\ ~(y = Color0) /\ ~(y = Color1) /\
   (cbit0 x <=> cbit0 y) ==> x = y`,
  COLOR_TAC THEN CONV_TAC TAUT);;

let ADDC_C23_EQ_C1 = prove
 (`!x y. ~(x = Color0) /\ ~(x = Color1) /\ ~(y = Color0) /\ ~(y = Color1) /\
         ~(cbit0 x <=> cbit0 y) ==> addc x y = Color1`,
  COLOR_TAC THEN CONV_TAC TAUT);;

let ADDC_COLOR1_23 = prove
 (`!e. ~(e = Color0) /\ ~(e = Color1)
       ==> ~(addc Color1 e = Color0) /\ ~(addc Color1 e = Color1) /\
           (cbit0(addc Color1 e) <=> ~cbit0 e)`,
  COLOR_TAC);;

let ADDC_CANCEL = prove
 (`(!a b:color. addc (addc a b) b = a) /\
   (!a b:color. addc a (addc a b) = b) /\
   (!a b:color. addc (addc a b) a = b) /\
   (!a b c:color. addc (addc a b) (addc b c) = addc a c)`,
  COLOR_TAC);;

let ADDC_CANCEL_SELF2 = prove
 (`!e1 e2:color. addc (addc e1 e2) e2 = e1`,
  REWRITE_TAC[ADDC_CANCEL]);;

let ADDC_SELF_CANCEL = prove
 (`!a b:color. addc a (addc a b) = b`,
  REWRITE_TAC[ADDC_CANCEL]);;

let MATCHG_CLAUSES = prove
 (`(!lb et. matchg lb et [] <=> et = [] /\ lb = []) /\
   (!lb w. matchg lb [] w <=> w = [] /\ lb = []) /\
   (!lb e et w. matchg lb (CONS e et) (CONS Gskip w) <=>
                e = Color1 /\ matchg lb et w) /\
   (!lb e et w. matchg lb (CONS e et) (CONS Gpush w) <=>
                ~(e = Color0) /\ ~(e = Color1) /\
                matchg (CONS (cbit0 e) lb) et w) /\
   (!e et w. matchg [] (CONS e et) (CONS Gpop0 w) <=> F) /\
   (!e et w. matchg [] (CONS e et) (CONS Gpop1 w) <=> F) /\
   (!b lb e et w. matchg (CONS b lb) (CONS e et) (CONS Gpop0 w) <=>
                  ~(e = Color0) /\ ~(e = Color1) /\ (cbit0 e <=> b) /\
                  matchg lb et w) /\
   (!b lb e et w. matchg (CONS b lb) (CONS e et) (CONS Gpop1 w) <=>
                  ~(e = Color0) /\ ~(e = Color1) /\ ~(cbit0 e <=> b) /\
                  matchg lb et w)`,
  REWRITE_TAC[matchg; GRAM_DISTINCT; NOT_CONS_NIL; HD; TL] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[matchg; NOT_CONS_NIL]);;

(* Case splits on a list and on a chromogram symbol with chosen names.       *)

let LIST_CASES_TAC tm x xs =
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN x (X_CHOOSE_THEN xs SUBST_ALL_TAC)) (ISPEC tm list_CASES);;

let GRAM_CASES_TAC s =
  REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC (SPEC s GRAM_CASES);;

(* ------------------------------------------------------------------------- *)
(* gram_neg negates the bit under the first unmatched Gpop; gram_flip turns  *)
(* a chromogram with exactly two unmatched Gpop into a balanced one.         *)
(* ------------------------------------------------------------------------- *)

let MATCH_GRAM_NEG_GEN = prove
 (`!w lb b0 et.
     matchg (APPEND lb [b0]) et (gram_neg_rec (LENGTH lb) w) <=>
     matchg (APPEND lb [~b0]) et w`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[gram_neg_rec; MATCHG_CLAUSES; APPEND_EQ_NIL; NOT_CONS_NIL] THEN
  LIST_CASES_TAC `et:color list` `e:color` `et':color list` THEN
  REWRITE_TAC[MATCHG_CLAUSES; APPEND_EQ_NIL; NOT_CONS_NIL] THEN
  GRAM_CASES_TAC `h:gram_symbol` THEN
  REWRITE_TAC[GRAM_DISTINCT; MATCHG_CLAUSES] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`CONS (cbit0 (e:color)) lb`; `b0:bool`; `et':color list`]) THEN
    REWRITE_TAC[APPEND; LENGTH; GSYM ADD1] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[];
    ALL_TAC; ALL_TAC] THEN
  LIST_CASES_TAC `lb:bool list` `b:bool` `lb':bool list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_SUB1; APPEND; MATCHG_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let MATCH_GRAM_NEG = prove
 (`!b0 et w. matchg [b0] et (gram_neg w) = matchg [~b0] et w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gram_neg] THEN
  MP_TAC(SPECL [`w:gram_symbol list`; `[]:bool list`; `b0:bool`;
                `et:color list`] MATCH_GRAM_NEG_GEN) THEN
  REWRITE_TAC[APPEND; LENGTH]);;

let GRAM_FLIP_REC_NOT_NIL = prove
 (`!w n. ~(gram_flip_rec n w = [])`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
    REWRITE_TAC[gram_flip_rec; NOT_CONS_NIL] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[NOT_CONS_NIL]));;

let MATCH_GRAM_FLIP_GEN = prove
 (`!w sb et.
     matchg sb et (gram_flip_rec (LENGTH sb) w) <=>
     matchg (APPEND sb [T; F]) et w \/ matchg (APPEND sb [F; T]) et w`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  LIST_CASES_TAC `et:color list` `e:color` `et':color list` THEN
  REWRITE_TAC[MATCHG_CLAUSES; APPEND_EQ_NIL; NOT_CONS_NIL;
              GRAM_FLIP_REC_NOT_NIL] THEN
  REWRITE_TAC[gram_flip_rec; MATCHG_CLAUSES; NOT_CONS_NIL] THEN
  GRAM_CASES_TAC `h:gram_symbol` THEN
  REWRITE_TAC[GRAM_DISTINCT; MATCHG_CLAUSES] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`CONS (cbit0 (e:color)) sb`; `et':color list`]) THEN
    REWRITE_TAC[APPEND; LENGTH; GSYM ADD1] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT;
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ALL_TAC; ALL_TAC] THEN
  LIST_CASES_TAC `sb:bool list` `b:bool` `sb':bool list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_SUB1; APPEND; MATCHG_CLAUSES;
              MATCH_GRAM_NEG] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `cbit0 (e:color)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let MATCH_GRAM_FLIP = prove
 (`!et w. matchg [] et (gram_flip w) <=>
          matchg [T; F] et w \/ matchg [F; T] et w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gram_flip] THEN
  MP_TAC(SPECL [`w:gram_symbol list`; `[]:bool list`; `et:color list`]
    MATCH_GRAM_FLIP_GEN) THEN
  REWRITE_TAC[APPEND; LENGTH]);;

let MATCHG_APPEND = prove
 (`!w bx lb lb0 et e s.
     gram_balanced (LENGTH lb) bx w
     ==> (matchg (APPEND lb lb0) (APPEND et [e]) (APPEND w [s]) <=>
          matchg lb et w /\ matchg lb0 [e] [s])`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  LIST_CASES_TAC `et:color list` `e0:color` `et':color list` THEN
  REWRITE_TAC[APPEND; gram_balanced; MATCHG_CLAUSES; NOT_CONS_NIL] THENL
   [REWRITE_TAC[LENGTH_EQ_NIL] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[APPEND];
    REWRITE_TAC[LENGTH_EQ_NIL] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[APPEND] THEN
    GRAM_CASES_TAC `s:gram_symbol` THEN
    LIST_CASES_TAC `lb0:bool list` `b:bool` `lb0':bool list` THEN
    REWRITE_TAC[MATCHG_CLAUSES; APPEND_EQ_NIL; NOT_CONS_NIL];
    DISCH_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MATCHG_SIZE) THEN
    REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC;
    ALL_TAC] THEN
  GRAM_CASES_TAC `h:gram_symbol` THEN
  REWRITE_TAC[GRAM_DISTINCT; MATCHG_CLAUSES] THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`bx:bool`; `CONS (cbit0 (e0:color)) lb`; `lb0:bool list`;
      `et':color list`; `e:color`; `s:gram_symbol`]) THEN
    ASM_REWRITE_TAC[LENGTH; APPEND; ADD1];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`~bx`; `lb:bool list`; `lb0:bool list`;
      `et':color list`; `e:color`; `s:gram_symbol`]) THEN
    ASM_REWRITE_TAC[];
    LIST_CASES_TAC `lb:bool list` `b:bool` `lb':bool list` THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_SUB1; APPEND; MATCHG_CLAUSES] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`bx:bool`; `lb':bool list`; `lb0:bool list`;
      `et':color list`; `e:color`; `s:gram_symbol`]) THEN
    ASM_REWRITE_TAC[];
    LIST_CASES_TAC `lb:bool list` `b:bool` `lb':bool list` THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_SUB1; APPEND; MATCHG_CLAUSES] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`~bx`; `lb':bool list`; `lb0:bool list`;
      `et':color list`; `e:color`; `s:gram_symbol`]) THEN
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT);;

let MATCH_GRAM_ROT = prove
 (`!et w. matchg [] (rot1 et) (gram_rot w) <=> matchg [] et w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gram_rot] THEN
  ASM_CASES_TAC `?b. gram_balanced 0 b (w:gram_symbol list)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `!et. ~matchg [] et (w:gram_symbol list)`
      (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP MATCHG_BALANCED) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~(?b. gram_balanced 0 b (w:gram_symbol list))` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `cbit0(sumt(et:color list))` THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `b0:bool`) THEN
  LIST_CASES_TAC `w:gram_symbol list` `s:gram_symbol`
    `w':gram_symbol list` THENL
   [REWRITE_TAC[MATCHG_CLAUSES; rot1] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL];
    ALL_TAC] THEN
  REWRITE_TAC[HD; TL; NOT_CONS_NIL] THEN
  UNDISCH_TAC `gram_balanced 0 b0 (CONS (s:gram_symbol) w')` THEN
  GRAM_CASES_TAC `s:gram_symbol` THEN
  REWRITE_TAC[GRAM_DISTINCT; gram_balanced; ADD_CLAUSES] THEN DISCH_TAC THENL
   [REWRITE_TAC[MATCH_GRAM_FLIP] THEN
    LIST_CASES_TAC `et:color list` `e:color` `et':color list` THEN
    REWRITE_TAC[ROT1_NIL; ROT1_CONS; MATCHG_CLAUSES; APPEND_EQ_NIL;
                NOT_CONS_NIL] THEN
    MP_TAC(ISPECL [`w':gram_symbol list`; `b0:bool`; `[T]`; `[F]`;
                   `et':color list`; `e:color`; `Gpop1`] MATCHG_APPEND) THEN
    MP_TAC(ISPECL [`w':gram_symbol list`; `b0:bool`; `[F]`; `[T]`;
                   `et':color list`; `e:color`; `Gpop1`] MATCHG_APPEND) THEN
    ASM_REWRITE_TAC[LENGTH; APPEND; MATCHG_CLAUSES;
                    ARITH_RULE `SUC 0 = 1`] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ASM_CASES_TAC `cbit0 (e:color)` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC TAUT;
    LIST_CASES_TAC `et:color list` `e:color` `et':color list` THEN
    REWRITE_TAC[ROT1_NIL; ROT1_CONS; MATCHG_CLAUSES; APPEND_EQ_NIL;
                NOT_CONS_NIL] THEN
    MP_TAC(ISPECL [`w':gram_symbol list`; `~b0`; `[]:bool list`;
                   `[]:bool list`; `et':color list`; `e:color`; `Gskip`]
      MATCHG_APPEND) THEN
    ASM_REWRITE_TAC[LENGTH; APPEND; MATCHG_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT]);;

(* ------------------------------------------------------------------------- *)
(* Rotation of lists and of ring traces.                                     *)
(* ------------------------------------------------------------------------- *)

let MAP_ROT1 = prove
 (`!f:A->B l. MAP f (rot1 l) = rot1 (MAP f l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ROT1_NIL; ROT1_CONS; MAP; MAP_APPEND]);;

let MEM_ROT1 = prove
 (`!r (x:A). MEM x (rot1 r) <=> MEM x r`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ROT1_NIL; ROT1_CONS; MEM; MEM_APPEND] THEN
  CONV_TAC TAUT);;

let SET_OF_LIST_ROT1 = prove
 (`!r:(A)list. set_of_list(rot1 r) = set_of_list r`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_ROT1]);;

let ALL_ROT1 = prove
 (`!P r:(A)list. ALL P (rot1 r) <=> ALL P r`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ROT1_NIL; ROT1_CONS; ALL; ALL_APPEND] THEN CONV_TAC TAUT);;

let PAIRWISE_ROT1 = prove
 (`!r:(A)list. PAIRWISE (\x y. ~(x = y)) (rot1 r) <=>
               PAIRWISE (\x y. ~(x = y)) r`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ROT1_NIL; ROT1_CONS; PAIRWISE_DISTINCT_APPEND;
              PAIRWISE_DISTINCT_CONS; PAIRWISE; MEM] THEN
  MESON_TAC[]);;

let LIST_CYCLE_ROT1 = prove
 (`!(e:A->A->bool) r. list_cycle e (rot1 r) <=> list_cycle e r`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ROT1_NIL; ROT1_CONS; list_cycle; NOT_CONS_NIL; APPEND_EQ_NIL;
              LAST_APPEND_SING; LIST_PATH_APPEND; list_path] THEN
  CONV_TAC TAUT);;

let TRACE_COL_ROT1 = prove
 (`!s:color list. ~(s = []) ==> trace_col(rot1 s) = rot1(trace_col s)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; ROT1_CONS; trace_DEF; APPEND_EQ_NIL;
              LAST_APPEND_SING; ptrace] THEN
  ONCE_REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] THEN
  SIMP_TAC[PTRACE_SNOC; NOT_CONS_NIL]);;

let ROT1_ROTR1 = prove
 (`!l:(A)list. rot1(rotr1 l) = l`,
  LIST_INDUCT_TAC THEN
    REWRITE_TAC[rotr1; ROT1_NIL; NOT_CONS_NIL; ROT1_CONS] THEN
  SIMP_TAC[APPEND_BUTLAST_LAST; NOT_CONS_NIL]);;

let ROTR1_ROT1 = prove
 (`!l:(A)list. rotr1(rot1 l) = l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[rotr1; ROT1_NIL; ROT1_CONS; APPEND_EQ_NIL; NOT_CONS_NIL;
              LAST_APPEND_SING; BUTLAST_APPEND; BUTLAST; APPEND_NIL]);;

let MAP_ROTR1 = prove
 (`!f:A->B l. MAP f (rotr1 l) = rotr1 (MAP f l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `rotr1 (l:A list)`] MAP_ROT1) THEN
  REWRITE_TAC[ROT1_ROTR1] THEN
  DISCH_THEN(MP_TAC o AP_TERM `rotr1:(B)list->(B)list`) THEN
  REWRITE_TAC[ROTR1_ROT1] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let TRACE_COL_ROTR1 = prove
 (`!(lc:color list). ~(lc = []) ==> trace_col(rotr1 lc) = rotr1(trace_col lc)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(rotr1 (lc:color list) = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[ROT1_ROTR1; ROT1_NIL]; ALL_TAC] THEN
  MP_TAC(SPEC `rotr1(lc:color list)` TRACE_COL_ROT1) THEN
  ASM_REWRITE_TAC[ROT1_ROTR1] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; ROTR1_ROT1]));;

let LENGTH_ITER_ROT1 = prove
 (`!n (l:(A)list). LENGTH(ITER n rot1 l) = LENGTH l`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; LENGTH_ROT1]);;

let ITER_ROT1_NOT_NIL = prove
 (`!n (l:(A)list). ~(l = []) ==> ~(ITER n rot1 l = [])`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_ITER_ROT1]);;

let ITER_ROT1_APPEND = prove
 (`!l1 (l2:(A)list). ITER (LENGTH l1) rot1 (APPEND l1 l2) = APPEND l2 l1`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ITER_ALT; APPEND; APPEND_NIL; ROT1_CONS;
                  GSYM APPEND_ASSOC]);;

let ROTR1_ITER_ROT1 = prove
 (`!l:(A)list. ~(l = []) ==> rotr1 l = ITER (LENGTH l - 1) rot1 l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; LENGTH; SUC_SUB1] THEN
  MP_TAC(ISPECL [`CONS (h:A) t`; `[]:(A)list`] ITER_ROT1_APPEND) THEN
  REWRITE_TAC[APPEND_NIL; APPEND; LENGTH; ITER] THEN
  DISCH_THEN(MP_TAC o AP_TERM `rotr1:(A)list->(A)list`) THEN
  REWRITE_TAC[ROTR1_ROT1] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let ITER_ROT1_INVARIANTS = prove
 (`!n (e:A->A->bool) P r.
     set_of_list (ITER n rot1 r) = set_of_list r /\
     (list_cycle e (ITER n rot1 r) <=> list_cycle e r) /\
     (PAIRWISE (\x y. ~(x = y)) (ITER n rot1 r) <=>
      PAIRWISE (\x y. ~(x = y)) r) /\
     (ALL P (ITER n rot1 r) <=> ALL P r)`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITER; SET_OF_LIST_ROT1; LIST_CYCLE_ROT1; PAIRWISE_ROT1;
                  ALL_ROT1]);;

let RING_TRACE_ROT1 = prove
 (`!(H:(A)hypermap) r et. ~(r = []) /\ ring_trace H r et
    ==> ring_trace H (rot1 r) (rot1 et)`,
  REWRITE_TAC[ring_trace] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `k:A->color` THEN
  ASM_SIMP_TAC[MAP_ROT1; TRACE_COL_ROT1; MAP_EQ_NIL]);;

let RING_TRACE_ROT1_ROTR1 = prove
 (`!(H:(A)hypermap) r et.
     ~(r = []) ==> (ring_trace H (rot1 r) et <=> ring_trace H r (rotr1 et))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[ring_trace] THEN STRIP_TAC THEN EXISTS_TAC `k:A->color` THEN
    ASM_SIMP_TAC[MAP_ROT1; TRACE_COL_ROT1; MAP_EQ_NIL; ROTR1_ROT1];
    DISCH_THEN(MP_TAC o MATCH_MP RING_TRACE_ROT1 o CONJ (ASSUME `~(r:(A)list =
      [])`)) THEN
    REWRITE_TAC[ROT1_ROTR1]]);;

(* The Kempe property of a ring is invariant under rotation.                 *)

let MATCH_GRAM_ROT_ALT = prove
 (`!et w. matchg [] et (gram_rot w) <=> matchg [] (rotr1 et) w`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [GSYM ROT1_ROTR1] THEN
  REWRITE_TAC[MATCH_GRAM_ROT]);;

let CHROMOGRAM_ROT1_STEP = prove
 (`!(H:(A)hypermap) r.
   ~(r = []) /\
   (!et. ring_trace H r et ==>
     ?w. matchg [] et w /\ !et'. matchg [] et' w ==> ring_trace H r et')
   ==> (!et. ring_trace H (rot1 r) et ==>
     ?w. matchg [] et w /\
         !et'. matchg [] et' w ==> ring_trace H (rot1 r) et')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `et:color list` THEN
  ASM_SIMP_TAC[RING_TRACE_ROT1_ROTR1] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:gram_symbol list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gram_rot w` THEN ASM_REWRITE_TAC[MATCH_GRAM_ROT_ALT]);;

let CHROMOGRAM_ROT_ITER = prove
 (`!(H:(A)hypermap) r n.
   ~(r = []) ==>
   (!et. ring_trace H r et ==>
     ?w. matchg [] et w /\ !et'. matchg [] et' w ==> ring_trace H r et')
   ==> (!et. ring_trace H (ITER n rot1 r) et ==>
     ?w. matchg [] et w /\
         !et'. matchg [] et' w ==> ring_trace H (ITER n rot1 r) et')`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  DISCH_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CHROMOGRAM_ROT1_STEP THEN
  ASM_SIMP_TAC[ITER_ROT1_NOT_NIL]);;

(* ------------------------------------------------------------------------- *)
(* Node cycles: closure under the map, orbits, and the Euler-tree leaf.      *)
(* ------------------------------------------------------------------------- *)

let LIST_CYCLE_HD = prove
 (`!f (x:A) p. list_cycle (\x y. f x = y) (x :: p) ==> f (LAST (x :: p)) = x`,
  REWRITE_TAC[list_cycle; NOT_CONS_NIL; list_path] THEN MESON_TAC[]);;

let LIST_CYCLE_F_CLOSED = prove
 (`!f (r:(A)list).
    list_cycle (\x y. f x = y) r ==> (!y. MEM y r ==> MEM (f y) r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_cycle] THEN
  LIST_CASES_TAC `r:(A)list` `x:A` `m:(A)list` THEN
  REWRITE_TAC[NOT_CONS_NIL; list_path] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIST_PATH_F_MEM) THEN
  REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let ORBIT_CYCLE_MEM = prove
 (`!f (r:(A)list) x.
    list_cycle (\x y. f x = y) r /\ MEM x r
    ==> (!y. y IN orbit_map f x ==> MEM y r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIST_CYCLE_F_CLOSED) THEN DISCH_TAC THEN
  REWRITE_TAC[ORBIT_MAP_ITER] THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN ASM_SIMP_TAC[ITER]);;

let LIST_CYCLE_MEM_ORBIT = prove
 (`!f (s:A->bool) r x.
    f permutes s /\ FINITE s /\
    list_cycle (\x y. f x = y) r /\
    (!z. MEM z r ==> z IN s) /\ MEM x r
    ==> (!y. MEM y r ==> y IN orbit_map f x)`,
  REWRITE_TAC[list_cycle] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIST_PATH_MEM_ORBIT) THEN DISCH_TAC THEN
  SUBGOAL_THEN `orbit_map f (x:A) = orbit_map f (LAST r)` SUBST1_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `s:A->bool` THEN
    ASM_MESON_TAC[MEM_LAST];
    ASM_SIMP_TAC[]]);;

let FACE_SIMPLE_PAIRWISE_GEN = prove
 (`!H:(A)hypermap r. face_simple H r ==> PAIRWISE (\x y. ~(x = y)) r`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[PAIRWISE];
    REWRITE_TAC[face_simple; PAIRWISE_DISTINCT_CONS; fband; GSYM EX_MEM] THEN
    ASM_MESON_TAC[CFACE_REFL]]);;

let KEMPE_LEAF = prove
 (`!(G:(A)hypermap) r.
    planar_hypermap G /\ plain_hypermap G /\
    list_cycle (\x y. node_map G x = y) r /\ ALL (\x. x IN dart G) r
    ==> ?z. MEM z r /\ (face_map G z = z \/ ~MEM (face_map G z) r)`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  SUBGOAL_THEN `~(r:(A)list = []) /\ MEM (HD r) r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[list_cycle; MEM; CONS_HD_TL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!z:A. MEM z r ==> !y. MEM y r ==> y IN orbit_map (node_map G) z`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LIST_CYCLE_MEM_ORBIT THEN
    EXISTS_TAC `dart(G:(A)hypermap)` THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FINITE_DART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`permN(G:(A)hypermap)`; `HD(r:(A)list)`] EULER_TREE) THEN
  ASM_SIMP_TAC[PERMN_COMPONENTS; clink; cross_edge] THEN ANTS_TAC THENL
   [MATCH_MP_TAC PLANAR_JORDAN THEN
    UNDISCH_TAC `planar_hypermap (G:(A)hypermap)` THEN
    REWRITE_TAC[planar_hypermap; GENUS_PERMN];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `MEM (z:A) r` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `r:(A)list`; `HD(r:(A)list)`]
      ORBIT_CYCLE_MEM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `~(edge_map G (z:A) = z) /\
     (MEM (face_map G z) r ==> face_map G z IN orbit_map (node_map G) z)`
    MP_TAC THENL [ASM_MESON_TAC[PLAIN_NEQ]; ALL_TAC] THEN
  UNDISCH_TAC `MEM (z:A) r` THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The double Walkup contraction H = edge_walkup (node_walkup G z) (edge z)  *)
(* of a plain hypermap G without node fixpoints: its darts are those of G    *)
(* except z and ez = edge z, its edge map is that of G, and its node and     *)
(* face maps are those of G with z and ez skipped.                           *)
(* ------------------------------------------------------------------------- *)

let PLAIN_Z_FACTS = prove
 (`!(G:(A)hypermap) z.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y))
     ==> ~(edge_map G z = z) /\ edge_map G z IN dart G /\
         edge_map G (edge_map G z) = z /\
         face_map G z IN dart G /\ face_map G (edge_map G z) IN dart G /\
         node_map G (face_map G z) = edge_map G z /\
         node_map G (face_map G (edge_map G z)) = z /\
         ~(face_map G z = edge_map G z) /\
         ~(face_map G (edge_map G z) = z) /\
         ~(face_map G (edge_map G z) = face_map G z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `edge_map G (z:A) IN dart G /\ edge_map G (edge_map G z) = z /\
     ~(edge_map G z = z)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART; PLAIN_EQ; PLAIN_NEQ]; ALL_TAC] THEN
  SUBGOAL_THEN
    `node_map G (face_map G z) = edge_map G (z:A) /\
     node_map G (face_map G (edge_map G z)) = z` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PLAIN_EQ']; ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_MAP_IN_DART] THEN ASM_MESON_TAC[]);;

let DART_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z.
     plain_hypermap G /\ z IN dart G
     ==> dart(edge_walkup (node_walkup G z) (edge_map G z)) =
         dart G DELETE z DELETE (edge_map G z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `edge_map G z IN dart(node_walkup G (z:A))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DART_NODE_WALKUP; IN_DELETE; EDGE_MAP_IN_DART; PLAIN_NEQ];
    ASM_SIMP_TAC[EDGE_WALKUP_COMPONENTS; DART_NODE_WALKUP]]);;

let EDGE_MAP_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z x.
     plain_hypermap G /\ z IN dart G /\
     x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z)
     ==> edge_map (edge_walkup (node_walkup G z) (edge_map G z)) x =
         edge_map G x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `~(edge_map G z = z:A) /\ edge_map G z IN dart G /\
     edge_map G (edge_map G z) = z /\ edge_map G (edge_map G x) = x`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PLAIN_NEQ; EDGE_MAP_IN_DART; PLAIN_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
    `edge_map G z IN dart(node_walkup G (z:A)) /\
     edge_map (node_walkup G z) (edge_map G z) = edge_map G z`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DART_NODE_WALKUP; IN_DELETE; EDGE_MAP_NODE_WALKUP] THEN
    ASM_REWRITE_TAC[SWAP_ENDS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`node_walkup G (z:A)`; `edge_map G (z:A)`]
    EDGE_MAP_GLINK_SKIP) THEN
  ASM_REWRITE_TAC[glink] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[o_THM; EDGE_MAP_NODE_WALKUP; SWAP_REFL; I_THM] THEN
  MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[]);;

let FACE_MAP_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z x.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z)
     ==> face_map (edge_walkup (node_walkup G z) (edge_map G z)) x =
         (if face_map G x = z then face_map G z
          else if face_map G x = edge_map G z then face_map G (edge_map G z)
          else face_map G x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`] PLAIN_Z_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `edge_map G (z:A) IN dart(node_walkup G (z:A))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DART_NODE_WALKUP; IN_DELETE]; ALL_TAC] THEN
  ASM_SIMP_TAC[EDGE_WALKUP_COMPONENTS; o_THM; FACE_MAP_NODE_WALKUP] THEN
  SUBGOAL_THEN
    `~(face_map G (x:A) = face_map G z) /\
     ~(face_map G x = face_map G (edge_map G z))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[HYPERMAP_INJ_EQ] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[SWAP_ENDS; SWAP_OTHER]));;

let NODE_MAP_CHAR = prove
 (`!(H:(A)hypermap) x c. face_map H (edge_map H c) = x ==> node_map H x = c`,
  MESON_TAC[edgeK]);;

let FACE_H_EDGE_H = prove
 (`!(G:(A)hypermap) z c.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     c IN dart G /\ ~(c = z) /\ ~(c = edge_map G z)
     ==> face_map (edge_walkup (node_walkup G z) (edge_map G z))
           (edge_map (edge_walkup (node_walkup G z) (edge_map G z)) c) =
         (if face_map G (edge_map G c) = z then face_map G z
          else if face_map G (edge_map G c) = edge_map G z
          then face_map G (edge_map G z)
          else face_map G (edge_map G c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `edge_map G (c:A) IN dart G /\ ~(edge_map G c = z) /\
     ~(edge_map G c = edge_map G z)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART] THEN
    ASM_MESON_TAC[HYPERMAP_INJ_EQ; PLAIN_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[EDGE_MAP_DOUBLE_WALKUP] THEN
  MATCH_MP_TAC FACE_MAP_DOUBLE_WALKUP THEN ASM_REWRITE_TAC[]);;

let NODE_MAP_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z x.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z)
     ==> node_map (edge_walkup (node_walkup G z) (edge_map G z)) x =
         (if node_map G x = z then node_map G (edge_map G z)
          else if node_map G x = edge_map G z then node_map G z
          else node_map G x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`] PLAIN_Z_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC NODE_MAP_CHAR THEN
  SUBGOAL_THEN
    `node_map G (x:A) IN dart G /\ node_map G (edge_map G z) IN dart G /\
     node_map G z IN dart G` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_IN_DART]; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THENL
   [SUBGOAL_THEN `x:A = face_map G (edge_map G z)` ASSUME_TAC THENL
     [ASM_MESON_TAC[nodeK]; ALL_TAC] THEN
    MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `node_map G (edge_map G (z:A))`]
      FACE_H_EDGE_H) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HYPERMAP_INJ_EQ]; ALL_TAC] THEN
    REWRITE_TAC[nodeK] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `x:A = face_map G z` ASSUME_TAC THENL
     [ASM_MESON_TAC[nodeK]; ALL_TAC] THEN
    MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `node_map G (z:A)`]
      FACE_H_EDGE_H) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HYPERMAP_INJ_EQ]; ALL_TAC] THEN
    REWRITE_TAC[nodeK] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `node_map G (x:A)`]
      FACE_H_EDGE_H) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[nodeK] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Colourings of G restrict to H, and colourings of H extend to G when the   *)
(* two new colours are distinct and agree with the faces of z and edge z.    *)
(* ------------------------------------------------------------------------- *)

let COLORING_NO_NODE_FP = prove
 (`!(G:(A)hypermap) k y. coloring G k /\ y IN dart G ==> ~(node_map G y = y)`,
  REWRITE_TAC[coloring] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `face_map G (edge_map G y) = (y:A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `face_map G (edge_map G (y:A))`; `y:A`]
      NODEI) THEN ASM_REWRITE_TAC[edgeK];
    ASM_MESON_TAC[EDGE_MAP_IN_DART]]);;

let COLORING_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z k.
     plain_hypermap G /\ z IN dart G /\ coloring G k
     ==> coloring (edge_walkup (node_walkup G z) (edge_map G z)) k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:A. y IN dart G ==> ~(node_map G y = y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLORING_NO_NODE_FP]; ALL_TAC] THEN
  UNDISCH_TAC `coloring G (k:A->color)` THEN REWRITE_TAC[coloring] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[DART_DOUBLE_WALKUP; IN_DELETE] THEN
  CONJ_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EDGE_MAP_DOUBLE_WALKUP; FACE_MAP_DOUBLE_WALKUP] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
  ASM_MESON_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART]);;

let COLORING_DOUBLE_WALKUP_LIFT = prove
 (`!(G:(A)hypermap) z k cz cez.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     coloring (edge_walkup (node_walkup G z) (edge_map G z)) k /\
     ~(cz = cez) /\
     (face_map G z = z \/ k (face_map G z) = cz) /\
     (face_map G (edge_map G z) = edge_map G z \/
      k (face_map G (edge_map G z)) = cez)
     ==> coloring G
          (\x. if x = z then cz else if x = edge_map G z then cez else k x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`] PLAIN_Z_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:A. x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z)
          ==> ~((k:A->color)(edge_map G x) = k x) /\
              k(if face_map G x = z then face_map G z
                else if face_map G x = edge_map G z
                then face_map G (edge_map G z) else face_map G x) = k x`
   ASSUME_TAC THENL
   [UNDISCH_TAC `coloring (edge_walkup (node_walkup G z) (edge_map G z))
                          (k:A->color)` THEN
    ASM_SIMP_TAC[coloring; DART_DOUBLE_WALKUP; IN_DELETE;
                 EDGE_MAP_DOUBLE_WALKUP; FACE_MAP_DOUBLE_WALKUP];
    ALL_TAC] THEN
  REWRITE_TAC[coloring] THEN CONJ_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  (ASM_CASES_TAC `x:A = z` THENL
    [ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN ASM_MESON_TAC[];
     ALL_TAC]) THEN
  (ASM_CASES_TAC `x:A = edge_map G z` THENL
    [ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN ASM_MESON_TAC[];
     ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
  THENL
   [SUBGOAL_THEN `~(edge_map G x = z) /\ ~(edge_map G x = edge_map G (z:A))`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[PLAIN_EQ; EDGEI];
    POP_ASSUM MP_TAC THEN
    ASM_CASES_TAC `face_map G x = z` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[FACEI]; ALL_TAC] THEN
    ASM_CASES_TAC `face_map G x = edge_map G z` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACEI]]);;

(* ------------------------------------------------------------------------- *)
(* Size, planarity and plainness of H; node orbits away from z and edge z.   *)
(* ------------------------------------------------------------------------- *)

let CARD_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z.
     plain_hypermap G /\ z IN dart G
     ==> CARD(dart(edge_walkup (node_walkup G z) (edge_map G z))) <
         CARD(dart G)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DART_DOUBLE_WALKUP] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN REWRITE_TAC[FINITE_DART] THEN
  UNDISCH_TAC `z:A IN dart G` THEN SET_TAC[]);;

let PLANAR_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z.
     plain_hypermap G /\ z IN dart G /\ planar_hypermap G
     ==> planar_hypermap(edge_walkup (node_walkup G z) (edge_map G z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PLANAR_EDGE_WALKUP THEN
  ASM_SIMP_TAC[PLANAR_NODE_WALKUP; DART_NODE_WALKUP; IN_DELETE;
               EDGE_MAP_IN_DART; PLAIN_NEQ]);;

let PLAIN_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z.
     plain_hypermap G /\ z IN dart G
     ==> plain_hypermap(edge_walkup (node_walkup G z) (edge_map G z))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `H = edge_walkup (node_walkup G z) (edge_map G (z:A))` THEN
  REWRITE_TAC[plain_hypermap] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `x IN dart G /\ ~(x:A = z) /\ ~(x = edge_map G z)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `x:A IN dart H` THEN EXPAND_TAC "H" THEN
    ASM_SIMP_TAC[DART_DOUBLE_WALKUP; IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map G x IN dart G /\ ~(edge_map G x = z:A) /\
                ~(edge_map G x = edge_map G z) /\ ~(edge_map G x = x) /\
                edge_map G (edge_map G x) = x` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART; PLAIN_NEQ; PLAIN_EQ] THEN
    ASM_MESON_TAC[PLAIN_EQ; HYPERMAP_INJ_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map H x = edge_map G (x:A) /\
                edge_map H (edge_map G x) = x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN ASM_SIMP_TAC[EDGE_MAP_DOUBLE_WALKUP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`edge_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`; `x:A`]
    ORBIT_SIZE_2) THEN
  ASM_SIMP_TAC[FINITE_DART; EDGE_MAP_PERMUTES]);;

let ORBIT_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z x.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\ x IN dart G /\
     (!y. y IN orbit_map (node_map G) x ==> ~(y = z) /\ ~(y = edge_map G z))
     ==> orbit_map (node_map (edge_walkup (node_walkup G z) (edge_map G z))) x
       =
         orbit_map (node_map G) x /\
         orbit_size (node_map (edge_walkup (node_walkup G z) (edge_map G z)))
           x =
         orbit_size (node_map G) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `!n. ITER n (node_map (edge_walkup (node_walkup G z) (edge_map G z))) x =
         ITER n (node_map G) (x:A)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ITER_AGREE THEN X_GEN_TAC `n:num` THEN
    ABBREV_TAC `y = ITER n (node_map G) (x:A)` THEN
    SUBGOAL_THEN `y IN orbit_map (node_map G) (x:A) /\
                  node_map G y IN orbit_map (node_map G) x`
      STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[GSYM(CONJUNCT2 ITER); ITER_IN_ORBIT];
      ALL_TAC] THEN
    SUBGOAL_THEN `y:A IN dart G` ASSUME_TAC THENL
     [ASM_MESON_TAC[ORBIT_SUBSET; SUBSET; NODE_MAP_PERMUTES]; ALL_TAC] THEN
    SUBGOAL_THEN
      `~(y:A = z) /\ ~(y = edge_map G z) /\
       ~(node_map G y = z) /\ ~(node_map G y = edge_map G z)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `y:A`] NODE_MAP_DOUBLE_WALKUP) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
      `orbit_map (node_map (edge_walkup (node_walkup G z) (edge_map G z))) x =
       orbit_map (node_map G) (x:A)`
      (fun th -> REWRITE_TAC[th; orbit_size]) THEN
    ASM_REWRITE_TAC[EXTENSION; ORBIT_MAP_ITER]]);;

let QUASICUBIC_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z s.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     (!x. x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z) /\ ~(x IN s)
          ==> orbit_size (node_map G) x = 3 /\
              (!y. y IN orbit_map (node_map G) x
                   ==> ~(y = z) /\ ~(y = edge_map G z)))
     ==> quasicubic (edge_walkup (node_walkup G z) (edge_map G z)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[quasicubic] THEN
  ASM_SIMP_TAC[DART_DOUBLE_WALKUP; IN_DELETE] THEN X_GEN_TAC `x:A` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `x:A`] ORBIT_DOUBLE_WALKUP) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* A node orbit through three darts in a 3-cycle.                            *)

let ORBIT_MAP_3CYCLE_SUBSET = prove
 (`!f (a:A) b c. f a = b /\ f b = c /\ f c = a
                 ==> orbit_map f a SUBSET {a, b, c}`,
  REWRITE_TAC[SUBSET; ORBIT_MAP_ITER; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Traces of the rings z :: nz :: p1 (in G) and nez :: fz :: nz :: p1 (in H).*)
(* ------------------------------------------------------------------------- *)

let TRACE_COL_CONS = prove
 (`!c cs:color list.
     trace_col (CONS c cs) = CONS (addc (LAST (CONS c cs)) c) (ptrace (CONS c
       cs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace_DEF; NOT_CONS_NIL; ptrace]);;

let LAST_MAP_CONS = prove
 (`!(k:A->B) a l. LAST (CONS (k a) (MAP k l)) = k (LAST (CONS a l))`,
  REWRITE_TAC[GSYM(CONJUNCT2 MAP)] THEN SIMP_TAC[LAST_MAP; NOT_CONS_NIL]);;

let TRACE_COL_RING = prove
 (`!(k:A->color) z nz p1.
     trace_col (MAP k (CONS z (CONS nz p1))) =
     CONS (addc (k (LAST (CONS nz p1))) (k z))
          (CONS (addc (k z) (k nz)) (ptrace (CONS (k nz) (MAP k p1))))`,
  REWRITE_TAC[MAP; TRACE_COL_CONS; ptrace] THEN
  SIMP_TAC[LAST_CONS_NE; NOT_CONS_NIL; LAST_MAP_CONS]);;

let TRACE_COL_RING_H = prove
 (`!(k:A->color) nez fz nz p1.
     trace_col (MAP k (CONS nez (CONS fz (CONS nz p1)))) =
     CONS (addc (k (LAST (CONS nz p1))) (k nez))
          (CONS (addc (k nez) (k fz))
                (CONS (addc (k fz) (k nz)) (ptrace (CONS (k nz) (MAP k
                  p1)))))`,
  REWRITE_TAC[MAP; TRACE_COL_CONS; ptrace] THEN
  SIMP_TAC[LAST_CONS_NE; NOT_CONS_NIL; LAST_MAP_CONS]);;

let TRACE_COL_RING_A = prove
 (`!(k:A->color) z nz p1.
     k (LAST (CONS nz p1)) = k nz
     ==> trace_col (MAP k (CONS z (CONS nz p1))) =
         CONS (addc (k z) (k nz))
              (CONS (addc (k z) (k nz)) (trace_col (MAP k p1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TRACE_COL_RING] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[CONS_11] THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC ADDC_COMM; ALL_TAC] THEN
  LIST_CASES_TAC `p1:(A)list` `h:A` `t:(A)list` THEN
  REWRITE_TAC[MAP; ptrace; trace_DEF; TRACE_COL_CONS; NOT_CONS_NIL;
              CONS_11] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  SIMP_TAC[LAST_CONS_NE; NOT_CONS_NIL; LAST_MAP_CONS]);;

(* A colouring separates a dart from its node successor.                     *)

let COLORING_NODE_NEQ = prove
 (`!(G:(A)hypermap) k y.
     coloring G k /\ y IN dart G ==> ~(k y = k (node_map G y))`,
  REWRITE_TAC[coloring] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `edge_map G (node_map G (y:A))`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `node_map G (y:A)`) THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; EDGE_MAP_IN_DART; nodeK] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The ring of H.  With r = z :: nz :: p1 a node ring of G through the leaf  *)
(* z: when face z = z the ring of H is p1 (and nz = edge z); when face z is  *)
(* not on r the ring of H is nez :: fz :: nz :: p1 where fz = face z,        *)
(* ez = edge z = node fz and nez = node ez (the node of fz is a 3-cycle).    *)
(* ------------------------------------------------------------------------- *)

let RING_FACTS = prove
 (`!(G:(A)hypermap) z nz p1.
     list_cycle (\x y. node_map G x = y) (CONS z (CONS nz p1))
     ==> node_map G z = nz /\ node_map G (LAST (CONS nz p1)) = z /\
         list_path (\x y. node_map G x = y) nz p1`,
  REWRITE_TAC[list_cycle; list_path; NOT_CONS_NIL] THEN
  SIMP_TAC[LAST_CONS_NE; NOT_CONS_NIL] THEN MESON_TAC[]);;

let RING_ORBIT = prove
 (`!(G:(A)hypermap) r x y.
     list_cycle (\x y. node_map G x = y) r /\ ALL (\x. x IN dart G) r /\
     MEM x r
     ==> (MEM y r <=> y IN orbit_map (node_map G) x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`;
                   `r:(A)list`; `x:A`] LIST_CYCLE_MEM_ORBIT) THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FINITE_DART] THEN
    ASM_MESON_TAC[ALL_MEM];
    MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `r:(A)list`; `x:A`]
      ORBIT_CYCLE_MEM) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* A node_G path whose targets avoid z and edge z is a node_H path.          *)

let LIST_PATH_DOUBLE_WALKUP = prove
 (`!(G:(A)hypermap) z a p.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     list_path (\x y. node_map G x = y) a p /\
     ALL (\x. x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z)) (CONS a p)
     ==> list_path
          (\x y. node_map (edge_walkup (node_walkup G z) (edge_map G z)) x = y)
          a p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_PATH_MONO THEN
  EXISTS_TAC `\x y:A. node_map G x = y` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  SUBGOAL_THEN `u IN dart G /\ ~(u:A = z) /\ ~(u = edge_map G z) /\
                ~(v:A = z) /\ ~(v = edge_map G z)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  ASM_SIMP_TAC[NODE_MAP_DOUBLE_WALKUP] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let ORBIT_AVOIDS_RING = prove
 (`!(G:(A)hypermap) r x w.
     list_cycle (\x y. node_map G x = y) r /\ ALL (\x. x IN dart G) r /\
     x IN dart G /\ ~(MEM x r) /\ MEM w r
     ==> ~(w IN orbit_map (node_map G) x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x IN orbit_map (node_map G) (w:A)` MP_TAC THENL
   [MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`;
                   `x:A`; `w:A`] ORBIT_MAP_EQ) THEN
    ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FINITE_DART] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_ORBIT_MAP_REFL];
    MP_TAC(ISPECL [`G:(A)hypermap`; `r:(A)list`; `w:A`; `x:A`] RING_ORBIT) THEN
    ASM_REWRITE_TAC[]]);;

let RING_CASE_A = prove
 (`!(G:(A)hypermap) z p1.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     list_cycle (\x y. node_map G x = y) (CONS z (CONS (edge_map G z) p1)) /\
     PAIRWISE (\x y. ~(x = y)) (CONS z (CONS (edge_map G z) p1)) /\
     ALL (\x. x IN dart G) (CONS z (CONS (edge_map G z) p1)) /\
     quasicubic G (set_of_list (CONS z (CONS (edge_map G z) p1))) /\
     ~(p1 = [])
     ==> list_cycle
           (\x y. node_map (edge_walkup (node_walkup G z) (edge_map G z)) x =
             y)
           p1 /\
         PAIRWISE (\x y. ~(x = y)) p1 /\
         ALL (\x. x IN dart (edge_walkup (node_walkup G z) (edge_map G z))) p1
           /\
         quasicubic (edge_walkup (node_walkup G z) (edge_map G z))
                    (set_of_list p1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_FACTS) THEN
  SUBGOAL_THEN
    `PAIRWISE (\x y:A. ~(x = y)) p1 /\ ~(z = edge_map G z) /\
     (!x:A. MEM x p1 ==> x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z))`
    STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PAIRWISE_DISTINCT_CONS; MEM; ALL;
                                GSYM ALL_MEM; DE_MORGAN_THM]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DART_DOUBLE_WALKUP; IN_DELETE] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `~(p1:(A)list = [])` THEN
    LIST_CASES_TAC `p1:(A)list` `h:A` `t:(A)list` THEN
    REWRITE_TAC[NOT_CONS_NIL; list_cycle; list_path] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[list_path]) THEN
    SUBGOAL_THEN `LAST (CONS (edge_map G (z:A)) (CONS h t)) = LAST (CONS h t)`
      SUBST_ALL_TAC THENL [SIMP_TAC[LAST_CONS_NE; NOT_CONS_NIL]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `LAST (CONS (h:A) t)`]
        NODE_MAP_DOUBLE_WALKUP) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MEM_LAST; NOT_CONS_NIL]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LIST_PATH_DOUBLE_WALKUP THEN
      ASM_REWRITE_TAC[GSYM ALL_MEM]];
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM ALL_MEM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC QUASICUBIC_DOUBLE_WALKUP THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_SET_OF_LIST] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(MEM (x:A) (CONS z (CONS (edge_map G z) p1)))`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC
       `quasicubic G (set_of_list (CONS z (CONS (edge_map G (z:A)) p1)))` THEN
      REWRITE_TAC[quasicubic; IN_SET_OF_LIST] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`G:(A)hypermap`; `CONS z (CONS (edge_map G (z:A)) p1)`;
                     `x:A`] ORBIT_AVOIDS_RING) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[MEM]]]);;

(* ------------------------------------------------------------------------- *)
(* The chromogram transformations of the two cases.  Case A: the trace of G  *)
(* is e1 :: e1 :: et where et is a trace of H; the chromogram is             *)
(* Gskip :: Gskip :: w or Gpush :: Gpop0 :: w.  Case B: the trace of H is    *)
(* h1 :: h2 :: tail and that of G is (h1 + h2) :: tail; the chromogram of G  *)
(* is Gpush :: gram_neg w0, Gskip :: gram_flip w0 or Gskip :: w0 according   *)
(* to the first two symbols of the chromogram s1 :: s2 :: w0 of H.           *)
(* ------------------------------------------------------------------------- *)

let COLOR_COMPUTE =
  REWRITE_TAC[addc_DEF; cbit0; cbit1; ccons; distinctness "color"];;

let CASE_A_CHROMOGRAM = prove
 (`!e1 et w.
     ~(e1 = Color0) /\ matchg [] et w
     ==> ?w2. matchg [] (CONS e1 (CONS e1 et)) w2 /\
              !et'. matchg [] et' w2
                    ==> ?e2 et2. et' = CONS e2 (CONS e2 et2) /\
                                 ~(e2 = Color0) /\ matchg [] et2 w`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `e1 = Color1` THENL
   [EXISTS_TAC `CONS Gskip (CONS Gskip w)`;
    EXISTS_TAC `CONS Gpush (CONS Gpop0 w)`] THEN
  ASM_REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL] THEN
    X_GEN_TAC `et':color list` THEN
  LIST_CASES_TAC `et':color list` `e:color` `et1:color list` THEN
  LIST_CASES_TAC `et1:color list` `e':color` `et2:color list` THEN
  REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`Color1`; `et2:color list`] THEN
    ASM_REWRITE_TAC[distinctness "color"];
    SUBGOAL_THEN `e':color = e` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC CBIT0_COLOR23_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`e:color`; `et2:color list`] THEN
    ASM_REWRITE_TAC[]]);;

let COLOR_ASM_TAC =
  ASM_REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL; addc_DEF; cbit0; cbit1; ccons;
                  distinctness "color"];;

let CASE_B_CHROMOGRAM = prove
 (`!h1 h2 tail w.
     matchg [] (CONS h1 (CONS h2 tail)) w /\ ~(addc h1 h2 = Color0)
     ==> ?w'. matchg [] (CONS (addc h1 h2) tail) w' /\
              !et'. matchg [] et' w'
                    ==> ?e rest e0. et' = CONS e rest /\ ~(e = Color0) /\
                                    ~(e0 = Color0) /\
                                    matchg [] (CONS e0 (CONS (addc e0 e)
                                      rest)) w`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  LIST_CASES_TAC `w:gram_symbol list` `s1:gram_symbol`
    `w1:gram_symbol list` THEN
  LIST_CASES_TAC `w1:gram_symbol list` `s2:gram_symbol`
    `w0:gram_symbol list` THEN
  GRAM_CASES_TAC `s1:gram_symbol` THEN GRAM_CASES_TAC `s2:gram_symbol` THEN
  REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~(cbit0 h1 <=> cbit0 h2)` ASSUME_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `h1:color = h2` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC CBIT0_COLOR23_EQ THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `~(addc h2 h2 = Color0)` THEN REWRITE_TAC[ADDCC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `addc h1 h2 = Color1` SUBST1_TAC THENL
     [MATCH_MP_TAC ADDC_C23_EQ_C1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `CONS Gskip (gram_flip w0)` THEN
    REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL; MATCH_GRAM_FLIP] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `matchg [cbit0 h2; cbit0 h1] tail w0` THEN
      UNDISCH_TAC `~(cbit0 h1 <=> cbit0 h2)` THEN
      ASM_CASES_TAC `cbit0 h1` THEN ASM_CASES_TAC `cbit0 h2` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
      X_GEN_TAC `et':color list` THEN
      LIST_CASES_TAC `et':color list` `e:color` `rest:color list` THEN
      REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL; MATCH_GRAM_FLIP] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
       [MAP_EVERY EXISTS_TAC [`e:color`; `rest:color list`; `Color2`];
        MAP_EVERY EXISTS_TAC [`e:color`; `rest:color list`; `Color3`]] THEN
      COLOR_ASM_TAC];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPEC `h1:color` ADDC_COLOR1_23) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN EXISTS_TAC `CONS Gpush (gram_neg w0)` THEN
    REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL; MATCH_GRAM_NEG] THEN
    SUBGOAL_THEN `addc h1 Color1 = addc Color1 h1` SUBST1_TAC THENL
     [MATCH_ACCEPT_TAC ADDC_COMM; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `et':color list` THEN
    LIST_CASES_TAC `et':color list` `e:color` `rest:color list` THEN
    REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL; MATCH_GRAM_NEG] THEN
      STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`e:color`; `rest:color list`; `addc Color1 e`] THEN
    MP_TAC(SPEC `e:color` ADDC_COLOR1_23) THEN
    ASM_REWRITE_TAC[ADDC_CANCEL; MATCHG_CLAUSES; NOT_CONS_NIL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `h2:color = h1` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC CBIT0_COLOR23_EQ THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~(addc h1 h1 = Color0)` THEN REWRITE_TAC[ADDCC]];
    SUBGOAL_THEN `addc h1 h2 = Color1` SUBST1_TAC THENL
     [MATCH_MP_TAC ADDC_C23_EQ_C1 THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `CONS Gskip w0` THEN
    ASM_REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL] THEN
    X_GEN_TAC `et':color list` THEN
    LIST_CASES_TAC `et':color list` `e:color` `rest:color list` THEN
    REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`e:color`; `rest:color list`; `Color2`] THEN
    COLOR_ASM_TAC;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPEC `h2:color` ADDC_COLOR1_23) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN EXISTS_TAC `CONS Gpush (gram_neg w0)` THEN
    ASM_REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL; MATCH_GRAM_NEG] THEN
    X_GEN_TAC `et':color list` THEN
    LIST_CASES_TAC `et':color list` `e:color` `rest:color list` THEN
    REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL; MATCH_GRAM_NEG] THEN
      STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`e:color`; `rest:color list`; `Color1`] THEN
    MP_TAC(SPEC `e:color` ADDC_COLOR1_23) THEN
    ASM_REWRITE_TAC[MATCHG_CLAUSES; NOT_CONS_NIL; distinctness "color"] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    UNDISCH_TAC `~(addc Color1 Color1 = Color0)` THEN COLOR_COMPUTE]);;

let RING_B_FACTS = prove
 (`!(G:(A)hypermap) z nz p1.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     list_cycle (\x y. node_map G x = y) (CONS z (CONS nz p1)) /\
     ALL (\x. x IN dart G) (CONS z (CONS nz p1)) /\
     quasicubic G (set_of_list (CONS z (CONS nz p1))) /\
     ~MEM (face_map G z) (CONS z (CONS nz p1))
     ==> node_map G (face_map G z) = edge_map G z /\
         node_map G (node_map G (edge_map G z)) = face_map G z /\
         ~MEM (edge_map G z) (CONS z (CONS nz p1)) /\
         ~MEM (node_map G (edge_map G z)) (CONS z (CONS nz p1)) /\
         ~(node_map G (edge_map G z) = edge_map G z) /\
         ~(node_map G (edge_map G z) = face_map G z) /\
         ~(face_map G z = edge_map G z) /\
         (!x. x IN orbit_map (node_map G) (edge_map G z)
              ==> x = face_map G z \/ x = edge_map G z \/
                  x = node_map G (edge_map G z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`] PLAIN_Z_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `node_map G (node_map G (edge_map G z)) = face_map G (z:A)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `set_of_list (CONS z (CONS (nz:A) p1))`;
                   `face_map G (z:A)`] QUASICUBIC_EQ) THEN
    ASM_REWRITE_TAC[IN_SET_OF_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!x. x IN orbit_map (node_map G) (edge_map G z)
         ==> x = face_map G z \/ x = edge_map G z \/
             x = node_map G (edge_map G (z:A))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `edge_map G (z:A)`;
                   `node_map G (edge_map G (z:A))`; `face_map G (z:A)`]
      ORBIT_MAP_3CYCLE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map G z IN orbit_map (node_map G) (edge_map G (z:A))`
    ASSUME_TAC THENL
   [REWRITE_TAC[ORBIT_MAP_ITER] THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[num_CONV `2`; num_CONV `1`; ITER] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `~MEM (edge_map G z) (CONS z (CONS nz p1)) /\
     ~MEM (node_map G (edge_map G z)) (CONS z (CONS (nz:A) p1))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~MEM (face_map G z) (CONS z (CONS (nz:A) p1))` THEN
    REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`G:(A)hypermap`; `CONS z (CONS (nz:A) p1)`;
                     `edge_map G (z:A)`; `face_map G (z:A)`] RING_ORBIT) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`G:(A)hypermap`; `CONS z (CONS (nz:A) p1)`;
                     `node_map G (edge_map G (z:A))`; `face_map G (z:A)`]
        RING_ORBIT) THEN
      ASM_REWRITE_TAC[ORBIT_MAP_ITER] THEN DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC `1` THEN REWRITE_TAC[num_CONV `1`; ITER] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NODE_MAP_IN_DART]);;

let RING_CASE_B = prove
 (`!(G:(A)hypermap) z nz p1.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     list_cycle (\x y. node_map G x = y) (CONS z (CONS nz p1)) /\
     PAIRWISE (\x y. ~(x = y)) (CONS z (CONS nz p1)) /\
     ALL (\x. x IN dart G) (CONS z (CONS nz p1)) /\
     quasicubic G (set_of_list (CONS z (CONS nz p1))) /\
     ~MEM (face_map G z) (CONS z (CONS nz p1))
     ==> list_cycle
           (\x y. node_map (edge_walkup (node_walkup G z) (edge_map G z)) x =
             y)
           (CONS (node_map G (edge_map G z)) (CONS (face_map G z) (CONS nz
             p1))) /\
         PAIRWISE (\x y. ~(x = y))
           (CONS (node_map G (edge_map G z)) (CONS (face_map G z) (CONS nz
             p1))) /\
         ALL (\x. x IN dart (edge_walkup (node_walkup G z) (edge_map G z)))
           (CONS (node_map G (edge_map G z)) (CONS (face_map G z) (CONS nz
             p1))) /\
         quasicubic (edge_walkup (node_walkup G z) (edge_map G z))
           (set_of_list
             (CONS (node_map G (edge_map G z)) (CONS (face_map G z) (CONS nz
               p1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`] PLAIN_Z_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `nz:A`; `p1:(A)list`]
    RING_B_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_FACTS) THEN
  SUBGOAL_THEN
    `!x:A. MEM x (CONS nz p1)
           ==> x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z)`
    ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PAIRWISE_DISTINCT_CONS; MEM; ALL;
                                GSYM ALL_MEM; DE_MORGAN_THM]) THEN
    ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN
    `node_map G (edge_map G z) IN dart G /\ ~(node_map G (edge_map G z) = z) /\
     ~(face_map G (z:A) = z) /\
     ~MEM (node_map G (edge_map G z)) (CONS nz p1) /\
     ~MEM (face_map G z) (CONS nz p1) /\ PAIRWISE (\x y:A. ~(x = y)) (CONS nz
       p1)`
    STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PAIRWISE_DISTINCT_CONS; MEM;
                                DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[NODE_MAP_IN_DART; PAIRWISE_DISTINCT_CONS; MEM;
                 DE_MORGAN_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[DART_DOUBLE_WALKUP; IN_DELETE] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[list_cycle; NOT_CONS_NIL; list_path] THEN
    SIMP_TAC[LAST_CONS_NE; NOT_CONS_NIL] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `LAST (CONS (nz:A) p1)`]
        NODE_MAP_DOUBLE_WALKUP) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MEM_LAST; NOT_CONS_NIL]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `node_map G (edge_map G (z:A))`]
        NODE_MAP_DOUBLE_WALKUP) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `face_map G (z:A)`]
        NODE_MAP_DOUBLE_WALKUP) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LIST_PATH_DOUBLE_WALKUP THEN
      ASM_REWRITE_TAC[GSYM ALL_MEM]];
    RULE_ASSUM_TAC(REWRITE_RULE[PAIRWISE_DISTINCT_CONS; MEM;
                                DE_MORGAN_THM]) THEN
    REWRITE_TAC[PAIRWISE_DISTINCT_CONS; MEM; DE_MORGAN_THM] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; GSYM CONJ_ASSOC] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[MEM] THEN STRIP_TAC THEN ASM_SIMP_TAC[MEM];
    MATCH_MP_TAC QUASICUBIC_DOUBLE_WALKUP THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_SET_OF_LIST; MEM; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(MEM (x:A) (CONS z (CONS nz p1)))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `quasicubic G (set_of_list (CONS z (CONS (nz:A) p1)))` THEN
      REWRITE_TAC[quasicubic; IN_SET_OF_LIST] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN CONJ_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THENL
       [MP_TAC(ISPECL [`G:(A)hypermap`; `CONS z (CONS (nz:A) p1)`; `x:A`]
          ORBIT_AVOIDS_RING) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
        ASM_REWRITE_TAC[MEM];
        MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `dart (G:(A)hypermap)`;
                       `x:A`; `edge_map G (z:A)`] ORBIT_MAP_EQ) THEN
        ASM_REWRITE_TAC[NODE_MAP_PERMUTES; FINITE_DART] THEN DISCH_TAC THEN
        SUBGOAL_THEN `x IN orbit_map (node_map G) (edge_map G (z:A))`
          MP_TAC THENL [ASM_REWRITE_TAC[IN_ORBIT_MAP_REFL]; ALL_TAC] THEN
        UNDISCH_TAC
          `!x. x IN orbit_map (node_map G) (edge_map G z)
               ==> x = face_map G z \/ x = edge_map G z \/
                   x = node_map G (edge_map G (z:A))` THEN
        DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* Traces of a lifted colouring (k0 agrees with k1 away from z and edge z).  *)
(* ------------------------------------------------------------------------- *)

let LIFT_TRACE_A = prove
 (`!(k0:A->color) k1 z ez p1 e2.
     k0 z = addc e2 (k1 (LAST (CONS ez p1))) /\
     k0 ez = k1 (LAST (CONS ez p1)) /\
     (!x. MEM x p1 ==> k0 x = k1 x)
     ==> trace_col (MAP k0 (CONS z (CONS ez p1))) =
         CONS e2 (CONS e2 (trace_col (MAP k1 p1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MAP (k0:A->color) p1 = MAP k1 p1` ASSUME_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC[GSYM ALL_MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `(k0:A->color) (LAST (CONS ez p1)) = k0 ez` ASSUME_TAC THENL
   [LIST_CASES_TAC `p1:(A)list` `h:A` `t:(A)list` THENL
     [REWRITE_TAC[LAST];
      RULE_ASSUM_TAC(SIMP_RULE[LAST_CONS_NE; NOT_CONS_NIL]) THEN
      SIMP_TAC[LAST_CONS_NE; NOT_CONS_NIL] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC MEM_LAST THEN
      REWRITE_TAC[NOT_CONS_NIL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k0:A->color`; `z:A`; `ez:A`; `p1:(A)list`]
    TRACE_COL_RING_A) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[ADDC_CANCEL]);;

let LIFT_TRACE_B = prove
 (`!(k0:A->color) k1 z nz p1 cz.
     k0 z = cz /\ (!x. MEM x (CONS nz p1) ==> k0 x = k1 x)
     ==> trace_col (MAP k0 (CONS z (CONS nz p1))) =
         CONS (addc (k1 (LAST (CONS nz p1))) cz)
              (CONS (addc cz (k1 nz)) (ptrace (CONS (k1 nz) (MAP k1 p1))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TRACE_COL_RING] THEN
  SUBGOAL_THEN
    `MAP (k0:A->color) p1 = MAP k1 p1 /\ k0 nz = k1 nz /\
     k0 (LAST (CONS nz p1)) = k1 (LAST (CONS nz p1))`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEM; MEM_LAST; NOT_CONS_NIL] THEN MATCH_MP_TAC MAP_EQ THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[MEM];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The two cases of the induction step: the Kempe property of the ring of H  *)
(* yields the Kempe property of the ring z :: nz :: p1 of G.                 *)
(* ------------------------------------------------------------------------- *)

let KEMPE_CASE_A = prove
 (`!(G:(A)hypermap) z p1.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     face_map G z = z /\
     (!x. MEM x p1 ==> x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z)) /\
     node_map G (LAST (CONS (edge_map G z) p1)) = z /\
     (!et. ring_trace (edge_walkup (node_walkup G z) (edge_map G z)) p1 et
           ==> ?w. matchg [] et w /\
                   !et'. matchg [] et' w
                         ==> ring_trace (edge_walkup (node_walkup G z)
                                                     (edge_map G z)) p1 et')
     ==> !et. ring_trace G (CONS z (CONS (edge_map G z) p1)) et
              ==> ?w. matchg [] et w /\
                      !et'. matchg [] et' w
                            ==> ring_trace G (CONS z (CONS (edge_map G z) p1))
                                           et'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`] PLAIN_Z_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `face_map G (edge_map G z) = LAST (CONS (edge_map G (z:A)) p1)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `face_map G (edge_map G (z:A))`;
                   `LAST (CONS (edge_map G (z:A)) p1)`] NODEI) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `et:color list` THEN REWRITE_TAC[ring_trace] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->color`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  SUBGOAL_THEN
    `coloring (edge_walkup (node_walkup G z) (edge_map G (z:A))) k`
    ASSUME_TAC THENL
   [MATCH_MP_TAC COLORING_DOUBLE_WALKUP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(k:A->color) (LAST (CONS (edge_map G z) p1)) = k (edge_map G z) /\
     ~(addc (k z) (k (edge_map G z)) = Color0)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `coloring G (k:A->color)` THEN
    REWRITE_TAC[coloring; ADDC_EQ_0] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A->color`; `z:A`; `edge_map G (z:A)`; `p1:(A)list`]
    TRACE_COL_RING_A) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `trace_col (MAP (k:A->color) p1)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ring_trace] THEN EXISTS_TAC `k:A->color` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:gram_symbol list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`addc ((k:A->color) z) (k (edge_map G z))`;
                 `trace_col (MAP (k:A->color) p1)`; `w:gram_symbol list`]
    CASE_A_CHROMOGRAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:gram_symbol list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w2:gram_symbol list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `et':color list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `et':color list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:color` (X_CHOOSE_THEN `et2:color list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[ring_trace] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:A->color`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  EXISTS_TAC
    `\x:A. if x = z then addc e2 (k1 (LAST (CONS (edge_map G z) p1)))
           else if x = edge_map G z then k1 (LAST (CONS (edge_map G z) p1))
           else k1 x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COLORING_DOUBLE_WALKUP_LIFT THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM
      `\u. addc u ((k1:A->color) (LAST (CONS (edge_map G z) p1)))`) THEN
    REWRITE_TAC[ADDC_CANCEL; ADDCC] THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LIFT_TRACE_A THEN REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;

let KEMPE_CASE_B = prove
 (`!(G:(A)hypermap) z nz p1.
     plain_hypermap G /\ z IN dart G /\
     (!y. y IN dart G ==> ~(node_map G y = y)) /\
     node_map G z = nz /\ node_map G (LAST (CONS nz p1)) = z /\
     node_map G (face_map G z) = edge_map G z /\
     node_map G (node_map G (edge_map G z)) = face_map G z /\
     (!x. MEM x (CONS nz p1)
          ==> x IN dart G /\ ~(x = z) /\ ~(x = edge_map G z)) /\
     ~(face_map G z = z) /\
     (!et. ring_trace (edge_walkup (node_walkup G z) (edge_map G z))
             (CONS (node_map G (edge_map G z)) (CONS (face_map G z) (CONS nz
               p1)))
             et
           ==> ?w. matchg [] et w /\
                   !et'. matchg [] et' w
                         ==> ring_trace (edge_walkup (node_walkup G z)
                                                     (edge_map G z))
                               (CONS (node_map G (edge_map G z))
                                     (CONS (face_map G z) (CONS nz p1))) et')
     ==> !et. ring_trace G (CONS z (CONS nz p1)) et
              ==> ?w. matchg [] et w /\
                      !et'. matchg [] et' w
                            ==> ring_trace G (CONS z (CONS nz p1)) et'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`] PLAIN_Z_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `face_map G (edge_map G z) = LAST (CONS (nz:A) p1)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:(A)hypermap`; `face_map G (edge_map G (z:A))`;
                   `LAST (CONS (nz:A) p1)`] NODEI) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LAST (CONS (nz:A) p1) IN dart G /\ ~(LAST (CONS nz p1) = z) /\
                ~(LAST (CONS nz p1) = edge_map G z)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_LAST; NOT_CONS_NIL]; ALL_TAC] THEN
  X_GEN_TAC `et:color list` THEN REWRITE_TAC[ring_trace] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->color`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  SUBGOAL_THEN
    `coloring (edge_walkup (node_walkup G z) (edge_map G (z:A))) k`
    ASSUME_TAC THENL
   [MATCH_MP_TAC COLORING_DOUBLE_WALKUP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(k:A->color) (face_map G z) = k z /\
     ~(addc (k (LAST (CONS nz p1))) (k z) = Color0)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ADDC_EQ_0] THEN CONJ_TAC THENL
     [UNDISCH_TAC `coloring G (k:A->color)` THEN REWRITE_TAC[coloring] THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`G:(A)hypermap`; `k:A->color`; `LAST (CONS (nz:A) p1)`]
        COLORING_NODE_NEQ) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[TRACE_COL_RING] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `trace_col (MAP (k:A->color)
       (CONS (node_map G (edge_map G z)) (CONS (face_map G z) (CONS nz
         p1))))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ring_trace] THEN EXISTS_TAC `k:A->color` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TRACE_COL_RING_H] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `wH:gram_symbol list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
    [`addc ((k:A->color) (LAST (CONS nz p1))) (k (node_map G (edge_map G z)))`;
     `addc ((k:A->color) (node_map G (edge_map G z))) (k z)`;
     `CONS (addc ((k:A->color) z) (k nz)) (ptrace (CONS (k nz) (MAP k p1)))`;
     `wH:gram_symbol list`] CASE_B_CHROMOGRAM) THEN
  ASM_REWRITE_TAC[ADDC_CANCEL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':gram_symbol list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w':gram_symbol list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `et':color list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `et':color list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:color` (X_CHOOSE_THEN `rest:color list`
    (X_CHOOSE_THEN `e0:color` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[ring_trace; TRACE_COL_RING_H] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:A->color`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[CONS_11] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `addc (e0:color)`) THEN
  REWRITE_TAC[ADDC_CANCEL] THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `e0:color`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADDC_CANCEL]) THEN REWRITE_TAC[ADDC_CANCEL] THEN
  SUBGOAL_THEN `~((k1:A->color) (face_map G z) = k1 (LAST (CONS nz p1)))`
    ASSUME_TAC THENL
   [UNDISCH_TAC
      `~(addc ((k1:A->color) (LAST (CONS nz p1))) (k1 (face_map G z)) =
         Color0)` THEN
    REWRITE_TAC[ADDC_EQ_0] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ring_trace] THEN
  EXISTS_TAC
    `\x:A. if x = z then (k1:A->color) (face_map G z)
           else if x = edge_map G z then k1 (LAST (CONS nz p1)) else k1 x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COLORING_DOUBLE_WALKUP_LIFT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL
     [`\x:A. if x = z then (k1:A->color) (face_map G z)
             else if x = edge_map G z then k1 (LAST (CONS nz p1)) else k1 x`;
      `k1:A->color`; `z:A`; `nz:A`; `p1:(A)list`;
      `(k1:A->color) (face_map G z)`] LIFT_TRACE_B) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      REWRITE_TAC[TRACE_COL_RING; CONS_11] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The induction step: a ring z :: nz :: p1 of G starting at a leaf z, and   *)
(* the induction hypothesis for all smaller maps. *)
(* ------------------------------------------------------------------------- *)

let KEMPE_STEP = prove
 (`!(G:(A)hypermap) z nz p1 k.
     plain_hypermap G /\ planar_hypermap G /\ coloring G k /\
     list_cycle (\x y. node_map G x = y) (CONS z (CONS nz p1)) /\
     PAIRWISE (\x y. ~(x = y)) (CONS z (CONS nz p1)) /\
     ALL (\x. x IN dart G) (CONS z (CONS nz p1)) /\
     quasicubic G (set_of_list (CONS z (CONS nz p1))) /\
     (face_map G z = z \/ ~MEM (face_map G z) (CONS z (CONS nz p1))) /\
     (!(G':(A)hypermap) r'.
        CARD(dart G') < CARD(dart G) /\
        ucycle_planar_plain_quasicubic G' r' /\ ALL (\x. x IN dart G') r'
        ==> kempe_closed (ring_trace G' r'))
     ==> !et. ring_trace G (CONS z (CONS nz p1)) et
              ==> ?w. matchg [] et w /\
                      !et'. matchg [] et' w
                            ==> ring_trace G (CONS z (CONS nz p1)) et'`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `!y:A. y IN dart G ==> ~(node_map G y = y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLORING_NO_NODE_FP]; ALL_TAC] THEN
  SUBGOAL_THEN `z:A IN dart G` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`] PLAIN_Z_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_FACTS) THEN
  SUBGOAL_THEN
    `plain_hypermap (edge_walkup (node_walkup G z) (edge_map G (z:A))) /\
     planar_hypermap (edge_walkup (node_walkup G z) (edge_map G z)) /\
     CARD(dart(edge_walkup (node_walkup G z) (edge_map G z))) < CARD(dart G) /\
     coloring (edge_walkup (node_walkup G z) (edge_map G z)) k`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PLAIN_DOUBLE_WALKUP; PLANAR_DOUBLE_WALKUP;
                 CARD_DOUBLE_WALKUP; COLORING_DOUBLE_WALKUP];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!s. list_cycle
           (\x y. node_map (edge_walkup (node_walkup G z) (edge_map G z)) x =
             y)
           s /\
         PAIRWISE (\x y. ~(x = y)) s /\
         ALL (\x. x IN dart (edge_walkup (node_walkup G z) (edge_map G z))) s
           /\
         quasicubic (edge_walkup (node_walkup G z) (edge_map G z))
                    (set_of_list s)
         ==> !et. ring_trace (edge_walkup (node_walkup G z) (edge_map G z)) s
           et
                  ==> ?w. matchg [] et w /\
                          !et'. matchg [] et' w
                                ==> ring_trace (edge_walkup (node_walkup G z)
                                                            (edge_map G (z:A)))
                                               s et'`
    (LABEL_TAC "ih") THENL
   [X_GEN_TAC `s:(A)list` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`edge_walkup (node_walkup G z) (edge_map G (z:A))`; `s:(A)list`]) THEN
    ASM_REWRITE_TAC[ucycle_planar_plain_quasicubic; ucycle_plain_quasicubic;
                    plain_quasicubic; kempe_closed] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN `nz:A = edge_map G z` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC KEMPE_CASE_A THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[PAIRWISE_DISTINCT_CONS; MEM; ALL;
                                  GSYM ALL_MEM; DE_MORGAN_THM]) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `p1:(A)list = []` THENL
     [ASM_REWRITE_TAC[ring_trace; MAP; trace_DEF] THEN
      X_GEN_TAC `et:color list` THEN STRIP_TAC THEN
      EXISTS_TAC `[]:gram_symbol list` THEN
      ASM_REWRITE_TAC[MATCHG_CLAUSES] THEN ASM_MESON_TAC[];
      REMOVE_THEN "ih" MATCH_MP_TAC THEN MATCH_MP_TAC RING_CASE_A THEN
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `nz:A`; `p1:(A)list`]
      RING_B_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC KEMPE_CASE_B THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[PAIRWISE_DISTINCT_CONS; MEM; ALL;
                                  GSYM ALL_MEM; DE_MORGAN_THM]) THEN
      ASM_MESON_TAC[MEM];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~MEM (face_map G z) (CONS z (CONS (nz:A) p1))` THEN
      REWRITE_TAC[MEM] THEN MESON_TAC[];
      REMOVE_THEN "ih" MATCH_MP_TAC THEN MATCH_MP_TAC RING_CASE_B THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let KEMPE_MAP_NONEMPTY = prove
 (`!(G:(A)hypermap) r.
     ucycle_planar_plain_quasicubic G r /\ ALL (\x. x IN dart G) r /\
     ~(r = []) /\
     (!(G':(A)hypermap) r'.
        CARD(dart G') < CARD(dart G) /\
        ucycle_planar_plain_quasicubic G' r' /\ ALL (\x. x IN dart G') r'
        ==> kempe_closed (ring_trace G' r'))
     ==> !et. ring_trace G r et
              ==> ?w. matchg [] et w /\
                      !et'. matchg [] et' w ==> ring_trace G r et'`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  UNDISCH_TAC `ucycle_planar_plain_quasicubic G (r:(A)list)` THEN
  REWRITE_TAC[ucycle_planar_plain_quasicubic; ucycle_plain_quasicubic;
              plain_quasicubic] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `r:(A)list`] KEMPE_LEAF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:(A)list` (X_CHOOSE_THEN `l2:(A)list`
    SUBST_ALL_TAC) o MATCH_MP MEM_SPLIT) THEN
  ABBREV_TAC `p = APPEND (l2:(A)list) l1` THEN
  SUBGOAL_THEN
    `ITER (LENGTH (l1:(A)list)) rot1 (APPEND l1 (CONS z l2)) = CONS (z:A) p /\
     ITER (LENGTH (CONS (z:A) l2)) rot1 (CONS z p) = APPEND l1 (CONS z l2)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    REWRITE_TAC[GSYM(CONJUNCT2 APPEND); ITER_ROT1_APPEND];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`LENGTH (l1:(A)list)`; `\x y:A. node_map G x = y`;
                 `\x:A. x IN dart G`; `APPEND l1 (CONS (z:A) l2)`]
    ITER_ROT1_INVARIANTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `quasicubic G (set_of_list (CONS (z:A) p)) /\
     (face_map G z = z \/ ~MEM (face_map G z) (CONS z p))`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_SET_OF_LIST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `CONS (z:A) p`; `LENGTH (CONS (z:A) l2)`]
    CHROMOGRAM_ROT_ITER) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `et:color list` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:A->color` STRIP_ASSUME_TAC o
              REWRITE_RULE[ring_trace]) THEN
  SUBGOAL_THEN `?nz p1. p = CONS (nz:A) p1`
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THENL
   [LIST_CASES_TAC `p:(A)list` `nz:A` `p1:(A)list` THENL
     [MP_TAC(ISPECL [`node_map (G:(A)hypermap)`; `z:A`; `[]:(A)list`]
        LIST_CYCLE_HD) THEN
      ASM_REWRITE_TAC[LAST] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
      ASM_MESON_TAC[COLORING_NO_NODE_FP];
      MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:(A)hypermap`; `z:A`; `nz:A`; `p1:(A)list`; `k:A->color`]
    KEMPE_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[ring_trace] THEN EXISTS_TAC `k:A->color` THEN
  ASM_REWRITE_TAC[]);;

let KEMPE_MAP = prove
 (`!(H:(A)hypermap) r.
    ucycle_planar_plain_quasicubic H r /\ ALL (\x. x IN dart H) r
    ==> kempe_closed (ring_trace H r)`,
  SUBGOAL_THEN
    `!n. !(G:(A)hypermap) r.
       CARD(dart G) = n /\ ucycle_planar_plain_quasicubic G r /\
       ALL (\x. x IN dart G) r
       ==> kempe_closed (ring_trace G r)`
    (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_MESON_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`G:(A)hypermap`; `r:(A)list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[kempe_closed] THEN X_GEN_TAC `et:color list` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RING_TRACE_PERMT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `r:(A)list = []` THENL
   [UNDISCH_TAC `ring_trace (G:(A)hypermap) r et` THEN
    ASM_REWRITE_TAC[ring_trace; MAP; trace_DEF] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:A->color`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    EXISTS_TAC `[]:gram_symbol list` THEN REWRITE_TAC[MATCHG_CLAUSES] THEN
    X_GEN_TAC `et':color list` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ring_trace] THEN EXISTS_TAC `k:A->color` THEN
    ASM_REWRITE_TAC[MAP; trace_DEF];
    MP_TAC(ISPECL [`G:(A)hypermap`; `r:(A)list`] KEMPE_MAP_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `CARD(dart(G':(A)hypermap))`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;
