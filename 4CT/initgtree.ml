(* ========================================================================= *)
(* 4CT/initgtree.ml                                                          *)
(*                                                                           *)
(* initgtree.v: the initial (full) chromogram tree gtree_init_tree h storing *)
(* exactly the balanced partial chromograms of ring size h (built by dynamic *)
(* programming from a table of gtree_pairs per height), its correctness      *)
(* theorem GTREE_MEM_INIT_TREE, and MATCH_COUNT_BALANCED: the number of such *)
(* chromograms matching a trace is the Dyck number of its high-bit count.    *)
(* Both proofs go through bal_spec h d b w, the partial chromograms w of     *)
(* length h whose completion from context (d,b) is balanced; the Dyck count  *)
(* is proved for a general context, the closing colour being ccons (ODD d)   *)
(* (~(b <=> sumb lb)) for the bit list lb of the matching stack.             *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/color.ml";;
needs "4CT/chromogram.ml";;
needs "4CT/gtree.ml";;
needs "4CT/dyck.ml";;
needs "4CT/initctree.ml";;

(* ------------------------------------------------------------------------- *)
(* The specification and the table construction (Coq definitions).           *)
(* ------------------------------------------------------------------------- *)

let init_gtree_spec = new_definition
 `init_gtree_spec h w <=> (LENGTH w = h) /\ gram_balanced 0 F (cgram 0 F w)`;;

let init_gtree_h1 = new_definition
 `init_gtree_h1 =
    [GtreePair GtreeLeaf01 GtreeLeaf0;
     GtreePair GtreeLeaf13 GtreeLeaf12;
     GtreePair GtreeLeaf23 GtreeLeaf23]`;;

let gtree_merge_pairs = define
 `gtree_merge_pairs (GtreePair t0 t0') (GtreePair t1 t1') (GtreePair t2 t3) =
    GtreePair (GtreeNode t0 t1' t2 t3) (GtreeNode t0' t1 t3 t2)`;;

let gtree_table_sub = new_recursive_definition list_RECURSION
 `(gtree_table_sub [] n = (\b. GtreeEmpty)) /\
  (gtree_table_sub (CONS pt tab') n =
     (\b. if n = 0 then gtree_pair_sub pt b
     else gtree_table_sub tab' (n - 1) b))`;;

let gtree_merge_line_fn = new_recursive_definition num_RECURSION
 `(gtree_merge_line_fn 0 = (\pt0 pt1 pt2 lpt. [gtree_merge_pairs pt0 pt1 pt2]))
  /\
  (gtree_merge_line_fn (SUC d) =
     (\pt0 pt1 pt2 lpt.
        CONS (gtree_merge_pairs pt0 pt1 pt2)
          (if lpt = [] then
             [gtree_merge_pairs empty_gtree_pair pt0 pt1;
              gtree_merge_pairs empty_gtree_pair empty_gtree_pair pt0]
           else
             gtree_merge_line_fn d (HD lpt) pt0 pt1 (TL lpt))))`;;

let gtree_merge_line = new_definition
 `gtree_merge_line pt0 pt1 pt2 lpt d = gtree_merge_line_fn d pt0 pt1 pt2 lpt`;;

let gtree_init_table_fn = new_recursive_definition num_RECURSION
 `(gtree_init_table_fn 0 = (\d. init_gtree_h1)) /\
  (gtree_init_table_fn (SUC h'') =
     (\d. let tab = gtree_init_table_fn h'' (SUC d) in
          if LENGTH tab < 2 then tab
          else gtree_merge_line (HD(TL tab)) (HD tab) empty_gtree_pair
          (TL(TL tab)) d))`;;

let gtree_init_table = new_definition
 `gtree_init_table d h' = gtree_init_table_fn h' d`;;

let gtree_init_tree = new_definition
 `gtree_init_tree h =
    (if h = 0 then GtreeEmpty
     else let tab = gtree_init_table 0 (h - 1) in
          if tab = [] then GtreeEmpty
          else gtree_pair_sub (HD tab) F)`;;

(* ------------------------------------------------------------------------- *)
(* bal_spec h d b w: w has length h and its completion from the context of   *)
(* d open chords and parity b is balanced; its recursion along w.            *)
(* ------------------------------------------------------------------------- *)

let bal_spec = new_definition
 `bal_spec h d b w <=> LENGTH w = h /\ gram_balanced d b (cgram d b w)`;;

let BAL_SPEC_NIL = prove
 (`!h d b. bal_spec h d b [] <=> h = 0 /\ (if d = 0 then b else d = 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bal_spec; LENGTH; cgram] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[gram_balanced; distinctness "gram_symbol"] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[gram_balanced; distinctness "gram_symbol"] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let BAL_SPEC_CONS = prove
 (`(!d b s w. bal_spec 0 d b (CONS s w) <=> F) /\
   (!h d b w. bal_spec (SUC h) d b (CONS Gpush w) <=>
              bal_spec h (SUC d) b w) /\
   (!h d b w. bal_spec (SUC h) d b (CONS Gskip w) <=> bal_spec h d (~b) w) /\
   (!h d b w. bal_spec (SUC h) d b (CONS Gpop0 w) <=>
              ~(d = 0) /\ bal_spec h (d - 1) b w) /\
   (!h d b w. bal_spec (SUC h) d b (CONS Gpop1 w) <=>
              ~(d = 0) /\ bal_spec h (d - 1) (~b) w)`,
  REWRITE_TAC[bal_spec; LENGTH; NOT_SUC; SUC_INJ; cgram; gram_balanced;
              distinctness "gram_symbol"; GSYM ADD1; CONJ_ACI]);;

let BAL_SPEC_0 = prove
 (`!d b w. bal_spec 0 d b w <=> w = [] /\ (if d = 0 then b else d = 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` list_CASES) THEN
  REWRITE_TAC[BAL_SPEC_NIL; BAL_SPEC_CONS; NOT_CONS_NIL]);;

let BAL_SPEC_FUN = prove
 (`(!h d b. (\w. bal_spec (SUC h) d b (CONS Gpush w)) =
            bal_spec h (SUC d) b) /\
   (!h d b. (\w. bal_spec (SUC h) d b (CONS Gskip w)) = bal_spec h d (~b)) /\
   (!h d b. (\w. bal_spec (SUC h) (SUC d) b (CONS Gpop0 w)) =
            bal_spec h d b) /\
   (!h d b. (\w. bal_spec (SUC h) (SUC d) b (CONS Gpop1 w)) =
            bal_spec h d (~b))`,
  REWRITE_TAC[FUN_EQ_THM; BAL_SPEC_CONS; NOT_SUC; SUC_SUB1]);;

let INIT_GTREE_SPEC_BAL = prove
 (`!h. init_gtree_spec h = bal_spec h 0 F`,
  REWRITE_TAC[FUN_EQ_THM; init_gtree_spec; bal_spec]);;

(* ------------------------------------------------------------------------- *)
(* Table plumbing: table_sub, merge_line, and the lengths of the tables.     *)
(* ------------------------------------------------------------------------- *)

let GTSUB_CLAUSES = prove
 (`(!n b. gtree_table_sub [] n b = GtreeEmpty) /\
   (!pt tab b. gtree_table_sub (CONS pt tab) 0 b = gtree_pair_sub pt b) /\
   (!pt tab n b. gtree_table_sub (CONS pt tab) (SUC n) b =
                 gtree_table_sub tab n b)`,
  REWRITE_TAC[gtree_table_sub; NOT_SUC; SUC_SUB1]);;

let GTREE_MERGE_LINE_CLAUSES = prove
 (`(!pt0 pt1 pt2 lpt. gtree_merge_line pt0 pt1 pt2 lpt 0 =
                      [gtree_merge_pairs pt0 pt1 pt2]) /\
   (!pt0 pt1 pt2 d. gtree_merge_line pt0 pt1 pt2 [] (SUC d) =
      [gtree_merge_pairs pt0 pt1 pt2;
       gtree_merge_pairs empty_gtree_pair pt0 pt1;
       gtree_merge_pairs empty_gtree_pair empty_gtree_pair pt0]) /\
   (!pt0 pt1 pt2 pt lpt d.
      gtree_merge_line pt0 pt1 pt2 (CONS pt lpt) (SUC d) =
      CONS (gtree_merge_pairs pt0 pt1 pt2)
           (gtree_merge_line pt pt0 pt1 lpt d))`,
  REWRITE_TAC[gtree_merge_line; gtree_merge_line_fn; NOT_CONS_NIL; HD; TL]);;

let LENGTH_GTREE_MERGE_LINE = prove
 (`!d pt0 pt1 pt2 lpt.
     0 < LENGTH(gtree_merge_line pt0 pt1 pt2 lpt d) /\
     (0 < d ==> 2 <= LENGTH(gtree_merge_line pt0 pt1 pt2 lpt d))`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `lpt:gtree_pair list` list_CASES) THEN
  REWRITE_TAC[GTREE_MERGE_LINE_CLAUSES; LENGTH] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPECL
    [`h:gtree_pair`; `pt0:gtree_pair`; `pt1:gtree_pair`;
     `t:gtree_pair list`])) THEN
  ARITH_TAC);;

let LENGTH_GTREE_INIT_TABLE = prove
 (`!h d. 0 < LENGTH(gtree_init_table d h) /\
         (0 < d ==> 2 <= LENGTH(gtree_init_table d h))`,
  INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[gtree_init_table; gtree_init_table_fn] THENL
   [REWRITE_TAC[init_gtree_h1; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; GSYM gtree_init_table] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC d`) THEN REWRITE_TAC[LT_0] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH_GTREE_MERGE_LINE]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the table: the height-1 table, the merge line (membership  *)
(* -wise a node of the entries of the line below), and the table invariant.  *)
(* ------------------------------------------------------------------------- *)

let NUM_CASES_3 = prove
 (`!n. n = 0 \/ n = SUC 0 \/ n = SUC(SUC 0) \/ ?m. n = SUC(SUC(SUC m))`,
  INDUCT_TAC THEN ASM_MESON_TAC[]);;

let GTSUB_INIT_H1 = prove
 (`!dw bw w. gtree_mem (gtree_table_sub init_gtree_h1 dw bw) w <=>
             bal_spec (SUC 0) dw bw w`,
  REPEAT GEN_TAC THEN STRIP_ASSUME_TAC(SPEC `dw:num` NUM_CASES_3) THEN
  ASM_REWRITE_TAC[init_gtree_h1; gtree_table_sub; gtree_pair_sub; NOT_SUC;
                  SUC_SUB1] THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` list_CASES) THEN
  REWRITE_TAC[CONJUNCT1 GTREE_MEM; BAL_SPEC_NIL; NOT_SUC] THEN
  STRUCT_CASES_TAC(ISPEC `h:gram_symbol` (cases "gram_symbol")) THEN
  BOOL_CASES_TAC `bw:bool` THEN
  REWRITE_TAC[gtree_mem; BAL_SPEC_CONS; BAL_SPEC_0; distinctness "gram_symbol";
              NOT_SUC; SUC_SUB1; ONE; SUC_INJ]);;

let GTSUB_MERGE_LINE = prove
 (`!dw d pt0 pt1 pt2 lpt bw w.
     dw <= d
     ==> (gtree_mem
           (gtree_table_sub (gtree_merge_line pt0 pt1 pt2 lpt d) dw bw) w <=>
          gtree_mem
           (GtreeNode
             (gtree_table_sub (CONS pt2 (CONS pt1 (CONS pt0 lpt)))
                              (SUC(SUC dw)) bw)
             (gtree_table_sub (CONS pt2 (CONS pt1 (CONS pt0 lpt)))
                              (SUC dw) (~bw))
             (gtree_table_sub (CONS pt2 (CONS pt1 (CONS pt0 lpt))) dw bw)
             (gtree_table_sub (CONS pt2 (CONS pt1 (CONS pt0 lpt))) dw (~bw)))
           w)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `d:num` num_CASES) THEN
  REWRITE_TAC[LE_0; LE_SUC; LE; NOT_SUC] THEN TRY DISCH_TAC THEN
  STRUCT_CASES_TAC(ISPEC `lpt:gtree_pair list` list_CASES) THEN
  ASM_SIMP_TAC[GTREE_MERGE_LINE_CLAUSES; GTSUB_CLAUSES] THEN
  MAP_EVERY (fun v -> STRUCT_CASES_TAC(ISPEC v (cases "gtree_pair")))
    [`pt0:gtree_pair`; `pt1:gtree_pair`; `pt2:gtree_pair`] THEN
  STRIP_ASSUME_TAC(SPEC `dw:num` NUM_CASES_3) THEN
  ASM_REWRITE_TAC[GTSUB_CLAUSES; gtree_merge_pairs; empty_gtree_pair;
                  gtree_pair_sub] THEN
  BOOL_CASES_TAC `bw:bool` THEN REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` list_CASES) THEN
  REWRITE_TAC[gtree_mem; gtree_sel; COND_ID; GTREE_MEM_EMPTY]);;

let GTSUB_INIT_TABLE = prove
 (`!h d dw bw w.
     dw <= d
     ==> (gtree_mem (gtree_table_sub (gtree_init_table d h) dw bw) w <=>
          bal_spec (SUC h) dw bw w)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[gtree_init_table; gtree_init_table_fn] THENL
   [REWRITE_TAC[GSYM init_gtree_h1; GTSUB_INIT_H1]; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; GSYM gtree_init_table] THEN
  MP_TAC(SPECL [`h:num`; `SUC d`] LENGTH_GTREE_INIT_TABLE) THEN
  REWRITE_TAC[LT_0] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n < 2)`; GTSUB_MERGE_LINE;
               LIST_HD2_TL2] THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` list_CASES) THEN
  REWRITE_TAC[CONJUNCT1 GTREE_MEM; BAL_SPEC_NIL; NOT_SUC] THEN
  STRUCT_CASES_TAC(ISPEC `h':gram_symbol` (cases "gram_symbol")) THEN
  REWRITE_TAC[gtree_mem; gtree_sel; distinctness "gram_symbol";
              BAL_SPEC_CONS; GTSUB_CLAUSES] THEN
  TRY(DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC)
        (SPEC `dw:num` num_CASES)) THEN
  ASM_SIMP_TAC[GTSUB_CLAUSES; gtree_pair_sub; empty_gtree_pair; COND_ID;
               GTREE_MEM_EMPTY; NOT_SUC; SUC_SUB1; LE_SUC; LE_0;
               ARITH_RULE `SUC k <= d ==> k <= SUC d /\ k <= d`;
               ARITH_RULE `dw <= d ==> dw <= SUC d`]);;

let GTREE_MEM_INIT_TREE = prove
 (`!h w. gtree_mem (gtree_init_tree h) w = init_gtree_spec h w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gtree_init_tree; INIT_GTREE_SPEC_BAL] THEN
  STRUCT_CASES_TAC(SPEC `h:num` num_CASES) THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF; GTREE_MEM_EMPTY] THENL
   [REWRITE_TAC[BAL_SPEC_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `0`; `0`; `F`; `w:gram_symbol list`]
    GTSUB_INIT_TABLE) THEN
  MP_TAC(SPECL [`n:num`; `0`] LENGTH_GTREE_INIT_TABLE) THEN
  SPEC_TAC(`gtree_init_table 0 n`,`tab:gtree_pair list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; LT_REFL; NOT_CONS_NIL; HD; GTSUB_CLAUSES; LE_REFL] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Dyck count.  In the context of the stack of the bit list lb with      *)
(* parity b0 the closing colour is ccons (ODD (LENGTH lb)) (~(b0 <=> sumb    *)
(* lb)) and the count of the balanced chromograms matching et is             *)
(* gen_dyck (LENGTH lb + 1) of the high-bit count of the closed trace.       *)
(* ------------------------------------------------------------------------- *)

let CASE_BITSTACK_CONST = prove
 (`!bs (v:A). case_bitstack bs v (\bs'. v) (\bs'. v) = v`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `bs:bit_stack` (cases "bit_stack")) THEN
  REWRITE_TAC[case_bitstack]);;

let GEN_DYCK_BIG_01 = prove
 (`!n p. gen_dyck (SUC(SUC(SUC n))) (if p then 1 else 0) = 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN MATCH_MP_TAC GEN_DYCK_MAX THEN
  ARITH_TAC);;

let LIST_CASES_2 = prove
 (`!l:A list. l = [] \/ (?a. l = [a]) \/ (?a b t. l = CONS a (CONS b t))`,
  LIST_INDUCT_TAC THEN ASM_MESON_TAC[]);;

let MATCH_COUNT_BAL_SPEC = prove
 (`!et h d lb b0.
     LENGTH lb = d
     ==> match_count (bal_spec h d b0) (stack_of_bitseq lb) et =
         (if LENGTH et = h /\
             ~(MEM Color0
                (CONS (addc (ccons (ODD d) (~(b0 <=> sumb lb))) (sumt et)) et))
          then gen_dyck (SUC d)
                 (count_cbit1
                   (CONS (addc (ccons (ODD d) (~(b0 <=> sumb lb))) (sumt et))
                         et))
          else 0)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THENL
   [REWRITE_TAC[MATCH_COUNT; BAL_SPEC_NIL; LENGTH; sumt; ADDC_0_RIGHT; MEM;
                count_cbit1; ADD_CLAUSES] THEN
    STRIP_ASSUME_TAC(ISPEC `lb:bool list` LIST_CASES_2) THEN
    ASM_REWRITE_TAC[LENGTH; ODD; sumb; GEN_DYCK_BIG_01; COND_ID] THEN
    BOOL_CASES_TAC `b0:bool` THEN TRY(BOOL_CASES_TAC `a:bool`) THEN
    REWRITE_TAC[ccons; cbit1; distinctness "color"; ONE; NOT_SUC; SUC_INJ;
                GEN_DYCK_ALL_CLOSE; EQ_SYM_EQ];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(SPEC `h':num` num_CASES) THENL
   [SIMP_TAC[MATCH_COUNT; BAL_SPEC_CONS; MATCH_COUNT_0; CASE_BITSTACK_CONST;
             NOT_SUC; ADD_CLAUSES; COND_ID; LENGTH];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
  REWRITE_TAC[MATCH_COUNT; distinctness "color"; LENGTH; sumt] THENL
   [REWRITE_TAC[MEM];
    ALL_TAC;
    STRUCT_CASES_TAC(ISPEC `lb:bool list` list_CASES) THENL
     [ALL_TAC; BOOL_CASES_TAC `h:bool`];
    STRUCT_CASES_TAC(ISPEC `lb:bool list` list_CASES) THENL
     [ALL_TAC; BOOL_CASES_TAC `h:bool`]] THEN
  REWRITE_TAC[stack_of_bitseq; case_bitstack] THEN
  REWRITE_TAC[GSYM STACK_PUSH_F; GSYM STACK_PUSH_T;
              GSYM(CONJUNCT1 stack_of_bitseq)] THEN
  REWRITE_TAC[LENGTH; BAL_SPEC_FUN] THEN ASM_SIMP_TAC[LENGTH] THEN
  REWRITE_TAC[LENGTH; ODD; SUMB_F; SUMB_T; ADDC_ASSOC; ADDC_CCONS; SUC_INJ;
              TAUT `((b <=> ~x) <=> ~(b <=> x)) /\
                    ((~b <=> x) <=> ~(b <=> x))`] THEN
  SIMP_TAC[MEM_C0_CONS_MID; COUNT_CBIT1_MID; distinctness "color"; cbit1] THEN
  REWRITE_TAC[ARITH_RULE `1 + k = SUC k`; ADD_CLAUSES; GEN_DYCK_SHIFT;
              GEN_DYCK_0] THEN
  COND_CASES_TAC THEN REWRITE_TAC[ADD_CLAUSES]);;

let MATCH_COUNT_BALANCED = prove
 (`!h et. match_count (init_gtree_spec h) Bstack0 et =
          (if LENGTH et = h /\ ~(MEM Color0 (ctrace et))
           then dyck (count_cbit1 (ctrace et)) else 0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`et:color list`; `h:num`; `0`; `[]:bool list`; `F`]
    MATCH_COUNT_BAL_SPEC) THEN
  REWRITE_TAC[LENGTH; stack_of_bitseq; INIT_GTREE_SPEC_BAL; ccons; ODD; sumb;
              addc_DEF; GSYM ctrace; GSYM ONE; GSYM dyck]);;
