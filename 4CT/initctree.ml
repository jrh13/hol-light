(* ========================================================================= *)
(* 4CT/initctree.ml                                                          *)
(*                                                                           *)
(* initctree.v: the initial (full) colouring tree ctree_init_tree h storing  *)
(* all even partial traces of ring size h, built by dynamic programming (a   *)
(* table of ctree_pairs per height, merged pairwise upwards, then the three  *)
(* pruned subtrees of height h-1 assembled), with its two correctness        *)
(* theorems CTREE_INIT_TREE_PROPER and CTREE_SUB_INIT_TREE.  Both go through *)
(* the same table invariants: entry i of the k-th table on branch b is the   *)
(* proper tree of height k whose counts are the Dyck numbers of the traces   *)
(* closed by ccons (ODD i) b (ITER_MERGE_PROPER, ITER_MERGE_SUB), the merge  *)
(* step being MERGE_TABLE_SUB and the leaf table LEAF_TABLE_SUB.             *)
(* ========================================================================= *)

needs "4CT/ctree.ml";;
needs "4CT/dyck.ml";;
needs "4CT/chromogram.ml";;

(* ------------------------------------------------------------------------- *)
(* The definitions (Coq's, with the two-step and n-indexed recursions recast *)
(* as primitive recursions: a toggle for the leaf table, curried maps for    *)
(* ctree_add_dyck).                                                          *)
(* ------------------------------------------------------------------------- *)

let count_cbit1 = define
 `(count_cbit1 ([]:color list) = 0) /\
  (count_cbit1 (CONS c et) = (if cbit1 c then 1 else 0) + count_cbit1 et)`;;

let ctree_table_sub = new_recursive_definition list_RECURSION
 `(ctree_table_sub [] n = (\b. CtreeEmpty)) /\
  (ctree_table_sub (CONS pt tab') n =
     (\b. if n = 0 then ctree_pair_sub pt b
     else ctree_table_sub tab' (n - 1) b))`;;

let iteri_ctree = new_recursive_definition num_RECURSION
 `(iteri_ctree 0 f x = x) /\
  (iteri_ctree (SUC n) f x = f n (iteri_ctree n f x))`;;

let ctree_add_dyck_fn = new_recursive_definition num_RECURSION
 `(ctree_add_dyck_fn 0 = (\m (lf:ctree). CtreeLeaf lf)) /\
  (ctree_add_dyck_fn (SUC n') =
     (\m lf. iteri_ctree (SUC m) (\m'. ctree_add_dyck_fn n' (SUC m')) lf))`;;

let ctree_add_dyck = define
 `ctree_add_dyck m n lf = ctree_add_dyck_fn n m lf`;;

let leaf_from1_fn = new_recursive_definition num_RECURSION
 `(leaf_from1_fn 0 = (\(lf:ctree) (n:num) (tog:bool). ([]:(ctree_pair)list)))
  /\
  (leaf_from1_fn (SUC h') =
     (\lf n tog.
        if tog then CONS (CtreePair CtreeEmpty lf)
                      (leaf_from1_fn h' (ctree_add_dyck 2 n lf) (n + 1) F)
        else CONS (CtreePair lf lf) (leaf_from1_fn h' lf n T)))`;;

let ctree_leaf_table_from = define
 `ctree_leaf_table_from lf n h = leaf_from1_fn h lf n F`;;

let ctree_leaf_table = define
 `ctree_leaf_table h =
    CONS (CtreePair CtreeEmpty (CtreeLeaf CtreeEmpty))
         (ctree_leaf_table_from (CtreeLeaf CtreeEmpty) 0 h)`;;

let ctree_merge_pair = define
 `ctree_merge_pair (CtreePair t0 t1) (CtreePair t2 t3) =
    CtreePair (ctree_cons t1 t2 t3) (ctree_cons t0 t3 t2)`;;

let ctree_pairmap = new_recursive_definition list_RECURSION
 `(ctree_pairmap x [] = []) /\
  (ctree_pairmap x (CONS y l) =
  CONS (ctree_merge_pair x y) (ctree_pairmap y l))`;;

let ctree_merge_table = define
 `(ctree_merge_table [] = []) /\
  (ctree_merge_table (CONS line tab') = ctree_pairmap line tab')`;;

let ctree_prune_1 = define
 `(ctree_prune_1 (CtreeNode t1 t2 t3) =
  ctree_cons (ctree_prune_1 t1) t2 CtreeEmpty) /\
  (ctree_prune_1 (CtreeLeaf lf) = CtreeLeaf lf) /\
  (ctree_prune_1 CtreeEmpty = CtreeEmpty)`;;
let ctree_prune_2 = define
 `(ctree_prune_2 (CtreeNode t1 t2 t3) =
  ctree_cons CtreeEmpty (ctree_prune_2 t2) t3) /\
  (ctree_prune_2 (CtreeLeaf lf) = CtreeLeaf lf) /\
  (ctree_prune_2 CtreeEmpty = CtreeEmpty)`;;
let ctree_prune_3 = define
 `(ctree_prune_3 (CtreeNode t1 t2 t3) =
  ctree_cons t1 CtreeEmpty (ctree_prune_3 t3)) /\
  (ctree_prune_3 (CtreeLeaf lf) = CtreeLeaf lf) /\
  (ctree_prune_3 CtreeEmpty = CtreeEmpty)`;;

let ctree_init_tree = define
 `ctree_init_tree h =
    (let tab = ITER (h - 1) ctree_merge_table (ctree_leaf_table h) in
     if LENGTH tab < 2 then CtreeEmpty
     else ctree_cons (ctree_prune_1 (ctree_pair_sub (HD tab) T))
                     (ctree_prune_2 (ctree_pair_sub (HD(TL tab)) F))
                     (ctree_prune_3 (ctree_pair_sub (HD(TL tab)) T)))`;;

(* ------------------------------------------------------------------------- *)
(* Tables: the entries of a table, of a merged pair and of a merged table    *)
(* (entry i of the merged table is the node of the entries i and i+1).       *)
(* ------------------------------------------------------------------------- *)

let CTSUB_CLAUSES = prove
 (`(!n b. ctree_table_sub [] n b = CtreeEmpty) /\
   (!pt tab b. ctree_table_sub (CONS pt tab) 0 b = ctree_pair_sub pt b) /\
   (!pt tab n b. ctree_table_sub (CONS pt tab) (SUC n) b =
                 ctree_table_sub tab n b)`,
  REWRITE_TAC[ctree_table_sub; NOT_SUC; SUC_SUB1]);;

let TABLE_SUB_HD = prove
 (`!tab b. 2 <= LENGTH tab
           ==> ctree_pair_sub (HD tab) b = ctree_table_sub tab 0 b /\
               ctree_pair_sub (HD(TL tab)) b = ctree_table_sub tab 1 b`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `tab:ctree_pair list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= 0)`] THEN
  STRUCT_CASES_TAC(ISPEC `t:ctree_pair list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= SUC 0)`; HD; TL; CTSUB_CLAUSES;
              ONE]);;

let MERGE_PAIR_SUB = prove
 (`!p q b. ctree_pair_sub (ctree_merge_pair p q) b =
           ctree_cons (ctree_pair_sub p (~b)) (ctree_pair_sub q b)
                      (ctree_pair_sub q (~b))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `p:ctree_pair` (cases "ctree_pair")) THEN
  STRUCT_CASES_TAC(ISPEC `q:ctree_pair` (cases "ctree_pair")) THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[ctree_merge_pair; ctree_pair_sub]);;

let PAIRMAP_SUB = prove
 (`!l x i b. i < LENGTH l
             ==> ctree_table_sub (ctree_pairmap x l) i b =
                 ctree_cons (ctree_table_sub (CONS x l) i (~b))
                            (ctree_table_sub (CONS x l) (SUC i) b)
                            (ctree_table_sub (CONS x l) (SUC i) (~b))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  ASM_SIMP_TAC[ctree_pairmap; CTSUB_CLAUSES; MERGE_PAIR_SUB; LT_SUC; LT_0]);;

let MERGE_TABLE_SUB = prove
 (`!tab i b. SUC i < LENGTH tab
             ==> ctree_table_sub (ctree_merge_table tab) i b =
                 ctree_cons (ctree_table_sub tab i (~b))
                            (ctree_table_sub tab (SUC i) b)
                            (ctree_table_sub tab (SUC i) (~b))`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[LENGTH; CONJUNCT1 LT; LT_SUC; ctree_merge_table; PAIRMAP_SUB]);;

let LENGTH_PAIRMAP = prove
 (`!l x. LENGTH(ctree_pairmap x l) = LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ctree_pairmap; LENGTH]);;

let LENGTH_MERGE_TABLE = prove
 (`!tab. LENGTH(ctree_merge_table tab) = LENGTH tab - 1`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ctree_merge_table; LENGTH; LENGTH_PAIRMAP; SUB_0; SUC_SUB1]);;

(* ------------------------------------------------------------------------- *)
(* Dyck numbers: the recursion of gen_dyck and the leaf bump                 *)
(* ctree_add_dyck m n (leaf d) = leaf (gen_dyck (m+1) (m+2n) + d), by the    *)
(* parallel recursions of ctree_add_dyck and gen_dyck.                       *)
(* ------------------------------------------------------------------------- *)

let ADD_DYCK_CLAUSES = prove
 (`(!m lf. ctree_add_dyck m 0 lf = CtreeLeaf lf) /\
   (!n lf. ctree_add_dyck 0 (SUC n) lf = ctree_add_dyck 1 n lf) /\
   (!m n lf. ctree_add_dyck (SUC m) (SUC n) lf =
             ctree_add_dyck (SUC(SUC m)) n (ctree_add_dyck m (SUC n) lf))`,
  REWRITE_TAC[ctree_add_dyck; ctree_add_dyck_fn; iteri_ctree; ONE]);;

let GEN_DYCK_CLAUSES = prove
 (`(!m. gen_dyck (SUC m) (m + 2 * 0) = 1) /\
   (!n. gen_dyck (SUC 0) (0 + 2 * SUC n) = gen_dyck (SUC 1) (1 + 2 * n)) /\
   (!m n. gen_dyck (SUC(SUC m)) (SUC m + 2 * SUC n) =
          gen_dyck (SUC(SUC(SUC m))) (SUC(SUC m) + 2 * n) +
          gen_dyck (SUC m) (m + 2 * SUC n))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; GEN_DYCK_ALL_CLOSE];
    SUBGOAL_THEN `0 + 2 * SUC n = SUC(SUC(2 * n)) /\ 1 + 2 * n = SUC(2 * n)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `SUC m + 2 * SUC n = SUC(SUC(SUC m) + 2 * n) /\
                  m + 2 * SUC n = SUC(SUC m) + 2 * n`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [ARITH_TAC; ALL_TAC]] THEN
  REWRITE_TAC[GEN_DYCK_SHIFT; GEN_DYCK_0; ADD_CLAUSES; ONE]);;

let CTREE_ADD_DYCK_LEAF_OF = prove
 (`!n m d. ctree_add_dyck m n (ctree_leaf_of d) =
           ctree_leaf_of (gen_dyck (SUC m) (m + 2 * n) + d)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_DYCK_CLAUSES; GEN_DYCK_CLAUSES; ctree_leaf_of; ONE;
                ADD_CLAUSES; ITER];
    INDUCT_TAC THEN GEN_TAC THEN
    ASM_REWRITE_TAC[ADD_DYCK_CLAUSES; GEN_DYCK_CLAUSES; ADD_ASSOC]]);;

let DYCK_STEP = prove
 (`!k. dyck (SUC(SUC k)) = gen_dyck 3 k + dyck k`,
  REWRITE_TAC[dyck; num_CONV `3`; TWO; ONE; GEN_DYCK_SHIFT; GEN_DYCK_0;
              ADD_CLAUSES]);;

let ADD_DYCK_BLOCK = prove
 (`!n. ctree_add_dyck 2 n (ctree_leaf_of (dyck (2 * n + 2))) =
       ctree_leaf_of (dyck (2 * (n + 1) + 2))`,
  REWRITE_TAC[CTREE_ADD_DYCK_LEAF_OF;
              ARITH_RULE `2 * (n + 1) + 2 = SUC(SUC(2 * n + 2))`;
              DYCK_STEP; ARITH_RULE `SUC 2 = 3`;
              ARITH_RULE `2 + 2 * n = 2 * n + 2`]);;

(* ------------------------------------------------------------------------- *)
(* The leaf table: its length and its entries.  The block of position j in   *)
(* leaf_from1_fn (j counted from the F position) carries leaf (dyck (2n+2))  *)
(* for the current n, advanced every two positions; entry i of the table is  *)
(* leaf (dyck (i + (if ODD i then 1 else 0))) unless the closing colour      *)
(* ccons (ODD i) b0 is Color0.                                               *)
(* ------------------------------------------------------------------------- *)

let LENGTH_LEAF_FROM1 = prove
 (`!h lf n tog. LENGTH(leaf_from1_fn h lf n tog) = h`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[leaf_from1_fn; LENGTH] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let CTREE_LEAF_TABLE_SIZE = prove
 (`!h. LENGTH(ctree_leaf_table h) = h + 1`,
  REWRITE_TAC[ctree_leaf_table; ctree_leaf_table_from; LENGTH;
              LENGTH_LEAF_FROM1; ADD1]);;

let LEAF_FROM1_SUB = prove
 (`!h i n b tog.
     i < h
     ==> ctree_table_sub
           (leaf_from1_fn h (ctree_leaf_of (dyck (2 * n + 2))) n tog) i b =
         (if ODD (if tog then SUC i else i) /\ ~b then CtreeEmpty
          else ctree_leaf_of
                 (dyck (2 * n + (if tog then SUC i else i) +
                        (if ODD (if tog then SUC i else i) then 1 else 2))))`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN REWRITE_TAC[LT_0; LT_SUC] THEN
  BOOL_CASES_TAC `tog:bool` THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_SIMP_TAC[leaf_from1_fn; CTSUB_CLAUSES; ctree_pair_sub; ADD_DYCK_BLOCK;
               ODD; ARITH_RULE `2 * n + 0 + 2 = 2 * n + 2`;
               ARITH_RULE `2 * n + SUC 0 + 1 = 2 * n + 2`;
               ARITH_RULE `2 * (n + 1) + i + c = 2 * n + SUC(SUC i) + c`]);;

let LEAF_OF_DYCK = prove
 (`ctree_leaf_of (dyck 0) = CtreeLeaf CtreeEmpty /\
   ctree_leaf_of (dyck (2 * 0 + 2)) = CtreeLeaf CtreeEmpty`,
  REWRITE_TAC[dyck; gen_dyck; MULT_CLAUSES; ADD_CLAUSES; TWO; ONE] THEN
  REWRITE_TAC[gen_dyck_fn] THEN NUM_REDUCE_TAC THEN
  REWRITE_TAC[ctree_leaf_of; ONE; ITER]);;

let LEAF_TABLE_SUB = prove
 (`!n i b0. i <= n
            ==> ctree_table_sub (ctree_leaf_table n) i b0 =
                (if ccons (ODD i) b0 = Color0 then CtreeEmpty
                 else ctree_leaf_of (dyck (i + (if ODD i then 1 else 0))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ctree_leaf_table; ctree_leaf_table_from] THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[CTSUB_CLAUSES; ctree_pair_sub; LE_SUC_LT; LE_0; ODD;
              ADD_CLAUSES] THENL
   [BOOL_CASES_TAC `b0:bool` THEN
    REWRITE_TAC[ccons; distinctness "color"; LEAF_OF_DYCK];
    REWRITE_TAC[GSYM(CONJUNCT2 LEAF_OF_DYCK)] THEN
    SIMP_TAC[LEAF_FROM1_SUB] THEN DISCH_THEN(K ALL_TAC) THEN
    BOOL_CASES_TAC `b0:bool` THEN ASM_CASES_TAC `ODD n'` THEN
    ASM_REWRITE_TAC[ccons; distinctness "color"] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The table invariants: after k merges the table has (n+1)-k entries, each  *)
(* a proper tree of height k whose count at a trace et of length k is the    *)
(* Dyck number of et closed by the colour ccons (ODD i) b0 + sumt et.        *)
(* ------------------------------------------------------------------------- *)

let ITER_MERGE_LENGTH = prove
 (`!k n. LENGTH(ITER k ctree_merge_table (ctree_leaf_table n)) = (n + 1) - k`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITER; LENGTH_MERGE_TABLE; CTREE_LEAF_TABLE_SIZE; SUB_0] THEN
  ARITH_TAC);;

let ITER_MERGE_PROPER = prove
 (`!k n i b.
     i < LENGTH(ITER k ctree_merge_table (ctree_leaf_table n))
     ==> ctree_proper k
           (ctree_table_sub (ITER k ctree_merge_table (ctree_leaf_table n))
                            i b)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ITER; LENGTH_MERGE_TABLE; CTREE_LEAF_TABLE_SIZE; GSYM ADD1;
              LT_SUC_LE] THEN
  DISCH_TAC THENL
   [ASM_SIMP_TAC[LEAF_TABLE_SUB] THEN COND_CASES_TAC THEN
    REWRITE_TAC[ctree_proper; CTREE_LEAF_OF_PROPER];
    ASM_SIMP_TAC[MERGE_TABLE_SUB; ARITH_RULE `i < n - 1 ==> SUC i < n`] THEN
    MATCH_MP_TAC(REWRITE_RULE[GSYM ADD1] CTREE_CONS_PROPER) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n - 1 ==> i < n /\ SUC i < n`]]);;

let ITER_MERGE_SUB = prove
 (`!k n i b0 et.
     i < LENGTH(ITER k ctree_merge_table (ctree_leaf_table n))
     ==> ctree_sub
           (ctree_table_sub (ITER k ctree_merge_table (ctree_leaf_table n))
                            i b0) et =
         (if LENGTH et = k /\
             ~(MEM Color0 (CONS (addc (ccons (ODD i) b0) (sumt et)) et))
          then dyck (i + count_cbit1
                           (CONS (addc (ccons (ODD i) b0) (sumt et)) et))
          else 0)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ITER; LENGTH_MERGE_TABLE; CTREE_LEAF_TABLE_SIZE; GSYM ADD1;
              LT_SUC_LE] THEN
  DISCH_TAC THEN STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THENL
   [ASM_SIMP_TAC[LEAF_TABLE_SUB] THEN
    REWRITE_TAC[LENGTH; sumt; ADDC_0; MEM; count_cbit1; CBIT1_CCONS;
                ADD_CLAUSES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ctree_sub; CTREE_SUB_LEAF_OF];
    ASM_SIMP_TAC[LEAF_TABLE_SUB] THEN REWRITE_TAC[LENGTH; NOT_SUC] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[ctree_sub; CTREE_SUB_LEAF_OF; NOT_CONS_NIL];
    ASM_SIMP_TAC[MERGE_TABLE_SUB; ARITH_RULE `i < n - 1 ==> SUC i < n`] THEN
    REWRITE_TAC[CTREE_SUB_CONS; ctree_sub; LENGTH; NOT_SUC];
    ASM_SIMP_TAC[MERGE_TABLE_SUB; ARITH_RULE `i < n - 1 ==> SUC i < n`] THEN
    REWRITE_TAC[CTREE_SUB_CONS; ctree_sub; LENGTH; SUC_INJ; NOT_CONS_NIL; HD;
                TL] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n - 1 ==> i < n /\ SUC i < n`] THEN
    STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
    REWRITE_TAC[distinctness "color"; sumt; MEM; count_cbit1; cbit1;
                ADDC_ASSOC; ADDC_CCONS; ODD; ADD_CLAUSES;
                ARITH_RULE `SUC(i + x + y) = i + x + 1 + y`]]);;

(* ------------------------------------------------------------------------- *)
(* Pruning keeps properness and keeps exactly the traces whose (rotated)     *)
(* tail is even; the even_trace of a trace with a nonzero head.              *)
(* ------------------------------------------------------------------------- *)

let PRUNE_PROPER_TAC def =
  MATCH_MP_TAC ctree_INDUCT THEN REWRITE_TAC[def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `h:num` num_CASES) THEN
  REWRITE_TAC[ctree_proper; NOT_SUC; SUC_SUB1] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM ADD1] CTREE_CONS_PROPER) THEN
  ASM_SIMP_TAC[ctree_proper];;

let PRUNE_1_PROPER = prove
 (`!t h. ctree_proper h t ==> ctree_proper h (ctree_prune_1 t)`,
  PRUNE_PROPER_TAC ctree_prune_1);;

let PRUNE_2_PROPER = prove
 (`!t h. ctree_proper h t ==> ctree_proper h (ctree_prune_2 t)`,
  PRUNE_PROPER_TAC ctree_prune_2);;

let PRUNE_3_PROPER = prove
 (`!t h. ctree_proper h t ==> ctree_proper h (ctree_prune_3 t)`,
  PRUNE_PROPER_TAC ctree_prune_3);;

let PRUNE_PROPER = prove
 (`!n t. ctree_proper n t
         ==> ctree_proper n (ctree_prune_1 t) /\
             ctree_proper n (ctree_prune_2 t) /\
             ctree_proper n (ctree_prune_3 t)`,
  SIMP_TAC[PRUNE_1_PROPER; PRUNE_2_PROPER; PRUNE_3_PROPER]);;

let PRUNE_SUB_TAC def =
  LIST_INDUCT_TAC THEN X_GEN_TAC `tr:ctree` THEN
  STRUCT_CASES_TAC(ISPEC `tr:ctree` (cases "ctree")) THEN
  REWRITE_TAC[def; ctree_sub; CTREE_SUB_CONS; permt; even_tail; NOT_CONS_NIL;
              COND_ID] THEN
  TRY(STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[HD; TL; permc_DEF; distinctness "color"; even_tail;
                  COND_ID] THEN
      ASM_REWRITE_TAC[]);;

let PRUNE_1_SUB = prove
 (`!et tr. ctree_sub (ctree_prune_1 tr) et =
           if even_tail et then ctree_sub tr et else 0`,
  PRUNE_SUB_TAC ctree_prune_1);;

let PRUNE_2_SUB = prove
 (`!et tr. ctree_sub (ctree_prune_2 tr) et =
           if even_tail (permt Eperm312 et) then ctree_sub tr et else 0`,
  PRUNE_SUB_TAC ctree_prune_2);;

let PRUNE_3_SUB = prove
 (`!et tr. ctree_sub (ctree_prune_3 tr) et =
           if even_tail (permt Eperm231 et) then ctree_sub tr et else 0`,
  PRUNE_SUB_TAC ctree_prune_3);;

let EVEN_TRACE_CONS = prove
 (`!c et. ~(c = Color0)
          ==> (even_trace (CONS c et) <=> even_tail (permt (edge_rot c) et))`,
  SIMP_TAC[even_trace; ttail; proper_trace; NOT_CONS_NIL; HD; TL]);;

(* ------------------------------------------------------------------------- *)
(* The two correctness theorems, and the two small trace facts on a middle   *)
(* colour used by initgtree.ml.                                              *)
(* ------------------------------------------------------------------------- *)

let CTREE_INIT_TREE_PROPER = prove
 (`!h. ctree_proper h (ctree_init_tree h)`,
  GEN_TAC THEN REWRITE_TAC[ctree_init_tree] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  STRUCT_CASES_TAC(SPEC `h:num` num_CASES) THENL
   [REWRITE_TAC[SUB_0; ITER; CTREE_LEAF_TABLE_SIZE; ARITH_RULE `0 + 1 < 2`;
                ctree_proper];
    ALL_TAC] THEN
  REWRITE_TAC[ITER_MERGE_LENGTH; SUC_SUB1;
              ARITH_RULE `~((SUC n + 1) - n < 2)`] THEN
  SIMP_TAC[TABLE_SUB_HD; ITER_MERGE_LENGTH;
           ARITH_RULE `2 <= (SUC n + 1) - n`] THEN
  MATCH_MP_TAC(REWRITE_RULE[GSYM ADD1] CTREE_CONS_PROPER) THEN
  SIMP_TAC[PRUNE_PROPER; ITER_MERGE_PROPER; ITER_MERGE_LENGTH;
           ARITH_RULE `0 < (SUC n + 1) - n /\ 1 < (SUC n + 1) - n`]);;

let COND_COND_0 = prove
 (`!c p (d:num). (if c then (if p then d else 0) else 0) =
                 (if p /\ c then d else 0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN BOOL_CASES_TAC `p:bool` THEN
  REWRITE_TAC[]);;

let CTREE_SUB_INIT_TREE = prove
 (`!h et. ctree_sub (ctree_init_tree h) et =
          (if LENGTH et = h /\ ~(MEM Color0 (ctrace et)) /\ even_trace et
           then dyck (count_cbit1 (ctrace et)) else 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ctree_init_tree] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  STRUCT_CASES_TAC(SPEC `h:num` num_CASES) THENL
   [REWRITE_TAC[SUB_0; ITER; CTREE_LEAF_TABLE_SIZE; ARITH_RULE `0 + 1 < 2`;
                ctree_sub] THEN
    STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; ctrace; sumt; MEM];
    ALL_TAC] THEN
  REWRITE_TAC[ITER_MERGE_LENGTH; SUC_SUB1;
              ARITH_RULE `~((SUC n + 1) - n < 2)`] THEN
  SIMP_TAC[TABLE_SUB_HD; ITER_MERGE_LENGTH;
           ARITH_RULE `2 <= (SUC n + 1) - n`] THEN
  REWRITE_TAC[CTREE_SUB_CONS] THEN
  STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THEN
  REWRITE_TAC[ctree_sub; LENGTH; NOT_SUC; SUC_INJ; NOT_CONS_NIL; HD; TL;
              ctrace; sumt; MEM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
  REWRITE_TAC[distinctness "color"; PRUNE_1_SUB; PRUNE_2_SUB; PRUNE_3_SUB] THEN
  SIMP_TAC[ITER_MERGE_SUB; ITER_MERGE_LENGTH; EVEN_TRACE_CONS;
           distinctness "color"; edge_rot_DEF; PERMT_ID;
           ARITH_RULE `0 < (SUC n + 1) - n /\ 1 < (SUC n + 1) - n`] THEN
  REWRITE_TAC[sumt; MEM; count_cbit1; cbit1; distinctness "color"; ONE; ODD;
              ccons; ADD_CLAUSES; COND_COND_0; CONJ_ACI;
              ARITH_RULE `SUC 0 + (x + y) = x + (SUC 0 + y)`]);;

let MEM_C0_CONS_MID = prove
 (`!x c et. ~(c = Color0)
            ==> (MEM Color0 (CONS x (CONS c et)) <=> MEM Color0 (CONS x et))`,
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

let COUNT_CBIT1_MID = prove
 (`!x c et. count_cbit1 (CONS x (CONS c et)) =
            (if cbit1 c then 1 else 0) + count_cbit1 (CONS x et)`,
  REWRITE_TAC[count_cbit1] THEN ARITH_TAC);;
