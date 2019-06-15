(* ========================================================================= *)
(* Properties of the lexicographic path order.                               *)
(* ========================================================================= *)

let ITLIST_ADD_1_POS = prove
 (`!l. 0 < ITLIST (+) l 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; ARITH] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let FVT_FUN_EMPTY = prove
 (`!f a args. MEM a args /\ (FVT(Fn f args) = {}) ==> (FVT a = {})`,
  REWRITE_TAC[FVT; EXTENSION; NOT_IN_EMPTY; IN_LIST_UNION; MEM_MAP;
              GSYM EX_MEM; o_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Notion of an *element* being nonwellfounded: can start a dchain.          *)
(* ------------------------------------------------------------------------- *)

let NONWF = new_definition
  `NONWF(R) a <=> ?s:num->A. (s 0 = a) /\ (!n. R (s(SUC n)) (s n))`;;

let WF_NONWF = prove
 (`WF(R) <=> !a. ~(NONWF(R) a)`,
  REWRITE_TAC[WF_DCHAIN; NONWF] THEN MESON_TAC[]);;

let NONWF_SUCCESSOR = prove
 (`!R a:A b. NONWF(R) b /\ R b a ==> NONWF(R) a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONWF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n. if n = 0 then a:A else s(n - 1)` THEN
  REWRITE_TAC[NOT_SUC] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> (SUC n - 1 = SUC(n - 1))`]);;

let WF_NONWF = prove
 (`WF(\x:A y. R x y /\ ~(NONWF(R) y))`,
  REWRITE_TAC[WF_DCHAIN; NONWF] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->A` MP_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[] THEN
  EXISTS_TAC `s:num->A` THEN ASM_REWRITE_TAC[]);;

let NONWF_INDUCT = prove
 (`(!a. ~(NONWF(R) a) /\ (!b. R b a ==> P(b)) ==> P(a))
   ==> !x. ~(NONWF(R) x) ==> P(x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(MATCH_MP(fst(EQ_IMP_RULE WF_IND)) WF_NONWF) THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[NONWF_SUCCESSOR]);;

(* ------------------------------------------------------------------------- *)
(* General result on "minimal" infinite descending chains.                   *)
(* ------------------------------------------------------------------------- *)

let WF_MINIMAL_STEP = prove
 (`!m:A->num a.
        NONWF(R) a
        ==> ?b. NONWF(R) b /\ R b a /\
                (!c. NONWF(R) c /\ R c a ==> m(b) <= m(c))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC
   `\n. ?c. NONWF(R) c /\ R c a /\ ((m:A->num)(c) = n)` num_WOP) THEN
  MATCH_MP_TAC(TAUT `(b ==> c) /\ a ==> (a <=> b) ==> c`) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[NOT_LT]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NONWF] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(m:A->num) (s 1)`; `(s:num->A) 1`] THEN
  ASM_REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN EXISTS_TAC `\n. s(SUC n):A` THEN
  ASM_REWRITE_TAC[ARITH] THEN ASM_MESON_TAC[num_CONV `1`]);;

let WF_MINIMAL_DCHAIN = prove
 (`!m:A->num.
     WF(R) <=> ~(?t. (!n. R (t(SUC n)) (t n)) /\
                     (!s. NONWF(R) s ==> m(t 0) <= m(s)) /\
                     (!n s. NONWF(R) s /\ R s (t n) ==> m(t(SUC n)) <= m(s)))`,
  GEN_TAC THEN REWRITE_TAC[WF_DCHAIN] THEN AP_TERM_TAC THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN DISCH_TAC THEN
  MP_TAC(SPEC `\n. ?s. NONWF(R) s /\ ((m:A->num)(s) = n)` num_WOP) THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [REWRITE_TAC[NONWF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n_0:num` MP_TAC) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `!s. NONWF R s ==> (m:A->num)(a) <= m(s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`a:A`; `\b (n:num). @c. NONWF(R) c /\ R c b /\
                            !d. NONWF(R) d /\ R d b ==> (m:A->num)(c) <= m(d)`]
   num_RECURSION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:num->A` THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `!d. b /\ d /\ a /\ c ==> a /\ b /\ c`) THEN
  EXISTS_TAC `(!n. NONWF R (t(SUC n):A))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN INDUCT_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SPEC `0`);
    FIRST_ASSUM(SUBST1_TAC o SPEC `SUC n`)] THEN
  CONV_TAC SELECT_CONV THEN
  MATCH_MP_TAC WF_MINIMAL_STEP THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Simple subsequence lemma finitely partitioning an infinite sequence.      *)
(* ------------------------------------------------------------------------- *)

let SEQUENCE_SUBSEQUENCE = prove
 (`!P (x:num->A).
        (!n. ?m. n < m /\ P(x m)) ==> ?f. subseq f /\ !n. P(x(f n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `st:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`st(0):num`; `\m:num p:num. st(m):num`] num_RECURSION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:num->num` THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSEQ_SUC] THEN ASM_MESON_TAC[];
    INDUCT_TAC THEN ASM_MESON_TAC[]]);;

let SEQUENCE_PARTITION_LEMMA = prove
 (`!x:num->A s. FINITE(s) /\ (!n. x(n) IN s)
                ==> ?a f. subseq f /\ (!n. x(f n) = a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?a:A. !n. ?m:num. n < m /\ (x m = a)` MP_TAC THENL
   [SUBGOAL_THEN
     `!s. FINITE s
          ==> (?n:num. !m. n < m ==> (x(m) IN s))
              ==> ?a:A. !n. ?m. n < m /\ (x m = a)`
     (fun th -> ASM_MESON_TAC[th]) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
    CONJ_TAC THENL [MESON_TAC[LT]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`b:A`; `s:A->bool`] THEN
    MATCH_MP_TAC(TAUT `(~a /\ c ==> b) ==> (a ==> b) ==> (c ==> b)`) THEN
    REWRITE_TAC[IN_INSERT; NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP] THEN
    ASM_MESON_TAC[ARITH_RULE `(m + n < p:num ==> m < p /\ n < p)`];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\x:A. x = a` SEQUENCE_SUBSEQUENCE) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Term size (used as auxiliary notion).                                     *)
(* ------------------------------------------------------------------------- *)

let termsize_EXISTS = prove
 (`?termsize.
     (!x. termsize(V x) = 1) /\
     (!f args. termsize(Fn f args) = ITLIST (+) (MAP termsize args) 1)`,
  MP_TAC(ISPECL [`\x:num. 1`;
                 `\(f:num) (args:term list) (ns:num list). ITLIST (+) ns 1`;
                 `[]:num list`;
                 `\(t:term) (ts:term list) (n:num) (ns:num list). CONS n ns`]
                term_raw_RECURSION) THEN
  REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MAP]);;

let termsize = new_specification ["termsize"] termsize_EXISTS;;

(* ------------------------------------------------------------------------- *)
(* Lexical extension of a relation, forcing equivalent list lengths.         *)
(* ------------------------------------------------------------------------- *)

let LEX_DEF = new_recursive_definition list_RECURSION
  `(LEX(<<) [] l <=> F) /\
   (LEX(<<) (CONS h t) l <=>
        if l = [] then F
        else if h << HD l then LENGTH t = LENGTH(TL l)
        else (h = HD l) /\ LEX(<<) t (TL l))`;;

let LEX = prove
 (`(LEX(<<) [] l <=> F) /\
   (LEX(<<) (CONS h1 t1) [] <=> F) /\
   (LEX(<<) (CONS h1 t1) (CONS h2 t2) <=>
        if h1 << h2 then LENGTH t1 = LENGTH t2
        else (h1 = h2) /\ LEX(<<) t1 t2)`,
  REWRITE_TAC[LEX_DEF; NOT_CONS_NIL; HD; TL]);;

let LEX_LENGTH = prove
 (`!l1 l2 R. LEX(R) l1 l2 ==> (LENGTH l1 = LENGTH l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LEX] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LEX] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH] THEN
  ASM_MESON_TAC[]);;

let MONO_LEX = prove
 (`(!x:A y:A. R x y ==> S x y) ==> LEX R x y ==> LEX S x y`,
  DISCH_TAC THEN SPEC_TAC(`y:A list`,`y:A list`) THEN
  SPEC_TAC(`x:A list`,`x:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LEX] THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LEX] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[LEX_LENGTH]);;

monotonicity_theorems := MONO_LEX::(!monotonicity_theorems);;

let LEX_MAP = prove
 (`!l1 l2. LEX (\x y. R (f x) (f y)) l1 l2 ==> LEX R (MAP f l1) (MAP f l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LEX; MAP] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LEX; MAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH_MAP] THEN ASM_SIMP_TAC[]);;

let LEX_REFL = prove
 (`!R l. (!x. MEM x l ==> ~(R x x)) ==> ~(LEX(R) l l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LEX; MEM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Stronger variant of WF preservation under lexicographic extension.        *)
(* ------------------------------------------------------------------------- *)

let LEX_LENGTH_CHAIN = prove
 (`!lis R. (!n. LEX(R) (lis(SUC n)) (lis n))
           ==> !n. LENGTH(lis(n)) = LENGTH(lis(0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[LEX_LENGTH]);;

let WF_LEX_STRONG_INDUCT = prove
 (`!n lis. (LENGTH(lis 0) = n)
           ==> ~((!n a:A. MEM a (lis n) ==> ~(NONWF(R) a)) /\
                 (!n. LEX(R) (lis(SUC n)) (lis n)))`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LEX_LENGTH_CHAIN) THEN
    UNDISCH_TAC `!n. LENGTH (lis n :(A)list) = LENGTH (lis 0)` THEN
    ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_MESON_TAC[LEX];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP LEX_LENGTH_CHAIN) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?hd tl. !n:num. CONS (hd n :A) (tl n) = lis(n)` MP_TAC THENL
   [EXISTS_TAC `\n:num. HD(lis n):A` THEN
    EXISTS_TAC `\n:num. TL(lis n):A list` THEN
    SUBGOAL_THEN `!n:num. ~(lis n :(A)list = [])` MP_TAC THENL
     [ASM_MESON_TAC[LEX_LENGTH_CHAIN; LENGTH; NOT_SUC]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[] THEN
    SPEC_TAC(`(lis:num->(A)list) m`,`l:(A)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]))) THEN
  UNDISCH_TAC `!n:num a:A. MEM a (CONS (hd n) (tl n)) ==> ~NONWF R a` THEN
  REWRITE_TAC[MEM; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  STRIP_TAC THEN UNDISCH_TAC
   `!n:num. LEX R (CONS (hd(SUC n):A) (tl(SUC n))) (CONS (hd n) (tl n))` THEN
  REWRITE_TAC[LEX] THEN
  UNDISCH_TAC `!m:num. LENGTH (CONS (hd m :A) (tl m)) = SUC n` THEN
  REWRITE_TAC[LENGTH; SUC_INJ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TAUT `(if p then T else r) <=> p \/ ~p /\ r`] THEN
  UNDISCH_TAC `!n:num a:A. MEM a (tl n) ==> ~NONWF R a` THEN
  UNDISCH_TAC `!m. LENGTH ((tl:num->(A)list) m) = n` THEN
  REWRITE_TAC[IMP_IMP] THEN
  SPEC_TAC(`tl:num->(A)list`,`tl:num->(A)list`) THEN
  ABBREV_TAC `h:A = hd 0` THEN
  SUBGOAL_THEN `~(NONWF(R) (h:A))` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
   UNDISCH_TAC `!n:num. ~NONWF R (hd n :A)` THEN
   UNDISCH_TAC `hd 0 :A = h` THEN MP_TAC th) THEN
  SPEC_TAC(`hd:num->A`,`hd:num->A`) THEN SPEC_TAC(`h:A`,`h:A`) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC NONWF_INDUCT THEN X_GEN_TAC `h:A` THEN STRIP_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN STRIP_TAC THEN
  X_GEN_TAC `hd:num->A` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?m. R (hd(SUC m):A) (hd m)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(hd:num->A) (SUC p)`) THEN ANTS_TAC THENL
   [SUBGOAL_THEN `!n. n <= p ==> (hd n :A = h)`
     (fun th -> ASM_MESON_TAC[th; LE_REFL]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[LE_SUC_LT] THEN
    ASM_MESON_TAC[LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. hd(SUC p + n):A`) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; NOT_IMP] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. tl(SUC p + n):A list`) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN
  FIRST_ASSUM(MP_TAC o check (is_disj o concl) o SPEC `SUC(p + m)`) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let WF_LEX_STRONG = prove
 (`!R lis. ~((!n a:A. MEM a (lis n) ==> ~(NONWF(R) a)) /\
             (!n. LEX(R) (lis(SUC n)) (lis n)))`,
  MESON_TAC[WF_LEX_STRONG_INDUCT]);;

(* ------------------------------------------------------------------------- *)
(* Ad-hoc but useful lemma.                                                  *)
(* ------------------------------------------------------------------------- *)

let LEX_RESTRICT = prove
 (`!P R l1 l2. LEX R l1 l2 /\
               (!a. MEM a l1 ==> P(a)) /\ (!a. MEM a l2 ==> P(a))
               ==> LEX (\x y. P(x) /\ P(y) /\ R x y) l1 l2`,
  GEN_TAC THEN GEN_TAC THEN REPEAT LIST_INDUCT_TAC THEN
  REWRITE_TAC[LEX; MEM] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subterm relationship.                                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("subterm",(12,"right"));;
parse_as_infix("psubterm",(12,"right"));;

let subterm_RULES,subterm_INDUCT,subterm_CASES = new_inductive_definition
  `(!t. t subterm t) /\
   (!s a f args. s subterm a /\ MEM a args ==> s subterm (Fn f args))`;;

let psubterm = new_definition
  `s psubterm t <=> s subterm t /\ ~(s = t)`;;

(* ------------------------------------------------------------------------- *)
(* A lemma we don't seem able to avoid.                                      *)
(* ------------------------------------------------------------------------- *)

let DESCENDANT_SMALLER = prove
 (`!f args s. MEM s args ==> termsize s < termsize (Fn f args)`,
  GEN_TAC THEN REWRITE_TAC[termsize] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP; ITLIST] THEN
  ASM_MESON_TAC[ARITH_RULE `0 < b ==> a < a + b`;
                ARITH_RULE `a < c ==> a < b + c`; ITLIST_ADD_1_POS]);;

let DESCENDANT_DISTINCT = prove
 (`!f args. ~(MEM (Fn f args) args)`,
  MESON_TAC[DESCENDANT_SMALLER; LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Trivial properties of subterm and psubterm relations.                     *)
(* ------------------------------------------------------------------------- *)

let SUBTERM_REFL = prove
 (`!t. t subterm t`,
  REWRITE_TAC[subterm_RULES]);;

let SUBTERM_TRANS = prove
 (`!s t u. s subterm t /\ t subterm u ==> s subterm u`,
  SUBGOAL_THEN `!t u. t subterm u ==> !s. s subterm t ==> s subterm u`
   (fun th -> MESON_TAC[th]) THEN MATCH_MP_TAC subterm_INDUCT THEN
  REWRITE_TAC[] THEN MESON_TAC[subterm_RULES]);;

let SUBTERM_ANTISYM = prove
 (`!s t. s subterm t /\ t subterm s ==> (s = t)`,
  MATCH_MP_TAC term_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[subterm_CASES] THEN SIMP_TAC[term_DISTINCT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[subterm_CASES] THEN REWRITE_TAC[term_INJ] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_MESON_TAC[subterm_RULES; SUBTERM_TRANS]);;

let SUBTERM_FVT = prove
 (`!x t. x IN FVT(t) ==> V(x) subterm t`,
  GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  SIMP_TAC[FVT; IN_SING; IN_LIST_UNION; SUBTERM_REFL] THEN
  REWRITE_TAC[MEM_MAP; GSYM EX_MEM; GSYM ALL_MEM] THEN
  MESON_TAC[subterm_RULES]);;

let PSUBTERM_ANTISYM = prove
 (`!s t. ~(s psubterm t /\ t psubterm s)`,
  REWRITE_TAC[psubterm] THEN MESON_TAC[SUBTERM_ANTISYM]);;

let SUBTERM_PSUBTERM_TRANS = prove
 (`!s t u. s subterm t /\ t psubterm u ==> s psubterm u`,
  REWRITE_TAC[psubterm] THEN MESON_TAC[SUBTERM_TRANS; SUBTERM_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Useful alternative characterization of psubterm.                          *)
(* ------------------------------------------------------------------------- *)

let PSUBTERM_CASES = prove
 (`!s t. s psubterm t <=>
         ?f args u. (t = Fn f args) /\ MEM u args /\ s subterm u`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[psubterm] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [subterm_CASES] THEN ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:num`; `args:term list`; `a:term`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBTERM_PSUBTERM_TRANS THEN
    EXISTS_TAC `a:term` THEN ASM_REWRITE_TAC[psubterm] THEN
    ASM_MESON_TAC[DESCENDANT_DISTINCT; subterm_RULES]]);;

(* ------------------------------------------------------------------------- *)
(* Stability of subterm relationships under instantiation.                   *)
(* ------------------------------------------------------------------------- *)

let SUBTERM_INSTANTIATION = prove
 (`!i s t. s subterm t ==> (termsubst i s) subterm (termsubst i t)`,
  GEN_TAC THEN MATCH_MP_TAC subterm_INDUCT THEN
  REWRITE_TAC[termsubst; subterm_RULES] THEN
  ASM_MESON_TAC[MEM_MAP; subterm_RULES]);;

let PSUBTERM_INSTANTIATION = prove
 (`!i s t. s psubterm t ==> (termsubst i s) psubterm (termsubst i t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[PSUBTERM_CASES] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num` THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`args:term list`; `u:term`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`MAP (termsubst i) args`; `termsubst i u`] THEN
  ASM_REWRITE_TAC[MEM_MAP; termsubst] THEN
  ASM_MESON_TAC[SUBTERM_INSTANTIATION]);;

(* ------------------------------------------------------------------------- *)
(* Inductive definition of the LPO.                                          *)
(* ------------------------------------------------------------------------- *)

let lpo_RULES,lpo_INDUCT,lpo_CASES = new_inductive_definition
  `(!x s. x IN FVT(s) /\ ~(s = V x) ==> V x << s) /\
   (!fs sargs ft targs si.
          MEM si sargs /\ (Fn ft targs << si \/ (si = Fn ft targs))
          ==> Fn ft targs << Fn fs sargs) /\
   (!fs ft sargs targs.
          (fs > ft \/ (fs = ft) /\ LENGTH sargs > LENGTH targs) /\
          ALL (\ti. ti << Fn fs sargs) targs
          ==> Fn ft targs << Fn fs sargs) /\
   (!f sargs targs.
          ALL (\ti. ti << Fn f sargs) targs /\ LEX(<<) targs sargs
          ==> Fn f targs << Fn f sargs)`;;

(* ------------------------------------------------------------------------- *)
(* Nicer cases theorem; essentially a recursive version of the definition.   *)
(* ------------------------------------------------------------------------- *)

let LPO_CASES = prove
 (`(!s x. (s << V x) <=> F) /\
   (!x t. V x << t <=> x IN FVT(t) /\ ~(t = V x)) /\
   (!f fargs g gargs.
          Fn f fargs << Fn g gargs <=>
                (?gi. MEM gi gargs /\
                      (Fn f fargs << gi \/ (Fn f fargs = gi))) \/
                (!fi. MEM fi fargs ==> fi << Fn g gargs) /\
                ((f < g \/ (f = g) /\ (LENGTH fargs < LENGTH gargs)) \/
                 (f = g) /\ LEX(<<) fargs gargs))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lpo_CASES] THEN
  REWRITE_TAC[term_DISTINCT; term_INJ; FVT; IN_SING; GSYM ALL_MEM; GT] THEN
  TRY(CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))) THEN
  REWRITE_TAC[TAUT `(a /\ b) /\ c <=> ~(a /\ b ==> ~c)`] THEN
  SIMP_TAC[] THEN REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* LPO does not introduce new variables.                                     *)
(* ------------------------------------------------------------------------- *)

let LPO_FVT = prove
 (`!s t. s << t ==> FVT(s) SUBSET FVT(t)`,
  MATCH_MP_TAC lpo_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ALL_TAC; SPEC_TAC(`Fn ft targs`,`t:term`); ALL_TAC; ALL_TAC] THEN
  SIMP_TAC[FVT; SUBSET; IN_SING; IN_LIST_UNION;
           GSYM EX_MEM; GSYM ALL_MEM; MEM_MAP] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* LPO is transitive (quite a tedious proof; follows Baader & Nipkow).       *)
(* ------------------------------------------------------------------------- *)

let LPO_TRANS_INDUCT = prove
 (`!n r s t.
        (termsize r + termsize s + termsize t = n) /\ t << s /\ s << r
        ==> t << r`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISJ_CASES_THEN MP_TAC (SPEC `t:term` term_CASES) THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:num` SUBST_ALL_TAC) THEN STRIP_TAC THEN
    MATCH_MP_TAC(el 0 (CONJUNCTS lpo_RULES)) THEN CONJ_TAC THENL
     [MP_TAC(MATCH_MP LPO_FVT (ASSUME `V x << s`)) THEN
      MP_TAC(MATCH_MP LPO_FVT (ASSUME `s << r`)) THEN
      REWRITE_TAC[FVT; SUBSET; IN_SING] THEN MESON_TAC[];
      ASM_MESON_TAC[LPO_CASES]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num` (X_CHOOSE_THEN `ts:term list`
    SUBST_ALL_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
  DISJ_CASES_THEN MP_TAC (SPEC `r:term` term_CASES) THENL
   [ASM_MESON_TAC[LPO_CASES]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `rs:term list`
    SUBST_ALL_TAC)) THEN
  DISJ_CASES_THEN MP_TAC (SPEC `s:term` term_CASES) THENL
   [ASM_MESON_TAC[LPO_CASES]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num` (X_CHOOSE_THEN `ss:term list`
    SUBST_ALL_TAC)) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP]) THEN
  ASM_CASES_TAC `?ri. MEM ri rs /\ (Fn g ss << ri \/ (Fn g ss = ri))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `ri:term`
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    MATCH_MP_TAC(el 1 (CONJUNCTS lpo_RULES)) THEN
    EXISTS_TAC `ri:term` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `termsize ri + termsize(Fn g ss) + termsize (Fn h ts)` THEN
    EXISTS_TAC `Fn g ss` THEN ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
    MATCH_MP_TAC DESCENDANT_SMALLER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!si. MEM si ss ==> si << Fn f rs` ASSUME_TAC THENL
   [UNDISCH_TAC `Fn g ss << Fn f rs` THEN
    GEN_REWRITE_TAC LAND_CONV [lpo_CASES] THEN
    REWRITE_TAC[term_DISTINCT; term_INJ; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `?si. MEM si ss /\ (Fn h ts << si \/ (Fn h ts = si))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `si:term`
     (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN EXISTS_TAC
      `termsize(Fn f rs) + termsize si + termsize (Fn h ts)`) THEN
    EXISTS_TAC `si:term` THEN
    ASM_SIMP_TAC[LT_ADD_LCANCEL; LT_ADD_RCANCEL] THEN
    MATCH_MP_TAC DESCENDANT_SMALLER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!ti. MEM ti ts ==> ti << Fn g ss` ASSUME_TAC THENL
   [UNDISCH_TAC `Fn h ts << Fn g ss` THEN
    GEN_REWRITE_TAC LAND_CONV [lpo_CASES] THEN
    REWRITE_TAC[term_DISTINCT; term_INJ; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!ti. MEM ti ts ==> ti << Fn f rs` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN EXISTS_TAC
     `termsize (Fn f rs) + termsize (Fn g ss) + termsize ti`) THEN
    EXISTS_TAC `Fn g ss` THEN
    ASM_SIMP_TAC[LT_ADD_LCANCEL; DESCENDANT_SMALLER]; ALL_TAC] THEN
  UNDISCH_TAC `Fn h ts << Fn g ss` THEN UNDISCH_TAC `Fn g ss << Fn f rs` THEN
  ONCE_REWRITE_TAC[LPO_CASES] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [ASM_MESON_TAC[LT_TRANS; LEX_LENGTH]; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [ASM_MESON_TAC[LT_TRANS; LEX_LENGTH]; ALL_TAC] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!r s t. MEM r rs /\ MEM s ss /\ MEM t ts /\
            t << s /\ s << r ==> t << r`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:term`; `b:term`; `c:term`] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN EXISTS_TAC
     `termsize a + termsize b + termsize c`) THEN
    EXISTS_TAC `b:term` THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC LT_ADD2 THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[DESCENDANT_SMALLER]; ALL_TAC] THEN
  MAP_EVERY(fun s -> SPEC_TAC(s,s))
   [`rs:term list`; `ss:term list`; `ts:term list`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC[LEX; MEM] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(ASM (GEN_MESON_TAC 0 15 1) [LEX_LENGTH]) THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(a1 /\ a2 ==> a3) /\ (b1 ==> b2 ==> b3)
                     ==> a1 /\ b1 ==> a2 /\ b2 ==> a3 /\ b3`) THEN
  SIMP_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let LPO_TRANS = prove
 (`!s t u. s << t /\ t << u ==> s << u`,
  MESON_TAC[LPO_TRANS_INDUCT]);;

(* ------------------------------------------------------------------------- *)
(* LPO has the subterm property.                                             *)
(* ------------------------------------------------------------------------- *)

let LPO_SUBTERM_LEMMA = prove
 (`!f args a. MEM a args ==> a << Fn f args`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  ONCE_REWRITE_TAC[LPO_CASES] THEN CONJ_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  REWRITE_TAC[FVT; IN_LIST_UNION; GSYM EX_MEM; GSYM ALL_MEM; MEM_MAP] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN REWRITE_TAC[term_DISTINCT] THEN
  EXISTS_TAC `FVT(V x)` THEN REWRITE_TAC[FVT; IN_SING] THEN
  EXISTS_TAC `V x` THEN ASM_REWRITE_TAC[FVT]);;

let LPO_SUBTERM = prove
 (`!s t. s subterm t ==> (s = t) \/ s << t`,
  MATCH_MP_TAC subterm_INDUCT THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[LPO_SUBTERM_LEMMA];
    DISJ2_TAC THEN MATCH_MP_TAC LPO_TRANS THEN
    EXISTS_TAC `a:term` THEN ASM_SIMP_TAC[LPO_SUBTERM_LEMMA]]);;

let LPO_PSUBTERM = prove
 (`!s t. s psubterm t ==> s << t`,
  REWRITE_TAC[psubterm] THEN MESON_TAC[LPO_SUBTERM]);;

(* ------------------------------------------------------------------------- *)
(* LPO is compatible with instantiation.                                     *)
(* ------------------------------------------------------------------------- *)

let LPO_INSTANTIATION = prove
 (`!i s t. s << t ==> termsubst i s << termsubst i t`,
  GEN_TAC THEN MATCH_MP_TAC lpo_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [MATCH_MP_TAC LPO_PSUBTERM THEN MATCH_MP_TAC PSUBTERM_INSTANTIATION THEN
    ASM_REWRITE_TAC[psubterm] THEN ASM_SIMP_TAC[SUBTERM_FVT];
    REWRITE_TAC[termsubst] THEN
    MATCH_MP_TAC(el 1 (CONJUNCTS lpo_RULES)) THEN
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[termsubst];
    REWRITE_TAC[termsubst] THEN
    MATCH_MP_TAC(el 2 (CONJUNCTS lpo_RULES)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM]) THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; termsubst; LENGTH_MAP] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[termsubst] THEN
    MATCH_MP_TAC(el 3 (CONJUNCTS lpo_RULES)) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ALL_MAP; o_DEF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[termsubst]) THEN ASM_SIMP_TAC[LEX_MAP]]);;

(* ------------------------------------------------------------------------- *)
(* LPO is a congruence.                                                      *)
(* ------------------------------------------------------------------------- *)

let LPO_CONGRUENCE = prove
 (`!s t. s << t
         ==> Fn f (APPEND largs (CONS s rargs))
              << Fn f (APPEND largs (CONS t rargs))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(last(CONJUNCTS lpo_RULES)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `u:term` THEN DISCH_TAC THEN
    ASM_CASES_TAC `u:term = s` THENL
     [MATCH_MP_TAC LPO_TRANS THEN EXISTS_TAC `t:term` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LPO_PSUBTERM THEN
      ONCE_REWRITE_TAC[PSUBTERM_CASES] THEN
      MAP_EVERY EXISTS_TAC
       [`f:num`; `APPEND largs (CONS (t:term) rargs)`; `t:term`] THEN
      ASM_REWRITE_TAC[MEM; SUBTERM_REFL; MEM_APPEND];
      MATCH_MP_TAC LPO_PSUBTERM THEN ONCE_REWRITE_TAC[PSUBTERM_CASES] THEN
      MAP_EVERY EXISTS_TAC
       [`f:num`; `APPEND largs (CONS (t:term) rargs)`; `u:term`] THEN
      REWRITE_TAC[SUBTERM_REFL] THEN
      ASM_MESON_TAC[MEM; MEM_APPEND]];
    SPEC_TAC(`largs:term list`,`largs:term list`) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LEX; APPEND] THEN
    COND_CASES_TAC THEN REWRITE_TAC[LENGTH; LENGTH_APPEND]]);;

(* ------------------------------------------------------------------------- *)
(* LPO is irreflexive.                                                       *)
(* ------------------------------------------------------------------------- *)

let LPO_REFL = prove
 (`!t. ~(t << t)`,
  MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[LPO_CASES] THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ALL_MEM; LT_REFL] THEN
  ASM_SIMP_TAC[LEX_REFL] THEN
  ASM_MESON_TAC[LPO_PSUBTERM; LPO_TRANS;
    PSUBTERM_CASES; SUBTERM_REFL; DESCENDANT_SMALLER; LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* LPO is wellfounded over a finite signature.                               *)
(* ------------------------------------------------------------------------- *)

let LPO_WF = prove
 (`!A. FINITE(A)
       ==> WF(\s t. functions_term(s) SUBSET A /\
                    functions_term(t) SUBSET A /\
                    s << t)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL WF_MINIMAL_DCHAIN)))) THEN
  EXISTS_TAC `termsize` THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->term`
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
    `!n:num. ?f args. (t(n) = Fn f args) /\
                      ALL (\t. ~(NONWF(\s t. functions_term(s) SUBSET A /\
                                             functions_term(t) SUBSET A /\
                                             s << t) t)) args`
  MP_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `(t:num->term) n` term_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [ASM_MESON_TAC[LPO_CASES]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `args:term list` THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `u:term` THEN DISCH_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `n = 0` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `u:term`) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
      ASM_SIMP_TAC[NOT_LE; DESCENDANT_SMALLER]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `u:term`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> (SUC(n - 1) = n)`] THEN
    REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; NOT_LE] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_THEN
       `!n:num. functions_term (t n) SUBSET A` (MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[functions_term; SUBSET; IN_LIST_UNION; IN_INSERT;
                      MEM_MAP; GSYM EX_MEM] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC LPO_TRANS THEN EXISTS_TAC `(t:num->term)(n)` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LPO_PSUBTERM THEN
        ONCE_REWRITE_TAC[PSUBTERM_CASES] THEN
        MAP_EVERY EXISTS_TAC [`f:num`; `args:term list`; `u:term`] THEN
        ASM_REWRITE_TAC[SUBTERM_REFL];
        FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
         [MATCH_MP (ARITH_RULE `~(n = 0) ==> (n = SUC(n - 1))`) th]) THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC DESCENDANT_SMALLER THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; GSYM ALL_MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `fn:num->num` (X_CHOOSE_THEN `args:num->term list`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?far:num#num s. subseq s /\
                    (!n:num. fn(s n),LENGTH(args(s n):term list) = far)`
  MP_TAC THENL
   [MATCH_MP_TAC SEQUENCE_PARTITION_LEMMA THEN
    EXISTS_TAC `A:num#num->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN
    UNDISCH_TAC `!n:num. functions_term (t n) SUBSET A` THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[SUBSET] o SPEC `n:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[functions_term; IN_INSERT];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [EXISTS_PAIR_THM] THEN
  REWRITE_TAC[PAIR_EQ; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num` (X_CHOOSE_THEN `ar:num`
   (X_CHOOSE_THEN `k:num->num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!m n. m <= n ==> t(n) << t(m) \/ (t(n) = t(m))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `!n d. t(n + d) << t(n) \/ (t(n + d) = t(n))`
     (fun th -> MESON_TAC[th; LE_EXISTS]) THEN
    GEN_TAC THEN  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_MESON_TAC[LPO_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> t(n) << t(m)` MP_TAC THENL
   [REWRITE_TAC[GSYM LE_SUC_LT] THEN
    ASM_MESON_TAC[LPO_TRANS]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o
    SPECL [`(k:num->num) n`; `k(SUC n):num`]) THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [SUBSEQ_SUC]) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[LPO_CASES] THEN
  REWRITE_TAC[LT_REFL] THEN
  SUBGOAL_THEN `!a n:num. MEM a (args n) ==> functions_term a SUBSET A`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    UNDISCH_THEN
         `!n:num. functions_term (t n) SUBSET A`
         (MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[functions_term; SUBSET; IN_LIST_UNION; IN_INSERT;
                    MEM_MAP; GSYM EX_MEM] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n a. ~(MEM a (args ((k:num->num) n)) /\
            (Fn f (args (k (SUC n))) << a \/ (Fn f (args (k (SUC n))) = a)))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    MATCH_MP_TAC(TAUT `(a ==> b) ==> ~a \/ b`) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [NONWF] o
              C MATCH_MP (ASSUME
     `MEM (a:term) (args((k:num->num) n))`)) THEN
    REWRITE_TAC[NONWF; TAUT `~p ==> ~q /\ ~r <=> q \/ r ==> p`] THEN
    DISCH_TAC THEN EXISTS_TAC
     `\r:num. if r = 0 then a:term else t(k(SUC n) + r)` THEN
    REWRITE_TAC[NOT_SUC] THEN X_GEN_TAC `m:num` THEN
    COND_CASES_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`k(SUC n):num`; `k(SUC n) + m`]) THEN
      REWRITE_TAC[LE_ADD] THEN UNDISCH_TAC `!n:num. t(SUC n) << t n` THEN
      DISCH_THEN(MP_TAC o SPEC `k(SUC n) + m`) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[LPO_TRANS]; ALL_TAC] THEN
    ASM_MESON_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(\s t.
                     functions_term s SUBSET A /\
                     functions_term t SUBSET A /\
                     s << t)`; `\n:num. (args:num->term list)(k n)`]
    WF_LEX_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN MATCH_MP_TAC LEX_RESTRICT THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Converse subterm property (not really needed, in fact).                   *)
(* ------------------------------------------------------------------------- *)

let LPO_SUBTERM_NOT = prove
 (`!t s. s subterm t ==> ~(t << s)`,
  MESON_TAC[LPO_SUBTERM; LPO_TRANS; LPO_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Completeness on ground terms.                                             *)
(* ------------------------------------------------------------------------- *)

let LEX_TOTAL = prove
 (`!fargs gargs.
        (LENGTH fargs = LENGTH gargs) /\
        (!fi gi. MEM fi fargs /\ MEM gi gargs
                 ==> fi << gi \/ gi << fi \/ (fi = gi))
        ==> LEX(<<) fargs gargs \/ LEX(<<) gargs fargs \/ (fargs = gargs)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LEX; MEM; LENGTH; NOT_SUC] THEN
  CONJ_TAC THENL [MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:term`; `ss:term list`] THEN DISCH_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LEX; MEM; LENGTH; NOT_SUC] THEN
  MAP_EVERY X_GEN_TAC [`t:term`; `ts:term list`] THEN
  DISCH_THEN(K ALL_TAC) THEN SIMP_TAC[SUC_INJ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `ts:term list`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[]);;

let LPO_GROUND_COMPLETE = prove
 (`!s t. (FVT(s) = {}) /\ (FVT(t) = {}) ==> s << t \/ t << s \/ (s = t)`,
  SUBGOAL_THEN
    `!n s t. (termsize(s) + termsize(t) = n) /\ (FVT(s) = {}) /\ (FVT(t) = {})
             ==> s << t \/ t << s \/ (s = t)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[FVT; EXTENSION; IN_SING; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`f:num`; `fargs:term list`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[FVT; EXTENSION; IN_SING; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:num`; `gargs:term list`] THEN
  DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!fi. MEM fi fargs
          ==> fi << Fn g gargs \/ Fn g gargs << fi \/ (fi = Fn g gargs)) /\
    (!gi. MEM gi gargs
          ==> gi << Fn f fargs \/ Fn f fargs << gi \/ (gi = Fn f fargs)) /\
    (!fi gi. MEM fi fargs /\ MEM gi gargs
          ==> fi << gi \/ gi << fi \/ (fi = gi))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_THEN `termsize (Fn f fargs) + termsize (Fn g gargs) = n`
        (SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM;
                  IMP_IMP]) THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> b /\ a /\ c /\ d`] THEN
    REWRITE_TAC[UNWIND_THM1] THEN
    ASM_SIMP_TAC[LT_ADD_LCANCEL; LT_ADD_RCANCEL; DESCENDANT_SMALLER;
                 ARITH_RULE `a + b < b + c <=> a < c`; LT_ADD2] THEN
    ASM_MESON_TAC[FVT_FUN_EMPTY];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[LPO_CASES] THEN
  SUBGOAL_THEN
   `(?a. MEM a gargs /\ (Fn f fargs << a \/ (Fn f fargs = a))) \/
    ~(?a. MEM a gargs /\ (Fn f fargs << a \/ (Fn f fargs = a))) /\
    (!a. MEM a gargs ==> a << Fn f fargs)`
  DISJ_CASES_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(?a. MEM a fargs /\ (Fn g gargs << a \/ (Fn g gargs = a))) \/
    ~(?a. MEM a fargs /\ (Fn g gargs << a \/ (Fn g gargs = a))) /\
    (!a. MEM a fargs ==> a << Fn g gargs)`
  DISJ_CASES_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[term_INJ] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`f:num`; `g:num`] LT_CASES) THEN
  ASM_REWRITE_TAC[LT_REFL] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`LENGTH(fargs:term list)`; `LENGTH(gargs:term list)`] LT_CASES) THEN
  ASM_REWRITE_TAC[LT_REFL] THEN
  MATCH_MP_TAC LEX_TOTAL THEN ASM_SIMP_TAC[]);;
