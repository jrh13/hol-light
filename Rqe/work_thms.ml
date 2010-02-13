let rec DISJ_TAC thm = DISJ_CASES_TAC thm THENL[ALL_TAC;TRY (POP_ASSUM DISJ_TAC)];;  

let INTERPSIGNS_CONJ = prove_by_refinement(
  `!P Q eqs l. 
    interpsigns eqs (\x. P x) l /\ 
    interpsigns eqs (\x. Q x) l ==> 
    interpsigns eqs (\x. P x \/ Q x) l`,
(* {{{ Proof *)

[
  STRIP_TAC THEN STRIP_TAC;
  REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC[interpsigns;ALL2;interpsign];
  REPEAT (POP_ASSUM MP_TAC);
  DISJ_TAC (ISPEC `h':sign` SIGN_CASES) THEN ASM_REWRITE_TAC[interpsign;interpsigns] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
]);;

(* }}} *)

let INTERPMAT_TRIO = prove_by_refinement( 
  `!eqs x y l r t.  
    interpmat (CONS x (CONS y t)) eqs (CONS l (CONS l (CONS l r))) ==>  
    interpmat (CONS y t) eqs (CONS l r)`, 
(* {{{ Proof *)

[ 
  REWRITE_TAC[interpmat;partition_line;NOT_CONS_NIL;ALL2;HD;TL;APPEND]; 
  REPEAT_N 6 STRIP_TAC; 
  DISJ_CASES_TAC (ISPEC `t:real list` list_CASES);
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  MATCH_ACCEPT_TAC ROL_SING; 
  REWRITE_TAC[ALL2];
  REWRITE_ASSUMS[TL];
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  EXISTS_TAC `\z. z < x \/ (z = x) \/ (x < z /\ z < y)`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[NOT_CONS_NIL;TL];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[ROL_TAIL;TL;NOT_CONS_NIL;];
  REWRITE_TAC[ALL2];
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  EXISTS_TAC `\z. z < x \/ (z = x) \/ (x < z /\ z < y)`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
]);;  

(* }}} *)

let PARTITION_LINE_NOT_NIL = prove_by_refinement(
  `!l. ~(partition_line l = [])`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[partition_line;NOT_CONS_NIL;];
  REWRITE_TAC[partition_line];
  COND_CASES_TAC;
  REWRITE_TAC[NOT_CONS_NIL];
  ASM_MESON_TAC[APPEND_EQ_NIL;NOT_CONS_NIL];
]);;

(* }}} *)

let ALL2_LENGTH = prove_by_refinement(
  `!P l1 l2. ALL2 P l1 l2 ==> (LENGTH l1 = LENGTH l2)`,
(* {{{ Proof *)
[
  STRIP_TAC;
  REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2;LENGTH];
  ASM_MESON_TAC[];
]);;  
(* }}} *)

let LENGTH_TL = prove_by_refinement( 
   `!l:A list. ~(l = []) ==> (LENGTH (TL l) = PRE (LENGTH l))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REWRITE_TAC[NOT_CONS_NIL;TL;LENGTH;];
  ARITH_TAC;
]);;
(* }}} *)

let PARTITION_LINE_LENGTH = prove_by_refinement(
  `!l. LENGTH (partition_line l) = 2 * LENGTH l + 1`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[partition_line;LENGTH;];
  ARITH_TAC;
  REWRITE_TAC[partition_line;LENGTH;];
  COND_CASES_TAC;
  ASM_REWRITE_TAC[LENGTH;];
  ARITH_TAC;
  REWRITE_TAC[APPEND;LENGTH;];
  ASM_SIMP_TAC[PARTITION_LINE_NOT_NIL;LENGTH_TL];
  ARITH_TAC;
]);;

(* }}} *)

let PARTITION_LINE_LENGTH_TL = prove_by_refinement(
  `!l. LENGTH (TL (partition_line l)) = 2 * LENGTH l`,
(* {{{ Proof *)
[
  STRIP_TAC;
  REWRITE_TAC[MATCH_MP LENGTH_TL (ISPEC `l:real list` PARTITION_LINE_NOT_NIL)]; 
  REWRITE_TAC[PARTITION_LINE_LENGTH];
  ARITH_TAC;
]);;
(* }}} *)

let PL_ALL2_LENGTH = prove_by_refinement(
  `!eqs pts sgns. ALL2 (interpsigns eqs) (partition_line pts) sgns ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1)`,
(* {{{ Proof *)

[
  REPEAT_N 3 STRIP_TAC;
  DISJ_CASES_TAC (ISPEC `pts:real list` list_CASES);
  ASM_REWRITE_TAC[interpmat;LENGTH;ROL_NIL;partition_line;];
  ARITH_SIMP_TAC[];
  DISJ_CASES_TAC (ISPEC `sgns:(sign list) list` list_CASES);
  ASM_REWRITE_TAC[ALL2];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[ALL2];  
  DISJ_CASES_TAC (ISPEC `t:(sign list) list` list_CASES);
  ASM_REWRITE_TAC[ALL2;LENGTH;ONE];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[ALL2];  
  (* save *) 
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[interpmat;partition_line;];
  COND_CASES_TAC;
  ASM_REWRITE_TAC[ROL_SING;LENGTH;GSYM ONE];
  ARITH_SIMP_TAC[];
  STRIP_TAC;
  CLAIM `LENGTH [\x. x < h; \x. x = h; \x. h < x] = LENGTH sgns`;
  ASM_MESON_TAC[ALL2_LENGTH];
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  REWRITE_ASSUMS[NOT_NIL];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  REWRITE_TAC[LENGTH];
  STRIP_TAC;
  CLAIM `LENGTH sgns = LENGTH (APPEND [\x. x < h; \x. x = h; \x. h < x /\ x < HD t] (TL (partition_line t)))`;
  ASM_MESON_TAC[ ALL2_LENGTH];
  DISCH_THEN SUBST1_TAC;
  REWRITE_TAC[LENGTH_APPEND];
  REWRITE_TAC[PARTITION_LINE_LENGTH_TL];
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
]);;

(* }}} *)

let INTERPMAT_LENGTH = prove_by_refinement(
 `!eqs pts sgns. interpmat pts eqs sgns ==> 
    (LENGTH sgns = 2 * LENGTH pts + 1)`,
(* {{{ Proof *)

[
  REPEAT_N 3 STRIP_TAC;
  DISJ_CASES_TAC (ISPEC `pts:real list` list_CASES);
  ASM_REWRITE_TAC[interpmat;LENGTH;ROL_NIL;partition_line;];
  ARITH_SIMP_TAC[];
  DISJ_CASES_TAC (ISPEC `sgns:(sign list) list` list_CASES);
  ASM_REWRITE_TAC[ALL2];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[ALL2];  
  DISJ_CASES_TAC (ISPEC `t:(sign list) list` list_CASES);
  ASM_REWRITE_TAC[ALL2;LENGTH;ONE];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[ALL2];  
  (* save *) 
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[interpmat;partition_line;];
  COND_CASES_TAC;
  ASM_REWRITE_TAC[ROL_SING;LENGTH;GSYM ONE];
  ARITH_SIMP_TAC[];
  STRIP_TAC;
  CLAIM `LENGTH [\x. x < h; \x. x = h; \x. h < x] = LENGTH sgns`;
  ASM_MESON_TAC[ALL2_LENGTH];
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  REWRITE_ASSUMS[NOT_NIL];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  REWRITE_TAC[LENGTH];
  STRIP_TAC;
  CLAIM `LENGTH sgns = LENGTH (APPEND [\x. x < h; \x. x = h; \x. h < x /\ x < HD t] (TL (partition_line t)))`;
  ASM_MESON_TAC[ ALL2_LENGTH];
  DISCH_THEN SUBST1_TAC;
  REWRITE_TAC[LENGTH_APPEND];
  REWRITE_TAC[PARTITION_LINE_LENGTH_TL];
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
]);;

(* }}} *)

let ALL2_HD = prove_by_refinement(
  `!b d a c. (LENGTH a = LENGTH c) ==> 
    ALL2 P (APPEND a b) (APPEND c d) ==> ALL2 P a c`,
(* {{{ Proof *)

[
  REPEAT_N 2 STRIP_TAC;
  LIST_INDUCT_TAC;
  ONCE_REWRITE_TAC[prove(`(x = y) <=> (y = x)`,MESON_TAC[])]; 
  REWRITE_TAC[LENGTH;LENGTH_EQ_NIL];
  MESON_TAC[ALL2];
  REWRITE_TAC[LENGTH;APPEND;];
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  REWRITE_TAC[LENGTH;APPEND;ALL2;SUC_INJ];
  ASM_MESON_TAC[];
]);;

(* }}} *)

let ALL2_TL = prove_by_refinement(
  `!b d a c. (LENGTH a = LENGTH c) ==> 
    ALL2 P (APPEND a b) (APPEND c d) ==> ALL2 P b d`,
(* {{{ Proof *)
[
  REPEAT_N 2 STRIP_TAC;
  LIST_INDUCT_TAC;
  ONCE_REWRITE_TAC[prove(`(x = y) <=> (y = x)`,MESON_TAC[])]; 
  REWRITE_TAC[LENGTH;LENGTH_EQ_NIL];
  MESON_TAC[APPEND];
  REWRITE_TAC[LENGTH;APPEND;];
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  REWRITE_TAC[ALL2;APPEND;LENGTH;SUC_INJ];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let ALL2_APPEND_LENGTH = prove_by_refinement(
  `!P a c b d. (LENGTH a = LENGTH c) ==> 
    ALL2 P (APPEND a b) (APPEND c d) ==> ALL2 P a c /\ ALL2 P b d`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[ALL2_HD;ALL2_TL];
]);;
(* }}} *)

let ALL2_APPEND = prove_by_refinement(
  `!a c b d. ALL2 P a c /\ ALL2 P b d ==> 
      ALL2 P (APPEND a b) (APPEND c d)`,
(* {{{ Proof *)
[
  REPEAT LIST_INDUCT_TAC THEN REWRITE_ALL[APPEND;ALL2;LENGTH;ARITH_RULE `~(0 = SUC x)`;APPEND_NIL];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[ALL2];
]);;
(* }}} *)

let ALL2_SPLIT = prove_by_refinement(
  `!a c b d. (LENGTH a = LENGTH c) ==> 
    (ALL2 P (APPEND a b) (APPEND c d) <=> ALL2 P a c /\ ALL2 P b d)`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[ALL2_APPEND;ALL2_APPEND_LENGTH];
]);;
(* }}} *)

let BUTLAST = new_recursive_definition list_RECURSION
  `(BUTLAST [] = []) /\ 
   (BUTLAST (CONS h t) = if t = [] then [] else CONS h (BUTLAST t))`;;

let BUTLAST_THM = prove_by_refinement(
  `(BUTLAST [] = []) /\ 
   (BUTLAST [x] = []) /\ 
   (BUTLAST (CONS h1 (CONS h2 t)) = CONS h1 (BUTLAST (CONS h2 t)))`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[BUTLAST;NOT_CONS_NIL;];
]);;
(* }}} *)

let HD_BUTLAST = prove_by_refinement(
  `!l. ~(l = []) ==> (!x. ~(l = [x])) ==> (HD (BUTLAST l) = HD l)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REWRITE_TAC[NOT_CONS_NIL;HD;BUTLAST];
  COND_CASES_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  REPEAT STRIP_TAC;
  REWRITE_TAC[HD];
]);;
(* }}} *)


let SUBLIST = new_recursive_definition list_RECURSION
  `(SUBLIST l [] <=> (l = [])) /\ 
   (SUBLIST l (CONS h t) <=> (l = []) \/ 
    SUBLIST l t \/  
    ((HD l = h) /\ SUBLIST (TL l) t))`;;

let SUBLIST_NIL = prove_by_refinement(
  `!l. SUBLIST [] l`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN 
  ASM_MESON_TAC[SUBLIST];
]);;
(* }}} *)

let SUBLIST_CONS = prove_by_refinement(
  `!l1 l2 h. SUBLIST l1 l2 ==> SUBLIST l1 (CONS h l2)`,
(* {{{ Proof *)
[
  REPEAT LIST_INDUCT_TAC THEN ASM_MESON_TAC[SUBLIST];
]);; 
(* }}} *)

let SUBLIST_TL = prove_by_refinement(
  `!l1 l2. SUBLIST l1 l2 ==> ~(l1 = []) ==> SUBLIST (TL l1) l2`,
(* {{{ Proof *)
[
  REPEAT LIST_INDUCT_TAC THEN ASM_MESON_TAC[SUBLIST;]
]);;
(* }}} *)

let SUBLIST_CONS2 = prove_by_refinement(
  `!h t l. SUBLIST (CONS h t) l ==> SUBLIST t l`,
(* {{{ Proof *)
[
  STRIP_TAC;
  REPEAT LIST_INDUCT_TAC THEN ASM_MESON_TAC[SUBLIST;NOT_CONS_NIL;HD;TL];
]);;
(* }}} *)

let SUBLIST_ID = prove_by_refinement(
  `!l. SUBLIST l l`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN ASM_MESON_TAC[SUBLIST;SUBLIST_NIL;NOT_CONS_NIL;HD;TL];
]);;
(* }}} *)

let SUBLIST_CONS_CONS = prove_by_refinement(
  `!h t1 t2. SUBLIST (CONS h t1) (CONS h t2) = SUBLIST t1 t2`,
(* {{{ Proof *)
[
  STRIP_TAC;
  REPEAT LIST_INDUCT_TAC;
  ASM_MESON_TAC[SUBLIST;SUBLIST_NIL;SUBLIST_ID];
  ASM_MESON_TAC[SUBLIST;SUBLIST_NIL;SUBLIST_ID];
  REWRITE_TAC[SUBLIST;SUBLIST_NIL;SUBLIST_ID;NOT_CONS_NIL;HD;TL];
  REWRITE_TAC[SUBLIST;SUBLIST_NIL;SUBLIST_ID;NOT_CONS_NIL;HD;TL;SUBLIST_CONS2;SUBLIST_CONS];
  ASM_MESON_TAC[SUBLIST;SUBLIST_NIL;SUBLIST_ID;NOT_CONS_NIL;HD;TL];
]);;
(* }}} *)

let SUBLIST_NEQ = prove_by_refinement(
  `!h1 h2 t1 t2. SUBLIST (CONS h1 t1) (CONS h2 t2) ==> ~(h1 = h2) ==> 
     SUBLIST (CONS h1 t1) t2`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[SUBLIST;NOT_CONS_NIL;HD;TL];
]);;
(* }}} *)

let SUBLIST_TRANS = prove_by_refinement(
  `!l1 l2 l3. SUBLIST l1 l2 ==> SUBLIST l2 l3 ==> SUBLIST l1 l3`, 
(* {{{ Proof *)
[
  REPEAT LIST_INDUCT_TAC;
  ASM_MESON_TAC[SUBLIST];
  ASM_MESON_TAC[SUBLIST];
  ASM_MESON_TAC[SUBLIST];
  ASM_MESON_TAC[SUBLIST];
  ASM_MESON_TAC[SUBLIST];
  ASM_MESON_TAC[SUBLIST];
  ASM_MESON_TAC[SUBLIST];
  REPEAT STRIP_TAC;
  REWRITE_TAC[SUBLIST;NOT_CONS_NIL;HD;TL];
  CASES_ON `h = h''`;
  DISJ2_TAC;
  ASM_REWRITE_TAC[];
  POP_ASSUM (REWRITE_ALL o list);
  CASES_ON `h' = h''`;
  POP_ASSUM (REWRITE_ALL o list);
  ASM_MESON_TAC[SUBLIST_CONS_CONS];
  REWRITE_ASSUMS[IMP_AND_THM];
  FIRST_ASSUM MATCH_MP_TAC;
  EVERY_ASSUM (fun x -> try MP_TAC (MATCH_MP SUBLIST_CONS2 x) with _ -> ALL_TAC);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[SUBLIST;NOT_CONS_NIL;HD;TL;SUBLIST_CONS;SUBLIST_CONS2];
  DISJ1_TAC;
  CASES_ON `h' = h''`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ASSUMS[SUBLIST_CONS_CONS];
  CLAIM `SUBLIST (CONS h t) t'`;
  ASM_MESON_TAC[SUBLIST_NEQ];
  STRIP_TAC;
  ASM_MESON_TAC[];
  CASES_ON `h = h'`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ASSUMS[SUBLIST_CONS_CONS];
  ASM_MESON_TAC[SUBLIST_NEQ];
  CLAIM `SUBLIST (CONS h t) t'`;
  ASM_MESON_TAC[SUBLIST_NEQ];
  STRIP_TAC;
  CLAIM `SUBLIST (CONS h' t') t''`;
  ASM_MESON_TAC[SUBLIST_NEQ];
  STRIP_TAC;
  CLAIM `SUBLIST t' t''`;
  ASM_MESON_TAC[SUBLIST_CONS2];
  STRIP_TAC;
  ASM_MESON_TAC[];
]);;  
(* }}} *)

let ROL_MEM = prove_by_refinement(
  `!h t. real_ordered_list (CONS h t) ==> !x. MEM x t ==> h < x`,
(* {{{ Proof *)
[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[MEM];
  REPEAT STRIP_TAC;
  CASES_ON `x = h'`;
  POP_ASSUM (REWRITE_ALL o list);
  ASM_MESON_TAC[ROL_CONS_CONS];
  CLAIM `real_ordered_list (CONS h t)`;
  ASM_MESON_TAC[ROL_CONS_CONS_DELETE];
  DISCH_THEN (REWRITE_ASSUMS o list);
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[MEM];
]);;
(* }}} *)

let SUBLIST_MEM = prove_by_refinement(
  `!x l1 l2. SUBLIST l1 l2 ==> MEM x l1 ==> MEM x l2`,
(* {{{ Proof *)
[
  STRIP_TAC;
  REPEAT LIST_INDUCT_TAC;
  REWRITE_TAC[MEM];
  REWRITE_TAC[MEM];
  REWRITE_TAC[SUBLIST;NOT_CONS_NIL;];
  REPEAT STRIP_TAC;
  CASES_ON `h = h'`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ASSUMS[SUBLIST_CONS_CONS];
  CASES_ON `x = h'`;
  ASM_MESON_TAC[MEM];
  REWRITE_ASSUMS[IMP_AND_THM];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[MEM;SUBLIST_CONS];
  CASES_ON `x = h'`;
  ASM_MESON_TAC[MEM];
  ASM_MESON_TAC[SUBLIST_NEQ;SUBLIST;MEM];
]);;  
(* }}} *)

let ROL_SUBLIST_LT = prove_by_refinement(
  `!h t1 t2. real_ordered_list (CONS h t2) ==> 
      SUBLIST (CONS h t1) (CONS h t2) ==> !x. MEM x t1 ==> h < x`, 
(* {{{ Proof *)
[
  STRIP_TAC;
  REPEAT LIST_INDUCT_TAC;
  REWRITE_TAC[MEM];
  REWRITE_TAC[MEM];
  ASM_MESON_TAC[SUBLIST;NOT_CONS_NIL;HD;TL];
  REPEAT STRIP_TAC;
  REWRITE_ASSUMS[SUBLIST_CONS_CONS];
  CLAIM `MEM x (CONS h'' t')`;
  ASM_MESON_TAC[SUBLIST_MEM];
  STRIP_TAC;
  ASM_MESON_TAC[ROL_MEM];
]);;
(* }}} *)

let SUBLIST_DELETE = prove_by_refinement(
  `!h1 h2 t l. SUBLIST (CONS h1 (CONS h2 t)) l ==> 
    SUBLIST (CONS h1 t) l`,
(* {{{ Proof *)
[
  STRIP_TAC THEN STRIP_TAC;
  REPEAT LIST_INDUCT_TAC;
  REWRITE_TAC[SUBLIST;NOT_CONS_NIL;];
  CASES_ON `h1 = h`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[SUBLIST;NOT_CONS_NIL;HD;TL;SUBLIST_NIL];
  STRIP_TAC;
  CLAIM `SUBLIST [h1; h2] t`;
  ASM_MESON_TAC[SUBLIST_NEQ];
  DISCH_THEN (REWRITE_ASSUMS o list);
  ASM_MESON_TAC[SUBLIST_CONS];
  REWRITE_TAC[SUBLIST;NOT_CONS_NIL;];  
  CASES_ON `h1 = h'`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[SUBLIST_CONS_CONS];
  MESON_TAC[SUBLIST_CONS2];
  STRIP_TAC;
  CLAIM `SUBLIST (CONS h1 (CONS h2 (CONS h t))) t'`;
  ASM_MESON_TAC[SUBLIST_NEQ];
  DISCH_THEN (REWRITE_ASSUMS o list);
  ASM_MESON_TAC[SUBLIST_CONS];
]);;
(* }}} *)

let SUBLIST_MATCH = prove_by_refinement(
  `!h t l. SUBLIST (CONS h t) l ==> 
     ?(l1:A list) l2. (l = APPEND l1 (CONS h l2)) /\ SUBLIST t l2`,
(* {{{ Proof *)
[
  STRIP_TAC;
  REPEAT LIST_INDUCT_TAC;
  REWRITE_TAC[SUBLIST;NOT_CONS_NIL;];
  CASES_ON `h = h'`;
  POP_ASSUM (REWRITE_ALL o list);
  STRIP_TAC;
  EXISTS_TAC `[]`;
  REWRITE_TAC[APPEND;SUBLIST_NIL];
  ASM_MESON_TAC[];
  REWRITE_TAC[SUBLIST_NIL];
  STRIP_TAC;
  CLAIM `SUBLIST [h] t`;
  ASM_MESON_TAC[SUBLIST_NEQ];
  DISCH_THEN (REWRITE_ASSUMS o list);
  REPEAT (POP_ASSUM MP_TAC);
  REPEAT STRIP_TAC;
  EXISTS_TAC `CONS h' l1`;
  EXISTS_TAC `l2`;
  REWRITE_TAC[APPEND];
  AP_TERM_TAC;
  ASM_MESON_TAC[];
  REWRITE_TAC[SUBLIST;NOT_CONS_NIL;];
  (* save *) 
  CASES_ON `h = h''`;
  POP_ASSUM (REWRITE_ALL o list);
  STRIP_TAC;
  REWRITE_ASSUMS[SUBLIST_CONS_CONS];
  EXISTS_TAC `[]:A list`;
  EXISTS_TAC `t'`;
  ASM_MESON_TAC[APPEND];
  (* save *) 
  STRIP_TAC;
  CLAIM `SUBLIST (CONS h (CONS h' t)) t'`;
  ASM_MESON_TAC[SUBLIST_NEQ];
  DISCH_THEN (REWRITE_ASSUMS o list);
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  EXISTS_TAC `CONS h'' l1`;
  EXISTS_TAC `l2`;
  ASM_REWRITE_TAC[APPEND];
]);;  
(* }}} *)

let ROL_SUBLIST = prove_by_refinement(
  `!l1 l2.  real_ordered_list l2 ==> SUBLIST l1 l2 ==> real_ordered_list l1`,  
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[ROL_NIL];
  REWRITE_TAC[real_ordered_list];
  REPEAT STRIP_TAC;
  REWRITE_ASSUMS[IMP_AND_THM];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[SUBLIST_CONS2];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  REWRITE_ASSUMS[NOT_NIL];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[HD];
  DISJ_CASES_TAC (ISPEC `l2:real list` list_CASES);
  ASM_MESON_TAC[SUBLIST;NOT_CONS_NIL];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  CASES_ON `h = h''`;
  POP_ASSUM (REWRITE_ALL o list);
  ASM_MESON_TAC[ROL_SUBLIST_LT;MEM];
  FIRST_ASSUM (fun x -> MP_TAC (MATCH_MP SUBLIST_MATCH x));
  STRIP_TAC;
  CLAIM `real_ordered_list (CONS h l2')`;
  ASM_MESON_TAC[ROL_APPEND];
  STRIP_TAC;
  CLAIM `MEM h' l2'`;
  ASM_MESON_TAC[SUBLIST_MEM;MEM];
  STRIP_TAC;
  ASM_MESON_TAC[ROL_MEM];
]);;
(* }}} *)

let SUBLIST_BUTLAST = prove_by_refinement(
  `!l. SUBLIST (BUTLAST l) l`, 
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[BUTLAST;SUBLIST_NIL];
  REWRITE_TAC[BUTLAST;SUBLIST_NIL;SUBLIST];
  REPEAT COND_CASES_TAC;
  REWRITE_TAC[SUBLIST_NIL];
  ASM_REWRITE_TAC[HD;TL;NOT_CONS_NIL;];
]);;

(* }}} *)

let SUBLIST_APPEND_HD = prove_by_refinement(
  `!l2 l3 l1. SUBLIST (APPEND l1 l2) (APPEND l1 l3) = SUBLIST l2 l3`,
(* {{{ Proof *)
[
  REPEAT_N 2 STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[APPEND];
  ASM_REWRITE_TAC[APPEND;SUBLIST_CONS_CONS];
]);;
(* }}} *)

let SUBLIST_ID_CONS = prove_by_refinement(
  `!h l. ~(SUBLIST (CONS h l) l)`,
(* {{{ Proof *)
[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[SUBLIST;NOT_CONS_NIL;];
  ASM_REWRITE_TAC[SUBLIST;NOT_CONS_NIL;HD;TL];
  ASM_MESON_TAC[SUBLIST_DELETE];
]);;
(* }}} *)

let SUBLIST_ID_APPEND = prove_by_refinement(
  `!m l. ~(l = []) ==> ~(SUBLIST (APPEND l m) m)`,
(* {{{ Proof *)
[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REWRITE_TAC[APPEND;];
  DISCH_THEN (fun x -> ALL_TAC);
  CASES_ON `t = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[APPEND;SUBLIST_ID_CONS];
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  ASM_MESON_TAC[SUBLIST_CONS2];
]);;
(* }}} *)

let SUBLIST_APPEND_TL = prove_by_refinement(
  `!l3 l1 l2. SUBLIST (APPEND l1 l3) (APPEND l2 l3) = SUBLIST l1 l2`,
(* {{{ Proof *)
[
  STRIP_TAC;
  REPEAT LIST_INDUCT_TAC;
  REWRITE_TAC[APPEND;APPEND_NIL;SUBLIST;SUBLIST_ID];
  REWRITE_ALL[SUBLIST_NIL;APPEND;APPEND_NIL;SUBLIST;SUBLIST_ID];
  ASM_REWRITE_TAC[];
  REWRITE_ALL[SUBLIST_NIL;SUBLIST;SUBLIST_ID;NOT_CONS_NIL;];  
  ASM_MESON_TAC[SUBLIST_ID_APPEND;APPEND;NOT_CONS_NIL;];
  REWRITE_TAC[APPEND];
  CASES_ON `h = h'`;
  POP_ASSUM (REWRITE_ALL o list);
  EQ_TAC;
  REWRITE_TAC[SUBLIST;APPEND;HD;TL;NOT_CONS_NIL;];
  STRIP_TAC;
  ASM_MESON_TAC[APPEND;];
  ASM_MESON_TAC[APPEND;];
  REWRITE_TAC[SUBLIST_CONS_CONS];
  ASM_MESON_TAC[];
  EQ_TAC;
  STRIP_TAC;
  MATCH_MP_TAC SUBLIST_CONS;
  CLAIM `SUBLIST (CONS h (APPEND t l3)) (APPEND t' l3)`;
  ASM_MESON_TAC[SUBLIST_NEQ];
  STRIP_TAC;
  ASM_MESON_TAC[APPEND;];
  ASM_REWRITE_TAC[NOT_CONS_NIL;SUBLIST;HD;TL];
  STRIP_TAC;
  ASM_MESON_TAC[APPEND;];  
]);;
(* }}} *)

let SUBLIST_TRANS2 = REWRITE_RULE[IMP_AND_THM] SUBLIST_TRANS;;

let APPEND_CONS = prove_by_refinement(
  `!h l1 l2. APPEND l1 (CONS h l2) = APPEND (APPEND l1 [h]) l2`,
(* {{{ Proof *)
[
  STRIP_TAC;
  REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND_NIL;APPEND];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let SUBLIST_APPEND = prove_by_refinement(
  `!l1 l2 m1 m2. SUBLIST l1 l2 ==> SUBLIST m1 m2 ==> 
    SUBLIST (APPEND l1 m1) (APPEND l2 m2)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[SUBLIST_NIL;APPEND];
  LIST_INDUCT_TAC;
  REWRITE_TAC[APPEND];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> FIRST_ASSUM (fun y -> ASSUME_TAC (MATCH_MP y x) THEN ASSUME_TAC x)); 
  REWRITE_TAC[APPEND];
  ASM_MESON_TAC[SUBLIST_CONS];
  LIST_INDUCT_TAC;
  MESON_TAC[SUBLIST;NOT_CONS_NIL];
  CASES_ON `h = h'`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[SUBLIST_CONS_CONS];
  REWRITE_TAC[SUBLIST_CONS_CONS;APPEND;];
  ASM_MESON_TAC[];
  REPEAT STRIP_TAC;
  CLAIM `SUBLIST (CONS h t) t'`;
  ASM_MESON_TAC[SUBLIST_NEQ];
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP y x)));
  POP_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  ASM_MESON_TAC[APPEND;SUBLIST_CONS];
]);;
(* }}} *)

let SUBLIST_APPEND2 = REWRITE_RULE[IMP_AND_THM] SUBLIST_APPEND;;

let ROL_APPEND2 = prove_by_refinement(
  `!l2 l1. real_ordered_list (APPEND l1 l2) ==> 
           real_ordered_list (APPEND l1 (BUTLAST l2))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ROL_SUBLIST);
  EXISTS_TAC `APPEND l1 l2`;
  ASM_REWRITE_TAC[SUBLIST_APPEND_HD;SUBLIST_BUTLAST];
]);;
(* }}} *)

let PL_LEM = prove_by_refinement(
  `!l. ~(l = []) ==> ~(TL (partition_line l) = [])`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  STRIP_TAC;
  REWRITE_TAC[partition_line];
  ASM_MESON_TAC[NOT_CONS_NIL;APPEND;TL];
]);; 
(* }}} *)

let HD_APPEND2 = prove_by_refinement(
  `!l m. ~(l = []) ==> (HD (APPEND l m) = HD l)`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REWRITE_TAC[APPEND;HD];
]);;

(* }}} *)

let BUTLAST_TL = prove_by_refinement(
  `!l. LENGTH l > 1 ==> (BUTLAST (TL l) = TL (BUTLAST l))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH] THEN ARITH_TAC;
  REWRITE_TAC[LENGTH];
  STRIP_TAC;
  REWRITE_TAC[TL;BUTLAST];
  COND_CASES_TAC;
  REWRITE_ASSUMS [GSYM LENGTH_0];
  REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;
  REWRITE_ASSUMS[NOT_NIL];
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[TL;BUTLAST];
]);;
(* }}} *)

let APPEND_TL = prove_by_refinement(
  `!m l. ~(l = []) ==> (APPEND (TL l) m = TL (APPEND l m))`,
(* {{{ Proof *)
[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REWRITE_TAC[APPEND;TL];
]);;
(* }}} *)

let APPEND_HD = prove_by_refinement(
  `!m l. ~(l = []) ==> (HD (APPEND l m) = HD l)`,
(* {{{ Proof *)
[  
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  STRIP_TAC;
  REWRITE_TAC[APPEND;HD];
]);;
(* }}} *)

let PL_LEM2 = prove_by_refinement(
  `!l. ~(l = []) ==> LENGTH (partition_line l) > 1`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN REWRITE_TAC[];
  REWRITE_TAC[partition_line];
  STRIP_TAC;
  COND_CASES_TAC;
  REWRITE_TAC[LENGTH] THEN ARITH_TAC;
  REWRITE_TAC[APPEND;LENGTH] THEN ARITH_TAC;
]);;
(* }}} *)

let BUTLAST_APPEND = prove_by_refinement(
  `!l m. ~(m = []) ==> 
     (BUTLAST (APPEND l m) = APPEND l (BUTLAST m))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[APPEND];
  REPEAT STRIP_TAC;
  REWRITE_TAC[APPEND;BUTLAST];
  ASM_MESON_TAC[APPEND_EQ_NIL];
]);;
(* }}} *)

let LENGTH_TL1 = prove_by_refinement(
  `!l. LENGTH l > 1 ==> ~(TL l = [])`,
(* {{{ Proof *)
[   
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH]  THEN ARITH_TAC;
  REWRITE_TAC[LENGTH;TL];
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ASSUMS o list);
  REWRITE_ASSUMS[LENGTH];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
]);;
(* }}} *)

let PL_BUTLAST = prove_by_refinement(
  `!l. ~(l = []) ==> ~(BUTLAST (partition_line l) = [])`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REWRITE_TAC[partition_line];
  COND_CASES_TAC;
  (* XXX REWRITE_TAC works here, but not MESON_TAC *)
  REWRITE_TAC[APPEND;NOT_CONS_NIL;BUTLAST];
  REWRITE_TAC[APPEND;NOT_CONS_NIL;BUTLAST];
]);; 
(* }}} *)

let PARTITION_LINE_APPEND = prove_by_refinement(
  `!h t l. ~(l = []) ==> 
    (partition_line (APPEND l (CONS h t)) = 
      APPEND (BUTLAST (partition_line l)) 
        (CONS (\x. LAST l < x /\ x < h) 
          (TL (partition_line (CONS h t)))))`,
(* {{{ Proof *)
[  
  STRIP_TAC THEN STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  DISCH_THEN (fun x -> ALL_TAC);
  CASES_ON `t' = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[HD;APPEND;partition_line;BUTLAST;LAST;TL;NOT_CONS_NIL;];
  POP_ASSUM (fun x -> REWRITE_ASSUMS [x] THEN ASSUME_TAC x);
  REWRITE_TAC[APPEND];
  CONV_TAC (LAND_CONV (REWRITE_CONV[partition_line]));
  COND_CASES_TAC;
  ASM_MESON_TAC[NOT_CONS_NIL;APPEND_EQ_NIL];
  POP_ASSUM (fun x -> ALL_TAC);
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[LAST];
  ASM_SIMP_TAC[APPEND_HD];
  CONV_TAC (RAND_CONV (LAND_CONV (RAND_CONV (REWRITE_CONV[partition_line]))));
  ASM_REWRITE_TAC[];
  REWRITE_TAC[APPEND;BUTLAST;NOT_CONS_NIL;];
  REPEAT AP_TERM_TAC;
  COND_CASES_TAC;
  ASM_MESON_TAC[PL_LEM2;LENGTH_TL1];
  REWRITE_TAC[APPEND];
  AP_TERM_TAC;
  MP_TAC (ISPEC `t':real list` PL_LEM2);
  ASM_REWRITE_TAC[];
  STRIP_TAC;  
  ASM_SIMP_TAC[BUTLAST_TL];
  MP_TAC (ISPEC `t':real list` PL_BUTLAST);  
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_SIMP_TAC[APPEND_TL];
]);;
(* }}} *)

let HD_TL = prove_by_refinement(
  `!l. ~(l = []) ==> (l = CONS (HD l) (TL l))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REWRITE_TAC[HD;TL];
]);;
(* }}} *)

let HD_LEM = prove_by_refinement(
  `!l1 l2. (TL l1 = l2) <=> (CONS (HD l1) (TL l1) = CONS (HD l1) l2)`,
(* {{{ Proof *)
[
  MESON_TAC[CONS_11];
]);; 
(* }}} *)

let rec LENGTH_N n ty =
  let zero = `0` in
  let neg = `(~)` in
  let imp_thm = TAUT `(a ==> b) ==> (b ==> a) ==> (a <=> b)` in 
  match n with 
    0 -> CONJUNCT1 LENGTH
  | 1 -> LENGTH_SING
  | n -> 
      let len_tm = mk_const ("LENGTH",[ty,aty]) in
      let tl_tm = mk_const ("TL",[ty,aty]) in
      let hd_tm = mk_const ("HD",[ty,aty]) in
      let t = mk_var("t",mk_type("list",[ty])) in
      let n_tm = mk_small_numeral n in
      let pren_tm = mk_small_numeral (n - 1) in
      let len_thm = ASSUME (mk_eq(mk_comb(len_tm,t),n_tm)) in
      let pre_thm = LENGTH_N (n - 1) ty in
      let n_nz = prove(mk_neg(mk_eq(n_tm,zero)),ARITH_TAC) in 
      let not_nil_thm = EQ_MP (REWRITE_RULE[len_thm] (AP_TERM neg (ISPEC t LENGTH_0))) n_nz in
      let n_suc = prove(mk_eq(n_tm,mk_comb(`SUC`,pren_tm)),ARITH_TAC) in
      let len_tl = REWRITE_RULE[n_suc;PRE;ISPEC (mk_comb(tl_tm,t)) pre_thm;len_thm] (MATCH_MP LENGTH_TL not_nil_thm) in 
      let cons_thm = MATCH_MP (ISPEC t HD_TL) not_nil_thm in
      let hd_thm = ONCE_REWRITE_RULE[HD_LEM] len_tl in
      let thm = REWRITE_RULE[GSYM cons_thm] hd_thm in
      let x0 = mk_var("x" ^ string_of_int n,ty) in
      let hdt = mk_comb(hd_tm,t) in
      let ex_thm = EXISTS (mk_exists(x0,subst[x0,hdt] (concl thm)),mk_comb(hd_tm,t)) thm in
      let left = DISCH (concl len_thm) ex_thm in
      let right = prove(mk_imp(concl ex_thm,concl len_thm),REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC) in
        GEN_ALL(MATCH_MPL[imp_thm;left;right]);;

let BUTLAST_LENGTH = prove_by_refinement(
  `!l. ~(l = []) ==> (LENGTH (BUTLAST l) = PRE (LENGTH l))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN REWRITE_TAC[];
  REWRITE_TAC[BUTLAST;LENGTH];
  COND_CASES_TAC;
  ASM_REWRITE_TAC[NOT_CONS_NIL;LENGTH;];
  ARITH_TAC;
  ASM_REWRITE_TAC[NOT_CONS_NIL;LENGTH;];
  ASM_SIMP_TAC[];
  MATCH_MP_TAC (ARITH_RULE `~(n = 0) ==> (SUC(PRE n) = PRE(SUC n))`);
  ASM_MESON_TAC[LENGTH_0];
]);;
(* }}} *)

let ALL2_LEM = prove_by_refinement(
  `!a b x y s eqs pts sgns. 
   ALL2 (interpsigns eqs) (partition_line 
    (APPEND pts [x; y])) (APPEND sgns [a; b; s; s; s]) ==>  
   ALL2 (interpsigns eqs) (partition_line 
    (APPEND pts [x])) (APPEND sgns [a; b; s])`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  DISJ_CASES_TAC (ISPEC `pts:real list` list_CASES);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;NOT_CONS_NIL;HD;TL];
  CLAIM `sgns = []`;
  CLAIM `LENGTH [\x'. x' < x; \x'. x' = x; \x'. x < x' /\ x' < y; \x. x = y; \x. y < x] = LENGTH (APPEND sgns [a; b; s; s; s])`;
  ASM_MESON_TAC[ALL2_LENGTH];
  REWRITE_TAC[LENGTH;LENGTH_APPEND;GSYM LENGTH_0];
  ARITH_TAC;
  DISCH_THEN (REWRITE_ALL o list);
  REWRITE_ALL [APPEND;ALL2;];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  EXISTS_TAC `\z. x < z /\ z < y \/ (z = y) \/ y < z`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
  (* save *) 
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;NOT_CONS_NIL;];  
  STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line (CONS (h:real) t))) (CONS (\x'. LAST (CONS h t) < x' /\ x' < x) (TL (partition_line [x; y])))) = LENGTH (APPEND sgns [(a:sign list); b; s; s; s])`;
  ASM_MESON_TAC[ALL2_LENGTH];
  CLAIM `~(partition_line [x; y] = [])`;
  REWRITE_TAC[APPEND;NOT_CONS_NIL;partition_line;];
  REWRITE_TAC[TL;APPEND;NOT_CONS_NIL;LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;LENGTH_TL];
  STRIP_TAC;
  ASM_SIMP_TAC[LENGTH_TL];
  REWRITE_TAC[partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[HD;LENGTH;APPEND;TL;BUTLAST;NOT_CONS_NIL;];
  ARITH_SIMP_TAC[];
  STRIP_TAC;
  CLAIM `LENGTH sgns = 2`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_PAIR];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[partition_line;BUTLAST;LAST;ALL2;TL;APPEND;NOT_CONS_NIL;LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;LENGTH_TL];  
  ASM_REWRITE_TAC[];
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  REWRITE_ASSUMS[HD];
  EXISTS_TAC `\z. x < z /\ z < y \/ (z = y) \/ y < z`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
  (* save *) 
  REWRITE_ALL[HD;partition_line;BUTLAST;LAST;ALL2;TL;APPEND;NOT_CONS_NIL;LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;LENGTH_TL];  
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  COND_CASES_TAC;
  ASM_MESON_TAC[PL_LEM2;LENGTH_TL1];
  ARITH_SIMP_TAC[LENGTH;];
  ASM_SIMP_TAC[PARTITION_LINE_LENGTH];
  ASM_SIMP_TAC[BUTLAST_LENGTH];
  CLAIM `~(partition_line t =  [])`;
  REWRITE_ASSUMS[NOT_NIL];
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[partition_line;NOT_CONS_NIL;list_CASES;APPEND;];
  COND_CASES_TAC;
  MESON_TAC[NOT_CONS_NIL];
  MESON_TAC[NOT_CONS_NIL];
  STRIP_TAC;
  ASM_SIMP_TAC[LENGTH_TL];
  STRIP_TAC;
  MP_TAC (ISPEC `t:real list` PARTITION_LINE_LENGTH);
  STRIP_TAC;
  CLAIM `~(LENGTH (partition_line t) = 0)`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP PL_LEM2);
  STRIP_TAC;
  CLAIM `~(PRE (LENGTH (partition_line t)) = 0)`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `SUC(LENGTH (partition_line t)) = LENGTH sgns`;
  REPEAT_N 5 (POP_ASSUM MP_TAC) THEN ARITH_TAC;
  DISCH_THEN (ASSUME_TAC o GSYM);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  REWRITE_TAC[GSYM APPEND];
  CLAIM `(ALL2 (interpsigns eqs) (BUTLAST
        (CONS (\x. x < h)
        (CONS (\x. x = h)
        (CONS (\x. h < x /\ x < HD t) (TL (partition_line t))))))
        sgns) /\ (ALL2 (interpsigns eqs) [\x'. LAST t < x' /\ x' < x; \x'. x' = x; \x'. x < x' /\
                                                      x' < y; 
       \x. x = y; \x. y < x] [a; b; s; s; s])`;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_APPEND_LENGTH);
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[BUTLAST;NOT_CONS_NIL;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;LENGTH_TL];
  CLAIM `~(LENGTH t = 0)`;
  ASM_MESON_TAC[LENGTH_0];
  ARITH_TAC;
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  STRIP_TAC;
  REWRITE_ASSUMS[BUTLAST;NOT_CONS_NIL;];
  ASM_MESON_TAC[];
  REWRITE_ALL[BUTLAST;LAST;ALL2;TL;APPEND;NOT_CONS_NIL;LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;LENGTH_TL];  
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  EXISTS_TAC `\z. x < z /\ z < y \/ (z = y) \/ y < z`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
]);;

(* }}} *)

let INTERPMAT_TRIO_TL = prove_by_refinement(
  `!a b x y s eqs pts sgns.
     interpmat (APPEND pts [x; y]) eqs 
        (APPEND sgns [a; b; s; s; s]) ==> 
     interpmat (APPEND pts [x]) eqs (APPEND sgns [a; b; s])`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ROL_SUBLIST);
  EXISTS_TAC `APPEND pts [x; y]`;
  ASM_REWRITE_TAC[SUBLIST_APPEND_HD;SUBLIST_CONS_CONS;SUBLIST_NIL];  
  MATCH_MP_TAC ALL2_LEM;
  ASM_MESON_TAC[];
]);;
(* }}} *)


let LAST_APPEND = prove_by_refinement(
  `!l1 l2. ~(l2 = []) ==> (LAST (APPEND l1 l2) = LAST l2)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[APPEND];
  REWRITE_TAC[APPEND;LAST;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[APPEND_EQ_NIL];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let APPEND_APPEND = prove_by_refinement(
  `!l1 l2 l3. APPEND (APPEND l1 l2) l3 = APPEND l1 (APPEND l2 l3)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[APPEND];
  REWRITE_TAC[APPEND];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let ALL2_LEM2 = prove_by_refinement(
  `!a b x y s eqs pts sgns qts rgns. 
   ALL2 (interpsigns eqs) (partition_line 
    (APPEND pts (CONS x (CONS y qts)))) 
    (APPEND sgns (CONS a (CONS b 
      (CONS s (CONS s (CONS s rgns)))))) ==>  
   (LENGTH sgns = 2 * LENGTH pts) ==>   
   ALL2 (interpsigns eqs) (partition_line 
    (APPEND pts (CONS x qts))) 
    (APPEND sgns (CONS a (CONS b (CONS s rgns))))`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (partition_line 
    (APPEND pts (CONS x (CONS y qts)))) = 
    LENGTH (APPEND sgns (CONS (a:sign list) (CONS b 
      (CONS s (CONS s (CONS s rgns))))))`;
  ASM_MESON_TAC[ALL2_LENGTH];
  ASM_REWRITE_TAC[PARTITION_LINE_LENGTH;LENGTH;APPEND;LENGTH_APPEND];
  STRIP_TAC;
  CLAIM `LENGTH rgns = 2 * LENGTH qts`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  POP_ASSUM (fun x -> ALL_TAC); 
  STRIP_TAC;
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  CLAIM `sgns = []`;
  ASM_MESON_TAC[ARITH_RULE `2 * 0 = 0`;LENGTH_0;LENGTH];   
  DISCH_THEN (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;NOT_CONS_NIL;HD;TL;APPEND;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[ALL2;partition_line;NOT_CONS_NIL;HD;TL;APPEND;];
  REPEAT_N 3 STRIP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  EXISTS_TAC `\(z:real). x < z /\ z < y \/ (z = y) \/ y < z`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[ALL2;partition_line;NOT_CONS_NIL;HD;TL;APPEND;];
  REPEAT_N 3 STRIP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  EXISTS_TAC `\(z:real). x < z /\ z < y \/ (z = y) \/ y < z /\ z < HD qts`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  CLAIM `LENGTH (BUTLAST (partition_line pts)) = LENGTH sgns`;
  ASM_REWRITE_TAC[];
  ASSUME_TAC (ISPEC `pts:real list` PARTITION_LINE_NOT_NIL);
  ASM_SIMP_TAC[BUTLAST_LENGTH];
  REWRITE_TAC[PARTITION_LINE_LENGTH];
  ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[ALL2_SPLIT];
  REWRITE_ALL[partition_line;NOT_CONS_NIL;HD;TL;];
  COND_CASES_TAC;
  REWRITE_TAC[ALL2;TL;HD;APPEND;];
  REPEAT_N 4 STRIP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  EXISTS_TAC `\(z:real). x < z /\ z < y \/ (z = y) \/ y < z`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT_N 4 STRIP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  EXISTS_TAC `\(z:real). x < z /\ z < y \/ (z = y) \/ y < z /\ z < HD qts`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
]);;

(* }}} *)

let INTERPMAT_TRIO_INNER = prove_by_refinement(
  `!a b x y s eqs qts rgns pts sgns.
     interpmat (APPEND pts (CONS x (CONS y qts))) eqs 
        (APPEND sgns (CONS a (CONS b 
          (CONS s (CONS s (CONS s rgns)))))) ==> 
        (LENGTH sgns = 2 * LENGTH pts) ==> 
       interpmat (APPEND pts (CONS x qts)) eqs 
        (APPEND sgns (CONS a (CONS b (CONS s rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ROL_SUBLIST);
  EXISTS_TAC `(APPEND pts (CONS x (CONS y qts)))`;
  ASM_REWRITE_TAC[SUBLIST_APPEND_HD;SUBLIST_CONS_CONS;SUBLIST_NIL];  
  MESON_TAC[SUBLIST_CONS;SUBLIST_ID];
  ASM_MESON_TAC[ALL2_LEM2];
]);;
(* }}} *)

let INTERPMAT_SING = prove_by_refinement(
  `!x l.  interpmat [x] eqs [l; l; l] ==> interpmat [] eqs [l]`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REWRITE_TAC[ROL_SING;partition_line;ROL_NIL;ALL2;];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_SUBSET;
  EXISTS_TAC `\(z:real). x < z \/ (z = x) \/ z < x`;
  STRIP_TAC;
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC INTERPSIGNS_CONJ;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let INFERISIGN_POS_POS_POS = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Unknown (CONS Pos r2)) 
            (CONS (CONS Pos r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Pos (CONS Pos r2)) 
            (CONS (CONS Pos r3) rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Pos r3) rgns))))`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] pos_pos_neq_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] pos_pos_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] pos_pos_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] pos_pos_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
]);;
(* }}} *)

let INFERISIGN_POS_POS_NEG = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Unknown (CONS Neg r2)) 
            (CONS (CONS Pos r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Pos (CONS Neg r2)) 
            (CONS (CONS Pos r3) rgns))))`,
(* {{{ Proof *)

[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Pos r3) rgns))))`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] pos_pos_neq_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] pos_pos_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] pos_pos_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] pos_pos_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
]);;

(* }}} *)


let INFERISIGN_NEG_NEG_POS = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Unknown (CONS Pos r2)) 
            (CONS (CONS Neg r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Neg (CONS Pos r2)) 
            (CONS (CONS Neg r3) rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Neg r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Neg r3) rgns))))`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] neg_neg_neq_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] neg_neg_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] neg_neg_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] neg_neg_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[REAL_ARITH `x < y ==> ~(x = y)`];  
]);;
(* }}} *)

let INFERISIGN_NEG_NEG_NEG = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Unknown (CONS Neg r2)) 
            (CONS (CONS Neg r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Neg (CONS Neg r2)) 
            (CONS (CONS Neg r3) rgns))))`,
(* {{{ Proof *)

[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Neg r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Neg r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] neg_neg_neq_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] neg_neg_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] neg_neg_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] neg_neg_neq_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
]);;

(* }}} *)


let ALL2_INTERPSIGN_SUBSET = prove_by_refinement(
  `!P Q l1 l2. ALL2 (interpsign P) l1 l2 ==> Q SUBSET P ==> 
   ALL2 (interpsign Q) l1 l2`,
(* {{{ Proof *)
[
  STRIP_TAC THEN STRIP_TAC THEN REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2];
  ASM_MESON_TAC[INTERPSIGN_SUBSET];
]);;
(* }}} *)


let HD_APPEND1 = prove_by_refinement(
  `!h i l1 l2. 
  HD (APPEND l1 (CONS h l2)) = HD (APPEND l1 (CONS h (CONS i l2)))`,
(* {{{ Proof *)
[
  STRIP_TAC THEN STRIP_TAC;
  LIST_INDUCT_TAC;
  ASM_REWRITE_TAC[HD;APPEND];
  ASM_REWRITE_TAC[HD;APPEND];
]);;  
(* }}} *)

let ROL_APPEND_INSERT = prove_by_refinement(
  `!h j l1 l2. 
    real_ordered_list (APPEND l1 (CONS h (CONS i l2))) ==> 
    h < j ==> j < i ==> 
      real_ordered_list (APPEND l1 (CONS h (CONS j (CONS i l2))))`,
(* {{{ Proof *)
[
  STRIP_TAC THEN STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[APPEND;real_ordered_list;HD;TL;NOT_CONS_NIL;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[APPEND;real_ordered_list];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[];
  ASM_MESON_TAC[APPEND_EQ_NIL;NOT_CONS_NIL;];
  ASM_MESON_TAC[];
  DISJ2_TAC;
  ASM_MESON_TAC[HD_APPEND1];
]);;
(* }}} *)


let INFERISIGN_POS_NEG_POS = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Unknown (CONS Pos r2)) 
            (CONS (CONS Neg r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    ?w. interpmat (APPEND pts (CONS y (CONS w (CONS z qts)))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
          (CONS (CONS Pos (CONS Pos r2)) 
          (CONS (CONS Zero (CONS Pos r2)) 
          (CONS (CONS Neg (CONS Pos r2)) 
          (CONS (CONS Neg r3) rgns))))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Neg r3) rgns))))`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] pos_neg_neq_thm);
  REWRITE_ALL[real_ordered_list;HD;NOT_CONS_NIL;];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[interpsigns;ALL2;interpsign;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[REAL_LT_TRANS];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];  
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  (* save *) 
  REWRITE_TAC[TL;APPEND;ALL2;real_gt;interpsigns;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] pos_neg_neq_thm);
  REWRITE_ALL[real_ordered_list;HD;NOT_CONS_NIL;];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[interpsigns;ALL2;interpsign;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[REAL_LT_TRANS];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];  
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
  ASM_MESON_TAC[REAL_LT_TRANS];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  CLAIM `!rts. APPEND (BUTLAST (partition_line pts)) 
       (CONS (\x. LAST pts < x /\ x < y) rts) = 
     APPEND (APPEND (BUTLAST (partition_line pts)) 
        [\x. LAST pts < x /\ x < y]) rts`;
  MESON_TAC[APPEND;APPEND_CONS];
  DISCH_THEN (ONCE_REWRITE_TAC o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_TAC[real_ordered_list;NOT_CONS_NIL;HD;];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[ALL2;partition_line;HD;TL;NOT_CONS_NIL;];
  (* save *) 
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;TL;HD;interpsigns;interpsign;ALL2;];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] pos_neg_neq_thm);
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  (* save *) 
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[interpsigns;interpsign];
  FIRST_ASSUM (MP_TAC o MATCH_MP ROL_APPEND);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[ROL_APPEND_INSERT];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;interpsign];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  (* save *) 
  REWRITE_ALL[APPEND;TL;HD;interpsigns;interpsign;ALL2;];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] pos_neg_neq_thm);
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  (* save *) 
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[interpsigns;interpsign];
  FIRST_ASSUM (MP_TAC o MATCH_MP ROL_APPEND);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[ROL_APPEND_INSERT];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;interpsign];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
]);;
(* }}} *)


let INFERISIGN_POS_NEG_NEG = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Unknown (CONS Neg r2)) 
            (CONS (CONS Neg r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    ?w. interpmat (APPEND pts (CONS y (CONS w (CONS z qts)))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
          (CONS (CONS Pos (CONS Neg r2)) 
          (CONS (CONS Zero (CONS Neg r2)) 
          (CONS (CONS Neg (CONS Neg r2)) 
          (CONS (CONS Neg r3) rgns))))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Neg r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] pos_neg_neq_thm);
  REWRITE_ALL[real_ordered_list;HD;NOT_CONS_NIL;];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];  
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  (* save *) 
  REWRITE_TAC[TL;APPEND;ALL2;real_gt;interpsigns;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] pos_neg_neq_thm);
  REWRITE_ALL[real_ordered_list;HD;NOT_CONS_NIL;];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];  
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  CLAIM `!rts. APPEND (BUTLAST (partition_line pts)) 
       (CONS (\x. LAST pts < x /\ x < y) rts) = 
     APPEND (APPEND (BUTLAST (partition_line pts)) 
        [\x. LAST pts < x /\ x < y]) rts`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (ONCE_REWRITE_TAC o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;real_gt;ROL_APPEND];
  REWRITE_TAC[real_ordered_list;NOT_CONS_NIL;HD;];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[ALL2;partition_line;HD;TL;NOT_CONS_NIL;];
  (* save *) 
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;TL;HD;interpsigns;interpsign;ALL2;];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] pos_neg_neq_thm);
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  (* save *) 
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[interpsigns;interpsign];
  FIRST_ASSUM (MP_TAC o MATCH_MP ROL_APPEND);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;ROL_APPEND_INSERT];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;interpsign];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  (* save *) 
  REWRITE_ALL[APPEND;TL;HD;interpsigns;interpsign;ALL2;];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] pos_neg_neq_thm);
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  (* save *) 
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[interpsigns;interpsign];
  FIRST_ASSUM (MP_TAC o MATCH_MP ROL_APPEND);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;ROL_APPEND_INSERT];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;interpsign];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
]);;
(* }}} *)


let INFERISIGN_NEG_POS_NEG = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Unknown (CONS Neg r2)) 
            (CONS (CONS Pos r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    ?w. interpmat (APPEND pts (CONS y (CONS w (CONS z qts)))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
          (CONS (CONS Neg (CONS Neg r2)) 
          (CONS (CONS Zero (CONS Neg r2)) 
          (CONS (CONS Pos (CONS Neg r2)) 
          (CONS (CONS Pos r3) rgns))))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = 
         LENGTH (APPEND sgns (CONS (CONS Neg r1) 
          (CONS (CONS Unknown (CONS Neg r2)) 
          (CONS (CONS Pos r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] neg_pos_neq_thm);
  REWRITE_ALL[real_ordered_list;HD;NOT_CONS_NIL;];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];  
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  (* save *) 
  REWRITE_TAC[TL;APPEND;ALL2;real_gt;interpsigns;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] neg_pos_neq_thm);
  REWRITE_ALL[real_ordered_list;HD;NOT_CONS_NIL;];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];  
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  CLAIM `!rts. APPEND (BUTLAST (partition_line pts)) 
       (CONS (\x. LAST pts < x /\ x < y) rts) = 
     APPEND (APPEND (BUTLAST (partition_line pts)) 
        [\x. LAST pts < x /\ x < y]) rts`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (ONCE_REWRITE_TAC o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;real_gt;ROL_APPEND];
  REWRITE_TAC[real_ordered_list;NOT_CONS_NIL;HD;];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[ALL2;partition_line;HD;TL;NOT_CONS_NIL;];
  (* save *) 
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;TL;HD;interpsigns;interpsign;ALL2;];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] neg_pos_neq_thm);
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  (* save *) 
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[interpsigns;interpsign];
  FIRST_ASSUM (MP_TAC o MATCH_MP ROL_APPEND);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;ROL_APPEND_INSERT];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;interpsign];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  (* save *) 
  REWRITE_ALL[APPEND;TL;HD;interpsigns;interpsign;ALL2;];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] neg_pos_neq_thm);
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  (* save *) 
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[interpsigns;interpsign];
  FIRST_ASSUM (MP_TAC o MATCH_MP ROL_APPEND);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;ROL_APPEND_INSERT];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;interpsign];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
]);;
(* }}} *)

let INFERISIGN_NEG_POS_POS = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Unknown (CONS Pos r2)) 
            (CONS (CONS Pos r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    ?w. interpmat (APPEND pts (CONS y (CONS w (CONS z qts)))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
          (CONS (CONS Neg (CONS Pos r2)) 
          (CONS (CONS Zero (CONS Pos r2)) 
          (CONS (CONS Pos (CONS Pos r2)) 
          (CONS (CONS Pos r3) rgns))))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = 
         LENGTH (APPEND sgns (CONS (CONS Neg r1) 
          (CONS (CONS Unknown (CONS Pos r2)) 
          (CONS (CONS Pos r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] neg_pos_neq_thm);
  REWRITE_ALL[real_ordered_list;HD;NOT_CONS_NIL;];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];  
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  (* save *) 
  REWRITE_TAC[TL;APPEND;ALL2;real_gt;interpsigns;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] neg_pos_neq_thm);
  REWRITE_ALL[real_ordered_list;HD;NOT_CONS_NIL;];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[real_gt;interpsigns;ALL2;interpsign;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];  
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[SUBSET;IN];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  ASM_MESON_TAC[real_gt;REAL_LT_TRANS];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  CLAIM `!rts. APPEND (BUTLAST (partition_line pts)) 
       (CONS (\x. LAST pts < x /\ x < y) rts) = 
     APPEND (APPEND (BUTLAST (partition_line pts)) 
        [\x. LAST pts < x /\ x < y]) rts`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (ONCE_REWRITE_TAC o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;real_gt;ROL_APPEND];
  REWRITE_TAC[real_ordered_list;NOT_CONS_NIL;HD;];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[ALL2;partition_line;HD;TL;NOT_CONS_NIL;];
  (* save *) 
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;TL;HD;interpsigns;interpsign;ALL2;];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] neg_pos_neq_thm);
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  (* save *) 
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[interpsigns;interpsign];
  FIRST_ASSUM (MP_TAC o MATCH_MP ROL_APPEND);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;ROL_APPEND_INSERT];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;interpsign];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  (* save *) 
  REWRITE_ALL[APPEND;TL;HD;interpsigns;interpsign;ALL2;];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`y:real`;`z:real`;`p:real list`] neg_pos_neq_thm);
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_ARITH `x < y ==> ~(x = y)`;REAL_ARITH `y < x ==> ~(x = y)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  REWRITE_ALL[interpsign;real_gt];
  (* save *) 
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[interpsigns;interpsign];
  FIRST_ASSUM (MP_TAC o MATCH_MP ROL_APPEND);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[real_gt;ROL_APPEND_INSERT];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;interpsign];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. y < x /\ x < z`;
  REWRITE_TAC[SUBSET;IN];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
  ASM_MESON_TAC[real_gt;real_gt;REAL_LT_TRANS;];
]);;
(* }}} *)


let INFERISIGN_ZERO_POS_POS = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Unknown (CONS Pos r2)) 
            (CONS (CONS Pos r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Pos (CONS Pos r2)) 
            (CONS (CONS Pos r3) rgns))))`,
(* {{{ Proof *)

[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Zero r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Pos r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_pos_pos_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_pos_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_pos_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_pos_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
]);;

(* }}} *)

let INFERISIGN_ZERO_POS_NEG = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Unknown (CONS Neg r2)) 
            (CONS (CONS Pos r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Pos (CONS Neg r2)) 
            (CONS (CONS Pos r3) rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Zero r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Pos r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_pos_pos_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_pos_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_pos_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_pos_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
]);;
(* }}} *)

let INFERISIGN_POS_ZERO_POS = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Unknown (CONS Pos r2)) 
            (CONS (CONS Zero r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Pos (CONS Pos r2)) 
            (CONS (CONS Zero r3) rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Zero r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] pos_zero_pos_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] pos_zero_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] pos_zero_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] pos_zero_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
]);;
(* }}} *)

let INFERISIGN_POS_ZERO_NEG = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Unknown (CONS Neg r2)) 
            (CONS (CONS Zero r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Pos r1) 
           (CONS (CONS Pos (CONS Neg r2)) 
            (CONS (CONS Zero r3) rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = LENGTH (APPEND sgns (CONS (CONS Pos r1) (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Zero r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] pos_zero_pos_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] pos_zero_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] pos_zero_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] pos_zero_pos_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
]);;
(* }}} *)

let INFERISIGN_ZERO_NEG_POS = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Unknown (CONS Pos r2)) 
            (CONS (CONS Neg r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Neg (CONS Pos r2)) 
            (CONS (CONS Neg r3) rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = 
   LENGTH (APPEND sgns (CONS (CONS Zero r1) 
   (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Neg r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_neg_neg_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_neg_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_neg_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_neg_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
]);;
(* }}} *)

let INFERISIGN_ZERO_NEG_NEG = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Unknown (CONS Neg r2)) 
            (CONS (CONS Neg r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Neg (CONS Neg r2)) 
            (CONS (CONS Neg r3) rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = 
   LENGTH (APPEND sgns (CONS (CONS Zero r1) 
   (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Neg r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_neg_neg_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_neg_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_neg_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] zero_neg_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
]);;
(* }}} *)



let INFERISIGN_NEG_ZERO_NEG = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Unknown (CONS Neg r2)) 
            (CONS (CONS Zero r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Neg (CONS Neg r2)) 
            (CONS (CONS Zero r3) rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = 
   LENGTH (APPEND sgns (CONS (CONS Neg r1) 
   (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Zero r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] neg_zero_neg_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] neg_zero_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] neg_zero_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] neg_zero_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
]);;
(* }}} *)

let INFERISIGN_NEG_ZERO_POS = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Unknown (CONS Pos r2)) 
            (CONS (CONS Zero r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> 
    interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Neg r1) 
           (CONS (CONS Neg (CONS Pos r2)) 
            (CONS (CONS Zero r3) rgns))))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = 
   LENGTH (APPEND sgns (CONS (CONS Neg r1) 
   (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Zero r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH sgns = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] neg_zero_neg_thm);
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] neg_zero_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;NOT_CONS_NIL;HD;ALL2;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[real_gt];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] neg_zero_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH sgns`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (REWRITE_RULE[real_gt;IMP_AND_THM] neg_zero_neg_thm);
  REWRITE_ALL[interpsign;real_ordered_list;ROL_APPEND;NOT_CONS_NIL;HD;ALL2;real_ordered_list;APPEND;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y (CONS z qts))`;
  ASM_MESON_TAC[real_gt;ROL_APPEND];
  REWRITE_ALL[NOT_CONS_NIL;real_gt;real_ordered_list;HD;];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
  ASM_MESON_TAC[real_gt;REAL_ARITH `x < y ==> ~(x = y)`];  
]);;
(* }}} *)

let INFERISIGN_ZERO_ZERO_POS = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Unknown (CONS Pos r2)) 
            (CONS (CONS Zero r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> F`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~((sgns:(sign list) list) = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = 
   LENGTH (APPEND sgns (CONS (CONS Zero r1) 
   (CONS (CONS Unknown (CONS Pos r2)) (CONS (CONS Zero r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH (sgns:(sign list) list) = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (PURE_REWRITE_RULE[real_gt;IMP_AND_THM] eq_eq_false_thm);
  EXISTS_TAC `y`;
  EXISTS_TAC `z`;
  EXISTS_TAC `p`;
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (PURE_REWRITE_RULE[real_gt;IMP_AND_THM] eq_eq_false_thm);
  EXISTS_TAC `y`;
  EXISTS_TAC `z`;
  EXISTS_TAC `p`;
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH (sgns:(sign list) list)`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC (PURE_REWRITE_RULE[real_gt;IMP_AND_THM] eq_eq_false_thm);
  EXISTS_TAC `y`;
  EXISTS_TAC `z`;
  EXISTS_TAC `p`;
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_TAC[HD;NOT_CONS_NIL;real_ordered_list];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH (sgns:(sign list)list)`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (PURE_REWRITE_RULE[real_gt;IMP_AND_THM] eq_eq_false_thm);
  EXISTS_TAC `y`;
  EXISTS_TAC `z`;
  EXISTS_TAC `p`;
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y(CONS  z qts))`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_TAC[HD;NOT_CONS_NIL;real_ordered_list];
  STRIP_TAC;
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
]);;
(* }}} *)

let INFERISIGN_ZERO_ZERO_NEG = prove_by_refinement(
  `!y z p pts qts eqs sgns rgns r1 r2 r3.
     interpmat (APPEND pts (CONS y (CONS z qts))) 
      (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) eqs)) 
        (APPEND sgns 
          (CONS (CONS Zero r1) 
           (CONS (CONS Unknown (CONS Neg r2)) 
            (CONS (CONS Zero r3) rgns)))) ==> 
     (LENGTH sgns = 2 * LENGTH pts + 1) ==> F`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~((sgns:(sign list) list) = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `LENGTH (partition_line (APPEND pts (CONS y (CONS z qts)))) = 
   LENGTH (APPEND sgns (CONS (CONS Zero r1) 
   (CONS (CONS Unknown (CONS Neg r2)) (CONS (CONS Zero r3) rgns))))`;
  ASM_MESON_TAC[real_gt;ALL2_LENGTH];
  STRIP_TAC;
  (* save *) 
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;];
  CLAIM `LENGTH (sgns:(sign list) list) = 1`;
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_ALL[LENGTH];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[LENGTH_1];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND];
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[partition_line;TL;HD;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;APPEND;ALL2;real_gt];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;ALL2;];
  ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign];
  REWRITE_ALL[real_gt];
  MATCH_MP_TAC (PURE_REWRITE_RULE[real_gt;IMP_AND_THM] eq_eq_false_thm);
  EXISTS_TAC `y`;
  EXISTS_TAC `z`;
  EXISTS_TAC `p`;
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[LENGTH;APPEND;TL;HD;ALL2;interpsigns];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[interpsign;real_gt;];
  MATCH_MP_TAC (PURE_REWRITE_RULE[real_gt;IMP_AND_THM] eq_eq_false_thm);
  EXISTS_TAC `y`;
  EXISTS_TAC `z`;
  EXISTS_TAC `p`;
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND;partition_line;NOT_CONS_NIL;];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[TL;HD;APPEND;ALL2;];
  CLAIM `APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y; \x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x] = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) [\x. x = y; \x. y < x /\ x < z; \x. x = z; \x. z < x]`;
  MESON_TAC[real_gt;APPEND;APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH (sgns:(sign list) list)`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC (PURE_REWRITE_RULE[real_gt;IMP_AND_THM] eq_eq_false_thm);
  EXISTS_TAC `y`;
  EXISTS_TAC `z`;
  EXISTS_TAC `p`;
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list [y; z]`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_TAC[HD;NOT_CONS_NIL;real_ordered_list];
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
  (* save *) 
  REWRITE_TAC[APPEND;TL;HD;ALL2;];
  REPEAT STRIP_TAC;
  CLAIM `!j. APPEND (BUTLAST (partition_line pts)) (CONS (\x. LAST pts < x /\ x < y) j) = APPEND (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) j`;
  MESON_TAC[APPEND;APPEND_CONS];
  DISCH_THEN (fun x -> ONCE_REWRITE_TAC[x] THEN ONCE_REWRITE_ASSUMS[x]);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts)) [\x. LAST pts < x /\ x < y]) = LENGTH (sgns:(sign list)list)`;
  REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ASM_SIMP_TAC[LENGTH_APPEND;BUTLAST_LENGTH;LENGTH;PARTITION_LINE_NOT_NIL;PARTITION_LINE_LENGTH];
  ARITH_TAC;
  REWRITE_ALL[TL;APPEND;HD];
  DISCH_THEN (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  REWRITE_ALL[ALL2;interpsigns;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsign;real_gt];
  MATCH_MP_TAC (PURE_REWRITE_RULE[real_gt;IMP_AND_THM] eq_eq_false_thm);
  EXISTS_TAC `y`;
  EXISTS_TAC `z`;
  EXISTS_TAC `p`;
  REWRITE_ALL[real_ordered_list;NOT_CONS_NIL;HD;interpsign];
  REWRITE_ALL[real_gt;ALL2;interpsigns;interpsign;];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `real_ordered_list (CONS y(CONS  z qts))`;
  ASM_MESON_TAC[ROL_APPEND];
  REWRITE_TAC[HD;NOT_CONS_NIL;real_ordered_list];
  STRIP_TAC;
  ASM_MESON_TAC[real_gt;];
  ASM_MESON_TAC[real_gt;real_gt;];
  ASM_MESON_TAC[real_gt;REAL_ARITH `x > y ==> ~(x = y)`];  
]);;
(* }}} *)

let BUTLAST_ID = prove_by_refinement(
  `!l. ~(l = []) ==> (APPEND (BUTLAST l) [LAST l] = l)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  DISCH_THEN (fun x -> ALL_TAC);
  REWRITE_TAC[BUTLAST;APPEND;LAST;];
  COND_CASES_TAC;
  ASM_REWRITE_TAC[BUTLAST;APPEND;LAST;];
  ASM_REWRITE_TAC[APPEND;];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let BUTLAST_ID = prove_by_refinement(
  `!l. ~(l = []) ==> (l = APPEND (BUTLAST l) [LAST l])`,
(* {{{ Proof *)
[
  MESON_TAC[BUTLAST_ID];
]);;
(* }}} *)

let BUTLAST_NIL = prove_by_refinement(
  `!l. (BUTLAST l = []) <=> (l = []) \/ (?x. l = [x])`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[BUTLAST;];
  REWRITE_TAC[BUTLAST;NOT_CONS_NIL;];
  COND_CASES_TAC;
  ASM_REWRITE_TAC[];
  MESON_TAC[];
  ASM_REWRITE_TAC[];
  POP_ASSUM (fun x -> REWRITE_ALL[x] THEN ASSUME_TAC x);
  REWRITE_TAC[NOT_CONS_NIL];
  STRIP_TAC;
  ASM_MESON_TAC[NOT_CONS_NIL;CONS_11];  
]);; 
(* }}} *)

let INFIN_HD_POS_LEM = prove_by_refinement(
  `!pts p ps r1 sgns.
  interpmat pts 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (CONS (CONS Unknown (CONS Pos r1)) sgns)  ==> 
   nonconstant p ==> 
  ?xminf. 
   interpmat (CONS xminf pts)
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
      (CONS (CONS Neg (CONS Pos r1)) 
      (CONS (CONS Neg (CONS Pos r1)) 
      (CONS (CONS Unknown (CONS Pos r1)) sgns)))`,  
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat;partition_line;];
  REPEAT STRIP_TAC;
  DISJ_CASES_TAC (ISPEC `pts:real list` list_CASES);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`&0`] POLY_DIFF_DOWN_LEFT5));
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN];
  (* save *) 
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[NOT_CONS_NIL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[NOT_CONS_NIL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`h:real`] POLY_DIFF_DOWN_LEFT5));
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  ASM_REWRITE_TAC[real_ordered_list;HD;NOT_CONS_NIL;];
  REWRITE_ALL[APPEND;TL;NOT_CONS_NIL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];  
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  (* save *) 
  POP_ASSUM (fun x -> (REWRITE_ALL[x] THEN ASSUME_TAC x));
  REWRITE_ALL[APPEND;NOT_CONS_NIL;HD;TL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`h:real`] POLY_DIFF_DOWN_LEFT5));
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  ASM_REWRITE_TAC[real_ordered_list;HD;NOT_CONS_NIL;];
  REWRITE_ALL[APPEND;TL;NOT_CONS_NIL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];  
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
]);;
(* }}} *)

let INFIN_TL_POS_LEM = prove_by_refinement(
  `!pts p ps r1 sgns r2.
  interpmat pts 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND sgns [a; b; CONS Unknown (CONS Pos r2)]) ==> 
   nonconstant p ==> 
  ?xinf. 
   interpmat (APPEND pts [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND sgns 
     [a; b; CONS Unknown (CONS Pos r2);
      CONS Pos (CONS Pos r2);
      CONS Pos (CONS Pos r2)])`,
(* {{{ Proof *)

[
  REWRITE_TAC[interpmat;partition_line;];
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (partition_line pts) = LENGTH (APPEND sgns [a; b; CONS Unknown (CONS Pos r2)])`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  CLAIM `LENGTH sgns = LENGTH (partition_line pts) - 3`;
  REWRITE_ALL[PARTITION_LINE_LENGTH];
  ASM_REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;  
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FALSE_ANTECEDENT_TAC;
  ARITH_TAC;
  (* save *) 
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  CLAIM `pts = APPEND (BUTLAST pts) [LAST (pts:real list)]`;
  MATCH_MP_TAC BUTLAST_ID;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `ALL2
       (interpsigns
       (CONS (\x. poly p x)
       (CONS (\x. poly (poly_diff p) x) ps)))
       (partition_line (APPEND (BUTLAST pts) [LAST pts]))
       (APPEND sgns [a; b; CONS Unknown (CONS Pos r2)])`;
  ASM_MESON_TAC[];
  CASES_ON `BUTLAST (pts:real list) = []`;
  CLAIM `?w. pts = [w:real]`;
  ASM_MESON_TAC[BUTLAST_NIL];
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];  
  CLAIM `sgns = []`;
  REPEAT_N 3 (POP_ASSUM (fun x -> ALL_TAC));
  REWRITE_TAC[GSYM LENGTH_0];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  DISCH_THEN (REWRITE_ALL o list);
  REWRITE_ALL[LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];  
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`w:real`] POLY_DIFF_UP_RIGHT3));  
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[ROL_CONS_CONS;ROL_SING];
  REWRITE_ALL[BUTLAST;TL;NOT_CONS_NIL;LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];    
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. w < x`;
  ASM_MESON_TAC[SUBSET;IN];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE];
  ASM_MESON_TAC[REAL_LT_TRANS];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. w < x`;
  ASM_MESON_TAC[SUBSET;IN];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_LT_IMP_LE];
  ASM_MESON_TAC[REAL_LT_IMP_LE;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. w < x`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  (* save *) 
  CLAIM `LENGTH (BUTLAST (partition_line (BUTLAST pts))) = LENGTH sgns`;
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;];
  REWRITE_ALL[PARTITION_LINE_LENGTH;LENGTH_APPEND;LENGTH;];
  MP_TAC (ISPEC `pts:real list` BUTLAST_LENGTH);
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  ASM_MESON_TAC[];
  POP_ASSUM SUBST1_TAC;
  REPEAT_N 4 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM SUBST1_TAC;
  ARITH_TAC;
  STRIP_TAC;
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REWRITE_ALL[BUTLAST;TL;NOT_CONS_NIL;LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];      
  REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`LAST pts:real`] POLY_DIFF_UP_RIGHT3));  
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ROL_INSERT_BACK_THM;
  ASM_REWRITE_TAC[];
  ONCE_ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REWRITE_TAC[partition_line;TL;];
  SIMP_TAC[NOT_CONS_NIL;LAST_APPEND];
  REWRITE_TAC[LAST];
  SIMP_TAC[BUTLAST_APPEND;NOT_CONS_NIL;];
  REWRITE_TAC[BUTLAST;NOT_CONS_NIL;];
  REWRITE_TAC[APPEND_APPEND];
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;BUTLAST;TL;NOT_CONS_NIL;LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];        
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. LAST pts < x`;
  ASM_MESON_TAC[SUBSET;IN];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE];
  ASM_MESON_TAC[REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. LAST pts < x`;
  ASM_MESON_TAC[SUBSET;IN];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE;REAL_LT_IMP_LE];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE;REAL_LT_IMP_LE;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. LAST pts < x`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
]);;

(* }}} *)

let INFIN_HD_NEG_LEM = prove_by_refinement(
  `!pts p ps r1 sgns.
  interpmat pts 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (CONS (CONS Unknown (CONS Neg r1)) sgns)  ==> 
   nonconstant p ==> 
  ?xminf. 
   interpmat (CONS xminf pts)
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
      (CONS (CONS Pos (CONS Neg r1)) 
      (CONS (CONS Pos (CONS Neg r1)) 
      (CONS (CONS Unknown (CONS Neg r1)) sgns)))`,  
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat;partition_line;];
  REPEAT STRIP_TAC;
  DISJ_CASES_TAC (ISPEC `pts:real list` list_CASES);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`&0`] POLY_DIFF_UP_LEFT5));
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[real_gt;REAL_LT_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN];
  (* save *) 
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[NOT_CONS_NIL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[NOT_CONS_NIL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`h:real`] POLY_DIFF_UP_LEFT5));
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  ASM_REWRITE_TAC[real_ordered_list;HD;NOT_CONS_NIL;];
  REWRITE_ALL[APPEND;TL;NOT_CONS_NIL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];  
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  (* save *) 
  POP_ASSUM (fun x -> (REWRITE_ALL[x] THEN ASSUME_TAC x));
  REWRITE_ALL[APPEND;NOT_CONS_NIL;HD;TL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`h:real`] POLY_DIFF_UP_LEFT5));
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  ASM_REWRITE_TAC[real_ordered_list;HD;NOT_CONS_NIL;];
  REWRITE_ALL[APPEND;TL;NOT_CONS_NIL;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];  
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. x < h`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE;];
]);;
(* }}} *)

let INFIN_TL_NEG_LEM = prove_by_refinement(
  `!pts p ps r1 sgns r2.
  interpmat pts 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND sgns [a; b; CONS Unknown (CONS Neg r2)]) ==> 
   nonconstant p ==> 
  ?xinf. 
   interpmat (APPEND pts [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND sgns 
     [a; b; CONS Unknown (CONS Neg r2);
      CONS Neg (CONS Neg r2);
      CONS Neg (CONS Neg r2)])`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat;partition_line;];
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (partition_line pts) = LENGTH (APPEND sgns [a; b; CONS Unknown (CONS Neg r2)])`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  CLAIM `LENGTH sgns = LENGTH (partition_line pts) - 3`;
  REWRITE_ALL[PARTITION_LINE_LENGTH];
  ASM_REWRITE_TAC[LENGTH_APPEND;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;  
  CASES_ON `pts = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FALSE_ANTECEDENT_TAC;
  ARITH_TAC;
  (* save *) 
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  CLAIM `pts = APPEND (BUTLAST pts) [LAST (pts:real list)]`;
  MATCH_MP_TAC BUTLAST_ID;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `ALL2
       (interpsigns
       (CONS (\x. poly p x)
       (CONS (\x. poly (poly_diff p) x) ps)))
       (partition_line (APPEND (BUTLAST pts) [LAST pts]))
       (APPEND sgns [a; b; CONS Unknown (CONS Neg r2)])`;
  ASM_MESON_TAC[];
  CASES_ON `BUTLAST (pts:real list) = []`;
  CLAIM `?w. pts = [w:real]`;
  ASM_MESON_TAC[BUTLAST_NIL];
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];  
  CLAIM `sgns = []`;
  REPEAT_N 3 (POP_ASSUM (fun x -> ALL_TAC));
  REWRITE_TAC[GSYM LENGTH_0];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  DISCH_THEN (REWRITE_ALL o list);
  REWRITE_ALL[LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];  
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`w:real`] POLY_DIFF_DOWN_RIGHT3));  
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[ROL_CONS_CONS;ROL_SING];
  REWRITE_ALL[BUTLAST;TL;NOT_CONS_NIL;LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];    
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. w < x`;
  ASM_MESON_TAC[SUBSET;IN];
  ASM_MESON_TAC[REAL_EQ_IMP_LE;REAL_LT_TRANS;];
  ASM_MESON_TAC[REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. w < x`;
  ASM_MESON_TAC[SUBSET;IN];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_LT_IMP_LE];
  ASM_MESON_TAC[REAL_LT_IMP_LE;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. w < x`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  (* save *) 
  CLAIM `LENGTH (BUTLAST (partition_line (BUTLAST pts))) = LENGTH sgns`;
  ASM_SIMP_TAC[BUTLAST_LENGTH;PARTITION_LINE_NOT_NIL;];
  REWRITE_ALL[PARTITION_LINE_LENGTH;LENGTH_APPEND;LENGTH;];
  MP_TAC (ISPEC `pts:real list` BUTLAST_LENGTH);
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  ASM_MESON_TAC[];
  POP_ASSUM SUBST1_TAC;
  REPEAT_N 4 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM SUBST1_TAC;
  ARITH_TAC;
  STRIP_TAC;
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP x y)));
  REWRITE_ALL[BUTLAST;TL;NOT_CONS_NIL;LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];      
  REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`LAST pts:real`] POLY_DIFF_DOWN_RIGHT3));  
  ASM_REWRITE_TAC[real_gt;];
  STRIP_TAC;
  EXISTS_TAC `Y`;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ROL_INSERT_BACK_THM;
  ASM_REWRITE_TAC[];
  ONCE_ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REWRITE_TAC[partition_line;TL;];
  SIMP_TAC[NOT_CONS_NIL;LAST_APPEND];
  REWRITE_TAC[LAST];
  SIMP_TAC[BUTLAST_APPEND;NOT_CONS_NIL;];
  REWRITE_TAC[BUTLAST;NOT_CONS_NIL;];
  REWRITE_TAC[APPEND_APPEND];
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2;BUTLAST;TL;NOT_CONS_NIL;LAST;LENGTH;LENGTH_APPEND;APPEND;partition_line;ALL2;interpsigns;interpsign;real_gt;ROL_SING];        
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[real_gt;REAL_LT_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. LAST pts < x`;
  ASM_MESON_TAC[SUBSET;IN];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE];
  ASM_MESON_TAC[REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. LAST pts < x`;
  ASM_MESON_TAC[SUBSET;IN];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE;REAL_LT_IMP_LE];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_EQ_IMP_LE;REAL_LT_IMP_LE;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. LAST pts < x`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
]);;
(* }}} *)

let INFIN_POS_POS = prove_by_refinement(
  `!pts p ps r1 sgns r2.
  interpmat pts 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND (CONS (CONS Unknown (CONS Pos r1)) sgns)  
     [a; b; CONS Unknown (CONS Pos r2)]) ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat (APPEND (CONS xminf pts) [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND 
      (CONS (CONS Neg (CONS Pos r1)) 
      (CONS (CONS Neg (CONS Pos r1)) 
      (CONS (CONS Unknown (CONS Pos r1)) sgns)))  
     [a; b; CONS Unknown (CONS Pos r2);
      CONS Pos (CONS Pos r2);
      CONS Pos (CONS Pos r2)])`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_ASSUMS[APPEND];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_HD_POS_LEM);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  EXISTS_TAC `xminf`;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]INFIN_TL_POS_LEM);
  ASM_REWRITE_TAC[APPEND;];
]);;
(* }}} *)

let INFIN_POS_NEG = prove_by_refinement(
  `!pts p ps r1 sgns r2.
  interpmat pts 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND (CONS (CONS Unknown (CONS Pos r1)) sgns)  
     [a; b; CONS Unknown (CONS Neg r2)]) ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat (APPEND (CONS xminf pts) [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND 
      (CONS (CONS Neg (CONS Pos r1)) 
      (CONS (CONS Neg (CONS Pos r1)) 
      (CONS (CONS Unknown (CONS Pos r1)) sgns)))  
     [a; b; CONS Unknown (CONS Neg r2);
      CONS Neg (CONS Neg r2);
      CONS Neg (CONS Neg r2)])`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_ASSUMS[APPEND];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_HD_POS_LEM);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  EXISTS_TAC `xminf`;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]INFIN_TL_NEG_LEM);
  ASM_REWRITE_TAC[APPEND;];
]);;
(* }}} *)

let INFIN_NEG_POS = prove_by_refinement(
  `!pts p ps r1 sgns r2.
  interpmat pts 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND (CONS (CONS Unknown (CONS Neg r1)) sgns)  
     [a; b; CONS Unknown (CONS Pos r2)]) ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat (APPEND (CONS xminf pts) [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND 
      (CONS (CONS Pos (CONS Neg r1)) 
      (CONS (CONS Pos (CONS Neg r1)) 
      (CONS (CONS Unknown (CONS Neg r1)) sgns)))  
     [a; b; CONS Unknown (CONS Pos r2);
      CONS Pos (CONS Pos r2);
      CONS Pos (CONS Pos r2)])`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_ASSUMS[APPEND];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_HD_NEG_LEM);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  EXISTS_TAC `xminf`;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]INFIN_TL_POS_LEM);
  ASM_REWRITE_TAC[APPEND;];
]);;
(* }}} *)

let INFIN_NEG_NEG = prove_by_refinement(
  `!pts p ps r1 sgns r2.
  interpmat pts 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND (CONS (CONS Unknown (CONS Neg r1)) sgns)  
     [a; b; CONS Unknown (CONS Neg r2)]) ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat (APPEND (CONS xminf pts) [xinf])
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    (APPEND 
      (CONS (CONS Pos (CONS Neg r1)) 
      (CONS (CONS Pos (CONS Neg r1)) 
      (CONS (CONS Unknown (CONS Neg r1)) sgns)))  
     [a; b; CONS Unknown (CONS Neg r2);
      CONS Neg (CONS Neg r2);
      CONS Neg (CONS Neg r2)])`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_ASSUMS[APPEND];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_HD_NEG_LEM);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  EXISTS_TAC `xminf`;
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM]INFIN_TL_NEG_LEM);
  ASM_REWRITE_TAC[APPEND;];
]);;
(* }}} *)

let INFIN_NIL_POS = prove_by_refinement(
  `!p ps r1.
  interpmat [] 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    [CONS Unknown (CONS Pos r1)]  ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat [xminf; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
      [CONS Neg (CONS Pos r1); 
       CONS Neg (CONS Pos r1); 
       CONS Unknown (CONS Pos r1);
       CONS Pos (CONS Pos r1);
       CONS Pos (CONS Pos r1)]`,  
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt;interpmat;partition_line;ROL_NIL;ALL2;interpsigns;interpsign];
  REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`&0`] POLY_DIFF_UP_RIGHT3));
  ASM_REWRITE_TAC[real_gt];
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`&0`] POLY_DIFF_DOWN_LEFT5));
  ASM_REWRITE_TAC[real_gt];
  STRIP_TAC;
  EXISTS_TAC `Y'`;
  EXISTS_TAC `Y`;
  ASM_REWRITE_TAC[real_gt;NOT_CONS_NIL;HD;TL;APPEND;ALL2;interpsigns;interpsign];
  REWRITE_TAC[ROL_CONS_CONS;ROL_SING];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
]);;
(* }}} *)

let INFIN_NIL_NEG = prove_by_refinement(
  `!p ps r1.
  interpmat [] 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    [CONS Unknown (CONS Neg r1)]  ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat [xminf; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
      [CONS Pos (CONS Neg r1); 
       CONS Pos (CONS Neg r1); 
       CONS Unknown (CONS Neg r1);
       CONS Neg (CONS Neg r1);
       CONS Neg (CONS Neg r1)]`,  
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt;interpmat;partition_line;ROL_NIL;ALL2;interpsigns;interpsign];
  REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`&0`] POLY_DIFF_DOWN_RIGHT3));
  ASM_REWRITE_TAC[real_gt];
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP (ISPECL [`p:real list`;`poly_diff p`;`&0`] POLY_DIFF_UP_LEFT5));
  ASM_REWRITE_TAC[real_gt];
  STRIP_TAC;
  EXISTS_TAC `Y'`;
  EXISTS_TAC `Y`;
  ASM_REWRITE_TAC[real_gt;NOT_CONS_NIL;HD;TL;APPEND;ALL2;interpsigns;interpsign];
  REWRITE_TAC[ROL_CONS_CONS;ROL_SING];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
  ASM_MESON_TAC[REAL_LT_TRANS;REAL_LT_IMP_LE;REAL_EQ_IMP_LE];
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] ALL2_INTERPSIGN_SUBSET);
  EXISTS_TAC `\x. T`;
  ASM_MESON_TAC[SUBSET;IN;REAL_LT_TRANS;];
]);;
(* }}} *)

let INFIN_SING_POS_POS = prove_by_refinement(
  `!p ps r1 x s2 r2 r3.
  interpmat [x] 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    [CONS Unknown (CONS Pos r1);CONS s2 r2;CONS Unknown (CONS Pos r3)]  ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat [xminf; x; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
      [CONS Neg (CONS Pos r1); 
       CONS Neg (CONS Pos r1); 
       CONS Unknown (CONS Pos r1);
       CONS s2 r2;
       CONS Unknown (CONS Pos r3);
       CONS Pos (CONS Pos r3);
       CONS Pos (CONS Pos r3)]`,  
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  ONCE_REWRITE_ASSUMS[prove(`[x; y; z] = APPEND [] [x; y; z]`,REWRITE_TAC[APPEND])];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_TL_POS_LEM);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MATCH_MP_TAC (prove(`(?y x. P x y) ==> (?x y. P x y)`,MESON_TAC[]));
  EXISTS_TAC `xinf`;
  REWRITE_ALL[APPEND];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_HD_POS_LEM);
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let INFIN_SING_POS_NEG = prove_by_refinement(
  `!p ps r1 x s2 r2 r3.
  interpmat [x] 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    [CONS Unknown (CONS Pos r1);CONS s2 r2;CONS Unknown (CONS Neg r3)]  ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat [xminf; x; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
      [CONS Neg (CONS Pos r1); 
       CONS Neg (CONS Pos r1); 
       CONS Unknown (CONS Pos r1);
       CONS s2 r2;
       CONS Unknown (CONS Neg r3);
       CONS Neg (CONS Neg r3);
       CONS Neg (CONS Neg r3)]`,  
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  ONCE_REWRITE_ASSUMS[prove(`[x; y; z] = APPEND [] [x; y; z]`,REWRITE_TAC[APPEND])];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_TL_NEG_LEM);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MATCH_MP_TAC (prove(`(?y x. P x y) ==> (?x y. P x y)`,MESON_TAC[]));
  EXISTS_TAC `xinf`;
  REWRITE_ALL[APPEND];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_HD_POS_LEM);
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let INFIN_SING_NEG_POS = prove_by_refinement(
  `!p ps r1 x s2 r2 r3.
  interpmat [x] 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    [CONS Unknown (CONS Neg r1);CONS s2 r2;CONS Unknown (CONS Pos r3)]  ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat [xminf; x; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
      [CONS Pos (CONS Neg r1); 
       CONS Pos (CONS Neg r1); 
       CONS Unknown (CONS Neg r1);
       CONS s2 r2;
       CONS Unknown (CONS Pos r3);
       CONS Pos (CONS Pos r3);
       CONS Pos (CONS Pos r3)]`,  
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  ONCE_REWRITE_ASSUMS[prove(`[x; y; z] = APPEND [] [x; y; z]`,REWRITE_TAC[APPEND])];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_TL_POS_LEM);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MATCH_MP_TAC (prove(`(?y x. P x y) ==> (?x y. P x y)`,MESON_TAC[]));
  EXISTS_TAC `xinf`;
  REWRITE_ALL[APPEND];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_HD_NEG_LEM);
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let INFIN_SING_NEG_NEG = prove_by_refinement(
  `!p ps r1 x s2 r2 r3.
  interpmat [x] 
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
    [CONS Unknown (CONS Neg r1);CONS s2 r2;CONS Unknown (CONS Neg r3)]  ==> 
   nonconstant p ==> 
  ?xminf xinf. 
   interpmat [xminf; x; xinf]
    (CONS (\x. poly p x) (CONS (\x. poly (poly_diff p) x) ps)) 
      [CONS Pos (CONS Neg r1); 
       CONS Pos (CONS Neg r1); 
       CONS Unknown (CONS Neg r1);
       CONS s2 r2;
       CONS Unknown (CONS Neg r3);
       CONS Neg (CONS Neg r3);
       CONS Neg (CONS Neg r3)]`,  
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  ONCE_REWRITE_ASSUMS[prove(`[x; y; z] = APPEND [] [x; y; z]`,REWRITE_TAC[APPEND])];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_TL_NEG_LEM);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MATCH_MP_TAC (prove(`(?y x. P x y) ==> (?x y. P x y)`,MESON_TAC[]));
  EXISTS_TAC `xinf`;
  REWRITE_ALL[APPEND];
  FIRST_ASSUM (MP_TAC o MATCH_MP INFIN_HD_NEG_LEM);
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let EL_SUC = prove_by_refinement(
  `!i h t. EL (SUC i) (CONS h t) = EL i t`,
(* {{{ Proof *)
[
  REWRITE_TAC[EL;TL];
]);;
(* }}} *)

let EL_PRE = prove_by_refinement(
  `!i h t. ~(i = 0) ==> (EL i (CONS h t) = EL (PRE i) t)`,
(* {{{ Proof *)
[
  INDUCT_TAC;
  REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REWRITE_TAC[EL;TL;PRE];
]);; 
(* }}} *)

let ALL2_EL_LT_LEM = prove_by_refinement(
  `!k P l1 l2 n. 
    (k = LENGTH l1) /\ ALL2 P l1 l2 /\ n < k ==> 
       P (EL n l1) (EL n l2)`,
(* {{{ Proof *)
[
  INDUCT_TAC;
  REPEAT STRIP_TAC;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_LENGTH);
  STRIP_TAC;
  CLAIM `~(l1 = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  REPEAT_N 3 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL;];
  STRIP_TAC;
  CLAIM `~(l2 = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (SUBST1_TAC o GSYM);
  REPEAT_N 2 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL;];
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ASSUMS[LENGTH;SUC_INJ;ALL2;];
  REPEAT_N 3 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  (* save *) 
  DISJ_CASES_TAC (ISPEC `n:num` num_CASES);
  POP_ASSUM (REWRITE_ALL o list);
  ASM_REWRITE_TAC[EL;HD];
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;TL;];
  REWRITE_ASSUMS[LENGTH;SUC_INJ;ALL2;LT_SUC];  
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let ALL2_EL_LT = prove_by_refinement(
  `!P l1 l2 n. ALL2 P l1 l2 /\ n < LENGTH l1 ==> P (EL n l1) (EL n l2)`,
(* {{{ Proof *)
[
  MESON_TAC[ALL2_EL_LT_LEM];
]);;
(* }}} *)

let ALL2_EL_LEM = prove_by_refinement(
  `!k P (l1:A list) (l2:B list).  (k = LENGTH l1) /\ (k = LENGTH l2) /\ 
    ~(?i. i < LENGTH l1 /\ ~(P (EL i l1) (EL i l2))) ==> ALL2 P l1 l2`,
(* {{{ Proof *)
[
  INDUCT_TAC;
  REPEAT STRIP_TAC;
  EVERY_ASSUM (MP_TAC o GSYM);
  ASM_MESON_TAC[LENGTH_0;ALL2];
  REPEAT STRIP_TAC;
  CLAIM `~(l1 = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  REPEAT_N 2 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL;];
  STRIP_TAC;
  CLAIM `~(l2 = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  REPEAT_N 2 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL;];
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[LENGTH;SUC_INJ;ALL2;];
  STRIP_TAC;
  ASM_MESON_TAC[LT_0;EL;HD;];
  (* save *) 
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_MESON_TAC[];
  REPEAT STRIP_TAC;
  CLAIM `SUC i < SUC (LENGTH t)`;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  REPEAT_N 3 (POP_ASSUM MP_TAC);
  REWRITE_ASSUMS[NOT_EXISTS_THM];
  POP_ASSUM (ASSUME_TAC o ISPEC `SUC i`);
  REWRITE_ALL[LT_SUC];
  REWRITE_ALL[EL;TL;];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let ALL2_EL = prove_by_refinement(
  `!P (l1:A list) (l2:B list). ALL2 P l1 l2 <=> (LENGTH l1 = LENGTH l2) /\ 
    ~(?i. i < LENGTH l1 /\ ~(P (EL i l1) (EL i l2)))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  EQ_TAC;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_LENGTH;
  ASM_MESON_TAC[];
  ASM_MESON_TAC[ALL2_EL_LT];
  (* save *) 
  ASM_MESON_TAC[ALL2_EL_LEM];
]);;
(* }}} *)

let EL_MAP = prove_by_refinement(
  `!f l n. n < LENGTH l ==> (EL n (MAP f l) = f (EL n l))`,
(* {{{ Proof *)
[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  REWRITE_TAC[MAP;LENGTH;];
  INDUCT_TAC;
  REWRITE_TAC[MAP;LENGTH;EL;HD;];  
  REWRITE_ALL[LT_SUC;TL;MAP;LENGTH;EL;HD;];  
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let REMOVE_HD_COL = prove_by_refinement(
  `!p ps sgns pts. 
    interpmat pts (CONS p ps) sgns ==> interpmat pts ps (MAP TL sgns)`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat;ALL2_EL];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[ALL2_EL];
  ASM_MESON_TAC[LENGTH_MAP];
  REWRITE_ASSUMS[NOT_EXISTS_THM];
  REPEAT_N 2 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `i:num`);
  REWRITE_TAC[DE_MORGAN_THM];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[];
  REWRITE_ALL[interpsigns];
  CLAIM `i < LENGTH sgns`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  ASM_SIMP_TAC[EL_MAP];
  REWRITE_ALL[interpsigns];
  CLAIM `~(EL i sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_LENGTH);
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  (* save *) 
  DISCH_THEN (MP_TAC o MATCH_MP HD_TL);
  DISCH_THEN (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN SUBST1_TAC x);
  REWRITE_TAC[ALL2;TL;];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;                                            
(* }}} *)

let REMOVE_COL1 = prove_by_refinement(
  `!sgns pts p1 p2 ps. 
   interpmat pts (CONS p1 (CONS p2 ps)) sgns ==> 
   interpmat pts (CONS p1 ps) (MAP (\x. CONS (HD x) (TL (TL x))) sgns)`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat;ALL2_EL];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[LENGTH_MAP];
  REWRITE_ASSUMS[NOT_EXISTS_THM];
  REPEAT_N 2 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `i:num`);
  REWRITE_TAC[DE_MORGAN_THM];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[];
  REWRITE_ALL[interpsigns];
  CLAIM `i < LENGTH sgns`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  ASM_SIMP_TAC[EL_MAP];
  REWRITE_ALL[interpsigns];
  CLAIM `~(EL i sgns = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_LENGTH);
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  (* save *) 
  DISCH_THEN (MP_TAC o MATCH_MP HD_TL);
  DISCH_THEN (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN SUBST1_TAC x);
  REWRITE_TAC[ALL2;TL;];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[HD;];
  CLAIM `~(TL (EL i sgns) = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_LENGTH);
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  (* save *) 
  DISCH_THEN (MP_TAC o MATCH_MP HD_TL);
  DISCH_THEN (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN SUBST1_TAC x);
  REWRITE_TAC[ALL2;TL;];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[HD;];
]);;
(* }}} *)

let ALL_EL = prove_by_refinement(
  `!P l. ALL P l <=> !n. n < LENGTH l ==> P (EL n l)`,
(* {{{ Proof *)
[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[ALL;LENGTH];
  ARITH_TAC;
  ASM_REWRITE_TAC[ALL];
  POP_ASSUM (fun x -> ALL_TAC);
  EQ_TAC;
  REPEAT STRIP_TAC;
  CASES_ON `n = 0`;
  POP_ASSUM (REWRITE_ALL o list);
  ASM_REWRITE_TAC[EL;HD;];
  REWRITE_ASSUMS[LENGTH];
  CLAIM `PRE n < LENGTH t`;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
  DISCH_THEN (fun x -> FIRST_ASSUM (MP_TAC o C MATCH_MP x));
  ASM_MESON_TAC[EL_PRE];
  (* save *) 
  REPEAT STRIP_TAC;
  REWRITE_ASSUMS[LENGTH];
  FIRST_ASSUM (MP_TAC o ISPEC `0`);
  REWRITE_TAC[EL;HD;];
  MESON_TAC[LT_0];
  REWRITE_ASSUMS[LENGTH];
  CLAIM `SUC n < SUC (LENGTH t)`;
  ASM_MESON_TAC[LT_SUC];
  DISCH_THEN (fun x -> FIRST_ASSUM (MP_TAC o C MATCH_MP x));
  REWRITE_TAC[EL_SUC];
]);;
(* }}} *)

let INTERPMAT_POL_LENGTH_LEM = prove_by_refinement(
  `!k pols l1 l2. ALL2 (interpsigns pols) l1 l2 /\ (k = LENGTH l2) ==>  
    ALL (\x. LENGTH x = LENGTH pols) l2`,
(* {{{ Proof *)
[
  INDUCT_TAC;
  REPEAT STRIP_TAC;
  CLAIM `l2 = []`;
  ASM_MESON_TAC[NOT_CONS_NIL;LENGTH_0;ALL2_LENGTH];
  DISCH_THEN (REWRITE_ALL o list);
  REWRITE_TAC[ALL];
  REPEAT STRIP_TAC;
  CLAIM `~(l2 = [])`;
  ASM_MESON_TAC[NOT_CONS_NIL;LENGTH_0;ALL2_LENGTH;NOT_SUC];
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC THEN (POP_ASSUM (REWRITE_ALL o list));
  CLAIM `~(l1 = [])`;
  ASM_MESON_TAC[NOT_CONS_NIL;LENGTH_0;ALL2_LENGTH;NOT_SUC];
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC THEN (POP_ASSUM (REWRITE_ALL o list));  
  REWRITE_ALL[ALL2;ALL;interpsigns];
  STRIP_TAC;
  ASM_MESON_TAC[ALL2_LENGTH];
  FIRST_ASSUM MATCH_MP_TAC;
  EXISTS_TAC `t'`;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[LENGTH];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
]);;
(* }}} *)

let INTERPMAT_POL_LENGTH = prove_by_refinement(
  `!pts pols sgns. interpmat pts pols sgns ==> 
    ALL (\x. LENGTH x = LENGTH pols) sgns`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  MESON_TAC[INTERPMAT_POL_LENGTH_LEM];
]);;
(* }}} *)

let RESTRIP_TAC = REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;;

let ALL2_BUTLAST = prove_by_refinement(
  `!P l1 l2. ALL2 P l1 l2 ==> ALL2 P (BUTLAST l1) (BUTLAST l2)`,
(* {{{ Proof *)

[
  STRIP_TAC;
  REPEAT LIST_INDUCT_TAC;
  REWRITE_TAC[ALL2;BUTLAST];
  REWRITE_TAC[ALL2;BUTLAST];
  REWRITE_TAC[ALL2;BUTLAST];
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_TAC[ALL2;BUTLAST;];
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL;ALL2;];
  REWRITE_ASSUMS[NOT_NIL];
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[ALL2];
  REWRITE_ASSUMS[NOT_NIL];
  RESTRIP_TAC;
  ASM_MESON_TAC[ALL2];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM MATCH_MP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;

(* }}} *)

let REMOVE_LAST = prove_by_refinement(
  `!pts pols sgns . 
     interpmat pts pols sgns ==> 
     interpmat pts (BUTLAST pols) (MAP BUTLAST sgns)`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat;ALL2_EL];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[LENGTH_MAP];
  REWRITE_ASSUMS[NOT_EXISTS_THM];
  REPEAT_N 2 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `i:num`);
  REWRITE_TAC[DE_MORGAN_THM];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[];
  REWRITE_ALL[interpsigns];
  CLAIM `i < LENGTH sgns`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  (* save *) 
  ASM_SIMP_TAC[EL_MAP];
  ASM_MESON_TAC[ALL2_BUTLAST];
]);;                                            
(* }}} *)

let INSERTAT = new_recursive_definition num_RECURSION
  `(INSERTAT 0 x l = CONS x l) /\ 
   (INSERTAT (SUC n) x l = CONS (HD l) (INSERTAT n x (TL l)))`;;

let MAP2_EL_LEM = prove_by_refinement(
  `!f k l1 l2 i. (LENGTH l1 = LENGTH l2) ==> i < LENGTH l1 ==> 
    (k = LENGTH l1) ==> 
     (EL i (MAP2 f l1 l2) = f (EL i l1) (EL i l2))`,
(* {{{ Proof *)
[
  STRIP_TAC;
  INDUCT_TAC;
  REPEAT STRIP_TAC;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
  REPEAT STRIP_TAC;
  CLAIM `~(l1 = [])`;
  ASM_MESON_TAC[LENGTH_0;NOT_SUC];
  CLAIM `~(l2 = [])`;
  ASM_MESON_TAC[LENGTH_0;NOT_SUC];
  REWRITE_TAC[NOT_NIL];
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[MAP2];
  REWRITE_ALL[LENGTH;SUC_INJ];
  DISJ_CASES_TAC (ISPEC `i:num` num_CASES);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;HD;];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;TL;];
  REWRITE_ASSUMS[LT_SUC];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let MAP2_EL = prove_by_refinement(
  `!f i l1 l2. (LENGTH l1 = LENGTH l2) ==> i < LENGTH l1 ==> 
     (EL i (MAP2 f l1 l2) = f (EL i l1) (EL i l2))`,
(* {{{ Proof *)
[
  MESON_TAC[MAP2_EL_LEM];
]);; 
(* }}} *)

let INSERTAT_LENGTH = prove_by_refinement(
  `!x n l. n <= LENGTH l ==> (LENGTH (INSERTAT n x l) = SUC (LENGTH l))`,
(* {{{ Proof *)

[
  STRIP_TAC;
  INDUCT_TAC;
  REWRITE_TAC[INSERTAT;LENGTH;];
  REWRITE_TAC[INSERTAT;LENGTH;];
  REPEAT STRIP_TAC;
  AP_TERM_TAC;
  CLAIM `~(l = [])`;
  ASM_MESON_TAC[LENGTH_0;NOT_LE;ARITH_RULE `~(SUC n <= 0)`];
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[LENGTH;TL;LE_SUC];
  ASM_MESON_TAC[];
]);; 

(* }}} *)

let NUM_CASES_TAC = TYPE_TAC (fun x -> DISJ_CASES_TAC (ISPEC x num_CASES));;

let INSERTAT_TL = prove_by_refinement(
  `!x n l. n < LENGTH l ==> (INSERTAT n x (TL l) = TL (INSERTAT (SUC n) x l))`,
(* {{{ Proof *)
[
  STRIP_TAC;
  INDUCT_TAC;
  REPEAT STRIP_TAC;
  REWRITE_TAC[INSERTAT;TL;];
  REPEAT STRIP_TAC;
  CLAIM `n < LENGTH l \/ (n = LENGTH l)`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  REWRITE_TAC[INSERTAT;HD;TL;];
  REWRITE_TAC[INSERTAT;HD;TL;];
]);;
(* }}} *)

let INSERTAT_EL = prove_by_refinement(
  `!n (x:A) i l. n <= LENGTH l ==> i <= LENGTH l ==> 
   ((i < n ==> (EL i (INSERTAT n x l) = EL i l)) /\ 
   ((i = n) ==> (EL i (INSERTAT n x l) = x)) /\ 
   (i > n ==> (EL i (INSERTAT n x l) = EL (PRE i) l)))`,
(* {{{ Proof *)
[
  INDUCT_TAC;
  REPEAT STRIP_TAC;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  ASM_REWRITE_TAC[INSERTAT;EL;HD;];
  ASM_REWRITE_TAC[INSERTAT;EL;HD;];
  DISJ_CASES_TAC (ISPEC `i:num` num_CASES);
  EVERY_ASSUM MP_TAC THEN ARITH_TAC;
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;TL;PRE];
  (* save *) 
  REPEAT_N 5 STRIP_TAC;
  CLAIM `~(l = [])`;
  ASM_MESON_TAC[LENGTH_0;NOT_LE;ARITH_RULE `~(SUC n <= 0)`];
  STRIP_TAC;
  CLAIM `n <= LENGTH (TL l)`;
  ASM_SIMP_TAC[LENGTH_TL];
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  (* save *) 
  REPEAT STRIP_TAC;
  REWRITE_TAC[INSERTAT];
  NUM_CASES_TAC `i`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;HD;];
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;TL;];
  CLAIM `n' <= LENGTH (TL l)`;
  REWRITE_ASSUMS[LT_SUC];
  ASM_MESON_TAC[LTE_TRANS;LT_TRANS;LET_TRANS;LT_IMP_LE];
  STRIP_TAC;
  REWRITE_ASSUMS[LT_SUC];
  ASM_MESON_TAC[];
  (* save *) 
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;INSERTAT;TL;];
  ASM_MESON_TAC[];
  REWRITE_TAC[INSERTAT];
  NUM_CASES_TAC `i`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;HD;PRE];
  (* save *) 
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;TL;PRE];
  CLAIM `n' <= LENGTH (TL l)`;
  ASM_SIMP_TAC[LENGTH_TL];
  REPEAT_N 3 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  REWRITE_ASSUMS[GT;LT_SUC];
  FIRST_X_ASSUM (MP_TAC o ISPECL[`x:A`;`n':num`;`TL l:A list`]); 
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  NUM_CASES_TAC `n'`;
  ASM_MESON_TAC[ARITH_RULE `x < y ==> ~(y = 0)`];
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[PRE;EL];
]);;
(* }}} *)

let USE_X_ASSUM lab ttac =
    USE_THEN lab (fun th -> UNDISCH_THEN (concl th) ttac);;

let MATINSERT_THM = prove_by_refinement(
  `!pts p pols n psgns sgns.
     interpmat pts pols sgns ==> 
     ALL2 (\x y. interpsign x p y) (partition_line pts) psgns ==> 
     n <= LENGTH pols ==> 
      interpmat pts (INSERTAT n p pols) (MAP2 (INSERTAT n) psgns sgns)`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat;ALL2_EL;NOT_EXISTS_THM;DE_MORGAN_THM;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  CLAIM `LENGTH (psgns:sign list) = LENGTH sgns`;
  ASM_MESON_TAC[LENGTH_MAP2];
  ASM_MESON_TAC[LENGTH_MAP2];  
  DISJ_LCASE;
  REWRITE_ASSUMS[];
  (* save *) 
  REWRITE_ALL[interpsigns];
  CLAIM `LENGTH psgns = LENGTH sgns`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `i < LENGTH psgns`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  ASM_SIMP_TAC[MAP2_EL];
  (* save *) 
  REWRITE_TAC[ALL2_EL];
  REWRITE_TAC[NOT_EXISTS_THM;DE_MORGAN_THM];
  REPEAT STRIP_TAC;
  ASM_SIMP_TAC[INSERTAT_LENGTH];
  CLAIM `LENGTH (EL i (sgns:(sign list) list)) = LENGTH pols`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  ASM_SIMP_TAC[INSERTAT_LENGTH];
  (* save *) 
  DISJ_LCASE;
  REWRITE_ASSUMS[];
  MP_TAC (ARITH_RULE `i' < n \/ (i' = n) \/ i' > (n:num)`);
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (EL i sgns) = LENGTH pols`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  CLAIM `n <= LENGTH (EL i sgns)`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `i' <= LENGTH (EL i sgns)`;
  ASM_MESON_TAC[LTE_TRANS;LET_TRANS;LT_TRANS;LT_IMP_LE];
  STRIP_TAC;
  ASM_SIMP_TAC[INSERTAT_EL];
  CLAIM `i' <= LENGTH pols`;
  ASM_MESON_TAC[LTE_TRANS;LET_TRANS;LT_TRANS;LT_IMP_LE];  
  STRIP_TAC;
  ASM_SIMP_TAC[INSERTAT_EL];
  REPEAT_N 12 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `i:num`);
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[];
  LABEL_ALL_TAC;
  USE_THEN "Z-12" MP_TAC;
  REWRITE_TAC[ALL2_EL];
  REWRITE_TAC[NOT_EXISTS_THM;DE_MORGAN_THM];
  STRIP_TAC;
  POP_ASSUM (MP_TAC o ISPEC `i':num`);
  POP_ASSUM (fun x -> ALL_TAC);
  ASM_REWRITE_TAC[];
  POP_ASSUM (fun x -> ALL_TAC);
  STRIP_TAC;
  ASM_MESON_TAC[ARITH_RULE `x <= y /\ z < x ==> z < (y:num)`];
  (* save *) 
  POP_ASSUM (REWRITE_ALL o list);
  CLAIM `LENGTH (EL i sgns) = LENGTH pols`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  CLAIM `n <= LENGTH (EL i sgns)`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  ASM_SIMP_TAC[INSERTAT_EL];
  ASM_MESON_TAC[ALL2_EL];
  (* save *) 
  CLAIM `LENGTH (EL i sgns) = LENGTH pols`;
  ASM_MESON_TAC[ALL2_LENGTH];
  STRIP_TAC;
  CLAIM `n <= LENGTH (EL i sgns)`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `i' <= LENGTH (EL i sgns)`;
  ASM_REWRITE_TAC[];
  LABEL_ALL_TAC;
  USE_THEN "Z-7" (MP_TAC o MATCH_MP INSERTAT_LENGTH);
  TYPE_TAC (fun x -> DISCH_THEN (MP_TAC o ISPEC x)) `p`;
  USE_THEN "Z-3" MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `i' <= LENGTH pols`;  
  ASM_MESON_TAC[];
  STRIP_TAC;
  ASM_SIMP_TAC[INSERTAT_EL];  
  LABEL_ALL_TAC;
  (* save *) 
  USE_X_ASSUM "Z-12" (MP_TAC o ISPEC `i:num`);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[ALL2_EL];  
  ASM_REWRITE_TAC[NOT_EXISTS_THM;DE_MORGAN_THM;];
  DISCH_THEN (MP_TAC o ISPEC `PRE i':num`);
  STRIP_TAC;
  CLAIM `~(i' = 0)`;
  USE_THEN "Z-4" MP_TAC THEN ARITH_TAC;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
]);;
(* }}} *)
 
let INTERP_CONST_POS = prove_by_refinement(
  `!c l. c > &0 ==> 
    ALL2 (\x y. interpsign x (\x. c) y) l (REPLICATE (LENGTH l) Pos)`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt;];
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[REPLICATE;LENGTH;ALL2;];
  DISCH_THEN (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  REWRITE_TAC[REPLICATE;LENGTH;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[REPLICATE;LENGTH;ALL2;interpsign;real_gt;];
]);;
(* }}} *)

let INTERP_CONST_NEG = prove_by_refinement(
  `!c l. c < &0 ==> 
    ALL2 (\x y. interpsign x (\x. c) y) l (REPLICATE (LENGTH l) Neg)`,
(* {{{ Proof *)
[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[REPLICATE;LENGTH;ALL2;];
  DISCH_THEN (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  REWRITE_TAC[REPLICATE;LENGTH;ALL2;interpsign;real_gt;];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let INTERP_CONST_ZERO = prove_by_refinement(
  `!c l. (c = &0) ==> 
    ALL2 (\x y. interpsign x (\x. c) y) l (REPLICATE (LENGTH l) Zero)`,
(* {{{ Proof *)
[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[REPLICATE;LENGTH;ALL2;];
  DISCH_THEN (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  REWRITE_TAC[REPLICATE;LENGTH;ALL2;interpsign;real_gt;];
  ASM_REWRITE_TAC[];
  (* XXX MESON FAILS HERE *)
]);;
(* }}} *)

let QUANT_CONV conv = RAND_CONV(ABS_CONV conv);;

let rec PATH_CONV2 s cnv =
  match s with
    [] -> cnv
  | "l"::t -> RATOR_CONV (PATH_CONV2 t cnv)
  | "r"::t -> RAND_CONV (PATH_CONV2 t cnv)
  | "q"::t -> QUANT_CONV (PATH_CONV2 t cnv)
  | "a"::t -> ABS_CONV (PATH_CONV2 t cnv)
  | _ -> failwith "PATH_CONV2: unknown direction";;
                 
let EL_REPLICATE = prove_by_refinement(
  `!n x i. i < n ==> (EL i (REPLICATE n x) = x)`,
(* {{{ Proof *)
[
  INDUCT_TAC;
  ARITH_TAC;
  REPEAT STRIP_TAC;
  REWRITE_TAC[REPLICATE];
  NUM_CASES_TAC `i`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;HD;];
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  REWRITE_TAC[EL;TL;];
  ASM_MESON_TAC[LT_SUC];
]);;
(* }}} *)

let ALL2_UNKNOWN = prove_by_refinement(
  `!p pts. ALL2 (\x y. interpsign x p y) (partition_line pts) 
    (REPLICATE (LENGTH (partition_line pts)) Unknown)`,
(* {{{ Proof *)
[
  REWRITE_TAC[ALL2_EL];
  REWRITE_TAC[NOT_EXISTS_THM;DE_MORGAN_THM];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[LENGTH_REPLICATE];
  DISJ_LCASE;
  REWRITE_ASSUMS[];
  ASM_SIMP_TAC[EL_REPLICATE];
  REWRITE_TAC[interpsign];
]);;
(* }}} *)

let MATINSERT_THM2 = prove_by_refinement(
  `!pts p pols n psgns sgns.
    ALL2 (\x y. interpsign x p y) (partition_line pts) psgns ==> 
    n <= LENGTH pols ==> 
    interpmat pts pols sgns ==> 
     interpmat pts (INSERTAT n p pols) (MAP2 (INSERTAT n) psgns sgns)`,
(* {{{ Proof *)
[
  MESON_TAC[MATINSERT_THM]
]);;
(* }}} *)

let FUN_EQ_TAC = MATCH_EQ_MP_TAC (GSYM FUN_EQ_THM);;

let INSERTAT_0 = prove_by_refinement(
  `INSERTAT 0 = CONS`,
(* {{{ Proof *)
[
  FUN_EQ_TAC;
  STRIP_TAC;
  FUN_EQ_TAC;
  REWRITE_TAC[INSERTAT];
]);;
(* }}} *)

let INFERPSIGN_MATINSERT_THM = prove_by_refinement(
  `!pts p pols sgns.
    interpmat pts pols sgns ==> 
     interpmat pts (CONS p pols) 
      (MAP2 CONS 
        (REPLICATE (2 * LENGTH pts + 1) Unknown) sgns)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  TYPE_TACL (fun l -> MP_TAC (ISPECL l MATINSERT_THM))
   [`pts`;`p`;`pols`;`0`;`REPLICATE (LENGTH (partition_line pts)) Unknown`;`sgns`];
  ASM_REWRITE_TAC[ALL2_UNKNOWN;ARITH_RULE `0 <= x`;INSERTAT;PARTITION_LINE_LENGTH];
  MESON_TAC[INSERTAT_0];
]);;
(* }}} *)

let INFERPSIGN_POS = prove_by_refinement(
  `!p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==> 
  (!x. p x = s x * q x + r x) ==> 
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Pos s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest))`,
(* {{{ Proof *)

[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  CASES_ON `pts1 = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;];
  COND_CASES_TAC;
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 5 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_TAC[REAL_MUL_RZERO;REAL_ADD_LID;];
  FIRST_ASSUM MATCH_MP_TAC;
  REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  (* save *) 
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_TAC[REAL_MUL_RZERO;REAL_ADD_LID;];
  FIRST_ASSUM MATCH_MP_TAC;
  REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REPEAT STRIP_TAC;
  CLAIM `(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) = 
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))`;
  ASM_MESON_TAC[APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[partition_line];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  REWRITE_ALL[TL;];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  RESTRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_TAC[REAL_MUL_RZERO;REAL_ADD_LID;];
  FIRST_ASSUM MATCH_MP_TAC;
  REWRITE_TAC[];
  (* save *) 
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REWRITE_ALL[TL;ALL2;interpsign;interpsigns;APPEND];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_TAC[REAL_MUL_RZERO;REAL_ADD_LID;];
  FIRST_ASSUM MATCH_MP_TAC;
  REWRITE_TAC[];
]);;  

(* }}} *)

let INFERPSIGN_NEG = prove_by_refinement(
  `!p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==> 
  (!x. p x = s x * q x + r x) ==> 
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Neg s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  CASES_ON `pts1 = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;];
  COND_CASES_TAC;
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 5 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_TAC[REAL_MUL_RZERO;REAL_ADD_LID;];
  FIRST_ASSUM MATCH_MP_TAC;
  REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  (* save *) 
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_TAC[REAL_MUL_RZERO;REAL_ADD_LID;];
  FIRST_ASSUM MATCH_MP_TAC;
  REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REPEAT STRIP_TAC;
  CLAIM `(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) = 
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))`;
  ASM_MESON_TAC[APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[partition_line];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  REWRITE_ALL[TL;];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  RESTRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_TAC[REAL_MUL_RZERO;REAL_ADD_LID;];
  FIRST_ASSUM MATCH_MP_TAC;
  REWRITE_TAC[];
  (* save *) 
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REWRITE_ALL[TL;ALL2;interpsign;interpsigns;APPEND];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  REWRITE_TAC[REAL_MUL_RZERO;REAL_ADD_LID;];
  FIRST_ASSUM MATCH_MP_TAC;
  REWRITE_TAC[];
]);;  
(* }}} *)

let INFERPSIGN_POS_EVEN_LEM = prove_by_refinement(
  `!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a <> &0) ==> 
  EVEN n ==> 
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Pos s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `a pow n > &0`;
  ASM_MESON_TAC[EVEN_ODD_POW];
  STRIP_TAC;
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  CASES_ON `pts1 = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;];
  COND_CASES_TAC;
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 5 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x > &0`;
  ASM_MESON_TAC[];
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 5 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x > &0`;
  ASM_MESON_TAC[];
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REPEAT STRIP_TAC;
  CLAIM `(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) = 
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))`;
  ASM_MESON_TAC[APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[partition_line];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  REWRITE_ALL[TL;];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  RESTRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x > &0`;
  ASM_MESON_TAC[];
  REPEAT_N 15 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  (* save *) 
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REWRITE_ALL[TL;ALL2;interpsign;interpsigns;APPEND];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 10 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x > &0`;
  ASM_MESON_TAC[];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 17 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`];
]);;  
(* }}} *)

let SPLIT_LIST_THM = prove_by_refinement(
  `!n (l:A list). n < LENGTH l ==> 
    ?l1 l2. (l = APPEND l1 l2) /\ (LENGTH l1 = n)`,
(* {{{ Proof *)
[
  INDUCT_TAC;
  REPEAT STRIP_TAC;
  EXISTS_TAC `[]:A list`;
  EXISTS_TAC `l`;
  REWRITE_TAC[APPEND;LENGTH];
  REPEAT STRIP_TAC;
  CLAIM `n < LENGTH l`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP y x)));
  STRIP_TAC;
  EXISTS_TAC `APPEND l1 [HD l2]`;
  EXISTS_TAC `TL (l2:A list)`;
  CLAIM `~((l2:A list) = [])`;
  REWRITE_TAC[GSYM LENGTH_0];
  STRIP_TAC;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC;
  POP_ASSUM (MP_TAC o AP_TERM `LENGTH:A list -> num`);
  REWRITE_TAC[LENGTH_APPEND];
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL;];
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  ASM_REWRITE_TAC[TL;HD;LENGTH_APPEND;LENGTH;];
  STRIP_TAC;
  REWRITE_TAC[APPEND_APPEND;APPEND;];
  ARITH_TAC;
]);;
(* }}} *)

let rec EXISTS_TACL = 
  (fun l -> 
     match l with
       [] -> ALL_TAC 
     | h::t -> TYPE_TAC EXISTS_TAC h THEN EXISTS_TACL t);;


let DIV_EVEN = prove_by_refinement(
 `!x. EVEN x ==> (2 * x DIV 2 = x)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  TYPE_TACL (fun l -> MP_TAC (ISPECL l DIVISION)) [`x`;`2`];
  ARITH_SIMP_TAC[];
  REWRITE_ASSUMS[EVEN_MOD];
  ASM_REWRITE_TAC[];
  ARITH_SIMP_TAC[];
  STRIP_TAC;
  REWRITE_ASSUMS[ARITH_RULE `x + 0 = x`];
  ONCE_REWRITE_ASSUMS[ARITH_RULE `x * y = y * x:num`];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let PRE_LEM = prove_by_refinement(
  `!n. (ODD n ==> EVEN (PRE n)) /\ 
       (~(n = 0) ==> (EVEN n ==> ODD (PRE n)))`,
(* {{{ Proof *)
[
  INDUCT_TAC;
  ARITH_TAC;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  REPEAT STRIP_TAC;
  REWRITE_TAC[PRE];
  ASM_MESON_TAC[ODD;NOT_ODD];
  ASM_MESON_TAC[ODD;PRE;NOT_ODD];
]);;
(* }}} *)

let EVEN_PRE = GEN_ALL (CONJUNCT1 (SPEC_ALL PRE_LEM));;
let ODD_PRE = GEN_ALL (CONJUNCT2 (SPEC_ALL PRE_LEM));;

let INFERPSIGN_POS_EVEN = prove_by_refinement(
  `!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a <> &0) ==> 
  EVEN n ==> 
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Pos s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest))`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND sgns (CONS 
    (APPEND (CONS Unknown s1) 
      (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) = 
        LENGTH (partition_line pts)`;
  REWRITE_ALL[interpmat];
  ASM_MESON_TAC[ALL2_LENGTH];
  REWRITE_TAC[LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;];
  STRIP_TAC;
  TYPE_TACL (fun l -> MP_TAC (ISPECL l SPLIT_LIST_THM)) [`(LENGTH sgns - 1) DIV 2`;`pts`];  
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  ARITH_TAC;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(l2 = [])`;
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  REWRITE_ALL[APPEND_NIL];
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] INFERPSIGN_POS_EVEN_LEM);
  ASM_REWRITE_TAC[];
  EXISTS_TACL [`a`;`n`;`s`];
  (* save *) 
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_MESON_TAC[];
  LABEL_ALL_TAC;
  CLAIM `EVEN (LENGTH sgns - 1)`;
  ASM_MESON_TAC[EVEN_PRE;ARITH_RULE `x - 1 = PRE x`];
  STRIP_TAC;
  ASM_SIMP_TAC[DIV_EVEN];
  USE_THEN "Z-5" MP_TAC THEN ARITH_TAC;
]);;  

(* }}} *)

let INFERPSIGN_NEG_EVEN_LEM = prove_by_refinement(
  `!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a <> &0) ==> 
  EVEN n ==> 
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Neg s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `a pow n > &0`;
  ASM_MESON_TAC[EVEN_ODD_POW];
  STRIP_TAC;
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  CASES_ON `pts1 = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;];
  COND_CASES_TAC;
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 5 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x < &0`;
  ASM_MESON_TAC[];
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 5 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x < &0`;
  ASM_MESON_TAC[];
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REPEAT STRIP_TAC;
  CLAIM `(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) = 
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))`;
  ASM_MESON_TAC[APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[partition_line];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  REWRITE_ALL[TL;];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  RESTRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x < &0`;
  ASM_MESON_TAC[];
  REPEAT_N 15 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  (* save *) 
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REWRITE_ALL[TL;ALL2;interpsign;interpsigns;APPEND];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 10 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x < &0`;
  ASM_MESON_TAC[];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 17 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT];
]);;  
(* }}} *)


let INFERPSIGN_NEG_EVEN = prove_by_refinement(
  `!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a <> &0) ==> 
  EVEN n ==> 
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Neg s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest))`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND sgns (CONS 
    (APPEND (CONS Unknown s1) 
      (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) = 
        LENGTH (partition_line pts)`;
  REWRITE_ALL[interpmat];
  ASM_MESON_TAC[ALL2_LENGTH];
  REWRITE_TAC[LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;];
  STRIP_TAC;
  TYPE_TACL (fun l -> MP_TAC (ISPECL l SPLIT_LIST_THM)) [`(LENGTH sgns - 1) DIV 2`;`pts`];  
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  ARITH_TAC;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(l2 = [])`;
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  REWRITE_ALL[APPEND_NIL];
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] INFERPSIGN_NEG_EVEN_LEM);
  ASM_REWRITE_TAC[];
  EXISTS_TACL [`a`;`n`;`s`];
  (* save *) 
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_MESON_TAC[];
  LABEL_ALL_TAC;
  CLAIM `EVEN (LENGTH sgns - 1)`;
  ASM_MESON_TAC[EVEN_PRE;ARITH_RULE `x - 1 = PRE x`];
  STRIP_TAC;
  ASM_SIMP_TAC[DIV_EVEN];
  USE_THEN "Z-5" MP_TAC THEN ARITH_TAC;
]);;  

(* }}} *)

let INFERPSIGN_ZERO_EVEN_LEM = prove_by_refinement(
  `!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a <> &0) ==> 
  EVEN n ==> 
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Zero s1) 
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `a pow n > &0`;
  ASM_MESON_TAC[EVEN_ODD_POW];
  STRIP_TAC;
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  CASES_ON `pts1 = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;];
  COND_CASES_TAC;
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 5 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x = &0`;
  ASM_MESON_TAC[];
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 5 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x = &0`;
  ASM_MESON_TAC[];
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REPEAT STRIP_TAC;
  CLAIM `(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) = 
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))`;
  ASM_MESON_TAC[APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[partition_line];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  REWRITE_ALL[TL;];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  RESTRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x = &0`;
  ASM_MESON_TAC[];
  REPEAT_N 15 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  (* save *) 
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REWRITE_ALL[TL;ALL2;interpsign;interpsigns;APPEND];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 10 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x = &0`;
  ASM_MESON_TAC[];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 17 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
]);;  
(* }}} *)

let INFERPSIGN_ZERO_EVEN = prove_by_refinement(
  `!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a <> &0) ==> 
  EVEN n ==> 
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Zero s1) 
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest))`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND sgns (CONS 
    (APPEND (CONS Unknown s1) 
      (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) = 
        LENGTH (partition_line pts)`;
  REWRITE_ALL[interpmat];
  ASM_MESON_TAC[ALL2_LENGTH];
  REWRITE_TAC[LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;];
  STRIP_TAC;
  TYPE_TACL (fun l -> MP_TAC (ISPECL l SPLIT_LIST_THM)) [`(LENGTH sgns - 1) DIV 2`;`pts`];  
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  ARITH_TAC;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(l2 = [])`;
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  REWRITE_ALL[APPEND_NIL];
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] INFERPSIGN_ZERO_EVEN_LEM);
  ASM_REWRITE_TAC[];
  EXISTS_TACL [`a`;`n`;`s`];
  (* save *) 
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_MESON_TAC[];
  LABEL_ALL_TAC;
  CLAIM `EVEN (LENGTH sgns - 1)`;
  ASM_MESON_TAC[EVEN_PRE;ARITH_RULE `x - 1 = PRE x`];
  STRIP_TAC;
  ASM_SIMP_TAC[DIV_EVEN];
  USE_THEN "Z-5" MP_TAC THEN ARITH_TAC;
]);;  

(* }}} *)


let INFERPSIGN_POS_ODD_POS_LEM = prove_by_refinement(
  `!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a > &0) ==> 
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Pos s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `a pow n > &0`;
  ASM_MESON_TAC[REAL_POW_LT;real_gt;];
  STRIP_TAC;
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  CASES_ON `pts1 = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;];
  COND_CASES_TAC;
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 4 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x > &0`;
  ASM_MESON_TAC[];
  REPEAT_N 5 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 4 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x > &0`;
  ASM_MESON_TAC[];
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REPEAT STRIP_TAC;
  CLAIM `(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) = 
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))`;
  ASM_MESON_TAC[APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[partition_line];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  REWRITE_ALL[TL;];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  RESTRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x > &0`;
  ASM_MESON_TAC[];
  REPEAT_N 14 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`;REAL_MUL_GT];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  (* save *) 
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REWRITE_ALL[TL;ALL2;interpsign;interpsigns;APPEND];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x > &0`;
  ASM_MESON_TAC[];
  REPEAT_N 15 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
]);;  

(* }}} *)

let INFERPSIGN_POS_ODD_POS = prove_by_refinement(
  `!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a > &0) ==> 
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Pos s1) 
        (APPEND (CONS Zero s2) (CONS Pos s3))) rest))`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND sgns (CONS 
    (APPEND (CONS Unknown s1) 
      (APPEND (CONS Zero s2) (CONS Pos s3))) rest)) = 
        LENGTH (partition_line pts)`;
  REWRITE_ALL[interpmat];
  ASM_MESON_TAC[ALL2_LENGTH];
  REWRITE_TAC[LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;];
  STRIP_TAC;
  TYPE_TACL (fun l -> MP_TAC (ISPECL l SPLIT_LIST_THM)) [`(LENGTH sgns - 1) DIV 2`;`pts`];  
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  ARITH_TAC;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(l2 = [])`;
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  REWRITE_ALL[APPEND_NIL];
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] INFERPSIGN_POS_ODD_POS_LEM);
  ASM_REWRITE_TAC[];
  EXISTS_TACL [`a`;`n`;`s`];
  (* save *) 
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_MESON_TAC[];
  LABEL_ALL_TAC;
  CLAIM `EVEN (LENGTH sgns - 1)`;
  ASM_MESON_TAC[EVEN_PRE;ARITH_RULE `x - 1 = PRE x`];
  STRIP_TAC;
  ASM_SIMP_TAC[DIV_EVEN];
  USE_THEN "Z-4" MP_TAC THEN ARITH_TAC;
]);;  

(* }}} *)

let INFERPSIGN_NEG_ODD_POS_LEM = prove_by_refinement(
  `!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a > &0) ==> 
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Neg s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `a pow n > &0`;
  ASM_MESON_TAC[REAL_POW_LT;real_gt;];
  STRIP_TAC;
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  CASES_ON `pts1 = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;];
  COND_CASES_TAC;
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 4 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x < &0`;
  ASM_MESON_TAC[real_gt];
  REPEAT_N 5 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 4 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x < &0`;
  ASM_MESON_TAC[];
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REPEAT STRIP_TAC;
  CLAIM `(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) = 
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))`;
  ASM_MESON_TAC[APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[partition_line];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  REWRITE_ALL[TL;];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  RESTRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x < &0`;
  ASM_MESON_TAC[];
  REPEAT_N 14 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`;REAL_MUL_GT];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  (* save *) 
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REWRITE_ALL[TL;ALL2;interpsign;interpsigns;APPEND];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x < &0`;
  ASM_MESON_TAC[];
  REPEAT_N 15 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
]);;  

(* }}} *)

let INFERPSIGN_NEG_ODD_POS = prove_by_refinement(
  `!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a > &0) ==> 
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Neg s1) 
        (APPEND (CONS Zero s2) (CONS Neg s3))) rest))`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND sgns (CONS 
    (APPEND (CONS Unknown s1) 
      (APPEND (CONS Zero s2) (CONS Neg s3))) rest)) = 
        LENGTH (partition_line pts)`;
  REWRITE_ALL[interpmat];
  ASM_MESON_TAC[ALL2_LENGTH];
  REWRITE_TAC[LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;];
  STRIP_TAC;
  TYPE_TACL (fun l -> MP_TAC (ISPECL l SPLIT_LIST_THM)) [`(LENGTH sgns - 1) DIV 2`;`pts`];  
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  ARITH_TAC;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(l2 = [])`;
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  REWRITE_ALL[APPEND_NIL];
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] INFERPSIGN_NEG_ODD_POS_LEM);
  ASM_REWRITE_TAC[];
  EXISTS_TACL [`a`;`n`;`s`];
  (* save *) 
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_MESON_TAC[];
  LABEL_ALL_TAC;
  CLAIM `EVEN (LENGTH sgns - 1)`;
  ASM_MESON_TAC[EVEN_PRE;ARITH_RULE `x - 1 = PRE x`];
  STRIP_TAC;
  ASM_SIMP_TAC[DIV_EVEN];
  USE_THEN "Z-4" MP_TAC THEN ARITH_TAC;
]);;  

(* }}} *)

let INFERPSIGN_ZERO_ODD_POS_LEM = prove_by_refinement(
  `!a n p ps q qs r rs s x pts1 pts2  s1 s2 s3 rest sgns.
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (LENGTH sgns = 2 * LENGTH pts1 + 1) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a > &0) ==> 
  interpmat (APPEND pts1 (CONS x pts2)) 
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Zero s1) 
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `a pow n > &0`;
  ASM_MESON_TAC[REAL_POW_LT;real_gt;];
  STRIP_TAC;
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_TAC[interpmat];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  CASES_ON `pts1 = []`;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;];
  COND_CASES_TAC;
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 4 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x = &0`;
  ASM_MESON_TAC[real_gt];
  REPEAT_N 5 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 6 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  CLAIM `?k. sgns = [k]`;
  MATCH_EQ_MP_TAC (GSYM LENGTH_1);
  REWRITE_ALL[LENGTH];
  REPEAT_N 4 (POP_ASSUM (fun x -> ALL_TAC));
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[APPEND;partition_line;ALL2;];
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_ALL[interpsigns;interpsign;ALL2;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x = &0`;
  ASM_MESON_TAC[];
  REPEAT_N 7 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`];
  ASM_REWRITE_TAC[];
  (* save *) 
  POP_ASSUM (fun x -> REPEAT (POP_ASSUM MP_TAC) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[PARTITION_LINE_APPEND];
  REPEAT STRIP_TAC;
  CLAIM `(APPEND (BUTLAST (partition_line pts1))
     (CONS (\x'. LAST pts1 < x' /\ x' < x)
     (TL (partition_line (CONS x pts2))))) = 
     (APPEND
      (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x])
     (TL (partition_line (CONS x pts2))))`;
  ASM_MESON_TAC[APPEND_CONS];
  DISCH_THEN (REWRITE_ALL o list);
  REPEAT (POP_ASSUM MP_TAC);
  REWRITE_ALL[partition_line];
  COND_CASES_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REPEAT STRIP_TAC;
  REWRITE_ALL[TL;];
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REPEAT_N 8 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  RESTRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x = &0`;
  ASM_MESON_TAC[];
  REPEAT_N 14 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`;REAL_MUL_GT;REAL_LT_IMP_NZ];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  (* save *) 
  CLAIM `LENGTH (APPEND (BUTLAST (partition_line pts1))
      [\x'. LAST pts1 < x' /\ x' < x]) = LENGTH sgns`;
  FIRST_ASSUM (MP_TAC o MATCH_MP  ALL2_LENGTH);
  ASM_SIMP_TAC[LENGTH_APPEND;PARTITION_LINE_NOT_NIL;BUTLAST_LENGTH;PARTITION_LINE_LENGTH;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));
  REPEAT STRIP_TAC;
  MATCH_MP_TAC ALL2_APPEND;
  ASM_REWRITE_TAC[];
  (* save *)
  REWRITE_ALL[TL;ALL2;interpsign;interpsigns;APPEND];
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  REPEAT_N 9 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> REPEAT STRIP_TAC THEN ASSUME_TAC x THEN ASSUME_TAC y));
  REWRITE_ALL[ALL2;interpsigns;APPEND;interpsign;];
  ASM_REWRITE_TAC[];
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  REPEAT_N 4 (POP_ASSUM MP_TAC);
  POP_ASSUM (fun x -> REPEAT STRIP_TAC THEN ASSUME_TAC x);
  FIRST_ASSUM (MP_TAC o MATCH_MP ALL2_APPEND_LENGTH);
  FIRST_ASSUM (fun x -> DISCH_THEN (fun y -> MP_TAC (MATCH_MP y x)));  
  REWRITE_TAC[ALL2;interpsign;];
  REPEAT STRIP_TAC;
  REWRITE_ALL[interpsigns;ALL2;interpsign;];
  ASM_REWRITE_TAC[];
  CLAIM `q x = &0`;
  ASM_MESON_TAC[];
  CLAIM `r x = &0`;
  ASM_MESON_TAC[];
  REPEAT_N 15 (POP_ASSUM MP_TAC);
  POP_ASSUM (MP_TAC o ISPEC `x:real`);
  REPEAT STRIP_TAC;
  POP_ASSUM (REWRITE_ALL o list);
  REWRITE_ALL[REAL_MUL_RZERO;REAL_ADD_LID;];
  REPEAT_N 16 (POP_ASSUM MP_TAC);
  POP_ASSUM (REWRITE_ALL o list o GSYM);
  REWRITE_TAC[real_gt;REAL_MUL_GT];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ARITH `~(x < y /\ y < x)`;REAL_MUL_LT;REAL_ENTIRE;ARITH_RULE `x < y ==> ~(x = y)`;REAL_MUL_GT;REAL_LT_IMP_NZ];
]);;  

(* }}} *)

let INFERPSIGN_ZERO_ODD_POS = prove_by_refinement(
  `!a n p ps q qs pts r rs s s1 s2 s3 rest sgns.
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Unknown s1) 
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) ==> 
  (LENGTH ps = LENGTH s1) ==> 
  (LENGTH qs = LENGTH s2) ==> 
  ODD (LENGTH sgns) ==> 
  (!x. a pow n * p x = s x * q x + r x) ==> 
  (a > &0) ==> 
  interpmat pts
    (APPEND (CONS p ps) (APPEND (CONS q qs) (CONS r rs)))
    (APPEND sgns 
      (CONS (APPEND (CONS Zero s1) 
        (APPEND (CONS Zero s2) (CONS Zero s3))) rest))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `LENGTH (APPEND sgns (CONS 
    (APPEND (CONS Unknown s1) 
      (APPEND (CONS Zero s2) (CONS Zero s3))) rest)) = 
        LENGTH (partition_line pts)`;
  REWRITE_ALL[interpmat];
  ASM_MESON_TAC[ALL2_LENGTH];
  REWRITE_TAC[LENGTH_APPEND;PARTITION_LINE_LENGTH;LENGTH;];
  STRIP_TAC;
  TYPE_TACL (fun l -> MP_TAC (ISPECL l SPLIT_LIST_THM)) [`(LENGTH sgns - 1) DIV 2`;`pts`];  
  STRIP_TAC;
  LABEL_ALL_TAC;
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  ARITH_TAC;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `~(l2 = [])`;
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  REWRITE_ALL[APPEND_NIL];
  POP_ASSUM (REWRITE_ALL o list);
  POP_ASSUM (fun x -> ALL_TAC);
  DISCH_THEN (REWRITE_ALL o list);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC THEN POP_ASSUM (REWRITE_ALL o list);
  MATCH_MP_TAC (REWRITE_RULE[IMP_AND_THM] INFERPSIGN_ZERO_ODD_POS_LEM);
  ASM_REWRITE_TAC[];
  EXISTS_TACL [`a`;`n`;`s`];
  (* save *) 
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_MESON_TAC[];
  LABEL_ALL_TAC;
  CLAIM `EVEN (LENGTH sgns - 1)`;
  ASM_MESON_TAC[EVEN_PRE;ARITH_RULE `x - 1 = PRE x`];
  STRIP_TAC;
  ASM_SIMP_TAC[DIV_EVEN];
  USE_THEN "Z-4" MP_TAC THEN ARITH_TAC;
]);;  

(* }}} *)
