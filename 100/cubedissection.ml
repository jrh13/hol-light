(* ========================================================================= *)
(* Impossibility of cube dissection into finitely many smaller cubes of      *)
(* pairwise distinct sizes ("cubing the cube"), originally proved by         *)
(* R. L. Brooks, C. A. B. Smith, A. H. Stone and W. T. Tutte,                *)
(* "The Dissection of Rectangles into Squares",                              *)
(* Duke Mathematical Journal, vol. 7 (1940), pp. 312-340.                    *)
(*                                                                           *)
(* The proof follows the elegant argument presented in J. E. Littlewood,     *)
(* "A Mathematician's Miscellany" (CUP, 1953), revised edition               *)
(* "Littlewood's Miscellany" (ed. B. Bollobas, CUP, 1986), pp. 28-29.        *)
(*                                                                           *)
(* Formalized in HOL Light by Claude Code (Opus 4.6), February 2026.         *)
(* ========================================================================= *)

needs "Multivariate/integration.ml";;

(* ------------------------------------------------------------------------- *)
(* Cube-shaped boxes in R^N (we only really use it for R^3 here)             *)
(* ------------------------------------------------------------------------- *)

let cube = new_definition
 `cube k <=>
     ?a:real^N d. &0 < d /\ k = interval[a,a + d % vec 1]`;;

let CUBE_IMP_NONEMPTY_INTERIOR = prove
 (`!k:real^N->bool. cube k ==> ~(interior k = {})`,
  SIMP_TAC[cube; LEFT_IMP_EXISTS_THM; INTERIOR_INTERVAL] THEN
  SIMP_TAC[INTERVAL_NE_EMPTY; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC);;

let CUBE_IMP_NONEMPTY = prove
 (`!k:real^N->bool. cube k ==> ~(k = {})`,
  MESON_TAC[CUBE_IMP_NONEMPTY_INTERIOR; INTERIOR_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* The length of an interval (first component; we only use it for cubes).    *)
(* ------------------------------------------------------------------------- *)

let interval_length = new_definition
 `interval_length (s:real^N->bool) =
        if s = {} then &0
        else interval_upperbound s$1 - interval_lowerbound s$1`;;

let INTERVAL_LENGTH_CUBE = prove
 (`!(a:real^N) d. interval_length(interval[a,a + d % vec 1]) = max d (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[interval_length] THEN
  SIMP_TAC[INTERVAL_UPPERBOUND_NONEMPTY; INTERVAL_LOWERBOUND_NONEMPTY] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
              INTERVAL_EQ_EMPTY; REAL_ADD_SUB; REAL_MUL_RID;
              REAL_ARITH `max d (&0) = if d < &0 then &0 else d`] THEN
  ASM_CASES_TAC `d:real < &0` THEN
  ASM_REWRITE_TAC[REAL_ARITH `a + d < a <=> d < &0`] THEN
  ASM_MESON_TAC[LE_REFL; DIMINDEX_GE_1]);;

let INTERVAL_LENGTH_CUBE_COMPONENT = prove
 (`!(k:real^N->bool) i.
        cube k
        ==> interval_upperbound k$i - interval_lowerbound k$i =
            interval_length k`,
  REWRITE_TAC[cube] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[interval_length] THEN ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN
  ASM_SIMP_TAC[INTERVAL_NE_EMPTY; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               VEC_COMPONENT; REAL_MUL_RID; REAL_LE_ADDR; REAL_LT_IMP_LE;
               INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN REAL_ARITH_TAC);;

let INTERVAL_LENGTH_CUBE_POS = prove
 (`!(a:real^N) d. &0 < d ==> interval_length(interval[a, a + d % vec 1]) = d`,
  REWRITE_TAC[INTERVAL_LENGTH_CUBE] THEN REAL_ARITH_TAC);;

let VECTOR2_CUBE = prove
 (`!c:real^3 s. vector[c$2 + s; c$3 + s]:real^2 =
                vector[c$2; c$3] + s % vec 1`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; VEC_COMPONENT; VECTOR_2; REAL_MUL_RID]);;

let CUBE_BOUNDS_TAC =
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND;
    VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
    REAL_MUL_RID; REAL_LE_ADDR; REAL_LT_IMP_LE];;

let MESON_ASSUME_TAC lemmas tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL [ASM_MESON_TAC lemmas; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Dissection of a set into pairwise differently-sized nonempty cubes.       *)
(* ------------------------------------------------------------------------- *)

let cube_dissection = new_definition
 `cube_dissection (d:(real^N->bool)->bool) <=>
        d division_of UNIONS d /\
        (!k. k IN d ==> cube k) /\
        pairwise (\k k'. ~(interval_length k = interval_length k')) d`;;

(* ------------------------------------------------------------------------- *)
(* A point on the boundary of a division element must belong to another.     *)
(* ------------------------------------------------------------------------- *)

let POINT_IN_MULTIPLE_DIVISION_OF_GEN = prove
 (`!D a b u v (x:real^N) i.
        D division_of UNIONS D /\
        interval[u,v] IN D /\ x IN interval[u,v] /\
        interval[a,b] SUBSET UNIONS D /\
        interval[u,v] SUBSET interval[a,b] /\
        1 <= i /\ i <= dimindex(:N) /\
        a$i < x$i /\ x$i < b$i /\ (x$i = u$i \/ x$i = v$i)
        ==> ?j'. j' IN D /\ ~(j' = interval[u,v]) /\ x IN j'`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS(D DELETE interval[u,v])` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC(MESON[CLOSURE_CLOSED]
   `closed (s:real^N->bool) /\ (x:real^N) IN closure s ==> x IN s`) THEN
  CONJ_TAC THENL [MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_MESON_TAC[FINITE_DELETE; IN_DELETE; division_of; CLOSED_INTERVAL];
    ALL_TAC] THEN MATCH_MP_TAC(MESON[SUBSET_CLOSURE; SUBSET]
   `UNIONS (D:(real^N->bool)->bool) DIFF s SUBSET UNIONS(D DELETE s) /\
    (x:real^N) IN closure(UNIONS D DIFF s)
    ==> x IN closure(UNIONS(D DELETE s))`) THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interval[a:real^N,b] DIFF interval[u,v] SUBSET
     UNIONS D DIFF interval[u:real^N,v]` MP_TAC THENL
   [UNDISCH_TAC `interval[a:real^N,b] SUBSET UNIONS D` THEN SET_TAC[];
    ALL_TAC] THEN DISCH_THEN(MP_TAC o MATCH_MP SUBSET_CLOSURE) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `interval[u:real^N,v] SUBSET interval[a:real^N,b]` THEN
  UNDISCH_TAC `(x:real^N) IN interval[u:real^N,v]` THEN
  REWRITE_TAC[SUBSET_INTERVAL; IN_INTERVAL] THEN DISCH_TAC THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; DISCH_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN REWRITE_TAC[IN_DIFF; IN_INTERVAL] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL [EXISTS_TAC
     `(lambda j. if j = i then max ((a:real^N)$i) ((u:real^N)$i - e / &2)
                 else (x:real^N)$j):real^N`;
    EXISTS_TAC
     `(lambda j. if j = i then min ((b:real^N)$i) ((v:real^N)$i + e / &2)
                 else (x:real^N)$j):real^N`] THEN SIMP_TAC[LAMBDA_BETA] THEN
  (CONJ_TAC THENL [CONJ_TAC THENL
      [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
       REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `j:num`)) THEN ASM_REWRITE_TAC[] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
       DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
       ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
     ASM_REWRITE_TAC[dist; NORM_LT_SQUARE; dot; GSYM REAL_POW_2] THEN
     SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT; IN_NUMSEG] THEN
     REWRITE_TAC[COND_RAND; COND_RATOR; REAL_SUB_REFL] THEN
     CONV_TAC REAL_RAT_REDUCE_CONV THEN
     ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; GSYM REAL_LT_SQUARE_ABS] THEN
     ASM_REAL_ARITH_TAC]));;

(* Specialized version when D division_of interval[a,b] *)
let POINT_IN_MULTIPLE_DIVISION_OF = prove
 (`!D a b u v (x:real^N) i.
        D division_of interval[a,b] /\
        interval[u,v] IN D /\ x IN interval[u,v] /\
        1 <= i /\ i <= dimindex(:N) /\
        a$i < x$i /\ x$i < b$i /\ (x$i = u$i \/ x$i = v$i)
        ==> ?j'. j' IN D /\ ~(j' = interval[u,v]) /\ x IN j'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC POINT_IN_MULTIPLE_DIVISION_OF_GEN THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `i:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[division_of; SUBSET_REFL]);;

let CUBE_EXISTS_FORM = prove
 (`!D:(real^N->bool)->bool.
        cube_dissection D /\
        (!(x:real^N) e. interval[x,x + e % vec 1] IN D /\
               P(interval[x,x + e % vec 1])
               ==> R x e)
        ==> (?j. j IN D /\ P j) ==> (?(x:real^N) e. R x e)`,
  GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cube(j:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[cube_dissection]; REWRITE_TAC[cube; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`xx:real^N`; `ee:real`] THEN STRIP_TAC THEN
  EXISTS_TAC `xx:real^N` THEN EXISTS_TAC `ee:real` THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let SQUARE_DISSECTION_NONEDGE = prove
 (`!D a b j:real^2->bool.
        cube_dissection D /\ UNIONS D = interval[a,b] /\ j IN D /\
        (!j'. j' IN D /\ ~(j' = j)
             ==> interval_length(j) < interval_length j')
        ==> j = interval[a,b] \/ j SUBSET interval(a,b)`,
  let iterm n = match n with
     1 -> `interval[x1:real^2,x1 + e1 % vec 1]`
   | 2 -> `interval[x2:real^2,x2 + e2 % vec 1]`
   | 3 -> `interval[x3:real^2,x3 + e3 % vec 1]`
   | 4 -> `interval[x4:real^2,x4 + e4 % vec 1]` in
  let itspec [m;n] = SPECL[iterm m; iterm n] in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cube(j:real^2->bool)` MP_TAC THENL
   [ASM_MESON_TAC[cube_dissection]; REWRITE_TAC[cube; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `d:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check(is_forall o concl)) THEN
  ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE; REAL_ARITH
    `&0 < d ==> max d (&0) = d`] THEN DISCH_TAC THEN SUBGOAL_THEN
   `~(interval[u:real^2,u + d % vec 1] = {}) /\ ~(interval[a:real^2,b] = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cube_dissection; division_of; SUBSET_EMPTY];
    ASM_REWRITE_TAC[EQ_INTERVAL; SUBSET_INTERVAL; CART_EQ;
                    DIMINDEX_2; FORALL_2]] THEN
  SUBGOAL_THEN `interval[u:real^2,u + d % vec 1] SUBSET interval[a,b]`
  MP_TAC THENL [ASM_MESON_TAC[cube_dissection; division_of]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL; DIMINDEX_2; FORALL_2] THEN
  UNDISCH_TAC `~(interval[u:real^2,u + d % vec 1] = {})` THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
    VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINOP_CONV o LAND_CONV o RAND_CONV)
    [EQ_SYM_EQ] THEN MP_TAC(ISPECL
   [`D:(real^2->bool)->bool`; `a:real^2`; `b:real^2`;
    `u:real^2`; `u + d % vec 1:real^2`]
        POINT_IN_MULTIPLE_DIVISION_OF) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; DIMINDEX_2] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cube_dissection]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  STRIP_TAC THEN SUBGOAL_THEN `(~((u:real^2)$1 = (a:real^2)$1)
     ==> ?x1 e1. d < e1 /\ &0 < e1 /\
                 interval[x1:real^2,x1 + e1 % vec 1] IN D /\
                 a$1 <= x1$1 /\ x1$1 + e1 = u$1 /\
                 a$2 <= x1$2 /\ x1$2 + e1 <= (b:real^2)$2 /\
                 vector[u$1; u$2 + d / &2] IN
                 interval[x1:real^2,x1 + e1 % vec 1]) /\
    (~((u:real^2)$2 = (a:real^2)$2)
     ==> ?x2 e2. d < e2 /\ &0 < e2 /\
                 interval[x2:real^2,x2 + e2 % vec 1] IN D /\
                 a$1 <= x2$1 /\ x2$1 + e2 <= (b:real^2)$1 /\
                 a$2 <= x2$2 /\ x2$2 + e2 = u$2 /\
                 vector[u$1 + d / &2; u$2] IN
                 interval[x2:real^2,x2 + e2 % vec 1]) /\
    (~((u + d % vec 1:real^2)$1 = (b:real^2)$1)
     ==> ?x3 e3. d < e3 /\ &0 < e3 /\
                 interval[x3:real^2,x3 + e3 % vec 1] IN D /\
                 x3$1 = (u + d % vec 1)$1 /\ x3$1 + e3 <= b$1 /\
                 (a:real^2)$2 <= x3$2 /\ x3$2 + e3 <= b$2 /\
                 vector[u$1 + d; u$2 + d / &2] IN
                 interval[x3:real^2,x3 + e3 % vec 1]) /\
    (~((u + d % vec 1:real^2)$2 = (b:real^2)$2)
     ==> ?x4 e4. d < e4 /\ &0 < e4 /\
                 interval[x4:real^2,x4 + e4 % vec 1] IN D /\
                 (a:real^2)$1 <= x4$1 /\ x4$1 + e4 <= b$1 /\
                 x4$2 = (u + d % vec 1)$2 /\ x4$2 + e4 <= b$2 /\
                 vector[u$1 + d / &2; u$2 + d] IN
                 interval[x4:real^2,x4 + e4 % vec 1])`
  MP_TAC THENL [ASM_SIMP_TAC[CONJ_ASSOC; REAL_ARITH
     `&0 < d ==> (d < e /\ &0 < e <=> d < e)`] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                GSYM CONJ_ASSOC; VEC_COMPONENT; REAL_MUL_RID] THEN
    REPEAT CONJ_TAC THEN DISCH_TAC THENL [FIRST_X_ASSUM(MP_TAC o SPECL
       [`vector[(u:real^2)$1; u$2 + d / &2]:real^2`; `1`]);
      FIRST_X_ASSUM(MP_TAC o SPECL
        [`vector[(u:real^2)$1 + d / &2; u$2]:real^2`; `2`]);
      FIRST_X_ASSUM(MP_TAC o SPECL
        [`vector[(u:real^2)$1 + d; u$2 + d / &2]:real^2`; `1`]);
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`vector[(u:real^2)$1 + d / &2; u$2 + d]:real^2`; `2`])] THEN
    (ANTS_TAC THENL [REWRITE_TAC[IN_INTERVAL; VECTOR_2; DIMINDEX_2; FORALL_2;
        VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(ISPEC `D:(real^2->bool)->bool` CUBE_EXISTS_FORM) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `e:real`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `interval[x:real^2,x + e % vec 1]`) THEN
      ASM_REWRITE_TAC[INTERVAL_LENGTH_CUBE] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[cube_dissection]) THEN
      ASM_REWRITE_TAC[division_of; AND_FORALL_THM] THEN DISCH_THEN(MP_TAC o
        SPEC `interval[x:real^2,x + e % vec 1]` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT1)
       (MP_TAC o SPEC `interval[u:real^2,u + d % vec 1]`)) THEN
      ASM_REWRITE_TAC[INTERIOR_INTERVAL; SUBSET_INTERVAL] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
      REWRITE_TAC[DISJOINT_INTERVAL; DIMINDEX_2; FORALL_2; IN_INTERVAL; MESON[]
       `(?(i:num). 1 <= i /\ i <= 2 /\ (P:num->bool) i) <=>
        ~(!i. 1 <= i /\ i <= 2 ==> ~P i)`;
        VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2;
                  VEC_COMPONENT; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC]); ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; IN_INTERVAL;
    VECTOR_2; DIMINDEX_2; FORALL_2; VEC_COMPONENT; REAL_MUL_RID] THEN
  MAP_EVERY ASM_CASES_TAC
   [`(u:real^2)$1 = (a:real^2)$1`;
    `(u:real^2)$1 + d = (b:real^2)$1`;
    `(u:real^2)$2 = (a:real^2)$2`;
    `(u:real^2)$2 + d = (b:real^2)$2`] THEN
  ASM_REWRITE_TAC[] THEN TRY ASM_REAL_ARITH_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cube_dissection]) THEN
  REWRITE_TAC[division_of; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THENL
   [DISCH_THEN(MP_TAC o itspec [3;4]);
    DISCH_THEN(MP_TAC o itspec [2;3]);
    DISCH_THEN(fun t -> MAP_EVERY (MP_TAC o C itspec t) [[2;3]; [2;4]; [3;4]]);
    DISCH_THEN(MP_TAC o itspec [1;4]);
    DISCH_THEN(MP_TAC o itspec [1;2]);
    DISCH_THEN(fun t -> MAP_EVERY (MP_TAC o C itspec t) [[1;2]; [1;4]; [2;4]]);
    DISCH_THEN(fun t -> MAP_EVERY (MP_TAC o C itspec t) [[1;3]; [1;4]; [3;4]]);
    DISCH_THEN(fun t -> MAP_EVERY (MP_TAC o C itspec t) [[1;2]; [1;3]; [2;3]])
   ] THEN ASM_REWRITE_TAC[EQ_INTERVAL; INTERIOR_INTERVAL; DISJOINT_INTERVAL;
    CART_EQ; DE_MORGAN_THM; DIMINDEX_2; FORALL_2; IN_INTERVAL;
    INTERVAL_NE_EMPTY; MESON[]
     `(?i. 1 <= i /\ i <= 2 /\ P i) <=>
      ~(!i. 1 <= i /\ i <= 2 ==> ~P i)`] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2;
                VEC_COMPONENT; REAL_MUL_RID; DE_MORGAN_THM;
                INTERVAL_NE_EMPTY] THEN
  ASM_REWRITE_TAC[REAL_ARITH `a + e:real <= a <=> ~(&0 < e)`] THEN
  REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
  ASM_REAL_ARITH_TAC);;

(* Minimum element of a finite set with pairwise distinct f-values *)
let FINITE_PAIRWISE_MINIMUM = prove
 (`!(f:A->real) s.
    FINITE s /\ ~(s = {}) /\ pairwise (\x y. ~(f x = f y)) s
    ==> ?x. x IN s /\ !y. y IN s /\ ~(y = x) ==> f x < f y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (f:A->real) s` INF_FINITE_LEMMA) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?x0:A. x0 IN s /\ (f:A->real) x0 = b` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_IMAGE]; ALL_TAC] THEN
  EXISTS_TAC `x0:A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y /\ ~(x = y) ==> x < y`) THEN
  CONJ_TAC THENL [SUBGOAL_THEN `b <= (f:A->real) y` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `pairwise (\x y:A. ~((f:A->real) x = f y)) s` THEN
    REWRITE_TAC[pairwise] THEN
    DISCH_THEN(MP_TAC o SPECL [`x0:A`; `y:A`]) THEN ASM_REWRITE_TAC[]]);;

(* =================================================================== *)
(* Valley-based proof of cube dissection impossibility                 *)
(* Following the infinite descent approach of Brooks/Smith/Stone/Tutte *)
(* =================================================================== *)

(* A valley for a dissection D is a cube v whose "top face" is        *)
(* properly covered by cubes from D. The cubes sitting on v have      *)
(* their footprint within v's and are strictly smaller than v.        *)

let valley = new_definition
 `valley (D:(real^3->bool)->bool) (v:real^3->bool) <=>
    cube v /\
    (!z:real^3. z$1 = interval_upperbound (v:real^3->bool) $ 1 /\
                interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
                z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
                interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
                z$3 < interval_upperbound (v:real^3->bool) $ 3
                ==> ?k. k IN D /\ z IN k /\
                        interval_lowerbound k $ 1 =
                        interval_upperbound (v:real^3->bool) $ 1) /\
    (!k. k IN D /\
         interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
         (?z:real^3. z IN k /\
              interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
              z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
              interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
              z$3 < interval_upperbound (v:real^3->bool) $ 3)
         ==> interval_lowerbound (v:real^3->bool) $ 2 <= interval_lowerbound k $ 2 /\
             interval_upperbound k $ 2 <= interval_upperbound (v:real^3->bool) $ 2 /\
             interval_lowerbound (v:real^3->bool) $ 3 <= interval_lowerbound k $ 3 /\
             interval_upperbound k $ 3 <= interval_upperbound (v:real^3->bool) $ 3) /\
    (!k. k IN D /\
         interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
         (?z:real^3. z IN k /\
              interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
              z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
              interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
              z$3 < interval_upperbound (v:real^3->bool) $ 3)
         ==> interval_length k < interval_length v)`;;

(* The initial valley: the bottom face of [a,b] is a valley.         *)
(* More precisely, the cube shifted down below [a,b] is a valley.    *)

let DIVISION_WHOLE_IS_SINGLETON = prove
 (`!D (a:real^3) b.
    D division_of interval[a,b] /\
    (!k:real^3->bool. k IN D ==> cube k) /\
    interval[a,b] IN D
    ==> D = {interval[a,b]}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING] THEN
  X_GEN_TAC `j:real^3->bool` THEN EQ_TAC THENL [DISCH_TAC THEN
    ASM_CASES_TAC `j = interval[a:real^3,b]` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `interior(j:real^3->bool) = {}` MP_TAC THENL [SUBGOAL_THEN
       `interior(j:real^3->bool) SUBSET interior(interval[a:real^3,b])`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_MESON_TAC[division_of];
        ALL_TAC] THEN MESON_ASSUME_TAC [division_of]
       `interior(j:real^3->bool) INTER interior(interval[a:real^3,b]) = {}` THEN
      ASM SET_TAC[]; ASM_MESON_TAC[CUBE_IMP_NONEMPTY_INTERIOR]];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let VALLEY_INITIAL = prove
 (`!D (a:real^3) d.
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    ~(D = {interval[a, a + d % vec 1]})
    ==> valley D (interval[a - d % basis 1, a - d % basis 1 + d % vec 1])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[valley] THEN
  MESON_ASSUME_TAC [cube_dissection]
    `D division_of interval[a:real^3, a + d % vec 1]` THEN
  (* Nonemptiness of the virtual valley interval *)
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:3)
         ==> (a - d % basis 1:real^3)$i <=
             (a - d % basis 1 + d % vec 1:real^3)$i`
  ASSUME_TAC THENL [REWRITE_TAC[DIMINDEX_3; FORALL_3] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Compute and rewrite bounds of the virtual valley interval *)
  SUBGOAL_THEN `interval_upperbound(interval[a - d % basis 1:real^3,
                                   a - d % basis 1 + d % vec 1]) $1 =
     (a:real^3)$1 /\
     interval_lowerbound(interval[a - d % basis 1:real^3,
                                   a - d % basis 1 + d % vec 1]) $2 =
     a$2 /\
     interval_upperbound(interval[a - d % basis 1:real^3,
                                   a - d % basis 1 + d % vec 1]) $2 =
     a$2 + d /\
     interval_lowerbound(interval[a - d % basis 1:real^3,
                                   a - d % basis 1 + d % vec 1]) $3 =
     a$3 /\
     interval_upperbound(interval[a - d % basis 1:real^3,
                                   a - d % basis 1 + d % vec 1]) $3 =
     a$3 + d /\
     interval_length(interval[a - d % basis 1:real^3,
                               a - d % basis 1 + d % vec 1]) = d`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_3;
             ARITH_RULE `1 <= 1`; ARITH_RULE `1 <= 2`;
             ARITH_RULE `1 <= 3`; ARITH_RULE `2 <= 3`;
             ARITH_RULE `3 <= 3`] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[INTERVAL_LENGTH_CUBE] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [(* Condition 1: cube *)
    REWRITE_TAC[cube] THEN
    MAP_EVERY EXISTS_TAC [`a - d % basis 1:real^3`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    (* Condition 2: covering - every point on right face is covered *)
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN interval[a:real^3, a + d % vec 1]`
    ASSUME_TAC THENL [REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `?k:real^3->bool. k IN D /\ (z:real^3) IN k`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IN_UNIONS] THEN ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(k:real^3->bool) SUBSET interval[a:real^3, a + d % vec 1] /\
       ~(k = {}) /\ (?u v:real^3. k = interval[u,v])` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    MESON_ASSUME_TAC [] `~(interval[u:real^3,v] = {})` THEN
    SUBGOAL_THEN `interval_lowerbound(k:real^3->bool) = (u:real^3)`
    (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^3) IN interval[a:real^3, a + d % vec 1]`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(u:real^3) IN interval[u:real^3, v]` MP_TAC THENL
       [REWRITE_TAC[IN_INTERVAL] THEN GEN_TAC THEN DISCH_TAC THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `~(interval[u:real^3,v] = {})` THEN
        REWRITE_TAC[INTERVAL_NE_EMPTY] THEN ASM_MESON_TAC[];
        ASM SET_TAC[]]; ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^3)$1 <= (z:real^3)$1` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN (k:real^3->bool)` THEN
      ASM_REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^3)$1 <= (u:real^3)$1` ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^3) IN interval[a:real^3, a + d % vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    (* Condition 3: containment - touching cubes stay within bounds *)
    X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
    MESON_ASSUME_TAC [division_of]
      `(k:real^3->bool) SUBSET interval[a:real^3, a + d % vec 1]` THEN
    SUBGOAL_THEN `?c:real^3 e. &0 < e /\ k = interval[c, c + e % vec 1]`
      STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[cube_dissection; cube]; ALL_TAC] THEN
    SUBGOAL_THEN `interval_lowerbound(k:real^3->bool) = (c:real^3) /\
       interval_upperbound(k:real^3->bool) = c + e % vec 1:real^3` STRIP_ASSUME_TAC THENL
     [CUBE_BOUNDS_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET interval[a:real^3, a + d % vec 1]` THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_3; FORALL_3] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    (* Condition 4: size - touching cubes are strictly smaller *)
    X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
    MESON_ASSUME_TAC [division_of]
      `(k:real^3->bool) SUBSET interval[a:real^3, a + d % vec 1]` THEN
    SUBGOAL_THEN `?c:real^3 e. &0 < e /\ k = interval[c, c + e % vec 1]`
      STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[cube_dissection; cube]; ALL_TAC] THEN
    SUBGOAL_THEN `interval_length(k:real^3->bool) = e`
    (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE_POS]; ALL_TAC] THEN
    SUBGOAL_THEN `e <= d` ASSUME_TAC THENL
     [UNDISCH_TAC `(k:real^3->bool) SUBSET interval[a:real^3, a + d % vec 1]` THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_3; FORALL_3] THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `e:real = d` THENL
     [SUBGOAL_THEN `c:real^3 = a` ASSUME_TAC THENL
       [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN UNDISCH_TAC
          `(k:real^3->bool) SUBSET interval[a:real^3, a + d % vec 1]` THEN
        ASM_REWRITE_TAC[SUBSET_INTERVAL; INTERVAL_NE_EMPTY;
          DIMINDEX_3; FORALL_3] THEN
        SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `k = interval[a:real^3, a + d % vec 1]`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `D = {interval[a:real^3, a + d % vec 1]}` MP_TAC THENL
       [MATCH_MP_TAC DIVISION_WHOLE_IS_SINGLETON THEN
        ASM_MESON_TAC[cube_dissection]; ASM_MESON_TAC[]];
      ASM_REAL_ARITH_TAC]]);;

(* If x is on k's face at coordinate 1 (x$1 = upperbound k$1) with    *)
(* interior y,z in k, and j is a different element of a division       *)
(* containing x, then j starts exactly at k's upper x-bound.           *)

let DIVISION_FACE_LOWERBOUND = prove
 (`!D (k:real^3->bool) j (x:real^3).
    D division_of UNIONS D /\
    ~(interior k = {}) /\ ~(interior j = {}) /\
    k IN D /\ j IN D /\ ~(j = k) /\
    x IN k /\ x IN j /\
    x$1 = interval_upperbound k $ 1 /\
    interval_lowerbound k $ 2 < x$2 /\
    x$2 < interval_upperbound k $ 2 /\
    interval_lowerbound k $ 3 < x$3 /\
    x$3 < interval_upperbound k $ 3
    ==> interval_lowerbound j $ 1 = interval_upperbound k $ 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?u v:real^3. k = interval[u,v] /\ ~(interval[u,v] = {})`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  SUBGOAL_THEN `?p q:real^3. j = interval[p,q] /\ ~(interval[p,q] = {})`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  SUBGOAL_THEN `interval_lowerbound k = (u:real^3) /\
     interval_upperbound k = (v:real^3) /\
     interval_lowerbound j = (p:real^3) /\
     interval_upperbound j = (q:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; INTERVAL_UPPERBOUND_NONEMPTY];
    ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `interior(k:real^3->bool) INTER interior(j:real^3->bool) = {}`
    MP_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`~(interior(k:real^3->bool) = {})`;
    `~(interior(j:real^3->bool) = {})`;
    `(x:real^3) IN (j:real^3->bool)`;
    `(x:real^3)$1 = interval_upperbound (k:real^3->bool) $ 1`;
    `interval_lowerbound (k:real^3->bool) $ 2 < (x:real^3)$2`;
    `(x:real^3)$2 < interval_upperbound (k:real^3->bool) $ 2`;
    `interval_lowerbound (k:real^3->bool) $ 3 < (x:real^3)$3`;
    `(x:real^3)$3 < interval_upperbound (k:real^3->bool) $ 3`] THEN
  ASM_REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_NE_EMPTY; IN_INTERVAL;
                   DISJOINT_INTERVAL; DIMINDEX_3; MESON[]
    `(?i. 1 <= i /\ i <= 3 /\ P i) <=>
     ~(!i. 1 <= i /\ i <= 3 ==> ~P i)`; FORALL_3] THEN REAL_ARITH_TAC);;

(* Shared setup for pairs of elements from the 2D face-projection set E. *)
(* Expands e1,e2 from E, gets 3D preimages m1,m2, proves m1!=m2,        *)
(* extracts cube forms and interval bounds.                            *)
let E_PAIR_PREIMAGE_TAC =
  UNDISCH_TAC `(e1:real^2->bool) IN E` THEN
  EXPAND_TAC "E" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(e2:real^2->bool) IN E` THEN
  EXPAND_TAC "E" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m2:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(m1:real^3->bool = m2)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(e1:real^2->bool = e2)` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(?c1:real^3 s1. &0 < s1 /\ m1 = interval[c1, c1 + s1 % vec 1]) /\
     (?c2:real^3 s2. &0 < s2 /\ m2 = interval[c2, c2 + s2 % vec 1])` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_MESON_TAC[cube_dissection; cube]; ALL_TAC] THEN
  SUBGOAL_THEN `interval_lowerbound m1 = c1:real^3 /\
     interval_upperbound m1 = c1 + s1 % vec 1:real^3 /\
     interval_lowerbound m2 = c2:real^3 /\
     interval_upperbound m2 = c2 + s2 % vec 1:real^3` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CUBE_BOUNDS_TAC; ALL_TAC];;

(* The smallest cube on v's face is strictly in v's y,z interior,      *)
(* not touching v's face boundary. This is essential for the wall      *)
(* argument: it ensures wall cubes exist on all sides of k.            *)
(* Proof uses 2D projection onto v's face + SQUARE_DISSECTION_NONEDGE *)

let VALLEY_FACE_INTERIOR = prove
 (`!D (a:real^3) d (v:real^3->bool) k.
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    valley D v /\
    k IN D /\
    interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
    (?z:real^3. z IN k /\
         interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\ z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
         interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\ z$3 < interval_upperbound (v:real^3->bool) $ 3) /\
    (!j'. j' IN D /\ ~(j' = k) /\
          interval_lowerbound j' $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
          (?z:real^3. z IN j' /\
               interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
               z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
               interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
               z$3 < interval_upperbound (v:real^3->bool) $ 3)
          ==> interval_length k < interval_length j')
    ==> interval_lowerbound (v:real^3->bool) $ 2 < interval_lowerbound k $ 2 /\
        interval_upperbound k $ 2 < interval_upperbound (v:real^3->bool) $ 2 /\
        interval_lowerbound (v:real^3->bool) $ 3 < interval_lowerbound k $ 3 /\
        interval_upperbound k $ 3 < interval_upperbound (v:real^3->bool) $ 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Setup: extract valley properties *)
  FIRST_ASSUM(fun th ->
    let th' = GEN_REWRITE_RULE I [valley] th in
    LABEL_TAC "vcub" (CONJUNCT1 th') THEN
    LABEL_TAC "vcov" (CONJUNCT1(CONJUNCT2 th')) THEN
    LABEL_TAC "vcont" (CONJUNCT1(CONJUNCT2(CONJUNCT2 th'))) THEN
    LABEL_TAC "vsz" (CONJUNCT2(CONJUNCT2(CONJUNCT2 th')))) THEN
  MESON_ASSUME_TAC [cube_dissection] `(D:(real^3->bool)->bool) division_of UNIONS D` THEN
  MESON_ASSUME_TAC [division_of] `FINITE(D:(real^3->bool)->bool)` THEN
  MESON_ASSUME_TAC [cube_dissection] `cube(k:real^3->bool)` THEN
  SUBGOAL_THEN `?cv:real^3 sv. &0 < sv /\ v = interval[cv, cv + sv % vec 1]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[valley; cube]; ALL_TAC] THEN
  SUBGOAL_THEN `?ck:real^3 sk. &0 < sk /\ k = interval[ck, ck + sk % vec 1]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cube]; ALL_TAC] THEN
  SUBGOAL_THEN `(interval_lowerbound(v:real^3->bool) = cv /\
      interval_upperbound v = cv + sv % vec 1:real^3) /\
     (interval_lowerbound(k:real^3->bool) = ck /\
      interval_upperbound k = ck + sk % vec 1:real^3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN CUBE_BOUNDS_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VEC_COMPONENT; REAL_MUL_RID] THEN
  (* Goal: cv$2 < ck$2 /\ ck$2+sk < cv$2+sv /\
           cv$3 < ck$3 /\ ck$3+sk < cv$3+sv *)
  (* Establish the face condition: ck$1 = cv$1 + sv *)
  SUBGOAL_THEN `(ck:real^3)$1 = (cv:real^3)$1 + sv` ASSUME_TAC THENL
   [UNDISCH_TAC `interval_lowerbound(k:real^3->bool) $ 1 =
                 interval_upperbound(v:real^3->bool) $ 1` THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
  (* Weak containment from valley *)
  SUBGOAL_THEN `(cv:real^3)$2 <= (ck:real^3)$2 /\ ck$2 + sk <= cv$2 + sv /\
     cv$3 <= ck$3 /\ ck$3 + sk <= cv$3 + sv` STRIP_ASSUME_TAC THENL
   [USE_THEN "vcont" (MP_TAC o SPEC `k:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
  (* sk < sv from valley size *)
  SUBGOAL_THEN `sk < sv` ASSUME_TAC THENL
   [USE_THEN "vsz" (MP_TAC o SPEC `k:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE_POS]; ALL_TAC] THEN
  (* Now use the 2D projection approach via SQUARE_DISSECTION_NONEDGE *)
  (* Construct a 2D cube_dissection from the face cubes *)
  ABBREV_TAC
    `E = IMAGE (\m:real^3->bool.
       interval[vector[(interval_lowerbound m)$2;
                       (interval_lowerbound m)$3]:real^2,
                vector[(interval_upperbound m)$2;
                       (interval_upperbound m)$3]])
       {m | m IN D /\
            interval_lowerbound m $ 1 = (cv:real^3)$1 + sv /\
            (?z:real^3. z IN m /\
                 cv$2 < z$2 /\ z$2 < cv$2 + sv /\
                 cv$3 < z$3 /\ z$3 < cv$3 + sv)}` THEN ABBREV_TAC
    `face_sq = interval[vector[(cv:real^3)$2; cv$3]:real^2,
                         vector[cv$2 + sv; cv$3 + sv]]` THEN ABBREV_TAC
    `proj_k = interval[vector[(ck:real^3)$2; ck$3]:real^2,
                        vector[ck$2 + sk; ck$3 + sk]]` THEN
  (* Key claim: E is a cube_dissection with UNIONS E = face_sq,
     proj_k IN E, and proj_k is smallest *)
  SUBGOAL_THEN `cube_dissection (E:(real^2->bool)->bool) /\
     UNIONS E = (face_sq:real^2->bool) /\
     (proj_k:real^2->bool) IN E /\
     (!e:real^2->bool. e IN E /\ ~(e = proj_k)
          ==> interval_length proj_k < interval_length e)`
    STRIP_ASSUME_TAC THENL [(* Prove the 4-conjunct claim about E *)
    (* First, rewrite z-hypothesis into cv/sv form *)
    SUBGOAL_THEN `?z:real^3. z IN k /\ (cv:real^3)$2 < z$2 /\ z$2 < cv$2 + sv /\
                  cv$3 < z$3 /\ z$3 < cv$3 + sv` (LABEL_TAC "zk_cv") THENL
     [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
       [`interval_lowerbound(v:real^3->bool) $ 2 < (z:real^3)$2`;
        `(z:real^3)$2 < interval_upperbound(v:real^3->bool) $ 2`;
        `interval_lowerbound(v:real^3->bool) $ 3 < (z:real^3)$3`;
        `(z:real^3)$3 < interval_upperbound(v:real^3->bool) $ 3`] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                       VEC_COMPONENT; REAL_MUL_RID] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    (* Conjunct 3: proj_k IN E *)
    SUBGOAL_THEN `(proj_k:real^2->bool) IN E` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN EXPAND_TAC "proj_k" THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `k:real^3->bool` THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                       VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
    (* FINITE E *)
    SUBGOAL_THEN `FINITE(E:(real^2->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `D:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    (* Conjunct 1: cube_dissection E *)
    (* Step A: All elements of E are cube *)
    SUBGOAL_THEN `!e:real^2->bool. e IN E ==> cube e`
      (LABEL_TAC "ecub") THENL [X_GEN_TAC `ea:real^2->bool` THEN
      EXPAND_TAC "E" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `ma:real^3->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?cma:real^3 sma. &0 < sma /\ ma = interval[cma, cma + sma % vec 1]`
        STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[cube_dissection; cube]; ALL_TAC] THEN
      SUBGOAL_THEN `interval_lowerbound(ma:real^3->bool) = cma /\
         interval_upperbound ma = cma + sma % vec 1:real^3` STRIP_ASSUME_TAC THENL
       [CUBE_BOUNDS_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                       VEC_COMPONENT; REAL_MUL_RID; cube] THEN
      EXISTS_TAC `vector[(cma:real^3)$2; cma$3]:real^2` THEN
      EXISTS_TAC `sma:real` THEN ASM_REWRITE_TAC[VECTOR2_CUBE]; ALL_TAC] THEN
    (* Step B: Disjoint interiors *)
    SUBGOAL_THEN `!e1 e2:real^2->bool. e1 IN E /\ e2 IN E /\ ~(e1 = e2)
       ==> interior e1 INTER interior e2 = {}` (LABEL_TAC "edisj") THENL
     [MAP_EVERY X_GEN_TAC [`e1:real^2->bool`; `e2:real^2->bool`] THEN
      STRIP_TAC THEN E_PAIR_PREIMAGE_TAC THEN
      MESON_ASSUME_TAC [] `(c1:real^3)$1 = (c2:real^3)$1` THEN
      MESON_ASSUME_TAC [cube_dissection; division_of]
        `interior(m1:real^3->bool) INTER interior m2 = {}` THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      REWRITE_TAC[IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `vector[(c1:real^3)$1 + min s1 s2 / &2;
                (y:real^2)$1; y$2]:real^3 IN interior m1 /\
         vector[(c1:real^3)$1 + min s1 s2 / &2;
                (y:real^2)$1; y$2]:real^3 IN interior m2`
        STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; IN_INTERVAL;
          DIMINDEX_3; FORALL_3; VECTOR_3;
          VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
          VEC_COMPONENT; REAL_MUL_RID] THEN
        UNDISCH_TAC `(y:real^2) IN interior(e1:real^2->bool)` THEN
        UNDISCH_TAC `(y:real^2) IN interior(e2:real^2->bool)` THEN
        ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; IN_INTERVAL;
          DIMINDEX_2; FORALL_2; VECTOR_2;
          VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
          VEC_COMPONENT; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `interior(m1:real^3->bool) INTER interior m2 = {}` THEN
      ASM SET_TAC[]; ALL_TAC] THEN
    (* Step C: Pairwise distinct interval_lengths *)
    SUBGOAL_THEN `pairwise (\k k':real^2->bool.
         ~(interval_length k = interval_length k')) E` (LABEL_TAC "epw") THENL
     [REWRITE_TAC[pairwise] THEN
      MAP_EVERY X_GEN_TAC [`e1:real^2->bool`; `e2:real^2->bool`] THEN
      STRIP_TAC THEN E_PAIR_PREIMAGE_TAC THEN
      SUBGOAL_THEN `interval_length(e1:real^2->bool) = s1 /\
         interval_length(e2:real^2->bool) = s2` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN
        ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                         VEC_COMPONENT; REAL_MUL_RID; VECTOR2_CUBE] THEN
        ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE_POS]; ALL_TAC] THEN
      SUBGOAL_THEN `~(interval_length(m1:real^3->bool) = interval_length(m2:real^3->bool))`
        MP_TAC THENL [ASM_MESON_TAC[cube_dissection; pairwise]; ALL_TAC] THEN
      ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE_POS]; ALL_TAC] THEN
    (* Assemble cube_dissection *)
    SUBGOAL_THEN `cube_dissection(E:(real^2->bool)->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[cube_dissection; division_of] THEN
      REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `ef:real^2->bool` THEN DISCH_TAC THEN
        REPEAT CONJ_TAC THENL [ASM SET_TAC[];
          ASM_MESON_TAC[CUBE_IMP_NONEMPTY];
          ASM_MESON_TAC[cube]];
        USE_THEN "edisj" ACCEPT_TAC;
        USE_THEN "ecub" ACCEPT_TAC;
        USE_THEN "epw" ACCEPT_TAC]; ALL_TAC] THEN
    (* Conjunct 2: UNIONS E = face_sq *)
    SUBGOAL_THEN
      `UNIONS(E:(real^2->bool)->bool) = (face_sq:real^2->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [(* UNIONS E ⊆ face_sq *)
        REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `p:real^2` THEN
        DISCH_THEN(X_CHOOSE_THEN `ep:real^2->bool` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `(ep:real^2->bool) IN E` THEN
        EXPAND_TAC "E" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `mp:real^3->bool` STRIP_ASSUME_TAC) THEN
        (* Valley containment for mp *)
        SUBGOAL_THEN `(cv:real^3)$2 <= interval_lowerbound(mp:real^3->bool)$2 /\
           interval_upperbound(mp:real^3->bool)$2 <= cv$2 + sv /\
           cv$3 <= interval_lowerbound(mp:real^3->bool)$3 /\
           interval_upperbound(mp:real^3->bool)$3 <= cv$3 + sv` STRIP_ASSUME_TAC THENL
         [USE_THEN "vcont" (MP_TAC o SPEC `mp:real^3->bool`) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                           VEC_COMPONENT; REAL_MUL_RID] THEN
            ASM_MESON_TAC[]; ALL_TAC] THEN
          ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                          VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
        UNDISCH_TAC `(p:real^2) IN ep` THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "face_sq" THEN
        REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
        REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
        (* face_sq ⊆ UNIONS E via closure argument *)
        SUBGOAL_THEN `closed(UNIONS(E:(real^2->bool)->bool))` ASSUME_TAC THENL
         [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
          X_GEN_TAC `ef:real^2->bool` THEN DISCH_TAC THEN
          ASM_MESON_TAC[cube_dissection; cube; CLOSED_INTERVAL];
          ALL_TAC] THEN
        SUBGOAL_THEN `interval(vector[(cv:real^3)$2;cv$3]:real^2,
                    vector[cv$2 + sv;cv$3 + sv]) SUBSET
           UNIONS(E:(real^2->bool)->bool)`
          ASSUME_TAC THENL
         [REWRITE_TAC[SUBSET; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                       VECTOR_2] THEN X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
          SUBGOAL_THEN `?mp2:real^3->bool. mp2 IN D /\
              vector[(cv:real^3)$1 + sv;(y:real^2)$1;y$2]:real^3 IN mp2 /\
              interval_lowerbound mp2$1 = interval_upperbound(v:real^3->bool)$1`
            (X_CHOOSE_THEN `mp2:real^3->bool` STRIP_ASSUME_TAC) THENL
           [USE_THEN "vcov"
              (MATCH_MP_TAC o SPEC
                `vector[(cv:real^3)$1 + sv;(y:real^2)$1;y$2]:real^3`) THEN
            ASM_REWRITE_TAC[VECTOR_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
          REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC
            `interval[vector[(interval_lowerbound(mp2:real^3->bool))$2;
                              (interval_lowerbound mp2)$3]:real^2,
                      vector[(interval_upperbound mp2)$2;
                              (interval_upperbound mp2)$3]]` THEN
          CONJ_TAC THENL
           [EXPAND_TAC "E" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
            EXISTS_TAC `mp2:real^3->bool` THEN
            ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VEC_COMPONENT; REAL_MUL_RID] THEN EXISTS_TAC
              `vector[(cv:real^3)$1+sv;(y:real^2)$1;y$2]:real^3` THEN
            ASM_REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
          (* y IN proj(mp2) via cube form *)
          SUBGOAL_THEN `?cmp2:real^3 smp2.
               &0 < smp2 /\ mp2 = interval[cmp2, cmp2 + smp2 % vec 1]`
            STRIP_ASSUME_TAC THENL
           [ASM_MESON_TAC[cube_dissection; cube]; ALL_TAC] THEN
          SUBGOAL_THEN `interval_lowerbound mp2 = cmp2:real^3 /\
             interval_upperbound mp2 = cmp2 + smp2 % vec 1:real^3`
            STRIP_ASSUME_TAC THENL [CUBE_BOUNDS_TAC; ALL_TAC] THEN
          UNDISCH_TAC
            `vector[(cv:real^3)$1+sv;(y:real^2)$1;y$2]:real^3 IN mp2` THEN
          ASM_REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; DIMINDEX_2;
            FORALL_2; VECTOR_3; VECTOR_2;
            VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
            VEC_COMPONENT; REAL_MUL_RID] THEN MESON_TAC[]; ALL_TAC] THEN
        (* Now: closed(UNIONS E), open interval ⊆ UNIONS E *)
        EXPAND_TAC "face_sq" THEN
        SUBGOAL_THEN `~(interval(vector[(cv:real^3)$2;cv$3]:real^2,
                       vector[cv$2 + sv;cv$3 + sv]) = {})`
          ASSUME_TAC THENL
         [REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
          UNDISCH_TAC `&0 < sv` THEN REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `interval[vector[(cv:real^3)$2;cv$3]:real^2,
                     vector[cv$2 + sv;cv$3 + sv]] =
           closure(interval(vector[(cv:real^3)$2;cv$3]:real^2,
                             vector[cv$2 + sv;cv$3 + sv]))`
          SUBST1_TAC THENL
         [MATCH_MP_TAC(GSYM CLOSURE_OPEN_INTERVAL) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    (* Conjunct 4: minimality *)
    SUBGOAL_THEN `!e:real^2->bool. e IN E /\ ~(e = proj_k)
          ==> interval_length proj_k < interval_length e` ASSUME_TAC THENL
     [X_GEN_TAC `e0:real^2->bool` THEN STRIP_TAC THEN
      (* Unfold e0 IN E to get preimage m1 *)
      UNDISCH_TAC `(e0:real^2->bool) IN E` THEN EXPAND_TAC "E" THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `m1:real^3->bool` STRIP_ASSUME_TAC) THEN
      (* m1 is cube, get m1 = interval[cm1, cm1 + sm1 % vec 1] *)
      SUBGOAL_THEN `?cm1:real^3 sm1. &0 < sm1 /\ m1 = interval[cm1, cm1 + sm1 % vec 1]`
        STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[cube_dissection; cube]; ALL_TAC] THEN
      (* m1 != k: if m1 = k then e0 = proj_k, contradiction *)
      SUBGOAL_THEN `~(m1:real^3->bool = k)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~(e0:real^2->bool = proj_k)` THEN
        ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                        VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
      SUBGOAL_THEN `interval_length(k:real^3->bool) < interval_length(m1:real^3->bool)`
        ASSUME_TAC THENL [FIRST_ASSUM(fun th ->
          if is_forall(concl th) then
            let v,_ = dest_forall(concl th) in
            if fst(dest_var v) = "j'" then
              MP_TAC(SPEC `m1:real^3->bool` th)
            else failwith ""
          else failwith "") THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                          VEC_COMPONENT; REAL_MUL_RID] THEN ASM_MESON_TAC[];
          REWRITE_TAC[]]; ALL_TAC] THEN
      (* interval_length k = sk, interval_length m1 = sm1 *)
      SUBGOAL_THEN `interval_length(k:real^3->bool) = sk /\
                    interval_length(m1:real^3->bool) = sm1`
        STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE_POS]; ALL_TAC] THEN
      (* interval_length proj_k = sk *)
      SUBGOAL_THEN `interval_length(proj_k:real^2->bool) = sk`
        ASSUME_TAC THENL
       [EXPAND_TAC "proj_k" THEN REWRITE_TAC[VECTOR2_CUBE] THEN
        ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE_POS]; ALL_TAC] THEN
      (* interval_length e0 = sm1 *)
      SUBGOAL_THEN `interval_length(e0:real^2->bool) = sm1`
        ASSUME_TAC THENL
       [SUBGOAL_THEN `interval_lowerbound(m1:real^3->bool) = cm1 /\
           interval_upperbound m1 = cm1 + sm1 % vec 1:real^3` STRIP_ASSUME_TAC THENL
         [CUBE_BOUNDS_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                         VEC_COMPONENT; REAL_MUL_RID; VECTOR2_CUBE] THEN
        ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE_POS]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`E:(real^2->bool)->bool`;
                  `vector[(cv:real^3)$2; cv$3]:real^2`;
                  `vector[(cv:real^3)$2 + sv; cv$3 + sv]:real^2`;
                  `proj_k:real^2->bool`]
    SQUARE_DISSECTION_NONEDGE) THEN
  ANTS_TAC THENL [EXPAND_TAC "face_sq" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [(* proj_k = face_sq: contradiction since sk < sv *)
    (* First establish nonemptiness for EQ_INTERVAL simplification *)
    SUBGOAL_THEN `~(interval[vector[(ck:real^3)$2;ck$3]:real^2,
                  vector[ck$2 + sk;ck$3 + sk]] = {}) /\
       ~(interval[vector[(cv:real^3)$2;cv$3]:real^2,
                  vector[cv$2 + sv;cv$3 + sv]] = {})` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    (* Derive the concrete interval equality by transitivity *)
    SUBGOAL_THEN `interval[vector[(ck:real^3)$2;ck$3]:real^2,
                vector[ck$2 + sk;ck$3 + sk]] =
       interval[vector[(cv:real^3)$2;cv$3]:real^2,
                vector[cv$2 + sv;cv$3 + sv]]` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    (* EQ_INTERVAL + nonemptiness gives endpoint equality,
       CART_EQ decomposes to components, yielding sk = sv *)
    ASM_REWRITE_TAC[EQ_INTERVAL; CART_EQ; DIMINDEX_2; FORALL_2;
                    VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    (* proj_k SUBSET interior(face_sq) *)
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    EXPAND_TAC "proj_k" THEN EXPAND_TAC "face_sq" THEN
    REWRITE_TAC[INTERIOR_INTERVAL; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                VECTOR_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID; INTERVAL_NE_EMPTY] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `vector[(ck:real^3)$2; ck$3]:real^2` th) THEN
      MP_TAC(SPEC `vector[(ck:real^3)$2 + sk; ck$3 + sk]:real^2` th)) THEN
    REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC]);;

(* Helper: a nonempty open real interval minus a finite set is nonempty *)
let REAL_OPEN_INTERVAL_AVOID_FINITE = prove
 (`!s a b. FINITE s /\ a < b ==> ?x:real. a < x /\ x < b /\ ~(x IN s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `INFINITE({x:real | a < x /\ x < b} DIFF s)` MP_TAC THENL
   [MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
    ASM_REWRITE_TAC[INFINITE; FINITE_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Containment: if k is the smallest on v's face, and j starts at k's  *)
(* right face with a point in k's y,z interior, and m is an adjacent   *)
(* cube on v's face forming a "wall", then j fits inside k.            *)

(* Get a real w2 (resp. w3) in an open interval (lo,hi) avoiding all  *)
(* cube lowerbound/upperbound values in dimension 2 (resp. 3).       *)
let AVOID_DIM2_TAC lo hi =
  SUBGOAL_THEN (mk_binop `(<):real->real->bool` lo hi) ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MAX_LT; REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\k':real^3->bool. interval_lowerbound k' $ 2) D UNION
    IMAGE (\k':real^3->bool. interval_upperbound k' $ 2) D`; lo; hi]
   REAL_OPEN_INTERVAL_AVOID_FINITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real` STRIP_ASSUME_TAC);;

let AVOID_DIM3_TAC lo hi =
  SUBGOAL_THEN (mk_binop `(<):real->real->bool` lo hi) ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MAX_LT; REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\k':real^3->bool. interval_lowerbound k' $ 3) D UNION
    IMAGE (\k':real^3->bool. interval_upperbound k' $ 3) D`; lo; hi]
   REAL_OPEN_INTERVAL_AVOID_FINITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w3:real` STRIP_ASSUME_TAC);;

(* Common tactic for the 4 bound branches of VALLEY_DESCENT_CONTAINMENT *)
(* Given: valley v, witness vector[ub v$1; w2; w3] in face,
   w2/w3 avoiding cube boundaries, various bounds on w2/w3 *)
(* Proves: contradiction via interior overlap with j *)
let BOUND_COMMON_TAC =
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [valley]) THEN DISCH_THEN(MP_TAC o SPEC
    `vector[interval_upperbound (v:real^3->bool) $ 1; w2; w3]:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* m != k: the witness point is outside k by choice of w2 or w3 *)
  SUBGOAL_THEN `~(m = k:real^3->bool)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC
      `(vector[interval_upperbound (v:real^3->bool) $ 1; w2; w3]:real^3) IN
        (k:real^3->bool)` THEN
    ASM_REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID; VECTOR_3] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* m cube *)
  MESON_ASSUME_TAC [cube_dissection] `cube(m:real^3->bool)` THEN
  SUBGOAL_THEN `?cm:real^3 sm. &0 < sm /\ m = interval[cm, cm + sm % vec 1]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cube]; ALL_TAC] THEN
  SUBGOAL_THEN `(cm + sm % vec 1:real^3)$2 = cm$2 + sm /\
     (cm + sm % vec 1:real^3)$3 = cm$3 + sm` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `interval_lowerbound m = (cm:real^3) /\
     interval_upperbound m = cm + sm % vec 1:real^3` STRIP_ASSUME_TAC THENL
   [CUBE_BOUNDS_TAC; ALL_TAC] THEN
  (* interval_length k < interval_length m *)
  SUBGOAL_THEN `interval_length (k:real^3->bool) < interval_length (m:real^3->bool)`
    ASSUME_TAC THENL [SUBGOAL_THEN
      `m IN D /\ ~(m = k:real^3->bool) /\
       interval_lowerbound (m:real^3->bool) $ 1 =
         interval_upperbound (v:real^3->bool) $ 1 /\
       (?zz:real^3. zz IN m /\
         interval_lowerbound (v:real^3->bool) $ 2 < zz$2 /\
         zz$2 < interval_upperbound (v:real^3->bool) $ 2 /\
         interval_lowerbound (v:real^3->bool) $ 3 < zz$3 /\
         zz$3 < interval_upperbound (v:real^3->bool) $ 3)`
      MP_TAC THENL [ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `vector[interval_upperbound (v:real^3->bool) $ 1;
                w2; w3]:real^3` THEN ASM_REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  (* sk < sm *)
  SUBGOAL_THEN `sk < sm` ASSUME_TAC THENL [UNDISCH_TAC
      `interval_length (k:real^3->bool) < interval_length (m:real^3->bool)` THEN
    ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE_POS]; ALL_TAC] THEN
  (* m != j *)
  SUBGOAL_THEN `~(m = j:real^3->bool)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(cj:real^3)$1 = interval_upperbound (v:real^3->bool) $ 1` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Strict bounds: wpt in m's open interior *)
  SUBGOAL_THEN `interval_lowerbound (m:real^3->bool) $ 2 IN
       IMAGE (\k':real^3->bool. interval_lowerbound k' $ 2) D /\
     interval_upperbound (m:real^3->bool) $ 2 IN
       IMAGE (\k':real^3->bool. interval_upperbound k' $ 2) D /\
     interval_lowerbound (m:real^3->bool) $ 3 IN
       IMAGE (\k':real^3->bool. interval_lowerbound k' $ 3) D /\
     interval_upperbound (m:real^3->bool) $ 3 IN
       IMAGE (\k':real^3->bool. interval_upperbound k' $ 3) D`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `m:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(w2 = interval_lowerbound (m:real^3->bool) $ 2) /\
     ~(w2 = interval_upperbound (m:real^3->bool) $ 2) /\
     ~(w3 = interval_lowerbound (m:real^3->bool) $ 3) /\
     ~(w3 = interval_upperbound (m:real^3->bool) $ 3)`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    ASM_MESON_TAC[IN_IMAGE; IN_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `(cm:real^3)$2 < w2 /\ w2 < cm$2 + sm /\
     cm$3 < w3 /\ w3 < cm$3 + sm` STRIP_ASSUME_TAC THENL
   [(* Non-strict from membership, then avoidance makes strict *)
    SUBGOAL_THEN `(cm:real^3)$2 <= w2 /\ w2 <= cm$2 + sm /\
       cm$3 <= w3 /\ w3 <= cm$3 + sm` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(vector[interval_upperbound (v:real^3->bool) $ 1;
           w2; w3]:real^3) IN interval[cm:real^3, cm + sm % vec 1]`
        MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3;
                  VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                  VEC_COMPONENT; REAL_MUL_RID; VECTOR_3] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ ~(x = y) ==> x < y`) THEN
    CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Interior overlap: interior(m) ∩ interior(j) != {} *)
  SUBGOAL_THEN `~(interior (m:real^3->bool) INTER interior j = {})`
    MP_TAC THENL [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    ASM_REWRITE_TAC[INTERIOR_INTERVAL] THEN
    MESON_ASSUME_TAC [] `(cm:real^3)$1 = (ck:real^3)$1` THEN
    EXISTS_TAC `vector[(ck:real^3)$1 + sk + (min (sm - sk) sj) / &2;
              w2; w3]:real^3` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID; VECTOR_3] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  UNDISCH_TAC `(D:(real^3->bool)->bool) division_of UNIONS D` THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o
    REWRITE_RULE[division_of]) THEN
  DISCH_THEN(MP_TAC o SPECL [`m:real^3->bool`; `j:real^3->bool`]) THEN
  ASM_REWRITE_TAC[];;

let VALLEY_DESCENT_CONTAINMENT = prove
 (`!D (a:real^3) d (v:real^3->bool) k j.
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    valley D v /\
    k IN D /\
    interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
    (?z:real^3. z IN k /\
         interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\ z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
         interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\ z$3 < interval_upperbound (v:real^3->bool) $ 3) /\
    (!j'. j' IN D /\ ~(j' = k) /\
          interval_lowerbound j' $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
          (?z:real^3. z IN j' /\
               interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
               z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
               interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
               z$3 < interval_upperbound (v:real^3->bool) $ 3)
          ==> interval_length k < interval_length j') /\
    j IN D /\
    interval_lowerbound j $ 1 = interval_upperbound k $ 1 /\
    (?z:real^3. z IN j /\
         interval_lowerbound k $ 2 < z$2 /\ z$2 < interval_upperbound k $ 2 /\
         interval_lowerbound k $ 3 < z$3 /\ z$3 < interval_upperbound k $ 3)
    ==> interval_lowerbound k $ 2 <= interval_lowerbound j $ 2 /\
        interval_upperbound j $ 2 <= interval_upperbound k $ 2 /\
        interval_lowerbound k $ 3 <= interval_lowerbound j $ 3 /\
        interval_upperbound j $ 3 <= interval_upperbound k $ 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Apply VALLEY_FACE_INTERIOR for strict containment of k in v *)
  MP_TAC(ISPECL [`D:(real^3->bool)->bool`; `a:real^3`; `d:real`;
                  `v:real^3->bool`; `k:real^3->bool`]
    VALLEY_FACE_INTERIOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  (* Common setup *)
  MESON_ASSUME_TAC [cube_dissection] `(D:(real^3->bool)->bool) division_of UNIONS D` THEN
  MESON_ASSUME_TAC [division_of] `FINITE(D:(real^3->bool)->bool)` THEN
  MESON_ASSUME_TAC [cube_dissection] `cube(k:real^3->bool)` THEN
  MESON_ASSUME_TAC [cube_dissection] `cube(j:real^3->bool)` THEN
  (* Express k and j in cube form *)
  SUBGOAL_THEN `?ck:real^3 sk. &0 < sk /\ k = interval[ck, ck + sk % vec 1]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cube]; ALL_TAC] THEN
  SUBGOAL_THEN `?cj:real^3 sj. &0 < sj /\ j = interval[cj, cj + sj % vec 1]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cube]; ALL_TAC] THEN
  SUBGOAL_THEN `(interval_lowerbound k = (ck:real^3) /\
      interval_upperbound k = ck + sk % vec 1:real^3) /\
     (interval_lowerbound j = (cj:real^3) /\
      interval_upperbound j = cj + sj % vec 1:real^3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN CUBE_BOUNDS_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VEC_COMPONENT; REAL_MUL_RID] THEN
  (* === Common setup for all four bounds === *)
  SUBGOAL_THEN `(ck + sk % vec 1:real^3)$1 = ck$1 + sk /\
     (ck + sk % vec 1:real^3)$2 = ck$2 + sk /\
     (ck + sk % vec 1:real^3)$3 = ck$3 + sk /\
     (cj + sj % vec 1:real^3)$1 = cj$1 + sj /\
     (cj + sj % vec 1:real^3)$2 = cj$2 + sj /\
     (cj + sj % vec 1:real^3)$3 = cj$3 + sj`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
  MESON_ASSUME_TAC [] `(cj:real^3)$1 = (ck:real^3)$1 + sk` THEN
  MESON_ASSUME_TAC [] `(ck:real^3)$1 = interval_upperbound (v:real^3->bool) $ 1` THEN
  (* Explicit component equalities to avoid expensive MESON chaining *)
  SUBGOAL_THEN `interval_lowerbound (k:real^3->bool) $ 2 = (ck:real^3)$2 /\
     interval_lowerbound k $ 3 = ck$3 /\
     interval_upperbound k $ 2 = ck$2 + sk /\
     interval_upperbound k $ 3 = ck$3 + sk` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                     VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `(interval_lowerbound (v:real^3->bool) $ 2 < (ck:real^3)$2 /\
     ck$2 + sk < interval_upperbound (v:real^3->bool) $ 2 /\
     interval_lowerbound (v:real^3->bool) $ 3 < ck$3 /\
     ck$3 + sk < interval_upperbound (v:real^3->bool) $ 3) /\
     (ck$2 < (z':real^3)$2 /\ z'$2 < ck$2 + sk /\
      ck$3 < z'$3 /\ z'$3 < ck$3 + sk)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z':real^3) IN interval[cj:real^3, cj + sj % vec 1]`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(cj:real^3)$2 <= (z':real^3)$2 /\ z'$2 <= cj$2 + sj /\
     cj$3 <= z'$3 /\ z'$3 <= cj$3 + sj` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(IMAGE (\k':real^3->bool. interval_lowerbound k' $ 2) D UNION
            IMAGE (\k':real^3->bool. interval_upperbound k' $ 2) D) /\
     FINITE(IMAGE (\k':real^3->bool. interval_lowerbound k' $ 3) D UNION
            IMAGE (\k':real^3->bool. interval_upperbound k' $ 3) D)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[FINITE_UNION] THEN
    CONJ_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN SUBGOAL_THEN
    `pairwise (\k:real^3->bool k'. ~(interval_length k = interval_length k')) D`
    ASSUME_TAC THENL [ASM_MESON_TAC[cube_dissection]; ALL_TAC] THEN
  (* === Prove each bound by contradiction === *)
  REPEAT CONJ_TAC THENL [(* Bound 1: ck$2 <= cj$2 *)
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN AVOID_DIM3_TAC
      `max (interval_lowerbound (v:real^3->bool) $ 3) ((cj:real^3)$3)`
      `min (interval_upperbound (v:real^3->bool) $ 3) ((cj:real^3)$3 + sj)` THEN
    AVOID_DIM2_TAC
      `max (interval_lowerbound (v:real^3->bool) $ 2) ((cj:real^3)$2)`
      `(ck:real^3)$2` THEN SUBGOAL_THEN
      `interval_lowerbound (v:real^3->bool) $ 2 < w2 /\ (cj:real^3)$2 < w2 /\
       interval_lowerbound (v:real^3->bool) $ 3 < w3 /\ cj$3 < w3 /\
       w3 < interval_upperbound (v:real^3->bool) $ 3 /\ w3 < cj$3 + sj /\
       w2 < interval_upperbound (v:real^3->bool) $ 2`
      STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BOUND_COMMON_TAC;

    (* Bound 2: cj$2 + sj <= ck$2 + sk *)
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN AVOID_DIM3_TAC
      `max (interval_lowerbound (v:real^3->bool) $ 3) ((cj:real^3)$3)`
      `min (interval_upperbound (v:real^3->bool) $ 3) ((cj:real^3)$3 + sj)` THEN
    AVOID_DIM2_TAC `(ck:real^3)$2 + sk`
      `min (interval_upperbound (v:real^3->bool) $ 2) ((cj:real^3)$2 + sj)` THEN
    SUBGOAL_THEN
      `interval_lowerbound (v:real^3->bool) $ 2 < w2 /\
       w2 < (cj:real^3)$2 + sj /\
       w2 < interval_upperbound (v:real^3->bool) $ 2 /\
       interval_lowerbound (v:real^3->bool) $ 3 < w3 /\ cj$3 < w3 /\
       w3 < interval_upperbound (v:real^3->bool) $ 3 /\ w3 < cj$3 + sj`
      STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BOUND_COMMON_TAC;

    (* Bound 3: ck$3 <= cj$3 *)
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN AVOID_DIM2_TAC
      `max (interval_lowerbound (v:real^3->bool) $ 2) ((cj:real^3)$2)`
      `min (interval_upperbound (v:real^3->bool) $ 2) ((cj:real^3)$2 + sj)` THEN
    AVOID_DIM3_TAC
      `max (interval_lowerbound (v:real^3->bool) $ 3) ((cj:real^3)$3)`
      `(ck:real^3)$3` THEN SUBGOAL_THEN
      `interval_lowerbound (v:real^3->bool) $ 2 < w2 /\ (cj:real^3)$2 < w2 /\
       w2 < interval_upperbound (v:real^3->bool) $ 2 /\ w2 < cj$2 + sj /\
       interval_lowerbound (v:real^3->bool) $ 3 < w3 /\ cj$3 < w3 /\
       w3 < interval_upperbound (v:real^3->bool) $ 3`
      STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BOUND_COMMON_TAC;

    (* Bound 4: cj$3 + sj <= ck$3 + sk *)
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN AVOID_DIM2_TAC
      `max (interval_lowerbound (v:real^3->bool) $ 2) ((cj:real^3)$2)`
      `min (interval_upperbound (v:real^3->bool) $ 2) ((cj:real^3)$2 + sj)` THEN
    AVOID_DIM3_TAC `(ck:real^3)$3 + sk`
      `min (interval_upperbound (v:real^3->bool) $ 3) ((cj:real^3)$3 + sj)` THEN
    SUBGOAL_THEN
      `interval_lowerbound (v:real^3->bool) $ 2 < w2 /\ (cj:real^3)$2 < w2 /\
       w2 < interval_upperbound (v:real^3->bool) $ 2 /\ w2 < cj$2 + sj /\
       interval_lowerbound (v:real^3->bool) $ 3 < w3 /\
       w3 < (cj:real^3)$3 + sj /\
       w3 < interval_upperbound (v:real^3->bool) $ 3`
      STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BOUND_COMMON_TAC]);;

(* The smallest face cube has a neighbor: there must be another cube on v's face
   that is distinct from k and also overlaps v's interior in dims 2,3 *)

let VALLEY_FACE_EXISTS_ANOTHER = prove
 (`!D (a:real^3) d (v:real^3->bool) (k:real^3->bool).
     &0 < d /\
     cube_dissection D /\
     UNIONS D = interval[a, a + d % vec 1] /\
     valley D v /\
     k IN D /\
     interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
     (?z. z IN k /\
          interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
          z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
          interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
          z$3 < interval_upperbound (v:real^3->bool) $ 3) /\
     (!j'. j' IN D /\ ~(j' = k) /\
           interval_lowerbound j' $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
           (?z. z IN j' /\
                interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
                z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
                interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
                z$3 < interval_upperbound (v:real^3->bool) $ 3)
           ==> interval_length k < interval_length j')
     ==> ?j0. j0 IN D /\ ~(j0 = k) /\
              interval_lowerbound j0 $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
              (?z'. z' IN j0 /\
                    interval_lowerbound (v:real^3->bool) $ 2 < z'$2 /\
                    z'$2 < interval_upperbound (v:real^3->bool) $ 2 /\
                    interval_lowerbound (v:real^3->bool) $ 3 < z'$3 /\
                    z'$3 < interval_upperbound (v:real^3->bool) $ 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: Strict containment from VALLEY_FACE_INTERIOR *)
  SUBGOAL_THEN `interval_lowerbound (v:real^3->bool) $ 2 <
       interval_lowerbound (k:real^3->bool) $ 2 /\
     interval_upperbound k $ 2 < interval_upperbound (v:real^3->bool) $ 2 /\
     interval_lowerbound (v:real^3->bool) $ 3 < interval_lowerbound k $ 3 /\
     interval_upperbound k $ 3 < interval_upperbound (v:real^3->bool) $ 3` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`D:(real^3->bool)->bool`; `a:real^3`; `d:real`;
                   `v:real^3->bool`; `k:real^3->bool`]
      VALLEY_FACE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Step 2: Cubical form of k *)
  SUBGOAL_THEN `?ck:real^3 sk. &0 < sk /\ k = interval[ck, ck + sk % vec 1]`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cube_dissection; cube]; ALL_TAC] THEN
  (* Step 3: Compute bounds of k *)
  SUBGOAL_THEN `interval_lowerbound (k:real^3->bool) = (ck:real^3) /\
     interval_upperbound k = ck + sk % vec 1:real^3` STRIP_ASSUME_TAC THENL
   [CUBE_BOUNDS_TAC; ALL_TAC] THEN
  (* Step 4: Construct witness point in gap between v and k *)
  ABBREV_TAC `zw = vector[interval_upperbound (v:real^3->bool) $ 1;
     (interval_lowerbound (v:real^3->bool) $ 2 + (ck:real^3)$2) / &2;
     (interval_lowerbound (v:real^3->bool) $ 3 + ck$3) / &2]:real^3` THEN
  (* Step 5: Witness NOT in k (its $2 component < lb k$2) *)
  SUBGOAL_THEN `~((zw:real^3) IN (k:real^3->bool))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3;
      VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
      REAL_MUL_RID] THEN EXPAND_TAC "zw" THEN REWRITE_TAC[VECTOR_3] THEN
    UNDISCH_TAC `interval_lowerbound (v:real^3->bool) $ 2 <
                 interval_lowerbound (k:real^3->bool) $ 2` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* Step 6: Witness in v's face interior *)
  SUBGOAL_THEN `(zw:real^3)$1 = interval_upperbound (v:real^3->bool) $ 1 /\
     interval_lowerbound (v:real^3->bool) $ 2 < zw$2 /\
     zw$2 < interval_upperbound (v:real^3->bool) $ 2 /\
     interval_lowerbound (v:real^3->bool) $ 3 < zw$3 /\
     zw$3 < interval_upperbound (v:real^3->bool) $ 3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zw" THEN REWRITE_TAC[VECTOR_3] THEN MAP_EVERY UNDISCH_TAC
      [`&0 < sk`;
       `interval_upperbound (k:real^3->bool) $ 3 <
        interval_upperbound (v:real^3->bool) $ 3`;
       `interval_lowerbound (v:real^3->bool) $ 3 <
        interval_lowerbound (k:real^3->bool) $ 3`;
       `interval_upperbound (k:real^3->bool) $ 2 <
        interval_upperbound (v:real^3->bool) $ 2`;
       `interval_lowerbound (v:real^3->bool) $ 2 <
        interval_lowerbound (k:real^3->bool) $ 2`] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[VEC_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  (* Step 7: Valley covering gives j0 containing zw *)
  SUBGOAL_THEN `?j0:real^3->bool. j0 IN D /\ (zw:real^3) IN j0 /\
     interval_lowerbound j0 $ 1 = interval_upperbound (v:real^3->bool) $ 1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[valley]; ALL_TAC] THEN
  (* Step 8: j0 satisfies all conditions *)
  EXISTS_TAC `j0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [(* j0 != k: zw IN j0 but ~(zw IN k) *)
    ASM_MESON_TAC[];
    (* zw witnesses j0 overlapping v's interior *)
    EXISTS_TAC `zw:real^3` THEN ASM_REWRITE_TAC[]]);;

(* Key descent: any valley produces a smaller valley on an element of D *)

let VALLEY_DESCENT = prove
 (`!D (a:real^3) d (v:real^3->bool).
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    valley D v
    ==> ?k. k IN D /\ interval_length k < interval_length v /\
            valley D k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MESON_ASSUME_TAC [cube_dissection] `(D:(real^3->bool)->bool) division_of UNIONS D` THEN
  MESON_ASSUME_TAC [division_of] `FINITE(D:(real^3->bool)->bool)` THEN
  MESON_ASSUME_TAC [valley] `cube(v:real^3->bool)` THEN
  (* Face set is nonempty: v has a nonempty face covered by valley *)
  SUBGOAL_THEN `?k0:real^3->bool. k0 IN D /\
       interval_lowerbound k0 $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
       (?z:real^3. z IN k0 /\
            interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
            z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
            interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
            z$3 < interval_upperbound (v:real^3->bool) $ 3)`
    STRIP_ASSUME_TAC THENL
   [(* v is cube with positive side, so face interior is nonempty *)
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cube]) THEN
    DISCH_THEN(X_CHOOSE_THEN `av:real^3`
      (X_CHOOSE_THEN `dv:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `interval_upperbound (v:real^3->bool) $ 1 = (av:real^3)$1 + dv /\
       interval_lowerbound (v:real^3->bool) $ 2 = av$2 /\
       interval_upperbound (v:real^3->bool) $ 2 = av$2 + dv /\
       interval_lowerbound (v:real^3->bool) $ 3 = av$3 /\
       interval_upperbound (v:real^3->bool) $ 3 = av$3 + dv` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `~(interval[av:real^3, av + dv % vec 1] = {})`
        ASSUME_TAC THENL [ASM_MESON_TAC[CUBE_IMP_NONEMPTY]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[INTERVAL_UPPERBOUND_NONEMPTY;
                    INTERVAL_LOWERBOUND_NONEMPTY;
                    VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    VEC_COMPONENT] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [valley]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC
      `vector[(av:real^3)$1 + dv; av$2 + dv / &2; av$3 + dv / &2]:real^3`) THEN
    REWRITE_TAC[VECTOR_3] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `vector[(av:real^3)$1 + dv; av$2 + dv / &2; av$3 + dv / &2]:real^3` THEN
    ASM_REWRITE_TAC[VECTOR_3] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MESON_ASSUME_TAC [cube_dissection]
    `pairwise (\k:real^3->bool k'. ~(interval_length k = interval_length k')) D` THEN
  (* Get smallest face cube using FINITE_PAIRWISE_MINIMUM *)
  MP_TAC(ISPECL
   [`interval_length:(real^3->bool)->real`;
    `{k:real^3->bool | k IN D /\
       interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
       (?z:real^3. z IN k /\
            interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
            z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
            interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
            z$3 < interval_upperbound (v:real^3->bool) $ 3)}`]
    FINITE_PAIRWISE_MINIMUM) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `k0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PAIRWISE_MONO THEN EXISTS_TAC `D:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `interval_length (k:real^3->bool) < interval_length (v:real^3->bool)`
    ASSUME_TAC THENL [ASM_MESON_TAC[valley]; ALL_TAC] THEN
  EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  (* valley D k *)
  REWRITE_TAC[valley] THEN
  MESON_ASSUME_TAC [cube_dissection] `cube(k:real^3->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [(* covering: forall z on k's face, exists j in D *)
    X_GEN_TAC `zc:real^3` THEN STRIP_TAC THEN
    (* Express k in interval form *)
    SUBGOAL_THEN `?ck:real^3 sk. &0 < sk /\ k = interval[ck, ck + sk % vec 1]`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cube]; ALL_TAC] THEN
    MESON_ASSUME_TAC [CUBE_IMP_NONEMPTY] `~(k:real^3->bool = {})` THEN
    MESON_ASSUME_TAC [] `~(interval[ck:real^3,ck + sk % vec 1] = {})` THEN
    SUBGOAL_THEN `(k:real^3->bool) SUBSET interval[a:real^3, a + d % vec 1]`
      ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    (* ub k$1 < a$1 + d *)
    SUBGOAL_THEN `interval_upperbound (k:real^3->bool) $ 1 < (a + d % vec 1:real^3) $ 1`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `interval_upperbound (k:real^3->bool) $ 1 = interval_lowerbound k $ 1 + interval_length k`
        ASSUME_TAC THENL [MP_TAC(ISPECL [`k:real^3->bool`; `1`]
          INTERVAL_LENGTH_CUBE_COMPONENT) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      (* There exists another face cube j0 != k *)
      MP_TAC(ISPECL [`D:(real^3->bool)->bool`; `a:real^3`; `d:real`;
                     `v:real^3->bool`; `k:real^3->bool`]
        VALLEY_FACE_EXISTS_ANOTHER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `j0:real^3->bool` STRIP_ASSUME_TAC) THEN
      (* interval_length k < interval_length j0 *)
      SUBGOAL_THEN `interval_length (k:real^3->bool) < interval_length (j0:real^3->bool)`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MESON_ASSUME_TAC [cube_dissection] `cube(j0:real^3->bool)` THEN
      SUBGOAL_THEN `interval_upperbound (j0:real^3->bool) $ 1 = interval_lowerbound j0 $ 1 + interval_length j0`
        ASSUME_TAC THENL [MP_TAC(ISPECL [`j0:real^3->bool`; `1`]
          INTERVAL_LENGTH_CUBE_COMPONENT) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      (* j0 SUBSET big box *)
      SUBGOAL_THEN `(j0:real^3->bool) SUBSET interval[a:real^3, a + d % vec 1]`
        ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MESON_ASSUME_TAC [CUBE_IMP_NONEMPTY] `~(j0:real^3->bool = {})` THEN
      (* ub j0$1 <= (a+d%vec1)$1 *)
      SUBGOAL_THEN `interval_upperbound (j0:real^3->bool) $ 1 <= (a + d % vec 1:real^3) $ 1`
        ASSUME_TAC THENL [SUBGOAL_THEN
          `?cj:real^3 sj. &0 < sj /\ j0 = interval[cj, cj + sj % vec 1]`
          STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cube]; ALL_TAC] THEN
        SUBGOAL_THEN `~(interval[cj:real^3, cj + sj % vec 1] = {})`
          ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `interval_upperbound (j0:real^3->bool) IN j0`
          ASSUME_TAC THENL
         [ASM_SIMP_TAC[INTERVAL_UPPERBOUND_NONEMPTY; IN_INTERVAL;
            DIMINDEX_3; FORALL_3;
            VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
            REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `interval_upperbound (j0:real^3->bool) IN interval[a:real^3, a + d % vec 1]`
          MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        SIMP_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3;
          VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
          REAL_MUL_RID] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    (* zc is in k (on its boundary in dim 1, interior in dims 2,3) *)
    SUBGOAL_THEN `(zc:real^3) IN (k:real^3->bool)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(zc:real^3)$1 = interval_upperbound (k:real^3->bool) $ 1`;
        `interval_lowerbound (k:real^3->bool) $ 2 < (zc:real^3) $ 2`;
        `(zc:real^3) $ 2 < interval_upperbound (k:real^3->bool) $ 2`;
        `interval_lowerbound (k:real^3->bool) $ 3 < (zc:real^3) $ 3`;
        `(zc:real^3) $ 3 < interval_upperbound (k:real^3->bool) $ 3`;
        `&0 < sk`] THEN ASM_SIMP_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3;
        VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
        REAL_MUL_RID; INTERVAL_LOWERBOUND_NONEMPTY;
        INTERVAL_UPPERBOUND_NONEMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    (* a$1 < zc$1 *)
    SUBGOAL_THEN `(a:real^3)$1 < (zc:real^3)$1` ASSUME_TAC THENL [UNDISCH_TAC
        `(zc:real^3)$1 = interval_upperbound (k:real^3->bool)$1` THEN
      UNDISCH_TAC
        `(k:real^3->bool) SUBSET interval[a:real^3,a + d % vec 1]` THEN
      UNDISCH_TAC `&0 < sk` THEN
      ASM_SIMP_TAC[SUBSET_INTERVAL; INTERVAL_UPPERBOUND_NONEMPTY;
        DIMINDEX_3; FORALL_3;
        VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
        REAL_MUL_RID] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    (* Apply POINT_IN_MULTIPLE_DIVISION_OF_GEN with i=1 *)
    MP_TAC(ISPECL
      [`D:(real^3->bool)->bool`; `a:real^3`; `a + d % vec 1:real^3`;
       `ck:real^3`; `ck + sk % vec 1:real^3`; `zc:real^3`; `1`]
      POINT_IN_MULTIPLE_DIVISION_OF_GEN) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= 1`; DIMINDEX_3; ARITH_RULE `1 <= 3`] THEN
    ANTS_TAC THENL [UNDISCH_TAC
        `interval_upperbound (k:real^3->bool)$1 <
         (a + d % vec 1:real^3)$1` THEN
      ASM_SIMP_TAC[SUBSET_REFL; INTERVAL_UPPERBOUND_NONEMPTY;
        VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
        REAL_MUL_RID] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `jc:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `jc:real^3->bool` THEN
    REPEAT CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[];
      MATCH_MP_TAC(ISPECL
        [`D:(real^3->bool)->bool`; `k:real^3->bool`;
         `jc:real^3->bool`; `zc:real^3`] DIVISION_FACE_LOWERBOUND) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CUBE_IMP_NONEMPTY_INTERIOR; cube_dissection]];
    (* containment: face cubes of k fit in k's y,z footprint *)
    X_GEN_TAC `j:real^3->bool` THEN STRIP_TAC THEN MATCH_MP_TAC(ISPECL
      [`D:(real^3->bool)->bool`; `a:real^3`; `d:real`;
       `v:real^3->bool`; `k:real^3->bool`; `j:real^3->bool`]
      VALLEY_DESCENT_CONTAINMENT) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    (* smaller: face cubes of k have smaller interval_length *)
    X_GEN_TAC `j:real^3->bool` THEN STRIP_TAC THEN
    (* j != k since lowerbound j$1 = upperbound k$1 > lowerbound k$1 *)
    SUBGOAL_THEN `~(j:real^3->bool = k)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN MP_TAC(ISPECL [`k:real^3->bool`; `1`]
        INTERVAL_LENGTH_CUBE_COMPONENT) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < interval_length(k:real^3->bool)` MP_TAC THENL
       [UNDISCH_TAC `cube(k:real^3->bool)` THEN
        REWRITE_TAC[cube] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[INTERVAL_LENGTH_CUBE] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `interval_lowerbound (k:real^3->bool) $ 2 <=
         interval_lowerbound (j:real^3->bool) $ 2 /\
       interval_upperbound j $ 2 <= interval_upperbound k $ 2 /\
       interval_lowerbound k $ 3 <= interval_lowerbound j $ 3 /\
       interval_upperbound j $ 3 <= interval_upperbound k $ 3` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL
        [`D:(real^3->bool)->bool`; `a:real^3`; `d:real`;
         `v:real^3->bool`; `k:real^3->bool`; `j:real^3->bool`]
        VALLEY_DESCENT_CONTAINMENT) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_ASSUME_TAC [cube_dissection] `cube(j:real^3->bool)` THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ ~(x = y) ==> x < y`) THEN
    CONJ_TAC THENL [MP_TAC(ISPECL [`k:real^3->bool`; `2`]
        INTERVAL_LENGTH_CUBE_COMPONENT) THEN
      MP_TAC(ISPECL [`j:real^3->bool`; `2`]
        INTERVAL_LENGTH_CUBE_COMPONENT) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_MESON_TAC[pairwise]]]);;

(* Impossibility: no cube dissection of an interval can have a valley *)

let VALLEY_IMPOSSIBLE = prove
 (`!D (a:real^3) d (v:real^3->bool).
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    valley D v ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MESON_ASSUME_TAC [cube_dissection] `(D:(real^3->bool)->bool) division_of UNIONS D` THEN
  MESON_ASSUME_TAC [division_of] `FINITE(D:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `!n (v:real^3->bool).
       CARD {k:real^3->bool | k IN (D:(real^3->bool)->bool) /\
             interval_length k < interval_length v}
       = n /\ valley D v ==> F`
  (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `v':real^3->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`D:(real^3->bool)->bool`; `a:real^3`; `d:real`;
                 `v':real^3->bool`]
    VALLEY_DESCENT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `CARD {k':real^3->bool | k' IN (D:(real^3->bool)->bool) /\
           interval_length k' < interval_length (k:real^3->bool)}`) THEN
  ANTS_TAC THENL [SUBGOAL_THEN
     `{k':real^3->bool | k' IN (D:(real^3->bool)->bool) /\
                          interval_length k' < interval_length (k:real^3->bool)}
      PSUBSET
      {k':real^3->bool | k' IN D /\
                          interval_length k' < interval_length (v':real^3->bool)}`
    MP_TAC THENL [REWRITE_TAC[PSUBSET; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `k:real^3->bool`) THEN
      ASM_REWRITE_TAC[REAL_LT_REFL];
      DISCH_TAC THEN
      SUBGOAL_THEN `FINITE {k':real^3->bool | k' IN (D:(real^3->bool)->bool) /\
                 interval_length k' < interval_length (v':real^3->bool)}`
      ASSUME_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `CARD {k':real^3->bool | k' IN (D:(real^3->bool)->bool) /\
               interval_length k' < interval_length (k:real^3->bool)}
         < CARD {k':real^3->bool | k' IN D /\
                 interval_length k' < interval_length (v':real^3->bool)}`
      MP_TAC THENL [MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]];
    DISCH_THEN(MP_TAC o SPEC `k:real^3->bool`) THEN ASM_REWRITE_TAC[]]);;

(* For the cube case: use VALLEY_INITIAL + VALLEY_IMPOSSIBLE *)
let ONLY_TRIVIAL_CUBE_DISSECTION_CUBE = prove
 (`!(a:real^3) d D.
        &0 < d /\
        cube_dissection D /\
        UNIONS D = interval[a, a + d % vec 1]
        ==> D = {interval[a, a + d % vec 1]}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `D = {interval[a:real^3, a + d % vec 1]}` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`D:(real^3->bool)->bool`; `a:real^3`; `d:real`;
                 `interval[a - d % basis 1:real^3,
                           a - d % basis 1 + d % vec 1]`]
    VALLEY_IMPOSSIBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VALLEY_INITIAL THEN ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

(* Clean statement: a cube dissection of a cube is trivial *)

let ONLY_TRIVIAL_CUBE_DISSECTION = prove
 (`!D:(real^3->bool)->bool.
        cube_dissection D /\ cube(UNIONS D) ==> D = {UNIONS D}`,
  GEN_TAC THEN REWRITE_TAC[cube] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `a:real^3`
      (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC))) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ONLY_TRIVIAL_CUBE_DISSECTION_CUBE THEN ASM_REWRITE_TAC[]);;
