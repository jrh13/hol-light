(* ========================================================================= *)
(* #61: Ceva's theorem.                                                      *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;
needs "Examples/sos.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* We use the notion of "betweenness".                                       *)
(* ------------------------------------------------------------------------- *)

let BETWEEN_THM = prove
 (`between x (a,b) <=>
       ?u. &0 <= u /\ u <= &1 /\ x = u % a + (&1 - u) % b`,
  REWRITE_TAC[BETWEEN_IN_CONVEX_HULL] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b} = {b,a}`] THEN
  REWRITE_TAC[CONVEX_HULL_2_ALT; IN_ELIM_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas to reduce geometric concepts to more convenient forms.             *)
(* ------------------------------------------------------------------------- *)

let NORM_CROSS = prove
 (`norm(a) * norm(b) * norm(c) = norm(d) * norm(e) * norm(f) <=>
   (a dot a) * (b dot b) * (c dot c) = (d dot d) * (e dot e) * (f dot f)`,
  let lemma = prove
   (`!x y. &0 <= x /\ &0 <= y ==> (x pow 2 = y pow 2 <=> x = y)`,
    REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[REAL_POW_2] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [`x:real`; `y:real`] REAL_LT_TOTAL) THEN
    ASM_MESON_TAC[REAL_LT_MUL2; REAL_LT_REFL]) in
  REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC(GSYM lemma) THEN SIMP_TAC[NORM_POS_LE; REAL_LE_MUL]);;

let COLLINEAR = prove
 (`!a b c:real^2.
        collinear {a:real^2,b,c} <=>
        ((a$1 - b$1) * (b$2 - c$2) = (a$2 - b$2) * (b$1 - c$1))`,
  let lemma = prove
   (`~(y1 = &0) /\ x2 * y1 = x1 * y2 ==> ?c. x1 = c * y1 /\ x2 = c * y2`,
    STRIP_TAC THEN EXISTS_TAC `x1 / y1` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^2 = b` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_MUL_LZERO] THEN
    REWRITE_TAC[COLLINEAR_SING; COLLINEAR_2; INSERT_AC];
    ALL_TAC] THEN
  REWRITE_TAC[collinear] THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (fun th ->
        MP_TAC(SPECL [`a:real^2`; `b:real^2`] th) THEN
        MP_TAC(SPECL [`b:real^2`; `c:real^2`] th))) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `a - b:real^2` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; ARITH; DE_MORGAN_THM] THEN STRIP_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT;
           VECTOR_SUB_COMPONENT; ARITH]
  THENL [ALL_TAC; ONCE_REWRITE_TAC[CONJ_SYM]] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN(REPEAT_TCL STRIP_THM_THEN SUBST1_TAC)) THEN
  MATCH_MP_TAC lemma THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* More or less automatic proof of the main direction.                       *)
(* ------------------------------------------------------------------------- *)

let CEVA_WEAK = prove
 (`!A B C X Y Z P:real^2.
        ~(collinear {A,B,C}) /\
        between X (B,C) /\ between Y (A,C) /\ between Z (A,B) /\
        between P (A,X) /\ between P (B,Y) /\ between P (C,Z)
        ==> dist(B,X) * dist(C,Y) * dist(A,Z) =
            dist(X,C) * dist(Y,A) * dist(Z,B)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[dist; NORM_CROSS; COLLINEAR; BETWEEN_THM] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
           CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  FIRST_X_ASSUM(MP_TAC o check(is_neg o concl)) THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* More laborious proof of equivalence.                                      *)
(* ------------------------------------------------------------------------- *)

let CEVA = prove
 (`!A B C X Y Z:real^2.
        ~(collinear {A,B,C}) /\
        between X (B,C) /\ between Y (C,A) /\ between Z (A,B)
        ==> (dist(B,X) * dist(C,Y) * dist(A,Z) =
             dist(X,C) * dist(Y,A) * dist(Z,B) <=>
             (?P. between P (A,X) /\ between P (B,Y) /\ between P (C,Z)))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`A:real^2 = B`; `A:real^2 = C`; `B:real^2 = C`] THEN
  ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_SING; COLLINEAR_2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[BETWEEN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `x:real`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `y:real`)
    (X_CHOOSE_TAC `z:real`)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN REWRITE_TAC[dist] THEN
  REWRITE_TAC[VECTOR_ARITH `B - (x % B + (&1 - x) % C) = (&1 - x) % (B - C)`;
              VECTOR_ARITH `(x % B + (&1 - x) % C) - C = x % (B - C)`] THEN
  REWRITE_TAC[NORM_MUL] THEN
  REWRITE_TAC[REAL_ARITH `(a * a') * (b * b') * (c * c') =
                          (a * b * c) * (a' * b' * c')`] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; REAL_EQ_MUL_RCANCEL; REAL_ENTIRE] THEN
  ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 <= &1 - x <=> x <= &1`; real_abs] THEN
  EQ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [COLLINEAR]) THEN
    SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; FORALL_2;
            VECTOR_ADD_COMPONENT; CART_EQ; VECTOR_MUL_COMPONENT; ARITH] THEN
    CONV_TAC REAL_RING] THEN
  DISCH_TAC THEN REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `?u v w. w = (&1 - u) * (&1 - x) /\
            v = (&1 - u) * x /\
            u = (&1 - v) * (&1 - y) /\
            u = (&1 - w) * z /\
            v = (&1 - w) * (&1 - z) /\
            w = (&1 - v) * y /\
            &0 <= u /\ u <= &1 /\ &0 <= v /\ v <= &1 /\ &0 <= w /\ w <= &1`
  (STRIP_ASSUME_TAC o GSYM) THENL
   [ALL_TAC;
    EXISTS_TAC `u % A + v % B + w % C:real^2` THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `u:real`; EXISTS_TAC `v:real`; EXISTS_TAC `w:real`] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  MATCH_MP_TAC(MESON[]
   `(!x. p x /\ q x ==> r x) /\ (?x. p x /\ q x)
    ==> (?x. p x /\ q x /\ r x)`) THEN
  CONJ_TAC THENL
   [GEN_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_neg o concl))) THEN
    REWRITE_TAC[IMP_IMP] THEN
    REPEAT(MATCH_MP_TAC(TAUT `(a ==> b /\ c) /\ (a /\ b /\ c ==> d)
                              ==> a ==> b /\ c /\ d`) THEN
           CONJ_TAC THENL
            [CONV_TAC REAL_RING ORELSE CONV_TAC REAL_SOS; ALL_TAC]) THEN
    CONV_TAC REAL_SOS;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR]) THEN
  ASM_CASES_TAC `x = &0` THENL
   [EXISTS_TAC `&1 - y / (&1 - x + x * y)` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_neg o concl))) THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  EXISTS_TAC `&1 - (&1 - z) / (x + (&1 - x) * (&1 - z))` THEN
  SUBGOAL_THEN `~(x + (&1 - x) * (&1 - z) = &0)` MP_TAC THENL
   [ALL_TAC;
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_neg o concl))) THEN
    CONV_TAC REAL_FIELD] THEN
  MATCH_MP_TAC(REAL_ARITH
   `z * (&1 - x) < &1 ==> ~(x + (&1 - x) * (&1 - z) = &0)`) THEN
  ASM_CASES_TAC `z = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_01] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * (&1 - x)` THEN
  ASM_SIMP_TAC[REAL_LE_RMUL; REAL_ARITH `x <= &1 ==> &0 <= &1 - x`] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Just for geometric intuition, verify metrical version of "between".       *)
(* This isn't actually needed in the proof. Moreover, this is now actually   *)
(* the definition of "between" so this is all a relic.                       *)
(* ------------------------------------------------------------------------- *)

let BETWEEN_SYM = prove
 (`!u v w. between v (u,w) <=> between v (w,u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BETWEEN_THM] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN EXISTS_TAC `&1 - u` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY VECTOR_ARITH_TAC THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let BETWEEN_METRICAL = prove
 (`!u v w:real^N. between v (u,w) <=> dist(u,v) + dist(v,w) = dist(u,w)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[BETWEEN_SYM] THEN REWRITE_TAC[BETWEEN_THM; dist] THEN
  REWRITE_TAC[VECTOR_ARITH `x % u + (&1 - x) % v = v + x % (u - v)`] THEN
  SUBST1_TAC(VECTOR_ARITH `u - w:real^N = (u - v) + (v - w)`) THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN REWRITE_TAC[NORM_TRIANGLE_EQ] THEN
  EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `u - (u + x):real^N = --x`; NORM_NEG;
                VECTOR_ARITH `(u + c % (w - u)) - w = (&1 - c) % (u - w)`] THEN
    REWRITE_TAC[VECTOR_ARITH `a % --(c % (x - y)) = (a * c) % (y - x)`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `c <= &1 ==> abs(&1 - c) = &1 - c`;
                 REAL_ARITH `&0 <= c ==> abs c = c`] THEN
    REWRITE_TAC[NORM_SUB; REAL_MUL_AC]] THEN
  DISCH_TAC THEN ASM_CASES_TAC `&0 < norm(u - v:real^N) + norm(v - w)` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `~(&0 < x + y) ==> &0 <= x /\ &0 <= y ==> x = &0 /\ y = &0`)) THEN
    REWRITE_TAC[NORM_POS_LE; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    STRIP_TAC THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_POS] THEN
    VECTOR_ARITH_TAC] THEN
  EXISTS_TAC `norm(u - v:real^N) / (norm(u - v) + norm(v - w))` THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO;
               REAL_MUL_LID; REAL_LE_ADDR; NORM_POS_LE] THEN
  MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN
  EXISTS_TAC `norm(u - v:real^N) + norm(v - w)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ARITH `x % (y + z % v) = x % y + (x * z) % v`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_DIV_LMUL] THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN VECTOR_ARITH_TAC);;
