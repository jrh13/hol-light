unambiguous_interface();;

let INT_NUM = prove(`!u. (integer (real_of_num u))`,
        (REWRITE_TAC[is_int]) THEN GEN_TAC THEN
        (EXISTS_TAC (`u:num`)) THEN (MESON_TAC[]));;

let INT_NUM_REAL = prove(`!u. (real_of_int (int_of_num u) = real_of_num u)`,
        (REWRITE_TAC[int_of_num]) THEN
        GEN_TAC THEN (MESON_TAC[INT_NUM;int_rep]));;

let INT_IS_INT = prove(`!(a:int). (integer (real_of_int a))`,
        REWRITE_TAC[int_rep;int_abstr]);;

let INT_OF_NUM_DEST = prove(`!a n. ((real_of_int a = (real_of_num n)) =
                (a = int_of_num n))`,
        (REWRITE_TAC[int_eq])
        THEN (REPEAT GEN_TAC)
        THEN (REWRITE_TAC[int_of_num])
        THEN (ASSUME_TAC (SPEC (`n:num`) INT_NUM))
        THEN (UNDISCH_EL_TAC 0)
        THEN (SIMP_TAC[int_rep]));;

let INT_REP = prove(`!a. ?n m. (a = (int_of_num n) - (int_of_num m))`,
        GEN_TAC
        THEN (let tt =(REWRITE_RULE[is_int] (SPEC (`a:int`) INT_IS_INT)) in
                (CHOOSE_TAC tt))
        THEN (POP_ASSUM DISJ_CASES_TAC)
        THENL [
         (EXISTS_TAC (`n:num`)) THEN (EXISTS_TAC (`0`)) THEN
         (ASM_REWRITE_TAC[INT_SUB_RZERO;GSYM INT_OF_NUM_DEST]);
         (EXISTS_TAC (`0`)) THEN (EXISTS_TAC (`n:num`)) THEN
         (REWRITE_TAC[INT_SUB_LZERO]) THEN
         (UNDISCH_EL_TAC 0) THEN
         (REWRITE_TAC[GSYM REAL_NEG_EQ;GSYM INT_NEG_EQ;GSYM int_neg_th;GSYM
        INT_OF_NUM_DEST])]);;

let INT_REP2 = prove( `!a. ?n. ((a = (&: n)) \/ (a = (--: (&: n))))`,
(GEN_TAC)
   THEN ((let tt =(REWRITE_RULE[is_int] (SPEC (`a:int`) INT_IS_INT)) in
      (CHOOSE_TAC tt)))
   THEN ((POP_ASSUM DISJ_CASES_TAC))
   THENL
   [ ((EXISTS_TAC (`n:num`)))
   THEN ((ASM_REWRITE_TAC[GSYM INT_OF_NUM_DEST]));
     ((EXISTS_TAC (`n:num`)))
   (* THEN ((RULE_EL 0 (REWRITE_RULE[GSYM REAL_NEG_EQ;GSYM int_neg_th]))) *)
   THEN (H_REWRITE_RULE[THM (GSYM REAL_NEG_EQ);THM (GSYM int_neg_th)] (HYP_INT 0))
   THEN ((ASM_REWRITE_TAC[GSYM INT_NEG_EQ;GSYM INT_OF_NUM_DEST]))]);;



(* ------------------------------------------------------------------ *)
(* nabs : int -> num gives the natural number abs. value of an int *)
(* ------------------------------------------------------------------ *)


let nabs = new_definition(`nabs n = @u. ((n = int_of_num u) \/ (n =
        int_neg (int_of_num u)))`);;

let NABS_POS = prove(`!u. (nabs (int_of_num u)) = u`,
        GEN_TAC
        THEN (REWRITE_TAC [nabs])
        THEN (MATCH_MP_TAC SELECT_UNIQUE)
        THEN (GEN_TAC THEN BETA_TAC)
        THEN (EQ_TAC)
        THENL [(TAUT_TAC (` ((A==>C)/\ (B==>C)) ==> (A\/B ==>C) `));
                MESON_TAC[]]
        THEN CONJ_TAC THENL
        (let branch2 =  (REWRITE_TAC[int_eq;int_neg_th;INT_NUM_REAL])
        THEN (REWRITE_TAC[prove (`! u y.(((real_of_num u) = --(real_of_num y))=
                ((real_of_num u) +(real_of_num y) = (&0)))`,REAL_ARITH_TAC)])
        THEN (REWRITE_TAC[REAL_OF_NUM_ADD;REAL_OF_NUM_EQ])
        THEN (MESON_TAC[ADD_EQ_0]) in
        [(REWRITE_TAC[int_eq;INT_NUM_REAL]);branch2])
        THEN (REWRITE_TAC[INT_NUM_REAL])
        THEN (MESON_TAC[REAL_OF_NUM_EQ]));;

let NABS_NEG = prove(`!n. (nabs (-- (int_of_num n))) = n`,
        GEN_TAC
        THEN (REWRITE_TAC [nabs])
        THEN (MATCH_MP_TAC SELECT_UNIQUE)
        THEN (GEN_TAC THEN BETA_TAC)
        THEN (EQ_TAC)
        THENL [(TAUT_TAC (` ((A==>C)/\ (B==>C)) ==> (A\/B ==>C) `));
                MESON_TAC[]]
        THEN CONJ_TAC THENL
        (let branch1 =  (REWRITE_TAC[int_eq;int_neg_th;INT_NUM_REAL])
        THEN (REWRITE_TAC[prove (`! u y.((--(real_of_num u) = (real_of_num y))=
                ((real_of_num u) +(real_of_num y) = (&0)))`,REAL_ARITH_TAC)])
        THEN (REWRITE_TAC[REAL_OF_NUM_ADD;REAL_OF_NUM_EQ])
        THEN (MESON_TAC[ADD_EQ_0]) in
        [branch1;(REWRITE_TAC[int_eq;INT_NUM_REAL])])
        THEN (REWRITE_TAC[INT_NUM_REAL;int_neg_th;REAL_NEG_EQ;REAL_NEG_NEG])
        THEN (MESON_TAC[REAL_OF_NUM_EQ]));;


