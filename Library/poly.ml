(* ========================================================================= *)
(* Properties of real polynomials (not canonically represented).             *)
(* ========================================================================= *)

needs "Library/analysis.ml";;

prioritize_real();;

parse_as_infix("++",(16,"right"));;
parse_as_infix("**",(20,"right"));;
parse_as_infix("##",(20,"right"));;
parse_as_infix("divides",(14,"right"));;
parse_as_infix("exp",(22,"right"));;

do_list override_interface
  ["++",`poly_add:real list->real list->real list`;
   "**",`poly_mul:real list->real list->real list`;
   "##",`poly_cmul:real->real list->real list`;
   "neg",`poly_neg:real list->real list`;
   "divides",`poly_divides:real list->real list->bool`;
   "exp",`poly_exp:real list -> num -> real list`;
   "diff",`poly_diff:real list->real list`];;

(* ------------------------------------------------------------------------- *)
(* Application of polynomial as a real function.                             *)
(* ------------------------------------------------------------------------- *)

let poly = new_recursive_definition list_RECURSION
  `(poly [] x = &0) /\
   (poly (CONS h t) x = h + x * poly t x)`;;

let POLY_CONST = prove
 (`!c x. poly [c] x = c`,
  REWRITE_TAC[poly] THEN REAL_ARITH_TAC);;

let POLY_X = prove
 (`!c x. poly [&0; &1] x = x`,
  REWRITE_TAC[poly] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on polynomials.                                     *)
(* ------------------------------------------------------------------------- *)

let poly_add = new_recursive_definition list_RECURSION
  `([] ++ l2 = l2) /\
   ((CONS h t) ++ l2 =
        (if l2 = [] then CONS h t
                    else CONS (h + HD l2) (t ++ TL l2)))`;;

let poly_cmul = new_recursive_definition list_RECURSION
  `(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))`;;

let poly_neg = new_definition
  `neg = (##) (--(&1))`;;

let poly_mul = new_recursive_definition list_RECURSION
  `([] ** l2 = []) /\
   ((CONS h t) ** l2 =
       (if t = [] then h ## l2
                  else (h ## l2) ++ CONS (&0) (t ** l2)))`;;

let poly_exp = new_recursive_definition num_RECURSION
  `(p exp 0 = [&1]) /\
   (p exp (SUC n) = p ** p exp n)`;;

(* ------------------------------------------------------------------------- *)
(* Differentiation of polynomials (needs an auxiliary function).             *)
(* ------------------------------------------------------------------------- *)

let poly_diff_aux = new_recursive_definition list_RECURSION
  `(poly_diff_aux n [] = []) /\
   (poly_diff_aux n (CONS h t) = CONS (&n * h) (poly_diff_aux (SUC n) t))`;;

let poly_diff = new_definition
  `diff l = (if l = [] then [] else (poly_diff_aux 1 (TL l)))`;;

(* ------------------------------------------------------------------------- *)
(* Lengths.                                                                  *)
(* ------------------------------------------------------------------------- *)

let LENGTH_POLY_DIFF_AUX = prove
 (`!l n. LENGTH(poly_diff_aux n l) = LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; poly_diff_aux]);;

let LENGTH_POLY_DIFF = prove
 (`!l. LENGTH(poly_diff l) = PRE(LENGTH l)`,
  LIST_INDUCT_TAC THEN 
  SIMP_TAC[poly_diff; LENGTH; LENGTH_POLY_DIFF_AUX; NOT_CONS_NIL; TL; PRE]);;

(* ------------------------------------------------------------------------- *)
(* Useful clausifications.                                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD_CLAUSES = prove
 (`([] ++ p2 = p2) /\
   (p1 ++ [] = p1) /\
   ((CONS h1 t1) ++ (CONS h2 t2) = CONS (h1 + h2) (t1 ++ t2))`,
  REWRITE_TAC[poly_add; NOT_CONS_NIL; HD; TL] THEN
  SPEC_TAC(`p1:real list`,`p1:real list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[poly_add]);;

let POLY_CMUL_CLAUSES = prove
 (`(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))`,
  REWRITE_TAC[poly_cmul]);;

let POLY_NEG_CLAUSES = prove
 (`(neg [] = []) /\
   (neg (CONS h t) = CONS (--h) (neg t))`,
  REWRITE_TAC[poly_neg; POLY_CMUL_CLAUSES; REAL_MUL_LNEG; REAL_MUL_LID]);;

let POLY_MUL_CLAUSES = prove
 (`([] ** p2 = []) /\
   ([h1] ** p2 = h1 ## p2) /\
   ((CONS h1 (CONS k1 t1)) ** p2 = h1 ## p2 ++ CONS (&0) (CONS k1 t1 ** p2))`,
  REWRITE_TAC[poly_mul; NOT_CONS_NIL]);;

let POLY_DIFF_CLAUSES = prove
 (`(diff [] = []) /\
   (diff [c] = []) /\
   (diff (CONS h t) = poly_diff_aux 1 t)`,
  REWRITE_TAC[poly_diff; NOT_CONS_NIL; HD; TL; poly_diff_aux]);;

(* ------------------------------------------------------------------------- *)
(* Various natural consequences of syntactic definitions.                    *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD = prove
 (`!p1 p2 x. poly (p1 ++ p2) x = poly p1 x + poly p2 x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_add; poly; REAL_ADD_LID] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; HD; TL; poly; REAL_ADD_RID] THEN
  REAL_ARITH_TAC);;

let POLY_CMUL = prove
 (`!p c x. poly (c ## p) x = c * poly p x`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[poly; poly_cmul] THEN
  REAL_ARITH_TAC);;

let POLY_NEG = prove
 (`!p x. poly (neg p) x = --(poly p x)`,
  REWRITE_TAC[poly_neg; POLY_CMUL] THEN
  REAL_ARITH_TAC);;

let POLY_MUL = prove
 (`!x p1 p2. poly (p1 ** p2) x = poly p1 x * poly p2 x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_mul; poly; REAL_MUL_LZERO; POLY_CMUL; POLY_ADD] THEN
  SPEC_TAC(`h:real`,`h:real`) THEN
  SPEC_TAC(`t:real list`,`t:real list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_mul; POLY_CMUL; POLY_ADD; poly; POLY_CMUL;
    REAL_MUL_RZERO; REAL_ADD_RID; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[POLY_ADD; POLY_CMUL; poly] THEN
  REAL_ARITH_TAC);;

let POLY_EXP = prove
 (`!p n x. poly (p exp n) x = (poly p x) pow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[poly_exp; real_pow; POLY_MUL] THEN
  REWRITE_TAC[poly] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The derivative is a bit more complicated.                                 *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_LEMMA = prove
 (`!l n x. ((\x. (x pow (SUC n)) * poly l x) diffl
                   ((x pow n) * poly (poly_diff_aux (SUC n) l) x))(x)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly; poly_diff_aux; REAL_MUL_RZERO; DIFF_CONST] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:real`] THEN
  REWRITE_TAC[REAL_LDISTRIB; REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] (CONJUNCT2 pow))] THEN
  POP_ASSUM(MP_TAC o SPECL [`SUC n`; `x:real`]) THEN
  SUBGOAL_THEN `(((\x. (x pow (SUC n)) * h)) diffl
                        ((x pow n) * &(SUC n) * h))(x)`
  (fun th -> DISCH_THEN(MP_TAC o CONJ th)) THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MP_TAC(SPEC `\x. x pow (SUC n)` DIFF_CMUL) THEN BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPEC `SUC n` DIFF_POW) THEN REWRITE_TAC[SUC_SUB1] THEN
    DISCH_THEN(MATCH_ACCEPT_TAC o ONCE_REWRITE_RULE[REAL_MUL_SYM]);
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC]]);;

let POLY_DIFF = prove
 (`!l x. ((\x. poly l x) diffl (poly (diff l) x))(x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[POLY_DIFF_CLAUSES] THEN
  ONCE_REWRITE_TAC[SYM(ETA_CONV `\x. poly l x`)] THEN
  REWRITE_TAC[poly; DIFF_CONST] THEN
  MAP_EVERY X_GEN_TAC [`x:real`] THEN
  MP_TAC(SPECL [`t:(real)list`; `0`; `x:real`] POLY_DIFF_LEMMA) THEN
  REWRITE_TAC[SYM(num_CONV `1`)] THEN REWRITE_TAC[pow; REAL_MUL_LID] THEN
  REWRITE_TAC[POW_1] THEN
  DISCH_THEN(MP_TAC o CONJ (SPECL [`h:real`; `x:real`] DIFF_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* Trivial consequences.                                                     *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFFERENTIABLE = prove
 (`!l x. (\x. poly l x) differentiable x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `poly (diff l) x` THEN
  REWRITE_TAC[POLY_DIFF]);;

let POLY_CONT = prove
 (`!l x. (\x. poly l x) contl x`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
  EXISTS_TAC `poly (diff l) x` THEN
  MATCH_ACCEPT_TAC POLY_DIFF);;

let POLY_IVT_POS = prove
 (`!p a b. a < b /\ poly p a < &0 /\ poly p b > &0
           ==> ?x. a < x /\ x < b /\ (poly p x = &0)`,
  REWRITE_TAC[real_gt] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x. poly p x`; `a:real`; `b:real`; `&0`] IVT) THEN
  REWRITE_TAC[POLY_CONT] THEN
  EVERY_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_LT_IMP_LE th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN
  CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_LT_REFL]) THEN
  FIRST_ASSUM CONTR_TAC);;

let POLY_IVT_NEG = prove
 (`!p a b. a < b /\ poly p a > &0 /\ poly p b < &0
           ==> ?x. a < x /\ x < b /\ (poly p x = &0)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `poly_neg p` POLY_IVT_POS) THEN
  REWRITE_TAC[POLY_NEG;
              REAL_ARITH `(--x < &0 <=> x > &0) /\ (--x > &0 <=> x < &0)`] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real`; `b:real`]) THEN
  ASM_REWRITE_TAC[REAL_ARITH `(--x = &0) <=> (x = &0)`]);;

let POLY_MVT = prove
 (`!p a b. a < b ==>
           ?x. a < x /\ x < b /\
              (poly p b - poly p a = (b - a) * poly (diff p) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`poly p`; `a:real`; `b:real`] MVT) THEN
  ASM_REWRITE_TAC[CONV_RULE(DEPTH_CONV ETA_CONV) (SPEC_ALL POLY_CONT);
    CONV_RULE(DEPTH_CONV ETA_CONV) (SPEC_ALL POLY_DIFFERENTIABLE)] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC DIFF_UNIQ THEN
  EXISTS_TAC `poly p` THEN EXISTS_TAC `x:real` THEN
  ASM_REWRITE_TAC[CONV_RULE(DEPTH_CONV ETA_CONV) (SPEC_ALL POLY_DIFF)]);;

let POLY_MVT_ADD = prove
 (`!p a x. ?y. abs(y) <= abs(x) /\
               (poly p (a + x) = poly p a + x * poly (diff p) (a + y))`,
  REPEAT GEN_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC `x:real` REAL_LT_NEGTOTAL) THENL
   [EXISTS_TAC `&0` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_RID; REAL_MUL_LZERO];
    MP_TAC(SPECL [`p:real list`; `a:real`; `a + x`] POLY_MVT) THEN
    ASM_REWRITE_TAC[REAL_LT_ADDR] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC) THEN
    REWRITE_TAC[REAL_ARITH `(x - y = ((a + b) - a) * z) <=>
                            (x = y + b * z)`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
    EXISTS_TAC `z - a` THEN REWRITE_TAC[REAL_ARITH `x + (y - x) = y`] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < x`; `a < z`; `z < a + x`] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`p:real list`; `a + x`; `a:real`] POLY_MVT) THEN
    ASM_REWRITE_TAC[REAL_ARITH `a + x < a <=> &0 < --x`] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC) THEN
    REWRITE_TAC[REAL_ARITH `(x - y = (a - (a + b)) * z) <=>
                            (x = y + b * --z)`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
    EXISTS_TAC `z - a` THEN REWRITE_TAC[REAL_ARITH `x + (y - x) = y`] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < --x`; `a + x < z`; `z < a`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD_RZERO = prove
 (`!p. poly (p ++ []) = poly p`,
  REWRITE_TAC[FUN_EQ_THM; POLY_ADD; poly; REAL_ADD_RID]);;

let POLY_MUL_ASSOC = prove
 (`!p q r. poly (p ** (q ** r)) = poly ((p ** q) ** r)`,
  REWRITE_TAC[FUN_EQ_THM; POLY_MUL; REAL_MUL_ASSOC]);;

let POLY_EXP_ADD = prove
 (`!d n p. poly(p exp (n + d)) = poly(p exp n ** p exp d)`,
  REWRITE_TAC[FUN_EQ_THM; POLY_MUL] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[POLY_MUL; ADD_CLAUSES; poly_exp; poly] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas for derivatives.                                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_AUX_ADD = prove
 (`!p1 p2 n. poly (poly_diff_aux n (p1 ++ p2)) =
             poly (poly_diff_aux n p1 ++ poly_diff_aux n p2)`,
  REPEAT(LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff_aux; poly_add]) THEN
  ASM_REWRITE_TAC[poly_diff_aux; FUN_EQ_THM; poly; NOT_CONS_NIL; HD; TL] THEN
  REAL_ARITH_TAC);;

let POLY_DIFF_AUX_CMUL = prove
 (`!p c n. poly (poly_diff_aux n (c ## p)) =
           poly (c ## poly_diff_aux n p)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; poly; poly_diff_aux; poly_cmul; REAL_MUL_AC]);;

let POLY_DIFF_AUX_NEG = prove
 (`!p n.  poly (poly_diff_aux n (neg p)) =
          poly (neg (poly_diff_aux n p))`,
  REWRITE_TAC[poly_neg; POLY_DIFF_AUX_CMUL]);;

let POLY_DIFF_AUX_MUL_LEMMA = prove
 (`!p n. poly (poly_diff_aux (SUC n) p) = poly (poly_diff_aux n p ++ p)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff_aux; poly_add; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[HD; TL; poly; FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Final results for derivatives.                                            *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_ADD = prove
 (`!p1 p2. poly (diff (p1 ++ p2)) =
           poly (diff p1  ++ diff p2)`,
  REPEAT LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_add; poly_diff; NOT_CONS_NIL; POLY_ADD_RZERO] THEN
  ASM_REWRITE_TAC[HD; TL; POLY_DIFF_AUX_ADD]);;

let POLY_DIFF_CMUL = prove
 (`!p c. poly (diff (c ## p)) = poly (c ## diff p)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff; poly_cmul] THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL; POLY_DIFF_AUX_CMUL]);;

let POLY_DIFF_NEG = prove
 (`!p. poly (diff (neg p)) = poly (neg (diff p))`,
  REWRITE_TAC[poly_neg; POLY_DIFF_CMUL]);;

let POLY_DIFF_MUL_LEMMA = prove
 (`!t h. poly (diff (CONS h t)) =
         poly (CONS (&0) (diff t) ++ t)`,
  REWRITE_TAC[poly_diff; NOT_CONS_NIL] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff_aux; NOT_CONS_NIL; HD; TL] THENL
   [REWRITE_TAC[FUN_EQ_THM; poly; poly_add; REAL_MUL_RZERO; REAL_ADD_LID];
    REWRITE_TAC[FUN_EQ_THM; poly; POLY_DIFF_AUX_MUL_LEMMA; POLY_ADD] THEN
    REAL_ARITH_TAC]);;

let POLY_DIFF_MUL = prove
 (`!p1 p2. poly (diff (p1 ** p2)) =
           poly (p1 ** diff p2 ++ diff p1 ** p2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_mul] THENL
   [REWRITE_TAC[poly_diff; poly_add; poly_mul]; ALL_TAC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[POLY_DIFF_CLAUSES] THEN
    REWRITE_TAC[poly_add; poly_mul; POLY_ADD_RZERO; POLY_DIFF_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; POLY_DIFF_ADD; POLY_ADD] THEN
  REWRITE_TAC[poly; POLY_ADD; POLY_DIFF_MUL_LEMMA; POLY_MUL] THEN
  ASM_REWRITE_TAC[POLY_DIFF_CMUL; POLY_ADD; POLY_MUL] THEN
  REAL_ARITH_TAC);;

let POLY_DIFF_EXP = prove
 (`!p n. poly (diff (p exp (SUC n))) =
         poly ((&(SUC n) ## (p exp n)) ** diff p)`,
  GEN_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[poly_exp] THENL
   [REWRITE_TAC[poly_exp; POLY_DIFF_MUL] THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; POLY_ADD; POLY_CMUL] THEN
    REWRITE_TAC[poly; POLY_DIFF_CLAUSES; ADD1; ADD_CLAUSES] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[POLY_DIFF_MUL] THEN
    ASM_REWRITE_TAC[POLY_MUL; POLY_ADD; FUN_EQ_THM; POLY_CMUL] THEN
    REWRITE_TAC[poly_exp; POLY_MUL] THEN
    REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC]);;

let POLY_DIFF_EXP_PRIME = prove
 (`!n a. poly (diff ([--a; &1] exp (SUC n))) =
         poly (&(SUC n) ## ([--a; &1] exp n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[POLY_DIFF_EXP] THEN
  REWRITE_TAC[FUN_EQ_THM; POLY_MUL] THEN
  REWRITE_TAC[poly_diff; poly_diff_aux; TL; NOT_CONS_NIL] THEN
  REWRITE_TAC[poly] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Key property that f(a) = 0 ==> (x - a) divides p(x). Very delicate!       *)
(* ------------------------------------------------------------------------- *)

let POLY_LINEAR_REM = prove
 (`!t h. ?q r. CONS h t = [r] ++ [--a; &1] ** q`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[] THENL
   [GEN_TAC THEN EXISTS_TAC `[]:real list` THEN
    EXISTS_TAC `h:real` THEN
    REWRITE_TAC[poly_add; poly_mul; poly_cmul; NOT_CONS_NIL] THEN
    REWRITE_TAC[HD; TL; REAL_ADD_RID];
    X_GEN_TAC `k:real` THEN POP_ASSUM(STRIP_ASSUME_TAC o SPEC `h:real`) THEN
    EXISTS_TAC `CONS (r:real) q` THEN EXISTS_TAC `r * a + k` THEN
    ASM_REWRITE_TAC[POLY_ADD_CLAUSES; POLY_MUL_CLAUSES; poly_cmul] THEN
    REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`q:real list`,`q:real list`) THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC[POLY_ADD_CLAUSES; POLY_MUL_CLAUSES; poly_cmul] THEN
    REWRITE_TAC[REAL_ADD_RID; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ADD_AC]]);;

let POLY_LINEAR_DIVIDES = prove
 (`!a p. (poly p a = &0) <=> (p = []) \/ ?q. p = [--a; &1] ** q`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[poly]; ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [DISJ2_TAC THEN STRIP_ASSUME_TAC(SPEC_ALL POLY_LINEAR_REM) THEN
    EXISTS_TAC `q:real list` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `poly (CONS h t) a = &0` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLY_ADD; POLY_MUL] THEN
      REWRITE_TAC[poly; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_ARITH `--a + a = &0`] THEN REAL_ARITH_TAC;
      REWRITE_TAC[poly_mul] THEN REWRITE_TAC[NOT_CONS_NIL] THEN
      SPEC_TAC(`q:real list`,`q:real list`) THEN LIST_INDUCT_TAC THENL
       [REWRITE_TAC[poly_cmul; poly_add; NOT_CONS_NIL; HD; TL; REAL_ADD_LID];
        REWRITE_TAC[poly_cmul; poly_add; NOT_CONS_NIL; HD; TL; REAL_ADD_LID]]];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[poly];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[poly] THEN
    REWRITE_TAC[POLY_MUL] THEN REWRITE_TAC[poly] THEN
    REWRITE_TAC[poly; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `--a + a = &0`] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Thanks to the finesse of the above, we can use length rather than degree. *)
(* ------------------------------------------------------------------------- *)

let POLY_LENGTH_MUL = prove
 (`!q. LENGTH([--a; &1] ** q) = SUC(LENGTH q)`,
  let lemma = prove
   (`!p h k a. LENGTH (k ## p ++ CONS h (a ## p)) = SUC(LENGTH p)`,
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[poly_cmul; POLY_ADD_CLAUSES; LENGTH]) in
  REWRITE_TAC[poly_mul; NOT_CONS_NIL; lemma]);;

(* ------------------------------------------------------------------------- *)
(* Thus a nontrivial polynomial of degree n has no more than n roots.        *)
(* ------------------------------------------------------------------------- *)

let POLY_ROOTS_INDEX_LEMMA = prove
 (`!n. !p. ~(poly p = poly []) /\ (LENGTH p = n)
           ==> ?i. !x. (poly p (x) = &0) ==> ?m. m <= n /\ (x = i m)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH_EQ_NIL] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `?a. poly p a = &0` THENL
     [UNDISCH_TAC `?a. poly p a = &0` THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      GEN_REWRITE_TAC LAND_CONV [POLY_LINEAR_DIVIDES] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real list` SUBST_ALL_TAC) THEN
      FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
      UNDISCH_TAC `~(poly ([-- a; &1] ** q) = poly [])` THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[POLY_LENGTH_MUL; SUC_INJ] THEN
      DISCH_TAC THEN ASM_CASES_TAC `poly q = poly []` THENL
       [ASM_REWRITE_TAC[POLY_MUL; poly; REAL_MUL_RZERO; FUN_EQ_THM];
        DISCH_THEN(K ALL_TAC)] THEN
      DISCH_THEN(MP_TAC o SPEC `q:real list`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `i:num->real`) THEN
      EXISTS_TAC `\m. if m = SUC n then (a:real) else i m` THEN
      REWRITE_TAC[POLY_MUL; LE; REAL_ENTIRE] THEN
      X_GEN_TAC `x:real` THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN(fun th -> EXISTS_TAC `SUC n` THEN MP_TAC th) THEN
        REWRITE_TAC[poly] THEN REAL_ARITH_TAC;
        DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `m:num <= n` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
      UNDISCH_TAC `~(?a. poly p a = &0)` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]]);;

let POLY_ROOTS_INDEX_LENGTH = prove
 (`!p. ~(poly p = poly [])
       ==> ?i. !x. (poly p(x) = &0) ==> ?n. n <= LENGTH p /\ (x = i n)`,
  MESON_TAC[POLY_ROOTS_INDEX_LEMMA]);;

let POLY_ROOTS_FINITE_LEMMA = prove
 (`!p. ~(poly p = poly [])
       ==> ?N i. !x. (poly p(x) = &0) ==> ?n:num. n < N /\ (x = i n)`,
  MESON_TAC[POLY_ROOTS_INDEX_LENGTH; LT_SUC_LE]);;

let FINITE_LEMMA = prove
 (`!i N P. (!x. P x ==> ?n:num. n < N /\ (x = i n))
           ==> ?a. !x. P x ==> x < a`,
  GEN_TAC THEN ONCE_REWRITE_TAC[RIGHT_IMP_EXISTS_THM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT] THEN MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `P:real->bool` THEN
  POP_ASSUM(MP_TAC o SPEC `\z. P z /\ ~(z = (i:num->real) N)`) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  EXISTS_TAC `abs(a) + abs(i(N:num)) + &1` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LT] THEN
  MP_TAC(REAL_ARITH `!x v. x < abs(v) + abs(x) + &1`) THEN
  MP_TAC(REAL_ARITH `!u v x. x < v ==> x < abs(v) + abs(u) + &1`) THEN
  MESON_TAC[]);;

let POLY_ROOTS_FINITE = prove
 (`!p. ~(poly p = poly []) <=>
       ?N i. !x. (poly p(x) = &0) ==> ?n:num. n < N /\ (x = i n)`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[POLY_ROOTS_FINITE_LEMMA] THEN
  REWRITE_TAC[FUN_EQ_THM; LEFT_IMP_EXISTS_THM; NOT_FORALL_THM; poly] THEN
  MP_TAC(GENL [`i:num->real`; `N:num`]
   (SPECL [`i:num->real`; `N:num`; `\x. poly p x = &0`] FINITE_LEMMA)) THEN
  REWRITE_TAC[] THEN MESON_TAC[REAL_LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Hence get entirety and cancellation for polynomials.                      *)
(* ------------------------------------------------------------------------- *)

let POLY_ENTIRE_LEMMA = prove
 (`!p q. ~(poly p = poly []) /\ ~(poly q = poly [])
         ==> ~(poly (p ** q) = poly [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[POLY_ROOTS_FINITE] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (X_CHOOSE_TAC `i2:num->real`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (X_CHOOSE_TAC `i1:num->real`)) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  EXISTS_TAC `\n:num. if n < N1 then i1(n):real else i2(n - N1)` THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[REAL_ENTIRE; POLY_MUL] THEN
  DISCH_THEN(DISJ_CASES_THEN (ANTE_RES_THEN (X_CHOOSE_TAC `n:num`))) THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN ARITH_TAC;
    EXISTS_TAC `N1 + n:num` THEN ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `~(m + n < m:num)`] THEN
    AP_TERM_TAC THEN ARITH_TAC]);;

let POLY_ENTIRE = prove
 (`!p q. (poly (p ** q) = poly []) <=>
         (poly p = poly []) \/ (poly q = poly [])`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[POLY_ENTIRE_LEMMA];
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; poly]]);;

let POLY_MUL_LCANCEL = prove
 (`!p q r. (poly (p ** q) = poly (p ** r)) <=>
           (poly p = poly []) \/ (poly q = poly r)`,
  let lemma1 = prove
   (`!p q. (poly (p ++ neg q) = poly []) <=> (poly p = poly q)`,
    REWRITE_TAC[FUN_EQ_THM; POLY_ADD; POLY_NEG; poly] THEN
    REWRITE_TAC[REAL_ARITH `(p + --q = &0) <=> (p = q)`]) in
  let lemma2 = prove
   (`!p q r. poly (p ** q ++ neg(p ** r)) = poly (p ** (q ++ neg(r)))`,
    REWRITE_TAC[FUN_EQ_THM; POLY_ADD; POLY_NEG; POLY_MUL] THEN
    REAL_ARITH_TAC) in
  ONCE_REWRITE_TAC[GSYM lemma1] THEN
  REWRITE_TAC[lemma2; POLY_ENTIRE] THEN
  REWRITE_TAC[lemma1]);;

let POLY_EXP_EQ_0 = prove
 (`!p n. (poly (p exp n) = poly []) <=> (poly p = poly []) /\ ~(n = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; poly] THEN
  REWRITE_TAC[LEFT_AND_FORALL_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[poly_exp; poly; REAL_MUL_RZERO; REAL_ADD_RID;
    REAL_OF_NUM_EQ; ARITH; NOT_SUC] THEN
  ASM_REWRITE_TAC[POLY_MUL; poly; REAL_ENTIRE] THEN
  CONV_TAC TAUT);;

let POLY_PRIME_EQ_0 = prove
 (`!a. ~(poly [a ; &1] = poly [])`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; poly] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 - a`) THEN
  REAL_ARITH_TAC);;

let POLY_EXP_PRIME_EQ_0 = prove
 (`!a n. ~(poly ([a ; &1] exp n) = poly [])`,
  MESON_TAC[POLY_EXP_EQ_0; POLY_PRIME_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Can also prove a more "constructive" notion of polynomial being trivial.  *)
(* ------------------------------------------------------------------------- *)

let POLY_ZERO_LEMMA = prove
 (`!h t. (poly (CONS h t) = poly []) ==> (h = &0) /\ (poly t = poly [])`,
  let lemma = REWRITE_RULE[FUN_EQ_THM; poly] POLY_ROOTS_FINITE in
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; poly] THEN
  ASM_CASES_TAC `h = &0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[REAL_ADD_LID];
    DISCH_THEN(MP_TAC o SPEC `&0`) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
  CONV_TAC CONTRAPOS_CONV THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[lemma]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (X_CHOOSE_TAC `i:num->real`)) THEN
  MP_TAC(SPECL [`i:num->real`; `N:num`; `\x. poly t x = &0`] FINITE_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  DISCH_THEN(MP_TAC o SPEC `abs(a) + &1`) THEN
  REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP (ASSUME `!x. (poly t x = &0) ==> x < a`)) THEN
    REAL_ARITH_TAC]);;

let POLY_ZERO = prove
 (`!p. (poly p = poly []) <=> ALL (\c. c = &0) p`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP POLY_ZERO_LEMMA) THEN ASM_REWRITE_TAC[];
    POP_ASSUM(SUBST1_TAC o SYM) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; poly] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Useful triviality.                                                        *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_AUX_ISZERO = prove
 (`!p n. ALL (\c. c = &0) (poly_diff_aux (SUC n) p) <=>
         ALL (\c. c = &0) p`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC
   [ALL; poly_diff_aux; REAL_ENTIRE; REAL_OF_NUM_EQ; NOT_SUC]);;


let POLY_DIFF_ISZERO = prove
 (`!p. (poly (diff p) = poly []) ==> ?h. poly p = poly [h]`,
  REWRITE_TAC[POLY_ZERO] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[POLY_DIFF_CLAUSES; ALL] THENL
   [EXISTS_TAC `&0` THEN REWRITE_TAC[FUN_EQ_THM; poly] THEN REAL_ARITH_TAC;
    REWRITE_TAC[num_CONV `1`; POLY_DIFF_AUX_ISZERO] THEN
    REWRITE_TAC[GSYM POLY_ZERO] THEN DISCH_TAC THEN
    EXISTS_TAC `h:real` THEN ASM_REWRITE_TAC[poly; FUN_EQ_THM]]);;

let POLY_DIFF_ZERO = prove
 (`!p. (poly p = poly []) ==> (poly (diff p) = poly [])`,
  REWRITE_TAC[POLY_ZERO] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff; NOT_CONS_NIL] THEN
  REWRITE_TAC[ALL; TL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`1`,`n:num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`t:real list`,`t:real list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; poly_diff_aux] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let POLY_DIFF_WELLDEF = prove
 (`!p q. (poly p = poly q) ==> (poly (diff p) = poly (diff q))`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `p ++ neg(q)` POLY_DIFF_ZERO) THEN
  REWRITE_TAC[FUN_EQ_THM; POLY_DIFF_ADD; POLY_DIFF_NEG; POLY_ADD] THEN
  ASM_REWRITE_TAC[POLY_NEG; poly; REAL_ARITH `a + --a = &0`] THEN
  REWRITE_TAC[REAL_ARITH `(a + --b = &0) <=> (a = b)`]);;

(* ------------------------------------------------------------------------- *)
(* Basics of divisibility.                                                   *)
(* ------------------------------------------------------------------------- *)

let divides = new_definition
  `p1 divides p2 <=> ?q. poly p2 = poly (p1 ** q)`;;

let POLY_PRIMES = prove
 (`!a p q. [a; &1] divides (p ** q) <=>
          [a; &1] divides p \/ [a; &1] divides q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides; POLY_MUL; FUN_EQ_THM; poly] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real list` (MP_TAC o SPEC `--a`)) THEN
    REWRITE_TAC[REAL_ENTIRE; GSYM real_sub; REAL_SUB_REFL; REAL_MUL_LZERO] THEN
    DISCH_THEN DISJ_CASES_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    (POP_ASSUM(MP_TAC o REWRITE_RULE[POLY_LINEAR_DIVIDES]) THEN
     REWRITE_TAC[REAL_NEG_NEG] THEN
     DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `s:real list` SUBST_ALL_TAC)) THENL
      [EXISTS_TAC `[]:real list` THEN REWRITE_TAC[poly; REAL_MUL_RZERO];
       EXISTS_TAC `s:real list` THEN GEN_TAC THEN
       REWRITE_TAC[POLY_MUL; poly] THEN REAL_ARITH_TAC]);
    DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_TAC `s:real list`)) THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `s ** q`; EXISTS_TAC `p ** s`] THEN
    GEN_TAC THEN REWRITE_TAC[POLY_MUL] THEN REAL_ARITH_TAC]);;

let POLY_DIVIDES_REFL = prove
 (`!p. p divides p`,
  GEN_TAC THEN REWRITE_TAC[divides] THEN EXISTS_TAC `[&1]` THEN
  REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly] THEN REAL_ARITH_TAC);;

let POLY_DIVIDES_TRANS = prove
 (`!p q r. p divides q /\ q divides r ==> p divides r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real list` ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real list` ASSUME_TAC) THEN
  EXISTS_TAC `t ** s` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; POLY_MUL; REAL_MUL_ASSOC]);;

let POLY_DIVIDES_EXP = prove
 (`!p m n. m <= n ==> (p exp m) divides (p exp n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; POLY_DIVIDES_REFL] THEN
  MATCH_MP_TAC POLY_DIVIDES_TRANS THEN
  EXISTS_TAC `p exp (m + d)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[divides] THEN EXISTS_TAC `p:real list` THEN
  REWRITE_TAC[poly_exp; FUN_EQ_THM; POLY_MUL] THEN
  REAL_ARITH_TAC);;

let POLY_EXP_DIVIDES = prove
 (`!p q m n. (p exp n) divides q /\ m <= n ==> (p exp m) divides q`,
  MESON_TAC[POLY_DIVIDES_TRANS; POLY_DIVIDES_EXP]);;

let POLY_DIVIDES_ADD = prove
 (`!p q r. p divides q /\ p divides r ==> p divides (q ++ r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real list` ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real list` ASSUME_TAC) THEN
  EXISTS_TAC `t ++ s` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; POLY_ADD; POLY_MUL] THEN
  REAL_ARITH_TAC);;

let POLY_DIVIDES_SUB = prove
 (`!p q r. p divides q /\ p divides (q ++ r) ==> p divides r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real list` ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real list` ASSUME_TAC) THEN
  EXISTS_TAC `s ++ neg(t)` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[FUN_EQ_THM; POLY_ADD; POLY_MUL; POLY_NEG] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RNEG] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let POLY_DIVIDES_SUB2 = prove
 (`!p q r. p divides r /\ p divides (q ++ r) ==> p divides q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_DIVIDES_SUB THEN
  EXISTS_TAC `r:real list` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p divides (q ++ r)` THEN
  REWRITE_TAC[divides; POLY_ADD; FUN_EQ_THM; POLY_MUL] THEN
  DISCH_THEN(X_CHOOSE_TAC `s:real list`) THEN
  EXISTS_TAC `s:real list` THEN
  X_GEN_TAC `x:real` THEN POP_ASSUM(MP_TAC o SPEC `x:real`) THEN
  REAL_ARITH_TAC);;

let POLY_DIVIDES_ZERO = prove
 (`!p q. (poly p = poly []) ==> q divides p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[divides] THEN
  EXISTS_TAC `[]:real list` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly; REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* At last, we can consider the order of a root.                             *)
(* ------------------------------------------------------------------------- *)

let POLY_ORDER_EXISTS = prove
 (`!a d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
             ==> ?n. ([--a; &1] exp n) divides p /\
                     ~(([--a; &1] exp (SUC n)) divides p)`,
  GEN_TAC THEN
  (STRIP_ASSUME_TAC o prove_recursive_functions_exist num_RECURSION)
    `(!p q. mulexp 0 p q = q) /\
     (!p q n. mulexp (SUC n) p q = p ** (mulexp n p q))` THEN
  SUBGOAL_THEN
   `!d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
           ==> ?n q. (p = mulexp (n:num) [--a; &1] q) /\
                     ~(poly q a = &0)`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[LENGTH_EQ_NIL] THEN MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `p:real list` THEN
    ASM_CASES_TAC `poly p a = &0` THENL
     [STRIP_TAC THEN UNDISCH_TAC `poly p a = &0` THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[POLY_LINEAR_DIVIDES]) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real list` SUBST_ALL_TAC) THEN
      UNDISCH_TAC
       `!p. (LENGTH p = d) /\ ~(poly p = poly [])
            ==> ?n q. (p = mulexp (n:num) [--a; &1] q) /\
                      ~(poly q a = &0)` THEN
      DISCH_THEN(MP_TAC o SPEC `q:real list`) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[POLY_LENGTH_MUL; POLY_ENTIRE;
        DE_MORGAN_THM; SUC_INJ]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num`
       (X_CHOOSE_THEN `s:real list` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `SUC n` THEN EXISTS_TAC `s:real list` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC `0` THEN EXISTS_TAC `p:real list` THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num`
       (X_CHOOSE_THEN `s:real list` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[divides] THEN CONJ_TAC THENL
     [EXISTS_TAC `s:real list` THEN
      SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC[poly_exp; FUN_EQ_THM; POLY_MUL; poly] THEN
      REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `r:real list` MP_TAC) THEN
      SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `~(poly s a = &0)` THEN CONV_TAC CONTRAPOS_CONV THEN
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[poly; poly_exp; POLY_MUL] THEN REAL_ARITH_TAC;
        REWRITE_TAC[] THEN ONCE_ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[poly_exp] THEN
        REWRITE_TAC[GSYM POLY_MUL_ASSOC; POLY_MUL_LCANCEL] THEN
        REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM] THEN
          DISCH_THEN(MP_TAC o SPEC `a + &1`) THEN
          REWRITE_TAC[poly] THEN REAL_ARITH_TAC;
          DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[]]]]]);;

let POLY_ORDER = prove
 (`!p a. ~(poly p = poly [])
         ==> ?!n. ([--a; &1] exp n) divides p /\
                      ~(([--a; &1] exp (SUC n)) divides p)`,
  MESON_TAC[POLY_ORDER_EXISTS; POLY_EXP_DIVIDES; LE_SUC_LT; LT_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Definition of order.                                                      *)
(* ------------------------------------------------------------------------- *)

let order = new_definition
  `order a p = @n. ([--a; &1] exp n) divides p /\
                   ~(([--a; &1] exp (SUC n)) divides p)`;;

let ORDER = prove
 (`!p a n. ([--a; &1] exp n) divides p /\
           ~(([--a; &1] exp (SUC n)) divides p) <=>
           (n = order a p) /\
           ~(poly p = poly [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[order] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~(poly p = poly [])` ASSUME_TAC THENL
     [FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[divides] THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `[]:real list` THEN
      REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly; REAL_MUL_RZERO];
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[]];
    ONCE_ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV] THEN
  ASM_MESON_TAC[POLY_ORDER]);;

let ORDER_THM = prove
 (`!p a. ~(poly p = poly [])
         ==> ([--a; &1] exp (order a p)) divides p /\
             ~(([--a; &1] exp (SUC(order a p))) divides p)`,
  MESON_TAC[ORDER]);;

let ORDER_UNIQUE = prove
 (`!p a n. ~(poly p = poly []) /\
           ([--a; &1] exp n) divides p /\
           ~(([--a; &1] exp (SUC n)) divides p)
           ==> (n = order a p)`,
  MESON_TAC[ORDER]);;

let ORDER_POLY = prove
 (`!p q a. (poly p = poly q) ==> (order a p = order a q)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[order; divides; FUN_EQ_THM; POLY_MUL]);;

let ORDER_ROOT = prove
 (`!p a. (poly p a = &0) <=> (poly p = poly []) \/ ~(order a p = 0)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `poly p = poly []` THEN
  ASM_REWRITE_TAC[poly] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o REWRITE_RULE[POLY_LINEAR_DIVIDES]) THEN
    ASM_CASES_TAC `p:real list = []` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real list` SUBST_ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `a:real` o MATCH_MP ORDER_THM) THEN
    ASM_REWRITE_TAC[poly_exp; DE_MORGAN_THM] THEN DISJ2_TAC THEN
    REWRITE_TAC[divides] THEN EXISTS_TAC `q:real list` THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `a:real` o MATCH_MP ORDER_THM) THEN
    UNDISCH_TAC `~(order a p = 0)` THEN
    SPEC_TAC(`order a p`,`n:num`) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[poly_exp; NOT_SUC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real list` SUBST1_TAC) THEN
    REWRITE_TAC[POLY_MUL; poly] THEN REAL_ARITH_TAC]);;

let ORDER_DIVIDES = prove
 (`!p a n. ([--a; &1] exp n) divides p <=>
           (poly p = poly []) \/ n <= order a p`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `poly p = poly []` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[divides] THEN EXISTS_TAC `[]:real list` THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; poly; REAL_MUL_RZERO];
    ASM_MESON_TAC[ORDER_THM; POLY_EXP_DIVIDES; NOT_LE; LE_SUC_LT]]);;

let ORDER_DECOMP = prove
 (`!p a. ~(poly p = poly [])
         ==> ?q. (poly p = poly (([--a; &1] exp (order a p)) ** q)) /\
                 ~([--a; &1] divides q)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ORDER_THM) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC o SPEC `a:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `q:real list` o REWRITE_RULE[divides]) THEN
  EXISTS_TAC `q:real list` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `r: real list` o REWRITE_RULE[divides]) THEN
  UNDISCH_TAC `~([-- a; &1] exp SUC (order a p) divides p)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[divides] THEN
  EXISTS_TAC `r:real list` THEN
  ASM_REWRITE_TAC[POLY_MUL; FUN_EQ_THM; poly_exp] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Important composition properties of orders.                               *)
(* ------------------------------------------------------------------------- *)

let ORDER_MUL = prove
 (`!a p q. ~(poly (p ** q) = poly []) ==>
           (order a (p ** q) = order a p + order a q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[POLY_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(order a p + order a q = order a (p ** q)) /\
                ~(poly (p ** q) = poly [])`
  MP_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REWRITE_TAC[GSYM ORDER] THEN CONJ_TAC THENL
   [MP_TAC(CONJUNCT1 (SPEC `a:real`
      (MATCH_MP ORDER_THM (ASSUME `~(poly p = poly [])`)))) THEN
    DISCH_THEN(X_CHOOSE_TAC `r: real list` o REWRITE_RULE[divides]) THEN
    MP_TAC(CONJUNCT1 (SPEC `a:real`
      (MATCH_MP ORDER_THM (ASSUME `~(poly q = poly [])`)))) THEN
    DISCH_THEN(X_CHOOSE_TAC `s: real list` o REWRITE_RULE[divides]) THEN
    REWRITE_TAC[divides; FUN_EQ_THM] THEN EXISTS_TAC `s ** r` THEN
    ASM_REWRITE_TAC[POLY_MUL; POLY_EXP_ADD] THEN REAL_ARITH_TAC;
    X_CHOOSE_THEN `r: real list` STRIP_ASSUME_TAC
    (SPEC `a:real` (MATCH_MP ORDER_DECOMP (ASSUME `~(poly p = poly [])`))) THEN
    X_CHOOSE_THEN `s: real list` STRIP_ASSUME_TAC
    (SPEC `a:real` (MATCH_MP ORDER_DECOMP (ASSUME `~(poly q = poly [])`))) THEN
    ASM_REWRITE_TAC[divides; FUN_EQ_THM; POLY_EXP_ADD; POLY_MUL; poly_exp] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real list` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `[--a; &1] divides (r ** s)` MP_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[POLY_PRIMES]] THEN
    REWRITE_TAC[divides] THEN EXISTS_TAC `t:real list` THEN
    SUBGOAL_THEN `poly ([-- a; &1] exp (order a p) ** r ** s) =
                  poly ([-- a; &1] exp (order a p) ** ([-- a; &1] ** t))`
    MP_TAC THENL
     [ALL_TAC; MESON_TAC[POLY_MUL_LCANCEL; POLY_EXP_PRIME_EQ_0]] THEN
    SUBGOAL_THEN `poly ([-- a; &1] exp (order a q) **
                        [-- a; &1] exp (order a p) ** r ** s) =
                  poly ([-- a; &1] exp (order a q) **
                        [-- a; &1] exp (order a p) **
                        [-- a; &1] ** t)`
    MP_TAC THENL
     [ALL_TAC; MESON_TAC[POLY_MUL_LCANCEL; POLY_EXP_PRIME_EQ_0]] THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; POLY_ADD] THEN
    FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
    REWRITE_TAC[REAL_MUL_AC]]);;

let ORDER_DIFF = prove
 (`!p a. ~(poly (diff p) = poly []) /\
         ~(order a p = 0)
         ==> (order a p = SUC (order a (diff p)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `~(poly p = poly [])` MP_TAC THENL
   [ASM_MESON_TAC[POLY_DIFF_ZERO]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real list` MP_TAC o
    SPEC `a:real` o MATCH_MP ORDER_DECOMP) THEN
  SPEC_TAC(`order a p`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; SUC_INJ] THEN
  STRIP_TAC THEN MATCH_MP_TAC ORDER_UNIQUE THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!r. r divides (diff p) <=>
                    r divides (diff ([-- a; &1] exp SUC n ** q))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[divides] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP POLY_DIFF_WELLDEF th]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[divides; FUN_EQ_THM] THEN
    EXISTS_TAC `[--a; &1] ** (diff q) ++ &(SUC n) ## q` THEN
    REWRITE_TAC[POLY_DIFF_MUL; POLY_DIFF_EXP_PRIME;
      POLY_ADD; POLY_MUL; POLY_CMUL] THEN
    REWRITE_TAC[poly_exp; POLY_MUL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[FUN_EQ_THM; divides; POLY_DIFF_MUL; POLY_DIFF_EXP_PRIME;
      POLY_ADD; POLY_MUL; POLY_CMUL] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real list` ASSUME_TAC) THEN
    UNDISCH_TAC `~([-- a; &1] divides q)` THEN
    REWRITE_TAC[divides] THEN
    EXISTS_TAC `inv(&(SUC n)) ## (r ++ neg(diff q))` THEN
    SUBGOAL_THEN
        `poly ([--a; &1] exp n ** q) =
         poly ([--a; &1] exp n ** ([-- a; &1] ** (inv (&(SUC n)) ##
                                   (r ++ neg (diff q)))))`
    MP_TAC THENL
     [ALL_TAC; MESON_TAC[POLY_MUL_LCANCEL; POLY_EXP_PRIME_EQ_0]] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
    SUBGOAL_THEN
        `!a b. (&(SUC n) * a = &(SUC n) * b) ==> (a = b)`
    MATCH_MP_TAC THENL
     [REWRITE_TAC[REAL_EQ_MUL_LCANCEL; REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
    REWRITE_TAC[POLY_MUL; POLY_CMUL] THEN
    SUBGOAL_THEN `!a b c. &(SUC n) * a * b * inv(&(SUC n)) * c =
                          a * b * c`
    (fun th -> REWRITE_TAC[th]) THENL
      [REPEAT GEN_TAC THEN
       GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
       REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
       AP_TERM_TAC THEN
       GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
       GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
       REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
       MATCH_MP_TAC REAL_MUL_RINV THEN
       REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real`) THEN
    REWRITE_TAC[poly_exp; POLY_MUL; POLY_ADD; POLY_NEG] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Now justify the standard squarefree decomposition, i.e. f / gcd(f,f').    *)
(* ------------------------------------------------------------------------- *)

let POLY_SQUAREFREE_DECOMP_ORDER = prove
 (`!p q d e r s.
        ~(poly (diff p) = poly []) /\
        (poly p = poly (q ** d)) /\
        (poly (diff p) = poly (e ** d)) /\
        (poly d = poly (r ** p ++ s ** diff p))
        ==> !a. order a q = (if order a p = 0 then 0 else 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `order a p = order a q + order a d` MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `order a (q ** d)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ORDER_POLY THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ORDER_MUL THEN
      FIRST_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      ASM_MESON_TAC[POLY_DIFF_ZERO]]; ALL_TAC] THEN
  ASM_CASES_TAC `order a p = 0` THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `order a (diff p) =
                order a e + order a d` MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `order a (e ** d)` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ORDER_POLY]; ASM_MESON_TAC[ORDER_MUL]]; ALL_TAC] THEN
  SUBGOAL_THEN `~(poly p = poly [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[POLY_DIFF_ZERO]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:real list`; `a:real`] ORDER_DIFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(AP_TERM `PRE` th)) THEN
  REWRITE_TAC[PRE] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `order a (diff p) <= order a d` MP_TAC THENL
   [SUBGOAL_THEN `([--a; &1] exp (order a (diff p))) divides d`
    MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[POLY_ENTIRE; ORDER_DIVIDES]] THEN
    SUBGOAL_THEN
      `([--a; &1] exp (order a (diff p))) divides p /\
       ([--a; &1] exp (order a (diff p))) divides (diff p)`
    MP_TAC THENL
     [REWRITE_TAC[ORDER_DIVIDES; LE_REFL] THEN DISJ2_TAC THEN
      REWRITE_TAC[ASSUME `order a (diff p) = PRE (order a p)`] THEN
      ARITH_TAC;
      DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN REWRITE_TAC[divides] THEN
      REWRITE_TAC[ASSUME `poly d = poly (r ** p ++ s ** diff p)`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real list` ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real list` ASSUME_TAC) THEN
      EXISTS_TAC `r ** g ++ s ** f` THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[FUN_EQ_THM; POLY_MUL; POLY_ADD] THEN ARITH_TAC];
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Define being "squarefree" --- NB with respect to real roots only.         *)
(* ------------------------------------------------------------------------- *)

let rsquarefree = new_definition
  `rsquarefree p <=> ~(poly p = poly []) /\
                     !a. (order a p = 0) \/ (order a p = 1)`;;

(* ------------------------------------------------------------------------- *)
(* Standard squarefree criterion and rephasing of squarefree decomposition.  *)
(* ------------------------------------------------------------------------- *)

let RSQUAREFREE_ROOTS = prove
 (`!p. rsquarefree p <=> !a. ~((poly p a = &0) /\ (poly (diff p) a = &0))`,
  GEN_TAC THEN REWRITE_TAC[rsquarefree] THEN
  ASM_CASES_TAC `poly p = poly []` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP POLY_DIFF_ZERO) THEN
    ASM_REWRITE_TAC[poly; NOT_FORALL_THM];
    ASM_CASES_TAC `poly(diff p) = poly []` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(X_CHOOSE_THEN `h:real` MP_TAC o
        MATCH_MP POLY_DIFF_ISZERO) THEN
      DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ORDER_POLY th]) THEN
      UNDISCH_TAC `~(poly p = poly [])` THEN ASM_REWRITE_TAC[poly] THEN
      REWRITE_TAC[FUN_EQ_THM; poly; REAL_MUL_RZERO; REAL_ADD_RID] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `a:real` THEN DISJ1_TAC THEN
      MP_TAC(SPECL [`[h:real]`; `a:real`] ORDER_ROOT) THEN
      ASM_REWRITE_TAC[FUN_EQ_THM; poly; REAL_MUL_RZERO; REAL_ADD_RID];
      ASM_REWRITE_TAC[ORDER_ROOT; DE_MORGAN_THM; num_CONV `1`] THEN
      ASM_MESON_TAC[ORDER_DIFF; SUC_INJ]]]);;

let RSQUAREFREE_DECOMP = prove
 (`!p a. rsquarefree p /\ (poly p a = &0)
         ==> ?q. (poly p = poly ([--a; &1] ** q)) /\
                 ~(poly q a = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rsquarefree] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORDER_DECOMP) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real list` MP_TAC o SPEC `a:real`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ORDER_ROOT]) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o SPEC `a:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  EXISTS_TAC `q:real list` THEN CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; POLY_MUL] THEN GEN_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [num_CONV `1`] THEN
    REWRITE_TAC[poly_exp; POLY_MUL] THEN
    REWRITE_TAC[poly] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN UNDISCH_TAC `~([-- a; &1] divides q)` THEN
    REWRITE_TAC[divides] THEN
    UNDISCH_TAC `poly q a = &0` THEN
    GEN_REWRITE_TAC LAND_CONV [POLY_LINEAR_DIVIDES] THEN
    ASM_CASES_TAC `q:real list = []` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `[] : real list` THEN REWRITE_TAC[FUN_EQ_THM] THEN
      REWRITE_TAC[POLY_MUL; poly; REAL_MUL_RZERO];
      MESON_TAC[]]]);;

let POLY_SQUAREFREE_DECOMP = prove
 (`!p q d e r s.
        ~(poly (diff p) = poly []) /\
        (poly p = poly (q ** d)) /\
        (poly (diff p) = poly (e ** d)) /\
        (poly d = poly (r ** p ++ s ** diff p))
        ==> rsquarefree q /\ (!a. (poly q a = &0) <=> (poly p a = &0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC th THEN
    ASSUME_TAC(MATCH_MP POLY_SQUAREFREE_DECOMP_ORDER th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `~(poly p = poly [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[POLY_DIFF_ZERO]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `~(poly p = poly [])` THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(fun th -> ASM_REWRITE_TAC[] THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[POLY_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC `poly p = poly (q ** d)` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[rsquarefree; ORDER_ROOT] THEN
  CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Normalization of a polynomial.                                            *)
(* ------------------------------------------------------------------------- *)

let normalize = new_recursive_definition list_RECURSION
  `(normalize [] = []) /\
   (normalize (CONS h t) =
      if normalize t = [] then if h = &0 then [] else [h]
                          else CONS h (normalize t))`;;

let POLY_NORMALIZE = prove
 (`!p. poly (normalize p) = poly p`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[normalize; poly] THEN
  ASM_CASES_TAC `h = &0` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[poly; FUN_EQ_THM] THEN
  UNDISCH_TAC `poly (normalize t) = poly t` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[poly] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* The degree of a polynomial.                                               *)
(* ------------------------------------------------------------------------- *)

let degree = new_definition
  `degree p = PRE(LENGTH(normalize p))`;;

let DEGREE_ZERO = prove
 (`!p. (poly p = poly []) ==> (degree p = 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[degree] THEN
  SUBGOAL_THEN `normalize p = []` SUBST1_TAC THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC(`p:real list`,`p:real list`) THEN
    REWRITE_TAC[POLY_ZERO] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[normalize; ALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `normalize t = []` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LENGTH; PRE]]);;

(* ------------------------------------------------------------------------- *)
(* Tidier versions of finiteness of roots.                                   *)
(* ------------------------------------------------------------------------- *)

let POLY_ROOTS_FINITE_SET = prove
 (`!p. ~(poly p = poly []) ==> FINITE { x | poly p x = &0}`,
  GEN_TAC THEN REWRITE_TAC[POLY_ROOTS_FINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num->real` ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:real | ?n:num. n < N /\ (x = i n)}` THEN
  CONJ_TAC THENL
   [SPEC_TAC(`N:num`,`N:num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    INDUCT_TAC THENL
     [SUBGOAL_THEN `{x:real | ?n. n < 0 /\ (x = i n)} = {}`
      (fun th -> REWRITE_TAC[th; FINITE_RULES]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; LT];
      SUBGOAL_THEN `{x:real | ?n. n < SUC N /\ (x = i n)} =
                    (i N) INSERT {x:real | ?n. n < N /\ (x = i n)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; LT] THEN MESON_TAC[];
        MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN ASM_REWRITE_TAC[]]];
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Crude bound for polynomial.                                               *)
(* ------------------------------------------------------------------------- *)

let POLY_MONO = prove
 (`!x k p. abs(x) <= k ==> abs(poly p x) <= poly (MAP abs p) k`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly; REAL_LE_REFL; MAP; REAL_ABS_0] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(h) + abs(x * poly t x)` THEN
  REWRITE_TAC[REAL_ABS_TRIANGLE; REAL_LE_LADD] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

(* ------------------------------------------------------------------------- *)
(* Conversions to perform operations if coefficients are rational constants. *)
(* ------------------------------------------------------------------------- *)

let POLY_DIFF_CONV =
  let aux_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 poly_diff_aux]
  and aux_conv1 = GEN_REWRITE_CONV I [CONJUNCT2 poly_diff_aux]
  and diff_conv0 = GEN_REWRITE_CONV I (butlast (CONJUNCTS POLY_DIFF_CLAUSES))
  and diff_conv1 = GEN_REWRITE_CONV I [last (CONJUNCTS POLY_DIFF_CLAUSES)] in
  let rec POLY_DIFF_AUX_CONV tm =
   (aux_conv0 ORELSEC
    (aux_conv1 THENC
     LAND_CONV REAL_RAT_MUL_CONV THENC
     RAND_CONV (LAND_CONV NUM_SUC_CONV THENC POLY_DIFF_AUX_CONV))) tm in
  diff_conv0 ORELSEC
  (diff_conv1 THENC POLY_DIFF_AUX_CONV);;

let POLY_CMUL_CONV =
  let cmul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 poly_cmul]
  and cmul_conv1 = GEN_REWRITE_CONV I [CONJUNCT2 poly_cmul] in
  let rec POLY_CMUL_CONV tm =
   (cmul_conv0 ORELSEC
    (cmul_conv1 THENC
     LAND_CONV REAL_RAT_MUL_CONV THENC
     RAND_CONV POLY_CMUL_CONV)) tm in
  POLY_CMUL_CONV;;

let POLY_ADD_CONV =
  let add_conv0 = GEN_REWRITE_CONV I (butlast (CONJUNCTS POLY_ADD_CLAUSES))
  and add_conv1 = GEN_REWRITE_CONV I [last (CONJUNCTS POLY_ADD_CLAUSES)] in
  let rec POLY_ADD_CONV tm =
   (add_conv0 ORELSEC
    (add_conv1 THENC
     LAND_CONV REAL_RAT_ADD_CONV THENC
     RAND_CONV POLY_ADD_CONV)) tm in
  POLY_ADD_CONV;;

let POLY_MUL_CONV =
  let mul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 POLY_MUL_CLAUSES]
  and mul_conv1 = GEN_REWRITE_CONV I [CONJUNCT1(CONJUNCT2 POLY_MUL_CLAUSES)]
  and mul_conv2 = GEN_REWRITE_CONV I [CONJUNCT2(CONJUNCT2 POLY_MUL_CLAUSES)] in
  let rec POLY_MUL_CONV tm =
   (mul_conv0 ORELSEC
    (mul_conv1 THENC POLY_CMUL_CONV) ORELSEC
    (mul_conv2 THENC
     LAND_CONV POLY_CMUL_CONV THENC
     RAND_CONV(RAND_CONV POLY_MUL_CONV) THENC
     POLY_ADD_CONV)) tm in
  POLY_MUL_CONV;;

let POLY_NORMALIZE_CONV =
  let pth = prove
   (`normalize (CONS h t) =
      (\n. if n = [] then if h = &0 then [] else [h] else CONS h n)
      (normalize t)`,
    REWRITE_TAC[normalize]) in
  let norm_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 normalize]
  and norm_conv1 = GEN_REWRITE_CONV I [pth]
  and norm_conv2 = GEN_REWRITE_CONV DEPTH_CONV
   [COND_CLAUSES; NOT_CONS_NIL; EQT_INTRO(SPEC_ALL EQ_REFL)] in
  let rec POLY_NORMALIZE_CONV tm =
   (norm_conv0 ORELSEC
    (norm_conv1 THENC
     RAND_CONV POLY_NORMALIZE_CONV THENC
     BETA_CONV THENC
     RATOR_CONV(RAND_CONV(RATOR_CONV(LAND_CONV REAL_RAT_EQ_CONV))) THENC
     norm_conv2)) tm in
  POLY_NORMALIZE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Now we're finished with polynomials...                                    *)
(* ------------------------------------------------------------------------- *)

do_list reduce_interface
 ["divides",`poly_divides:real list->real list->bool`;
  "exp",`poly_exp:real list -> num -> real list`;
  "diff",`poly_diff:real list->real list`];;

unparse_as_infix "exp";;
