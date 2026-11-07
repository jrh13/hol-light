(* ========================================================================= *)
(* Class number two: the cases of the discriminant, the genus character and  *)
(* the eighteen known discriminants.                                         *)
(*                                                                           *)
(* Purpose: the elementary part of the class number two problem (Baker,      *)
(* Transcendental Number Theory, Ch. 5, sec. 5) for the class number of      *)
(* Gauss, form_classno D, the number of reduced primitive forms of           *)
(* discriminant D. CN_FORMS_TWO_CASES: for squarefree d with                 *)
(* form_classno (qdisc d) = 2, either d = p q with primes p = 1, q = 3 mod 4 *)
(* and d = 3 mod 8 or d = 15, or d is a prime = 1 mod 4, or d = 2 p with an  *)
(* odd prime p. CN_GENUS_CHARACTER: in the first case (q | p) = -1, i.e.     *)
(* qchar p q = -1 (needed for the representation numbers of the two forms).  *)
(* CLASS_NUMBER_TWO_EXAMPLES: the eighteen values of d with class number     *)
(* two.                                                                      *)
(*                                                                           *)
(* Method: genus theory by witnesses, as CLASSNO_ONE_CASES of                *)
(* Baker/classno_forms.ml. If form_classno D = 2, every reduced primitive    *)
(* form of discriminant D is one of two given distinct ones                  *)
(* (CNF_CLASSNO_TWO_OTHER), so three distinct reduced primitive forms        *)
(* exclude a case (CNF_CLASSNO_THREE). The witnesses: the forms              *)
(* (2,1,(d+1)/8) and (2,-1,(d+1)/8) for d = 7 mod 8, d > 15 (CNF_MOD8_7);    *)
(* for a prime d = 3 mod 4, d > 3, the second reduced form (a,b,c) is not    *)
(* ambiguous (b = 0, abs b = a and a = c force the principal form or d = 3), *)
(* so (a,-b,c) is a third one (CNF_PRIME_MOD4_3); a squarefree d = 3 mod 4   *)
(* with at least three prime factors has two factorisations d = m n,         *)
(* 1 < m < n, with different m (CNF_TWO_FACTORIZATIONS), and the ambiguous   *)
(* forms determine m (QFORM_AMBIGUOUS_WITNESS of Baker/classno_forms.ml,     *)
(* CNF_COMPOSITE_MOD4_3); for the discriminant -4d the forms (m,0,n) for     *)
(* composite d = m n = 1 mod 4 (CNF_MOD4_1) and (m,0,2n) for d = 2 m n, m n  *)
(* odd (CNF_MOD4_2). The genus character: reduction does not change the set  *)
(* of represented integers (QFORM_REDUCE_FORM); the values prime to p of the *)
(* principal form f are residues mod p, as 4 f = (2x + y)^2 + d y^2          *)
(* (CNF_PRIN_VALUE_RESIDUE), and those of F = (q,q,(p+q)/4) have the         *)
(* character (q | p), as 4 q F = (2qx + qy)^2 + d y^2                        *)
(* (CNF_SECOND_VALUE_RESIDUE); f does not represent q (CNF_PRIN_NOT_PRIME),  *)
(* so the reduction G of F is the second form. A prime r = 1 mod 4 that is a *)
(* non-residue mod p and mod q (Dirichlet and the Chinese remainder theorem, *)
(* CNF_AUX_PRIME) has -d a square mod 4 r (Jacobi reciprocity, CNF_SPLIT_B); *)
(* a reduced form representing r (QFORM_REPRESENTED_REDUCED) is f or G: f is *)
(* excluded by (r | p) = -1, and G gives (q | p) = (r | p). The eighteen:    *)
(* the evaluator FORM_CLASSNO_CONV.                                          *)
(*                                                                           *)
(* Main results: CN_FORMS_TWO_CASES, CN_GENUS_CHARACTER,                     *)
(* CLASS_NUMBER_TWO_EXAMPLES; CNF_CLASSNO_TWO_OTHER, CNF_CLASSNO_THREE,      *)
(* CNF_AUX_PRIME; helper names CNF_*.                                        *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (qf_reduced, form_classno, qdisc, qform),     *)
(* Baker/classno_forms.ml (QF_FORMS_IN, CLASSNO_FORMS_FINITE,                *)
(* CLASSNO_PRINCIPAL_REDUCED, QF_PRIMITIVE_SQUAREFREE, QF_PRIMITIVE_BEZOUT,  *)
(* QF_REDUCED_BOUNDS, QFORM_REDUCE_FORM,                                     *)
(* QFORM_REPRESENTED_REDUCED, QFORM_AMBIGUOUS_WITNESS, FORM_CLASSNO_CONV,    *)
(* CLASSNO_FORMS_MOD4_CASES, CLASSNO_FORMS_MOD8_CASES,                       *)
(* CLASSNO_FORMS_PRODUCT_MOD4, CLASSNO_FORMS_NONPRIME,                       *)
(* CLASSNO_FORMS_MOD_CASES_TAC, CLASSNO_NINE), Baker/classno_chardefs.ml     *)
(* (qchar), Baker/classno_rep.ml (CLASSNO_REP_DMOD4, CLASSNO_REP_DMOD4_ODD,  *)
(* CLASSNO_REP_SPLIT_B, CLASSNO_REP_INT_SQUARE); Library/jacobi.ml           *)
(* (JACOBI_RECIPROCITY, JACOBI_PRIME, JACOBI_EQ_1, JACOBI_MINUS1,            *)
(* JACOBI_LMUL, JACOBI_CONG), Library/primitive.ml                           *)
(* (QUADRATIC_NONRESIDUE_EXISTS), Library/pocklington.ml (squarefree,        *)
(* SQUAREFREE_MUL, CHINESE_REMAINDER_USUAL), 100/dirichlet.ml (DIRICHLET).   *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files), so that the file also  *)
(* loads alone.                                                              *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Baker/classno_rep.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Counting reduced forms when the class number is two.                   *)
(* ------------------------------------------------------------------------- *)

let CNF_CARD_2_CASES = prove
 (`!s:A->bool x y z.
        FINITE s /\ CARD s = 2 /\ x IN s /\ y IN s /\ z IN s /\ ~(x = y)
        ==> z = x \/ z = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:A->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` (X_CHOOSE_THEN `v:A`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY]) THEN
  ASM_MESON_TAC[]);;

let CNF_CARD_2_OTHER = prove
 (`!s:A->bool x. FINITE s /\ CARD s = 2 /\ x IN s ==> ?y. y IN s /\ ~(y = x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:A->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` (X_CHOOSE_THEN `v:A`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY]) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]);;

(* If form_classno D = 2, every reduced primitive form of discriminant D is  *)
(* one of two given distinct ones, and there is a second one besides any     *)
(* given one.                                                                *)

let CNF_CLASSNO_TWO_OTHER = prove
 (`!D a b c a' b' c' a'' b'' c''.
        form_classno D = 2 /\
        qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
        gcd(a,gcd(b,c)) = &1 /\
        qf_reduced a' b' c' /\ b' pow 2 - &4 * a' * c' = D /\
        gcd(a',gcd(b',c')) = &1 /\
        qf_reduced a'' b'' c'' /\ b'' pow 2 - &4 * a'' * c'' = D /\
        gcd(a'',gcd(b'',c'')) = &1 /\
        ~(a = a' /\ b = b' /\ c = c')
        ==> (a'' = a /\ b'' = b /\ c'' = c) \/
            (a'' = a' /\ b'' = b' /\ c'' = c')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{(a,b,c) | qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
                             gcd(a,gcd(b,c)) = &1}`;
                 `(a:int,b:int,c:int)`; `(a':int,b':int,c':int)`;
                 `(a'':int,b'':int,c'':int)`] CNF_CARD_2_CASES) THEN
  REWRITE_TAC[CLASSNO_FORMS_FINITE; QF_FORMS_IN; PAIR_EQ;
              GSYM form_classno] THEN
  ASM_REWRITE_TAC[]);;

let CNF_CLASSNO_TWO_SECOND = prove
 (`!D a b c.
        form_classno D = 2 /\
        qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
        gcd(a,gcd(b,c)) = &1
        ==> ?a' b' c'. qf_reduced a' b' c' /\
                       b' pow 2 - &4 * a' * c' = D /\
                       gcd(a',gcd(b',c')) = &1 /\
                       ~(a' = a /\ b' = b /\ c' = c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{(a,b,c) | qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
                             gcd(a,gcd(b,c)) = &1}`;
                 `(a:int,b:int,c:int)`] CNF_CARD_2_OTHER) THEN
  REWRITE_TAC[CLASSNO_FORMS_FINITE; QF_FORMS_IN; GSYM form_classno] THEN
  ASM_REWRITE_TAC[EXISTS_PAIR_THM; QF_FORMS_IN; PAIR_EQ; GSYM CONJ_ASSOC]);;

(* Three pairwise distinct reduced primitive forms exclude class number two  *)
(* (primitivity is automatic for the discriminant -d, d squarefree).         *)

let CNF_CLASSNO_THREE = prove
 (`!D a b c a' b' c' a'' b'' c''.
        qf_reduced a b c /\ b pow 2 - &4 * a * c = D /\
        gcd(a,gcd(b,c)) = &1 /\
        qf_reduced a' b' c' /\ b' pow 2 - &4 * a' * c' = D /\
        gcd(a',gcd(b',c')) = &1 /\
        qf_reduced a'' b'' c'' /\ b'' pow 2 - &4 * a'' * c'' = D /\
        gcd(a'',gcd(b'',c'')) = &1 /\
        ~(a = a' /\ b = b' /\ c = c') /\
        ~(a'' = a /\ b'' = b /\ c'' = c) /\
        ~(a'' = a' /\ b'' = b' /\ c'' = c')
        ==> ~(form_classno D = 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`D:int`; `a:int`; `b:int`; `c:int`; `a':int`; `b':int`;
                `c':int`; `a'':int`; `b'':int`; `c'':int`]
         CNF_CLASSNO_TWO_OTHER) THEN
  ASM_REWRITE_TAC[]);;

let CNF_CLASSNO_THREE_SQUAREFREE = prove
 (`!d a b c a' b' c' a'' b'' c''.
        squarefree d /\
        qf_reduced a b c /\ b pow 2 - &4 * a * c = --(&d) /\
        qf_reduced a' b' c' /\ b' pow 2 - &4 * a' * c' = --(&d) /\
        qf_reduced a'' b'' c'' /\ b'' pow 2 - &4 * a'' * c'' = --(&d) /\
        ~(a = a' /\ b = b' /\ c = c') /\
        ~(a'' = a /\ b'' = b /\ c'' = c) /\
        ~(a'' = a' /\ b'' = b' /\ c'' = c')
        ==> ~(form_classno(--(&d)) = 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CNF_CLASSNO_THREE THEN
  MAP_EVERY EXISTS_TAC [`a:int`; `b:int`; `c:int`; `a':int`; `b':int`;
                        `c':int`; `a'':int`; `b'':int`; `c'':int`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC QF_PRIMITIVE_SQUAREFREE THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. Witnesses for the discriminant -d, d = 3 mod 4.                        *)
(* ------------------------------------------------------------------------- *)

let CNF_INT_PRIME_FACTOR = prove
 (`!d x y:int. prime d /\ x * y = &d /\ &0 < x /\ &0 < y
               ==> x = &1 \/ y = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `y:int` INT_OF_NUM_EXISTS) THEN
  MP_TAC(SPEC `x:int` INT_OF_NUM_EXISTS) THEN
  ASM_SIMP_TAC[INT_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_MUL; INT_OF_NUM_EQ;
                              INT_OF_NUM_LT]) THEN
  REWRITE_TAC[INT_OF_NUM_EQ] THEN
  FIRST_ASSUM(MP_TAC o SPEC `m:num` o CONJUNCT2 o REWRITE_RULE[prime] o
    check (fun th -> concl th = `prime d`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[divides] THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  UNDISCH_TAC `m * n = d` THEN ASM_REWRITE_TAC[] THEN
  PURE_ONCE_REWRITE_TAC[ARITH_RULE `d * n = d <=> d * n = d * 1`] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[PRIME_IMP_NZ]);;

let CNF_DISC_B_NONZERO = prove
 (`!a b c:int d. b pow 2 - &4 * a * c = --(&d) /\ d MOD 4 = 3
                 ==> ~(b = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `4 divides d` MP_TAC THENL
   [REWRITE_TAC[num_divides; int_divides] THEN EXISTS_TAC `a * c:int` THEN
    UNDISCH_TAC `&0 pow 2 - &4 * a * c = --(&d:int)` THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[DIVIDES_MOD] THEN ARITH_TAC]);;

(* d = 7 mod 8, d > 15: the reduced forms (2,1,(d+1)/8) and (2,-1,(d+1)/8)   *)
(* besides the principal form.                                               *)

let CNF_MOD8_7 = prove
 (`!d. squarefree d /\ d MOD 8 = 7 /\ 15 < d
       ==> ~(form_classno(--(&d)) = 2)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `d MOD 4 = 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `d MOD 4 = (d MOD 8) MOD 4` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `8 = 4 * 2`; MOD_MOD];
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(SPEC `d:num` CLASSNO_PRINCIPAL_REDUCED) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`d:num`; `8`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `k = d DIV 8` THEN
  SUBGOAL_THEN `&d:int = &8 * &k + &7 /\ &2:int <= &k` MP_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
                INT_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`d = k * 8 + 7`; `15 < d`] THEN ARITH_TAC;
    STRIP_TAC] THEN
  MATCH_MP_TAC CNF_CLASSNO_THREE_SQUAREFREE THEN
  MAP_EVERY EXISTS_TAC [`&1:int`; `&1:int`; `&((d + 1) DIV 4):int`;
                        `&2:int`; `&1:int`; `&k + &1:int`;
                        `&2:int`; `--(&1):int`; `&k + &1:int`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[qf_reduced] THEN CONV_TAC INT_REDUCE_CONV THEN
  MAP_EVERY UNDISCH_TAC [`&d:int = &8 * &k + &7`; `&2:int <= &k`] THEN
  INT_ARITH_TAC);;

(* d prime, d = 3 mod 4, d > 3: a reduced form (a,b,c) with abs b = a is the *)
(* principal form, and a reduced form with a = c forces d = 3; with b <> 0   *)
(* the second reduced form (a,b,c) gives the third one (a,-b,c).             *)

let CNF_PRIME_AMBIG_A = prove
 (`!d a c:int. prime d /\ a * (&4 * c - a) = &d /\ &0 < a /\ a <= c
               ==> a = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `a:int`; `&4 * c - a:int`] CNF_INT_PRIME_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < a:int`; `a <= c:int`] THEN INT_ARITH_TAC);;

let CNF_PRIME_AMBIG_C = prove
 (`!d b c:int. prime d /\ (&2 * c - b) * (&2 * c + b) = &d /\
               &0 < c /\ abs b <= c
               ==> d = 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `&2 * c - b:int`; `&2 * c + b:int`]
    CNF_INT_PRIME_FACTOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < c:int`; `abs b <= c:int`] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `b = &2 * c - &1:int` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&2 * c - b = &1:int` THEN INT_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `b = &1 - &2 * c:int` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&2 * c + b = &1:int` THEN INT_ARITH_TAC; ALL_TAC]] THEN
  ASM_INT_ARITH_TAC);;

let CNF_PRIME_MOD4_3 = prove
 (`!d. prime d /\ d MOD 4 = 3 /\ ~(d = 3) ==> ~(form_classno(--(&d)) = 2)`,
  GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `d:num` CLASSNO_PRINCIPAL_REDUCED) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`--(&d:int)`; `&1:int`; `&1:int`; `&((d + 1) DIV 4):int`]
         CNF_CLASSNO_TWO_SECOND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INT_GCD_1]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int`
   (X_CHOOSE_THEN `c:int` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP QF_REDUCED_BOUNDS) THEN
  SUBGOAL_THEN `~(b = &0:int)` ASSUME_TAC THENL
   [MATCH_MP_TAC CNF_DISC_B_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`a:int`; `c:int`; `d:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(abs b = a:int)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`d:num`; `a:int`; `c:int`] CNF_PRIME_AMBIG_A) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `b pow 2 - &4 * a * c = --(&d:int)` THEN
      ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= b:int` ASSUME_TAC THENL
     [UNDISCH_TAC `qf_reduced a b c` THEN REWRITE_TAC[qf_reduced] THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(a:int = &1 /\ b:int = &1 /\ c:int = &((d + 1) DIV 4))` THEN
    REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`b pow 2 - &4 * a * c = --(&d:int)`;
      `&1 pow 2 - &4 * &1 * &((d + 1) DIV 4) = --(&d:int)`;
      `abs b = a:int`; `a = &1:int`; `&0 <= b:int`] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `a:int = &1 /\ b:int = &1` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a = c:int)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`d:num`; `b:int`; `c:int`] CNF_PRIME_AMBIG_C) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `b pow 2 - &4 * c * c = --(&d:int)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `a:int`; `b:int`; `c:int`;
                `&1:int`; `&1:int`; `&((d + 1) DIV 4):int`;
                `a:int`; `--b:int`; `c:int`] CNF_CLASSNO_THREE_SQUAREFREE) THEN
  ASM_SIMP_TAC[PRIME_IMP_SQUAREFREE] THEN
  REWRITE_TAC[qf_reduced; INT_ABS_NEG] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `(--b:int) pow 2 = b pow 2`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`~(b = &0:int)`; `~(abs b = a:int)`;
                         `abs b <= a:int`] THEN
  INT_ARITH_TAC);;

(* A squarefree d that is neither 1, a prime nor a product of two primes has *)
(* two factorisations d = m1 n1 = m2 n2 with 1 < mi < ni and m1 <> m2.       *)

let CNF_TWO_FACTORIZATIONS = prove
 (`!d. squarefree d /\ ~prime d /\ ~(d = 1) /\
       ~(?p q. prime p /\ prime q /\ d = p * q)
       ==> ?m1 n1 m2 n2. d = m1 * n1 /\ 1 < m1 /\ m1 < n1 /\
                         d = m2 * n2 /\ 1 < m2 /\ m2 < n2 /\ ~(m1 = m2)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SQUAREFREE_IMP_NZ) THEN
  MP_TAC(SPEC `d:num` CLASSNO_FORMS_NONPRIME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `n:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `coprime(m:num,n)` ASSUME_TAC THENL
   [UNDISCH_TAC `squarefree d` THEN UNDISCH_TAC `d = m * n` THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[SQUAREFREE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `m < n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `coprime(n:num,n)` THEN REWRITE_TAC[COPRIME_REFL] THEN
    UNDISCH_TAC `1 < n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `prime m` THENL
   [ASM_CASES_TAC `prime n` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `n:num` CLASSNO_FORMS_NONPRIME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`1 < m`; `m < n`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `y:num`
     STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `n:num`; `x:num`; `m * y:num`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MAP_EVERY UNDISCH_TAC [`d = m * n`; `n = x * y`] THEN CONV_TAC NUM_RING;
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 * y` THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN
      MAP_EVERY UNDISCH_TAC [`x <= y`; `1 < x`; `1 < m`] THEN ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `coprime(x:num,n)` THEN UNDISCH_TAC `n = x * y` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COPRIME_RMUL; COPRIME_REFL] THEN
      ASM_MESON_TAC[LT_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` CLASSNO_FORMS_NONPRIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `1 < m` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `y:num`
   STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`x:num`; `y * n:num`; `m:num`; `n:num`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MAP_EVERY UNDISCH_TAC [`d = m * n`; `m = x * y`] THEN CONV_TAC NUM_RING;
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `y * 2` THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN
    MAP_EVERY UNDISCH_TAC [`x <= y`; `1 < x`; `1 < m`; `m < n`] THEN
    ARITH_TAC;
    DISCH_TAC THEN
    UNDISCH_TAC `m = x * y` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    PURE_ONCE_REWRITE_TAC[ARITH_RULE `x = x * y <=> x * 1 = x * y`] THEN
    REWRITE_TAC[EQ_MULT_LCANCEL] THEN
    MAP_EVERY UNDISCH_TAC [`x <= y`; `1 < x`] THEN ARITH_TAC]);;

(* d = 3 mod 4 composite with class number two: d is a product of two primes *)
(* (two factorisations would give two distinct non-principal ambiguous       *)
(* forms).                                                                   *)

let CNF_COMPOSITE_MOD4_3 = prove
 (`!d. squarefree d /\ d MOD 4 = 3 /\ ~prime d /\ form_classno(--(&d)) = 2
       ==> ?p q. prime p /\ prime q /\ d = p * q`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPEC `d:num` CNF_TWO_FACTORIZATIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `1 MOD 4 = 3` THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m1:num`; `n1:num`; `m2:num`; `n2:num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `m1:num`; `n1:num`] QFORM_AMBIGUOUS_WITNESS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:int` (X_CHOOSE_THEN `b1:int`
   (X_CHOOSE_THEN `c1:int` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  MP_TAC(SPECL [`d:num`; `m2:num`; `n2:num`] QFORM_AMBIGUOUS_WITNESS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:int` (X_CHOOSE_THEN `b2:int`
   (X_CHOOSE_THEN `c2:int` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  MP_TAC(SPEC `d:num` CLASSNO_PRINCIPAL_REDUCED) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `form_classno(--(&d)) = 2` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CNF_CLASSNO_THREE_SQUAREFREE THEN
  MAP_EVERY EXISTS_TAC [`a1:int`; `b1:int`; `c1:int`; `a2:int`; `b2:int`;
                        `c2:int`; `&1:int`; `&1:int`;
                        `&((d + 1) DIV 4):int`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [SUBGOAL_THEN `~(&m1:int = &m2)` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_EQ]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`a1:int = b1 /\ a1 = &m1 \/ b1 < a1 /\ &2 * a1 - b1 = &m1`;
      `a2:int = b2 /\ a2 = &m2 \/ b2 < a2 /\ &2 * a2 - b2 = &m2`] THEN
    INT_ARITH_TAC;
    UNDISCH_TAC `&2 <= a1:int` THEN INT_ARITH_TAC;
    UNDISCH_TAC `&2 <= a2:int` THEN INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 3. Witnesses for the discriminant -4d.                                    *)
(* ------------------------------------------------------------------------- *)

let CNF_PRIMITIVE_DIAGONAL = prove
 (`!m n. coprime(m,n) ==> gcd(&m:int,gcd(&0,&n)) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INT_GCD_0; INT_ABS_NUM; GSYM NUM_GCD] THEN
  SIMP_TAC[COPRIME_GCD; INT_OF_NUM_EQ]);;

(* d = 1 mod 4 composite, d = m n (1 < m < n): the third form (m,0,n)        *)
(* besides (1,0,d) and (2,2,(d+1)/2).                                        *)

let CNF_MOD4_1 = prove
 (`!d. squarefree d /\ d MOD 4 = 1 /\ ~(d = 1) /\
       form_classno(--(&4 * &d)) = 2
       ==> prime d`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `k = d DIV 4` THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPEC `d:num` CLASSNO_FORMS_NONPRIME) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SQUAREFREE_IMP_NZ]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `n:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `coprime(m:num,n)` ASSUME_TAC THENL
   [UNDISCH_TAC `squarefree d` THEN UNDISCH_TAC `d = m * n` THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[SQUAREFREE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&d:int = &4 * &k + &1 /\ &1:int <= &k /\ &d:int = &m * &n /\
                &1:int < &m /\ &m:int <= &n`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
                INT_OF_NUM_LE; INT_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`d = k * 4 + 1`; `~(d = 1)`; `d = m * n`;
                           `1 < m`; `m <= n`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `gcd(&1:int,gcd(&0,&d)) = &1 /\
                gcd(&2:int,gcd(&2,&2 * &k + &1)) = &1 /\
                gcd(&m:int,gcd(&0,&n)) = &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INT_GCD_1; CNF_PRIMITIVE_DIAGONAL] THEN
    MATCH_MP_TAC QF_PRIMITIVE_BEZOUT THEN
    MAP_EVERY EXISTS_TAC [`--(&k):int`; `&0:int`; `&1:int`] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `form_classno(--(&4 * &d)) = 2` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CNF_CLASSNO_THREE THEN
  MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`; `&d:int`;
                        `&2:int`; `&2:int`; `&2 * &k + &1:int`;
                        `&m:int`; `&0:int`; `&n:int`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[qf_reduced] THEN
  MAP_EVERY UNDISCH_TAC [`&d:int = &4 * &k + &1`; `&1:int <= &k`;
                         `&d:int = &m * &n`; `&1:int < &m`; `&m:int <= &n`]
  THEN INT_ARITH_TAC);;

(* d = 2 mod 4 with d/2 = m n composite (1 < m <= n): the third form         *)
(* (m,0,2n) besides (1,0,d) and (2,0,d/2).                                   *)

let CNF_MOD4_2 = prove
 (`!d. squarefree d /\ d MOD 4 = 2 /\ ~(d = 2) /\
       form_classno(--(&4 * &d)) = 2
       ==> ?p. prime p /\ ODD p /\ d = 2 * p`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `k = d DIV 4` THEN
  ASM_CASES_TAC `prime(2 * k + 1)` THENL
   [EXISTS_TAC `2 * k + 1` THEN ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN
    UNDISCH_TAC `d = k * 4 + 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `2 * k + 1` CLASSNO_FORMS_NONPRIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`d = k * 4 + 2`; `~(d = 2)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `n:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `d = 2 * m * n` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`d = k * 4 + 2`; `2 * k + 1 = m * n`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(m:num,2 * n)` ASSUME_TAC THENL
   [UNDISCH_TAC `squarefree d` THEN UNDISCH_TAC `d = 2 * m * n` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SQUAREFREE_MUL; COPRIME_RMUL] THEN
    MESON_TAC[COPRIME_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `coprime(2,2 * n)` THEN
    REWRITE_TAC[COPRIME_RMUL; COPRIME_REFL; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&d:int = &4 * &k + &2 /\ &1:int <= &k /\
                &d:int = &2 * &m * &n /\ &1:int < &m /\ &m:int <= &n /\
                ~(&m:int = &2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
                INT_OF_NUM_LE; INT_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`d = k * 4 + 2`; `~(d = 2)`; `d = 2 * m * n`;
                           `1 < m`; `m <= n`; `~(m = 2)`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `gcd(&1:int,gcd(&0,&d)) = &1 /\
                gcd(&2:int,gcd(&0,&2 * &k + &1)) = &1 /\
                gcd(&m:int,gcd(&0,&(2 * n))) = &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INT_GCD_1; CNF_PRIMITIVE_DIAGONAL] THEN
    MATCH_MP_TAC QF_PRIMITIVE_BEZOUT THEN
    MAP_EVERY EXISTS_TAC [`--(&k):int`; `&0:int`; `&1:int`] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `form_classno(--(&4 * &d)) = 2` THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
  MATCH_MP_TAC CNF_CLASSNO_THREE THEN
  MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`; `&d:int`;
                        `&2:int`; `&0:int`; `&2 * &k + &1:int`;
                        `&m:int`; `&0:int`; `&(2 * n):int`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[qf_reduced; GSYM INT_OF_NUM_MUL] THEN
  MAP_EVERY UNDISCH_TAC [`&d:int = &4 * &k + &2`; `&1:int <= &k`;
                         `&d:int = &2 * &m * &n`; `&1:int < &m`;
                         `&m:int <= &n`; `~(&m:int = &2)`]
  THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. The cases of class number two.                                         *)
(* ------------------------------------------------------------------------- *)

let CNF_PRODUCT_MOD4_CASES = prove
 (`!p q. (p * q) MOD 4 = 3
         ==> p MOD 4 = 1 /\ q MOD 4 = 3 \/ p MOD 4 = 3 /\ q MOD 4 = 1`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
  CLASSNO_FORMS_MOD_CASES_TAC [`p MOD 4`; `q MOD 4`]);;

let CN_FORMS_TWO_CASES = prove
 (`!d. squarefree d /\ form_classno (qdisc d) = 2
       ==> (?p q. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
                  d = p * q /\ (d MOD 8 = 3 \/ d = 15)) \/
           (prime d /\ d MOD 4 = 1) \/
           (?p. prime p /\ ODD p /\ d = 2 * p)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(d = 1) /\ ~(d = 2) /\ ~(d = 3) /\ ~(d = 7)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `d:num` CLASSNO_NINE) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLASSNO_FORMS_MOD4_CASES) THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CNF_MOD4_1 THEN REPEAT CONJ_TAC THEN
      TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `form_classno (qdisc d) = 2` THEN
      ASM_REWRITE_TAC[qdisc; ARITH_EQ];
      FIRST_ASSUM ACCEPT_TAC];
    DISJ2_TAC THEN DISJ2_TAC THEN MATCH_MP_TAC CNF_MOD4_2 THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `form_classno (qdisc d) = 2` THEN
    ASM_REWRITE_TAC[qdisc; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `form_classno(--(&d)) = 2` ASSUME_TAC THENL
   [UNDISCH_TAC `form_classno (qdisc d) = 2` THEN ASM_REWRITE_TAC[qdisc];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP CLASSNO_FORMS_MOD8_CASES) THENL
   [ASM_CASES_TAC `prime d` THENL
     [MP_TAC(SPEC `d:num` CNF_PRIME_MOD4_3) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `d:num` CNF_COMPOSITE_MOD4_3) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `q:num`
     STRIP_ASSUME_TAC)) THEN
    DISJ1_TAC THEN
    MP_TAC(SPECL [`p:num`; `q:num`] CNF_PRODUCT_MOD4_CASES) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `d MOD 4 = 3` THEN UNDISCH_TAC `d = p * q` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`p:num`; `q:num`];
      MAP_EVERY EXISTS_TAC [`q:num`; `p:num`] THEN
      ONCE_REWRITE_TAC[MULT_SYM]] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `d = 15` THENL
   [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`5`; `3`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV PRIME_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `15 < d` ASSUME_TAC THENL
   [MP_TAC(SPECL [`d:num`; `8`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MAP_EVERY UNDISCH_TAC [`~(d = 7)`; `~(d = 15)`] THEN
    SPEC_TAC(`d DIV 8`,`k:num`) THEN GEN_TAC THEN
    STRIP_ASSUME_TAC(ARITH_RULE `k = 0 \/ k = 1 \/ 2 <= k`) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `d:num` CNF_MOD8_7) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. Quadratic characters of the values of the two forms.                   *)
(* ------------------------------------------------------------------------- *)

let CNF_JACOBI_SQUARE = prove
 (`!p n z:int. prime p /\ ~(p divides n) /\ (z pow 2 == &n) (mod &p)
               ==> jacobi(n,p) = &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC JACOBI_EQ_1 THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
    EXISTS_TAC `num_of_int(abs z)` THEN
    REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW] THEN
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_POW2_ABS]]);;

let CNF_JACOBI_4 = prove
 (`!p n. ODD p ==> jacobi(4 * n,p) = jacobi(n,p)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[JACOBI_LMUL; ARITH_RULE `4 = 2 EXP 2`; JACOBI_SQUARED] THEN
  ASM_REWRITE_TAC[COPRIME_2; INT_MUL_LID]);;

let CNF_PRIME_NDIVIDES_4MUL = prove
 (`!p n. prime p /\ ODD p /\ ~(p divides n) ==> ~(p divides 4 * n)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `~(p divides n)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC COPRIME_DIVPROD THEN EXISTS_TAC `4` THEN
  ASM_REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; COPRIME_RMUL; COPRIME_2]);;

(* Values prime to p (p | d) of the principal form are residues mod p:       *)
(* 4 f(x,y) = (2x + y)^2 + d y^2.                                            *)

let CNF_PRIN_VALUE_RESIDUE = prove
 (`!d p r x y.
        d MOD 4 = 3 /\ prime p /\ p divides d /\ ~(p divides r) /\
        qform (&1) (&1) (&((d + 1) DIV 4)) x y = &r
        ==> jacobi(r,p) = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC) o MATCH_MP CLASSNO_REP_DMOD4) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `d:num`)) THEN
  SUBGOAL_THEN `ODD p` ASSUME_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_ODD) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ACCEPT_TAC) THEN
    UNDISCH_TAC `2 divides 4 * k + 3` THEN REWRITE_TAC[DIVIDES_2] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `jacobi(4 * r,p) = &1` MP_TAC THENL
   [MATCH_MP_TAC CNF_JACOBI_SQUARE THEN EXISTS_TAC `&2 * x + y:int` THEN
    ASM_SIMP_TAC[CNF_PRIME_NDIVIDES_4MUL] THEN
    REWRITE_TAC[int_congruent] THEN
    SUBGOAL_THEN
     `(&2 * x + y) pow 2 - &(4 * r):int = &(4 * k + 3) * --(y pow 2)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `qform (&1) (&1) (&(k + 1)) x y = &r` THEN
      REWRITE_TAC[qform; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!p d z:int. p divides d ==> ?e. d * z = p * e`) THEN
    ASM_REWRITE_TAC[GSYM num_divides];
    ASM_SIMP_TAC[CNF_JACOBI_4]]);;

(* Values prime to p of the form F = (q,q,(p+q)/4) have the character        *)
(* (q | p): 4 q F(x,y) = (2 q x + q y)^2 + p q y^2.                          *)

let CNF_SECOND_VALUE_RESIDUE = prove
 (`!p q r x y.
        prime p /\ ODD p /\ ~(p divides q) /\ ~(p divides r) /\
        (p + q) MOD 4 = 0 /\
        qform (&q) (&q) (&((p + q) DIV 4)) x y = &r
        ==> jacobi(r,p) = jacobi(q,p)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(p + q) MOD 4 = 0` THEN REWRITE_TAC[MOD_EQ_0] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:num`) THEN
  SUBGOAL_THEN `(p + q) DIV 4 = t` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `jacobi(4 * q * r,p) = &1` MP_TAC THENL
   [MATCH_MP_TAC CNF_JACOBI_SQUARE THEN
    EXISTS_TAC `&2 * &q * x + &q * y:int` THEN
    ASM_SIMP_TAC[CNF_PRIME_NDIVIDES_4MUL; PRIME_DIVPROD_EQ] THEN
    REWRITE_TAC[int_congruent] THEN
    SUBGOAL_THEN
     `(&2 * &q * x + &q * y) pow 2 - &(4 * q * r):int =
      &p * --(&q * y pow 2)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `qform (&q) (&q) (&t) x y = &r` THEN
      UNDISCH_TAC `p + q = t * 4` THEN
      REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL;
                  GSYM INT_OF_NUM_ADD; qform] THEN
      CONV_TAC INT_RING;
      ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CNF_JACOBI_4; JACOBI_LMUL] THEN
  MP_TAC(SPECL [`q:num`; `p:num`] JACOBI_CASES) THEN
  MP_TAC(SPECL [`r:num`; `p:num`] JACOBI_CASES) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

(* The principal form does not represent a prime q with 4 q < d.             *)

let CNF_PRIN_NOT_PRIME = prove
 (`!d q x y. d MOD 4 = 3 /\ 4 * q < d /\ prime q
             ==> ~(qform (&1) (&1) (&((d + 1) DIV 4)) x y = &q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST1_TAC) o MATCH_MP CLASSNO_REP_DMOD4) THEN
  REWRITE_TAC[qform; GSYM INT_OF_NUM_ADD; INT_MUL_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&4 * &q = (&2 * x + y) pow 2 + &d * (y:int) pow 2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] THEN
    UNDISCH_TAC `x pow 2 + x * y + (&k + &1) * y pow 2 = &q:int` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `y:int = &0` THENL
   [UNDISCH_TAC `prime q` THEN
    UNDISCH_TAC `x pow 2 + x * y + (&k + &1) * y pow 2 = &q:int` THEN
    ASM_REWRITE_TAC[INT_POW_ZERO; ARITH_EQ; INT_MUL_LZERO; INT_MUL_RZERO;
                    INT_ADD_RID] THEN
    ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN
    MP_TAC(SPEC `abs x:int` INT_OF_NUM_OF_INT) THEN
    REWRITE_TAC[INT_ABS_POS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[PRIME_EXP; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1:int <= y pow 2` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN MATCH_MP_TAC INT_POW_LE_1 THEN
    UNDISCH_TAC `~(y:int = &0)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&d:int <= &d * y pow 2` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_RID] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN ASM_REWRITE_TAC[INT_POS];
    ALL_TAC] THEN
  MP_TAC(SPEC `&2 * x + y:int` INT_LE_POW_2) THEN
  UNDISCH_TAC `&4 * &q = (&2 * x + y) pow 2 + &d * (y:int) pow 2` THEN
  UNDISCH_TAC `4 * q < d` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 6. An auxiliary prime r = 1 mod 4 that is a non-residue mod p and mod q   *)
(* (Dirichlet and the Chinese remainder theorem); -d is a square mod 4 r.    *)
(* ------------------------------------------------------------------------- *)

let CNF_NONRESIDUE = prove
 (`!p. prime p /\ ODD p ==> ?a. jacobi(a,p) = --(&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` QUADRATIC_NONRESIDUE_EXISTS) THEN
  ASM_SIMP_TAC[GSYM ODD_PRIME] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `a:num` THEN ASM_SIMP_TAC[JACOBI_PRIME] THEN
  ASM_MESON_TAC[PRIME_COPRIME_EQ]);;

let CNF_JACOBI_NEG1_COPRIME = prove
 (`!a p. jacobi(a,p) = --(&1) ==> coprime(a,p)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM JACOBI_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN
  INT_ARITH_TAC);;

let CNF_CONG_MOD3 = prove
 (`!r k l m n. (r == k) (mod (l * m * n))
               ==> (r == k) (mod l) /\ (r == k) (mod m) /\ (r == k) (mod n)`,
  NUMBER_TAC);;

let CNF_AUX_PRIME = prove
 (`!p q. prime p /\ prime q /\ ODD p /\ ODD q /\ ~(p = q)
         ==> ?r. prime r /\ r MOD 4 = 1 /\
                 jacobi(r,p) = --(&1) /\ jacobi(r,q) = --(&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:num` CNF_NONRESIDUE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
  MP_TAC(SPEC `q:num` CNF_NONRESIDUE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:num`) THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `a:num`; `b:num`]
    CHINESE_REMAINDER_USUAL) THEN
  ASM_SIMP_TAC[DISTINCT_PRIME_COPRIME] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`4`; `p * q`; `1`; `k1:num`] CHINESE_REMAINDER_USUAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; COPRIME_LMUL; COPRIME_RMUL] THEN
    ASM_REWRITE_TAC[COPRIME_2];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(k == a) (mod p) /\ (k == b) (mod q)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(k1 == a) (mod p)`; `(k1 == b) (mod q)`;
      `(k == k1) (mod (p * q))`] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(k,4 * p * q)` ASSUME_TAC THENL
   [SUBGOAL_THEN `coprime(a:num,p) /\ coprime(b:num,q)` MP_TAC THENL
     [ASM_SIMP_TAC[CNF_JACOBI_NEG1_COPRIME]; ALL_TAC] THEN
    REWRITE_TAC[COPRIME_RMUL] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(k == 1) (mod 4)` THEN SPEC_TAC(`4`,`m:num`) THEN
      CONV_TAC NUMBER_RULE;
      MAP_EVERY UNDISCH_TAC [`(k == a) (mod p)`; `coprime(a:num,p)`] THEN
      CONV_TAC NUMBER_RULE;
      MAP_EVERY UNDISCH_TAC [`(k == b) (mod q)`; `coprime(b:num,q)`] THEN
      CONV_TAC NUMBER_RULE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`4 * p * q`; `k:num`] DIRICHLET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; ARITH_RULE `~(4 = 0)`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (STRIP_ASSUME_TAC o MATCH_MP CNF_CONG_MOD3)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(r == 1) (mod 4)` MP_TAC THENL
     [ASM_MESON_TAC[CONG_TRANS];
      REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV];
    SUBGOAL_THEN `(r == a) (mod p)` (SUBST1_TAC o MATCH_MP JACOBI_CONG) THENL
     [ASM_MESON_TAC[CONG_TRANS]; FIRST_ASSUM ACCEPT_TAC];
    SUBGOAL_THEN `(r == b) (mod q)` (SUBST1_TAC o MATCH_MP JACOBI_CONG) THENL
     [ASM_MESON_TAC[CONG_TRANS]; FIRST_ASSUM ACCEPT_TAC]]);;

let CNF_MOD4_1_ODD = prove
 (`!r. r MOD 4 = 1 ==> ODD r /\ EVEN((r - 1) DIV 2)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`r:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[ADD_SUB; ARITH_RULE `x * 4 = 2 * 2 * x`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; EVEN_MULT; ARITH]);;

let CNF_RECIPROCITY_1MOD4 = prove
 (`!r n. ODD r /\ ODD n /\ EVEN((r - 1) DIV 2) /\ coprime(r,n)
         ==> jacobi(n,r) = jacobi(r,n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r:num`; `n:num`] JACOBI_RECIPROCITY) THEN
  ASM_REWRITE_TAC[INT_POW_NEG; EVEN_MULT; INT_POW_ONE; INT_MUL_LID]);;

let CNF_SPLIT_B = prove
 (`!p q r. prime p /\ prime q /\ prime r /\ (p * q) MOD 4 = 3 /\
           r MOD 4 = 1 /\ jacobi(r,p) = --(&1) /\ jacobi(r,q) = --(&1)
           ==> ?b:int. (b pow 2 + &(p * q) == &0) (mod (&4 * &r))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CNF_MOD4_1_ODD) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP CLASSNO_REP_DMOD4_ODD) THEN
  REWRITE_TAC[ODD_MULT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `coprime(r:num,p) /\ coprime(r:num,q)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CNF_JACOBI_NEG1_COPRIME]; ALL_TAC] THEN
  SUBGOAL_THEN `jacobi(p,r) = --(&1) /\ jacobi(q,r) = --(&1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`r:num`; `p:num`] CNF_RECIPROCITY_1MOD4);
      MP_TAC(SPECL [`r:num`; `q:num`] CNF_RECIPROCITY_1MOD4)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `jacobi((r - 1) * p * q,r) = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[JACOBI_LMUL; JACOBI_MINUS1] THEN
    ASM_REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r divides (r - 1) * p * q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM PRIME_COPRIME_EQ; COPRIME_RMUL] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_MINUS1 THEN
    ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC CLASSNO_REP_SPLIT_B THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CLASSNO_REP_INT_SQUARE] THEN
  MP_TAC(SPECL [`(r - 1) * p * q`; `r:num`] JACOBI_PRIME) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [ALL_TAC; CONV_TAC INT_REDUCE_CONV] THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:num`) THEN EXISTS_TAC `x:num` THEN
  MP_TAC(SPECL [`x EXP 2`; `r - 1`; `p * q`]
   (NUMBER_RULE `!x s d:num. (x == s * d) (mod (s + 1)) <=>
                             (s + 1) divides x + d`)) THEN
  SUBGOAL_THEN `r - 1 + 1 = r` SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. The genus character: (q | p) = -1.                                     *)
(* ------------------------------------------------------------------------- *)

(* The reduction G of (q,q,(p+q)/4) represents q, which the principal form   *)
(* does not; the reduction of (r,b,(b^2+d)/(4r)) represents r and is G (the  *)
(* principal form is excluded by (r | p) = -1), so (q | p) = (r | p) = -1.   *)

let CN_GENUS_CHARACTER = prove
 (`!p q. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
         form_classno (--(&(p * q))) = 2
         ==> qchar p q = --(&1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[qchar] THEN
  SUBGOAL_THEN `jacobi(q,p) = --(&1)`
   (fun th -> REWRITE_TAC[th; int_neg_th; int_of_num_th]) THEN
  (* Arithmetic of p, q and d = p q. *)
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CNF_MOD4_1_ODD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CLASSNO_REP_DMOD4_ODD) THEN
  SUBGOAL_THEN `~(p:num = q)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `q MOD 4 = 1` THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p * q) MOD 4 = 3` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `squarefree(p * q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE; DISTINCT_PRIME_COPRIME];
    ALL_TAC] THEN
  SUBGOAL_THEN `5 <= p` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`p DIV 4`,`k:num`) THEN GEN_TAC THEN
    STRIP_ASSUME_TAC(ARITH_RULE `k = 0 \/ 1 <= k`) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `4 * q < p * q` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `5 * q` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN
    MP_TAC(SPEC `q:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLASSNO_FORMS_PRODUCT_MOD4 o
    check (fun th -> concl th = `(p * q) MOD 4 = 3`)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&4 * &((p + q) DIV 4):int = &p + &q` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
    MP_TAC(SPECL [`p + q`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p divides q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIVIDES_PRIME_PRIME]; ALL_TAC] THEN
  ABBREV_TAC `d = p * q` THEN
  SUBGOAL_THEN `p divides d /\ &0:int < &d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[INT_OF_NUM_LT; LT_NZ; MULT_EQ_0] THEN
    CONJ_TAC THENL [CONV_TAC NUMBER_RULE; ASM_MESON_TAC[PRIME_IMP_NZ]];
    ALL_TAC] THEN
  (* The principal form f0 and the second form G, reduced from (q,q,(p+q)/4). *)
  MP_TAC(SPEC `d:num` CLASSNO_PRINCIPAL_REDUCED) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&q pow 2 - &4 * &q * &((p + q) DIV 4):int = --(&d)`
  ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    UNDISCH_TAC `&4 * &((p + q) DIV 4):int = &p + &q` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&q:int`; `&q:int`; `&((p + q) DIV 4):int`; `d:num`]
    QFORM_REDUCE_FORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:int` (X_CHOOSE_THEN `b2:int`
   (X_CHOOSE_THEN `c2:int` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "VG"))))))) THEN
  SUBGOAL_THEN `?x y. qform a2 b2 c2 x y = &q` ASSUME_TAC THENL
   [USE_THEN "VG" (fun th -> REWRITE_TAC[GSYM th]) THEN
    MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`] THEN
    REWRITE_TAC[qform] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a2:int = &1 /\ b2:int = &1 /\ c2:int = &((d + 1) DIV 4))`
  ASSUME_TAC THENL
   [DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `x:int` (X_CHOOSE_TAC `y:int`) o
      check (is_exists o concl)) THEN
    MP_TAC(SPECL [`d:num`; `q:num`; `x:int`; `y:int`] CNF_PRIN_NOT_PRIME) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* The auxiliary prime r and a reduced form H representing r.            *)
  MP_TAC(SPECL [`p:num`; `q:num`] CNF_AUX_PRIME) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(p divides r)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM PRIME_COPRIME_EQ] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    MATCH_MP_TAC CNF_JACOBI_NEG1_COPRIME THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`] CNF_SPLIT_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:int` MP_TAC) THEN
  REWRITE_TAC[int_congruent; INT_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:int`) THEN
  MP_TAC(SPECL [`d:num`; `r:num`; `b:int`; `c:int`]
    QFORM_REPRESENTED_REDUCED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_MUL_ASSOC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0:int < &d` THEN REWRITE_TAC[INT_OF_NUM_LT] THEN ARITH_TAC;
      MATCH_MP_TAC QF_PRIMITIVE_SQUAREFREE THEN EXISTS_TAC `d:num` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `b pow 2 + &d = (&4 * &r) * c:int` THEN INT_ARITH_TAC];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a3:int`; `b3:int`; `c3:int`; `x3:int`; `y3:int`] THEN
  STRIP_TAC THEN
  (* h = 2: H is G or the principal form. *)
  MP_TAC(SPECL [`--(&d:int)`; `a2:int`; `b2:int`; `c2:int`;
                `&1:int`; `&1:int`; `&((d + 1) DIV 4):int`;
                `a3:int`; `b3:int`; `c3:int`] CNF_CLASSNO_TWO_OTHER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[INT_GCD_1];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC)) THENL
   [SUBGOAL_THEN `?x y. qform (&q) (&q) (&((p + q) DIV 4)) x y = &r`
    MP_TAC THENL
     [USE_THEN "VG" (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY EXISTS_TAC [`x3:int`; `y3:int`] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `x:int`; `y:int`]
      CNF_SECOND_VALUE_RESIDUE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(SPECL [`d:num`; `p:num`; `r:num`; `x3:int`; `y3:int`]
      CNF_PRIN_VALUE_RESIDUE) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `jacobi(r,p) = --(&1)` THEN INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 8. The eighteen discriminants of class number two (FORM_CLASSNO_CONV).    *)
(* ------------------------------------------------------------------------- *)

let CLASS_NUMBER_TWO_EXAMPLES = prove
 (`!d. d IN {5,6,10,13,15,22,35,37,51,58,91,115,123,187,235,267,403,427}
       ==> form_classno (qdisc d) = 2`,
  GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[qdisc] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV FORM_CLASSNO_CONV THENC NUM_REDUCE_CONV));;
