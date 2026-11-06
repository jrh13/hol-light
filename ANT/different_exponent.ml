(* ========================================================================= *)
(* The exact exponent of the different and of the discriminant.              *)
(*                                                                           *)
(* For a number field k with ring of integers O and a nonzero prime P of O   *)
(* above the rational prime p (prime p and ring_of_num k p IN P), with e =   *)
(* e(P|p) = ramification_index (integer_ring,O) (ring_of_int k) P and f =    *)
(* f(P|p) = residue_degree (integer_ring,O) (ring_of_int k) P, the different *)
(* D = number_field_different (subfield_generated k {ring_0 k},k) I of       *)
(* ANT/different.ml (the different over the prime subfield) and the          *)
(* discriminant d_K = number_field_discriminant k (Dedekind):                *)
(*                                                                           *)
(*   D SUBSET P^e <=> p divides e      (NUMBER_FIELD_DIFFERENT_WILD)         *)
(*   v_P(D) = e - 1 <=> ~(p divides e)                                       *)
(*                             (NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q)     *)
(*   e <= v_P(D) <=> p divides e                                             *)
(*                             (NUMBER_FIELD_DIFFERENT_VALUATION_WILD_Q)     *)
(*                                                                           *)
(* where v_P(D) = ideal_valuation O P D, and e - 1 <= v_P(D) always (from    *)
(* NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION of ANT/different_extension.ml  *)
(* over the prime subfield, with RAMIFICATION_INDEX_PRIME_SUBFIELD of        *)
(* ANT/relative_split.ml); the tame half in the form ~(D SUBSET P^e) is      *)
(* NUMBER_FIELD_DIFFERENT_TAME. With v_p(m) = index p m (Library/prime.ml),  *)
(* for every nonzero ideal j of O the exponent of p in the norm is v_p(N(j)) *)
(* = sum of f(P) v_P(j) over the primes P above p                            *)
(* (NUMBER_FIELD_IDEAL_NORM_PRIME_EXPONENT), so v_p(d_K) is the sum of the   *)
(* f(P) v_P(D) (NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT); v_p(d_K) is at    *)
(* least the sum of the f(P) (e(P) - 1), with equality iff p is tamely       *)
(* ramified, i.e. p divides no e(P)                                          *)
(* (NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_GE,                             *)
(* NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_TAME).                           *)
(*                                                                           *)
(* Route. pO = P^e Q with Q = (pO : P^e) prime to P, so P^e + Q = O, P^e     *)
(* INTER Q = pO and O/pO = O/P^e x O/Q; the trace of O over Z reduced modulo *)
(* p is the sum of the traces of O/P^e and O/Q over F_p = Z/pZ               *)
(* (ALGEBRA_TRACE_INTEGER_MOD_SPLIT). On O/P^e the trace is e times the      *)
(* trace of the residue field O/P (DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW): for *)
(* a uniformizer t (in P but not in P^2) and lifts b(j) of a basis of O/P    *)
(* over F_p, the cosets of t^(s DIV f) b(s MOD f), s < f e, form a basis of  *)
(* O/P^e (DEDEKIND_QUOTIENT_POW_FREE_BASIS, with the level lemmas            *)
(* DEDEKIND_IDEAL_POW_LEVEL_SPAN, _COEFFS and _INDEPENDENT, which rest on    *)
(* DEDEKIND_UNIFORMIZER_CRITERION of ANT/dedekind_valuation.ml), and in it   *)
(* multiplication by x is block triangular with the matrix of x on O/P in    *)
(* each of the e diagonal blocks. So on Q the trace modulo p is e times the  *)
(* residue trace, which is not identically zero (finite fields are           *)
(* separable): all elements of Q have traces divisible by p iff p divides e  *)
(* (ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES). Finally D SUBSET P^e   *)
(* iff x D SUBSET pO = P^e Q for all x in Q (cancel Q), iff x / p is in the  *)
(* codifferent for all x in Q (NUMBER_FIELD_CODIFFERENT_DIV), iff p divides  *)
(* the traces of all elements of Q (NUMBER_FIELD_CODIFFERENT_DIV_NUM). The   *)
(* exponents of the discriminant follow from N(D) = |d_K|                    *)
(* (NUMBER_FIELD_IDEAL_NORM_DIFFERENT), N(j) = prod N(P)^v_P(j)              *)
(* (IDEAL_NORM_FACTORIZATION) and N(P) = p^f(P)                              *)
(* (RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q).                                    *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (RING_CHAR_QUOTIENT_RING_DIVIDES,             *)
(* QUOTIENT_RING_LINCOMB_LIFT, RING_OF_INT_REM_CHAR_DIVIDES,                 *)
(* IN_RING_IDEAL_SUB_SUM_RESTRICT), Library/fieldtheory.ml                   *)
(* (FREE_BASIS_EXISTS), Library/ring_det.ml (free bases, coordinates,        *)
(* mul_matrix, algebra_trace, ADD_MULT_LT_MULT, RING_SUM_NUMSEG_DIV_SLICE),  *)
(* Library/prime.ml (index, INDEX_NPRODUCT),                                 *)
(* ANT/ideal_arith.ml (RING_ISOMORPHISM_QUOTIENT_RING_INTER),                *)
(* ANT/dedekind.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml,            *)
(* ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml,             *)
(* ANT/trace_form.ml (ALGEBRA_TRACE_PROD_RING,                               *)
(* ALGEBRA_TRACE_ISOMORPHIC_IMAGE), ANT/finite_field_trace.ml                *)
(* (ALGEBRA_TRACE_FINITE_FIELD_NONZERO), ANT/ramification.ml                 *)
(* (FREE_BASIS_QUOTIENT_RING_INTEGER_MOD,                                    *)
(* ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD,                                  *)
(* ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD), ANT/relative_split.ml               *)
(* (RAMIFICATION_INDEX_PRIME_SUBFIELD), ANT/different.ml and                 *)
(* ANT/different_extension.ml (NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION).  *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_det.ml";;
needs "Library/prime.ml";;
needs "Library/products.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_valuation.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/trace_form.ml";;
needs "ANT/finite_field_trace.ml";;
needs "ANT/ramification.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/different.ml";;
needs "ANT/different_extension.ml";;

(* ------------------------------------------------------------------------- *)
(* A basis of r/P^e from a basis of r/P over Z/pZ and a uniformizer.         *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_IDEAL_POW_LEVEL_SPAN = prove
 (`!r P (t:A) p f g (b:num->A) e.
        dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
        t IN P /\ ~(t IN ideal_pow r P 2) /\
        free_basis (integer_mod_ring p,quotient_ring r P)
                   (ring_of_int (quotient_ring r P)) f g /\
        (!j. b j IN ring_carrier r) /\
        (!j. j < f ==> ring_coset r P (b j) = g j)
        ==> !i y. i <= e /\ y IN ideal_pow r P i
                  ==> ?c:num->int.
                        (!s. s DIV f < i ==> c s = &0) /\
                        ring_sub r y
                         (ring_sum r {s:num | s < f * e}
                           (\s. ring_mul r (ring_of_int r (c s))
                                 (ring_mul r (ring_pow r t (s DIV f))
                                             (b (s MOD f))))) IN
                        ideal_pow r P e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `t:A`]
    DEDEKIND_UNIFORMIZER_CRITERION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "u1" o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!d i (y:A). i + d = e /\ y IN ideal_pow r P i
            ==> ?c:num->int.
                  (!s. s DIV f < i ==> c s = &0) /\
                  ring_sub r y
                   (ring_sum r {s:num | s < f * e}
                     (\s. ring_mul r (ring_of_int r (c s))
                           (ring_mul r (ring_pow r t (s DIV f))
                                       (b (s MOD f))))) IN
                  ideal_pow r P e`
  (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN
             EXISTS_TAC `e - i:num` THEN ASM_REWRITE_TAC[] THEN
             ASM_ARITH_TAC) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `\s:num. &0:int` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(CONJUNCT1 RING_OF_INT_CLAUSES)] THEN
    SUBGOAL_THEN `(y:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET; RING_IDEAL_IDEAL_POW];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL; RING_POW; RING_SUM_0;
                 RING_SUB_RZERO] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET; RING_IDEAL_IDEAL_POW];
    ALL_TAC] THEN
  REMOVE_THEN "u1" (MP_TAC o SPECL [`i:num`; `1:num`; `y:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `ring_coset r P (a:A)` o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [free_basis]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d0:num->int` (ASSUME_TAC o CONJUNCT2))] THEN
  SUBGOAL_THEN
   `ring_sub r a (ring_sum r {j:num | j < f}
                   (\j. ring_mul r (ring_of_int r ((d0:num->int) j))
                                   ((b:num->A) j))) IN P`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`r:A ring`; `P:A->bool`; `a:A`;
      `ring_sum r {j:num | j < f}
         (\j. ring_mul r (ring_of_int r ((d0:num->int) j)) ((b:num->A) j))`]
     RING_COSET_EQ) THEN
    ASM_REWRITE_TAC[RING_SUM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `f:num`; `b:num->A`;
                   `g:num->A->bool`; `d0:num->int`]
      QUOTIENT_RING_LINCOMB_LIFT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL
   [`i + 1:num`;
    `ring_sub r y
      (ring_mul r (ring_pow r t i)
        (ring_sum r {j:num | j < f}
          (\j. ring_mul r (ring_of_int r ((d0:num->int) j))
                          ((b:num->A) j))))`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[]
     `!u w:A s. u = w /\ w IN s ==> u IN s`) THEN
    EXISTS_TAC
     `ring_add r (ring_sub r y (ring_mul r (ring_pow r t i) a))
        (ring_mul r (ring_pow r t i)
          (ring_sub r a
            (ring_sum r {j:num | j < f}
              (\j. ring_mul r (ring_of_int r ((d0:num->int) j))
                              ((b:num->A) j)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_sub r y (ring_mul r u z) =
        ring_add r (ring_sub r y (ring_mul r u a))
                   (ring_mul r u (ring_sub r a (z:A)))`) THEN
      ASM_SIMP_TAC[RING_POW; RING_SUM];
      ALL_TAC] THEN
    MATCH_MP_TAC IN_RING_IDEAL_ADD THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; RING_POW_IN_IDEAL_POW; IDEAL_POW_1];
    DISCH_THEN(X_CHOOSE_THEN `c:num->int` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC
   `\s. (c:num->int) s + (if s DIV f = i then (d0:num->int) (s MOD f)
                          else &0)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(s DIV f = i) /\ s DIV f < i + 1` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[INT_ADD_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sum r {s:num | s < f * e}
      (\s. ring_mul r
             (ring_of_int r ((c:num->int) s +
                (if s DIV f = i then (d0:num->int) (s MOD f) else &0)))
             (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))) =
    ring_add r
     (ring_sum r {s:num | s < f * e}
        (\s. ring_mul r (ring_of_int r (c s))
                      (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f)))))
     (ring_mul r (ring_pow r t i)
        (ring_sum r {j:num | j < f}
          (\j. ring_mul r (ring_of_int r (d0 j)) (b j))))`
  SUBST1_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      free_in `ideal_pow r (P:A->bool) e` (concl th) &&
      free_in `c:num->int` (concl th))) THEN
    MATCH_MP_TAC(MESON[]
     `(a:A) = b ==> a IN s ==> b IN s`) THEN
    MATCH_MP_TAC(RING_RULE
     `ring_sub r (ring_sub r y w) z = ring_sub r y (ring_add r z (w:A))`) THEN
    ASM_SIMP_TAC[RING_SUM; RING_MUL; RING_POW]] THEN
  REWRITE_TAC[RING_OF_INT_ADD] THEN
  ASM_SIMP_TAC[RING_ADD_RDISTRIB; RING_OF_INT; RING_MUL; RING_POW] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_ADD o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; RING_MUL; RING_POW; RING_OF_INT] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  TRANS_TAC EQ_TRANS
   `ring_sum r {s:num | s < f * e}
      (\s. if s DIV f = i
           then ring_mul r (ring_of_int r ((d0:num->int) (s MOD f)))
                  (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))
           else ring_0 r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(CONJUNCT1 RING_OF_INT_CLAUSES)] THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL; RING_POW];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_NUMSEG_DIV_SLICE o
    lhand o snd) THEN
  ASM_SIMP_TAC[RING_MUL; RING_POW; RING_OF_INT] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM RING_SUM_LMUL; FINITE_NUMSEG_LT; RING_MUL; RING_OF_INT;
           RING_POW; ASSUME `(t:A) IN ring_carrier r`;
           ASSUME `!j. (b:num->A) j IN ring_carrier r`] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul r a (ring_mul r u v) = ring_mul r u (ring_mul r a (v:A))`) THEN
  ASM_SIMP_TAC[RING_OF_INT; RING_POW]);;

let DEDEKIND_IDEAL_POW_LEVEL_COEFFS = prove
 (`!r P (t:A) f g (b:num->A) e (c:num->int) l a.
        dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
        t IN P /\ ~(t IN ideal_pow r P 2) /\
        (!j. b j IN ring_carrier r) /\
        (!j. j < f ==> ring_coset r P (b j) = g j) /\
        l < e /\ (!s. s < f * e /\ s DIV f < l ==> c s = &0) /\
        a IN ring_carrier r /\
        ring_sub r (ring_mul r (ring_pow r t l) a)
          (ring_sum r {s:num | s < f * e}
            (\s. ring_mul r (ring_of_int r (c s))
                  (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f))))) IN
        ideal_pow r P (l + 1)
        ==> ring_coset r P a =
            ring_sum (quotient_ring r P) {j:num | j < f}
              (\j. ring_mul (quotient_ring r P)
                     (ring_of_int (quotient_ring r P) (c (j + f * l))) (g j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `t:A`]
    DEDEKIND_UNIFORMIZER_CRITERION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "u2" o CONJUNCT2) THEN
  MP_TAC(BETA_RULE(ISPECL [`r:A ring`; `P:A->bool`; `f:num`; `b:num->A`;
                 `g:num->A->bool`; `\j. (c:num->int) (j + f * l)`]
    QUOTIENT_RING_LINCOMB_LIFT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_COSET_EQ o snd) THEN
  ASM_SIMP_TAC[RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN
  REMOVE_THEN "u2" (MP_TAC o SPECL
   [`l:num`; `1:num`;
    `ring_sub r a
      (ring_sum r {j:num | j < f}
        (\j. ring_mul r (ring_of_int r ((c:num->int) (j + f * l)))
                        ((b:num->A) j)))`]) THEN
  ASM_SIMP_TAC[RING_SUB; RING_SUM; IDEAL_POW_1] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `~(f = 0) \/ f = 0` STRIP_ASSUME_TAC THENL
   [ARITH_TAC;
    ALL_TAC;
    ASM_REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; RING_SUM_CLAUSES] THEN
    ASM_SIMP_TAC[RING_SUB_RZERO; RING_MUL_RZERO; RING_POW] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      free_in `ideal_pow r (P:A->bool) (l + 1)` (concl th))) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC;
                    RING_SUM_CLAUSES] THEN
    ASM_SIMP_TAC[RING_SUB_RZERO; RING_MUL; RING_POW]] THEN
  MP_TAC(ISPECL
   [`r:A ring`; `f:num`; `e:num`; `l:num`;
    `\s. ring_mul r (ring_of_int r ((c:num->int) s))
           (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))`]
   RING_SUM_NUMSEG_DIV_SLICE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_MUL; RING_POW; RING_OF_INT];
    DISCH_THEN(MP_TAC o BETA_RULE)] THEN
  SUBGOAL_THEN
   `ring_sum r {j:num | j < f}
      (\j. ring_mul r (ring_of_int r ((c:num->int) (j + f * l)))
             (ring_mul r (ring_pow r t ((j + f * l) DIV f))
                         ((b:num->A) ((j + f * l) MOD f)))) =
    ring_mul r (ring_pow r t l)
      (ring_sum r {j:num | j < f}
         (\j. ring_mul r (ring_of_int r (c (j + f * l))) (b j)))`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM RING_SUM_LMUL; FINITE_NUMSEG_LT; RING_MUL; RING_OF_INT;
             RING_POW; ASSUME `(t:A) IN ring_carrier r`;
             ASSUME `!j. (b:num->A) j IN ring_carrier r`] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul r a (ring_mul r u v) = ring_mul r u (ring_mul r a (v:A))`) THEN
    ASM_SIMP_TAC[RING_OF_INT; RING_POW];
    DISCH_THEN(LABEL_TAC "sl")] THEN
  SUBGOAL_THEN
   `ring_mul r (ring_pow r t l)
      (ring_sub r a
        (ring_sum r {j:num | j < f}
          (\j. ring_mul r (ring_of_int r ((c:num->int) (j + f * l)))
                          ((b:num->A) j)))) =
    ring_sub r (ring_mul r (ring_pow r t l) a)
      (ring_mul r (ring_pow r t l)
        (ring_sum r {j:num | j < f}
          (\j. ring_mul r (ring_of_int r (c (j + f * l))) (b j))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_SUB_LDISTRIB THEN ASM_SIMP_TAC[RING_POW; RING_SUM];
    REMOVE_THEN "sl" (SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC IN_RING_IDEAL_SUB_SUM_RESTRICT THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; FINITE_NUMSEG_LT; RING_MUL; RING_POW;
               RING_OF_INT] THEN
  X_GEN_TAC `s:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s DIV f < l` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:num` o check (fun th ->
      free_in `c:num->int` (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM(CONJUNCT1 RING_OF_INT_CLAUSES)] THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL; RING_POW; IN_RING_IDEAL_0;
                 RING_IDEAL_IDEAL_POW];
    MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW; RING_OF_INT] THEN
    SUBGOAL_THEN `l + 1 <= s DIV f` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `l + 1`; `s DIV f`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN
    MATCH_MP_TAC(SET_RULE `(x:A) IN s ==> s SUBSET t ==> x IN t`) THEN
    MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RING_POW_IN_IDEAL_POW]]);;

let DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT = prove
 (`!r P (t:A) p f g (b:num->A) e m (c:num->int).
        dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
        t IN P /\ ~(t IN ideal_pow r P 2) /\
        free_basis (integer_mod_ring p,quotient_ring r P)
                   (ring_of_int (quotient_ring r P)) f g /\
        (!j. b j IN ring_carrier r) /\
        (!j. j < f ==> ring_coset r P (b j) = g j) /\
        m <= e /\
        (!s. s < f * e ==> c s IN ring_carrier(integer_mod_ring p)) /\
        ring_sum r {s:num | s < f * e}
          (\s. ring_mul r (ring_of_int r (c s))
                (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f)))) IN
        ideal_pow r P m
        ==> !s. s < f * e /\ s DIV f < m ==> c s = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `!l. l < m ==> !j. j < f ==> (c:num->int)(j + f * l) = &0`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MULT_CLAUSES; CONJUNCT1 LT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s DIV f`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `s MOD f`) THEN ASM_SIMP_TAC[MOD_LT_EQ] THEN
    SUBGOAL_THEN `s MOD f + f * s DIV f = s` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`s:num`; `f:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `l:num` THEN
  DISCH_THEN(LABEL_TAC "lt") THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `t:A`; `f:num`; `g:num->A->bool`;
                 `b:num->A`; `e:num`; `c:num->int`; `l:num`; `ring_0 r:A`]
    DEDEKIND_IDEAL_POW_LEVEL_COEFFS) THEN
  ASM_REWRITE_TAC[RING_0] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `s:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[MULT_CLAUSES; CONJUNCT1 LT]; ALL_TAC] THEN
      REMOVE_THEN "lt" (MP_TAC o SPEC `s DIV f`) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `s MOD f`) THEN ASM_SIMP_TAC[MOD_LT_EQ] THEN
      SUBGOAL_THEN `s MOD f + f * s DIV f = s` (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(SPECL [`s:num`; `f:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[RING_MUL_RZERO; RING_POW; RING_SUB_LZERO; RING_SUM] THEN
      MATCH_MP_TAC IN_RING_IDEAL_NEG THEN
      REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
      MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `l + 1`; `m:num`]
        IDEAL_POW_ANTIMONO) THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_coset r P (ring_0 r:A) = ring_0 (quotient_ring r P)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; IN_RING_IDEAL_0;
                 RING_0];
    DISCH_THEN(ASSUME_TAC o SYM)] THEN
  FIRST_ASSUM(MP_TAC o SPEC `\j. (c:num->int) (j + f * l)` o
    CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [free_basis]) THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC ADD_MULT_LT_MULT THEN ASM_ARITH_TAC);;

let DEDEKIND_QUOTIENT_POW_FREE_BASIS = prove
 (`!r P (t:A) p f g (b:num->A) e.
        dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
        t IN P /\ ~(t IN ideal_pow r P 2) /\
        ring_of_num r p IN ideal_pow r P e /\
        free_basis (integer_mod_ring p,quotient_ring r P)
                   (ring_of_int (quotient_ring r P)) f g /\
        (!j. b j IN ring_carrier r) /\
        (!j. j < f ==> ring_coset r P (b j) = g j)
        ==> free_basis
              (integer_mod_ring p,quotient_ring r (ideal_pow r P e))
              (ring_of_int (quotient_ring r (ideal_pow r P e))) (f * e)
              (\s. ring_coset r (ideal_pow r P e)
                     (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:num->int.
      ring_coset r (ideal_pow r P e)
       (ring_sum r {s:num | s < f * e}
         (\s. ring_mul r (ring_of_int r (c s))
                (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f))))) =
      ring_sum (quotient_ring r (ideal_pow r P e)) {s:num | s < f * e}
        (\s. ring_mul (quotient_ring r (ideal_pow r P e))
               (ring_of_int (quotient_ring r (ideal_pow r P e)) (c s))
               (ring_coset r (ideal_pow r P e)
                 (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f)))))`
  (LABEL_TAC "lin") THENL
   [GEN_TAC THEN
    MP_TAC(BETA_RULE(ISPECL
     [`r:A ring`; `ideal_pow r (P:A->bool) e`; `f * e:num`;
      `\s. ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f))`;
      `\s. ring_coset r (ideal_pow r P e)
             (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))`;
      `c:num->int`] QUOTIENT_RING_LINCOMB_LIFT)) THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RING_MUL; RING_POW];
    ALL_TAC] THEN
  REWRITE_TAC[free_basis] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; RING_IDEAL_IDEAL_POW; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_MUL; RING_POW];
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; RING_IDEAL_IDEAL_POW;
                 FORALL_IN_GSPEC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `t:A`; `p:num`; `f:num`;
                   `g:num->A->bool`; `b:num->A`; `e:num`]
      DEDEKIND_IDEAL_POW_LEVEL_SPAN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`0`; `y:A`]) THEN
    ASM_REWRITE_TAC[LE_0; IDEAL_POW_0; CONJUNCT1 LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num->int` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\s. (c:num->int) s rem &p` THEN
    REWRITE_TAC[INTEGER_MOD_RING_CARRIER_REM] THEN
    MP_TAC(ISPECL [`quotient_ring r (ideal_pow r (P:A->bool) e)`; `p:num`]
      RING_OF_INT_REM_CHAR_DIVIDES) THEN
    ASM_SIMP_TAC[RING_CHAR_QUOTIENT_RING_DIVIDES; RING_IDEAL_IDEAL_POW] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REMOVE_THEN "lin" (SUBST1_TAC o SYM o SPEC `c:num->int`) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_COSET_EQ o snd) THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RING_SUM];
    X_GEN_TAC `c:num->int` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[INTEGER_MOD_RING_CLAUSES] THEN
    X_GEN_TAC `s:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `t:A`; `p:num`; `f:num`;
                   `g:num->A->bool`; `b:num->A`; `e:num`; `e:num`;
                   `c:num->int`] DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[MULT_CLAUSES; CONJUNCT1 LT];
        ASM_SIMP_TAC[RDIV_LT_EQ]]] THEN
    W(fun (_,w) -> MP_TAC(ISPECL
      [`r:A ring`; `ideal_pow r (P:A->bool) e`; lhand w]
      RING_COSET_EQ_IDEAL)) THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RING_SUM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REMOVE_THEN "lin" (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[QUOTIENT_RING_0; RING_IDEAL_IDEAL_POW]]);;

(* ------------------------------------------------------------------------- *)
(* The trace of r/P^e is e times the trace of the residue field.             *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW = prove
 (`!r P p f g e (x:A).
        dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
        ring_of_num r p IN ideal_pow r P e /\
        free_basis (integer_mod_ring p,quotient_ring r P)
                   (ring_of_int (quotient_ring r P)) f g /\
        x IN ring_carrier r
        ==> algebra_trace
              (integer_mod_ring p,quotient_ring r (ideal_pow r P e))
              (ring_of_int (quotient_ring r (ideal_pow r P e)))
              (ring_coset r (ideal_pow r P e) x) =
            ring_mul (integer_mod_ring p) (ring_of_num (integer_mod_ring p) e)
              (algebra_trace (integer_mod_ring p,quotient_ring r P)
                 (ring_of_int (quotient_ring r P)) (ring_coset r P x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`] DEDEKIND_PRIME_IDEAL_UNIFORMIZER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?b:num->A. !j. b j IN ring_carrier r /\
                   (j < f ==> ring_coset r P (b j) = g j)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j:num < f` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(MP_TAC o SPEC `j:num` o CONJUNCT1 o
        GEN_REWRITE_RULE I [free_basis]) THEN
      ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN MESON_TAC[];
      MESON_TAC[RING_0]];
    REWRITE_TAC[FORALL_AND_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num->A` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `t:A`; `p:num`; `f:num`;
                 `g:num->A->bool`; `b:num->A`; `e:num`]
    DEDEKIND_QUOTIENT_POW_FREE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `G = \s. ring_coset r (ideal_pow r P e)
              (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_homomorphism(integer_mod_ring p,quotient_ring r (ideal_pow r P e))
      (ring_of_int (quotient_ring r (ideal_pow r P e)):int->A->bool)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT;
                 RING_CHAR_QUOTIENT_RING_DIVIDES; RING_IDEAL_IDEAL_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_coset r (ideal_pow r P e) (x:A) IN
    ring_carrier(quotient_ring r (ideal_pow r P e))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; RING_IDEAL_IDEAL_POW; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ring_of_int (quotient_ring r (ideal_pow r P e)):int->A->bool`;
    `integer_mod_ring p`; `quotient_ring r (ideal_pow r (P:A->bool) e)`;
    `f * e:num`; `G:num->A->bool`; `ring_coset r (ideal_pow r P e) (x:A)`]
   ALGEBRA_TRACE_FREE_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`integer_mod_ring p`;
                 `algebra_trace (integer_mod_ring p,quotient_ring r P)
                    (ring_of_int (quotient_ring r P)) (ring_coset r P (x:A))`;
                 `{l:num | l < e}`] RING_SUM_CONST) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT;
              ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  TRANS_TAC EQ_TRANS
   `ring_sum (integer_mod_ring p) {l:num | l < e}
     (\l. ring_sum (integer_mod_ring p) {j:num | j < f}
       (\j. mul_matrix
              (integer_mod_ring p,quotient_ring r (ideal_pow r P e))
              (ring_of_int (quotient_ring r (ideal_pow r P e))) (f * e) G
              (ring_coset r (ideal_pow r P e) (x:A))
              (j + f * l) (j + f * l)))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_MOD_DIV o rand o snd) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MUL_MATRIX_IN_CARRIER THEN
      ASM_SIMP_TAC[ADD_MULT_LT_MULT];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `s:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s MOD f + f * s DIV f = s` (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`s:num`; `f:num`] DIVISION) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MULT_CLAUSES; CONJUNCT1 LT]; ALL_TAC] THEN
    ARITH_TAC;
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `l:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[]] THEN
  SUBGOAL_THEN `ring_of_num r p IN (P:A->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `1:num`; `e:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism(integer_mod_ring p,quotient_ring r P)
      (ring_of_int (quotient_ring r P):int->A->bool)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT;
                 RING_CHAR_QUOTIENT_RING_DIVIDES];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ring_of_int (quotient_ring r P):int->A->bool`;
    `integer_mod_ring p`; `quotient_ring r (P:A->bool)`;
    `f:num`; `g:num->A->bool`; `ring_coset r P (x:A)`]
   ALGEBRA_TRACE_FREE_BASIS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[mul_matrix] THEN
  SUBGOAL_THEN `~(f = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(G:num->A->bool) (j + f * l) =
    ring_coset r (ideal_pow r P e) (ring_mul r (ring_pow r t l) (b j))`
  SUBST1_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES;
             ASSUME `j:num < f`; ASSUME `~(f = 0)`];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(MATCH_MP
   (ASSUME `!j. j < f ==> ring_coset r P ((b:num->A) j) = g j`)
   (ASSUME `j:num < f`))] THEN
  ASM_SIMP_TAC[QUOTIENT_RING_MUL; RING_IDEAL_IDEAL_POW; RING_MUL; RING_POW] THEN
  ABBREV_TAC
   `C = basis_coordinates
          (integer_mod_ring p,quotient_ring r (ideal_pow r P e))
          (ring_of_int (quotient_ring r (ideal_pow r P e))) (f * e) G
          (ring_coset r (ideal_pow r P e)
            (ring_mul r x (ring_mul r (ring_pow r t l) ((b:num->A) j))))` THEN
  MP_TAC(ISPECL
   [`ring_of_int (quotient_ring r (ideal_pow r P e)):int->A->bool`;
    `integer_mod_ring p`; `quotient_ring r (ideal_pow r (P:A->bool) e)`;
    `f * e:num`; `G:num->A->bool`;
    `ring_coset r (ideal_pow r P e)
       (ring_mul r x (ring_mul r (ring_pow r t l) ((b:num->A) j)))`]
   BASIS_COORDINATES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; RING_IDEAL_IDEAL_POW; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_MUL; RING_POW];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`r:A ring`; `ideal_pow r (P:A->bool) e`; `f * e:num`;
    `\s. ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f))`;
    `G:num->A->bool`; `C:num->int`] QUOTIENT_RING_LINCOMB_LIFT)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RING_MUL; RING_POW] THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `ring_sub r (ring_mul r x (ring_mul r (ring_pow r t l) ((b:num->A) j)))
      (ring_sum r {s:num | s < f * e}
        (\s. ring_mul r (ring_of_int r ((C:num->int) s))
              (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f))))) IN
    ideal_pow r P e`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) RING_COSET_EQ o snd) THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RING_SUM; RING_MUL; RING_POW];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `t:A`; `p:num`; `f:num`;
                 `g:num->A->bool`; `b:num->A`; `e:num`; `l:num`;
                 `C:num->int`] DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT) THEN
  ASM_SIMP_TAC[LT_IMP_LE] THEN ANTS_TAC THENL
   [MATCH_MP_TAC(MESON[IN_RING_IDEAL_SUB; RING_IDEAL_IDEAL_POW;
                       RING_RULE `ring_sub r a (ring_sub r a (b:A)) = b`]
     `!a b:A. a IN ring_carrier r /\ b IN ring_carrier r /\
              a IN ideal_pow r P l /\ ring_sub r a b IN ideal_pow r P l
              ==> b IN ideal_pow r P l`) THEN
    EXISTS_TAC
     `ring_mul r x (ring_mul r (ring_pow r t l) ((b:num->A) j))` THEN
    ASM_SIMP_TAC[RING_MUL; RING_POW; RING_SUM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN
      ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW] THEN
      MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN
      ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RING_POW_IN_IDEAL_POW];
      MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `l:num`; `e:num`]
        IDEAL_POW_ANTIMONO) THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; LT_IMP_LE] THEN ASM SET_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `t:A`; `f:num`; `g:num->A->bool`;
                 `b:num->A`; `e:num`; `C:num->int`; `l:num`;
                 `ring_mul r x ((b:num->A) j)`]
    DEDEKIND_IDEAL_POW_LEVEL_COEFFS) THEN
  ASM_SIMP_TAC[RING_MUL] THEN ANTS_TAC THENL
   [SUBGOAL_THEN
     `ring_mul r (ring_pow r t l) (ring_mul r x ((b:num->A) j)) =
      ring_mul r x (ring_mul r (ring_pow r t l) (b j))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul r u (ring_mul r x v) = ring_mul r x (ring_mul r u (v:A))`) THEN
      ASM_SIMP_TAC[RING_POW];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `l + 1`; `e:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
    DISCH_TAC] THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL
   [`ring_of_int (quotient_ring r P):int->A->bool`;
    `integer_mod_ring p`; `quotient_ring r (P:A->bool)`;
    `f:num`; `g:num->A->bool`; `ring_coset r P (ring_mul r x ((b:num->A) j))`;
    `\i. (C:num->int) (i + f * l)`] BASIS_COORDINATES_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Traces modulo p on a ring free over Z with pr = P^e INTER Q.              *)
(* ------------------------------------------------------------------------- *)

(* For an ideal i containing the prime p of a ring r free over Z, r/i is a   *)
(* finite algebra over Z/pZ with a free basis.                               *)
let FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS = prove
 (`!r:A ring n w p i.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ prime p /\
        ring_ideal r i /\ ring_of_num r p IN i
        ==> FINITE(ring_carrier(quotient_ring r i)) /\
            ring_homomorphism(integer_mod_ring p,quotient_ring r i)
                             (ring_of_int(quotient_ring r i)) /\
            ?m g. free_basis (integer_mod_ring p,quotient_ring r i)
                             (ring_of_int(quotient_ring r i)) m g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `j = ideal_generated r {ring_of_num r p:A}` THEN
  SUBGOAL_THEN `ring_ideal r (j:A->bool) /\ (j:A->bool) SUBSET i`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(ring_carrier(quotient_ring r (j:A->bool)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_int(quotient_ring r (j:A->bool))`;
                   `integer_mod_ring p`; `quotient_ring r (j:A->bool)`;
                   `n:num`; `\i. ring_coset r j ((w:num->A) i)`]
      FREE_BASIS_HAS_SIZE) THEN
    EXPAND_TAC "j" THEN
    ASM_SIMP_TAC[FREE_BASIS_QUOTIENT_RING_INTEGER_MOD;
                 RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING;
                 FINITE_INTEGER_MOD_RING; PRIME_IMP_NZ] THEN
    SIMP_TAC[HAS_SIZE];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN
    EXISTS_TAC `j:A->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT;
                 RING_CHAR_QUOTIENT_RING_DIVIDES];
    STRIP_TAC THEN EXISTS_TAC
     `extension_degree (integer_mod_ring p,quotient_ring r i)
                       (ring_of_int(quotient_ring r (i:A->bool)))` THEN
    MATCH_MP_TAC FREE_BASIS_EXISTS THEN
    EXISTS_TAC `ring_carrier(quotient_ring r (i:A->bool))` THEN
    ASM_REWRITE_TAC[ring_spanning; RING_SPAN_SELF; SUBSET_REFL;
                    FIELD_INTEGER_MOD_RING]]);;

(* For pr = j1 INTER j2 with j1 + j2 = r, the trace of r modulo p is the    *)
(* sum of the traces of r/j1 and r/j2 over Z/pZ (r/pr = r/j1 x r/j2).       *)
let ALGEBRA_TRACE_INTEGER_MOD_SPLIT = prove
 (`!r:A ring n w p j1 j2 y.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ prime p /\
        ring_ideal r j1 /\ ring_ideal r j2 /\
        ring_setadd r j1 j2 = ring_carrier r /\
        j1 INTER j2 = ideal_generated r {ring_of_num r p} /\
        y IN ring_carrier r
        ==> algebra_trace (integer_ring,r) (ring_of_int r) y rem &p =
            ring_add (integer_mod_ring p)
             (algebra_trace (integer_mod_ring p,quotient_ring r j1)
                (ring_of_int (quotient_ring r j1)) (ring_coset r j1 y))
             (algebra_trace (integer_mod_ring p,quotient_ring r j2)
                (ring_of_int (quotient_ring r j2)) (ring_coset r j2 y))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `j = ideal_generated r {ring_of_num r p:A}` THEN
  SUBGOAL_THEN `ring_ideal r (j:A->bool) /\ ring_of_num r p IN j`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC THEN
    REWRITE_TAC[SING_SUBSET; IN_SING; RING_OF_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_of_num r p IN (j1:A->bool) /\ ring_of_num r p IN j2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `j1 INTER j2 = (j:A->bool)` THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `p:num`; `j2:A->bool`]
    FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS) THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `p:num`; `j1:A->bool`]
    FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `n1:num` (X_CHOOSE_TAC `g1:num->A->bool`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `n2:num` (X_CHOOSE_TAC `g2:num->A->bool`)))) THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `p:num`; `y:A`]
    ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`r:A ring`; `j1:A->bool`; `j2:A->bool`]
    RING_ISOMORPHISM_QUOTIENT_RING_INTER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(A->bool)->(A->bool)#(A->bool)`
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p`; `quotient_ring r (j:A->bool)`;
    `prod_ring (quotient_ring r j1) (quotient_ring r (j2:A->bool))`;
    `ring_of_int(quotient_ring r (j:A->bool))`;
    `h:(A->bool)->(A->bool)#(A->bool)`;
    `n:num`; `\i. ring_coset r j ((w:num->A) i)`; `ring_coset r j (y:A)`]
   ALGEBRA_TRACE_ISOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "j" THEN
    ASM_SIMP_TAC[FREE_BASIS_QUOTIENT_RING_INTEGER_MOD;
                 RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING;
                 QUOTIENT_RING_CARRIER; RING_IDEAL_IDEAL_GENERATED] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `(h:(A->bool)->(A->bool)#(A->bool)) o
    ring_of_int (quotient_ring r j) =
    (\a. ring_of_int (quotient_ring r j1) a,
         ring_of_int (quotient_ring r j2) a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `a:int` THEN
    REWRITE_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_RING_OF_INT
      (MATCH_MP RING_HOMOMORPHISM_RING_COSET
        (ASSUME `ring_ideal r (j:A->bool)`)))] THEN
    ASM_SIMP_TAC[RING_OF_INT; PAIR_EQ] THEN
    REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT
      (MATCH_MP RING_HOMOMORPHISM_RING_COSET
        (ASSUME `ring_ideal r (j1:A->bool)`))] THEN
    REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT
      (MATCH_MP RING_HOMOMORPHISM_RING_COSET
        (ASSUME `ring_ideal r (j2:A->bool)`))];
    ALL_TAC] THEN
  MATCH_MP_TAC ALGEBRA_TRACE_PROD_RING THEN
  MAP_EVERY EXISTS_TAC
   [`n1:num`; `n2:num`; `g1:num->A->bool`; `g2:num->A->bool`] THEN
  ASM_SIMP_TAC[QUOTIENT_RING_CARRIER] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* With pr = P^e INTER Q and P^e + Q = r, the traces of the elements of Q    *)
(* are all divisible by p iff p divides e: on Q the trace modulo p is e      *)
(* times the trace of the residue field r/P, which is not identically zero.  *)
let ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES = prove
 (`!r:A ring n w p P Q e.
        dedekind_domain r /\ free_basis (integer_ring,r) (ring_of_int r) n w /\
        prime p /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\ ring_ideal r Q /\
        ring_setadd r (ideal_pow r P e) Q = ring_carrier r /\
        ideal_pow r P e INTER Q = ideal_generated r {ring_of_num r p}
        ==> ((!x. x IN Q
                  ==> &p divides
                      algebra_trace (integer_ring,r) (ring_of_int r) x) <=>
             p divides e)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `ring_of_num r p IN ideal_pow r (P:A->bool) e /\
                ring_of_num r p IN Q`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!x:A s t u. s INTER t = u /\ x IN u ==> x IN s /\ x IN t`) THEN
    EXISTS_TAC `ideal_generated r {ring_of_num r p:A}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN
    REWRITE_TAC[SING_SUBSET; IN_SING; RING_OF_NUM];
    ALL_TAC] THEN
  ASM_CASES_TAC `e = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[DIVIDES_0] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `w:num->A`; `1`] THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_POW_1; ARITH_EQ] THEN
    UNDISCH_TAC
     `ideal_pow r P 0 INTER Q = ideal_generated r {ring_of_num r p:A}` THEN
    REWRITE_TAC[IDEAL_POW_0] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_of_num r p IN (P:A->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `1`; `e:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `p:num`; `P:A->bool`]
    FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:num` (X_CHOOSE_TAC `g:num->A->bool`)))) THEN
  SUBGOAL_THEN `field(quotient_ring r (P:A->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_QUOTIENT_RING; DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN Q
          ==> algebra_trace (integer_ring,r) (ring_of_int r) x rem &p =
              ring_mul (integer_mod_ring p)
                (ring_of_num (integer_mod_ring p) e)
                (algebra_trace (integer_mod_ring p,quotient_ring r P)
                   (ring_of_int (quotient_ring r P)) (ring_coset r P x))`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `p:num`;
                   `ideal_pow r (P:A->bool) e`; `Q:A->bool`; `x:A`]
      ALGEBRA_TRACE_INTEGER_MOD_SPLIT) THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `ring_coset r Q (x:A) = ring_0(quotient_ring r Q)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `Q:A->bool`] RING_HOMOMORPHISM_RING_COSET) THEN
    MP_TAC(ISPECL [`quotient_ring r (Q:A->bool)`; `p:num`]
      RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT) THEN
    ASM_SIMP_TAC[RING_CHAR_QUOTIENT_RING_DIVIDES] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ALGEBRA_TRACE_0] THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `p:num`; `f:num`;
                   `g:num->A->bool`; `e:num`; `x:A`]
      DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RING_ADD_RZERO THEN
    SIMP_TAC[RING_MUL; RING_OF_NUM; ALGEBRA_TRACE_NORM_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN ring_carrier(integer_mod_ring p)
        ==> (ring_mul (integer_mod_ring p) (ring_of_num (integer_mod_ring p) e)
               t = ring_0 (integer_mod_ring p) <=>
             p divides e \/ t = ring_0 (integer_mod_ring p))`
  (LABEL_TAC "mul") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`integer_mod_ring p`; `ring_of_num (integer_mod_ring p) e`;
                   `t:int`] INTEGRAL_DOMAIN_MUL_EQ_0) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; FIELD_INTEGER_MOD_RING;
                 RING_OF_NUM] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[RING_OF_NUM_EQ_0; INTEGER_MOD_RING_CHAR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN Q
          ==> (&p divides algebra_trace (integer_ring,r) (ring_of_int r) x <=>
               p divides e \/
               algebra_trace (integer_mod_ring p,quotient_ring r P)
                 (ring_of_int (quotient_ring r P)) (ring_coset r P x) =
               ring_0 (integer_mod_ring p))`
  (LABEL_TAC "dvd") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM INT_REM_EQ_0] THEN
    USE_THEN "key" (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[SYM(SPEC `p:num`
      (CONJUNCT1(CONJUNCT2(CONJUNCT2 INTEGER_MOD_RING_CLAUSES))))] THEN
    USE_THEN "mul" MATCH_MP_TAC THEN
    REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER];
    ALL_TAC] THEN
  EQ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(~q ==> ~p) ==> p ==> q`) THEN DISCH_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  MP_TAC(ISPECL [`integer_mod_ring p`; `quotient_ring r (P:A->bool)`;
                 `ring_of_int (quotient_ring r (P:A->bool))`; `f:num`;
                 `g:num->A->bool`] ALGEBRA_TRACE_FINITE_FIELD_NONZERO) THEN
  ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING] THEN
  ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; EXISTS_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `ring_setadd r (ideal_pow r P e) Q = ring_carrier(r:A ring)` THEN
  REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `ring_1 r:A`) THEN
  REWRITE_TAC[RING_1; ring_setadd; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` (X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u:A) IN ring_carrier r /\ (v:A) IN ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET; RING_IDEAL_IDEAL_POW];
    ALL_TAC] THEN
  EXISTS_TAC `ring_mul r a v:A` THEN
  SUBGOAL_THEN `ring_mul r a v IN (Q:A->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[IN_RING_IDEAL_LMUL]; ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN `ring_coset r P (ring_mul r a v) = ring_coset r P (a:A)`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[RING_COSET_EQ; RING_MUL] THEN
  SUBGOAL_THEN `ring_sub r (ring_mul r a v) a = ring_neg r (ring_mul r a (u:A))`
  SUBST1_TAC THENL
   [MP_TAC(RING_RULE
     `ring_1 r = ring_add r u v
      ==> ring_sub r (ring_mul r a v) a = ring_neg r (ring_mul r a (u:A))`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC IN_RING_IDEAL_NEG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `1`; `e:num`]
    IDEAL_POW_ANTIMONO) THEN
  ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]);;

(* The tame case: some element of Q has a trace prime to p.                  *)
let ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW = prove
 (`!r:A ring n w p P Q e.
        dedekind_domain r /\ free_basis (integer_ring,r) (ring_of_int r) n w /\
        prime p /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\ ring_ideal r Q /\
        ring_setadd r (ideal_pow r P e) Q = ring_carrier r /\
        ideal_pow r P e INTER Q = ideal_generated r {ring_of_num r p} /\
        ~(p divides e)
        ==> ?x. x IN Q /\
                ~(&p divides
                  algebra_trace (integer_ring,r) (ring_of_int r) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The different: P^e divides D iff p divides e.                             *)
(* ------------------------------------------------------------------------- *)

(* With pO = P^e Q, Q prime to P: D SUBSET P^e iff x D SUBSET pO for all x  *)
(* in Q (cancel Q), iff x / p is in the codifferent for all x in Q, iff p   *)
(* divides the traces of all elements of Q, iff p divides e.                *)
let NUMBER_FIELD_DIFFERENT_WILD = prove
 (`!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        prime p /\ ring_of_num k p IN P
        ==> (number_field_different (subfield_generated k {ring_0 k},k) I SUBSET
             ideal_pow (ring_of_integers k) P
               (ramification_index (integer_ring,ring_of_integers k)
                                   (ring_of_int k) P) <=>
             p divides ramification_index (integer_ring,ring_of_integers k)
                                           (ring_of_int k) P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I` THEN
  SUBGOAL_THEN `~(P = {ring_0 k:A})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ring_of_num k p IN {ring_0 k:A}` THEN
    REWRITE_TAC[IN_SING; RING_OF_NUM_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
    SIMP_TAC[DIVIDES_ZERO] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
    RAMIFICATION_INDEX_PRIME) THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`]
    RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
  ABBREV_TAC `e = ramification_index (integer_ring,ring_of_integers k)
                    (ring_of_int k) (P:A->bool)` THEN
  ABBREV_TAC
   `q = ideal_generated (ring_of_integers k) {ring_of_num k p:A}` THEN
  STRIP_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL o
    check (fun th ->
      concl th = `prime_ideal (ring_of_integers k) (P:A->bool)`)) THEN
  SUBGOAL_THEN `maximal_ideal (ring_of_integers k) (P:A->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers k) (q:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. q SUBSET ideal_pow (ring_of_integers (k:A ring)) P m <=> m <= e`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_IDEAL_SUBSET_POW_VALUATION; RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?Q. ring_ideal (ring_of_integers k) Q /\
        ideal_prod (ring_of_integers k)
          (ideal_pow (ring_of_integers k) P e) Q = (q:A->bool)`
  (X_CHOOSE_THEN `Q:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pq")))
  THENL
   [EXISTS_TAC
     `ideal_quotient (ring_of_integers k) q
        (ideal_pow (ring_of_integers k) (P:A->bool) e)` THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_QUOTIENT; RING_IDEAL_IMP_SUBSET;
                 RING_IDEAL_IDEAL_POW] THEN
    MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((Q:A->bool) SUBSET P)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC e` o check (is_forall o concl)) THEN
    REWRITE_TAC[ARITH_RULE `~(SUC e <= e)`] THEN
    USE_THEN "pq" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IDEAL_POW_SUC] THEN
    TRANS_TAC SUBSET_TRANS
     `ideal_prod (ring_of_integers k)
        (ideal_pow (ring_of_integers k) P e) (P:A->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC(SET_RULE `s = t ==> (s:A->bool) SUBSET t`) THEN
      MATCH_MP_TAC IDEAL_PROD_COMM THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Q = {ring_0 k:A})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~({ring_0 k:A} SUBSET P)` THEN REWRITE_TAC[SING_SUBSET] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`]
      IN_RING_IDEAL_0) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_setadd (ring_of_integers k) (ideal_pow (ring_of_integers k) P e) Q =
    ring_carrier(ring_of_integers k) /\
    ideal_pow (ring_of_integers k) P e INTER Q = (q:A->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `Q:A->bool`;
                     `e:num`; `1:num`] COMAXIMAL_IDEAL_POW) THEN
      ASM_SIMP_TAC[IDEAL_POW_1; MAXIMAL_IDEAL_COMAXIMAL];
      DISCH_TAC THEN USE_THEN "pq" (SUBST1_TAC o SYM) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_PROD_COMAXIMAL THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`; `p:num`;
                 `P:A->bool`; `Q:A->bool`; `e:num`]
    ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `!x:A. x IN Q ==> x IN ring_carrier(ring_of_integers k) /\
                     x IN ring_carrier k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET; RING_OF_INTEGERS_SUBSET];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `!x:A. x IN Q
          ==> !d. d IN number_field_different
                         (subfield_generated k {ring_0 k},k) I
                  ==> ring_mul k x d IN (q:A->bool)` THEN
  CONJ_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      X_GEN_TAC `d:A` THEN DISCH_TAC THEN
      USE_THEN "pq" (SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN `(d:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET;
                      RING_IDEAL_NUMBER_FIELD_DIFFERENT];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_mul k x d = ring_mul (ring_of_integers k) d (x:A)`
      SUBST1_TAC THENL
       [REWRITE_TAC[RING_OF_INTEGERS] THEN MATCH_MP_TAC RING_MUL_SYM THEN
        ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC[] THEN
      ASM SET_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `Q:A->bool`;
                     `number_field_different
                        (subfield_generated k {ring_0 k},k) I:A->bool`;
                     `ideal_pow (ring_of_integers k) P e:A->bool`]
        DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW; RING_IDEAL_NUMBER_FIELD_DIFFERENT;
                      RING_OF_INTEGERS] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN
       `ideal_prod (ring_of_integers k) Q
          (ideal_pow (ring_of_integers k) P e) = (q:A->bool)`
      SUBST1_TAC THENL
       [USE_THEN "pq" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN
        ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW];
        ALL_TAC] THEN
      MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `!x:A. x IN Q
          ==> !y. y IN ring_carrier(ring_of_integers k)
                  ==> &p divides
                      algebra_trace (integer_ring,ring_of_integers k)
                        (ring_of_int k) (ring_mul k x y)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `p:num`; `x:A`]
      NUMBER_FIELD_CODIFFERENT_DIV_NUM) THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_0 k}:A ring`; `k:A ring`;
                   `I:A->A`; `ring_of_num k p:A`; `x:A`]
      NUMBER_FIELD_CODIFFERENT_DIV) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
      ASM_SIMP_TAC[IN_SUBRING_NUM; RING_OF_INTEGERS_SUBRING; RING_OF_NUM_EQ_0;
                   DIVIDES_ZERO; PRIME_IMP_NZ; FIELD_SUBFIELD_GENERATED;
                   NUMBER_FIELD_IMP_FIELD;
                   RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ASSUME
       `ideal_generated (ring_of_integers k) {ring_of_num k p:A} = q`]];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `ring_1 k:A`) THEN
    ASM_SIMP_TAC[IN_SUBRING_1; RING_OF_INTEGERS_SUBRING; RING_MUL_RID];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `Q:A->bool`; `x:A`; `y:A`]
      IN_RING_IDEAL_RMUL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS]]);;

(* If p does not divide e(P) then the different is not contained in P^e(P):  *)
(* the exponent of P in the different is e(P) - 1 (tame ramification).       *)
let NUMBER_FIELD_DIFFERENT_TAME = prove
 (`!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        prime p /\ ring_of_num k p IN P /\
        ~(p divides ramification_index (integer_ring,ring_of_integers k)
                                        (ring_of_int k) P)
        ==> ~(number_field_different (subfield_generated k {ring_0 k},k) I
              SUBSET
              ideal_pow (ring_of_integers k) P
               (ramification_index (integer_ring,ring_of_integers k)
                                   (ring_of_int k) P))`,
  MESON_TAC[NUMBER_FIELD_DIFFERENT_WILD]);;

(* ------------------------------------------------------------------------- *)
(* The exponent of P in the different.                                       *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q,
    NUMBER_FIELD_DIFFERENT_VALUATION_WILD_Q = (CONJ_PAIR o prove)
 (`(!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        prime p /\ ring_of_num k p IN P
        ==> ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) P - 1 <=
            ideal_valuation (ring_of_integers k) P
              (number_field_different (subfield_generated k {ring_0 k},k) I) /\
            (ideal_valuation (ring_of_integers k) P
               (number_field_different (subfield_generated k {ring_0 k},k) I) =
             ramification_index (integer_ring,ring_of_integers k)
               (ring_of_int k) P - 1 <=>
             ~(p divides ramification_index (integer_ring,ring_of_integers k)
                           (ring_of_int k) P))) /\
   (!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        prime p /\ ring_of_num k p IN P
        ==> (ramification_index (integer_ring,ring_of_integers k)
               (ring_of_int k) P <=
             ideal_valuation (ring_of_integers k) P
               (number_field_different
                  (subfield_generated k {ring_0 k},k) I) <=>
             p divides ramification_index (integer_ring,ring_of_integers k)
                         (ring_of_int k) P))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> q /\ r) ==> (p ==> q) /\ (p ==> r)`) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(P = {ring_0 k:A})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ring_of_num k p IN {ring_0 k:A}` THEN
    REWRITE_TAC[IN_SING; RING_OF_NUM_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
    SIMP_TAC[DIVIDES_ZERO] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`]
    NUMBER_FIELD_DIFFERENT_WILD) THEN
  SUBGOAL_THEN
   `number_field_different (subfield_generated k {ring_0 k},k) I SUBSET
    ideal_pow (ring_of_integers k) P
      (ramification_index (integer_ring,ring_of_integers k)
         (ring_of_int k) (P:A->bool) - 1)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`subfield_generated k {ring_0 k}:A ring`; `k:A ring`;
                   `I:A->A`; `P:A->bool`]
      NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION) THEN
    ASM_SIMP_TAC[RAMIFICATION_INDEX_PRIME_SUBFIELD; FIELD_SUBFIELD_GENERATED;
                 NUMBER_FIELD_IMP_FIELD; RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
                 PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`]
    NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                 `number_field_different
                    (subfield_generated k {ring_0 k},k) I:A->bool`]
    DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_NUMBER_FIELD_DIFFERENT;
               NUMBER_FIELD_DIFFERENT_NONZERO; FIELD_SUBFIELD_GENERATED;
               NUMBER_FIELD_IMP_FIELD; RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
               RING_OF_INTEGERS] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_CASES_TAC
   `p divides ramification_index (integer_ring,ring_of_integers k)
                (ring_of_int k) (P:A->bool)` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The exponent of p in the discriminant.                                    *)
(* ------------------------------------------------------------------------- *)

(* The exponent of p in the norm of an ideal j: the sum of f(P) v_P(j) over *)
(* the primes P above p (from N(j) = prod N(P)^v_P(j) and N(P) = q^f(P) for *)
(* the prime q below P).                                                     *)
let NUMBER_FIELD_IDEAL_NORM_PRIME_EXPONENT = prove
 (`!k:A ring j p.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        ~(j = {ring_0 k}) /\ prime p
        ==> index p (ideal_norm (ring_of_integers k) j) =
            nsum {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
                 (\P. residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) P *
                      ideal_valuation (ring_of_integers k) P j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
    IDEAL_NORM_FACTORIZATION) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
    DEDEKIND_IDEAL_FACTORIZATION) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS; RING_OF_INTEGERS_FINITE_QUOTIENT] THEN
  ABBREV_TAC
   `S = {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             (j:A->bool) SUBSET P}` THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k:A})
        ==> ~(ideal_norm (ring_of_integers k) P = 0) /\
            index p (ideal_norm (ring_of_integers k) P) =
            if ring_of_num k p IN P
            then residue_degree (integer_ring,ring_of_integers k)
                   (ring_of_int k) P
            else 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`]
      RING_OF_INTEGERS_PRIME_IDEAL_ABOVE) THEN
    ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC)
      (LABEL_TAC "uniq")) THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `q:num`]
      RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ; INDEX_EXP; INDEX_PRIME] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES];
      COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
      USE_THEN "uniq" (MP_TAC o SPECL [`p:num`; `q:num`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. P IN S ==> prime_ideal (ring_of_integers k) P /\
                   ~(P = {ring_0 k:A}) /\ (j:A->bool) SUBSET P`
  ASSUME_TAC THENL [EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INDEX_NPRODUCT o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[EXP_EQ_0] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[INDEX_EXP] THEN
  ABBREV_TAC
   `U = {P | P IN S /\ ring_of_num k p IN (P:A->bool)}` THEN
  TRANS_TAC EQ_TRANS
   `nsum U (\P. residue_degree (integer_ring,ring_of_integers k)
                  (ring_of_int k) P *
                ideal_valuation (ring_of_integers k) P (j:A->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_SUPERSET THEN EXPAND_TAC "U" THEN
    REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    CONJ_TAC THEN X_GEN_TAC `P:A->bool` THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[MULT_CLAUSES] THEN ARITH_TAC;
      ASM_CASES_TAC `ring_of_num k p IN (P:A->bool)` THENL
       [ASM_MESON_TAC[]; ASM_SIMP_TAC[MULT_CLAUSES]]];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
  EXPAND_TAC "U" THEN EXPAND_TAC "S" THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ring_of_num k p IN {ring_0 k:A}` THEN
    REWRITE_TAC[IN_SING; RING_OF_NUM_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
    SIMP_TAC[DIVIDES_ZERO] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[MULT_EQ_0] THEN DISJ2_TAC THEN
  SUBGOAL_THEN `~(P = {ring_0 k:A})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ring_of_num k p IN {ring_0 k:A}` THEN
    REWRITE_TAC[IN_SING; RING_OF_NUM_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
    SIMP_TAC[DIVIDES_ZERO] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `j:A->bool`]
    IDEAL_VALUATION_EQ_0) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_MESON_TAC[SUBSET]);;

let NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT = prove
 (`!k:A ring p.
        number_field k /\ prime p
        ==> index p (num_of_int(abs(number_field_discriminant k))) =
            nsum {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
                 (\P. residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) P *
                      ideal_valuation (ring_of_integers k) P
                        (number_field_different
                           (subfield_generated k {ring_0 k},k) I))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM NUMBER_FIELD_IDEAL_NORM_DIFFERENT] THEN
  MATCH_MP_TAC NUMBER_FIELD_IDEAL_NORM_PRIME_EXPONENT THEN
  ASM_SIMP_TAC[RING_IDEAL_NUMBER_FIELD_DIFFERENT;
               NUMBER_FIELD_DIFFERENT_NONZERO; FIELD_SUBFIELD_GENERATED;
               NUMBER_FIELD_IMP_FIELD; RING_HOMOMORPHISM_SUBFIELD_INCLUSION]);;

let NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_TAME = prove
 (`!k:A ring p.
        number_field k /\ prime p /\
        (!P. prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
             ==> ~(p divides ramification_index
                               (integer_ring,ring_of_integers k)
                               (ring_of_int k) P))
        ==> index p (num_of_int(abs(number_field_discriminant k))) =
            nsum {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
                 (\P. residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) P *
                      (ramification_index (integer_ring,ring_of_integers k)
                         (ring_of_int k) P - 1))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q]);;

let NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_GE = prove
 (`!k:A ring p.
        number_field k /\ prime p
        ==> nsum {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
                 (\P. residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) P *
                      (ramification_index (integer_ring,ring_of_integers k)
                         (ring_of_int k) P - 1))
            <= index p (num_of_int(abs(number_field_discriminant k))) /\
            (nsum {P | prime_ideal (ring_of_integers k) P /\
                       ring_of_num k p IN P}
                  (\P. residue_degree (integer_ring,ring_of_integers k)
                         (ring_of_int k) P *
                       (ramification_index (integer_ring,ring_of_integers k)
                          (ring_of_int k) P - 1)) =
             index p (num_of_int(abs(number_field_discriminant k))) <=>
             !P. prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
                 ==> ~(p divides ramification_index
                                   (integer_ring,ring_of_integers k)
                                   (ring_of_int k) P))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`]
    RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `ps = {P | prime_ideal (ring_of_integers k) P /\
             ring_of_num k p IN (P:A->bool)}` THEN
  SUBGOAL_THEN
   `!P:A->bool. P IN ps
        ==> 1 <= residue_degree (integer_ring,ring_of_integers k)
                   (ring_of_int k) P /\
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) P - 1 <=
            ideal_valuation (ring_of_integers k) P
              (number_field_different (subfield_generated k {ring_0 k},k) I) /\
            (ideal_valuation (ring_of_integers k) P
               (number_field_different (subfield_generated k {ring_0 k},k) I) =
             ramification_index (integer_ring,ring_of_integers k)
               (ring_of_int k) P - 1 <=>
             ~(p divides ramification_index (integer_ring,ring_of_integers k)
                           (ring_of_int k) P))`
  ASSUME_TAC THENL
   [EXPAND_TAC "ps" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`]
      NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q) THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`]
      NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:A->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(ARITH_RULE `a < b ==> ~(a = b:num)`) THEN
    MATCH_MP_TAC NSUM_LT THEN ASM_SIMP_TAC[LE_MULT_LCANCEL] THEN
    EXISTS_TAC `P:A->bool` THEN
    SUBGOAL_THEN `(P:A->bool) IN ps` ASSUME_TAC THENL
     [EXPAND_TAC "ps" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
    X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN
     `prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN (P:A->bool)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(P:A->bool) IN ps` THEN EXPAND_TAC "ps" THEN
      SIMP_TAC[IN_ELIM_THM];
      ASM_MESON_TAC[]]]);;
