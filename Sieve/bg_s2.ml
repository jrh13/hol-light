(* ========================================================================= *)
(* Bounded gaps between primes, part 2: the sums S2.                         *)
(*                                                                           *)
(* S2(m) = sum of (sum_c Y c prod_{col_supp c} maynard_lfac h c p n)^2 over  *)
(* the n with N <= n < 2N, n == nu (mod W) and n + h m prime.                *)
(*                                                                           *)
(* * LAMBDA_EXPAND: the sieve weight of n is sum_{c'} [col_div h c' n]       *)
(*   maynard_lambda c', where maynard_lambda fam Y c' = prod_{col_supp c'}   *)
(*   (-p) sum_{c >= c'} Y c and col_div h c' n says that every p in col_supp *)
(*   c' divides n + h(c' p); S2_SQUARE expands the square into pairs (c1,    *)
(*   c2).                                                                    *)
(* * Local densities: PAIR_RESIDUE_CARD and RESIDUE_SQUARE_SUM count the     *)
(*   residues r mod prod P with no p in P dividing r + h m, colour by colour *)
(*   (maynard_sloc m p i j), using maynard_hdist (h i <> h j mod p).         *)
(*   S2_MAIN_IDENTITY:                                                       *)
(*     sum_{c1,c2} maynard_lambda c1 maynard_lambda c2 [maynard_pairok m c1  *)
(*     c2] /                                                                 *)
(*                 prod_{col_supp c1 UNION col_supp c2} (p - 1)              *)
(*       = sum_{a,b} Y a Y b prod_P maynard_sloc m p (a p) (b p) / (p - 1).  *)
(* * S2_MAIN_LOWER: grouping by col_strip m (colour m removed) and           *)
(*   OFFDIAG_STATES with the weights maynard_swt give the lower bound        *)
(*     sum_e prod_{col_supp e} (p^2 - p - 1)/(p - 1) T(e)^2 - error,         *)
(*   T(e) = sum_{col_strip m a = e} y a / prod_{col_supp a} (p - 1).         *)
(* * Primes: S2_COUNT_PI writes each count as a difference of pi_ap values   *)
(*   for the modulus W prod col_supp c and a residue coprime to it           *)
(*   (CRT_RESIDUE_EXISTS); S2_PAIR_ZERO, S2_PAIR_ERR; bv_disc x d b =        *)
(*   |pi(x;d,b) - pi(x)/phi(d)|; GENERIC_BV_SUM (one worst residue per       *)
(*   modulus).                                                               *)
(* * S2_ERROR_SUM: |S2(m) - X/phi(W) main| <= L^2 sum_t (k + 1)^(2|t|)       *)
(*   (bv_disc x2 + bv_disc x1), t SUBSET P with prod t < R^2, if             *)
(*   |maynard_lambda| <= L; MAYNARD_LAMBDA_BOUND: |maynard_lambda| <= ym     *)
(*   prod_P (1 + u) prod_P (1 + k u).                                        *)
(* ========================================================================= *)

needs "Sieve/bg_s1.ml";;
needs "Sieve/chen_sieve.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Expanding S2 over divisor colourings.                                     *)
(* ------------------------------------------------------------------------- *)

let col_div = new_definition
 `col_div (h:num->num) (c:num->num) n <=>
    !p. p IN col_supp c ==> p divides n + h(c p)`;;

let maynard_lambda = new_definition
 `maynard_lambda fam (Y:(num->num)->real) (c':num->num) =
    product (col_supp c') (\p. --(&p)) *
    sum {c | c IN fam /\ col_sub c' c} Y`;;

let LAMBDA_EXPAND = prove
 (`!h fam (Y:(num->num)->real) n.
     FINITE fam /\ (!c. c IN fam ==> FINITE(col_supp c))
     ==> sum fam (\c. Y c * product (col_supp c) (\p. maynard_lfac h c p n)) =
         sum {c' | ?c. c IN fam /\ col_sub c' c}
             (\c'. if col_div h c' n then maynard_lambda fam Y c' else &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fam:(num->num)->bool`; `Y:(num->num)->real`;
                 `\p:num. --(&p)`; `\p i. p divides n + (h:num->num) i`]
         SIEVE_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(a:real) = a' /\ (b:real) = b' ==> a = b ==> b' = a'`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[maynard_lambda; col_div] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_ELIM_THM];
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[maynard_lfac] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC]);;

let S2_SQUARE = prove
 (`!h fam (Y:(num->num)->real) A (Pr:num->bool).
     FINITE fam /\ (!c. c IN fam ==> FINITE(col_supp c)) /\ FINITE A
     ==> sum {n | n IN A /\ Pr n}
             (\n. sum fam
                    (\c. Y c * product (col_supp c) (\p. maynard_lfac h c p n))
                  pow 2) =
         sum {c' | ?c. c IN fam /\ col_sub c' c} (\c1.
           sum {c' | ?c. c IN fam /\ col_sub c' c} (\c2.
             maynard_lambda fam Y c1 * maynard_lambda fam Y c2 *
             &(CARD {n | n IN A /\ Pr n /\ col_div h c1 n /\
                     col_div h c2 n})))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_EXPAND] THEN
  SUBGOAL_THEN `FINITE {c' | ?c. c IN fam /\ col_sub c' (c:num->num)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_DOWN_COLOURINGS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {n:num | n IN A /\ Pr n}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SQUARE_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c1:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c2:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. (if col_div h c1 n then maynard_lambda fam (Y:(num->num)->real)
           c1 else &0) *
        (if col_div h c2 n then maynard_lambda fam Y c2 else &0) =
        (if col_div h c1 n /\
         col_div h c2 n then maynard_lambda fam Y c1 * maynard_lambda fam Y c2
         else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`col_div h c1 n`; `col_div h c2 n`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC; REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Local residue counts.                                                     *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_ADD_MOD = prove
 (`!p n x. ~(p = 0) ==> (p divides n + x <=> p divides n MOD p + x)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`n:num`; `p:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
    [CONJUNCT1 th]) THEN
  SPEC_TAC(`n MOD p`,`m:num`) THEN SPEC_TAC(`n DIV p`,`q:num`) THEN
  CONV_TAC NUMBER_RULE);;

let RED_RESIDUE_CARD = prove
 (`!p a b. ~(p = 0)
           ==> CARD {s | s < p /\ ~(p divides s + b)} = p - 1 /\
               CARD {s | s < p /\ ~(p divides s + b) /\ p divides s + a} =
               (if (a == b) (mod p) then 0 else 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{s | s < p /\ ~(p divides s + b)} =
                  {s | s < p} DIFF {s | s < p /\ p divides s + b}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RESIDUES_DIVIDING] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_DIFF o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; SING_SUBSET; IN_ELIM_THM; MOD_LT_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CARD_NUMSEG_LT; CARD_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s | s < p /\ ~(p divides s + b) /\ p divides s + a} =
    {s | s IN {s | s < p /\ p divides s + a} /\ ~(p divides s + b)}`
  SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RESIDUES_DIVIDING] THEN
  ABBREV_TAC `s0 = (p - a MOD p) MOD p` THEN
  SUBGOAL_THEN `p divides s0 + a` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `a:num`] RESIDUES_DIVIDING) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `p divides s0 + b` ASSUME_TAC THENL
     [UNDISCH_TAC `p divides s0 + a` THEN
       UNDISCH_TAC `(a:num == b) (mod p)` THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    SUBGOAL_THEN `{s | s IN {s0} /\ ~(p divides s + b)} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[CARD_CLAUSES]];
    SUBGOAL_THEN `~(p divides s0 + b)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((a:num == b) (mod p))` THEN
       REWRITE_TAC[] THEN
      UNDISCH_TAC `p divides s0 + a` THEN UNDISCH_TAC `p divides s0 + b` THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    SUBGOAL_THEN `{s | s IN {s0} /\ ~(p divides s + b)} = {s0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN ASM_MESON_TAC[];
      REWRITE_TAC[CARD_SING]]]);;

let LOCAL_PAIR_CARD = prove
 (`!h k m p i j.
     prime p /\ m IN 1..k /\ i <= k /\ j <= k /\
     (!u v. u IN 1..k /\ v IN 1..k /\ ~(u = v) ==> ~((h u == h v) (mod p)))
     ==> CARD {s | s < p /\ ~(p divides s + h m) /\
                   (~(i = 0) ==> p divides s + h i) /\
                   (~(j = 0) ==> p divides s + h j)} =
         (if i = 0 /\ j = 0 then p - 1
          else if (~(i = 0) ==> ~(i = m)) /\ (~(j = 0) ==> ~(j = m)) /\
                  (~(i = 0) /\ ~(j = 0) ==> i = j)
          then 1 else 0)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  SUBGOAL_THEN
   `!u. ~(u = 0) /\ u <= k ==> (((h:num->num) u == h m) (mod p) <=> u = m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONG_REFL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_CASES_TAC `j = 0` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[RED_RESIDUE_CARD];
    ASM_SIMP_TAC[RED_RESIDUE_CARD] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[RED_RESIDUE_CARD] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[TAUT `(a /\ b /\ c /\ c) <=> (a /\ b /\ c)`] THEN
    ASM_SIMP_TAC[RED_RESIDUE_CARD] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD(s:num->bool) = 0`) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `s:num` THEN STRIP_TAC THEN
  UNDISCH_TAC
   `!u v. u IN 1..k /\ v IN 1..k /\ ~(u = v)
          ==> ~(((h:num->num) u == h v) (mod p))` THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN
  ASM_REWRITE_TAC[IN_NUMSEG; NOT_IMP] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `p divides s + (h:num->num) i` THEN
  UNDISCH_TAC `p divides s + (h:num->num) j` THEN
  CONV_TAC NUMBER_RULE);;

let maynard_hdist = new_definition
 `maynard_hdist (h:num->num) k P <=>
    !p i j. p IN P /\ i IN 1..k /\ j IN 1..k /\ ~(i = j)
            ==> ~((h i == h j) (mod p))`;;

let maynard_pairok = new_definition
 `maynard_pairok m (c1:num->num) (c2:num->num) <=>
    (!p. p IN col_supp c1 ==> ~(c1 p = m)) /\
    (!p. p IN col_supp c2 ==> ~(c2 p = m)) /\
    (!p. p IN col_supp c1 /\ p IN col_supp c2 ==> c1 p = c2 p)`;;

let PAIR_RESIDUE_CARD = prove
 (`!h k m P c1 c2.
     FINITE P /\ (!p. p IN P ==> prime p) /\ maynard_hdist h k P /\
     m IN 1..k /\
     c1 IN col_set k P /\ c2 IN col_set k P
     ==> CARD {r | r < nproduct P (\p. p) /\
                   (!p. p IN P ==> ~(p divides r + h m)) /\
                   col_div h c1 r /\ col_div h c2 r} =
         (if maynard_pairok m c1 c2
          then nproduct (P DIFF (col_supp c1 UNION col_supp c2)) (\p. p - 1)
          else 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN P ==> ~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!p. ~(p IN P) ==> (c1:num->num) p = 0) /\
    (!p. ~(p IN P) ==> (c2:num->num) p = 0) /\
    (!p. c1 p <= k) /\ (!p. c2 p <= k)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(c1:num->num) IN col_set k P` THEN
    UNDISCH_TAC `(c2:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; IN_ELIM_THM] THEN MESON_TAC[LE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{r | r < nproduct P (\p. p) /\ (!p. p IN P ==> ~(p divides r + h m)) /\
         col_div h c1 r /\ col_div h c2 r} =
    {r | r < nproduct P (\p. p) /\
         !p. p IN P ==> (\p s. ~(p divides s + h m) /\
                               (~(c1 p = 0) ==> p divides s + h(c1 p)) /\
                               (~(c2 p = 0) ==> p divides s + h(c2 p)))
                        p (r MOD p)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; col_div; col_supp] THEN
    X_GEN_TAC `r:num` THEN
    ASM_SIMP_TAC[GSYM DIVIDES_ADD_MOD] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CRT_CARD o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `nproduct P (\p. if c1 p = 0 /\ c2 p = 0 then p - 1
                    else if (~(c1 p = 0) ==> ~(c1 p = m)) /\
                            (~(c2 p = 0) ==> ~(c2 p = m)) /\
                            (~(c1 p = 0) /\ ~(c2 p = 0) ==> c1 p = c2 p)
                    then 1 else 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NPRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC LOCAL_PAIR_CARD THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `maynard_hdist h k P` THEN REWRITE_TAC[maynard_hdist] THEN
    DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[maynard_pairok; col_supp; IN_ELIM_THM] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `nproduct P (\p. if c1 p = 0 /\ c2 p = 0 then p - 1 else 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(~((c1:num->num) p = 0) ==> ~(c1 p = m)) /\
        (~((c2:num->num) p = 0) ==> ~(c2 p = m)) /\
        (~(c1 p = 0) /\ ~(c2 p = 0) ==> c1 p = c2 p)`
      (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `nproduct (P DIFF ({p | ~(c1 p = 0)} UNION {p | ~(c2 p = 0)}))
               (\p. if c1 p = 0 /\ c2 p = 0 then p - 1 else 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_SUPERSET THEN
      REWRITE_TAC[SUBSET_DIFF] THEN X_GEN_TAC `p:num` THEN
      REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((c1:num->num) p = 0 /\ (c2:num->num) p = 0)`
        (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC NPRODUCT_EQ THEN
      REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
  STRIP_TAC THEN EXISTS_TAC `p:num` THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let SUM_RESIDUES_EXCEPT = prove
 (`!p b (f:num->real).
     ~(p = 0)
     ==> sum {s | s < p} (\s. if p divides s + b then &0 else f s) =
         sum {s | s < p} f - f((p - b MOD p) MOD p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum {s | s < p} (\s. if p divides s + b then &0 else f s) =
    sum {s | s < p} f -
    sum {s | s < p} (\s. if p divides s + b then f s else &0)`
  SUBST1_TAC THENL
   [SIMP_TAC[GSYM SUM_SUB; FINITE_NUMSEG_LT] THEN MATCH_MP_TAC SUM_EQ THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{s | s IN {s | s < p} /\ p divides s + b} =
                {(p - b MOD p) MOD p}`
  SUBST1_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[RESIDUES_DIVIDING];
    REWRITE_TAC[SUM_SING]]);;

let maynard_sloc = new_definition
 `maynard_sloc m p i j =
    if (i = 0 \/ i = m) /\ (j = 0 \/ j = m) then &p - &1
    else if (i = 0 \/ i = m) \/ (j = 0 \/ j = m) then --(&1)
    else if i = j then &p pow 2 - &p - &1
    else --(&p + &1)`;;

let LOCAL_RED_MAYNARD_LFAC_SUM = prove
 (`!h k m p (a:num->num) (b:num->num).
     prime p /\ m IN 1..k /\ a p <= k /\ b p <= k /\
     (!u v. u IN 1..k /\ v IN 1..k /\ ~(u = v) ==> ~((h u == h v) (mod p)))
     ==> sum {s | s < p} (\s. if p divides s + h m then &0
                              else maynard_lfac h a p s *
                              maynard_lfac h b p s) =
         maynard_sloc m p (a p) (b p)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  ASM_SIMP_TAC[SUM_RESIDUES_EXCEPT] THEN
  ABBREV_TAC `s0 = (p - (h:num->num) m MOD p) MOD p` THEN
  SUBGOAL_THEN `p divides s0 + (h:num->num) m` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `(h:num->num) m`] RESIDUES_DIVIDING) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. ~(u = 0) /\ u <= k ==> (p divides s0 + (h:num->num) u <=> u = m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(((h:num->num) u == h m) (mod p))` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
        UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> ~b`) THEN
        UNDISCH_TAC `p divides s0 + (h:num->num) m` THEN
        CONV_TAC NUMBER_RULE];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. ~(u = 0) /\ u <= k /\ ~(v = 0) /\ v <= k
          ==> ((h:num->num) u = h v <=> u = v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(((h:num->num) u == h v) (mod p))` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
          check (fun th -> can (find_term ((=) `1..k`)) (concl th))) THEN
        REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
        MESON_TAC[CONG_REFL]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[maynard_lfac; col_supp; IN_ELIM_THM] THEN
  ASM_CASES_TAC `(a:num->num) p = 0` THEN
  ASM_CASES_TAC `(b:num->num) p = 0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID] THENL
   [SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
    ASM_REWRITE_TAC[maynard_sloc] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[SUM_RESIDUES_ONE] THEN REWRITE_TAC[maynard_sloc] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(b:num->num) p = m` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[SUM_RESIDUES_ONE] THEN REWRITE_TAC[maynard_sloc] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(a:num->num) p = m` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `(h:num->num)((a:num->num) p)`;
                `(h:num->num)((b:num->num) p)`; `&1 - &p`; `&1 - &p`]
         SUM_RESIDUES_PAIR_GEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `1..k`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[maynard_sloc] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:num->num) p = b p` THENL
   [ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `(b:num->num) p = m` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(a:num->num) p = m` THEN
  ASM_CASES_TAC `(b:num->num) p = m` THEN
  ASM_REWRITE_TAC[] THEN TRY REAL_ARITH_TAC THEN
  UNDISCH_TAC `~((a:num->num) p = b p)` THEN ASM_REWRITE_TAC[]);;

let RESIDUE_SQUARE_SUM = prove
 (`!h k m P fam (Y:(num->num)->real).
     FINITE P /\ (!p. p IN P ==> prime p) /\ maynard_hdist h k P /\
     m IN 1..k /\
     fam SUBSET col_set k P
     ==> sum {r | r < nproduct P (\p. p) /\
                  (!p. p IN P ==> ~(p divides r + h m))}
             (\r. sum fam
                    (\c. Y c * product (col_supp c) (\p. maynard_lfac h c p r))
                  pow 2) =
         sum fam (\a. sum fam (\b.
           Y a * Y b * product P (\p. maynard_sloc m p (a p) (b p))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_COL_SET]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> ~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN fam ==> col_supp c SUBSET P /\ FINITE(col_supp c) /\ !p. c p <= k`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c:num->num) IN col_set k P` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `{p | ~((c:num->num) p = 0)} SUBSET P` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[FINITE_SUBSET];
      ASM_MESON_TAC[LE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {r | r < nproduct P (\p. p) /\
                (!p. p IN P ==> ~(p divides r + (h:num->num) m))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r:num | r < nproduct P (\p. p)}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SQUARE_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `b:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!r. (Y a * product (col_supp a) (\p. maynard_lfac h a p r)) *
        (Y b * product (col_supp b) (\p. maynard_lfac h b p r)) =
        Y a * Y b * (product (col_supp a) (\p. maynard_lfac h a p r) *
                     product (col_supp b) (\p. maynard_lfac h b p r))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL] THEN
  REPEAT AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {r | r < nproduct P (\p. p)}
        (\r. if (!p. p IN P ==> ~(p divides r + (h:num->num) m))
             then product (col_supp a) (\p. maynard_lfac h a p r) *
                  product (col_supp b) (\p. maynard_lfac h b p r)
             else &0)` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_ELIM_THM];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {r | r < nproduct P (\p. p)}
        (\r. product P (\p. (\p x. if p divides x + h m then &0
                                   else maynard_lfac h a p x *
                                   maynard_lfac h b p x)
                            p (r MOD p)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN
       `product (col_supp a) (\p. maynard_lfac h a p r) =
        product P (\p. maynard_lfac h a p r) /\
        product (col_supp b) (\p. maynard_lfac h b p r) =
        product P (\p. maynard_lfac h b p r)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_SUPERSET THEN
        ASM_SIMP_TAC[maynard_lfac] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN MATCH_MP_TAC PRODUCT_EQ THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[GSYM DIVIDES_ADD_MOD] THEN
      BINOP_TAC THEN MATCH_MP_TAC MAYNARD_LFAC_MOD THEN ASM_SIMP_TAC[];
      CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[PRODUCT_EQ_0] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[GSYM DIVIDES_ADD_MOD]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:num->bool`;
                 `\p x. if p divides x + (h:num->num) m then &0
                        else maynard_lfac h a p x * maynard_lfac h b p x`]
         CRT_SUM_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC LOCAL_RED_MAYNARD_LFAC_SUM THEN
  EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `maynard_hdist h k P` THEN REWRITE_TAC[maynard_hdist] THEN
  DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main identity for S2.                                                 *)
(* ------------------------------------------------------------------------- *)

let COL_SUB_SET = prove
 (`!k P (c:num->num) c'. c IN col_set k P /\ col_sub c' c
                         ==> c' IN col_set k P`,
  REWRITE_TAC[col_set; col_sub; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(c':num->num) p = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
  ASM_MESON_TAC[]);;

let PRODUCT_DIFF_SPLIT = prove
 (`!(f:A->real) s t.
     FINITE s /\ t SUBSET s
     ==> product s f = product (s DIFF t) f * product t f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `product ((s DIFF t) UNION (t:A->bool)) f` THEN CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PRODUCT_UNION THEN
  ASM_MESON_TAC[FINITE_DIFF; FINITE_SUBSET; SET_RULE
   `DISJOINT (s DIFF t) (t:A->bool)`]);;

let S2_MAIN_IDENTITY = prove
 (`!h k m P fam (Y:(num->num)->real).
     FINITE P /\ (!p. p IN P ==> prime p) /\ maynard_hdist h k P /\
     m IN 1..k /\
     fam SUBSET col_set k P
     ==> sum {c' | ?c. c IN fam /\ col_sub c' c} (\c1.
           sum {c' | ?c. c IN fam /\ col_sub c' c} (\c2.
             maynard_lambda fam Y c1 * maynard_lambda fam Y c2 *
             (if maynard_pairok m c1 c2
              then inv(product (col_supp c1 UNION col_supp c2) (\p. &p - &1))
              else &0))) =
         sum fam (\a. sum fam (\b.
           Y a * Y b *
           product P (\p. maynard_sloc m p (a p) (b p) / (&p - &1))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_COL_SET]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. c IN fam ==> FINITE(col_supp c)` ASSUME_TAC THENL
   [X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:num->num) IN col_set k P` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> &1 <= &p - &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `2 <= p` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ph = product P (\p. &p - &1)` THEN
  SUBGOAL_THEN `&0 < ph` ASSUME_TAC THENL
   [EXPAND_TAC "ph" THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 <= x ==> &0 < x`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->num`; `fam:(num->num)->bool`; `Y:(num->num)->real`;
                 `{r:num | r < nproduct P (\p. p)}`;
                 `\r. !p. p IN P ==> ~(p divides r + (h:num->num) m)`]
         S2_SQUARE) THEN
  MP_TAC(ISPECL [`h:num->num`; `k:num`; `m:num`; `P:num->bool`;
                 `fam:(num->num)->bool`; `Y:(num->num)->real`]
         RESIDUE_SQUARE_SUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `inv ph *
    sum {c' | ?c. c IN fam /\ col_sub c' c} (\c1.
      sum {c' | ?c. c IN fam /\ col_sub c' c} (\c2.
        maynard_lambda fam (Y:(num->num)->real) c1 * maynard_lambda fam Y c2 *
        &(CARD {n | n < nproduct P (\p. p) /\
                    (!p. p IN P ==> ~(p divides n + h m)) /\
                    col_div h c1 n /\ col_div h c2 n})))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `b:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN EXPAND_TAC "ph" THEN
    ASM_SIMP_TAC[PRODUCT_DIV] THEN
    SUBGOAL_THEN `~(product P (\p. &p - &1) = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]] THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; FINITE_DOWN_COLOURINGS] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c1:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c2:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c1:num->num) IN col_set k P /\ (c2:num->num) IN col_set k P`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c1 IN {c' | ?c. c IN fam /\ col_sub c' (c:num->num)}` THEN
    UNDISCH_TAC `c2 IN {c' | ?c. c IN fam /\ col_sub c' (c:num->num)}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[COL_SUB_SET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->num`; `k:num`; `m:num`; `P:num->bool`;
                 `c1:num->num`; `c2:num->num`] PAIR_RESIDUE_CARD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `col_supp c1 UNION col_supp c2 SUBSET P` ASSUME_TAC THENL
   [UNDISCH_TAC `(c1:num->num) IN col_set k P` THEN
    UNDISCH_TAC `(c2:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(col_supp c1 UNION col_supp c2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT; FINITE_DIFF] THEN
  SUBGOAL_THEN
   `product (P DIFF (col_supp c1 UNION col_supp c2)) (\p. &(p - 1)) =
    product (P DIFF (col_supp c1 UNION col_supp c2)) (\p. &p - &1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p:num. &p - &1`; `P:num->bool`;
                 `col_supp c1 UNION col_supp c2`] PRODUCT_DIFF_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < product (col_supp c1 UNION col_supp c2) (\p. &p - &1)`
  MP_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < x`) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < ph` THEN
  UNDISCH_TAC `product P (\p. &p - &1) = ph` THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl) o
    check (fun th -> can
             (find_term ((=) `P DIFF (col_supp c1 UNION col_supp c2)`))
                         (concl th))) THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Grouping by the stripped colouring; the main term from below.             *)
(* ------------------------------------------------------------------------- *)

let SUM_NUMSEG_EXCEPT = prove
 (`!k m (f:num->real).
     m IN 1..k
     ==> sum (1..k) (\j. if j = m then &0 else f j) = sum (1..k) f - f m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum (1..k) (\j. if j = m then &0 else f j) =
    sum (1..k) (\j. f j - (if j = m then f j else &0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_SUB; FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[MESON[] `(if (j:num) = m then (f:num->real) j else &0) =
                            (if j = m then f m else &0)`] THEN
  ASM_REWRITE_TAC[SUM_DELTA; ETA_AX]);;

let STATE_SUMS_EXCEPT = prove
 (`!k m (w:num->num->real) a d v.
     m IN 1..k /\
     (!j. w m j = &0 /\ w j m = &0) /\ w 0 0 = &1 /\
     (!j. ~(j = 0) /\ ~(j = m) ==> w 0 j = a /\ w j 0 = a) /\
     (!i. ~(i = 0) /\ ~(i = m) ==> w i i = d) /\
     (!i j. ~(i = 0) /\ ~(i = m) /\ ~(j = 0) /\ ~(j = m) /\ ~(i = j)
            ==> w i j = v)
     ==> sum(0..k) (\i. sum(0..k) (\j. w i j)) =
         &1 + (&k - &1) * (&2 * a + d + (&k - &2) * v) /\
         sum(0..k) (\i. w i i) = &1 + (&k - &1) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0) /\ 1 <= k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..k) (\j. (w:num->num->real) 0 j) =
    sum(1..k) (\j. if j = m then &0 else a)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `a:real`)) (concl th))) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= j ==> ~(j = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..k) (\i. (w:num->num->real) i i) =
    sum(1..k) (\i. if i = m then &0 else d)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..k) (\i. (w:num->num->real) i 0 + sum(1..k) (\j. w i j)) =
    sum(1..k) (\i. if i = m then &0 else a + d + (&k - &2) * v)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[SUM_0; REAL_ADD_LID]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:num->num->real) i 0 = a` SUBST1_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`]; ALL_TAC] THEN
    SUBGOAL_THEN
     `sum(1..k) (\j. (w:num->num->real) i j) =
      sum(1..k) (\j. if j = m then &0 else if i = j then d else v)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_NUMSEG_EXCEPT] THEN
    ASM_SIMP_TAC[SUM_NUMSEG_DELTA_ELSE; IN_NUMSEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_NUMSEG_EXCEPT; SUM_CONST_NUMSEG; ADD_SUB] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; REAL_OF_NUM_ADD] THEN
  REAL_ARITH_TAC);;

let col_strip = new_definition
 `col_strip m (c:num->num) = \p. if c p = m then 0 else c p`;;

let maynard_swt = new_definition
 `maynard_swt m p i j =
    if i = m \/ j = m then &0
    else if i = 0 /\ j = 0 then &1
    else if i = 0 \/ j = 0 then inv(&p - &1) pow 2
    else if i = j then inv(&p - &1) + inv(&p - &1) pow 2
    else &3 * inv(&p - &1) pow 2`;;

let MAYNARD_SLOC_STRIP = prove
 (`!m p i j. maynard_sloc m p (if i = m then 0 else i)
               (if j = m then 0 else j) =
             maynard_sloc m p i j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[maynard_sloc] THEN
  MAP_EVERY ASM_CASES_TAC [`i:num = m`; `j:num = m`] THEN
  ASM_REWRITE_TAC[]);;

let LOCAL_MAYNARD_SWT = prove
 (`!m p i j.
     2 <= p /\ ~(i = m) /\ ~(j = m)
     ==> (if i = 0 then &1 else inv(&p - &1)) *
         (if j = 0 then &1 else inv(&p - &1)) *
         abs(maynard_sloc m p i j / (&p - &1))
         <= maynard_swt m p i j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[maynard_sloc; maynard_swt] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_CASES_TAC `j = 0` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(&p - &1 = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_DIV_REFL; REAL_ABS_1; REAL_MUL_LID; REAL_LE_REFL];
    REWRITE_TAC[real_div; REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_1;
                REAL_MUL_LID; REAL_MUL_RID; REAL_POW_2] THEN
    SUBGOAL_THEN `&0 <= inv(&p - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LE_REFL];
    REWRITE_TAC[real_div; REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_1;
                REAL_MUL_LID; REAL_MUL_RID; REAL_POW_2] THEN
    SUBGOAL_THEN `&0 <= inv(&p - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &p - &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `&0 <= &p pow 2 - &p - &1` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `&0 <= (&p - &2) * &p` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&1 <= x ==> abs x = x`;
                 REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    UNDISCH_TAC `&1 <= &p - &1` THEN UNDISCH_TAC `&2 <= &p` THEN
    SPEC_TAC(`&p:real`,`x:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&0 < x - &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `inv(x - &1) * inv(x - &1) * (x pow 2 - x - &1) / (x - &1) =
      (x pow 2 - x - &1) / (x - &1) pow 3 /\
      inv(x - &1) + inv(x - &1) pow 2 =
      ((x - &1) pow 2 + (x - &1)) / (x - &1) pow 3`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN UNDISCH_TAC `&0 < x - &1` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&1 <= x ==> abs x = x`;
               REAL_ABS_NEG] THEN
  SUBGOAL_THEN `abs(&p + &1) = &p + &1` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&1 <= &p - &1` THEN UNDISCH_TAC `&2 <= &p` THEN
  SPEC_TAC(`&p:real`,`x:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < x - &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(x - &1) * inv(x - &1) * (x + &1) / (x - &1) =
    (x + &1) / (x - &1) pow 3 /\
    &3 * inv(x - &1) pow 2 = (&3 * (x - &1)) / (x - &1) pow 3`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < x - &1` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC);;

let STRIP_SUM_BOUND = prove
 (`!k m P fam (y:(num->num)->real) ym e.
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\ ~(m = 0) /\
     fam SUBSET col_set k P /\ &0 <= ym /\ col_supp e SUBSET P /\
     (!c. c IN fam ==> abs(y c) <= ym)
     ==> abs(sum {a | a IN fam /\ col_strip m a = e}
                 (\a. y a / product (col_supp a) (\p. &p - &1)))
         <= ym * product P (\p. &1 + inv(&p - &1)) *
            product (col_supp e) (\p. inv(&p - &1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_COL_SET]; ALL_TAC] THEN
  ABBREV_TAC `S = {a | a IN fam /\ col_strip m a = (e:num->num)}` THEN
  SUBGOAL_THEN `FINITE(S:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> &1 <= &p - &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a IN S
        ==> col_supp a = col_supp e UNION {p | a p = m} /\
            DISJOINT (col_supp e) {p | (a:num->num) p = m} /\
            {p | a p = m} SUBSET P /\ col_supp e SUBSET P`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:num->num` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:num->num) IN col_set k P` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[col_set; col_strip; col_supp; IN_ELIM_THM; EXTENSION; IN_UNION;
                DISJOINT; SUBSET; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THEN X_GEN_TAC `p:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
    ASM_CASES_TAC `(a:num->num) p = m` THEN
    ASM_CASES_TAC `(p:num) IN P` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum S (\a. (ym * product (col_supp e) (\p. inv(&p - &1))) *
               product {p | (a:num->num) p = m} (\p. inv(&p - &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum S (\a. abs((y:(num->num)->real) a /
                               product (col_supp a) (\p. &p - &1)))` THEN
    ASM_SIMP_TAC[SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num->num`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FINITE(col_supp e) /\ FINITE {p | (a:num->num) p = m}`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_UNION] THEN
    SUBGOAL_THEN
     `&0 < product (col_supp e) (\p. &p - &1) /\
      &0 < product {p | (a:num->num) p = m} (\p. &p - &1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < x`) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_INV; REAL_ABS_DIV; REAL_ABS_MUL;
                 REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_MUL] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(a:num->num) IN S` THEN EXPAND_TAC "S" THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c = (a * c) * b:real`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_ADD_EXPAND] THEN
  SUBGOAL_THEN
   `sum S (\a. product {p | (a:num->num) p = m} (\p. inv(&p - &1))) =
    sum (IMAGE (\a:num->num. {p | a p = m}) S)
        (\t. product t (\p. inv(&p - &1)))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:num->num`; `b:num->num`] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; EXTENSION] THEN
      STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
      UNDISCH_TAC `col_strip m (a:num->num) = e` THEN
      UNDISCH_TAC `col_strip m (b:num->num) = e` THEN
      REWRITE_TAC[col_strip; FUN_EQ_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
                           MP_TAC th) THEN
      ASM_CASES_TAC `(a:num->num) p = m` THEN
      ASM_CASES_TAC `(b:num->num) p = m` THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:num->num` o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `S:(num->num)->bool`)) (concl th)))
    THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM SET_TAC[]);;

let SUM_PAIR_GROUP = prove
 (`!(f:A->B) s (Y:A->real) (L:B->B->real).
     FINITE s
     ==> sum s (\a. sum s (\b. Y a * Y b * L (f a) (f b))) =
         sum (IMAGE f s) (\e. sum (IMAGE f s) (\e'.
           sum {a | a IN s /\ f a = e} Y * sum {a | a IN s /\ f a = e'} Y *
           L e e'))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!e:B. sum (IMAGE (f:A->B) s)
              (\e'. sum {a | a IN s /\ f a = e'} (Y:A->real) *
                    (L:B->B->real) e e') =
          sum s (\b. Y b * L e (f b))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`f:A->B`; `\b. (Y:A->real) b * L (e:B) ((f:A->B) b)`;
                   `s:A->bool`; `IMAGE (f:A->B) s`] SUM_GROUP) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `e':B` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL; FINITE_IMAGE] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  MP_TAC(ISPECL [`f:A->B`;
                 `\a. (Y:A->real) a * sum s (\b. Y b * L ((f:A->B) a) (f b))`;
                 `s:A->bool`; `IMAGE (f:A->B) s`] SUM_GROUP) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `e:B` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
  SIMP_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_LMUL]);;

let S2_DIAG_LOCAL = prove
 (`!m P (e:num->num).
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\ col_supp e SUBSET P /\
     (!p. ~(e p = m))
     ==> product P (\p. maynard_sloc m p (e p) (e p) / (&p - &1)) =
         product (col_supp e) (\p. (&p pow 2 - &p - &1) / (&p - &1))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `product (col_supp e) (\p. maynard_sloc m p (e p) (e p) / (&p - &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_SUPERSET THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[col_supp; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[maynard_sloc] THEN
    MATCH_MP_TAC REAL_DIV_REFL THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN
    REWRITE_TAC[col_supp; IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[maynard_sloc]]);;

let S2_PAIR_MAYNARD_SWT = prove
 (`!m P (e:num->num) e' t1 t2 tm.
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\
     col_supp e SUBSET P /\ col_supp e' SUBSET P /\
     (!p. ~(e p = m)) /\ (!p. ~(e' p = m)) /\
     abs t1 <= tm * product (col_supp e) (\p. inv(&p - &1)) /\
     abs t2 <= tm * product (col_supp e') (\p. inv(&p - &1))
     ==> abs(t1 * t2 *
             product P (\p. maynard_sloc m p (e p) (e' p) / (&p - &1)))
         <= tm pow 2 * product P (\p. maynard_swt m p (e p) (e' p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN P ==> &0 <= inv(&p - &1)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:num->num. col_supp c SUBSET P
                 ==> product (col_supp c) (\p. inv(&p - &1)) =
                     product P (\p. if c p = 0 then &1 else inv(&p - &1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `product (col_supp c) (\p. if c p = 0 then &1
                                       else inv(&p - &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[col_supp; IN_ELIM_THM] THEN
      SIMP_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_SUPERSET THEN
      ASM_REWRITE_TAC[col_supp; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= product P (\p. if (e:num->num) p = 0 then &1 else inv(&p - &1)) /\
    &0 <= product P (\p. if (e':num->num) p = 0 then &1 else inv(&p - &1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= tm` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < product (col_supp e) (\p. inv(&p - &1))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LT THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      X_GEN_TAC `q:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
      SUBGOAL_THEN `2 <= q` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= tm * product (col_supp e) (\p. inv(&p - &1))` MP_TAC
    THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs t1` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_SIMP_TAC[REAL_LE_MUL_EQ]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[GSYM PRODUCT_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(tm * product P (\p. if (e:num->num) p = 0 then &1 else inv(&p - &1))) *
    (tm * product P (\p. if (e':num->num) p = 0 then &1 else inv(&p - &1))) *
    product P (\p. abs(maynard_sloc m p (e p) (e' p) / (&p - &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS]]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a * b) * (c * d) * e = (a * c) * b * d * e:real`;
              GSYM REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN MATCH_MP_TAC PRODUCT_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_POS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_POS];
    MATCH_MP_TAC LOCAL_MAYNARD_SWT THEN ASM_SIMP_TAC[]]);;

let COL_STRIP_SET = prove
 (`!k m P (a:num->num).
     ~(m = 0) /\ a IN col_set k P
     ==> col_strip m a IN col_set k P /\ (!p. ~(col_strip m a p = m)) /\
         col_supp(col_strip m a) SUBSET P`,
  REWRITE_TAC[col_set; col_strip; col_supp; IN_ELIM_THM; SUBSET] THEN
  REPEAT STRIP_TAC THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[LE_0];
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

let S2_MAIN_LOWER = prove
 (`!k m P fam (y:(num->num)->real) ym.
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\ m IN 1..k /\
     fam SUBSET col_set k P /\ &0 <= ym /\
     (!c. c IN fam ==> abs(y c) <= ym)
     ==> sum (IMAGE (col_strip m) fam) (\e.
           product (col_supp e) (\p. (&p pow 2 - &p - &1) / (&p - &1)) *
           sum {a | a IN fam /\ col_strip m a = e}
               (\a. y a / product (col_supp a) (\p. &p - &1)) pow 2) -
         (ym * product P (\p. &1 + inv(&p - &1))) pow 2 *
         (product P (\p. &1 + (&k - &1) *
             (&2 * inv(&p - &1) pow 2 + (inv(&p - &1) + inv(&p - &1) pow 2) +
              (&k - &2) * (&3 * inv(&p - &1) pow 2))) -
          product P (\p. &1 + (&k - &1) * (inv(&p - &1) + inv(&p - &1) pow 2)))
         <= sum fam (\a. sum fam (\b.
              y a / product (col_supp a) (\p. &p - &1) *
              y b / product (col_supp b) (\p. &p - &1) *
              product P (\p. maynard_sloc m p (a p) (b p) / (&p - &1))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `m IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_COL_SET]; ALL_TAC] THEN
  ABBREV_TAC `Y = \a:num->num. y a / product (col_supp a) (\p. &p - &1)` THEN
  ABBREV_TAC `L = \e e':num->num.
                    product P
                      (\p. maynard_sloc m p (e p) (e' p) / (&p - &1))` THEN
  SUBGOAL_THEN
   `!a b:num->num.
      y a / product (col_supp a) (\p. &p - &1) *
      y b / product (col_supp b) (\p. &p - &1) *
      product P (\p. maynard_sloc m p (a p) (b p) / (&p - &1)) =
      (Y:(num->num)->real) a * Y b * L (col_strip m a) (col_strip m b)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["Y"; "L"] THEN
    REWRITE_TAC[col_strip; MAYNARD_SLOC_STRIP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`col_strip m`; `fam:(num->num)->bool`; `Y:(num->num)->real`;
                 `L:(num->num)->(num->num)->real`] SUM_PAIR_GROUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `E = IMAGE (col_strip m) (fam:(num->num)->bool)` THEN
  ABBREV_TAC `T0 = \e. sum {a | a IN fam /\ col_strip m a = e}
                           (Y:(num->num)->real)` THEN
  SUBGOAL_THEN
    `!e. sum {a | a IN fam /\ col_strip m a = e} (Y:(num->num)->real)
                    = T0 e`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "T0" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(E:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN E ==> e IN col_set k P /\ (!p. ~((e:num->num) p = m)) /\
                   col_supp e SUBSET P`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `a:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC COL_STRIP_SET THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN E
        ==> abs((T0:(num->num)->real) e) <=
            (ym * product P (\p. &1 + inv(&p - &1))) *
            product (col_supp e) (\p. inv(&p - &1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "T0" THEN EXPAND_TAC "Y" THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC STRIP_SUM_BOUND THEN EXISTS_TAC `k:num` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tm = ym * product P (\p. &1 + inv(&p - &1))` THEN
  SUBGOAL_THEN
   `sum E (\e. sum E (\e'. (T0:(num->num)->real) e * T0 e' *
                           (L:(num->num)->(num->num)->real) e e')) =
    sum E (\e. product (col_supp e) (\p. (&p pow 2 - &p - &1) / (&p - &1)) *
               T0 e pow 2) +
    sum E (\e. sum (E DELETE e) (\e'. T0 e * T0 e' * L e e'))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `e:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUM_DELETE] THEN
    SUBGOAL_THEN
     `(L:(num->num)->(num->num)->real) e e =
      product (col_supp e) (\p. (&p pow 2 - &p - &1) / (&p - &1))`
    SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[] THEN MATCH_MP_TAC S2_DIAG_LOCAL THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs b <= c ==> a - c <= a + b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum E (\e. sum (E DELETE e) (\e'.
      tm pow 2 *
      product P (\p. maynard_swt m p ((e:num->num) p) ((e':num->num) p))))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum E (\e. abs(sum (E DELETE e)
                    (\e'. (T0:(num->num)->real) e * T0 e' *
                          (L:(num->num)->(num->num)->real) e e')))` THEN
    ASM_SIMP_TAC[SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (E DELETE e)
                    (\e'. abs((T0:(num->num)->real) e * T0 e' *
                              (L:(num->num)->(num->num)->real) e e'))` THEN
    ASM_SIMP_TAC[SUM_ABS; FINITE_DELETE] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
    X_GEN_TAC `e':num->num` THEN STRIP_TAC THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC S2_PAIR_MAYNARD_SWT THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL; FINITE_DELETE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `product P (\p. sum (0..k) (\i. sum (0..k) (\j. maynard_swt m p i j))) -
    product P (\p. sum (0..k) (\i. maynard_swt m p i i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OFFDIAG_STATES THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= inv(&p - &1)` MP_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN
      SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[maynard_swt] THEN REPEAT COND_CASES_TAC THEN
    SIMP_TAC[REAL_POS; REAL_LE_POW_2; REAL_LE_ADD; REAL_LE_MUL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `m:num`; `maynard_swt m p`; `inv(&p - &1) pow 2`;
                 `inv(&p - &1) + inv(&p - &1) pow 2`;
                 `&3 * inv(&p - &1) pow 2`] STATE_SUMS_EXCEPT) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[maynard_swt] THEN SIMP_TAC[]; SIMP_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* Counting primes in the progressions.                                      *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_1_SING = prove
 (`!s:A->bool. FINITE s /\ CARD s = 1 ==> ?a. s = {a}`,
  REWRITE_TAC[GSYM HAS_SIZE; ONE; HAS_SIZE_CLAUSES] THEN MESON_TAC[]);;

let CONG_NPRODUCT_PRIMES = prove
 (`!t. FINITE t /\ (!p. p IN t ==> prime p)
       ==> !x y. (x == y) (mod (nproduct t (\p. p))) <=>
                 !p. p IN t ==> (x == y) (mod p)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NPRODUCT_CLAUSES; NOT_IN_EMPTY; CONG_MOD_1]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `s:num->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `coprime(q,nproduct s (\p. p))` ASSUME_TAC THENL
   [MATCH_MP_TAC COPRIME_PRIME_NPRODUCT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONG_CHINESE_EQ]);;

let CRT_RESIDUE_EXISTS = prove
 (`!t (LP:num->num->bool).
     FINITE t /\ (!p. p IN t ==> prime p) /\
     (!p. p IN t ==> CARD {s | s < p /\ LP p s} = 1)
     ==> ?b. b < nproduct t (\p. p) /\
             !n. (!p. p IN t ==> LP p (n MOD p)) <=>
                 n MOD nproduct t (\p. p) = b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`LP:num->num->bool`; `t:num->bool`] CRT_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `nproduct t (\p. CARD {r | r < p /\ (LP:num->num->bool) p r}) = 1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `nproduct t (\p:num. 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_EQ THEN ASM_SIMP_TAC[];
      REWRITE_TAC[NPRODUCT_ONE]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `{r | r < nproduct t (\p. p) /\
                     !p. p IN t ==> (LP:num->num->bool) p (r MOD p)}`
         CARD_EQ_1_SING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r:num | r < nproduct t (\p. p)}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:num`) THEN EXISTS_TAC `b:num` THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[EXTENSION; IN_ELIM_THM; IN_SING]) THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(nproduct t (\p. p) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NPRODUCT_EQ_0] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n MOD nproduct t (\p. p)`) THEN
  ASM_SIMP_TAC[MOD_LT_EQ; NPRODUCT_PRIMES_MOD]);;

let S2_COUNT_PI = prove
 (`!h m Wp t nu N (c:num->num).
     FINITE Wp /\ (!p. p IN Wp ==> prime p) /\
     FINITE t /\ (!p. p IN t ==> prime p) /\ DISJOINT Wp t /\
     col_supp c = t /\
     (!p. p IN Wp ==> ~(p divides nu + h m)) /\
     (!p. p IN t ==> ~((h(c p) == h m) (mod p))) /\ 1 <= N
     ==> ?b. coprime(b,nproduct (Wp UNION t) (\p. p)) /\
             CARD {n | N <= n /\ n < 2 * N /\
                       (n == nu) (mod (nproduct Wp (\p. p))) /\
                       prime(n + h m) /\ col_div h c n} =
             pi_ap ((2 * N + h m) - 1) (nproduct (Wp UNION t) (\p. p)) b -
             pi_ap ((N + h m) - 1) (nproduct (Wp UNION t) (\p. p)) b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(Wp UNION t:num->bool) /\
                (!p. p IN Wp UNION t ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `d = nproduct (Wp UNION t) (\p:num. p)` THEN
  MP_TAC(ISPECL [`Wp UNION t:num->bool`;
                 `\p s. if p IN Wp then s = nu MOD p
                        else p divides s + (h:num->num)((c:num->num) p)`]
         CRT_RESIDUE_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_UNION] THEN
    DISCH_TAC THEN SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    ASM_CASES_TAC `(p:num) IN Wp` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `{s | s < p /\ s = nu MOD p} = {nu MOD p}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
        ASM_MESON_TAC[MOD_LT_EQ];
        REWRITE_TAC[CARD_SING]];
      ASM_SIMP_TAC[RESIDUES_DIVIDING; CARD_SING]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `beta:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "crt"))) THEN
  USE_THEN "crt" (MP_TAC o SPEC `beta:num`) THEN
  REWRITE_TAC[MATCH_MP MOD_LT (ASSUME `beta:num < d`)] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_NZ; LE_0; LET_TRANS; NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (n == nu) (mod (nproduct Wp (\p. p))) /\ col_div h c n <=>
        (n == beta) (mod d)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    ASM_SIMP_TAC[CONG_NPRODUCT_PRIMES; CONG; MOD_LT] THEN
    USE_THEN "crt" (SUBST1_TAC o SYM o SPEC `n:num`) THEN
    REWRITE_TAC[col_div; IN_UNION; ASSUME `col_supp (c:num->num) = t`] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN X_GEN_TAC `p:num` THEN
      ASM_CASES_TAC `(p:num) IN Wp` THEN ASM_SIMP_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[PRIME_IMP_NZ; IN_UNION]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM DIVIDES_ADD_MOD];
      DISCH_TAC THEN CONJ_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((p:num) IN Wp)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `DISJOINT Wp (t:num->bool)` THEN
        UNDISCH_TAC `(p:num) IN t` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[PRIME_IMP_NZ; IN_UNION]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM DIVIDES_ADD_MOD]];
    ALL_TAC] THEN
  EXISTS_TAC `beta + (h:num->num) m` THEN CONJ_TAC THENL
   [EXPAND_TAC "d" THEN ASM_SIMP_TAC[COPRIME_NPRODUCT_EQ] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `prime p /\ ~(p = 0)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
      can (find_term ((=) `beta MOD p`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(p:num) IN Wp UNION t` THEN REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `(p:num) IN Wp` THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(beta:num == nu) (mod p)` MP_TAC THENL
       [ASM_REWRITE_TAC[CONG]; ALL_TAC] THEN
      SUBGOAL_THEN `~(p divides nu + (h:num->num) m)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(c ==> b ==> a) ==> ~a ==> c ==> ~b`) THEN
      CONV_TAC NUMBER_RULE;
      DISCH_TAC THEN ASM_SIMP_TAC[GSYM DIVIDES_ADD_MOD] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
        can (find_term ((=) `(h:num->num) m`)) (concl th) &&
        can (find_term ((=) `t:num->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> ~b`) THEN
      UNDISCH_TAC `p divides beta + (h:num->num)((c:num->num) p)` THEN
      CONV_TAC NUMBER_RULE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{n | N <= n /\ n < 2 * N /\ (n == nu) (mod nproduct Wp (\p. p)) /\
         prime (n + h m) /\ col_div h c n} =
    {n | N <= n /\ n < 2 * N /\ prime(n + (h:num->num) m) /\
         (n == beta) (mod d)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (is_forall o concl)) THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  REWRITE_TAC[pi_ap] THEN
  ABBREV_TAC `x1 = (N + (h:num->num) m) - 1` THEN
  ABBREV_TAC `x2 = (2 * N + (h:num->num) m) - 1` THEN
  SUBGOAL_THEN `x1 <= x2 /\ (!q. x1 < q <=> N + (h:num->num) m <= q) /\
                (!q. q <= x2 <=> q < 2 * N + h m)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x1"; "x2"] THEN
    REPEAT CONJ_TAC THEN TRY GEN_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `CARD({q | prime q /\ q <= x2 /\ (q == beta + (h:num->num) m) (mod d)} DIFF
         {q | prime q /\ q <= x1 /\ (q == beta + h m) (mod d)})` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CARD_DIFF THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{q:num | q <= x2}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LE] THEN SET_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LE_TRANS]]] THEN
  SUBGOAL_THEN
   `{q | prime q /\ q <= x2 /\ (q == beta + (h:num->num) m) (mod d)} DIFF
    {q | prime q /\ q <= x1 /\ (q == beta + h m) (mod d)} =
    IMAGE (\n. n + h m)
          {n | N <= n /\ n < 2 * N /\ prime(n + h m) /\ (n == beta) (mod d)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `q:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `q - (h:num->num) m` THEN
      SUBGOAL_THEN `N + (h:num->num) m <= q` ASSUME_TAC THENL
       [ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `q - (h:num->num) m + h m = q` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[GSYM(SPECL [`(h:num->num) m`] CONG_ADD_RCANCEL_EQ)] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(q:num) <= x2` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[CONG_ADD_RCANCEL_EQ] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[EQ_ADD_RCANCEL] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{n:num | n < 2 * N}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]);;

let col_union = new_definition
 `col_union (c1:num->num) c2 = \p. if c1 p = 0 then c2 p else c1 p`;;

let COL_SUPP_UNION = prove
 (`!c1 c2. col_supp(col_union c1 c2) = col_supp c1 UNION col_supp c2`,
  REWRITE_TAC[col_supp; col_union; EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let COL_DIV_UNION = prove
 (`!h m (c1:num->num) c2 n.
     maynard_pairok m c1 c2
     ==> (col_div h (col_union c1 c2) n <=> col_div h c1 n /\ col_div h c2 n)`,
  REWRITE_TAC[maynard_pairok; col_div; COL_SUPP_UNION; IN_UNION] THEN
  REWRITE_TAC[col_supp; col_union; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    STRIP_TAC THEN X_GEN_TAC `p:num` THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[]]);;

let REAL_PHI_NPRODUCT_PRIMES = prove
 (`!s. FINITE s /\ (!p. p IN s ==> prime p)
       ==> &(phi(nproduct s (\p. p))) = product s (\p. &p - &1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PHI_NPRODUCT_PRIMES] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT] THEN MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
  ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]);;

let PI_AP_MONO = prove
 (`!x y d a. x <= y ==> pi_ap x d a <= pi_ap y d a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pi_ap] THEN MATCH_MP_TAC CARD_SUBSET THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LE_TRANS];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | p <= y}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LE] THEN SET_TAC[]]);;

let PI_UPTO_MONO = prove
 (`!x y. x <= y ==> pi_upto x <= pi_upto y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pi_upto] THEN MATCH_MP_TAC CARD_SUBSET THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LE_TRANS];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | p <= y}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LE] THEN SET_TAC[]]);;

let S2_PAIR_ZERO = prove
 (`!h k m P (c1:num->num) c2 A.
     (!p. p IN P ==> prime p) /\ maynard_hdist h k P /\ m IN 1..k /\
     c1 IN col_set k P /\ c2 IN col_set k P /\ ~(maynard_pairok m c1 c2) /\
     (!n p. n IN A /\ p IN P ==> p < n + h m)
     ==> CARD {n | n IN A /\ prime(n + h m) /\ col_div h c1 n /\
                   col_div h c2 n} = 0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD(s:num->bool) = 0`) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[col_div] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!c:num->num p. c IN col_set k P /\ p IN col_supp c ==> p IN P /\
                   c p IN 1..k`
  ASSUME_TAC THENL
   [REWRITE_TAC[col_set; col_supp; IN_ELIM_THM; IN_NUMSEG] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
    ASM_CASES_TAC `(p:num) IN P` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:num->num p. c IN col_set k P /\ p IN col_supp c /\
                   p divides n + (h:num->num)(c p) ==> ~(c p = m)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `p IN P /\ prime p` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `p = n + (h:num->num) m` ASSUME_TAC THENL
     [UNDISCH_TAC `p divides n + (h:num->num)(c p)` THEN
      ASM_SIMP_TAC[DIVIDES_PRIME_PRIME];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `p:num`] o check (fun th ->
      can (find_term ((=) `A:num->bool`)) (concl th))) THEN
    ASM_MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  UNDISCH_TAC `~(maynard_pairok m (c1:num->num) c2)` THEN
  REWRITE_TAC[maynard_pairok] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `maynard_hdist h k P` THEN
  REWRITE_TAC[maynard_hdist; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `(c1:num->num) p`; `(c2:num->num) p`] THEN
  REWRITE_TAC[NOT_IMP] THEN
  SUBGOAL_THEN `p IN P /\ (c1:num->num) p IN 1..k /\ (c2:num->num) p IN 1..k`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `!n. p divides n + a /\ p divides n + b ==> (a:num == b) (mod p)`) THEN
  EXISTS_TAC `n:num` THEN ASM_MESON_TAC[]);;

let COL_UNION_COLOUR = prove
 (`!k m P (c1:num->num) c2 p.
     c1 IN col_set k P /\ c2 IN col_set k P /\ maynard_pairok m c1 c2 /\
     p IN col_supp c1 UNION col_supp c2
     ==> col_union c1 c2 p IN 1..k /\ ~(col_union c1 c2 p = m)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[maynard_pairok; col_set; col_supp; IN_UNION; IN_ELIM_THM;
                                  col_union; IN_NUMSEG] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl))) THEN
  ASM_CASES_TAC `(p:num) IN P` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(c1:num->num) p = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let S2_PAIR_ERR = prove
 (`!h k m Wp P nu N (c1:num->num) c2.
     FINITE Wp /\ (!p. p IN Wp ==> prime p) /\
     FINITE P /\ (!p. p IN P ==> prime p) /\ DISJOINT Wp P /\
     maynard_hdist h k P /\ m IN 1..k /\
     c1 IN col_set k P /\ c2 IN col_set k P /\ maynard_pairok m c1 c2 /\
     (!p. p IN Wp ==> ~(p divides nu + h m)) /\ 1 <= N
     ==> ?b. coprime(b,nproduct (Wp UNION (col_supp c1 UNION col_supp c2))
                               (\p. p)) /\
             abs(&(CARD {n | N <= n /\ n < 2 * N /\
                             (n == nu) (mod (nproduct Wp (\p. p))) /\
                             prime(n + h m) /\ col_div h c1 n /\
                             col_div h c2 n}) -
                 (&(pi_upto ((2 * N + h m) - 1)) -
                  &(pi_upto ((N + h m) - 1))) /
                 (product Wp (\p. &p - &1) *
                  product (col_supp c1 UNION col_supp c2) (\p. &p - &1)))
             <= abs(&(pi_ap ((2 * N + h m) - 1)
                       (nproduct
                          (Wp UNION (col_supp c1 UNION col_supp c2)) (\p. p))
                       b) -
                    &(pi_upto ((2 * N + h m) - 1)) /
                    &(phi(nproduct (Wp UNION (col_supp c1 UNION col_supp c2))
                                   (\p. p)))) +
                abs(&(pi_ap ((N + h m) - 1)
                       (nproduct
                          (Wp UNION (col_supp c1 UNION col_supp c2)) (\p. p))
                       b) -
                    &(pi_upto ((N + h m) - 1)) /
                    &(phi(nproduct (Wp UNION (col_supp c1 UNION col_supp c2))
                                   (\p. p))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = col_supp c1 UNION col_supp (c2:num->num)` THEN
  SUBGOAL_THEN `t SUBSET (P:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    UNDISCH_TAC `(c1:num->num) IN col_set k P` THEN
    UNDISCH_TAC `(c2:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(t:num->bool) /\ (!p. p IN t ==> prime p) /\
                DISJOINT Wp (t:num->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->num`; `m:num`; `Wp:num->bool`; `t:num->bool`;
                 `nu:num`; `N:num`;
                  `col_union (c1:num->num) c2`] S2_COUNT_PI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COL_SUPP_UNION] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `maynard_hdist h k P` THEN REWRITE_TAC[maynard_hdist] THEN
    DISCH_THEN(MP_TAC o SPECL [`p:num`; `col_union (c1:num->num) c2 p`;
                               `m:num`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MP_TAC(ISPECL [`k:num`; `m:num`; `P:num->bool`; `c1:num->num`;
                   `c2:num->num`; `p:num`] COL_UNION_COLOUR) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. col_div h (col_union (c1:num->num) c2) n <=> col_div h c1 n /\
        col_div h c2 n`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC COL_DIV_UNION THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!p. p IN Wp UNION t ==> prime p` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_PHI_NPRODUCT_PRIMES; FINITE_UNION] THEN
  ASM_SIMP_TAC[PRODUCT_UNION] THEN
  SUBGOAL_THEN
   `pi_ap ((N + (h:num->num) m) - 1) (nproduct (Wp UNION t) (\p. p)) b <=
    pi_ap ((2 * N + h m) - 1) (nproduct (Wp UNION t) (\p. p)) b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PI_AP_MONO THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[real_div; REAL_SUB_RDISTRIB] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bombieri-Vinogradov discrepancies and the error sum.                      *)
(* ------------------------------------------------------------------------- *)

let MAX_RESIDUE_CHOICE = prove
 (`!(S:A->bool) (dm:A->num) (bm:A->num) (g:num->num->real).
     FINITE S /\ (!x. x IN S ==> coprime(bm x,dm x))
     ==> ?a. (!d. coprime(a d,d)) /\
             !x. x IN S ==> g (dm x) (bm x) <= g (dm x) (a (dm x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!d. ?b. coprime(b,d) /\
            !x. x IN S /\ (dm:A->num) x = d ==> g d ((bm:A->num) x) <= g d b`
  MP_TAC THENL
   [X_GEN_TAC `d:num` THEN
    ASM_CASES_TAC `{x | x IN S /\ (dm:A->num) x = d} = {}` THENL
     [EXISTS_TAC `1` THEN REWRITE_TAC[COPRIME_1] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x:A. (g:num->num->real) d ((bm:A->num) x)`;
                   `{x | x IN S /\ (dm:A->num) x = d}`] FINITE_MAX_IMAGE) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(bm:A->num) y` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:num->num` THEN REWRITE_TAC[FORALL_AND_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let GENERIC_BV_SUM = prove
 (`!(S:A->bool) (key:A->B) (D:B->num) bm (err:A->real) (g:num->num->real).
     FINITE S /\
     (!x. x IN S ==> coprime(bm x,D(key x)) /\
                     abs(err x) <= g (D(key x)) (bm x))
     ==> ?a. (!d. coprime(a d,d)) /\
             sum S (\x. abs(err x)) <=
             sum (IMAGE key S)
                 (\u. &(CARD {x | x IN S /\ key x = u}) * g (D u) (a (D u)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:A->bool`; `\x:A. (D:B->num)((key:A->B) x)`;
                 `bm:A->num`; `g:num->num->real`] MAX_RESIDUE_CHOICE) THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:num->num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum S (\x:A. (g:num->num->real) (D((key:A->B) x))
                                                (a (D(key x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`key:A->B`;
                 `\x:A. (g:num->num->real) (D((key:A->B) x)) (a (D(key x)))`;
                 `S:A->bool`; `IMAGE (key:A->B) S`] SUM_GROUP) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `u:B` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {x | x IN S /\ (key:A->B) x = u}
                  (\x:A. (g:num->num->real) (D u) (a ((D:B->num) u)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_ELIM_THM];
    ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT]]);;

let CARD_COL_SET = prove
 (`!k P. FINITE P ==> &(CARD(col_set k P)) = (&k + &1) pow CARD P`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `P:num->bool`; `\p:num i:num. &1`]
         COL_SET_SUM_PRODUCT) THEN
  ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_ONE; SUM_CONST; FINITE_COL_SET;
               SUM_CONST_NUMSEG; REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) - 0 = k + 1`; REAL_OF_NUM_ADD]);;

let SUM_SUM_PAIRS_RESTRICT = prove
 (`!(D:A->bool) (R:A->A->bool) (f:A->A->real).
     FINITE D
     ==> sum D (\c1. sum D (\c2. if R c1 c2 then f c1 c2 else &0)) =
         sum {x | x IN D CROSS D /\ R (FST x) (SND x)}
             (\x. f (FST x) (SND x))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_PRODUCT o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  REWRITE_TAC[GSYM CROSS; LAMBDA_PAIR_THM] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[FST; SND]);;

let W_M_TRICK = prove
 (`!M w g. &0 < M /\ &0 <= w /\ &0 <= g ==> w * g <= M * g + w pow 2 * g / M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w <= M + w pow 2 / M` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_FIELD `&0 < M ==> M + w pow 2 / M =
                                         (M pow 2 + w pow 2) / M`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= (w - M) pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= w * M` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(M + w pow 2 / M) * (g:real)` THEN
    ASM_SIMP_TAC[REAL_LE_RMUL] THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC]);;

let bv_disc = new_definition
 `bv_disc x d b = abs(&(pi_ap x d b) - &(pi_upto x) / &(phi d))`;;

let BV_DISC_POS = prove
 (`!x d b. &0 <= bv_disc x d b`,
  REWRITE_TAC[bv_disc; REAL_ABS_POS]);;

let PAIRS_SUPPORT_COUNT = prove
 (`!k P (D:(num->num)->bool) (R:(num->num)#(num->num)->bool) u.
     D SUBSET col_set k P /\ FINITE u
     ==> &(CARD {x | x IN D CROSS D /\ R x /\
                     col_supp(FST x) UNION col_supp(SND x) = u})
         <= (&k + &1) pow (2 * CARD u)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(col_set k u CROSS col_set k u))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_CROSS; FINITE_COL_SET] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`c1:num->num`; `c2:num->num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c1:num->num) IN col_set k P /\ (c2:num->num) IN col_set k P`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `col_supp (c1:num->num) UNION col_supp (c2:num->num) = u` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[col_set; col_supp; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[];
    ASM_SIMP_TAC[CARD_CROSS; FINITE_COL_SET; GSYM REAL_OF_NUM_MUL;
                 CARD_COL_SET] THEN
    REWRITE_TAC[GSYM REAL_POW_ADD; MULT_2; REAL_LE_REFL]]);;

let S2_ERROR_SUM = prove
 (`!h k m Wp P nu N fam (Y:(num->num)->real) L R.
     FINITE Wp /\ (!p. p IN Wp ==> prime p) /\
     FINITE P /\ (!p. p IN P ==> prime p) /\ DISJOINT Wp P /\
     maynard_hdist h k P /\ m IN 1..k /\ fam SUBSET col_set k P /\
     (!c. c IN fam ==> &(nproduct (col_supp c) (\p. p)) < R) /\
     (!p. p IN Wp ==> ~(p divides nu + h m)) /\ 1 <= N /\
     (!p. p IN P ==> p < N) /\
     (!c. (?c0. c0 IN fam /\ col_sub c c0)
          ==> abs(maynard_lambda fam Y c) <= L)
     ==> ?a. (!d. coprime(a d,d)) /\
             abs(sum {n | n IN {n | N <= n /\ n < 2 * N /\
                                    (n == nu) (mod (nproduct Wp (\p. p)))} /\
                          prime(n + h m)}
                     (\n. sum fam (\c. Y c * product (col_supp c)
                                                (\p. maynard_lfac h c p
                                                       n)) pow 2) -
                 (&(pi_upto ((2 * N + h m) - 1)) -
                  &(pi_upto ((N + h m) - 1))) /
                 product Wp (\p. &p - &1) *
                 sum {c' | ?c. c IN fam /\ col_sub c' c} (\c1.
                   sum {c' | ?c. c IN fam /\ col_sub c' c} (\c2.
                     maynard_lambda fam Y c1 * maynard_lambda fam Y c2 *
                     (if maynard_pairok m c1 c2
                      then inv(product (col_supp c1 UNION col_supp c2)
                                       (\p. &p - &1))
                      else &0))))
             <= L pow 2 *
                sum {t | t SUBSET P /\ &(nproduct t (\p. p)) < R pow 2}
                    (\t. (&k + &1) pow (2 * CARD t) *
                  (bv_disc ((2 * N + h m) - 1) (nproduct (Wp UNION t) (\p. p))
                          (a (nproduct (Wp UNION t) (\p. p))) +
                   bv_disc ((N + h m) - 1) (nproduct (Wp UNION t) (\p. p))
                          (a (nproduct (Wp UNION t) (\p. p)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_COL_SET]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. c IN fam ==> FINITE(col_supp c)` ASSUME_TAC THENL
   [X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:num->num) IN col_set k P` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `A = {n | N <= n /\ n < 2 * N /\
                       (n == nu) (mod (nproduct Wp (\p:num. p)))}` THEN
  SUBGOAL_THEN `FINITE(A:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{n:num | n < 2 * N}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num->num`; `fam:(num->num)->bool`; `Y:(num->num)->real`;
                 `A:num->bool`;
                  `\n. prime(n + (h:num->num) m)`] S2_SQUARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `D = {c' | ?c. c IN fam /\ col_sub c' (c:num->num)}` THEN
  SUBGOAL_THEN `FINITE(D:(num->num)->bool) /\ D SUBSET col_set k P`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_DOWN_COLOURINGS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[COL_SUB_SET; SUBSET]];
    ALL_TAC] THEN
  ABBREV_TAC `XW = (&(pi_upto ((2 * N + (h:num->num) m) - 1)) -
                    &(pi_upto ((N + h m) - 1))) /
                   product Wp (\p. &p - &1)` THEN
  ABBREV_TAC
   `e = \c1 c2. &(CARD {n | n IN A /\ prime(n + (h:num->num) m) /\
                            col_div h c1 n /\ col_div h c2 n}) -
                (if maynard_pairok m c1 c2
                 then XW *
                 inv(product (col_supp c1 UNION col_supp c2) (\p. &p - &1))
                 else &0)` THEN
  SUBGOAL_THEN
   `sum D (\c1. sum D (\c2. maynard_lambda fam Y c1 * maynard_lambda fam Y c2 *
              &(CARD {n | n IN A /\ prime(n + (h:num->num) m) /\
                          col_div h c1 n /\ col_div h c2 n}))) -
    XW * sum D (\c1. sum D (\c2. maynard_lambda fam (Y:(num->num)->real) c1 *
              maynard_lambda fam Y c2 *
              (if maynard_pairok m c1 c2
               then inv(product (col_supp c1 UNION col_supp c2) (\p. &p - &1))
               else &0))) =
    sum D (\c1. sum D (\c2. maynard_lambda fam Y c1 * maynard_lambda fam Y c2 *
                            (e:(num->num)->(num->num)->real) c1 c2))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c1:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c2:num->num` THEN DISCH_TAC THEN
    EXPAND_TAC "e" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c1 c2. c1 IN D /\ c2 IN D /\ ~(maynard_pairok m c1 c2)
            ==> (e:(num->num)->(num->num)->real) c1 c2 = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "e" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC S2_PAIR_ZERO THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `P:num->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `N:num` THEN
      ASM_SIMP_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S = {x | x IN D CROSS D /\
                       maynard_pairok m (FST x)
                         (SND (x:(num->num)#(num->num)))}` THEN
  SUBGOAL_THEN `FINITE(S:(num->num)#(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_SIMP_TAC[FINITE_CROSS];
    ALL_TAC] THEN
  ABBREV_TAC `Dm = \t. nproduct (Wp UNION t) (\p:num. p)` THEN
  ABBREV_TAC `key = \x:(num->num)#(num->num).
                    col_supp(FST x) UNION col_supp(SND x)` THEN
  ABBREV_TAC `g = \d b. bv_disc ((2 * N + (h:num->num) m) - 1) d b +
                         bv_disc ((N + h m) - 1) d b` THEN
  SUBGOAL_THEN
   `!x. x IN S
        ==> ?b. coprime(b,(Dm:(num->bool)->num) ((key:(num->num)#(num->num)->
                                                   num->bool) x)) /\
                abs((e:(num->num)->(num->num)->real) (FST x) (SND x)) <=
                (g:num->num->real) (Dm(key x)) b`
  MP_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`c1:num->num`; `c2:num->num`] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_CROSS; FST; SND] THEN
    STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["Dm"; "key"; "g"; "e"] THEN
    REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:num->num`; `k:num`; `m:num`; `Wp:num->bool`;
                   `P:num->bool`; `nu:num`; `N:num`; `c1:num->num`;
                   `c2:num->num`] S2_PAIR_ERR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[bv_disc] THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `abs(x - y) <= z ==> y = y' ==> abs(x - y') <= z`)) THEN
    EXPAND_TAC "XW" THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `bm:(num->num)#(num->num)->num` o
    REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  MP_TAC(ISPECL [`S:(num->num)#(num->num)->bool`;
                 `key:(num->num)#(num->num)->num->bool`;
                 `Dm:(num->bool)->num`; `bm:(num->num)#(num->num)->num`;
                 `\x:(num->num)#(num->num).
                    (e:(num->num)->(num->num)->real) (FST x) (SND x)`;
                 `g:num->num->real`] GENERIC_BV_SUM) THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:num->num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `!c. c IN D ==> abs(maynard_lambda fam (Y:(num->num)->real) c) <= L`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!d b. &0 <= (g:num->num->real) d b` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN SIMP_TAC[REAL_LE_ADD; BV_DISC_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum D (\c1. sum D (\c2.
     L pow 2 * abs((e:(num->num)->(num->num)->real) c1 c2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum D (\c1. abs(sum D (\c2.
      maynard_lambda fam (Y:(num->num)->real) c1 * maynard_lambda fam Y c2 *
      (e:(num->num)->(num->num)->real) c1 c2)))` THEN
    ASM_SIMP_TAC[SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `c1:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum D (\c2. abs(maynard_lambda fam (Y:(num->num)->real) c1 *
                                maynard_lambda fam Y c2 *
                                (e:(num->num)->(num->num)->real) c1 c2))` THEN
    ASM_SIMP_TAC[SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `c2:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_POW_2; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  SUBGOAL_THEN
   `sum D (\c1. sum D (\c2. abs((e:(num->num)->(num->num)->real) c1 c2))) =
    sum S (\x. abs(e (FST x) (SND x)))`
  SUBST1_TAC THENL
   [EXPAND_TAC "S" THEN
    MP_TAC(ISPECL [`D:(num->num)->bool`;
                   `maynard_pairok m`;
                   `\c1 c2. abs((e:(num->num)->(num->num)->real) c1 c2)`]
           SUM_SUM_PAIRS_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c1:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c2:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[FST; SND] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_ABS_0];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (key:(num->num)#(num->num)->num->bool) S)
                  (\u. &(CARD {x | x IN S /\ key x = u}) *
                       (g:num->num->real) ((Dm:(num->bool)->num) u)
                                         (a (Dm u)))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. x IN S ==> (key:(num->num)#(num->num)->num->bool) x SUBSET P`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN EXPAND_TAC "key" THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`c1:num->num`; `c2:num->num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c1:num->num) IN col_set k P /\ (c2:num->num) IN col_set k P`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_UNION; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (key:(num->num)#(num->num)->num->bool) S)
                  (\u. (&k + &1) pow (2 * CARD u) *
                       (g:num->num->real) ((Dm:(num->bool)->num) u)
                                         (a (Dm u)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:(num->num)#(num->num)` THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S" THEN EXPAND_TAC "key" THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC PAIRS_SUPPORT_COUNT THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:(num->num)#(num->num)` o
      check (fun th -> can (find_term ((=) `P:num->bool`)) (concl th) &&
                       is_forall (concl th))) THEN
    EXPAND_TAC "key" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. bv_disc ((2 * N + (h:num->num) m) - 1) (nproduct (Wp UNION t) (\p. p))
               (a (nproduct (Wp UNION t) (\p. p))) +
        bv_disc ((N + h m) - 1) (nproduct (Wp UNION t) (\p. p))
               (a (nproduct (Wp UNION t) (\p. p))) =
        (g:num->num->real) ((Dm:(num->bool)->num) t) (a (Dm t))`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["g"; "Dm"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN D ==> FINITE(col_supp c) /\ col_supp c SUBSET P /\
                   &(nproduct (col_supp c) (\p:num. p)) < R`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->num` THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:num->num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `col_supp c SUBSET col_supp(c0:num->num) /\
                  col_supp c0 SUBSET P /\ FINITE(col_supp c0)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(c0:num->num) IN col_set k P` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `col_sub (c:num->num) c0` THEN
      REWRITE_TAC[col_sub; col_set; col_supp; SUBSET; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[];
        ASM_MESON_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
        ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET];
      ASM_MESON_TAC[SUBSET_TRANS];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `&(nproduct (col_supp(c0:num->num)) (\p:num. p))` THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC NPRODUCT_SUBSET_LE THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET; PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN S
        ==> &(nproduct ((key:(num->num)#(num->num)->num->bool) x)
                       (\p. p)) < R pow 2`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN EXPAND_TAC "key" THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`c1:num->num`; `c2:num->num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `R:real`)) (concl th) && is_forall (concl th))) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `c2:num->num` th) THEN
                         MP_TAC(SPEC `c1:num->num` th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&(nproduct (col_supp c1) (\p:num. p)) *
                &(nproduct (col_supp c2) (\p:num. p))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC NPRODUCT_UNION_LE THEN ASM_REWRITE_TAC[IN_UNION] THEN
      ASM_MESON_TAC[SUBSET; PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
      ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{t:num->bool | t SUBSET P}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC]);;

let COL_SET_SUM_SUPP = prove
 (`!k P (u:num->real).
     FINITE P
     ==> sum (col_set k P) (\c. product (col_supp c) u) =
         product P (\p. &1 + &k * u p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (col_set k P)
                  (\c. product P (\p. if c p = 0 then &1 else u p))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:num->num` THEN
    REWRITE_TAC[col_set; IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `product (col_supp c) (\p. if c p = 0 then &1 else u p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[col_supp; IN_ELIM_THM] THEN
      SIMP_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_SUPERSET THEN
      REWRITE_TAC[col_supp; IN_ELIM_THM; SUBSET] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COL_SET_SUM_PRODUCT] THEN MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `sum (1..k) (\i. if i = 0 then &1 else (u:num->real) p) =
                sum (1..k) (\i. u p)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB]]);;

let EXTENSION_SUM_BOUND = prove
 (`!k P fam (c':num->num) (u:num->real).
     FINITE P /\ fam SUBSET col_set k P /\ (!p. p IN P ==> &0 <= u p)
     ==> sum {c | c IN fam /\ col_sub c' c}
             (\c. product (col_supp c DIFF col_supp c') u)
         <= product P (\p. &1 + &k * u p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_COL_SET]; ALL_TAC] THEN
  ABBREV_TAC
    `r = \c:num->num. col_restrict (col_supp c DIFF col_supp c') c` THEN
  SUBGOAL_THEN
   `!c:num->num. col_sub c' c ==> col_supp((r:(num->num)->num->num) c) =
                               col_supp c DIFF col_supp c'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "r" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC COL_SUPP_RESTRICT THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (r:(num->num)->num->num)
                         {c | c IN fam /\ col_sub c' c})
                  (\c. product (col_supp c) u)` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`c1:num->num`; `c2:num->num`] THEN
      STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN
      UNDISCH_TAC `(r:(num->num)->num->num) c1 = r c2` THEN
      EXPAND_TAC "r" THEN REWRITE_TAC[col_restrict; FUN_EQ_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
      MAP_EVERY UNDISCH_TAC [`col_sub c' (c1:num->num)`;
       `col_sub c' (c2:num->num)`] THEN
      REWRITE_TAC[col_sub; col_supp; IN_DIFF; IN_ELIM_THM] THEN
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
                           MP_TAC(SPEC `p:num` th)) THEN
      ASM_CASES_TAC `(c':num->num) p = 0` THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM COL_SET_SUM_SUPP] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_COL_SET] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->num` THEN STRIP_TAC THEN EXPAND_TAC "r" THEN
    SUBGOAL_THEN `(c:num->num) IN col_set k P` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[col_set; col_restrict; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `p:num` THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[LE_0];
    ALL_TAC] THEN
  X_GEN_TAC `c:num->num` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:num->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(c:num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(c:num->num) IN col_set k P` THEN
    UNDISCH_TAC `(p:num) IN col_supp c` THEN
    REWRITE_TAC[col_set; col_supp; IN_ELIM_THM] THEN MESON_TAC[]]);;

let PRODUCT_SUBSET_GE1 = prove
 (`!(f:A->real) s t.
     FINITE t /\ s SUBSET t /\ (!x. x IN t ==> &1 <= f x)
     ==> product s f <= product t f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `t:A->bool`;
   `s:A->bool`] PRODUCT_DIFF_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `product (t DIFF s) (\x:A. &1)` THEN
    CONJ_TAC THENL [REWRITE_TAC[PRODUCT_ONE; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_MESON_TAC[FINITE_SUBSET; SUBSET; REAL_ARITH `&1 <= x ==> &0 <= x`]]);;

(* ------------------------------------------------------------------------- *)
(* The size of maynard_lambda.                                               *)
(* ------------------------------------------------------------------------- *)

let MAYNARD_LAMBDA_BOUND = prove
 (`!k P fam (y:(num->num)->real) ym c'.
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\ fam SUBSET col_set k P /\
     (!c. c IN fam ==> abs(y c) <= ym) /\ (?c0. c0 IN fam /\ col_sub c' c0)
     ==> abs(maynard_lambda fam
               (\c. y c / product (col_supp c) (\p. &p - &1)) c')
         <= ym * product P (\p. &1 + inv(&p - &1)) *
                 product P (\p. &1 + &k * inv(&p - &1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN P ==> &1 <= &p - &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ym` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_COL_SET]; ALL_TAC] THEN
  SUBGOAL_THEN `!c:num->num. c IN col_set k P ==> col_supp c SUBSET P`
  ASSUME_TAC THENL
   [REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c':num->num) IN col_set k P` ASSUME_TAC THENL
   [ASM_MESON_TAC[COL_SUB_SET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(col_supp c') /\ col_supp c' SUBSET P`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `F' = {c | c IN fam /\ col_sub c' (c:num->num)}` THEN
  SUBGOAL_THEN `FINITE(F':(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "F'" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN F' ==> c IN col_set k P /\ col_supp c' SUBSET col_supp c /\
                    FINITE(col_supp c) /\ col_supp c SUBSET P /\
                    abs(y c) <= ym`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:num->num` THEN EXPAND_TAC "F'" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c:num->num) IN col_set k P` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `col_sub c' (c:num->num)` THEN
      REWRITE_TAC[col_sub; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ASM_MESON_TAC[FINITE_SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[maynard_lambda] THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[GSYM PRODUCT_ABS; REAL_ABS_NEG; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `product (col_supp c') (&) *
    sum F' (\c. ym * product (col_supp c') (\p. inv(&p - &1)) *
                product (col_supp c DIFF col_supp c') (\p. inv(&p - &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum F' (\c. abs((y:(num->num)->real) c /
                                product (col_supp c) (\p. &p - &1)))` THEN
    ASM_SIMP_TAC[SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:num->num` o check (fun th ->
      can (find_term ((=) `F':(num->num)->bool`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `product (col_supp c) (\p. &p - &1) =
      product (col_supp c') (\p. &p - &1) *
      product (col_supp c DIFF col_supp c') (\p. &p - &1)`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC PRODUCT_DIFF_SPLIT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < product (col_supp c') (\p. &p - &1) /\
      &0 < product (col_supp c DIFF col_supp c') (\p. &p - &1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
      ASM_SIMP_TAC[FINITE_DIFF] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < x`) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_INV; FINITE_DIFF; REAL_ABS_DIV;
                 REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_MUL] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_RMUL THEN
           ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL] THEN
  SUBGOAL_THEN
   `product (col_supp c') (&) * ym * product (col_supp c') (\p. inv(&p - &1)) *
    sum F' (\c. product (col_supp c DIFF col_supp c') (\p. inv(&p - &1))) =
    ym * product (col_supp c') (\p. &1 + inv(&p - &1)) *
    sum F' (\c. product (col_supp c DIFF col_supp c') (\p. inv(&p - &1)))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `product (col_supp c') (\p. &1 + inv(&p - &1)) =
      product (col_supp c') (&) * product (col_supp c') (\p. inv(&p - &1))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN MATCH_MP_TAC PRODUCT_EQ THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `&1 <= &p - &1` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; CONV_TAC REAL_FIELD];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM SET_TAC[];
    MATCH_MP_TAC PRODUCT_SUBSET_GE1 THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_ADDR; REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_DIFF]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM SET_TAC[];
    EXPAND_TAC "F'" THEN MATCH_MP_TAC EXTENSION_SUM_BOUND THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM_SIMP_TAC[]]);;
