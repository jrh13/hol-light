(* ========================================================================= *)
(* Dirichlet convolution and Vaughan's identity.                             *)
(*                                                                           *)
(* dirichlet_conv f g n = sum_{d | n} f(d) g(n/d) (0 at n = 0):              *)
(* DIRICHLET_CONV_SYM, DIRICHLET_CONV_ASSOC, DIRICHLET_CONV_SUB,             *)
(* DIRICHLET_CONV_DELTA, DIRICHLET_CONV_MANGOLDT_ONE (Lambda * 1 = log); for *)
(* completely multiplicative chi the twisted partial sums regroup along the  *)
(* hyperbola (DIRICHLET_CONV_VSUM):                                          *)
(*   sum_{n<=N} (f*g)(n) chi(n) = sum_{d<=N} f(d) chi(d) sum_{k<=N/d} g(k)   *)
(*   chi(k).                                                                 *)
(* VAUGHAN_IDENTITY: with F_U = Lambda [n <= U], G_V = mu [d <= V] and       *)
(* e_V = delta - G_V * 1,                                                    *)
(*   Lambda = F_U + G_V * log - (G_V * F_U) * 1 + (Lambda - F_U) * e_V,      *)
(* a consequence of associativity, Lambda * 1 = log and mu * 1 = delta;      *)
(* VAUGHAN_VSUM is the twisted summatory form (the sums S1 - S4 of [D] 24).  *)
(* Coefficients: e_V(k) = 0 for 1 <= k <= V, |e_V(k)| <= tau_le V k =        *)
(* #{d | k, d <= V}; |(G_V * F_U)(s)| <= log s, = 0 for s > UV.              *)
(* SUM_TAU_LE_SQUARE: if every l has #{k in s, l | k} <= X/l + Y then        *)
(*   sum_{k in s} tau_le(V,k)^2 <= X (1 + log V)^3 + Y V^2,                  *)
(* from sum_{d1,d2 <= M} 1/lcm(d1,d2) <= (1 + log M)^3 (gcd(d1,d2) <=        *)
(* sum_{g | d1, g | d2} g); corollaries for 1..K and for real intervals.     *)
(* PRIME_POWER_SUM_BOUND: psi(n) - theta(n) <= sqrt n log^2 n.               *)
(* PI_THETA_NORM: partial summation from theta(k,c) = sum_{p<=k} c(p) log p  *)
(* to sum_{p<=x} c(p).                                                       *)
(* ========================================================================= *)

needs "Sieve/nt.ml";;
needs "100/dirichlet.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Dirichlet convolution.                                                    *)
(* ------------------------------------------------------------------------- *)

let dirichlet_conv = new_definition
 `dirichlet_conv (f:num->real) (g:num->real) n =
    if n = 0 then &0 else sum {d | d divides n} (\d. f d * g(n DIV d))`;;

let DIVISOR_NONZERO = prove
 (`!d n. ~(n = 0) /\ d divides n ==> ~(d = 0) /\ ~(n DIV d = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_ZERO]; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[DIV_EQ_0; NOT_LT] THEN ASM_MESON_TAC[DIVIDES_LE]);;

let DIRICHLET_CONV_EQ = prove
 (`!f g f' g'. (!n. ~(n = 0) ==> f n = f' n) /\
               (!n. ~(n = 0) ==> g n = g' n)
               ==> dirichlet_conv f g = dirichlet_conv f' g'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; dirichlet_conv] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:num`; `n:num`] DIVISOR_NONZERO) THEN
  ASM_SIMP_TAC[]);;

let DIRICHLET_CONV_SYM = prove
 (`!f g. dirichlet_conv f g = dirichlet_conv g f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; dirichlet_conv] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC LAND_CONV
     [GSYM(ISPEC `\d. (g:num->real) d * f(n DIV d)`
            (MATCH_MP SUM_DIVISORS_REFLECT th))]) THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `n DIV (n DIV d) = d` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[DIV_MULT; ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT];
    REWRITE_TAC[REAL_MUL_SYM]]);;

let DIRICHLET_CONV_ASSOC = prove
 (`!f g h. dirichlet_conv (dirichlet_conv f g) h =
           dirichlet_conv f (dirichlet_conv g h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[dirichlet_conv] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!d. d divides n ==> ~(d = 0) /\ ~(n DIV d = 0)`
  ASSUME_TAC THENL [ASM_MESON_TAC[DIVISOR_NONZERO]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {d | d divides n}
     (\d. sum {e | e divides d} (\e. f e * g(d DIV e) * h(n DIV d)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `d:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM SUM_RMUL; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {e | e divides n}
     (\e. sum {b | b divides (n DIV e)}
              (\b. f e * g b * h(n DIV e DIV b)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `e:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM SUM_LMUL]] THEN
  SUBGOAL_THEN `FINITE {d | d divides n}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_DIVISORS]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`{d | d divides n}`; `\d:num. {e | e divides d}`;
     `\d e. (f:num->real) e * (g:num->real)(d DIV e) * (h:num->real)(n DIV d)`]
     SUM_SUM_PRODUCT)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[FINITE_DIVISORS];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`{e | e divides n}`;
     `\e:num. {b | b divides (n DIV e)}`;
     `\e b. (f:num->real) e * (g:num->real) b * (h:num->real)(n DIV e DIV b)`]
     SUM_SUM_PRODUCT)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[FINITE_DIVISORS];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `\(d:num,e:num). (e, d DIV e)` THEN
  EXISTS_TAC `\(e:num,b:num). (e * b, e)` THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
  REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `p divides n` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `q divides (p * a) DIV p` THEN ASM_SIMP_TAC[DIV_MULT] THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num` SUBST_ALL_TAC) THEN
    ASM_SIMP_TAC[DIV_MULT] THEN
    MAP_EVERY EXISTS_TAC [`p * q:num`; `p:num`] THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXISTS_TAC `b:num` THEN REWRITE_TAC[MULT_AC];
                    EXISTS_TAC `q:num` THEN REWRITE_TAC[MULT_AC]];
    SUBGOAL_THEN `~(p = 0) /\ ~(q = 0)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[DIVIDES_ZERO]; ALL_TAC] THEN
    UNDISCH_TAC `q divides p` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:num` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `(q * s) divides n` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[DIV_MULT; GSYM MULT_ASSOC] THEN
    SUBGOAL_THEN `(q * s * t) DIV q = s * t /\ (q * s * t) DIV (q * s) = t`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[DIV_MULT] THEN REWRITE_TAC[MULT_ASSOC] THEN
      ASM_SIMP_TAC[DIV_MULT; MULT_EQ_0];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`q:num`; `s:num`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXISTS_TAC `s * t:num` THEN REWRITE_TAC[MULT_AC];
                    EXISTS_TAC `t:num` THEN REWRITE_TAC[]]]);;

let DIRICHLET_CONV_SUB = prove
 (`!f g h. dirichlet_conv f (\n. g n - h n) =
           \n. dirichlet_conv f g n - dirichlet_conv f h n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; dirichlet_conv] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_SUB_REFL; REAL_SUB_LDISTRIB; SUM_SUB; FINITE_DIVISORS]);;

let DIRICHLET_CONV_SUB_LEFT = prove
 (`!f g h. dirichlet_conv (\n. f n - g n) h =
           \n. dirichlet_conv f h n - dirichlet_conv g h n`,
  ONCE_REWRITE_TAC[DIRICHLET_CONV_SYM] THEN REWRITE_TAC[DIRICHLET_CONV_SUB]);;

let DIRICHLET_CONV_DELTA = prove
 (`!f n. ~(n = 0) ==> dirichlet_conv f (\k. if k = 1 then &1 else &0) n = f n`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_conv] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {d | d divides n} (\d. if d = n then f n else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `d:num` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `n DIV d = 1 <=> d = n` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
      DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
      ASM_SIMP_TAC[DIV_MULT] THEN
      REWRITE_TAC[ARITH_RULE `d = d * e <=> d * 1 = d * e:num`] THEN
      ASM_REWRITE_TAC[EQ_MULT_LCANCEL] THEN MESON_TAC[];
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO]];
    REWRITE_TAC[SUM_DELTA; IN_ELIM_THM; DIVIDES_REFL]]);;

let DIRICHLET_CONV_MANGOLDT_ONE = prove
 (`!n. ~(n = 0) ==> dirichlet_conv mangoldt (\k. &1) n = log(&n)`,
  SIMP_TAC[dirichlet_conv; REAL_MUL_RID; LOG_MANGOLDT_SUM; ETA_AX]);;

let DIRICHLET_CONV_VSUM = prove
 (`!f g (c:num->complex) N.
     (!m n. c(m * n) = c m * c n)
     ==> vsum(1..N) (\n. Cx(dirichlet_conv f g n) * c n) =
         vsum(1..N) (\d. Cx(f d) * c d *
                         vsum(1..N DIV d) (\k. Cx(g k) * c k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(1..N) (\n. vsum {d | d divides n}
     (\d. Cx(f d) * c d * (Cx(g(n DIV d)) * c(n DIV d))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[dirichlet_conv; LE_1; ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
    REWRITE_TAC[GSYM VSUM_CX] THEN
    ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_DIVISORS; LE_1;
                 ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `d:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c:num->complex) n = c d * c(n DIV d)` SUBST1_TAC THENL
     [UNDISCH_TAC `d divides n` THEN REWRITE_TAC[DIVIDES_DIV_MULT] THEN
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_SYM];
      REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING];
    REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT; LE_1;
                 ARITH_RULE `1 <= n ==> ~(n = 0)`]]);;

(* ------------------------------------------------------------------------- *)
(* Vaughan's identity.                                                       *)
(* ------------------------------------------------------------------------- *)

let vaughan_F = new_definition
 `vaughan_F U m = if &m <= U then mangoldt m else &0`;;

let vaughan_G = new_definition
 `vaughan_G V d = if &d <= V then mobius d else &0`;;

let vaughan_e = new_definition
 `vaughan_e V k =
    (if k = 1 then &1 else &0) - dirichlet_conv (vaughan_G V) (\t. &1) k`;;

let VAUGHAN_IDENTITY = prove
 (`!U V n. ~(n = 0)
     ==> mangoldt n =
         vaughan_F U n + dirichlet_conv (vaughan_G V) (\h. log(&h)) n -
         dirichlet_conv (dirichlet_conv (vaughan_G V) (vaughan_F U))
           (\t. &1) n +
         dirichlet_conv (\m. mangoldt m - vaughan_F U m) (vaughan_e V) n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `vaughan_e V = \k. (if k = 1 then &1 else &0) -
                                  dirichlet_conv (vaughan_G V) (\t. &1) k`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; vaughan_e]; ALL_TAC] THEN
  REWRITE_TAC[DIRICHLET_CONV_SUB; ETA_AX] THEN
  ASM_SIMP_TAC[DIRICHLET_CONV_DELTA] THEN
  SUBGOAL_THEN
   `dirichlet_conv (\m. mangoldt m - vaughan_F U m)
      (dirichlet_conv (vaughan_G V) (\t. &1)) n =
    dirichlet_conv (vaughan_G V) (\h. log(&h)) n -
    dirichlet_conv (dirichlet_conv (vaughan_G V) (vaughan_F U)) (\t. &1) n`
  SUBST1_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [DIRICHLET_CONV_SYM] THEN
  REWRITE_TAC[DIRICHLET_CONV_ASSOC] THEN
  SUBGOAL_THEN
   `dirichlet_conv (vaughan_G V)
      (dirichlet_conv (\t. &1) (\m. mangoldt m - vaughan_F U m)) =
    dirichlet_conv (vaughan_G V)
      (\h. log(&h) - dirichlet_conv (vaughan_F U) (\t. &1) h)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC DIRICHLET_CONV_EQ THEN REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [DIRICHLET_CONV_SYM] THEN
    REWRITE_TAC[DIRICHLET_CONV_SUB_LEFT; ETA_AX] THEN
    ASM_SIMP_TAC[DIRICHLET_CONV_MANGOLDT_ONE];
    REWRITE_TAC[DIRICHLET_CONV_SUB; ETA_AX]]);;

let VAUGHAN_VSUM = prove
 (`!U V (c:num->complex) N.
     (!m n. c(m * n) = c m * c n)
     ==> vsum(1..N) (\n. Cx(mangoldt n) * c n) =
         vsum(1..N) (\n. Cx(vaughan_F U n) * c n) +
         vsum(1..N) (\d. Cx(vaughan_G V d) * c d *
                         vsum(1..N DIV d) (\h. Cx(log(&h)) * c h)) -
         vsum(1..N)
           (\s. Cx(dirichlet_conv (vaughan_G V) (vaughan_F U) s) * c s *
                         vsum(1..N DIV s) c) +
         vsum(1..N) (\m. Cx(mangoldt m - vaughan_F U m) * c m *
                         vsum(1..N DIV m) (\k. Cx(vaughan_e V k) * c k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum(1..N) (\n. Cx(vaughan_F U n) * c n +
                    Cx(dirichlet_conv (vaughan_G V) (\h. log(&h)) n) * c n -
                    Cx(dirichlet_conv
                         (dirichlet_conv (vaughan_G V) (vaughan_F U))
                           (\t. &1) n) *
                    c n +
                    Cx(dirichlet_conv (\m. mangoldt m - vaughan_F U m)
                             (vaughan_e V) n) *
                    c n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MP_TAC(SPECL [`U:real`; `V:real`;
     `n:num`] VAUGHAN_IDENTITY) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[CX_ADD; CX_SUB] THEN CONV_TAC COMPLEX_RING;
    SIMP_TAC[VSUM_ADD; VSUM_SUB; FINITE_NUMSEG] THEN
    ASM_SIMP_TAC[DIRICHLET_CONV_VSUM] THEN
    REWRITE_TAC[COMPLEX_MUL_LID; ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* The coefficients.                                                         *)
(* ------------------------------------------------------------------------- *)

let tau_le = new_definition
 `tau_le V k = CARD {d | d divides k /\ &d <= V}`;;

let VAUGHAN_E_SMALL = prove
 (`!V k. 1 <= k /\ &k <= V ==> vaughan_e V k = &0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[vaughan_e; dirichlet_conv; LE_1;
               ARITH_RULE `1 <= k ==> ~(k = 0)`] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> y - x = &0:real`) THEN
  ASM_SIMP_TAC[GSYM DIVISORSUM_MOBIUS; REAL_MUL_RID] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; vaughan_G] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&d <= V` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k:real` THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC);;

let VAUGHAN_E_BOUND = prove
 (`!V k. &1 <= V ==> abs(vaughan_e V k) <= &(tau_le V k)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[vaughan_e; dirichlet_conv; ARITH_RULE `~(0 = 1)`] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_POS];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
   [MP_TAC(SPECL [`V:real`; `k:num`] VAUGHAN_E_SMALL) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_ABS_NUM; REAL_POS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[vaughan_e; dirichlet_conv; REAL_MUL_RID; REAL_SUB_LZERO] THEN
  REWRITE_TAC[REAL_ABS_NEG; vaughan_G; tau_le] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `FINITE {d | d IN {d | d divides k} /\ &d <= V}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_SIMP_TAC[FINITE_DIVISORS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {d | d IN {d | d divides k} /\ &d <= V} (\d. &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[REAL_ABS_MOBIUS];
    ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID; IN_ELIM_THM; REAL_LE_REFL]]);;

let VAUGHAN_C_BOUND = prove
 (`!U V s. ~(s = 0)
           ==> abs(dirichlet_conv (vaughan_G V) (vaughan_F U) s) <= log(&s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_conv] THEN
  ASM_SIMP_TAC[LOG_MANGOLDT_SUM] THEN REWRITE_TAC[ETA_AX] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
    [GSYM(ISPEC `mangoldt` (MATCH_MP SUM_DIVISORS_REFLECT th))]) THEN
  MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  REWRITE_TAC[vaughan_G; vaughan_F] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ABS_NUM;
              MANGOLDT_POS_LE] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_MOBIUS; REAL_ABS_POS] THEN
  REWRITE_TAC[real_abs; MANGOLDT_POS_LE; REAL_LE_REFL]);;

let VAUGHAN_C_ZERO = prove
 (`!U V s. U * V < &s ==> dirichlet_conv (vaughan_G V) (vaughan_F U) s = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dirichlet_conv] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  REWRITE_TAC[vaughan_G; vaughan_F] THEN
  ASM_CASES_TAC `&d <= V` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  ASM_CASES_TAC `&(s DIV d) <= U` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  UNDISCH_TAC `U * V < &s` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DIVIDES_DIV_MULT]) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
    [GSYM th]) THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS]);;

let TAU_LE_DIVIDES_MONO = prove
 (`!V k n. k divides n /\ ~(n = 0) ==> tau_le V k <= tau_le V n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tau_le] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[DIVIDES_TRANS];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d | d divides n}` THEN
    ASM_SIMP_TAC[FINITE_DIVISORS] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Mean square of tau_le.                                                    *)
(* ------------------------------------------------------------------------- *)

let TAU_LE_SUM = prove
 (`!V M k. ~(k = 0) /\ &M <= V /\ V < &M + &1
           ==> &(tau_le V k) =
               sum(1..M) (\d. if d divides k then &1 else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tau_le] THEN
  SUBGOAL_THEN
   `{d | d divides k /\ &d <= V} = {d | d IN 1..M /\ d divides k}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `d:num` THEN ASM_CASES_TAC `d divides k` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= d <=> ~(d = 0)`] THEN
      ASM_MESON_TAC[DIVIDES_ZERO];
      ASM_REWRITE_TAC[]] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN `&d < &M + &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
        ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M:real` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUM_RESTRICT_SET]]);;

let SUM_MULTIPLES = prove
 (`!f g M. ~(g = 0)
           ==> sum(1..M) (\d. if g divides d then f d else &0) =
               sum(1..M DIV g) (\e. f(g * e))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN
   `{d | d IN 1..M /\ g divides d} = IMAGE (\e. g * e) (1..M DIV g)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `d:num` THEN ASM_SIMP_TAC[LE_RDIV_EQ] THEN EQ_TAC THENL
     [REWRITE_TAC[divides] THEN STRIP_TAC THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `1 <= g * x` THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
      MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `1 <= e` THEN UNDISCH_TAC `~(g = 0)` THEN
        REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
        MESON_TAC[];
        REWRITE_TAC[divides] THEN MESON_TAC[]]];
    ASM_SIMP_TAC[SUM_IMAGE; EQ_MULT_LCANCEL] THEN REWRITE_TAC[o_DEF]]);;

let CARD_REAL_INTERVAL = prove
 (`!x y. x <= y ==> &(CARD {t | x < &t /\ &t <= y}) <= y - x + &1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `y < &0` THENL
   [SUBGOAL_THEN `{t | x < &t /\ &t <= y} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
      X_GEN_TAC `t:num` THEN MP_TAC(SPEC `t:num` REAL_POS) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CARD_CLAUSES] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `y:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ny:num`) THEN
  MP_TAC(SPEC `y:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x < &0` THENL
   [SUBGOAL_THEN `{t | x < &t /\ &t <= y} = 0..ny` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `t:num` THEN MP_TAC(SPEC `t:num` REAL_POS) THEN
      DISCH_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      EQ_TAC THEN STRIP_TAC THENL
       [SUBGOAL_THEN `&t < &ny + &1` MP_TAC THENL
         [ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
          ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[CARD_NUMSEG; ARITH_RULE `(n + 1) - 0 = n + 1`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `nx:num`) THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{t | x < &t /\ &t <= y} = (nx + 1)..ny` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `t:num` THEN EQ_TAC THEN STRIP_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `&nx < &t` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
        SUBGOAL_THEN `&t < &ny + &1` MP_TAC THENL
         [ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC]];
      CONJ_TAC THENL
       [SUBGOAL_THEN `&nx + &1 <= &t` MP_TAC THENL
         [ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE];
          ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `&t <= &ny` MP_TAC THENL
         [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ASM_REAL_ARITH_TAC]]];
    REWRITE_TAC[CARD_NUMSEG] THEN
    ASM_CASES_TAC `nx + 1 <= ny + 1` THENL
     [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(ny + 1) - (nx + 1) = 0` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]]]);;

let CARD_MULTIPLES_INTERVAL = prove
 (`!l a b. 1 <= l /\ a <= &b
           ==> &(CARD {k | k IN {k | a < &k /\ k <= b} /\ l divides k})
               <= (&b - a) / &l + &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &l` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {t | a / &l < &t /\ &t <= &b / &l}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..b` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `t:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&b / &l` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {t | a / &l < &t /\ &t <= &b / &l})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD(IMAGE (\t. l * t) {t | a / &l < &t /\ &t <= &b / &l})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `k:num` THEN REWRITE_TAC[divides] THEN STRIP_TAC THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `x:num` THEN
      REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_MUL;
       GSYM REAL_OF_NUM_LE]) THEN
      CONJ_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CARD_IMAGE_LE]];
    MP_TAC(SPECL [`a / &l`; `&b / &l`] CARD_REAL_INTERVAL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_DIV2_EQ]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_SUB_RDISTRIB]]);;

let SUM_DIVISOR_RECIP_LE = prove
 (`!g M. 1 <= g /\ 1 <= M
         ==> &0 <= sum(1..M) (\d. if g divides d then inv(&d) else &0) /\
             sum(1..M) (\d. if g divides d then inv(&d) else &0)
             <= inv(&g) * (&1 + log(&M))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_MULTIPLES; ARITH_RULE `1 <= g ==> ~(g = 0)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_INV_MUL; SUM_LMUL] THEN
  SUBGOAL_THEN `&0 < inv(&g)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(1..M DIV g) (\e. inv(&e))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_CASES_TAC `M DIV g = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `~(1 = 0)`] THEN
    MP_TAC(SPEC `&M:real` LOG_POS) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 + log(&(M DIV g))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HARMONIC_LE_LOG THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> &1 + a <= &1 + b:real`) THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[DIV_LE]]);;

let SUM_INV_LCM_LE = prove
 (`!M. 1 <= M
       ==> sum(1..M) (\d1. sum(1..M) (\d2. inv(&(lcm(d1,d2)))))
           <= (&1 + log(&M)) pow 3`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..M) (\d1. sum(1..M) (\d2. sum(1..M)
      (\g. &g * (if g divides d1 then inv(&d1) else &0) *
               (if g divides d2 then inv(&d2) else &0))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `d1:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `d2:num` THEN
      STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `inv(&(lcm(d1,d2))) = &(gcd(d1,d2)) * inv(&d1) * inv(&d2)`
    SUBST1_TAC THENL
     [MP_TAC(SPECL [`d1:num`; `d2:num`] MULT_GCD_LCM) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
      SUBGOAL_THEN `~(&d1 = &0) /\ ~(&d2 = &0) /\ ~(&(lcm(d1,d2)) = &0)`
      MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ; LCM_ZERO] THEN ASM_ARITH_TAC;
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`{gcd(d1,d2)}`; `1..M`;
      `\g. &g * (if g divides d1 then inv(&d1) else &0) *
               (if g divides d2 then inv(&d2) else &0)`]
     SUM_SUBSET_SIMPLE) THEN
    REWRITE_TAC[SUM_SING; FINITE_NUMSEG; GCD] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SING; IN_NUMSEG] THEN
      X_GEN_TAC `g:num` THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; GCD_ZERO] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `d1:num` THEN
        ASM_REWRITE_TAC[GCD_LE] THEN ASM_ARITH_TAC];
      X_GEN_TAC `g:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `S = \g. sum(1..M) (\d. if g divides d then inv(&d) else &0)` THEN
  SUBGOAL_THEN
   `sum(1..M) (\d1. sum(1..M) (\d2. sum(1..M)
      (\g. &g * (if g divides d1 then inv(&d1) else &0) *
               (if g divides d2 then inv(&d2) else &0)))) =
    sum(1..M) (\g. &g * (S:num->real) g pow 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..M) (\d1. sum(1..M) (\g. sum(1..M) (\d2.
        &g * (if g divides d1 then inv(&d1) else &0) *
             (if g divides d2 then inv(&d2) else &0))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `g:num` THEN STRIP_TAC THEN
    EXPAND_TAC "S" THEN
    REWRITE_TAC[REAL_POW_2; SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN
    SIMP_TAC[REAL_MUL_SUM; FINITE_NUMSEG; GSYM SUM_LMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..M) (\g. inv(&g) * (&1 + log(&M)) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `g:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`g:num`; `M:num`] SUM_DIVISOR_RECIP_LE) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&g * (inv(&g) * (&1 + log(&M))) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(&g = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
        CONV_TAC REAL_FIELD]];
    REWRITE_TAC[SUM_RMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `(x:real) pow 3 = x * x pow 2`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC HARMONIC_LE_LOG THEN ASM_REWRITE_TAC[]]);;

let SUM_TAU_LE_SQUARE = prove
 (`!V s X Y. &1 <= V /\ FINITE s /\ (!k. k IN s ==> ~(k = 0)) /\
             &0 <= X /\ &0 <= Y /\
             (!l. 1 <= l
                  ==> &(CARD {k | k IN s /\ l divides k}) <= X / &l + Y)
             ==> sum s (\k. &(tau_le V k) pow 2)
                 <= X * (&1 + log V) pow 3 + Y * V pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `V:real` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  MP_TAC(SPEC `V:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= M` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &M` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum s (\k. &(tau_le V k) pow 2) =
    sum(1..M) (\d1. sum(1..M) (\d2.
      sum s (\k. if lcm(d1,d2) divides k then &1 else &0)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum s (\k. sum(1..M) (\d1. sum(1..M) (\d2.
        if lcm(d1,d2) divides k then &1 else &0)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(SPECL [`V:real`; `M:num`; `k:num`] TAU_LE_SUM) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      SIMP_TAC[REAL_POW_2; REAL_MUL_SUM; FINITE_NUMSEG] THEN
      REWRITE_TAC[LCM_DIVIDES; REAL_ARITH
       `(if p then &1 else &0) * (if q then &1 else &0) =
        (if p /\ q then &1 else &0):real`];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..M) (\d1. sum s (\k. sum(1..M) (\d2.
        if lcm(d1,d2) divides k then &1 else &0)))` THEN
    CONJ_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL
       [`\k d1. sum(1..M) (\d2. if lcm(d1,d2) divides k then &1 else &0)`;
        `s:num->bool`; `1..M`] SUM_SWAP)) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG];
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d1:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(BETA_RULE(ISPECL
       [`\k d2. if lcm(d1,d2) divides k then &1 else &0`;
        `s:num->bool`; `1..M`] SUM_SWAP)) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..M) (\d1. sum(1..M) (\d2.
                X * inv(&(lcm(d1,d2))) + Y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `d1:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `d2:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC[GSYM CARD_EQ_SUM; FINITE_RESTRICT] THEN
    REWRITE_TAC[GSYM real_div] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; LCM_ZERO] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG; ADD_SUB] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + log(&M)) pow 3` THEN
    ASM_SIMP_TAC[SUM_INV_LCM_LE] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MP_TAC(SPEC `&M:real` LOG_POS) THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> &1 + a <= &1 + b:real`) THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC];
    SUBGOAL_THEN `&M * &M * Y = Y * &M pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS]]);;

let SUM_TAU_LE_SQUARE_NUMSEG = prove
 (`!V K. &1 <= V
         ==> sum(1..K) (\k. &(tau_le V k) pow 2)
             <= &K * (&1 + log V) pow 3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`V:real`; `1..K`; `&K:real`; `&0:real`] SUM_TAU_LE_SQUARE) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_ADD_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_POS; REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_MULTIPLES_LE THEN ASM_ARITH_TAC]);;

let SUM_TAU_LE_SQUARE_INTERVAL = prove
 (`!V a b. &1 <= V /\ &0 <= a /\ a <= &b
           ==> sum {k | a < &k /\ k <= b} (\k. &(tau_le V k) pow 2)
               <= (&b - a) * (&1 + log V) pow 3 + V pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`V:real`; `{k | a < &k /\ k <= b}`; `&b - a`; `&1`]
    SUM_TAU_LE_SQUARE) THEN
  REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..b` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    MESON_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_MULTIPLES_INTERVAL THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Prime powers.                                                             *)
(* ------------------------------------------------------------------------- *)

let PRIME_POWER_SUM_BOUND = prove
 (`!n. 1 <= n
       ==> sum(1..n) (\m. mangoldt m - (if prime m then log(&m) else &0))
           <= sqrt(&n) * log(&n) pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[SUM_SING_NUMSEG; MANGOLDT_1; PRIME_1; LOG_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Q = {(p,k) | prime p /\ 2 <= k /\ p EXP k <= n}` THEN
  ABBREV_TAC `A = {p | &1 < &p /\ &p <= sqrt(&n)}` THEN
  ABBREV_TAC `B = {k | &1 < &k /\ &k <= log(&n) / log(&2)}` THEN
  SUBGOAL_THEN `&0 < log(&2) /\ &0 < log(&n)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(A:num->bool) /\ FINITE(B:num->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[FINITE_NUM_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:num#num->bool) SUBSET {(p,k) | p IN A /\ k IN B}`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "A"; "B"] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LE_EXP;
       ARITH_RULE `2 <= p ==> ~(p = 0)`] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      ASM_SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [REWRITE_TAC[EXP_LT_0] THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(Q:num#num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(p,k) | p IN (A:num->bool) /\ k IN (B:num->bool)}` THEN
    ASM_SIMP_TAC[FINITE_PRODUCT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(IMAGE (\x. FST x EXP SND x) (Q:num#num->bool))
                 (\m. if prime m then &0 else mangoldt m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..n) (\m. if prime m then &0 else mangoldt m)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
      MP_TAC(SPECL [`m:num`; `1`] MANGOLDT_PRIMEPOW) THEN
      ASM_REWRITE_TAC[EXP_1; LE_REFL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_SUBSET THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_IMAGE] THEN CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN
      REWRITE_TAC[IN_DIFF; IN_NUMSEG; IN_IMAGE; NOT_EXISTS_THM] THEN
      STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      REWRITE_TAC[mangoldt] THEN COND_CASES_TAC THEN
      REWRITE_TAC[REAL_LE_REFL] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `k:num`
        STRIP_ASSUME_TAC) o check (is_exists o concl)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(p:num,k:num)`) THEN
      EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `2 <= k /\ p EXP k <= n` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `~prime m` THEN ASM_REWRITE_TAC[PRIME_EXP] THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; MANGOLDT_POS_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (Q:num#num->bool) (\x. log(&(FST x)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (Q:num#num->bool)
                  ((\m. if prime m then &0 else mangoldt m) o
                       (\x. FST x EXP SND x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_IMAGE_LE THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN DISCH_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; MANGOLDT_POS_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      EXPAND_TAC "Q" THEN
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; o_DEF] THEN
      MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[PRIME_EXP; ARITH_RULE `2 <= k ==> ~(k = 1)`] THEN
      ASM_SIMP_TAC[MANGOLDT_PRIMEPOW; ARITH_RULE `2 <= k ==> 1 <= k`;
                   ARITH_RULE `2 <= k ==> ~(k = 1)`]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(Q:num#num->bool)) * (log(&n) / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &2`] THEN
    SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM LOG_POW] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LE_EXP;
     ARITH_RULE `2 <= p ==> ~(p = 0)`] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(sqrt(&n) * log(&n) / log(&2)) * (log(&n) / &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&(CARD {(p,k) | p IN (A:num->bool) /\ k IN (B:num->bool)})` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_PRODUCT];
      ASM_SIMP_TAC[CARD_PRODUCT; GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
      MAP_EVERY EXPAND_TAC ["A"; "B"] THEN CONJ_TAC THENL
       [MP_TAC(SPECL [`&1`; `sqrt(&n)`] CARD_REAL_INTERVAL) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC REAL_LE_RSQRT THEN
          REWRITE_TAC[REAL_POW_2; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
          ASM_ARITH_TAC;
          DISCH_TAC THEN
          MATCH_MP_TAC(REAL_ARITH `x <= y - &1 + &1 ==> x <= y:real`) THEN
          FIRST_ASSUM ACCEPT_TAC];
        MP_TAC(SPECL [`&1`; `log(&n) / log(&2)`] CARD_REAL_INTERVAL) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
          MATCH_MP_TAC LOG_MONO_LE_IMP THEN
          REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
          DISCH_TAC THEN
          MATCH_MP_TAC(REAL_ARITH `x <= y - &1 + &1 ==> x <= y:real`) THEN
          FIRST_ASSUM ACCEPT_TAC]]];
    ALL_TAC] THEN
  MP_TAC LOG_2_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(&n) * log(&n) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_POW_2] THEN
  SUBGOAL_THEN `inv(log(&2)) * inv(&2) <= &1` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(sqrt(&n) * log(&n) * log(&n)) * (inv(log(&2)) * inv(&2))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From theta to sums over primes.                                           *)
(* ------------------------------------------------------------------------- *)

let PI_THETA_NORM = prove
 (`!x (c:num->complex).
     2 <= x
     ==> norm(vsum {p | prime p /\ p <= x} c)
         <= inv(log(&x + &1)) *
            norm(vsum(1..x) (\m. Cx(if prime m then log(&m) else &0) * c m)) +
            sum(2..x) (\k. (inv(log(&k)) - inv(log(&k + &1))) *
              norm(vsum(1..k)
                     (\m. Cx(if prime m then log(&m) else &0) * c m)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `th = \k. vsum(1..k) (\m. Cx(if prime m then log(&m) else &0) *
                                       (c:num->complex) m)` THEN
  MP_TAC(ISPECL [`\k. inv(log(&k))`; `\k. (th:num->complex)(k - 1)`;
                 `2`; `x:num`] VSUM_PARTIAL_SUC) THEN
  ASM_REWRITE_TAC[ADD_SUB] THEN
  SUBGOAL_THEN `(th:num->complex)(2 - 1) = Cx(&0)` SUBST1_TAC THENL
   [EXPAND_TAC "th" THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[VSUM_SING_NUMSEG; PRIME_1; COMPLEX_MUL_LZERO];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN
   `vsum(2..x) (\k. inv(log(&k)) % ((th:num->complex) k - th(k - 1))) =
    vsum {p | prime p /\ p <= x} c`
  SUBST1_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "th" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:complex) <= x /\ norm(b) <= y ==> norm(a - b) <= x + y`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NORM_MUL; GSYM REAL_OF_NUM_ADD] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
      REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC LOG_POS THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `y <= x ==> abs(y - x) = x - y`) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN CONJ_TAC THENL
       [ASM_ARITH_TAC; REAL_ARITH_TAC]]] THEN
  EXPAND_TAC "th" THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(2..x) (\k. if prime k then c k else Cx(&0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\m. Cx(if prime m then log(&m) else &0) *
                        (c:num->complex) m`; `1`; `k:num`]
      VSUM_CLAUSES_RIGHT) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `(a + b) - a:complex = b`] THEN
    REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; COMPLEX_MUL_LZERO] THEN
    SUBGOAL_THEN `~(log(&k) = &0)` (fun th ->
      REWRITE_TAC[MATCH_MP REAL_MUL_LINV th; COMPLEX_MUL_LID]) THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM VSUM_RESTRICT_SET; GSYM COMPLEX_VEC_0] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    MESON_TAC[PRIME_GE_2]]);;
