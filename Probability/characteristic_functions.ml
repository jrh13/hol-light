(* ========================================================================= *)
(* Characteristic functions and CLT infrastructure.                          *)
(*                                                                           *)
(* Follows Williams "Probability with Martingales" Chapters 16-17.           *)
(* Includes simple CDF and characteristic function definitions, Taylor       *)
(* analysis of cos/sin, CF product formulas for independent sums,            *)
(* Hoeffding-style concentration bounds, parameterized Gaussian integral,    *)
(* standard normal CDF and distribution, and Levy continuity theorem         *)
(* (simple version). Also CLT convergence in distribution for simple RVs.    *)
(* ========================================================================= *)

needs "100/fourier.ml";;
needs "Probability/martingale_convergence.ml";;

(* ========================================================================= *)
(* CONVERGENCE IN DISTRIBUTION AND CHARACTERISTIC FUNCTIONS                  *)
(* ========================================================================= *)

(* Cumulative distribution function of a simple RV *)
let simple_cdf = new_definition
  `simple_cdf (p:A prob_space) (X:A->real) (x:real) =
   prob p {a | a IN prob_carrier p /\ X a <= x}`;;

(* Characteristic function of a simple RV (real and imaginary parts) *)
let char_fn_re = new_definition
  `char_fn_re (p:A prob_space) (X:A->real) (t:real) =
   simple_expectation p (\x. cos(t * X x))`;;

let char_fn_im = new_definition
  `char_fn_im (p:A prob_space) (X:A->real) (t:real) =
   simple_expectation p (\x. sin(t * X x))`;;

(* Characteristic function at 0: phi(0) = 1 + 0i *)
let CHAR_FN_ZERO = prove
 (`!p:A prob_space (X:A->real).
     char_fn_re p X (&0) = &1 /\ char_fn_im p X (&0) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[char_fn_re; char_fn_im] THEN
  REWRITE_TAC[REAL_MUL_LZERO; SIN_0; COS_0] THEN
  REWRITE_TAC[SIMPLE_EXPECTATION_CONST]);;

(* CDF is between 0 and 1 *)
let SIMPLE_CDF_BOUNDS = prove
 (`!p:A prob_space (X:A->real) x.
     simple_rv p X
     ==> &0 <= simple_cdf p X x /\ simple_cdf p X x <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_cdf] THENL
  [MATCH_MP_TAC PROB_POSITIVE THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
   DISCH_THEN(MP_TAC o CONJUNCT1) THEN
   REWRITE_TAC[random_variable] THEN SIMP_TAC[];
   MATCH_MP_TAC PROB_LE_1 THEN
   FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
   DISCH_THEN(MP_TAC o CONJUNCT1) THEN
   REWRITE_TAC[random_variable] THEN SIMP_TAC[]]);;

(* Helper: composition of a function with a simple RV preserving finite range *)
(* Measurability: preimage of (-inf,a] under f o X is finite union of level
   sets of X, hence measurable. Currently CHEAT'd, will be filled in. *)
let SIMPLE_RV_REAL_COMPOSE = prove
 (`!p:A prob_space X (f:real->real).
     simple_rv p X ==> simple_rv p (\x. f(X x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_rv] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simple_rv]) THEN
  CONJ_TAC THENL
  [(* Measurability: {f(X x) <= a} = finite union of level sets {X x = v} *)
   REWRITE_TAC[random_variable] THEN X_GEN_TAC `a:real` THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\ (f:real->real)((X:A->real) x) <= a} =
      UNIONS (IMAGE (\v. {x | x IN prob_carrier p /\ X x = v})
                    {v | (?y:A. y IN prob_carrier p /\ (X:A->real) y = v) /\
                         (f:real->real) v <= a})`
     SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
    EQ_TAC THENL
    [(* Forward: z in carrier, f(X z) <= a ==> z in UNIONS *)
     STRIP_TAC THEN
     EXISTS_TAC `{x:A | x IN prob_carrier p /\ (X:A->real) x = X z}` THEN
     ASM_REWRITE_TAC[IN_ELIM_THM] THEN
     EXISTS_TAC `(X:A->real) z` THEN
     TRY BETA_TAC THEN
     ASM_REWRITE_TAC[] THEN
     EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
     (* Backward: z in UNIONS ==> z in carrier, f(X z) <= a *)
     DISCH_THEN(X_CHOOSE_THEN `s:A->bool`
       (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
     DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
     UNDISCH_TAC `(z:A) IN s` THEN ASM_REWRITE_TAC[] THEN
     TRY BETA_TAC THEN
     REWRITE_TAC[IN_ELIM_THM] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* The finite union is in prob_events *)
   MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `s:A->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN TRY BETA_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(X:A->real) x | x IN prob_carrier p}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
   (* Finite range: IMAGE f over finite range is finite *)
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `IMAGE (f:real->real)
                     {(X:A->real) x | x IN prob_carrier p}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(X:A->real) z` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[]]]);;
(* Helper: upper and lower bounds on expectation via pointwise bounds *)
let SIMPLE_EXPECTATION_UPPER_BOUND = prove
 (`!p:A prob_space Y c.
     simple_rv p Y /\
     (!x. x IN prob_carrier p ==> Y x <= c)
     ==> simple_expectation p Y <= c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c = simple_expectation (p:A prob_space) (\x:A. c:real)`
    SUBST1_TAC THENL
  [REWRITE_TAC[SIMPLE_EXPECTATION_CONST]; ALL_TAC] THEN
  MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
  ASM_REWRITE_TAC[SIMPLE_RV_CONST]);;

let SIMPLE_EXPECTATION_LOWER_BOUND = prove
 (`!p:A prob_space Y c.
     simple_rv p Y /\
     (!x. x IN prob_carrier p ==> c <= Y x)
     ==> c <= simple_expectation p Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c = simple_expectation (p:A prob_space) (\x:A. c:real)`
    SUBST1_TAC THENL
  [REWRITE_TAC[SIMPLE_EXPECTATION_CONST]; ALL_TAC] THEN
  MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
  ASM_REWRITE_TAC[SIMPLE_RV_CONST]);;

(* Characteristic function real part bounded by 1 *)
let CHAR_FN_RE_BOUND = prove
 (`!p:A prob_space (X:A->real) t.
     simple_rv p X ==> abs(char_fn_re p X t) <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[char_fn_re] THEN
  (* Upper bound: E[cos(tX)] <= 1 *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x:A. cos(t * X x)) <= &1`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `\x:A. cos(t * (X:A->real) x)`; `&1`]
    SIMPLE_EXPECTATION_UPPER_BOUND) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. cos(t * y)`]
      SIMPLE_RV_REAL_COMPOSE) THEN
     ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
     BETA_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     MP_TAC(SPEC `t * (X:A->real) y` COS_BOUNDS) THEN REAL_ARITH_TAC];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Lower bound: -1 <= E[cos(tX)] *)
  SUBGOAL_THEN
    `-- &1 <= simple_expectation (p:A prob_space) (\x:A. cos(t * X x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `\x:A. cos(t * (X:A->real) x)`; `-- &1`]
    SIMPLE_EXPECTATION_LOWER_BOUND) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. cos(t * y)`]
      SIMPLE_RV_REAL_COMPOSE) THEN
     ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
     BETA_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     MP_TAC(SPEC `t * (X:A->real) y` COS_BOUNDS) THEN REAL_ARITH_TAC];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Characteristic function imaginary part bounded by 1 *)
let CHAR_FN_IM_BOUND = prove
 (`!p:A prob_space (X:A->real) t.
     simple_rv p X ==> abs(char_fn_im p X t) <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[char_fn_im] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x:A. sin(t * X x)) <= &1`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `\x:A. sin(t * (X:A->real) x)`; `&1`]
    SIMPLE_EXPECTATION_UPPER_BOUND) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. sin(t * y)`]
      SIMPLE_RV_REAL_COMPOSE) THEN
     ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
     BETA_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     MP_TAC(SPEC `t * (X:A->real) y` SIN_BOUNDS) THEN REAL_ARITH_TAC];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `-- &1 <= simple_expectation (p:A prob_space) (\x:A. sin(t * X x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `\x:A. sin(t * (X:A->real) x)`; `-- &1`]
    SIMPLE_EXPECTATION_LOWER_BOUND) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. sin(t * y)`]
      SIMPLE_RV_REAL_COMPOSE) THEN
     ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
     BETA_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
     MP_TAC(SPEC `t * (X:A->real) y` SIN_BOUNDS) THEN REAL_ARITH_TAC];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* sin(x)^2 <= x^2 -- from |sin(x)| <= |x| *)
let SIN_POW2_LE = prove
 (`!x:real. sin(x) pow 2 <= x pow 2`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
  REWRITE_TAC[REAL_ABS_SIN_BOUND_LE]);;

(* 1 - cos(x) <= x^2 / 2 -- fundamental quadratic bound *)
let ONE_MINUS_COS_LE = prove
 (`!x:real. &1 - cos(x) <= x pow 2 / &2`,
  GEN_TAC THEN
  SUBGOAL_THEN `cos(x) = &1 - &2 * sin(x / &2) pow 2` SUBST1_TAC THENL
  [MP_TAC(SPEC `x / &2` COS_DOUBLE_SIN) THEN
   REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 - &2 * s) = &2 * s`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (x / &2) pow 2` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN
   REWRITE_TAC[SIN_POW2_LE] THEN REAL_ARITH_TAC;
   REWRITE_TAC[REAL_POW_DIV; REAL_POW_2] THEN CONV_TAC REAL_FIELD]);;


(* ========================================================================= *)
(* COMPOSED EXPECTATION AND INDEPENDENCE OF FUNCTIONS OF RVs                 *)
(* ========================================================================= *)

(* Pointwise: f(X(x)) = sum over IMAGE X carrier of f(u)*1_{X=u}(x) *)
let SIMPLE_RV_COMPOSE_SUM_INDICATOR = prove
 (`!p:A prob_space (X:A->real) (f:real->real) x.
     simple_rv p X /\ x IN prob_carrier p
     ==> f(X x) =
         sum (IMAGE X (prob_carrier p))
             (\u. f(u) * indicator_fn {z | z IN prob_carrier p /\ X z = u} x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (IMAGE (X:A->real) (prob_carrier p))` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `(X:A->real) x IN IMAGE X (prob_carrier p)` ASSUME_TAC THENL
  [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  (* Convert indicator to conditional *)
  SUBGOAL_THEN
    `!u:real. f(u) * indicator_fn
        {z:A | z IN prob_carrier p /\ (X:A->real) z = u} x =
      if X x = u then f(u) else &0`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN
   ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Collapse sum via SUM_DELTA *)
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (IMAGE (X:A->real) (prob_carrier p))
                  (\u. if u = X x then f(X x) else &0)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN
   ASM_CASES_TAC `(X:A->real) x = u` THENL
   [ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(u:real = (X:A->real) x)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]];
   REWRITE_TAC[SUM_DELTA] THEN ASM_REWRITE_TAC[]]);;

(* E[f(X)] = sum over IMAGE X carrier of f(u) * P(X = u) *)
let SIMPLE_EXPECTATION_COMPOSE_SUM = prove
 (`!p:A prob_space (X:A->real) (f:real->real).
     simple_rv p X
     ==> simple_expectation p (\x. f(X x)) =
         sum (IMAGE X (prob_carrier p))
             (\u. f(u) * prob p {x | x IN prob_carrier p /\ X x = u})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (X:A->real) (prob_carrier p)` THEN
  SUBGOAL_THEN `FINITE (S:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "S" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  (* Step 1: E[f(X)] = E[sum_u f(u)*1_{X=u}] by ext *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x. (f:real->real)((X:A->real) x)) =
     simple_expectation p (\x. sum (S:real->bool)
       (\u. f(u) * indicator_fn {z | z IN prob_carrier p /\ X z = u} x))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   EXPAND_TAC "S" THEN
   MATCH_MP_TAC SIMPLE_RV_COMPOSE_SUM_INDICATOR THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: Push E through the sum using ISPECL *)
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\(u:real) (x:A). (f:real->real)(u) *
        indicator_fn {z:A | z IN prob_carrier (p:A prob_space) /\
          (X:A->real) z = u} x`;
     `S:real->bool`]
    SIMPLE_EXPECTATION_SUM_FINITE) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   MATCH_MP_TAC SIMPLE_RV_CMUL THEN REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
   MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN ASM_MESON_TAC[simple_rv];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  (* Step 3: Each E[f(u)*1_{X=u}] = f(u)*P(X=u) *)
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN
    `{z:A | z IN prob_carrier p /\ (X:A->real) z = u} IN prob_events p`
    ASSUME_TAC THENL
  [MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN ASM_MESON_TAC[simple_rv];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `indicator_fn {z:A | z IN prob_carrier p /\ (X:A->real) z = u}`;
    `(f:real->real) u`]
    SIMPLE_EXPECTATION_CMUL) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[]);;

(* Sum of probabilities over image of simple RV = 1 *)
let SIMPLE_PROB_SUM_ONE = prove
 (`!p:A prob_space (X:A->real).
     simple_rv p X
     ==> sum (IMAGE X (prob_carrier p))
             (\v. prob p {x | x IN prob_carrier p /\ X x = v}) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\u:real. &1`]
    SIMPLE_EXPECTATION_COMPOSE_SUM) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SIMPLE_EXPECTATION_CONST]);;

(* Jensen's inequality for simple random variables *)
let SIMPLE_JENSEN = prove
 (`!p:A prob_space (X:A->real) (f:real->real).
     simple_rv p X /\ f real_convex_on (:real)
     ==> f(simple_expectation p X) <=
         simple_expectation p (\a. f(X a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V = IMAGE (X:A->real) (prob_carrier p)` THEN
  ABBREV_TAC `P = \v:real. prob (p:A prob_space) {x:A | x IN prob_carrier p /\ (X:A->real) x = v}` THEN
  (* Expand E[X] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (X:A->real) =
     sum V (\v:real. v * (P:real->real) v)`
    SUBST1_TAC THENL
  [EXPAND_TAC "V" THEN EXPAND_TAC "P" THEN
   REWRITE_TAC[simple_expectation; SET_IN_SIMP];
   ALL_TAC] THEN
  (* Expand E[f(X)] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\a:A. (f:real->real)((X:A->real) a)) =
     sum V (\v:real. f v * (P:real->real) v)`
    SUBST1_TAC THENL
  [EXPAND_TAC "V" THEN EXPAND_TAC "P" THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_COMPOSE_SUM THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* FINITE V *)
  SUBGOAL_THEN `FINITE (V:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "V" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  (* sum P = 1 *)
  SUBGOAL_THEN `sum V (P:real->real) = &1` ASSUME_TAC THENL
  [EXPAND_TAC "V" THEN EXPAND_TAC "P" THEN
   MATCH_MP_TAC SIMPLE_PROB_SUM_ONE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* P(v) >= 0 *)
  SUBGOAL_THEN `!v:real. v IN V ==> &0 <= (P:real->real) v` ASSUME_TAC THENL
  [EXPAND_TAC "P" THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC PROB_POSITIVE THEN
   MATCH_MP_TAC RANDOM_VARIABLE_LEVEL_SET THEN ASM_MESON_TAC[simple_rv];
   ALL_TAC] THEN
  (* Rewrite v * P v = P v * v, f v * P v = P v * f v *)
  SUBGOAL_THEN `sum (V:real->bool) (\v:real. v * (P:real->real) v) =
                sum V (\v. P v * v)` SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `sum (V:real->bool) (\v:real. (f:real->real) v * (P:real->real) v) =
                sum V (\v. P v * f v)` SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Apply REAL_CONVEX_ON_IMP_JENSEN *)
  MP_TAC(ISPECL [`f:real->real`; `(:real)`;
                  `V:real->bool`; `P:real->real`; `\v:real. v`]
    REAL_CONVEX_ON_IMP_JENSEN) THEN
  BETA_TAC THEN
  ASM_REWRITE_TAC[IN_UNIV; IS_REALINTERVAL_UNIV; ETA_AX]);;

(* E[f(X)*g(Y)] = E[f(X)]*E[g(Y)] for independent simple RVs *)
let SIMPLE_EXPECTATION_PRODUCT_COMPOSE_INDEP = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) (f:real->real) (g:real->real).
     simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
     ==> simple_expectation p (\x. f(X x) * g(Y x)) =
         simple_expectation p (\x. f(X x)) *
         simple_expectation p (\x. g(Y x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `RX = IMAGE (X:A->real) (prob_carrier p)` THEN
  ABBREV_TAC `RY = IMAGE (Y:A->real) (prob_carrier p)` THEN
  SUBGOAL_THEN `FINITE (RX:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "RX" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (RY:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "RY" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  (* Step 1: Pointwise f(X(x))*g(Y(x)) = double sum of f(u)*g(v)*1_{X=u,Y=v} *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x. (f:real->real)((X:A->real) x) * (g:real->real)((Y:A->real) x)) =
     simple_expectation p (\x. sum (RX:real->bool) (\u. sum (RY:real->bool)
       (\v. f(u) * g(v) * indicator_fn
         {z | z IN prob_carrier p /\ X z = u /\ Y z = v} x)))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   (* f(X(x)) = sum_u f(u)*1_{X=u} and g(Y(x)) = sum_v g(v)*1_{Y=v} *)
   SUBGOAL_THEN
     `(f:real->real)((X:A->real) x) =
      sum (RX:real->bool) (\u. f(u) * indicator_fn
        {z | z IN prob_carrier p /\ X z = u} x)`
     SUBST1_TAC THENL
   [EXPAND_TAC "RX" THEN MATCH_MP_TAC SIMPLE_RV_COMPOSE_SUM_INDICATOR THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `(g:real->real)((Y:A->real) x) =
      sum (RY:real->bool) (\v. g(v) * indicator_fn
        {z | z IN prob_carrier p /\ Y z = v} x)`
     SUBST1_TAC THENL
   [EXPAND_TAC "RY" THEN MATCH_MP_TAC SIMPLE_RV_COMPOSE_SUM_INDICATOR THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Product of sums = double sum via GSYM SUM_RMUL and SUM_LMUL *)
   ONCE_REWRITE_TAC[GSYM SUM_RMUL] THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN ONCE_REWRITE_TAC[GSYM SUM_LMUL] THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
   BETA_TAC THEN
   (* f(u)*1_{X=u} * (g(v)*1_{Y=v}) = f(u)*g(v)*1_{X=u,Y=v} *)
   SUBGOAL_THEN
     `{z:A | z IN prob_carrier p /\ (X:A->real) z = u /\ (Y:A->real) z = v} =
      {z | z IN prob_carrier p /\ X z = u} INTER
      {z | z IN prob_carrier p /\ Y z = v}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[INDICATOR_FN_INTER] THEN
   ABBREV_TAC `a = indicator_fn {z:A | z IN prob_carrier p /\ (X:A->real) z = u} (x:A)` THEN
   ABBREV_TAC `b = indicator_fn {z:A | z IN prob_carrier p /\ (Y:A->real) z = v} (x:A)` THEN
   CONV_TAC REAL_RING;
   ALL_TAC] THEN
  (* Step 2: Push E through double sum *)
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\(u:real) (x:A). sum (RY:real->bool) (\(v:real). (f:real->real)(u) * (g:real->real)(v) *
        indicator_fn {z:A | z IN prob_carrier (p:A prob_space) /\
          (X:A->real) z = u /\ (Y:A->real) z = v} x)`;
     `RX:real->bool`]
    SIMPLE_EXPECTATION_SUM_FINITE) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\(v:real) (x:A). (f:real->real)(u) * (g:real->real)(v) *
         indicator_fn {z:A | z IN prob_carrier (p:A prob_space) /\
           (X:A->real) z = u /\ (Y:A->real) z = v} x`;
      `RY:real->bool`]
     SIMPLE_RV_SUM_FINITE) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    MATCH_MP_TAC SIMPLE_RV_LEVEL_SET_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  (* Sum of expectations = double sum of f(u)*g(v)*P(X=u,Y=v) *)
  SUBGOAL_THEN
    `sum (RX:real->bool) (\u. simple_expectation (p:A prob_space) (\x. sum (RY:real->bool)
       (\v. (f:real->real) u * (g:real->real) v *
         indicator_fn {z | z IN prob_carrier p /\ (X:A->real) z = u /\
           (Y:A->real) z = v} x))) =
     sum RX (\u. sum RY (\v. f(u) * g(v) *
       prob p {z | z IN prob_carrier p /\ X z = u /\ Y z = v}))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN
   (* Push E through inner sum *)
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\(v:real) (x:A). (f:real->real)(u) * (g:real->real)(v) *
         indicator_fn {z:A | z IN prob_carrier (p:A prob_space) /\
           (X:A->real) z = u /\ (Y:A->real) z = v} x`;
      `RY:real->bool`]
     SIMPLE_EXPECTATION_SUM_FINITE) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    MATCH_MP_TAC SIMPLE_RV_LEVEL_SET_INTER_IN_EVENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real` THEN DISCH_TAC THEN
   BETA_TAC THEN
   (* E[f(u)*g(v)*1_A] = f(u)*g(v)*P(A) via CMUL + INDICATOR *)
   SUBGOAL_THEN
     `{z:A | z IN prob_carrier p /\ (X:A->real) z = u /\
       (Y:A->real) z = v} IN prob_events p`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_LEVEL_SET_INTER_IN_EVENTS THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `indicator_fn {z:A | z IN prob_carrier (p:A prob_space) /\
        (X:A->real) z = u /\ (Y:A->real) z = v}`;
      `(f:real->real) u * (g:real->real) v`]
     SIMPLE_EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Apply independence: P(X=u,Y=v) = P(X=u)*P(Y=v) *)
  SUBGOAL_THEN
    `sum (RX:real->bool) (\u. sum (RY:real->bool) (\v.
       (f:real->real)(u) * (g:real->real)(v) *
       prob (p:A prob_space)
         {z | z IN prob_carrier p /\ (X:A->real) z = u /\ (Y:A->real) z = v})) =
     sum RX (\u. sum RY (\v.
       f(u) * g(v) *
       (prob p {z | z IN prob_carrier p /\ X z = u} *
        prob p {z | z IN prob_carrier p /\ Y z = v})))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real` THEN
   DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC INDEP_RV_POINT_MASS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 4: Factor the double sum *)
  (* f(u)*g(v)*P(X=u)*P(Y=v) = (f(u)*P(X=u))*(g(v)*P(Y=v)) *)
  SUBGOAL_THEN
    `!u:real. sum (RY:real->bool) (\v:real.
       (f:real->real)(u) * (g:real->real)(v) *
       (prob (p:A prob_space) {z | z IN prob_carrier p /\ (X:A->real) z = u} *
        prob p {z | z IN prob_carrier p /\ (Y:A->real) z = v})) =
     (f(u) * prob p {z | z IN prob_carrier p /\ X z = u}) *
     sum RY (\v. g(v) * prob p {z | z IN prob_carrier p /\ Y z = v})`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `(\v:real. (f:real->real)(u) * (g:real->real)(v) *
        (prob (p:A prob_space) {z | z IN prob_carrier p /\ (X:A->real) z = u} *
         prob p {z | z IN prob_carrier p /\ (Y:A->real) z = v})) =
      (\v. (f(u) * prob p {z | z IN prob_carrier p /\ X z = u}) *
           (g(v) * prob p {z | z IN prob_carrier p /\ Y z = v}))`
     SUBST1_TAC THENL
   [ABS_TAC THEN
    ABBREV_TAC `a = (f:real->real) u` THEN
    ABBREV_TAC `b = (g:real->real) v` THEN
    ABBREV_TAC `c = prob (p:A prob_space)
      {z | z IN prob_carrier p /\ (X:A->real) z = u}` THEN
    ABBREV_TAC `d = prob (p:A prob_space)
      {z | z IN prob_carrier p /\ (Y:A->real) z = v}` THEN
    CONV_TAC REAL_RING;
    REWRITE_TAC[SUM_LMUL]];
   REWRITE_TAC[SUM_RMUL]] THEN
  (* Step 5: Recognize as E[f(X)]*E[g(Y)] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x:A. (f:real->real)((X:A->real) x)) =
     sum (RX:real->bool) (\u. f(u) * prob p {x | x IN prob_carrier p /\ X x = u})`
    (fun th -> REWRITE_TAC[th]) THENL
  [EXPAND_TAC "RX" THEN MATCH_MP_TAC SIMPLE_EXPECTATION_COMPOSE_SUM THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x:A. (g:real->real)((Y:A->real) x)) =
     sum (RY:real->bool) (\u. g(u) * prob p {x | x IN prob_carrier p /\ Y x = u})`
    (fun th -> REWRITE_TAC[th]) THEN
  EXPAND_TAC "RY" THEN MATCH_MP_TAC SIMPLE_EXPECTATION_COMPOSE_SUM THEN
  ASM_REWRITE_TAC[]);;

(* Characteristic function of sum of independent RVs - real part *)
(* phi_{X+Y}(t) = phi_X(t) * phi_Y(t) for real part (with imaginary cross term) *)
let CHAR_FN_ADD_INDEP_RE = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) t.
     simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
     ==> char_fn_re p (\x. X x + Y x) t =
         char_fn_re p X t * char_fn_re p Y t -
         char_fn_im p X t * char_fn_im p Y t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[char_fn_re; char_fn_im] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  (* Establish simple_rv for trig compositions using ISPECL *)
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. cos(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. cos(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. cos(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `\y:real. cos(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sin(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. sin(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sin(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `\y:real. sin(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_rv (p:A prob_space)
       (\x:A. cos(t * (X:A->real) x) * cos(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_rv (p:A prob_space)
       (\x:A. sin(t * (X:A->real) x) * sin(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 1: cos(t*(X+Y)) = cos(tX)*cos(tY) - sin(tX)*sin(tY) *)
  SUBGOAL_THEN
    `!x:A. cos(t * ((X:A->real) x + (Y:A->real) x)) =
           cos(t * X x) * cos(t * Y x) - sin(t * X x) * sin(t * Y x)`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB; COS_ADD]; ALL_TAC] THEN
  (* Step 2: E[f-g] = E[f] - E[g] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. cos(t * (X:A->real) x) * cos(t * (Y:A->real) x) -
              sin(t * X x) * sin(t * Y x)) =
     simple_expectation p (\x. cos(t * X x) * cos(t * Y x)) -
     simple_expectation p (\x. sin(t * X x) * sin(t * Y x))`
    (fun th -> REWRITE_TAC[th]) THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. cos(t * (X:A->real) x) * cos(t * (Y:A->real) x)`;
     `\x:A. sin(t * (X:A->real) x) * sin(t * (Y:A->real) x)`]
     SIMPLE_EXPECTATION_SUB) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: E[cos(tX)*cos(tY)] = E[cos(tX)]*E[cos(tY)] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. cos(t * (X:A->real) x) * cos(t * (Y:A->real) x)) =
     simple_expectation p (\x. cos(t * X x)) *
     simple_expectation p (\x. cos(t * Y x))`
    (fun th -> REWRITE_TAC[th]) THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`;
     `\u:real. cos(t * u)`; `\v:real. cos(t * v)`]
     SIMPLE_EXPECTATION_PRODUCT_COMPOSE_INDEP) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 4: E[sin(tX)*sin(tY)] = E[sin(tX)]*E[sin(tY)] *)
  (* Note: (fun th -> REWRITE_TAC[th]) closes the main goal by reflexivity *)
  (* so SUBGOAL_THEN produces only 1 goal - use THEN not THENL *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. sin(t * (X:A->real) x) * sin(t * (Y:A->real) x)) =
     simple_expectation p (\x. sin(t * X x)) *
     simple_expectation p (\x. sin(t * Y x))`
    (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`;
     `\u:real. sin(t * u)`; `\v:real. sin(t * v)`]
     SIMPLE_EXPECTATION_PRODUCT_COMPOSE_INDEP) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let CHAR_FN_ADD_INDEP_IM = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) t.
     simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
     ==> char_fn_im p (\x. X x + Y x) t =
         char_fn_re p X t * char_fn_im p Y t +
         char_fn_im p X t * char_fn_re p Y t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[char_fn_re; char_fn_im] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  (* Establish simple_rv for trig compositions using ISPECL *)
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. cos(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. cos(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. cos(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `\y:real. cos(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sin(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. sin(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sin(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `\y:real. sin(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_rv (p:A prob_space)
       (\x:A. sin(t * (X:A->real) x) * cos(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_rv (p:A prob_space)
       (\x:A. cos(t * (X:A->real) x) * sin(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 1: sin(t*(X+Y)) = sin(tX)*cos(tY) + cos(tX)*sin(tY) *)
  SUBGOAL_THEN
    `!x:A. sin(t * ((X:A->real) x + (Y:A->real) x)) =
           sin(t * X x) * cos(t * Y x) + cos(t * X x) * sin(t * Y x)`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[REAL_ADD_LDISTRIB; SIN_ADD]; ALL_TAC] THEN
  (* Step 2: E[f+g] = E[f] + E[g] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. sin(t * (X:A->real) x) * cos(t * (Y:A->real) x) +
              cos(t * X x) * sin(t * Y x)) =
     simple_expectation p (\x. sin(t * X x) * cos(t * Y x)) +
     simple_expectation p (\x. cos(t * X x) * sin(t * Y x))`
    (fun th -> REWRITE_TAC[th]) THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. sin(t * (X:A->real) x) * cos(t * (Y:A->real) x)`;
     `\x:A. cos(t * (X:A->real) x) * sin(t * (Y:A->real) x)`]
     SIMPLE_EXPECTATION_ADD) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: E[sin(tX)*cos(tY)] = E[sin(tX)]*E[cos(tY)] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. sin(t * (X:A->real) x) * cos(t * (Y:A->real) x)) =
     simple_expectation p (\x. sin(t * X x)) *
     simple_expectation p (\x. cos(t * Y x))`
    (fun th -> REWRITE_TAC[th]) THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`;
     `\u:real. sin(t * u)`; `\v:real. cos(t * v)`]
     SIMPLE_EXPECTATION_PRODUCT_COMPOSE_INDEP) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 4: E[cos(tX)*sin(tY)] = E[cos(tX)]*E[sin(tY)] *)
  (* After rewrite, goal becomes a+b = b+a, need REAL_ARITH_TAC *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. cos(t * (X:A->real) x) * sin(t * (Y:A->real) x)) =
     simple_expectation p (\x. cos(t * X x)) *
     simple_expectation p (\x. sin(t * Y x))`
    (fun th -> REWRITE_TAC[th]) THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`;
     `\u:real. cos(t * u)`; `\v:real. sin(t * v)`]
     SIMPLE_EXPECTATION_PRODUCT_COMPOSE_INDEP) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   REAL_ARITH_TAC]);;

(* E[X]^2 <= E[X^2] -- consequence of Var(X) >= 0 *)
let SIMPLE_EXPECTATION_SQ_LE = prove
 (`!p:A prob_space (X:A->real).
     simple_rv p X
     ==> simple_expectation p X pow 2 <=
         simple_expectation p (\x. X x pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`] SIMPLE_VARIANCE_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`] SIMPLE_VARIANCE_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* |phi(t)|^2 <= 1: characteristic function modulus bound *)
(* Uses E[cos(tX)]^2 + E[sin(tX)]^2 <= E[cos^2(tX)] + E[sin^2(tX)] = E[1] = 1 *)
let CHAR_FN_MODULUS_LE = prove
 (`!p:A prob_space (X:A->real) t.
     simple_rv p X
     ==> char_fn_re p X t pow 2 + char_fn_im p X t pow 2 <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[char_fn_re; char_fn_im] THEN
  (* Establish simple_rv for cos and sin compositions *)
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. cos(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. cos(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sin(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. sin(t * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  (* Use E[f]^2 <= E[f^2] for both cos and sin *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `simple_expectation (p:A prob_space) (\x:A. cos(t * (X:A->real) x) pow 2) +
     simple_expectation p (\x. sin(t * X x) pow 2)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. cos(t * (X:A->real) x)`] SIMPLE_EXPECTATION_SQ_LE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. sin(t * (X:A->real) x)`] SIMPLE_EXPECTATION_SQ_LE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* E[cos^2] + E[sin^2] = E[cos^2 + sin^2] = E[1] = 1 *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x:A. cos(t * (X:A->real) x) pow 2) +
     simple_expectation p (\x. sin(t * X x) pow 2) =
     simple_expectation p (\x:A. &1)`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `simple_rv (p:A prob_space) (\x:A. cos(t * (X:A->real) x) pow 2)`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
       `\y:real. cos(t * y) pow 2`] SIMPLE_RV_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `simple_rv (p:A prob_space) (\x:A. sin(t * (X:A->real) x) pow 2)`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
       `\y:real. sin(t * y) pow 2`] SIMPLE_RV_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
      `\x:A. cos(t * (X:A->real) x) pow 2`;
      `\x:A. sin(t * (X:A->real) x) pow 2`]
      SIMPLE_EXPECTATION_ADD) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN(SUBST1_TAC o GSYM) THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
   MP_TAC(SPEC `t * (X:A->real) y` SIN_CIRCLE) THEN REAL_ARITH_TAC;
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST] THEN REAL_ARITH_TAC]);;

(* Algebraic identity: |(a+ib)(c+id)|^2 = |a+ib|^2 * |c+id|^2 *)
let COMPLEX_PRODUCT_MODULUS_SQ = prove
 (`!r1:real s1:real r2:real s2:real.
     (r1 * r2 - s1 * s2) pow 2 + (r1 * s2 + s1 * r2) pow 2 =
     (r1 pow 2 + s1 pow 2) * (r2 pow 2 + s2 pow 2)`,
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

(* N-fold char fn modulus factorization for i.i.d. simple RVs *)
let CHAR_FN_SUM_IID_MODULUS = prove
 (`!p:A prob_space (X:num->A->real) n t.
     (!i. i <= n ==> simple_rv p (X i)) /\
     (!i. i <= n ==>
        char_fn_re p (X i) t = char_fn_re p (X 0) t /\
        char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> char_fn_re p (\x. sum(0..n) (\i. X i x)) t pow 2 +
         char_fn_im p (\x. sum(0..n) (\i. X i x)) t pow 2 =
         (char_fn_re p (X 0) t pow 2 +
          char_fn_im p (X 0) t pow 2) pow (SUC n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case: n = 0, sum(0..0) = X 0 *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..0) (\i. (X:num->A->real) i x)) = X 0`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_SING_NUMSEG] THEN GEN_TAC THEN BETA_TAC THEN
    REFL_TAC;
    REWRITE_TAC[real_pow; REAL_MUL_RID]];
   (* Inductive step: n -> SUC n *)
   REPEAT STRIP_TAC THEN
   (* Step 1: Rewrite sum(0..SUC n) as sum(0..n) + X(SUC n) *)
   SUBGOAL_THEN
     `!x:A. sum(0..SUC n) (\i. (X:num->A->real) i x) =
            sum(0..n) (\i. X i x) + X (SUC n) x`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   (* Step 2: Establish simple_rv and indep_rv *)
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN
    ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) ((X:num->A->real) (SUC n))`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
   SUBGOAL_THEN `indep_rv (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) (X (SUC n))`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `n < SUC n`]; ALL_TAC] THEN
   (* Step 3: Get RE and IM char fn factorizations *)
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
     `(X:num->A->real) (SUC n)`; `t:real`]
     CHAR_FN_ADD_INDEP_RE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
     `(X:num->A->real) (SUC n)`; `t:real`]
     CHAR_FN_ADD_INDEP_IM) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_TAC THEN
   (* Step 4: Rewrite goal and apply modulus identity *)
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[COMPLEX_PRODUCT_MODULUS_SQ] THEN
   (* Step 5: Replace X(SUC n) char fns with X(0) *)
   SUBGOAL_THEN
     `char_fn_re (p:A prob_space) ((X:num->A->real) (SUC n)) t =
      char_fn_re p (X 0) t /\
      char_fn_im p (X (SUC n)) t = char_fn_im p (X 0) t`
     STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   (* Step 6: Apply IH for partial sum modulus *)
   SUBGOAL_THEN
     `char_fn_re (p:A prob_space)
        (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t pow 2 +
      char_fn_im p (\x. sum(0..n) (\i. X i x)) t pow 2 =
      (char_fn_re p (X 0) t pow 2 +
       char_fn_im p (X 0) t pow 2) pow (SUC n)`
     SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
    [ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`];
     ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`];
     ASM_MESON_TAC[ARITH_RULE `k < n ==> k < SUC n`]];
    ALL_TAC] THEN
   (* Step 7: Final algebra: a^(n+1) * a = a^(n+2) *)
   REWRITE_TAC[real_pow] THEN CONV_TAC REAL_RING]);;

(* Taylor approximation bound for cos: |cos(x) - (1 - x^2/2)| <= x^4/6 *)
let COS_APPROX_BOUND = prove
 (`!x:real. abs(cos(x) - (&1 - x pow 2 / &2)) <= x pow 4 / &6`,
  GEN_TAC THEN MP_TAC(ISPECL [`1`; `Cx x`] TAYLOR_CCOS) THEN
  REWRITE_TAC[num_CONV `1`; VSUM_CLAUSES_NUMSEG; LE_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM CX_COS; complex_pow; COMPLEX_POW_1; COMPLEX_MUL_RID;
              COMPLEX_MUL_LID; COMPLEX_DIV_1] THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_NEG; GSYM CX_POW; GSYM CX_ADD;
              GSYM CX_SUB; GSYM CX_DIV; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[IM_CX; REAL_ABS_0; REAL_EXP_0; REAL_MUL_LID] THEN
  SIMP_TAC[REAL_EVENPOW_ABS; ARITH] THEN REAL_ARITH_TAC);;

(* Characteristic function real part approximation by second moment *)
let CHAR_FN_RE_APPROX = prove
 (`!p:A prob_space (X:A->real) t.
    simple_rv p X
    ==> abs(char_fn_re p X t -
            (&1 - t pow 2 * simple_expectation p (\x. X x pow 2) / &2))
        <= t pow 4 * simple_expectation p (\x. X x pow 4) / &6`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[char_fn_re] THEN
  (* Establish simple_rv for composed functions *)
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. cos(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
     `\y:real. cos(t * y)`] SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (X:A->real) x pow 2)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
     `\y:real. y pow 2`] SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. (X:A->real) x pow 4)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
     `\y:real. y pow 4`] SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_rv (p:A prob_space)
      (\x:A. &1 - t pow 2 * (X:A->real) x pow 2 / &2)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
     `\y:real. &1 - t pow 2 * y pow 2 / &2`] SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  (* Step 1: Linearity - replace 1-t^2*E[X^2]/2 with E[1-t^2*X^2/2] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. &1 - t pow 2 * (X:A->real) x pow 2 / &2) =
     &1 - t pow 2 * simple_expectation p (\x. X x pow 2) / &2`
    (fun th -> REWRITE_TAC[GSYM th]) THENL
  [(* Prove E[1-t^2*X^2/2] = 1-t^2*E[X^2]/2 *)
   (* First normalize: t^2*y^2/2 = (t^2/2)*y^2 *)
   SUBGOAL_THEN
     `simple_expectation (p:A prob_space)
        (\x:A. &1 - t pow 2 * (X:A->real) x pow 2 / &2) =
      simple_expectation p (\x. &1 - (t pow 2 / &2) * X x pow 2)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   (* Split via SUB: E[1 - c*X^2] = E[1] - E[c*X^2] *)
   MP_TAC(ISPECL [`p:A prob_space`; `\x:A. &1`;
                   `\x:A. (t pow 2 / &2) * (X:A->real) x pow 2`]
                  SIMPLE_EXPECTATION_SUB) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [REWRITE_TAC[SIMPLE_RV_CONST] THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST] THEN
   (* E[c*X^2] = c*E[X^2] *)
   MP_TAC(ISPECL [`p:A prob_space`; `\x:A. (X:A->real) x pow 2`;
                   `t pow 2 / &2`] SIMPLE_EXPECTATION_CMUL) THEN
   BETA_TAC THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Now goal has E[1-t^2*X^2/2] instead of 1-t^2*E[X^2]/2 *)
  (* Use SIMPLE_EXPECTATION_SUB: E[f] - E[g] = E[f-g] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x:A. cos(t * (X:A->real) x)) -
     simple_expectation p (\x. &1 - t pow 2 * X x pow 2 / &2) =
     simple_expectation p
       (\x. cos(t * X x) - (&1 - t pow 2 * X x pow 2 / &2))`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: Triangle inequality |E[f]| <= E[|f|] *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x. abs(cos(t * (X:A->real) x) -
             (&1 - t pow 2 * X x pow 2 / &2)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_ABS_LE THEN
   MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Monotonicity E[|f|] <= E[t^4*X^4/6] via COS_APPROX_BOUND *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x:A. t pow 4 * (X:A->real) x pow 4 / &6)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ABS THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
      `\y:real. t pow 4 * y pow 4 / &6`] SIMPLE_RV_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
   X_GEN_TAC `a:A` THEN DISCH_TAC THEN
   MP_TAC(SPEC `t * (X:A->real) a` COS_APPROX_BOUND) THEN
   REWRITE_TAC[real_div; REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
   DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  (* Step 4: E[t^4*X^4/6] = t^4*E[X^4]/6 *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. t pow 4 * (X:A->real) x pow 4 / &6) =
     t pow 4 * simple_expectation p (\x. X x pow 4) / &6`
    (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
  (* Normalize t^4*y^4/6 = (t^4/6)*y^4, then use CMUL *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
       (\x:A. t pow 4 * (X:A->real) x pow 4 / &6) =
     simple_expectation p (\x. (t pow 4 / &6) * X x pow 4)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x:A. (X:A->real) x pow 4`;
                  `t pow 4 / &6`] SIMPLE_EXPECTATION_CMUL) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* Lower bound for log: log(x) >= 1 - 1/x for x > 0 *)
(* Derived from LOG_LE_STRONG: log(1+x) <= x, applied to inv(x)-1 *)
let LOG_LOWER_BOUND = prove
 (`!x. &0 < x ==> &1 - inv(x) <= log(x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `log(inv(x:real)) <= inv(x) - &1` ASSUME_TAC THENL
  [MP_TAC(SPEC `inv(x:real) - &1` LOG_LE_STRONG) THEN
   REWRITE_TAC[REAL_ARITH `&1 + (y - &1) = y`] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_SIMP_TAC[REAL_LT_INV_EQ];
   ALL_TAC] THEN
  SUBGOAL_THEN `log(inv(x:real)) = --log(x)` SUBST_ALL_TAC THENL
  [MATCH_MP_TAC LOG_INV THEN ASM_REWRITE_TAC[];
   ASM_REAL_ARITH_TAC]);;

(* Upper bound: (1-c/(n+1))^(n+1) <= exp(-c) for 0<=c<n+1 *)
(* From 1-x <= exp(-x) applied pointwise, then REAL_POW_LE2 *)
let POW_LE_EXP_NEG = prove
 (`!c n. &0 <= c /\ c < &(SUC n)
         ==> (&1 - c / &(SUC n)) pow (SUC n) <= exp(--c)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(c / &(SUC n))) pow (SUC n)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LE] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_0] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `--(c / &(SUC n))` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
   REWRITE_TAC[GSYM REAL_EXP_N] THEN
   SUBGOAL_THEN `&(SUC n) * --(c / &(SUC n)) = --c`
     (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; NOT_SUC]; CONV_TAC REAL_FIELD]]);;

(* Lower bound: exp(-c*(n+1)/(n+1-c)) <= (1-c/(n+1))^(n+1) *)
(* From LOG_LOWER_BOUND: log(x) >= 1-1/x, applied to 1-c/(n+1) *)
let EXP_NEG_LE_POW = prove
 (`!c n. &0 <= c /\ c < &(SUC n)
         ==> exp(--(c * &(SUC n) / (&(SUC n) - c)))
             <= (&1 - c / &(SUC n)) pow (SUC n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(SUC n)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT; LT_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - c / &(SUC n)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(SUC n) - c` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Rewrite pow as exp(log(pow)) *)
  SUBGOAL_THEN
    `(&1 - c / &(SUC n)) pow (SUC n) =
     exp(&(SUC n) * log(&1 - c / &(SUC n)))`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[REAL_EXP_N] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC EXP_LOG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  (* Key step: log(1-c/(n+1)) >= -c/((n+1)-c) from LOG_LOWER_BOUND *)
  SUBGOAL_THEN
    `--(c / (&(SUC n) - c)) <= log(&1 - c / &(SUC n))`
    ASSUME_TAC THENL
  [MP_TAC(SPEC `&1 - c / &(SUC n)` LOG_LOWER_BOUND) THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= l ==> a <= l`) THEN
   SUBGOAL_THEN `~(&(SUC n) = &0) /\ ~(&(SUC n) - c = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_EQ; NOT_SUC] THEN ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_FIELD];
   ALL_TAC] THEN
  (* Multiply by &(SUC n) >= 0 *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(SUC n) * --(c / (&(SUC n) - c))` THEN CONJ_TAC THENL
  [SUBGOAL_THEN `~(&(SUC n) = &0) /\ ~(&(SUC n) - c = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_EQ; NOT_SUC] THEN ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_FIELD];
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_POS]; ASM_REWRITE_TAC[]]]);;

(* Helper: 1 - exp(-y) <= y for all y *)
let ONE_MINUS_EXP_NEG_LE = prove
 (`!y. &1 - exp(--y) <= y`,
  GEN_TAC THEN MP_TAC(SPEC `--(y:real)` REAL_EXP_LE_X) THEN REAL_ARITH_TAC);;

(* Helper: exp(-a) - exp(-(a+y)) <= exp(-a) * y *)
let EXP_DIFF_LE = prove
 (`!a y. exp(--a) - exp(--(a + y)) <= exp(--a) * y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_NEG_ADD; REAL_EXP_ADD] THEN
  SUBGOAL_THEN `exp(--a) - exp(--a) * exp(--y) =
                exp(--a) * (&1 - exp(--y))` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_EXP_POS_LE; ONE_MINUS_EXP_NEG_LE]);;

(* Difference bound: exp(-c) - (1-c/(n+1))^(n+1) <= exp(-c)*c^2/(n+1-c) *)
let POW_EXP_NEG_DIFF = prove
 (`!c n. &0 < c /\ c < &(SUC n)
         ==> exp(--c) - (&1 - c / &(SUC n)) pow (SUC n)
             <= exp(--c) * c pow 2 / (&(SUC n) - c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(SUC n) - c` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--c) - exp(--(c * &(SUC n) / (&(SUC n) - c)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `a <= b ==> c - b <= c - a`) THEN
   MATCH_MP_TAC EXP_NEG_LE_POW THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `c * &(SUC n) / (&(SUC n) - c) = c + c pow 2 / (&(SUC n) - c)`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `~(&(SUC n) - c = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
   ALL_TAC] THEN
  MATCH_ACCEPT_TAC(SPECL [`c:real`; `c pow 2 / (&(SUC n) - c)`] EXP_DIFF_LE));;

(* Exponential limit: (1-c/(n+1))^(n+1) --> exp(-c) as n-->inf *)
(* Key ingredient for CLT: uses POW_LE_EXP_NEG and EXP_NEG_LE_POW *)
let REALLIM_POW_EXP_NEG = prove
 (`!c. &0 < c ==>
   ((\n. (&1 - c / &(SUC n)) pow (SUC n)) ---> exp(--c)) sequentially`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `&2 * c`
    (MATCH_MP REAL_ARCH (REAL_ARITH `&0 < &1`))) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_THEN(X_CHOOSE_TAC `K:num`) THEN
  MP_TAC(SPEC `&2 * exp(--c) * c pow 2 / e`
    (MATCH_MP REAL_ARCH (REAL_ARITH `&0 < &1`))) THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  EXISTS_TAC `M + K:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `c < &(SUC n)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&K` THEN
   CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&2 * c < &(SUC n)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&K` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(SUC n) - c` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - c / &(SUC n)) pow (SUC n) <= exp(--c)` ASSUME_TAC THENL
  [MATCH_MP_TAC POW_LE_EXP_NEG THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((&1 - c / &(SUC n)) pow (SUC n) - exp(--c)) =
                exp(--c) - (&1 - c / &(SUC n)) pow (SUC n)` SUBST1_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `exp(--c) * c pow 2 / (&(SUC n) - c)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC POW_EXP_NEG_DIFF THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Need: exp(-c) * c^2 / (SUC n - c) < e *)
  (* Normalize: a * (b/c) = (a*b)/c so REAL_LT_LDIV_EQ applies *)
  SUBGOAL_THEN `exp(--c) * c pow 2 / (&(SUC n) - c) =
                (exp(--c) * c pow 2) / (&(SUC n) - c)` SUBST1_TAC THENL
  [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  (* Goal: exp(-c) * c^2 < e * (SUC n - c) *)
  (* Multiply both sides by 2: suffices to show *)
  (* &2 * (exp(-c)*c^2) < &2 * (e*(SUC n - c)) *)
  ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_LMUL_EQ
    (REAL_ARITH `&0 < &2`))] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `e * &(SUC n)` THEN CONJ_TAC THENL
  [(* &2 * (exp(-c) * c^2) < e * SUC n *)
   SUBGOAL_THEN `&2 * exp(--c) * c pow 2 / e < &(SUC n)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&M` THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `(&2 * exp(--c) * c pow 2 / e) * e < &(SUC n) * e`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(&2 * exp(--c) * c pow 2 / e) * e =
                 &2 * (exp(--c) * c pow 2)` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `~(e = &0)` MP_TAC THENL
    [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
   SUBGOAL_THEN `&(SUC n) * e = e * &(SUC n)` SUBST_ALL_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   (* e * SUC n <= &2 * (e * (SUC n - c)) *)
   SUBGOAL_THEN `&2 * (e * (&(SUC n) - c)) = e * (&2 * (&(SUC n) - c))`
     SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

(* Power difference bound for sequences in [-1,1] *)
let POW_DIFF_BOUND_UNIT = prove
 (`!n x y. abs(x) <= &1 /\ abs(y) <= &1
           ==> abs(x pow n - y pow n) <= &n * abs(x - y)`,
  INDUCT_TAC THENL
  [REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[real_pow] THEN
  SUBGOAL_THEN `abs(x pow n - y pow n) <= &n * abs(x - y)` ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(y pow n) <= &1` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ABS_POW] THEN
   MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS];
   ALL_TAC] THEN
  (* Goal: abs(x * x pow n - y * y pow n) <= &(SUC n) * abs(x - y) *)
  (* Rewrite x*a - y*b as x*(a-b) + (x-y)*b via triangle inequality *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(x * (x pow n - y pow n)) +
              abs((x - y) * y pow n)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH
    `a - b = c + d ==> abs(a - b) <= abs c + abs d`) THEN
   CONV_TAC REAL_RING;
   ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  (* Goal: abs(x)*abs(x^n-y^n) + abs(x-y)*abs(y^n) <= (n+1)*abs(x-y) *)
  SUBGOAL_THEN `abs(x) * abs(x pow n - y pow n) <= &n * abs(x - y)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs(x) * (&n * abs(x - y))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&1 * (&n * abs(x - y))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_ABS_POS];
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `abs(x - y) * abs(y pow n) <= abs(x - y)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs(x - y) * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n * abs(x - y) + abs(x - y)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC]);;

(* Perturbed exponential limit: (1 - (c+h(n))/(n+1))^(n+1) -> exp(-c) *)
(* when h -> 0. Key ingredient for CLT where c = t^2*sigma^2/2 + error. *)
let REALLIM_POW_EXP_NEG_PERTURB = prove
 (`!c h. &0 < c /\ ((h:num->real) ---> &0) sequentially
         ==> ((\n. (&1 - (c + h n) / &(SUC n)) pow (SUC n)) ---> exp(--c))
             sequentially`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (* Get N1 from REALLIM_POW_EXP_NEG *)
  SUBGOAL_THEN
    `((\n. (&1 - c / &(SUC n)) pow (SUC n)) ---> exp(--c)) sequentially`
    MP_TAC THENL
  [MATCH_MP_TAC REALLIM_POW_EXP_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (ASSUME_TAC o BETA_RULE)) THEN
  (* Get N2 from h -> 0: |h(n)| < e/2 *)
  SUBGOAL_THEN
    `?N2:num. !n. N2 <= n ==> abs((h:num->real) n - &0) < e / &2`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `((h:num->real) ---> &0) sequentially` THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MESON_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?N3:num. !n. N3 <= n ==> abs((h:num->real) n - &0) < c`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `((h:num->real) ---> &0) sequentially` THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `?N4:num. &2 * c < &N4` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_ARCH_LT]; ALL_TAC] THEN
  (* Remove (h ---> &0) assumption to avoid ASM_REAL_ARITH_TAC failure *)
  UNDISCH_TAC `((h:num->real) ---> &0) sequentially` THEN
  DISCH_THEN(K ALL_TAC) THEN
  EXISTS_TAC `N1 + N2 + N3 + N4:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* Establish key bounds for this n *)
  SUBGOAL_THEN `abs((h:num->real) n) < e / &2` ASSUME_TAC THENL
  [SUBGOAL_THEN `abs((h:num->real) n - &0) < e / &2` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `abs((h:num->real) n) < c` ASSUME_TAC THENL
  [SUBGOAL_THEN `abs((h:num->real) n - &0) < c` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&2 * c < &(SUC n)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&N4` THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(SUC n)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  (* Bound 1: |perturbed_pow - unperturbed_pow| < e/2 *)
  SUBGOAL_THEN
    `abs((&1 - (c + (h:num->real) n) / &(SUC n)) pow (SUC n) -
         (&1 - c / &(SUC n)) pow (SUC n)) < e / &2`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `abs((h:num->real) n)` THEN
   CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
   (* Goal: abs(perturbed^(SUC n) - unperturbed^(SUC n)) <= abs(h n) *)
   SUBGOAL_THEN `abs(&1 - (c + (h:num->real) n) / &(SUC n)) <= &1`
     ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> -- &1 <= &1 - x`) THEN
     ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 - x <= &1`) THEN
     MATCH_MP_TAC REAL_LE_DIV THEN
     REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN `abs(&1 - c / &(SUC n)) <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> -- &1 <= &1 - x`) THEN
     ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 - x <= &1`) THEN
     MATCH_MP_TAC REAL_LE_DIV THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS]];
    ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(SUC n) * abs((&1 - (c + (h:num->real) n) / &(SUC n)) -
               (&1 - c / &(SUC n)))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC POW_DIFF_BOUND_UNIT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 - (c + (h:num->real) n) / &(SUC n)) -
                 (&1 - c / &(SUC n)) = --(h n / &(SUC n))`
     SUBST1_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_DIV; REAL_ABS_NUM] THEN
   SUBGOAL_THEN `&(SUC n) * abs((h:num->real) n) / &(SUC n) = abs(h n)`
     SUBST1_TAC THENL
   [ASM_MESON_TAC[REAL_DIV_LMUL]; REWRITE_TAC[REAL_LE_REFL]];
   ALL_TAC] THEN
  (* Bound 2: |unperturbed_pow - exp(-c)| < e/2 *)
  SUBGOAL_THEN
    `abs((&1 - c / &(SUC n)) pow (SUC n) - exp(--c)) < e / &2`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  (* Combine via triangle inequality *)
  ASM_REAL_ARITH_TAC);;

(* Key lemma for CLT: char_fn_re power converges to exponential *)
let CHAR_FN_RE_POW_CONV_EXP = prove
 (`!p:A prob_space (X:A->real) t.
    simple_rv p X /\
    simple_expectation p X = &0 /\
    &0 < simple_expectation p (\x. X x pow 2)
    ==> ((\n. char_fn_re p X (t / sqrt(&(SUC n))) pow (SUC n))
         ---> exp(--(t pow 2 * simple_expectation p (\x. X x pow 2) / &2)))
        sequentially`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `sigma_sq = simple_expectation (p:A prob_space)
    (\x. (X:A->real) x pow 2)` THEN
  ABBREV_TAC `m4 = simple_expectation (p:A prob_space)
    (\x. (X:A->real) x pow 4)` THEN
  (* Case t = 0: trivial *)
  ASM_CASES_TAC `t = &0` THENL
  [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_INV_0;
                    CHAR_FN_ZERO; REAL_POW_ONE;
                    REAL_POW_2; REAL_MUL_RZERO;
                    REAL_NEG_0; REAL_EXP_0; REALLIM_CONST];
   ALL_TAC] THEN
  (* t <> 0: setup *)
  ABBREV_TAC `c = t pow 2 * sigma_sq / &2` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
  [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_MUL THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_POW_2];
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  ABBREV_TAC `h = \n:num. &(SUC n) *
    (&1 - char_fn_re (p:A prob_space) (X:A->real) (t / sqrt(&(SUC n)))) - c` THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. (&1 - (c + (h:num->real) n) / &(SUC n)) pow (SUC n)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   EXPAND_TAC "h" THEN BETA_TAC THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `~(&(SUC n) = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_POW_EXP_NEG_PERTURB THEN
  ASM_REWRITE_TAC[] THEN
  (* Show h --> &0 via comparison *)
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n:num. t pow 4 * m4 / &6 * inv(&n + &1)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
   EXPAND_TAC "h" THEN BETA_TAC THEN
   SUBGOAL_THEN `~(&(SUC n) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < &(SUC n)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `(t / sqrt(&(SUC n))) pow 2 * sigma_sq / &2 = c / &(SUC n)`
     ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_POW_DIV] THEN
    SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
    UNDISCH_TAC `~(&(SUC n) = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
     `t / sqrt(&(SUC n))`] CHAR_FN_RE_APPROX) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `&(SUC n) * (&1 - char_fn_re (p:A prob_space) (X:A->real)
       (t / sqrt(&(SUC n)))) - c =
      --(&(SUC n) * (char_fn_re p X (t / sqrt(&(SUC n))) -
        (&1 - (t / sqrt(&(SUC n))) pow 2 * sigma_sq / &2)))`
     SUBST1_TAC THENL
   [UNDISCH_TAC `(t / sqrt (&(SUC n))) pow 2 * sigma_sq / &2 = c / &(SUC n)` THEN
    UNDISCH_TAC `~(&(SUC n) = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_NUM] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(SUC n) * ((t / sqrt(&(SUC n))) pow 4 *
     simple_expectation (p:A prob_space) (\x. (X:A->real) x pow 4) / &6)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_POS]; EXPAND_TAC "m4" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   EXPAND_TAC "m4" THEN
   REWRITE_TAC[REAL_POW_DIV] THEN
   ONCE_REWRITE_TAC[ARITH_RULE `4 = 2 * 2`] THEN
   REWRITE_TAC[GSYM REAL_POW_POW] THEN
   SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
   MATCH_MP_TAC(REAL_ARITH `x:real = y ==> x <= y`) THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
   UNDISCH_TAC `~(&(SUC n) = &0)` THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
   CONV_TAC REAL_FIELD;
   MATCH_MP_TAC REALLIM_NULL_LMUL THEN
   MATCH_MP_TAC REALLIM_NULL_LMUL THEN
   REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]]);;

(* Algebraic identity: R*r - S*s - r*P = r*(R - P) - S*s *)
let REAL_MUL_SUB_REARRANGE = prove
 (`!R S r s P:real. R * r - S * s - r * P = r * (R - P) - S * s`,
  CONV_TAC REAL_RING);;

(* Helper: triangle inequality for the inductive step *)
(* |R*r - S*s - r*r^n| <= |r|*|R - r^n| + |S|*|s| *)
let CHAR_FN_SUM_IID_TRIANGLE = prove
 (`!R S r s:real n.
     abs r <= &1 /\ abs S <= &1 /\
     abs(R - r pow (SUC n)) <= &(SUC n) * abs s
     ==> abs(R * r - S * s - r * r pow (SUC n))
         <= &(SUC(SUC n)) * abs s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_MUL_SUB_REARRANGE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(r * (R - r pow (SUC n))) + abs(S * s)` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * (&(SUC n) * abs s) + &1 * abs s` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN
   ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL];
   REWRITE_TAC[REAL_MUL_LID] THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC]);;

(* Bound on IID sum char_fn_re deviation from power *)
(* |Re(phi_sum) - (Re phi)^(n+1)| <= (n+1) * |Im phi| *)
let CHAR_FN_SUM_IID_RE_BOUND = prove
 (`!p:A prob_space (X:num->A->real) n t.
     (!i. i <= n ==> simple_rv p (X i)) /\
     (!i. i <= n ==>
        char_fn_re p (X i) t = char_fn_re p (X 0) t /\
        char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> abs(char_fn_re p (\x. sum(0..n) (\i. X i x)) t -
             char_fn_re p (X 0) t pow (SUC n))
         <= &(SUC n) * abs(char_fn_im p (X 0) t)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..0) (\i. (X:num->A->real) i x)) = X 0`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; SUM_SING_NUMSEG] THEN GEN_TAC THEN BETA_TAC THEN
    REFL_TAC; ALL_TAC] THEN
   REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_SUB_REFL; REAL_ABS_NUM] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_ABS_POS];
   (* Step case: n -> SUC n *)
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(0..SUC n) (\i. (X:num->A->real) i x)) =
                 (\x. sum(0..n) (\i. X i x) + X (SUC n) x)`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN BETA_TAC THEN
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN
    GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) ((X:num->A->real) (SUC n))`
     ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `indep_rv (p:A prob_space)
     (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) (X (SUC n))`
     ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. sum(0..n) (\i. (X:num->A->real) i x)`;
     `(X:num->A->real) (SUC n)`; `t:real`]
     CHAR_FN_ADD_INDEP_RE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   BETA_TAC THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `char_fn_re (p:A prob_space) ((X:num->A->real) (SUC n)) t =
      char_fn_re p (X 0) t /\
      char_fn_im p (X (SUC n)) t = char_fn_im p (X 0) t`
     STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   ONCE_REWRITE_TAC[real_pow] THEN
   MATCH_MP_TAC CHAR_FN_SUM_IID_TRIANGLE THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CHAR_FN_RE_BOUND THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CHAR_FN_IM_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   GEN_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* |sin(x) - x| <= |x|^3 / 2 via Taylor remainder *)
let SIN_APPROX_BOUND = prove
 (`!x:real. abs(sin(x) - x) <= abs(x) pow 3 / &2`,
  GEN_TAC THEN MP_TAC(ISPECL [`0`; `Cx x`] TAYLOR_CSIN) THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; VSUM_CLAUSES_LEFT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM CX_SIN; complex_pow; COMPLEX_POW_1; COMPLEX_MUL_RID;
              COMPLEX_MUL_LID; COMPLEX_DIV_1] THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_NEG; GSYM CX_POW; GSYM CX_ADD;
              GSYM CX_SUB; GSYM CX_DIV; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[IM_CX; REAL_ABS_0; REAL_EXP_0; REAL_MUL_LID] THEN
  SIMP_TAC[REAL_EVENPOW_ABS; ARITH] THEN REAL_ARITH_TAC);;

(* char_fn_im bound for mean-zero RVs: |E[sin(tX)]| <= |t|^3 * E[|X|^3] / 2 *)
let CHAR_FN_IM_MEAN_ZERO_BOUND = prove
 (`!p:A prob_space (X:A->real) t.
     simple_rv p X /\ simple_expectation p X = &0
     ==> abs(char_fn_im p X t)
         <= abs(t) pow 3 * simple_expectation p (\x. abs(X x) pow 3) / &2`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[char_fn_im] THEN
  (* Establish simple_rv for sin(tX) *)
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sin(t * (X:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
     `\y:real. sin(t * y)`] SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  (* E[sin(tX)] = E[sin(tX) - tX] since E[tX] = t*E[X] = 0 *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x:A. sin(t * (X:A->real) x)) =
     simple_expectation p (\x. sin(t * X x) - t * X x)`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `simple_expectation (p:A prob_space) (\x:A. sin(t * (X:A->real) x) - t * X x) =
      simple_expectation p (\x. sin(t * X x)) -
      simple_expectation p (\x. t * X x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN
    ASM_SIMP_TAC[SIMPLE_RV_CMUL]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `t:real`]
     SIMPLE_EXPECTATION_CMUL) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO];
   ALL_TAC] THEN
  (* |E[sin(tX) - tX]| <= E[|sin(tX) - tX|] *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x:A. abs(sin(t * (X:A->real) x) - t * X x))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_ABS_LE THEN
   MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_SIMP_TAC[SIMPLE_RV_CMUL];
   ALL_TAC] THEN
  (* E[|sin(tX) - tX|] <= E[abs(tX)^3 / 2] via SIN_APPROX_BOUND *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\x:A. abs(t * (X:A->real) x) pow 3 / &2)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ABS THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_SIMP_TAC[SIMPLE_RV_CMUL];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
      `\y:real. abs(t * y) pow 3 / &2`] SIMPLE_RV_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
   X_GEN_TAC `a:A` THEN DISCH_TAC THEN
   MP_TAC(SPEC `t * (X:A->real) a` SIN_APPROX_BOUND) THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* E[abs(tX)^3/2] = abs(t)^3/2 * E[abs(X)^3] *)
  SUBGOAL_THEN
    `(\x:A. abs(t * (X:A->real) x) pow 3 / &2) =
     (\x. (abs(t) pow 3 / &2) * abs(X x) pow 3)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; REAL_ABS_MUL; REAL_POW_MUL] THEN
   GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x:A. abs((X:A->real) x) pow 3`;
                  `abs(t) pow 3 / &2`] SIMPLE_EXPECTATION_CMUL) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
     `\y:real. abs(y) pow 3`] SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* Helper: inv(sqrt(SUC n)) -> 0 *)
let REALLIM_INV_SQRT_SUC = prove
 (`((\n. inv(sqrt(&(SUC n)))) ---> &0) sequentially`,
  SUBGOAL_THEN `((\n. sqrt(inv(&(SUC n)))) ---> sqrt(&0)) sequentially`
    MP_TAC THENL
  [MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
   CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT]; ALL_TAC] THEN
   MP_TAC(SPEC `&1` REALLIM_1_OVER_N_OFFSET) THEN
   MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   REPEAT STRIP_TAC THEN
   AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
   REWRITE_TAC[SQRT_0; SQRT_INV]]);;

(* CLT error term: (n+1) * |Im phi(t/sqrt(n+1))| -> 0 for mean-zero X *)

let CLT_IM_ERROR_VANISHES = prove
 (`!p:A prob_space (X:A->real) t.
    simple_rv p X /\ simple_expectation p X = &0
    ==> ((\n. &(SUC n) * abs(char_fn_im p X (t / sqrt(&(SUC n)))))
         ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m3 = simple_expectation (p:A prob_space)
    (\x. abs((X:A->real) x) pow 3)` THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. abs(t) pow 3 * m3 / &2 * inv(sqrt(&(SUC n)))` THEN
  CONJ_TAC THENL
  [(* Eventually bound *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                   `t / sqrt(&(SUC n))`] CHAR_FN_IM_MEAN_ZERO_BOUND) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_ABS] THEN
   SUBGOAL_THEN `abs(&(SUC n)) = &(SUC n)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_NUM]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(SUC n) * (abs(t / sqrt(&(SUC n))) pow 3 * m3 / &2)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[REAL_ABS_DIV; REAL_POW_DIV] THEN
   SUBGOAL_THEN `abs(sqrt(&(SUC n))) = sqrt(&(SUC n))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 < sqrt(&(SUC n))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `sqrt(&(SUC n)) * sqrt(&(SUC n)) = &(SUC n)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&(SUC n)` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS; REAL_POW_2] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
   SUBGOAL_THEN `sqrt(&(SUC n)) pow 3 = &(SUC n) * sqrt(&(SUC n))`
     SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 = SUC(SUC(SUC 0))`; real_pow;
                REAL_POW_1; REAL_MUL_RID] THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN
   MATCH_MP_TAC(REAL_FIELD
     `&0 < s /\ &0 < n ==> n * (t / (n * s) * m / &2) = t * m / &2 * inv s`) THEN
   ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
   (* Limit part: C * inv(sqrt(SUC n)) -> 0 *)
   REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_NULL_LMUL) THEN
   MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_NULL_LMUL) THEN
   MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_NULL_LMUL) THEN
   REWRITE_TAC[REALLIM_INV_SQRT_SUC]]);;

(* CLT: characteristic function of IID sum converges *)
let CLT_CHAR_FN_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) t.
    (!n. simple_rv p (X n)) /\
    simple_expectation p (X 0) = &0 /\
    &0 < simple_expectation p (\x. X 0 x pow 2) /\
    (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
           char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> ((\n. char_fn_re p (\x. sum(0..n) (\i. X i x))
                            (t / sqrt(&(SUC n))))
         ---> exp(--(t pow 2 * simple_expectation p (\x. X 0 x pow 2) / &2)))
        sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_TRANSFORM) THEN
  EXISTS_TAC
    `\n. char_fn_re (p:A prob_space) (X 0) (t / sqrt(&(SUC n))) pow (SUC n)` THEN
  CONJ_TAC THENL
  [(* Difference -> 0 *)
   MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_NULL_COMPARISON) THEN
   EXISTS_TAC
     `\n. &(SUC n) * abs(char_fn_im (p:A prob_space) (X 0)
                           (t / sqrt(&(SUC n))))` THEN
   CONJ_TAC THENL
   [(* Eventually bound *)
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    MATCH_MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`;
                    `t / sqrt(&(SUC n))`] CHAR_FN_SUM_IID_RE_BOUND) THEN
    ASM_MESON_TAC[];
    (* Limit: (n+1)*|Im phi(t/sqrt(n+1))| -> 0 *)
    MATCH_MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`; `t:real`]
      CLT_IM_ERROR_VANISHES) THEN
    ASM_REWRITE_TAC[]];
   (* char_fn_re pow -> exp *)
   MATCH_MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`; `t:real`]
     CHAR_FN_RE_POW_CONV_EXP) THEN
   ASM_REWRITE_TAC[]]);;

(* Algebraic identity for product-subtraction decomposition *)
let REAL_MUL_SUB_DECOMP = prove
 (`!a b P Q:real. (a + b) * P - a * Q = b * P + a * (P - Q)`,
  CONV_TAC REAL_RING);;

(* Helper: (a+b)^n - a^n <= n*b when 0<=a, 0<=b, a+b<=1 *)
let REAL_POW_DIFF_BOUND = prove
 (`!n a b. &0 <= a /\ &0 <= b /\ a + b <= &1
           ==> (a + b) pow n - a pow n <= &n * b`,
  INDUCT_TAC THENL
  [REWRITE_TAC[real_pow; REAL_SUB_REFL] THEN REAL_ARITH_TAC;
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THEN
   ONCE_REWRITE_TAC[REAL_MUL_SUB_DECOMP] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `b * &1 + &1 * (&n * b)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `a * (&n * b)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[REAL_POS]]]];
    REAL_ARITH_TAC]]);;

(* If f^2 --> 0 then f --> 0 *)
let REALLIM_NULL_SQABS = prove
 (`!(f:num->real). ((\n. f(n) pow 2) ---> &0) sequentially
                ==> (f ---> &0) sequentially`,
  GEN_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_TAC THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `?N:num. !n. N <= n ==> abs((f:num->real) n pow 2) < eps pow 2`
    MP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:num->real) n pow 2 < eps pow 2` ASSUME_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(SPEC `(f:num->real) n` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_MESON_TAC[REAL_LT_SQUARE_ABS;
                 REAL_ARITH `&0 < e ==> abs e = e`]);;

(* x^2 - y^2 = (x-y)(x+y) *)
let REAL_SQ_DIFF_FACTOR = prove
 (`!x y:real. x pow 2 - y pow 2 = (x - y) * (x + y)`,
  CONV_TAC REAL_RING);;

(* Bound on difference of squares when both values bounded by 1 *)
let REAL_DIFF_SQ_BOUND = prove
 (`!x y d. abs(x - y) <= d /\ abs(x) <= &1 /\ abs(y) <= &1
            ==> abs(x pow 2 - y pow 2) <= &2 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_SQ_DIFF_FACTOR; REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `d * &2` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL2 THEN
   REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
   REAL_ARITH_TAC]);;

(* x^2 <= |x| when |x| <= 1 *)
let REAL_SQ_LE_ABS = prove
 (`!x. abs x <= &1 ==> x pow 2 <= abs x`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs x pow 2` THEN CONJ_TAC THENL
  [REWRITE_TAC[REAL_ABS_POW] THEN REAL_ARITH_TAC;
   GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
   MATCH_MP_TAC REAL_POW_MONO_INV THEN
   ASM_REWRITE_TAC[REAL_ABS_POS] THEN ARITH_TAC]);;

(* REAL_POW_POW with renamed variables to avoid clash with free n *)
let REAL_POW_POW_SWAP = prove
 (`!x:real m p. (x pow m) pow p = (x pow p) pow m`,
  REWRITE_TAC[REAL_POW_POW; MULT_SYM]);;

(* Helper: S'^2 bound from modulus identity + re/im bounds *)
let S_SQ_DECOMP_BOUND = prove
 (`!R S' r s n.
    R pow 2 + S' pow 2 = (r pow 2 + s pow 2) pow SUC n /\
    (r pow 2 + s pow 2) pow SUC n - (r pow 2) pow SUC n
      <= &(SUC n) * abs s /\
    abs((r pow SUC n) pow 2 - R pow 2) <= &2 * &(SUC n) * abs s
    ==> S' pow 2 <= &3 * &(SUC n) * abs s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((r pow 2 + s pow 2) pow SUC n - (r pow 2) pow SUC n) +
              abs((r pow SUC n) pow 2 - R pow 2)` THEN
  CONJ_TAC THENL
  [(* S'^2 <= (A-B) + |C-D| using (r^m)^p = (r^p)^m *)
   MP_TAC(SPECL [`r:real`; `SUC n`; `2`] REAL_POW_POW_SWAP) THEN
   ASM_REAL_ARITH_TAC;
   (* (A-B) + |C-D| <= (n+1)|s| + 2(n+1)|s| = 3(n+1)|s| *)
   ASM_REAL_ARITH_TAC]);;

(* Bound on Im^2 of characteristic function of IID sum:
   Im_Sn^2 <= 3*(n+1)*|char_fn_im(X_0, t)| *)
let CHAR_FN_SUM_IID_IM_SQ_BOUND = prove
 (`!p:A prob_space (X:num->A->real) n t.
     (!i. i <= n ==> simple_rv p (X i)) /\
     (!i. i <= n ==>
        char_fn_re p (X i) t = char_fn_re p (X 0) t /\
        char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> char_fn_im p (\x. sum(0..n) (\i. X i x)) t pow 2
         <= &3 * (&(SUC n) * abs(char_fn_im p (X 0) t))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `r = char_fn_re (p:A prob_space) ((X:num->A->real) 0) t` THEN
  ABBREV_TAC `s = char_fn_im (p:A prob_space) ((X:num->A->real) 0) t` THEN
  ABBREV_TAC `R = char_fn_re (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
  ABBREV_TAC `S' = char_fn_im (p:A prob_space)
    (\x:A. sum(0..n) (\i. (X:num->A->real) i x)) t` THEN
  (* Step 1: R^2+S'^2 = (r^2+s^2)^(n+1) via MP_TAC *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`; `t:real`]
    CHAR_FN_SUM_IID_MODULUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 2: |R-r^(n+1)| <= (n+1)|s| *)
  MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`; `t:real`]
    CHAR_FN_SUM_IID_RE_BOUND) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 3: r^2+s^2 <= 1 *)
  MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`; `t:real`]
    CHAR_FN_MODULUS_LE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 4: |s| <= 1 *)
  MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`; `t:real`]
    CHAR_FN_IM_BOUND) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 5: |r| <= 1 *)
  MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`; `t:real`]
    CHAR_FN_RE_BOUND) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 5b: |r^(n+1)| <= 1 *)
  SUBGOAL_THEN `abs(r pow (SUC n)) <= &1` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
   ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  (* Step 6: |R| <= 1 *)
  MP_TAC(ISPECL [`p:A prob_space`;
    `(\x:A. sum(0..n) (\i. (X:num->A->real) i x))`; `t:real`]
    CHAR_FN_RE_BOUND) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* Step 7: (r^2+s^2)^(n+1) - (r^2)^(n+1) <= (n+1)*s^2 *)
  SUBGOAL_THEN `(r pow 2 + s pow 2) pow (SUC n) - (r pow 2) pow (SUC n)
                <= &(SUC n) * s pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_DIFF_BOUND THEN
   ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  (* Step 8: s^2 <= |s| *)
  SUBGOAL_THEN `s pow 2 <= abs s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_SQ_LE_ABS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 9: first part <= (n+1)*|s| *)
  SUBGOAL_THEN `(r pow 2 + s pow 2) pow (SUC n) - (r pow 2) pow (SUC n)
                <= &(SUC n) * abs s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `&(SUC n) * s pow 2` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  (* Step 10: |second part| <= 2*(n+1)*|s| *)
  SUBGOAL_THEN `abs((r pow (SUC n)) pow 2 - R pow 2)
                <= &2 * (&(SUC n) * abs s)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_DIFF_SQ_BOUND THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Final: apply S_SQ_DECOMP_BOUND helper lemma *)
  MATCH_MP_TAC S_SQ_DECOMP_BOUND THEN
  MAP_EVERY EXISTS_TAC [`R:real`; `r:real`] THEN
  ASM_REWRITE_TAC[]);;

(* CLT: Imaginary part of char fn of standardized sum converges to 0 *)
let CLT_CHAR_FN_IM_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) t.
    (!n. simple_rv p (X n)) /\
    simple_expectation p (X 0) = &0 /\
    &0 < simple_expectation p (\x. X 0 x pow 2) /\
    (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
           char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> ((\n. char_fn_im p (\x. sum(0..n) (\i. X i x))
                            (t / sqrt(&(SUC n))))
         ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_NULL_SQABS THEN BETA_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_NULL_COMPARISON) THEN
  EXISTS_TAC `\n. &3 *
    (&(SUC n) * abs(char_fn_im (p:A prob_space) ((X:num->A->real) 0)
      (t / sqrt(&(SUC n)))))` THEN
  CONJ_TAC THENL
  [(* Eventually bound: |Im_Sn^2| <= 3*(n+1)*|s_n| *)
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
   X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
   SUBGOAL_THEN `!y:real. abs(y pow 2) = y pow 2`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`;
                    `t / sqrt(&(SUC n))`] CHAR_FN_SUM_IID_IM_SQ_BOUND) THEN
   ASM_MESON_TAC[];
   (* Limit: 3 * ((n+1)*|s_n|) -> 0 *)
   MATCH_MP_TAC(INST_TYPE [`:num`,`:A`] REALLIM_NULL_LMUL) THEN
   MATCH_MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) 0`; `t:real`]
     CLT_IM_ERROR_VANISHES) THEN
   ASM_MESON_TAC[]]);;

(* Combined CLT: characteristic function of standardized IID sum converges
   Re -> exp(-t^2*sigma^2/2), Im -> 0 *)
let CLT_CHAR_FN_CONVERGENCE_FULL = prove
 (`!p:A prob_space (X:num->A->real) t.
    (!n. simple_rv p (X n)) /\
    simple_expectation p (X 0) = &0 /\
    &0 < simple_expectation p (\x. X 0 x pow 2) /\
    (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
           char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> ((\n. char_fn_re p (\x. sum(0..n) (\i. X i x))
                            (t / sqrt(&(SUC n))))
         ---> exp(--(t pow 2 * simple_expectation p (\x. X 0 x pow 2) / &2)))
        sequentially /\
        ((\n. char_fn_im p (\x. sum(0..n) (\i. X i x))
                            (t / sqrt(&(SUC n))))
         ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
  [MATCH_MP_TAC CLT_CHAR_FN_CONVERGENCE;
   MATCH_MP_TAC CLT_CHAR_FN_IM_CONVERGENCE] THEN
  ASM_MESON_TAC[]);;

(* Standardized CLT: after normalizing by sigma, char fn converges to
   the standard normal characteristic function exp(-t^2/2) *)
let CLT_STANDARDIZED = prove
 (`!p:A prob_space (X:num->A->real) t.
    (!n. simple_rv p (X n)) /\
    simple_expectation p (X 0) = &0 /\
    &0 < simple_expectation p (\x. X 0 x pow 2) /\
    (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
           char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> ((\n. char_fn_re p (\x. sum(0..n) (\i. X i x))
              (t / (sqrt(simple_expectation p (\x. X 0 x pow 2)) *
                    sqrt(&(SUC n)))))
         ---> exp(--(t pow 2 / &2)))
        sequentially /\
        ((\n. char_fn_im p (\x. sum(0..n) (\i. X i x))
              (t / (sqrt(simple_expectation p (\x. X 0 x pow 2)) *
                    sqrt(&(SUC n)))))
         ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
    `sigma_sq = simple_expectation (p:A prob_space)
       (\x. (X:num->A->real) 0 x pow 2)` THEN
  SUBGOAL_THEN `&0 < sigma_sq` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt sigma_sq` ASSUME_TAC THENL
  [ASM_MESON_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sqrt sigma_sq = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Rewrite t/(sqrt(s)*sqrt(n+1)) = (t/sqrt(s))/sqrt(n+1) *)
  SUBGOAL_THEN `!m. t / (sqrt sigma_sq * sqrt(&(SUC m))) =
                    (t / sqrt sigma_sq) / sqrt(&(SUC m))`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
   REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  (* Rewrite exp(--(t^2/2)) to match CLT_CHAR_FN_CONVERGENCE_FULL form *)
  SUBGOAL_THEN
    `exp(--(t pow 2 / &2)) =
     exp(--((t / sqrt sigma_sq) pow 2 * sigma_sq / &2))`
    SUBST1_TAC THENL
  [AP_TERM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[REAL_POW_DIV] THEN
   SUBGOAL_THEN `sqrt sigma_sq pow 2 = sigma_sq` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `&0 < sigma_sq` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  (* Expand sigma_sq back to simple_expectation for MATCH_MP_TAC *)
  EXPAND_TAC "sigma_sq" THEN
  MATCH_MP_TAC CLT_CHAR_FN_CONVERGENCE_FULL THEN
  ASM_MESON_TAC[]);;

(* Variance form: when E[X] = 0, Var(X) = E[X^2] *)
let SIMPLE_VARIANCE_MEAN_ZERO = prove
 (`!p:A prob_space (X:A->real).
     simple_rv p X /\ simple_expectation p X = &0
     ==> simple_variance p X = simple_expectation p (\x. X x pow 2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SIMPLE_VARIANCE_ALT] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* CLT with variance notation: nicer form of CLT_STANDARDIZED *)
let CLT_VARIANCE_FORM = prove
 (`!p:A prob_space (X:num->A->real) t.
    (!n. simple_rv p (X n)) /\
    simple_expectation p (X 0) = &0 /\
    &0 < simple_variance p (X 0) /\
    (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
           char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> ((\n. char_fn_re p (\x. sum(0..n) (\i. X i x))
              (t / (sqrt(simple_variance p (X 0)) * sqrt(&(SUC n)))))
         ---> exp(--(t pow 2 / &2)))
        sequentially /\
        ((\n. char_fn_im p (\x. sum(0..n) (\i. X i x))
              (t / (sqrt(simple_variance p (X 0)) * sqrt(&(SUC n)))))
         ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simple_variance (p:A prob_space) ((X:num->A->real) 0) =
                simple_expectation p (\x. X 0 x pow 2)` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_VARIANCE_MEAN_ZERO THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < simple_expectation (p:A prob_space)
    (\x. (X:num->A->real) 0 x pow 2)` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLT_STANDARDIZED THEN
  ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* MOMENT GENERATING FUNCTION AND HOEFFDING'S INEQUALITY                     *)
(* ========================================================================= *)

(* Moment generating function for simple RVs *)
let simple_mgf = new_definition
  `simple_mgf (p:A prob_space) (X:A->real) (s:real) =
   simple_expectation p (\x. exp(s * X x))`;;

(* exp(sX) is simple_rv when X is *)
let SIMPLE_RV_EXP = prove
 (`!p:A prob_space (X:A->real) s.
     simple_rv p X ==> simple_rv p (\x. exp(s * X x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. exp(s * y)`]
    SIMPLE_RV_REAL_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC);;

(* MGF is non-negative *)
let SIMPLE_MGF_NONNEG = prove
 (`!p:A prob_space (X:A->real) s.
     simple_rv p X ==> &0 <= simple_mgf p X s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_mgf] THEN
  MATCH_MP_TAC SIMPLE_EXPECTATION_POS THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_EXP THEN ASM_REWRITE_TAC[];
   X_GEN_TAC `a:A` THEN DISCH_TAC THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT]]);;

(* ========================================================================= *)
(* CHERNOFF BOUND (EXPONENTIAL MARKOV)                                       *)
(* ========================================================================= *)

(* Chernoff bound: P(X >= t) <= exp(-st) * E[exp(sX)] for s > 0.
   This follows from applying Markov to exp(sX). *)
let CHERNOFF_BOUND = prove
 (`!p:A prob_space (X:A->real) s t.
     simple_rv p X /\ &0 < s
     ==> prob p {x | x IN prob_carrier p /\ X x >= t} <=
         exp(--(s * t)) * simple_mgf p X s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[simple_mgf] THEN
  SUBGOAL_THEN `{x:A | x IN prob_carrier p /\ (X:A->real) x >= t} =
                {x | x IN prob_carrier p /\ exp(s * X x) >= exp(s * t)}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
   ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[real_ge; REAL_EXP_MONO_LE] THEN
   ASM_SIMP_TAC[REAL_LE_LMUL_EQ];
   ALL_TAC] THEN
  MP_TAC(ISPECL
    [`p:A prob_space`; `\x:A. exp(s * (X:A->real) x)`; `exp(s * t)`]
    MARKOV_INEQUALITY_SIMPLE) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y:real. exp(s * y)`]
     SIMPLE_RV_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    CONJ_TAC THENL
    [X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
     REWRITE_TAC[REAL_EXP_POS_LT]]];
   ALL_TAC] THEN
  BETA_TAC THEN
  REWRITE_TAC[real_div] THEN
  SUBGOAL_THEN `inv(exp(s * t)) = exp(--(s * t))` SUBST1_TAC THENL
  [REWRITE_TAC[GSYM REAL_EXP_NEG]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

(* ========================================================================= *)
(* HOEFFDING'S LEMMA AND INEQUALITY                                          *)
(* ========================================================================= *)

(* Analytic lemma: for 0 <= p <= 1, the function
   L(h) = -ph + log(1-p+p*exp(h)) satisfies L(h) <= h^2/8.
   This is the core of Hoeffding's lemma.
   We prove it using L(0)=0, L'(0)=0, L''(h) <= 1/4. *)

(* Key fact: x*exp(h)/(1-x+x*exp(h))^2 <= 1/4 for 0 <= x <= 1 *)
(* This follows from the AM-GM: for u > 0, u/(1+u)^2 <= 1/4,
   and setting u = x*exp(h)/(1-x) when 0 < x < 1 *)

(* Pointwise convexity bound on exp: since exp is convex,
   exp(s*x) <= (b-x)/(b-a)*exp(s*a) + (x-a)/(b-a)*exp(s*b) *)
let CONVEX_BOUND_EXP = prove
 (`!s a b x:real. a < b /\ a <= x /\ x <= b
     ==> exp(s * x) <= (b - x) / (b - a) * exp(s * a) +
                        (x - a) / (b - a) * exp(s * b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `s * x:real = (b - x) / (b - a) * (s * a) + (x - a) / (b - a) * (s * b)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
  [UNDISCH_TAC `~(b - a = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC (ISPEC `(:real)` REAL_CONVEX_ON_EXP) THEN
  REWRITE_TAC[real_convex_on; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
   UNDISCH_TAC `~(b - a = &0)` THEN CONV_TAC REAL_FIELD]);;


(* AM-GM: 4*A*B <= (A+B)^2, equivalent to (A-B)^2 >= 0 *)
let FOUR_AB_LE_APB_SQ = prove
 (`!A B:real. &4 * A * B <= (A + B) pow 2`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `A - B:real` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB] THEN
  REAL_ARITH_TAC);;

(* AM-GM fractional bound: A*B/(A+B)^2 <= 1/4
   Note: explicit parens on (A * B) needed because / has higher precedence
   than * in HOL Light, so A * B / C parses as A * (B / C). *)
let AM_GM_FRAC_BOUND = prove
 (`!A B:real. &0 <= A /\ &0 <= B /\ &0 < A + B
   ==> (A * B) / (A + B) pow 2 <= &1 / &4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (A + B:real) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  (* Goal: A * B <= &1 / &4 * (A + B) pow 2
     i.e. A * B <= inv(&4) * (A + B) pow 2 *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((A + B:real) pow 2) / &4` THEN
  CONJ_TAC THENL
  [SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &4`] THEN
   (* Goal: (A * B) * &4 <= (A + B) pow 2
      Note: (A * B) * &4 is left-associated since RDIV_EQ builds a * c *)
   GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
   (* Goal: &4 * (A * B) <= (A + B) pow 2 = FOUR_AB_LE_APB_SQ *)
   REWRITE_TAC[FOUR_AB_LE_APB_SQ];
   (* Goal: ((A + B) pow 2) / &4 <= &1 / &4 * (A + B) pow 2 *)
   REWRITE_TAC[real_div; REAL_MUL_LID] THEN
   GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
   REWRITE_TAC[REAL_LE_REFL]]);;

(* Denominator 1-p+p*exp(t) is always positive for 0 <= p <= 1 *)
let HOEFFDING_DENOM_POS = prove
 (`!p t:real. &0 <= p /\ p <= &1 ==> &0 < &1 - p + p * exp t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `p = &0` THENL
  [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_SUB_RZERO] THEN
   REAL_ARITH_TAC;
   SUBGOAL_THEN `&0 < p * exp t` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_POS_LT]];
    ASM_REAL_ARITH_TAC]]);;

(* Second derivative bound for Hoeffding: L''(t) <= 1/4
   Note: parens around numerator needed due to / precedence. *)
let HOEFFDING_SECOND_DERIV_BOUND = prove
 (`!p t:real. &0 <= p /\ p <= &1
   ==> (p * (&1 - p) * exp t) / (&1 - p + p * exp t) pow 2 <= &1 / &4`,
  REPEAT STRIP_TAC THEN
  (* Rewrite numerator: p * (1-p) * exp t = (1-p) * (p * exp t) *)
  SUBGOAL_THEN
    `(p * (&1 - p) * exp t) / (&1 - p + p * exp t:real) pow 2 =
     ((&1 - p) * (p * exp t)) / (&1 - p + p * exp t) pow 2`
    SUBST1_TAC THENL
  [AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[REAL_MUL_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   MATCH_ACCEPT_TAC REAL_MUL_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC AM_GM_FRAC_BOUND THEN
  REPEAT CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC REAL_LE_MUL THEN
   CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT]];
   MATCH_MP_TAC HOEFFDING_DENOM_POS THEN ASM_REWRITE_TAC[]]);;

(* First derivative of Hoeffding's L function:
   L(t) = -p*t + log(1-p+p*exp(t)),  L'(t) = -p + p*exp(t)/(1-p+p*exp(t)) *)
let HOEFFDING_L_HAS_DERIV = prove
 (`!p t:real. &0 <= p /\ p <= &1 ==>
    ((\t. --p * t + log(&1 - p + p * exp t))
     has_real_derivative
     (--p + (p * exp t) / (&1 - p + p * exp t)))
    (atreal t)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC HOEFFDING_DENOM_POS THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[REAL_MUL_RID; REAL_MUL_LID; REAL_ADD_LID; GSYM real_div]]);;

(* Second derivative of Hoeffding's L function:
   L''(t) = p*(1-p)*exp(t) / (1-p+p*exp(t))^2 *)
let HOEFFDING_LPRIME_HAS_DERIV = prove
 (`!p t:real. &0 <= p /\ p <= &1 ==>
    ((\t. --p + (p * exp t) / (&1 - p + p * exp t))
     has_real_derivative
     ((p * (&1 - p) * exp t) / (&1 - p + p * exp t) pow 2))
    (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&1 - p + p * exp t = &0)` ASSUME_TAC THENL
  [MATCH_MP_TAC (REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
   MATCH_MP_TAC HOEFFDING_DENOM_POS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REAL_DIFF_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_LID; REAL_ADD_LID] THEN
  UNDISCH_TAC `~(&1 - p + p * exp t = &0)` THEN
  CONV_TAC REAL_FIELD);;

(* L(0) = 0 *)
let HOEFFDING_L_AT_ZERO = prove
 (`!p:real. --p * &0 + log(&1 - p + p * exp(&0)) = &0`,
  GEN_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_EXP_0; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `&1 - p + p = &1`; LOG_1]);;

(* L'(0) = 0 *)
let HOEFFDING_LPRIME_AT_ZERO = prove
 (`!p:real. --p + (p * exp(&0)) / (&1 - p + p * exp(&0)) = &0`,
  GEN_TAC THEN
  REWRITE_TAC[REAL_EXP_0; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `&1 - p + p = &1`] THEN
  REWRITE_TAC[REAL_DIV_1] THEN REAL_ARITH_TAC);;

(* Second derivative bound for abs: abs(L''(t)) <= 1/4.
   Since L''(t) >= 0 (numerator p*(1-p)*exp(t) >= 0 when 0<=p<=1), abs = id. *)
let HOEFFDING_SECOND_DERIV_ABS_BOUND = prove
 (`!p t:real. &0 <= p /\ p <= &1
   ==> abs((p * (&1 - p) * exp t) / (&1 - p + p * exp t) pow 2) <= &1 / &4`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
  CONJ_TAC THENL
  [(* Non-negativity of L''(t) *)
   MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT]]];
    REWRITE_TAC[REAL_LE_POW_2]];
   (* L''(t) <= 1/4 *)
   MATCH_MP_TAC HOEFFDING_SECOND_DERIV_BOUND THEN ASM_REWRITE_TAC[]]);;

(* Taylor bound: L(t) <= t^2/8 using REAL_TAYLOR with n=1, B=1/4 *)
let HOEFFDING_L_TAYLOR_BOUND = prove
 (`!p t:real. &0 <= p /\ p <= &1
   ==> --p * t + log(&1 - p + p * exp t) <= t pow 2 / &8`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL
    [`\(i:num) (t:real).
       if i = 0 then --p * t + log(&1 - p + p * exp t)
       else if i = 1 then --p + (p * exp t) / (&1 - p + p * exp t)
       else (p * (&1 - p) * exp t) / (&1 - p + p * exp t) pow 2`;
     `1`; `(:real)`; `&1 / &4`] REAL_TAYLOR) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [(* Derivative conditions for i <= 1 *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 0 \/ i = 1` DISJ_CASES_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 = 0 <=> T`; ARITH_RULE `1 = 0 <=> F`;
                     ARITH_RULE `1 = 1 <=> T`; ARITH_RULE `0 + 1 = 1`;
                     ARITH_RULE `1 + 1 = 2`; ARITH_RULE `~(2 = 0)`;
                     ARITH_RULE `~(2 = 1)`] THENL
    [(* i=0: derivative of L *)
     REWRITE_TAC[WITHINREAL_UNIV] THEN
     MATCH_MP_TAC HOEFFDING_L_HAS_DERIV THEN ASM_REWRITE_TAC[];
     (* i=1: derivative of L' *)
     REWRITE_TAC[WITHINREAL_UNIV] THEN
     MATCH_MP_TAC HOEFFDING_LPRIME_HAS_DERIV THEN ASM_REWRITE_TAC[]];
    (* Bound on f(n+1) = f(2) = L'' *)
    X_GEN_TAC `u:real` THEN
    REWRITE_TAC[ARITH_RULE `1 + 1 = 2`; ARITH_RULE `~(2 = 0)`;
                 ARITH_RULE `~(2 = 1)`] THEN
    MATCH_MP_TAC HOEFFDING_SECOND_DERIV_ABS_BOUND THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Apply with w=0, z=t *)
  DISCH_THEN (MP_TAC o SPECL [`&0`; `t:real`]) THEN
  (* Simplify sum(0..1) and FACT *)
  REWRITE_TAC[ARITH_RULE `1 + 1 = 2`] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH_RULE `0 + 1 = 1`] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `1 <= 1`; ARITH_RULE `1 + 1 = 2`] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `~(3 <= 2)`] THEN
  REWRITE_TAC[ARITH_RULE `0 = 0 <=> T`; ARITH_RULE `~(1 = 0)`;
               ARITH_RULE `1 = 1 <=> T`; ARITH_RULE `~(2 = 0)`;
               ARITH_RULE `~(2 = 1)`] THEN
  REWRITE_TAC[HOEFFDING_L_AT_ZERO; HOEFFDING_LPRIME_AT_ZERO] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[FACT; ARITH_RULE `SUC 0 = 1`; ARITH_RULE `SUC 1 = 2`] THEN
  REWRITE_TAC[ARITH_RULE `1 * 1 = 1`; ARITH_RULE `2 * 1 = 2`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_MUL_RID; REAL_POW_1] THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_ABS] THEN
  (* abs(L(t) - (0 + 0 * t)) <= (1/4) * abs(t)^2 / 2 *)
  (* i.e. abs(L(t)) <= abs(t)^2 / 8 *)
  REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LZERO; REAL_ADD_RID; REAL_SUB_RZERO] THEN
  (* Simplify sum(2..1)(...) = &0 since 1 < 2 *)
  SIMP_TAC[SUM_TRIV_NUMSEG; ARITH_RULE `1 < 2`] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  (* Goal: abs(L(t)) <= 1/4 * abs(t)^2 / 2 ==> L(t) <= t^2/8 *)
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(--p * t + log (&1 - p + p * exp t))` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_ABS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 / &4 * abs(t) pow 2 / &2` THEN
  ASM_REWRITE_TAC[] THEN
  (* abs(t)^2 = t^2, then 1/4 * t^2 / 2 = t^2 / 8 *)
  SUBGOAL_THEN `abs(t:real) pow 2 = t pow 2` SUBST1_TAC THENL
  [REWRITE_TAC[GSYM REAL_ABS_POW; REAL_ABS_REFL; REAL_LE_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_FIELD);;

(* Algebraic identity: exp(L(u)) = (1-p)*exp(-pu) + p*exp((1-p)*u) *)
let HOEFFDING_EXP_L_EQ = prove
 (`!p u:real. &0 <= p /\ p <= &1
   ==> (&1 - p) * exp(--p * u) + p * exp((&1 - p) * u) =
       exp(--p * u + log(&1 - p + p * exp u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - p + p * exp u` ASSUME_TAC THENL
  [MATCH_MP_TAC HOEFFDING_DENOM_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Replace exp((1-p)*u) with exp(-pu)*exp(u) *)
  SUBGOAL_THEN `exp((&1 - p) * u) = exp(--p * u) * exp(u:real)` SUBST1_TAC THENL
  [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN
  (* Goal: (1-p)*exp(-pu) + p*(exp(-pu)*exp(u)) = exp(-pu) * (1-p + p*exp u) *)
  (* Generalize over exp terms to get a pure polynomial identity *)
  SPEC_TAC (`exp(u:real)`, `f:real`) THEN
  SPEC_TAC (`exp(--p * u)`, `e:real`) THEN
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

(* Analytic inequality: the convexity bound is <= exp(s^2(b-a)^2/8).
   This is the core analytic content of Hoeffding's lemma.
   Requires a <= 0 and 0 <= b (which hold when E[X]=0 and a <= X <= b). *)
let HOEFFDING_ANALYTIC_LEMMA = prove
 (`!a b s:real. a <= &0 /\ &0 <= b /\ a < b
     ==> b / (b - a) * exp(s * a) + (--a) / (b - a) * exp(s * b) <=
         exp(s pow 2 * (b - a) pow 2 / &8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Abbreviate p = (-a)/(b-a), then b/(b-a) = 1-p *)
  SUBGOAL_THEN `b / (b - a) = &1 - (--a) / (b - a):real` SUBST1_TAC THENL
  [UNDISCH_TAC `~(b - a = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `p = (--a) / (b - a):real` THEN
  SUBGOAL_THEN `&0 <= p` ASSUME_TAC THENL
  [EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `p <= &1` ASSUME_TAC THENL
  [EXPAND_TAC "p" THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Rewrite exp arguments: s*a = -p*(s*(b-a)), s*b = (1-p)*(s*(b-a)) *)
  SUBGOAL_THEN `s * a = --p * (s * (b - a)):real` SUBST1_TAC THENL
  [EXPAND_TAC "p" THEN
   UNDISCH_TAC `~(b - a = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `s * b = (&1 - p) * (s * (b - a)):real` SUBST1_TAC THENL
  [EXPAND_TAC "p" THEN
   UNDISCH_TAC `~(b - a = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  (* Apply HOEFFDING_EXP_L_EQ to transform LHS to exp form *)
  MP_TAC (ISPECL [`p:real`; `s * (b - a):real`] HOEFFDING_EXP_L_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  (* Reduce exp(A) <= exp(B) to A <= B *)
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  (* Use HOEFFDING_L_TAYLOR_BOUND with t = s*(b-a), then equate (s*(b-a))^2/8 = s^2*(b-a)^2/8 *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(s * (b - a)) pow 2 / &8` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC HOEFFDING_L_TAYLOR_BOUND THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC REAL_EQ_IMP_LE THEN
   REWRITE_TAC[REAL_POW_MUL; real_div; REAL_MUL_ASSOC]]);;

(* MGF convexity bound: E[exp(sX)] <= b/(b-a)*exp(sa) + (-a)/(b-a)*exp(sb) *)
let SIMPLE_MGF_CONVEX_BOUND = prove
 (`!p:A prob_space (X:A->real) a b s.
     simple_rv p X /\
     simple_expectation p X = &0 /\
     (!x. x IN prob_carrier p ==> a <= X x /\ X x <= b) /\
     a < b
     ==> simple_mgf p X s <=
         b / (b - a) * exp(s * a) + (--a) / (b - a) * exp(s * b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[simple_mgf] THEN
  ABBREV_TAC `c = (b * exp(s * a) - a * exp(s * b)) / (b - a)` THEN
  ABBREV_TAC `d = (exp(s * b) - exp(s * a)) / (b - a)` THEN
  (* Step 1: E[exp(sX)] <= E[c + d*X] by monotonicity + convexity *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space) (\x:A. c + d * (X:A->real) x)` THEN
  CONJ_TAC THENL
  [(* Monotonicity: exp(s*X(x)) <= c + d*X(x) pointwise *)
   MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_EXP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ADD THEN
    REWRITE_TAC[SIMPLE_RV_CONST] THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   X_GEN_TAC `y:A` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(b - (X:A->real) y) / (b - a) * exp(s * a) +
               (X y - a) / (b - a) * exp(s * b)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_BOUND_EXP THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    EXPAND_TAC "c" THEN EXPAND_TAC "d" THEN
    UNDISCH_TAC `~(b - a = &0)` THEN CONV_TAC REAL_FIELD];
   ALL_TAC] THEN
  (* Step 2: E[c + d*X] = c + d*E[X] = c = b/(b-a)*exp(sa) + (-a)/(b-a)*exp(sb) *)
  MP_TAC (ISPECL [`p:A prob_space`; `\x:A. (c:real)`; `\x:A. d * (X:A->real) x`]
    SIMPLE_EXPECTATION_ADD) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[SIMPLE_RV_CONST];
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SIMPLE_EXPECTATION_CONST] THEN
  MP_TAC (ISPECL [`p:A prob_space`; `X:A->real`; `d:real`]
    SIMPLE_EXPECTATION_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  EXPAND_TAC "c" THEN
  UNDISCH_TAC `~(b - a = &0)` THEN CONV_TAC REAL_FIELD);;

(* Hoeffding's lemma: E[exp(sX)] <= exp(s^2(b-a)^2/8) when
   E[X] = 0 and a <= X <= b almost surely *)
let HOEFFDING_LEMMA = prove
 (`!p:A prob_space (X:A->real) a b s.
     simple_rv p X /\
     simple_expectation p X = &0 /\
     (!x. x IN prob_carrier p ==> a <= X x /\ X x <= b) /\
     a < b
     ==> simple_mgf p X s <= exp(s pow 2 * (b - a) pow 2 / &8)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `b / (b - a) * exp(s * a) + (--a) / (b - a) * exp(s * b)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_MGF_CONVEX_BOUND THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[];
   MATCH_MP_TAC HOEFFDING_ANALYTIC_LEMMA THEN ASM_REWRITE_TAC[] THEN
   (* Need a <= &0 /\ &0 <= b from E[X]=0 and a <= X <= b *)
   CONJ_TAC THENL
   [(* a <= &0: from E[const a] <= E[X] = 0 *)
    SUBGOAL_THEN `simple_expectation (p:A prob_space) (\x:A. a:real) <=
                  simple_expectation p (X:A->real)` MP_TAC THENL
    [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
     ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN ASM_MESON_TAC[];
     ASM_REWRITE_TAC[SIMPLE_EXPECTATION_CONST]];
    (* &0 <= b: from 0 = E[X] <= E[const b] = b *)
    SUBGOAL_THEN `simple_expectation (p:A prob_space) (X:A->real) <=
                  simple_expectation p (\x:A. b:real)` MP_TAC THENL
    [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
     ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN
     GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN ASM_MESON_TAC[];
     ASM_REWRITE_TAC[SIMPLE_EXPECTATION_CONST]]]]);;


(* Hoeffding's inequality for a single bounded, mean-zero RV *)
let HOEFFDING_SINGLE = prove
 (`!p:A prob_space (X:A->real) a b t.
     simple_rv p X /\
     simple_expectation p X = &0 /\
     (!x. x IN prob_carrier p ==> a <= X x /\ X x <= b) /\
     a < b /\ &0 < t
     ==> prob p {x | x IN prob_carrier p /\ X x >= t} <=
         exp(--(&2 * t pow 2 / (b - a) pow 2))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = &4 * t / (b - a) pow 2` THEN
  SUBGOAL_THEN `&0 < (b - a) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((b - a) pow 2 = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
  [EXPAND_TAC "s" THEN
   MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 1: Chernoff bound *)
  SUBGOAL_THEN
    `prob (p:A prob_space) {x | x IN prob_carrier p /\ (X:A->real) x >= t} <=
     exp(--(s * t)) * simple_mgf p X s`
    (LABEL_TAC "H1") THENL
  [MATCH_MP_TAC CHERNOFF_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 2: Hoeffding's lemma *)
  SUBGOAL_THEN
    `simple_mgf (p:A prob_space) (X:A->real) s <=
     exp(s pow 2 * (b - a) pow 2 / &8)`
    (LABEL_TAC "H2") THENL
  [MATCH_MP_TAC HOEFFDING_LEMMA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 3: Multiply Hoeffding bound by exp(-st) *)
  SUBGOAL_THEN
    `exp(--(s * t)) * simple_mgf (p:A prob_space) (X:A->real) s <=
     exp(--(s * t)) * exp(s pow 2 * (b - a) pow 2 / &8)`
    (LABEL_TAC "H3") THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
    ASM_MESON_TAC[]];
   ALL_TAC] THEN
  (* Step 4: Chain: P(X>=t) <= exp(-st)*exp(s^2(b-a)^2/8) *)
  SUBGOAL_THEN
    `prob (p:A prob_space) {x | x IN prob_carrier p /\ (X:A->real) x >= t} <=
     exp(--(s * t)) * exp(s pow 2 * (b - a) pow 2 / &8)`
    (LABEL_TAC "H4") THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `exp(--(s * t)) * simple_mgf (p:A prob_space) (X:A->real) s` THEN
   CONJ_TAC THENL
   [USE_THEN "H1" ACCEPT_TAC; USE_THEN "H3" ACCEPT_TAC];
   ALL_TAC] THEN
  (* Step 5: exp(-st)*exp(s^2(b-a)^2/8) = exp(-st + s^2(b-a)^2/8) *)
  SUBGOAL_THEN
    `exp(--(s * t)) * exp(s pow 2 * (b - a) pow 2 / &8) =
     exp(--(s * t) + s pow 2 * (b - a) pow 2 / &8)`
    (LABEL_TAC "H5") THENL
  [REWRITE_TAC[REAL_EXP_ADD]; ALL_TAC] THEN
  (* Step 6: -st + s^2(b-a)^2/8 = -2t^2/(b-a)^2 when s = 4t/(b-a)^2 *)
  SUBGOAL_THEN
    `--(s * t) + s pow 2 * (b - a) pow 2 / &8 =
     --(&2 * t pow 2 / (b - a) pow 2)`
    (LABEL_TAC "H6") THENL
  [EXPAND_TAC "s" THEN
   UNDISCH_TAC `&0 < (b - a) pow 2` THEN
   UNDISCH_TAC `&0 < t` THEN
   CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(s * t)) * exp(s pow 2 * (b - a) pow 2 / &8)` THEN
  CONJ_TAC THENL
  [USE_THEN "H4" ACCEPT_TAC;
   USE_THEN "H5" (fun th -> REWRITE_TAC[th]) THEN
   USE_THEN "H6" (fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[REAL_LE_REFL]]);;

(* MGF of a sum of two independent RVs = product of MGFs *)
let SIMPLE_MGF_ADD_INDEP = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) s.
     simple_rv p X /\ simple_rv p Y /\ indep_rv p X Y
     ==> simple_mgf p (\x. X x + Y x) s = simple_mgf p X s * simple_mgf p Y s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[simple_mgf] THEN
  SUBGOAL_THEN
    `(\x:A. exp(s * ((X:A->real) x + (Y:A->real) x))) =
     (\x. exp(s * X x) * exp(s * Y x))` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_EXP_ADD]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `X:A->real`; `Y:A->real`;
    `\u:real. exp(s * u)`; `\v:real. exp(s * v)`]
    SIMPLE_EXPECTATION_PRODUCT_COMPOSE_INDEP)) THEN
  ASM_REWRITE_TAC[]);;

(* Hoeffding MGF bound for sums of independent mean-zero bounded RVs *)
let HOEFFDING_MGF_SUM_BOUND = prove
 (`!p:A prob_space (X:num->A->real) (a:num->real) (b:num->real) s n.
     (!i. i <= n ==> simple_rv p (X i)) /\
     (!i. i <= n ==> simple_expectation p (X i) = &0) /\
     (!i. i <= n ==> !x. x IN prob_carrier p ==> a i <= X i x /\ X i x <= b i) /\
     (!i. i <= n ==> a i < b i) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
     ==> simple_mgf p (\x. sum(0..n) (\i. X i x)) s <=
         exp(s pow 2 * sum(0..n) (\i. (b i - a i) pow 2) / &8)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   STRIP_TAC THEN
   REWRITE_TAC[SUM_SING_NUMSEG] THEN BETA_TAC THEN
   REWRITE_TAC[ETA_AX] THEN
   MATCH_MP_TAC HOEFFDING_LEMMA THEN
   ASM_MESON_TAC[LE_REFL];
   ALL_TAC] THEN
  (* Inductive step *)
  STRIP_TAC THEN
  (* First establish the IH hypotheses hold for n *)
  SUBGOAL_THEN
    `simple_mgf (p:A prob_space) (\x. sum(0..n) (\i. (X:num->A->real) i x)) s <=
     exp(s pow 2 * sum(0..n) (\i. ((b:num->real) i - (a:num->real) i) pow 2) / &8)`
    (LABEL_TAC "IH") THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  (* Hoeffding lemma for X (SUC n) *)
  SUBGOAL_THEN
    `simple_mgf (p:A prob_space) ((X:num->A->real) (SUC n)) s <=
     exp(s pow 2 * ((b:num->real) (SUC n) - (a:num->real) (SUC n)) pow 2 / &8)`
    (LABEL_TAC "HL") THENL
  [MATCH_MP_TAC HOEFFDING_LEMMA THEN
   ASM_MESON_TAC[LE_REFL];
   ALL_TAC] THEN
  (* Rewrite sum(0..SUC n) = sum(0..n) + X(SUC n) *)
  SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  (* MGF factorization via independence *)
  SUBGOAL_THEN
    `simple_mgf (p:A prob_space) (\x:A. sum (0..n) (\i. (X:num->A->real) i x) + X (SUC n) x) s =
     simple_mgf p (\x. sum(0..n) (\i. X i x)) s * simple_mgf p (X (SUC n)) s`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_MGF_ADD_INDEP THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`];
    ALL_TAC] THEN
   CONJ_TAC THENL [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
   ASM_SIMP_TAC[ARITH_RULE `n < SUC n`];
   ALL_TAC] THEN
  (* Now bound product of MGFs by product of exp bounds *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(s pow 2 * sum(0..n) (\i. ((b:num->real) i - (a:num->real) i) pow 2) / &8) *
              exp(s pow 2 * ((b:num->real) (SUC n) - (a:num->real) (SUC n)) pow 2 / &8)` THEN
  CONJ_TAC THENL
  [(* Product of MGFs <= product of exp bounds *)
   MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_MGF_NONNEG THEN
    MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`];
    USE_THEN "IH" ACCEPT_TAC;
    MATCH_MP_TAC SIMPLE_MGF_NONNEG THEN ASM_SIMP_TAC[LE_REFL];
    USE_THEN "HL" ACCEPT_TAC];
   ALL_TAC] THEN
  (* exp(A) * exp(B) = exp(A + B), and A+B = the full sum *)
  REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
  SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_ADD_RDISTRIB] THEN
  REAL_ARITH_TAC);;

(* Hoeffding's inequality for sums of independent bounded mean-zero RVs *)
let HOEFFDING_SUM = prove
 (`!p:A prob_space (X:num->A->real) (a:num->real) (b:num->real) t n.
     (!i. i <= n ==> simple_rv p (X i)) /\
     (!i. i <= n ==> simple_expectation p (X i) = &0) /\
     (!i. i <= n ==> !x. x IN prob_carrier p ==> a i <= X i x /\ X i x <= b i) /\
     (!i. i <= n ==> a i < b i) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k))) /\
     &0 < t /\ &0 < sum(0..n) (\i. (b i - a i) pow 2)
     ==> prob p {x | x IN prob_carrier p /\ sum(0..n) (\i. X i x) >= t} <=
         exp(--(&2 * t pow 2 / sum(0..n) (\i. (b i - a i) pow 2)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `V = sum(0..n) (\i. ((b:num->real) i - (a:num->real) i) pow 2)` THEN
  ABBREV_TAC `s = &4 * t / V` THEN
  SUBGOAL_THEN `~(V = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
  [EXPAND_TAC "s" THEN
   MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 1: Chernoff bound *)
  SUBGOAL_THEN
    `prob (p:A prob_space) {x | x IN prob_carrier p /\ sum(0..n) (\i. (X:num->A->real) i x) >= t} <=
     exp(--(s * t)) * simple_mgf p (\x. sum(0..n) (\i. X i x)) s`
    (LABEL_TAC "CH") THENL
  [MATCH_MP_TAC CHERNOFF_BOUND THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: Hoeffding MGF bound *)
  SUBGOAL_THEN
    `simple_mgf (p:A prob_space) (\x. sum(0..n) (\i. (X:num->A->real) i x)) s <=
     exp(s pow 2 * V / &8)`
    (LABEL_TAC "HB") THENL
  [EXPAND_TAC "V" THEN MATCH_MP_TAC HOEFFDING_MGF_SUM_BOUND THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Combine: P <= exp(-st) * exp(s^2 V/8) *)
  SUBGOAL_THEN
    `prob (p:A prob_space) {x | x IN prob_carrier p /\ sum(0..n) (\i. (X:num->A->real) i x) >= t} <=
     exp(--(s * t)) * exp(s pow 2 * V / &8)`
    (LABEL_TAC "COMB") THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `exp(--(s * t)) * simple_mgf (p:A prob_space) (\x. sum(0..n) (\i. (X:num->A->real) i x)) s` THEN
   CONJ_TAC THENL
   [USE_THEN "CH" ACCEPT_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
     USE_THEN "HB" ACCEPT_TAC]];
   ALL_TAC] THEN
  (* Step 4: exp(-st) * exp(s^2V/8) = exp(-st + s^2V/8) = exp(-2t^2/V) *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(s * t)) * exp(s pow 2 * V / &8)` THEN
  CONJ_TAC THENL
  [USE_THEN "COMB" ACCEPT_TAC;
   REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
   MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
   UNDISCH_TAC `&0 < V` THEN
   UNDISCH_TAC `&0 < t` THEN
   EXPAND_TAC "s" THEN EXPAND_TAC "V" THEN
   CONV_TAC REAL_FIELD]);;

(* Adding constants preserves independence *)
let INDEP_RV_ADD_CONST = prove
 (`!p:A prob_space (X:A->real) (Y:A->real) c d.
     indep_rv p X Y
     ==> indep_rv p (\x. X x + c) (\x. Y x + d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[indep_rv] THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (\x:A. (X:A->real) x + c)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `(\x:A. c:real)`]
     RANDOM_VARIABLE_ADD) THEN BETA_TAC THEN
   ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable (p:A prob_space) (\x:A. (Y:A->real) x + d)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `(\x:A. d:real)`]
     RANDOM_VARIABLE_ADD) THEN BETA_TAC THEN
   ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x + c <= a /\ Y x + d <= b} =
     {x | x IN prob_carrier p /\ X x <= a - c /\ Y x <= b - d}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ X x + c <= a} =
     {x | x IN prob_carrier p /\ X x <= a - c}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ Y x + d <= b} =
     {x | x IN prob_carrier p /\ Y x <= b - d}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
   EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Hoeffding's inequality for sums with general means *)
let HOEFFDING_SUM_GENERAL = prove
 (`!p:A prob_space (X:num->A->real) (a:num->real) (b:num->real) t n.
     (!i. i <= n ==> simple_rv p (X i)) /\
     (!i. i <= n ==> !x. x IN prob_carrier p ==> a i <= X i x /\ X i x <= b i) /\
     (!i. i <= n ==> a i < b i) /\
     (!k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k))) /\
     &0 < t /\ &0 < sum(0..n) (\i. (b i - a i) pow 2)
     ==> prob p {x | x IN prob_carrier p /\
           sum(0..n) (\i. X i x) - sum(0..n) (\i. simple_expectation p (X i)) >= t} <=
         exp(--(&2 * t pow 2 / sum(0..n) (\i. (b i - a i) pow 2)))`,
  REPEAT STRIP_TAC THEN
  (* Rewrite: sum X - sum E[X] = sum (X - E[X]) *)
  SUBGOAL_THEN
    `!x:A. sum(0..n) (\i. (X:num->A->real) i x) -
           sum(0..n) (\i. simple_expectation p (X i)) =
           sum(0..n) (\i. X i x - simple_expectation p (X i))`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REWRITE_TAC[GSYM SUM_SUB_NUMSEG]; ALL_TAC] THEN
  (* Apply HOEFFDING_SUM to the centered variables via MP_TAC *)
  MP_TAC(ISPECL [
    `p:A prob_space`;
    `\i:num. \x:A. (X:num->A->real) i x - simple_expectation p (X i)`;
    `\i:num. (a:num->real) i - simple_expectation p ((X:num->A->real) i)`;
    `\i:num. (b:num->real) i - simple_expectation p ((X:num->A->real) i)`;
    `t:real`; `n:num`
  ] HOEFFDING_SUM) THEN
  BETA_TAC THEN
  (* Simplify (b - E[X]) - (a - E[X]) = b - a *)
  SUBGOAL_THEN
    `!i:num. ((b:num->real) i - simple_expectation p ((X:num->A->real) i)) -
             ((a:num->real) i - simple_expectation p (X i)) = b i - a i`
    (fun th -> REWRITE_TAC[th]) THENL
  [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
  [(* Branch 1: simple_rv of centered variables *)
   GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC SIMPLE_RV_SUB THEN
   REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SIMPLE_RV_CONST];
   (* Branch 2: E[X_i - E[X_i]] = 0 *)
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space) ((X:num->A->real) i)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) i`;
     `(\x:A. simple_expectation p ((X:num->A->real) i))`]
     SIMPLE_EXPECTATION_SUB) THEN
   BETA_TAC THEN ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST] THEN REAL_ARITH_TAC;
   (* Branch 3: bounds *)
   GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `(a:num->real) i <= (X:num->A->real) i x /\ X i x <= (b:num->real) i`
     MP_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
   (* Branch 4: a' < b' *)
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `(a:num->real) i < (b:num->real) i` MP_TAC THENL
   [ASM_MESON_TAC[]; REAL_ARITH_TAC];
   (* Branch 5: independence *)
   GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `(\x:A. sum(0..k) (\i. (X:num->A->real) i x -
         simple_expectation p (X i))) =
      (\x. sum(0..k) (\i. X i x) +
           --sum(0..k) (\i. simple_expectation p (X i)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[SUM_SUB_NUMSEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `(\x:A. (X:num->A->real) (SUC k) x -
         simple_expectation p (X (SUC k))) =
      (\x. X (SUC k) x + --simple_expectation p (X (SUC k)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC INDEP_RV_ADD_CONST THEN
   REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
   (* Branch 6: &0 < t *)
   ASM_REWRITE_TAC[];
   (* Branch 7: &0 < sum (b - a)^2 *)
   ASM_REWRITE_TAC[]])

(* ========================================================================= *)
(* AZUMA-HOEFFDING INEQUALITY                                                *)
(* ========================================================================= *)

(* Helper: strict inequality level set is in sub-sigma-algebra *)
let MEASURABLE_WRT_STRICT_LT = prove
 (`!p:A prob_space G (X:A->real) v.
     sub_sigma_algebra p G /\ measurable_wrt p G X
     ==> {x | x IN prob_carrier p /\ X x < v} IN G`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ISPECL [`X:A->real`; `v:real`; `prob_carrier (p:A prob_space)`]
    OPEN_HALFLINE_AS_UNION] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIV] THEN
   X_GEN_TAC `s:A->bool` THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
   ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `measurable_wrt (p:A prob_space) G X` THEN
   REWRITE_TAC[measurable_wrt] THEN
   DISCH_THEN(MP_TAC o SPEC `v - inv(&n + &1)`) THEN
   MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[EXTENSION; IN_ELIM_THM];
   REWRITE_TAC[SIMPLE_IMAGE] THEN
   MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]]);;

(* Level sets of G-measurable functions are in G *)
let MEASURABLE_WRT_LEVEL_SET = prove
 (`!p:A prob_space G (X:A->real) v.
     sub_sigma_algebra p G /\ measurable_wrt p G X
     ==> {x | x IN prob_carrier p /\ X x = v} IN G`,
  REPEAT STRIP_TAC THEN
  (* {X = v} = {X <= v} DIFF {X < v} *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (X:A->real) x = v} =
     {x | x IN prob_carrier p /\ X x <= v} DIFF
     {x | x IN prob_carrier p /\ X x < v}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
   X_GEN_TAC `y:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((X:A->real) y < v)` MP_TAC THENL
    [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `p:A prob_space` SUB_SIGMA_ALGEBRA_DIFF) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[measurable_wrt];
   MATCH_MP_TAC MEASURABLE_WRT_STRICT_LT THEN ASM_REWRITE_TAC[]]);;

(* Martingale difference has zero expectation on any F_n-event *)
let MARTINGALE_DIFF_INDICATOR_ZERO = prove
 (`!p:A prob_space FF (X:num->A->real) n (B:A->bool).
     martingale p FF X /\ B IN FF n
     ==> simple_expectation p
           (\x. (X (SUC n) x - X n x) * indicator_fn B x) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(B:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[martingale; filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x:A. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (B:A->bool) x) =
     (\x. X (SUC n) x * indicator_fn B x - X n x * indicator_fn B x)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_rv p (\x:A. (X:num->A->real) (SUC n) x * indicator_fn (B:A->bool) x) /\
     simple_rv p (\x. X n x * indicator_fn B x)`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC[martingale];
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [ASM_MESON_TAC[martingale];
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]]];
   ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a - b = &0`) THEN
  ASM_MESON_TAC[martingale]);;

(* Composition of measurable simple RV with any function is measurable *)
let MEASURABLE_WRT_COMPOSE = prove
 (`!p:A prob_space G (Y:A->real) (f:real->real).
     sub_sigma_algebra p G /\ simple_rv p Y /\ measurable_wrt p G Y
     ==> measurable_wrt p G (\x. f(Y x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN
  ABBREV_TAC `R = IMAGE (Y:A->real) (prob_carrier p)` THEN
  SUBGOAL_THEN `FINITE (R:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  (* {f(Y) <= v} = UNIONS of level sets {Y = u} for u with f(u) <= v *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ f((Y:A->real) x) <= v} =
     UNIONS (IMAGE (\u. {x | x IN prob_carrier p /\ Y x = u})
                   {u:real | u IN R /\ (f:real->real) u <= v})`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `(Y:A->real) x` THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
   X_GEN_TAC `u:real` THEN STRIP_TAC THEN
   MATCH_MP_TAC(ISPEC `p:A prob_space` MEASURABLE_WRT_LEVEL_SET) THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC COUNTABLE_IMAGE THEN MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
   MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `R:real->bool` THEN
   ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* Conditional convex MGF bound for martingale differences on an event *)
(* For A in FF_n: E[exp(s*D) * 1_A] <= (b/(b-a)*exp(sa) + (-a)/(b-a)*exp(sb))*P(A) *)
let MARTINGALE_DIFF_CONVEX_INDICATOR = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real)
     (n:num) (s:real) (a:real) (b:real) (A:A->bool).
     martingale p FF X /\
     A IN FF n /\
     (!x. x IN prob_carrier p ==>
        a <= X (SUC n) x - X n x /\ X (SUC n) x - X n x <= b) /\
     a < b
     ==> simple_expectation p
           (\x. exp(s * (X (SUC n) x - X n x)) * indicator_fn A x) <=
         (b / (b - a) * exp(s * a) + --a / (b - a) * exp(s * b)) *
         prob p A`,
  REPEAT STRIP_TAC THEN
  (* Prerequisites *)
  SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[martingale; filtration; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (\x:A. (X:num->A->real) (SUC n) x - X n x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
   ASM_MESON_TAC[martingale]; ALL_TAC] THEN
  SUBGOAL_THEN `~(b - a = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Step 1: Pointwise bound via monotonicity *)
  (* exp(s*D(x))*1_A(x) <= (C + beta*D(x))*1_A(x) where C = b/(b-a)*exp(sa)+(-a)/(b-a)*exp(sb) *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `simple_expectation (p:A prob_space)
      (\x:A. ((b / (b - a) * exp(s * a) + --a / (b - a) * exp(s * b)) +
               (exp(s * b) - exp(s * a)) / (b - a) *
               ((X:num->A->real) (SUC n) x - X n x)) *
              indicator_fn (A:A->bool) x)` THEN
  CONJ_TAC THENL
  [(* Monotonicity: pointwise exp(s*D(x)) <= C + beta*D(x) then multiply by 1_A >= 0 *)
   MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_EXP THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[SIMPLE_RV_CONST];
      MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]];
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(b - ((X:num->A->real) (SUC n) x - X n x)) / (b - a) *
                exp(s * a) +
                ((X (SUC n) x - X n x) - a) / (b - a) * exp(s * b)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC CONVEX_BOUND_EXP THEN
     CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_EQ_IMP_LE THEN
     UNDISCH_TAC `~(b - a = &0)` THEN CONV_TAC REAL_FIELD];
    REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Step 2: E[(C + beta*D)*1_A] = C*P(A) + beta*E[D*1_A] *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\x:A. ((b / (b - a) * exp(s * a) + --a / (b - a) * exp(s * b)) +
               (exp(s * b) - exp(s * a)) / (b - a) *
               ((X:num->A->real) (SUC n) x - X n x)) *
              indicator_fn (A:A->bool) x) =
     (b / (b - a) * exp(s * a) + --a / (b - a) * exp(s * b)) * prob p A +
     (exp(s * b) - exp(s * a)) / (b - a) *
       simple_expectation p (\x. (X (SUC n) x - X n x) * indicator_fn A x)`
    SUBST1_TAC THENL
  [(* Distribute: (C + beta*D)*1_A = C*1_A + beta*(D*1_A) *)
   SUBGOAL_THEN
     `(\x:A. ((b / (b - a) * exp(s * a) + --a / (b - a) * exp(s * b)) +
              (exp(s * b) - exp(s * a)) / (b - a) *
              ((X:num->A->real) (SUC n) x - X n x)) *
             indicator_fn (A:A->bool) x) =
      (\x. (b / (b - a) * exp(s * a) + --a / (b - a) * exp(s * b)) *
           indicator_fn A x +
           (exp(s * b) - exp(s * a)) / (b - a) *
           ((X (SUC n) x - X n x) * indicator_fn A x))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* Apply SIMPLE_EXPECTATION_ADD *)
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. (b / (b - a) * exp(s * a) + --a / (b - a) * exp(s * b)) *
            indicator_fn (A:A->bool) x`;
     `\x:A. (exp(s * b) - exp(s * a)) / (b - a) *
            (((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x)`]
     SIMPLE_EXPECTATION_ADD) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_CMUL THEN REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIMPLE_RV_CMUL THEN REWRITE_TAC[ETA_AX] THEN
     MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
   BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
   (* E[C*1_A] = C*P(A) *)
   MP_TAC(ISPECL [`p:A prob_space`; `indicator_fn (A:A->bool)`;
     `b / (b - a) * exp(s * a) + --a / (b - a) * exp(s * b)`]
     SIMPLE_EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_INDICATOR] THEN
   (* E[beta*(D*1_A)] = beta*E[D*1_A] *)
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. ((X:num->A->real) (SUC n) x - X n x) * indicator_fn (A:A->bool) x`;
     `(exp(s * b) - exp(s * a)) / (b - a)`]
     SIMPLE_EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: E[D*1_A] = 0 from MARTINGALE_DIFF_INDICATOR_ZERO *)
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
    `X:num->A->real`; `n:num`; `A:A->bool`]
    MARTINGALE_DIFF_INDICATOR_ZERO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* Conditional Hoeffding bound: combines convex bound with analytic lemma *)
let MARTINGALE_DIFF_EXP_INDICATOR_BOUND = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real)
     (n:num) (s:real) (a:real) (b:real) (A:A->bool).
     martingale p FF X /\
     A IN FF n /\
     (!x. x IN prob_carrier p ==>
        a <= X (SUC n) x - X n x /\ X (SUC n) x - X n x <= b) /\
     a < b
     ==> simple_expectation p
           (\x. exp(s * (X (SUC n) x - X n x)) * indicator_fn A x) <=
         exp(s pow 2 * (b - a) pow 2 / &8) * prob p A`,
  REPEAT STRIP_TAC THEN
  (* Show a <= 0 /\ 0 <= b from E[D] = 0 *)
  SUBGOAL_THEN `a <= &0 /\ &0 <= b` STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `simple_rv p (\x:A. (X:num->A->real) (SUC n) x - X n x)`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
    ASM_MESON_TAC[martingale]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_expectation p (\x:A. (X:num->A->real) (SUC n) x - X n x) = &0`
     ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) (SUC n)`;
      `(X:num->A->real) n`] SIMPLE_EXPECTATION_SUB) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
      `X:num->A->real`] MARTINGALE_EXPECTATION_CONST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      SUBST1_TAC(SPEC `SUC n` th) THEN SUBST1_TAC(SPEC `n:num` th)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `a <= simple_expectation p
      (\x:A. (X:num->A->real) (SUC n) x - X n x)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `simple_expectation (p:A prob_space) (\x:A. a)` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[SIMPLE_EXPECTATION_CONST; REAL_LE_REFL]; ALL_TAC] THEN
     MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
     ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     ASM_MESON_TAC[];
     ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `simple_expectation p
      (\x:A. (X:num->A->real) (SUC n) x - X n x) <= b` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `simple_expectation (p:A prob_space) (\x:A. b)` THEN
     CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SIMPLE_EXPECTATION_CONST; REAL_LE_REFL]] THEN
     MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
     ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN
     X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
     ASM_MESON_TAC[];
     ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Chain: E[exp(s*D)*1_A] <= C*P(A) <= exp(...)*P(A) *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(b / (b - a) * exp(s * a) + --a / (b - a) * exp(s * b)) *
              prob p (A:A->bool)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC MARTINGALE_DIFF_CONVEX_INDICATOR THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC HOEFFDING_ANALYTIC_LEMMA THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC PROB_POSITIVE THEN
   ASM_MESON_TAC[martingale; filtration; sub_sigma_algebra; SUBSET]]);;

(* Subtraction preserves measurability for simple RVs *)
let MEASURABLE_WRT_SUB = prove
 (`!p:A prob_space G (Y1:A->real) (Y2:A->real).
     sub_sigma_algebra p G /\
     simple_rv p Y1 /\ measurable_wrt p G Y1 /\
     simple_rv p Y2 /\ measurable_wrt p G Y2
     ==> measurable_wrt p G (\x. Y1 x - Y2 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN
  ABBREV_TAC `R2 = IMAGE (Y2:A->real) (prob_carrier p)` THEN
  SUBGOAL_THEN `FINITE (R2:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "R2" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  (* {Y1 - Y2 <= v} = UNIONS_{u in R2} ({Y2 = u} INTER {Y1 <= v + u}) *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (Y1:A->real) x - Y2 x <= v} =
     UNIONS (IMAGE (\u. {x | x IN prob_carrier p /\ Y2 x = u} INTER
                        {x | x IN prob_carrier p /\ Y1 x <= v + u})
                   R2)`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `(Y2:A->real) x` THEN
    CONJ_TAC THENL
    [EXPAND_TAC "R2" THEN REWRITE_TAC[IN_IMAGE] THEN
     EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
   X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   MATCH_MP_TAC(ISPEC `p:A prob_space` SUB_SIGMA_ALGEBRA_INTER) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `p:A prob_space` MEASURABLE_WRT_LEVEL_SET) THEN
    ASM_REWRITE_TAC[];
    ACCEPT_TAC(SPEC `v + u:real` (REWRITE_RULE[measurable_wrt]
      (ASSUME `measurable_wrt (p:A prob_space) G (Y1:A->real)`)))];
   MATCH_MP_TAC COUNTABLE_IMAGE THEN MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
   ASM_REWRITE_TAC[]]);;

(* Step lemma for Azuma: E[Z * exp(s*D)] <= exp(s^2*c^2/8) * E[Z] *)
(* for F_n-measurable non-negative simple Z *)
let MARTINGALE_DIFF_EXP_ADAPTED_BOUND = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real)
     (n:num) (s:real) (a:real) (b:real) (Z:A->real).
     martingale p FF X /\
     simple_rv p Z /\ measurable_wrt p (FF n) Z /\
     (!x. x IN prob_carrier p ==> &0 <= Z x) /\
     (!x. x IN prob_carrier p ==>
        a <= X (SUC n) x - X n x /\ X (SUC n) x - X n x <= b) /\
     a < b
     ==> simple_expectation p
           (\x. Z x * exp(s * (X (SUC n) x - X n x))) <=
         exp(s pow 2 * (b - a) pow 2 / &8) * simple_expectation p Z`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (Z:A->real) (prob_carrier p)` THEN
  SUBGOAL_THEN `FINITE (S:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "S" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[martingale; filtration]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!u:real. {x:A | x IN prob_carrier p /\ (Z:A->real) x = u} IN (FF:num->(A->bool)->bool) (n:num)`
    ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC(ISPEC `p:A prob_space` MEASURABLE_WRT_LEVEL_SET) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!u:real. u IN S ==> &0 <= u` ASSUME_TAC THENL
  [EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE] THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* simple_rv for exp(s*D) *)
  SUBGOAL_THEN `simple_rv p (\x:A. exp(s * ((X:num->A->real) (SUC n) x - X n x)))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_EXP THEN
   MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
   ASM_MESON_TAC[martingale]; ALL_TAC] THEN
  (* Step 1: Pointwise decomposition Z * exp(s*D) = sum_v v * 1_{Z=v} * exp(s*D) *)
  SUBGOAL_THEN
    `!x:A. x IN prob_carrier p ==>
       (Z:A->real) x * exp(s * ((X:num->A->real) (SUC n) x - X n x)) =
       sum S (\u. u * (exp(s * (X (SUC n) x - X n x)) *
         indicator_fn {z | z IN prob_carrier p /\ Z z = u} x))`
    ASSUME_TAC THENL
  [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `Z:A->real`; `\v:real. v`; `w:A`]
     SIMPLE_RV_COMPOSE_SUM_INDICATOR)) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
   REWRITE_TAC[GSYM SUM_RMUL] THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN REWRITE_TAC[REAL_MUL_AC];
   ALL_TAC] THEN
  (* Step 2: E[Z * exp(s*D)] = sum_v (v * E[exp(s*D) * 1_{Z=v}]) *)
  SUBGOAL_THEN
    `simple_expectation p (\x:A. (Z:A->real) x *
       exp(s * ((X:num->A->real) (SUC n) x - X n x))) =
     sum S (\u:real. u * simple_expectation p
       (\x. exp(s * (X (SUC n) x - X n x)) *
         indicator_fn {z | z IN prob_carrier p /\ Z z = u} x))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
    `simple_expectation p (\x:A. (Z:A->real) x *
       exp(s * ((X:num->A->real) (SUC n) x - X n x))) =
     simple_expectation p (\x. sum S (\u. u *
       (exp(s * (X (SUC n) x - X n x)) *
         indicator_fn {z | z IN prob_carrier p /\ Z z = u} x)))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
   (* Swap E and sum *)
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\u:real. \x:A. u *
        (exp(s * ((X:num->A->real) (SUC n) x - X n x)) *
          indicator_fn {z | z IN prob_carrier p /\ (Z:A->real) z = u} x)`;
      `S:real->bool`]
     SIMPLE_EXPECTATION_SUM_FINITE) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
     ASM_MESON_TAC[sub_sigma_algebra; SUBSET]];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN
   MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`;
     `\x:A. exp(s * ((X:num->A->real) (SUC n) x - X n x)) *
       indicator_fn {z | z IN prob_carrier p /\ (Z:A->real) z = u} x`;
     `u:real`] SIMPLE_EXPECTATION_CMUL)) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
     ASM_MESON_TAC[sub_sigma_algebra; SUBSET]];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Step 3: Similarly decompose E[Z] = sum_v (v * P({Z=v})) *)
  SUBGOAL_THEN
    `simple_expectation p (Z:A->real) =
     sum S (\u:real. u * prob p {z:A | z IN prob_carrier p /\ Z z = u})`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
    `simple_expectation p (Z:A->real) =
     simple_expectation p (\x. sum S (\u. u *
       indicator_fn {z | z IN prob_carrier p /\ Z z = u} x))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`p:A prob_space`; `Z:A->real`; `\v:real. v`; `w:A`]
      SIMPLE_RV_COMPOSE_SUM_INDICATOR)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   MP_TAC(ISPECL
     [`p:A prob_space`;
      `\u:real. \x:A. u *
        indicator_fn {z | z IN prob_carrier p /\ (Z:A->real) z = u} x`;
      `S:real->bool`]
     SIMPLE_EXPECTATION_SUM_FINITE) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    ASM_MESON_TAC[sub_sigma_algebra; SUBSET];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   BETA_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `indicator_fn {z:A | z IN prob_carrier p /\ (Z:A->real) z = u}`;
     `u:real`] SIMPLE_EXPECTATION_CMUL) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN
    ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN
   ASM_MESON_TAC[sub_sigma_algebra; SUBSET];
   ALL_TAC] THEN
  (* Step 4: SUM_LE: for each v, v*E[exp*1] <= v*exp(c)*P({Z=v}) *)
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `u:real` THEN DISCH_TAC THEN BETA_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2(CONJUNCT2 REAL_MUL_AC)] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
  [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MARTINGALE_DIFF_EXP_INDICATOR_BOUND THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Azuma MGF bound by induction *)
let AZUMA_MGF_BOUND = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real)
     (a:num->real) (b:num->real) (s:real) (n:num).
     martingale p FF X /\
     (!i. i <= n ==>
        !x. x IN prob_carrier p ==>
          a i <= X (SUC i) x - X i x /\ X (SUC i) x - X i x <= b i) /\
     (!i. i <= n ==> a i < b i)
     ==> simple_expectation p (\x. exp(s * (X (SUC n) x - X 0 x))) <=
         exp(s pow 2 * sum(0..n) (\i. (b i - a i) pow 2) / &8)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  GEN_TAC THEN INDUCT_TAC THENL
  [(* Base case: n = 0 *)
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[SUM_SING_NUMSEG] THEN BETA_TAC THEN
   REWRITE_TAC[simple_mgf] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\x:A. (X:num->A->real) (SUC 0) x - X 0 x`;
     `(a:num->real) 0`; `(b:num->real) 0`; `s:real`] HOEFFDING_LEMMA) THEN
   REWRITE_TAC[simple_mgf] THEN BETA_TAC THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
     ASM_MESON_TAC[martingale]; ALL_TAC] THEN
    CONJ_TAC THENL
    [(* E[X 1 - X 0] = 0 *)
     MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) (SUC 0)`;
       `(X:num->A->real) 0`] SIMPLE_EXPECTATION_SUB) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[martingale]; ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
       `X:num->A->real`] MARTINGALE_EXPECTATION_CONST) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN(fun th ->
       SUBST1_TAC(SPEC `SUC 0` th) THEN SUBST1_TAC(SPEC `0` th)) THEN
     REAL_ARITH_TAC;
     ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[LE_REFL]; ASM_MESON_TAC[LE_REFL]];
    ALL_TAC] THEN
   REWRITE_TAC[];
   (* Inductive step: n -> SUC n *)
   REPEAT STRIP_TAC THEN
   (* IH: E[exp(s*(X(SUC n) - X 0))] <= exp(s^2*sum(0..n)(...)/8) *)
   SUBGOAL_THEN
     `simple_expectation p (\x:A. exp(s * ((X:num->A->real) (SUC n) x - X 0 x))) <=
      exp(s pow 2 * sum(0..n) (\i. ((b:num->real) i - (a:num->real) i) pow 2) / &8)`
     (LABEL_TAC "IH") THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
   (* Write exp(s*(X(SUC(SUC n)) - X 0)) = exp(s*D) * exp(s*(X(SUC n) - X 0)) *)
   SUBGOAL_THEN
     `!x:A. x IN prob_carrier p ==>
       exp(s * ((X:num->A->real) (SUC(SUC n)) x - X 0 x)) =
       exp(s * (X (SUC n) x - X 0 x)) * exp(s * (X (SUC(SUC n)) x - X (SUC n) x))`
     ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* Z = exp(s*(X(SUC n) - X 0)) is simple_rv and FF(SUC n)-measurable *)
   ABBREV_TAC `Z = \x:A. exp(s * ((X:num->A->real) (SUC n) x - X 0 x))` THEN
   (* Extract needed facts from martingale via explicit CONJUNCT navigation *)
   (* martingale = A /\ (B /\ (C /\ D)) where A=filtration, B=simple_adapted,
      C=!n.simple_rv, D=conditional expectations *)
   SUBGOAL_THEN `!k:num. simple_rv p ((X:num->A->real) k)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)`) THEN
    REWRITE_TAC[martingale] THEN
    DISCH_THEN(fun th -> ACCEPT_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 th))));
    ALL_TAC] THEN
   SUBGOAL_THEN `sub_sigma_algebra (p:A prob_space) ((FF:num->(A->bool)->bool) (SUC n))` ASSUME_TAC THENL
   [MP_TAC(ASSUME `martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)`) THEN
    REWRITE_TAC[martingale; filtration] THEN
    DISCH_THEN(fun th -> ACCEPT_TAC(SPEC `SUC n` (CONJUNCT1(CONJUNCT1 th))));
    ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt p ((FF:num->(A->bool)->bool) (SUC n)) ((X:num->A->real) (SUC n))` ASSUME_TAC THENL
   [MP_TAC(ASSUME `martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)`) THEN
    REWRITE_TAC[martingale; simple_adapted; adapted] THEN
    DISCH_THEN(fun th -> ACCEPT_TAC(SPEC `SUC n` (CONJUNCT1(CONJUNCT1(CONJUNCT2 th)))));
    ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt p ((FF:num->(A->bool)->bool) (SUC n)) ((X:num->A->real) 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `p:A prob_space` MEASURABLE_WRT_MONO) THEN
    EXISTS_TAC `(FF:num->(A->bool)->bool) 0` THEN CONJ_TAC THENL
    [MP_TAC(ASSUME `martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)`) THEN
     REWRITE_TAC[martingale; simple_adapted; adapted] THEN
     DISCH_THEN(fun th -> ACCEPT_TAC(SPEC `0` (CONJUNCT1(CONJUNCT1(CONJUNCT2 th)))));
     MP_TAC(ASSUME `martingale (p:A prob_space) (FF:num->(A->bool)->bool) (X:num->A->real)`) THEN
     REWRITE_TAC[martingale; filtration] THEN
     DISCH_THEN(MP_TAC o CONJUNCT1) THEN
     DISCH_THEN(MP_TAC o CONJUNCT2) THEN
     DISCH_THEN(MP_TAC o SPECL [`0`; `SUC n`]) THEN
     REWRITE_TAC[LE_0]];
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv p (Z:A->real)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN MATCH_MP_TAC SIMPLE_RV_EXP THEN
    MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt p ((FF:num->(A->bool)->bool) (SUC n)) (Z:A->real)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    SUBGOAL_THEN
      `(\x:A. exp(s * ((X:num->A->real) (SUC n) x - X 0 x))) =
       (\x. (\v. exp(s * v)) ((\x. X (SUC n) x - X 0 x) x))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(ISPEC `p:A prob_space` MEASURABLE_WRT_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC(ISPEC `p:A prob_space` MEASURABLE_WRT_SUB) THEN
     REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   (* Z >= 0 *)
   SUBGOAL_THEN `!x:A. x IN prob_carrier p ==> &0 <= Z x` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
   (* Step bound: E[Z * exp(s*D)] <= exp(c^2) * E[Z] *)
   SUBGOAL_THEN
     `simple_expectation p (\x:A. (Z:A->real) x * exp(s * ((X:num->A->real) (SUC(SUC n)) x - X (SUC n) x))) <=
      exp(s pow 2 * ((b:num->real) (SUC n) - (a:num->real) (SUC n)) pow 2 / &8) *
      simple_expectation p Z`
     (LABEL_TAC "STEP") THENL
   [MATCH_MP_TAC MARTINGALE_DIFF_EXP_ADAPTED_BOUND THEN
    EXISTS_TAC `FF:num->(A->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [ASM_MESON_TAC[LE_REFL]; ASM_MESON_TAC[LE_REFL]];
    ALL_TAC] THEN
   (* Rewrite LHS *)
   SUBGOAL_THEN
     `simple_expectation p (\x:A. exp(s * ((X:num->A->real) (SUC(SUC n)) x - X 0 x))) =
      simple_expectation p (\x. (Z:A->real) x * exp(s * (X (SUC(SUC n)) x - X (SUC n) x)))`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    EXPAND_TAC "Z" THEN BETA_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
   (* Chain: E[Z*exp(s*D)] <= exp(c_n) * E[Z] <= exp(c_n) * exp(sum) = exp(sum') *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `exp(s pow 2 * ((b:num->real) (SUC n) - (a:num->real) (SUC n)) pow 2 / &8) *
               simple_expectation p (Z:A->real)` THEN
   CONJ_TAC THENL [USE_THEN "STEP" ACCEPT_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `exp(s pow 2 * ((b:num->real) (SUC n) - (a:num->real) (SUC n)) pow 2 / &8) *
               exp(s pow 2 * sum (0..n) (\i. ((b:num->real) i - (a:num->real) i) pow 2) / &8)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
     USE_THEN "IH" ACCEPT_TAC];
    ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
   MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN BETA_TAC THEN
   REAL_ARITH_TAC]);;

(* Azuma-Hoeffding inequality for martingales *)
let AZUMA_HOEFFDING = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real)
     (a:num->real) (b:num->real) (t:real) (n:num).
     martingale p FF X /\
     (!i. i <= n ==>
        !x. x IN prob_carrier p ==>
          a i <= X (SUC i) x - X i x /\ X (SUC i) x - X i x <= b i) /\
     (!i. i <= n ==> a i < b i) /\
     &0 < t /\ &0 < sum(0..n) (\i. (b i - a i) pow 2)
     ==> prob p {x | x IN prob_carrier p /\ X (SUC n) x - X 0 x >= t} <=
         exp(--(&2 * t pow 2 / sum(0..n) (\i. (b i - a i) pow 2)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `V = sum(0..n) (\i. ((b:num->real) i - (a:num->real) i) pow 2)` THEN
  ABBREV_TAC `s0 = &4 * t / V` THEN
  SUBGOAL_THEN `~(V = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s0` ASSUME_TAC THENL
  [EXPAND_TAC "s0" THEN
   MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 1: Chernoff bound *)
  SUBGOAL_THEN
    `prob (p:A prob_space) {x | x IN prob_carrier p /\ (X:num->A->real) (SUC n) x - X 0 x >= t} <=
     exp(--(s0 * t)) * simple_expectation p (\x. exp(s0 * (X (SUC n) x - X 0 x)))`
    (LABEL_TAC "CH") THENL
  [MP_TAC(ISPECL [`p:A prob_space`;
    `\x:A. (X:num->A->real) (SUC n) x - X 0 x`; `s0:real`; `t:real`]
    CHERNOFF_BOUND) THEN
   REWRITE_TAC[simple_mgf] THEN BETA_TAC THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_RV_SUB THEN
    REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[martingale];
    REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 2: MGF bound *)
  SUBGOAL_THEN
    `simple_expectation p (\x:A. exp(s0 * ((X:num->A->real) (SUC n) x - X 0 x))) <=
     exp(s0 pow 2 * V / &8)`
    (LABEL_TAC "MB") THENL
  [EXPAND_TAC "V" THEN MATCH_MP_TAC AZUMA_MGF_BOUND THEN
   EXISTS_TAC `FF:num->(A->bool)->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Combine *)
  SUBGOAL_THEN
    `prob (p:A prob_space) {x | x IN prob_carrier p /\ (X:num->A->real) (SUC n) x - X 0 x >= t} <=
     exp(--(s0 * t)) * exp(s0 pow 2 * V / &8)`
    (LABEL_TAC "COMB") THENL
  [TRANS_TAC REAL_LE_TRANS
     `exp(--(s0 * t)) * simple_expectation p (\x:A. exp(s0 * ((X:num->A->real) (SUC n) x - X 0 x)))` THEN
   CONJ_TAC THENL
   [USE_THEN "CH" ACCEPT_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
     USE_THEN "MB" ACCEPT_TAC]];
   ALL_TAC] THEN
  (* Step 4: Optimize: exp(-st + s^2V/8) = exp(-2t^2/V) for s = 4t/V *)
  TRANS_TAC REAL_LE_TRANS
    `exp(--(s0 * t)) * exp(s0 pow 2 * V / &8)` THEN
  CONJ_TAC THENL
  [USE_THEN "COMB" ACCEPT_TAC;
   REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
   MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
   UNDISCH_TAC `&0 < V` THEN
   UNDISCH_TAC `&0 < t` THEN
   EXPAND_TAC "s0" THEN EXPAND_TAC "V" THEN
   CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* DOOB DECOMPOSITION AND HELPERS                                            *)
(* ========================================================================= *)

(* Measurability under addition *)
let MEASURABLE_WRT_ADD = prove
 (`!p:A prob_space G (Y1:A->real) (Y2:A->real).
     sub_sigma_algebra p G /\
     simple_rv p Y1 /\ measurable_wrt p G Y1 /\
     simple_rv p Y2 /\ measurable_wrt p G Y2
     ==> measurable_wrt p G (\x. Y1 x + Y2 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN
  ABBREV_TAC `R2 = IMAGE (Y2:A->real) (prob_carrier p)` THEN
  SUBGOAL_THEN `FINITE (R2:real->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "R2" THEN REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
   ASM_MESON_TAC[simple_rv]; ALL_TAC] THEN
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\ (Y1:A->real) x + Y2 x <= v} =
     UNIONS (IMAGE (\u. {x | x IN prob_carrier p /\ Y2 x = u} INTER
                        {x | x IN prob_carrier p /\ Y1 x <= v - u})
                   R2)`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
   X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `(Y2:A->real) x` THEN
    CONJ_TAC THENL
    [EXPAND_TAC "R2" THEN REWRITE_TAC[IN_IMAGE] THEN
     EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  MATCH_MP_TAC SIGMA_ALGEBRA_UNION_COUNTABLE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
   X_GEN_TAC `u:real` THEN DISCH_TAC THEN
   MATCH_MP_TAC(ISPEC `p:A prob_space` SUB_SIGMA_ALGEBRA_INTER) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `p:A prob_space` MEASURABLE_WRT_LEVEL_SET) THEN
    ASM_REWRITE_TAC[];
    ACCEPT_TAC(SPEC `v - u:real` (REWRITE_RULE[measurable_wrt]
      (ASSUME `measurable_wrt (p:A prob_space) G (Y1:A->real)`)))];
   MATCH_MP_TAC COUNTABLE_IMAGE THEN MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
   ASM_REWRITE_TAC[]]);;

(* E[Y * 1_atom] = Y(x) * P(atom) when Y is G-measurable *)
let SIMPLE_EXPECTATION_INDICATOR_MEASURABLE = prove
 (`!p:A prob_space G (Y:A->real) x.
     sub_sigma_algebra p G /\ FINITE G /\ simple_rv p Y /\
     measurable_wrt p G Y /\
     x IN prob_carrier p /\ ~(prob p (sigma_atom G x) = &0)
     ==> simple_expectation p (\z. Y z * indicator_fn (sigma_atom G x) z) =
         Y x * prob p (sigma_atom G x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sigma_atom G (x:A) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SIGMA_ATOM_IN_G; sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma_algebra (G:(A->bool)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN UNIONS G` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation p (\z. (Y:A->real) z * indicator_fn (sigma_atom G x) z) =
     simple_expectation p (\z. Y x * indicator_fn (sigma_atom G x) z)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `z:A` THEN DISCH_TAC THEN BETA_TAC THEN
   REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_MUL_RID] THEN
    ASM_MESON_TAC[MEASURABLE_WRT_CONSTANT_ON_ATOM];
    REWRITE_TAC[REAL_MUL_RZERO]];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
                  `indicator_fn (sigma_atom G (x:A))`;
                  `(Y:A->real) x`] SIMPLE_EXPECTATION_CMUL) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[SIMPLE_EXPECTATION_INDICATOR]);;

(* Submartingale ==> E[X_{n+1}|F_n](x) >= X_n(x) on positive-prob atoms *)
let SUBMARTINGALE_COND_EXP_GE = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real) n x.
     submartingale p FF X /\ FINITE (FF n) /\
     x IN prob_carrier p /\ ~(prob p (sigma_atom (FF n) x) = &0)
     ==> X n x <= simple_cond_exp p (FF n) (X (SUC n)) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [submartingale] th)) THEN
  SUBGOAL_THEN `sub_sigma_algebra p ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN UNIONS ((FF:num->(A->bool)->bool) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra]; ALL_TAC] THEN
  SUBGOAL_THEN
    `sigma_atom ((FF:num->(A->bool)->bool) n) (x:A) IN FF n` ASSUME_TAC THENL
  [MATCH_MP_TAC SIGMA_ATOM_IN_G THEN ASM_MESON_TAC[sub_sigma_algebra];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `sigma_atom ((FF:num->(A->bool)->bool) n) (x:A) IN prob_events p`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[sub_sigma_algebra; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
    `measurable_wrt p ((FF:num->(A->bool)->bool) n) ((X:num->A->real) n)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[simple_adapted; adapted]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p ((X:num->A->real) n)` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p ((X:num->A->real) (SUC n))` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_rv p (simple_cond_exp p ((FF:num->(A->bool)->bool) n)
                    ((X:num->A->real) (SUC n)))` ASSUME_TAC THENL
  [ASM_MESON_TAC[SIMPLE_COND_EXP_SIMPLE_RV]; ALL_TAC] THEN
  SUBGOAL_THEN
    `measurable_wrt p ((FF:num->(A->bool)->bool) n)
      (simple_cond_exp p (FF n) ((X:num->A->real) (SUC n)))` ASSUME_TAC THENL
  [ASM_MESON_TAC[SIMPLE_COND_EXP_SIMPLE_RV_WRT; simple_rv_wrt]; ALL_TAC] THEN
  (* Step 1: E[X_n * 1_atom] = X_n(x) * P(atom) *)
  SUBGOAL_THEN
    `simple_expectation p
       (\z. (X:num->A->real) n z *
            indicator_fn (sigma_atom (FF n) x) z) =
     X n x * prob p (sigma_atom ((FF:num->(A->bool)->bool) n) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR_MEASURABLE THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 2: E[CE * 1_atom] = E[X_{n+1} * 1_atom] *)
  SUBGOAL_THEN
    `simple_expectation p
       (\z. simple_cond_exp p (FF n) ((X:num->A->real) (SUC n)) z *
            indicator_fn (sigma_atom (FF n) x) z) =
     simple_expectation p
       (\z. X (SUC n) z * indicator_fn (sigma_atom (FF n) x) z)`
    (ASSUME_TAC o SYM) THENL
  [MATCH_MP_TAC SIMPLE_COND_EXP_PROPERTY THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 3: E[CE * 1_atom] = CE(x) * P(atom) *)
  SUBGOAL_THEN
    `simple_expectation p
       (\z. simple_cond_exp p (FF n) ((X:num->A->real) (SUC n)) z *
            indicator_fn (sigma_atom (FF n) x) z) =
     simple_cond_exp p (FF n) (X (SUC n)) x *
     prob p (sigma_atom ((FF:num->(A->bool)->bool) n) x)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR_MEASURABLE THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 4: submartingale inequality *)
  SUBGOAL_THEN
    `simple_expectation p
       (\z. (X:num->A->real) n z *
            indicator_fn (sigma_atom (FF n) x) z) <=
     simple_expectation p
       (\z. X (SUC n) z * indicator_fn (sigma_atom (FF n) x) z)`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPECL
     [`n:num`; `sigma_atom ((FF:num->(A->bool)->bool) n) (x:A)`]) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 5: P(atom) > 0 *)
  SUBGOAL_THEN
    `&0 < prob p (sigma_atom ((FF:num->(A->bool)->bool) n) (x:A))`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[PROB_POSITIVE; REAL_LT_LE]; ALL_TAC] THEN
  (* Final cancellation *)
  MP_TAC(ISPECL
    [`(X:num->A->real) n x`;
     `simple_cond_exp p ((FF:num->(A->bool)->bool) n)
        ((X:num->A->real) (SUC n)) x`;
     `prob p (sigma_atom ((FF:num->(A->bool)->bool) n) (x:A))`]
    REAL_LE_RMUL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_REAL_ARITH_TAC);;

(* Sum from 1..n preserves simple_rv *)
let SIMPLE_RV_SUM_NUMSEG_1 = prove
 (`!p:A prob_space (f:num->A->real) n.
     (!k. 1 <= k /\ k <= n ==> simple_rv p (f k))
     ==> simple_rv p (\x. sum(1..n) (\k. f k x))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* n = 0: sum(1..0) = &0 *)
   DISCH_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(1..0) (\k. (f:num->A->real) k x)) = (\x. &0)`
     (fun th -> REWRITE_TAC[th; SIMPLE_RV_CONST]) THEN
   REWRITE_TAC[FUN_EQ_THM; SUM_CLAUSES_NUMSEG] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`];
   (* n -> SUC n: sum(1..SUC n) = sum(1..n) + f(SUC n) *)
   DISCH_TAC THEN
   SUBGOAL_THEN
     `(\x:A. sum(1..SUC n) (\k. (f:num->A->real) k x)) =
      (\x. sum(1..n) (\k. f k x) + f (SUC n) x)`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`];
    ALL_TAC] THEN
   MATCH_MP_TAC SIMPLE_RV_ADD THEN REWRITE_TAC[ETA_AX] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

(* Sum from 1..n preserves measurable_wrt along a filtration *)
let MEASURABLE_WRT_SUM_FILTRATION_1 = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (f:num->A->real) n.
     filtration p FF /\
     (!k. 1 <= k /\ k <= n ==> simple_rv p (f k)) /\
     (!k. 1 <= k /\ k <= n ==> measurable_wrt p (FF (k-1)) (f k))
     ==> measurable_wrt p (FF n) (\x. sum(1..n) (\k. f k x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [(* n = 0: sum(1..0) = &0 *)
   DISCH_TAC THEN
   SUBGOAL_THEN `(\x:A. sum(1..0) (\k. (f:num->A->real) k x)) = (\x. &0)`
     (fun th -> REWRITE_TAC[th] THEN MATCH_MP_TAC MEASURABLE_WRT_CONST THEN
                ASM_MESON_TAC[filtration]) THEN
   REWRITE_TAC[FUN_EQ_THM; SUM_CLAUSES_NUMSEG] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`];
   (* n -> SUC n *)
   STRIP_TAC THEN
   SUBGOAL_THEN
     `(\x:A. sum(1..SUC n) (\k. (f:num->A->real) k x)) =
      (\x. sum(1..n) (\k. f k x) + f (SUC n) x)`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`];
    ALL_TAC] THEN
   SUBGOAL_THEN `sub_sigma_algebra p ((FF:num->(A->bool)->bool) (SUC n))`
     ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv p (\x:A. sum(1..n) (\k. (f:num->A->real) k x))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG_1 THEN
    ASM_MESON_TAC[ARITH_RULE `k <= n ==> k <= SUC n`];
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv p ((f:num->A->real) (SUC n))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `1 <= SUC n /\ SUC n <= SUC n`]; ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt p ((FF:num->(A->bool)->bool) n)
     (\x:A. sum(1..n) (\k. (f:num->A->real) k x))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ARITH_RULE `k <= n ==> k <= SUC n`];
    ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt p ((FF:num->(A->bool)->bool) n)
     ((f:num->A->real) (SUC n))` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `1 <= SUC n /\ SUC n <= SUC n`;
                   ARITH_RULE `SUC n - 1 = n`];
    ALL_TAC] THEN
   SUBGOAL_THEN `(FF:num->(A->bool)->bool) n SUBSET FF (SUC n)`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[FILTRATION_MONO; ARITH_RULE `n <= SUC n`]; ALL_TAC] THEN
   MATCH_MP_TAC MEASURABLE_WRT_ADD THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[] THEN
   CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
   EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN ASM_REWRITE_TAC[]]);;

(* Helper: E[(X - CE(G,X)) * 1_a] = 0 for a IN G *)
let COND_EXP_INDICATOR_DIFF_ZERO = prove
 (`!p:A prob_space G (X:A->real) a.
     sub_sigma_algebra p G /\ FINITE G /\ simple_rv p X /\ a IN G
     ==> simple_expectation p
           (\x. (X x - simple_cond_exp p G X x) * indicator_fn a x) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simple_rv p (simple_cond_exp p G (X:A->real))` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_COND_EXP_SIMPLE_RV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
  [ASM_MESON_TAC[SUB_SIGMA_ALGEBRA_IN_EVENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv p (indicator_fn (a:A->bool))` ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation p
       (\x:A. ((X:A->real) x - simple_cond_exp p G X x) * indicator_fn a x) =
     simple_expectation p
       (\x. X x * indicator_fn a x - simple_cond_exp p G X x * indicator_fn a x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation p
       (\x:A. (X:A->real) x * indicator_fn a x -
              simple_cond_exp p G X x * indicator_fn a x) =
     simple_expectation p (\x. X x * indicator_fn a x) -
     simple_expectation p (\x. simple_cond_exp p G X x * indicator_fn a x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN
   CONJ_TAC THEN MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation p
       (\x:A. simple_cond_exp p G (X:A->real) x * indicator_fn a x) =
     simple_expectation p (\x. X x * indicator_fn a x)`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_COND_EXP_PROPERTY THEN
   REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Doob Decomposition: X = M + A with M martingale, A predictable increasing *)
(* Modified: increasing condition restricted to positive-probability atoms *)
let DOOB_DECOMPOSITION = prove
 (`!p:A prob_space (FF:num->(A->bool)->bool) (X:num->A->real).
     submartingale p FF X /\ (!n. FINITE (FF n))
     ==> ?M A. martingale p FF M /\
               simple_adapted p FF A /\
               (!x. x IN prob_carrier p ==> A 0 x = &0) /\
               (!n x. x IN prob_carrier p /\
                      ~(prob p (sigma_atom (FF n) x) = &0)
                      ==> A (SUC n) x >= A n x) /\
               (!n x. x IN prob_carrier p ==>
                  X n x = M n x + A n x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [submartingale] th)) THEN
  (* Witnesses: M_n = X_n - A_n, A_n = sum of Doob increments *)
  EXISTS_TAC `\n (x:A). (X:num->A->real) n x -
    sum(1..n) (\k. simple_cond_exp p ((FF:num->(A->bool)->bool) (k-1))
                     ((X:num->A->real) k) x - X (k-1) x)` THEN
  EXISTS_TAC `\n (x:A). sum(1..n)
    (\k. simple_cond_exp p ((FF:num->(A->bool)->bool) (k-1))
           ((X:num->A->real) k) x - X (k-1) x)` THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  (* Establish D_k = CE(FF(k-1), X k) - X(k-1) properties *)
  SUBGOAL_THEN
    `!k. 1 <= k ==>
       simple_rv p (\x:A. simple_cond_exp p ((FF:num->(A->bool)->bool) (k-1))
         ((X:num->A->real) k) x - X (k-1) x) /\
       measurable_wrt p (FF (k-1))
         (\x. simple_cond_exp p (FF (k-1)) (X k) x - X (k-1) x)`
    (LABEL_TAC "Dk") THENL
  [GEN_TAC THEN DISCH_TAC THEN
   SUBGOAL_THEN `sub_sigma_algebra p ((FF:num->(A->bool)->bool) (k-1))`
     ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv p
     (simple_cond_exp p ((FF:num->(A->bool)->bool) (k-1))
       ((X:num->A->real) k))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_COND_EXP_SIMPLE_RV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `measurable_wrt p ((FF:num->(A->bool)->bool) (k-1))
     (simple_cond_exp p (FF (k-1)) ((X:num->A->real) k))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) (k-1)`;
                    `(X:num->A->real) k`] SIMPLE_COND_EXP_SIMPLE_RV_WRT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SIMP_TAC[simple_rv_wrt]; ALL_TAC] THEN
   CONJ_TAC THENL
   [(* simple_rv of D_k *)
    MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    (* measurable_wrt of D_k w.r.t. FF(k-1) *)
    MATCH_MP_TAC(ISPEC `p:A prob_space` MEASURABLE_WRT_SUB) THEN
    REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simple_adapted; adapted]];
   ALL_TAC] THEN
  (* Establish A_n is simple_rv *)
  SUBGOAL_THEN `!n. simple_rv p
    (\x:A. sum(1..n)
      (\k. simple_cond_exp p ((FF:num->(A->bool)->bool) (k-1))
        ((X:num->A->real) k) x - X (k-1) x))` (LABEL_TAC "An_rv") THENL
  [GEN_TAC THEN MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG_1 THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   USE_THEN "Dk" (MP_TAC o SPEC `k:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Prove: martingale p FF M *)
  (* First establish M_rv *)
  SUBGOAL_THEN `!n. simple_rv p
    (\x:A. (X:num->A->real) n x -
      sum(1..n)(\k. simple_cond_exp p ((FF:num->(A->bool)->bool) (k-1))
        (X k) x - X (k-1) x))` (LABEL_TAC "M_rv") THENL
  [GEN_TAC THEN MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    USE_THEN "An_rv" (ACCEPT_TAC o SPEC `n:num`)];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[martingale] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   (* Conjunct 1: filtration *)
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   (* Conjunct 2: simple_adapted *)
   CONJ_TAC THENL
   [REWRITE_TAC[simple_adapted; adapted] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONJ_TAC THENL
    [(* adapted: measurable_wrt *)
     GEN_TAC THEN
     MATCH_MP_TAC(ISPEC `p:A prob_space` MEASURABLE_WRT_SUB) THEN
     REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     CONJ_TAC THENL [ASM_MESON_TAC[simple_adapted; adapted]; ALL_TAC] THEN
     CONJ_TAC THENL
     [USE_THEN "An_rv" (ACCEPT_TAC o SPEC `n:num`); ALL_TAC] THEN
     MATCH_MP_TAC MEASURABLE_WRT_SUM_FILTRATION_1 THEN
     ASM_REWRITE_TAC[] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     ASM_MESON_TAC[];
     (* FINITE range *)
     GEN_TAC THEN
     USE_THEN "M_rv" (MP_TAC o SPEC `n:num`) THEN
     REWRITE_TAC[simple_rv] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     MESON_TAC[]];
    ALL_TAC] THEN
   (* Conjunct 3: simple_rv *)
   CONJ_TAC THENL
   [GEN_TAC THEN USE_THEN "M_rv" (ACCEPT_TAC o SPEC `n:num`);
    ALL_TAC] THEN
   (* Conjunct 4: conditional expectation condition *)
   GEN_TAC THEN X_GEN_TAC `a:A->bool` THEN DISCH_TAC THEN
   SUBGOAL_THEN `sub_sigma_algebra p ((FF:num->(A->bool)->bool) n)`
     ASSUME_TAC THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
   SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUB_SIGMA_ALGEBRA_IN_EVENTS]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv p (indicator_fn (a:A->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_INDICATOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv p (simple_cond_exp p ((FF:num->(A->bool)->bool) n)
     ((X:num->A->real) (SUC n)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_COND_EXP_SIMPLE_RV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   (* Rewrite M(SUC n)*1_a using sum expansion *)
   SUBGOAL_THEN
     `simple_expectation p
        (\x:A. ((X:num->A->real) (SUC n) x -
          sum(1..SUC n)(\k. simple_cond_exp p
            ((FF:num->(A->bool)->bool) (k-1)) (X k) x - X (k-1) x)) *
          indicator_fn a x) =
      simple_expectation p
        (\x. (X n x - sum(1..n)(\k. simple_cond_exp p (FF (k-1))
            (X k) x - X (k-1) x)) * indicator_fn a x +
          (X (SUC n) x - simple_cond_exp p (FF n) (X (SUC n)) x) *
            indicator_fn a x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   (* Split E[f + g] = E[f] + E[g] *)
   SUBGOAL_THEN
     `simple_expectation p
        (\x:A. ((X:num->A->real) n x -
          sum(1..n)(\k. simple_cond_exp p
            ((FF:num->(A->bool)->bool) (k-1)) (X k) x - X (k-1) x)) *
          indicator_fn a x +
          (X (SUC n) x - simple_cond_exp p (FF n) (X (SUC n)) x) *
            indicator_fn a x) =
      simple_expectation p
        (\x. (X n x - sum(1..n)(\k. simple_cond_exp p (FF (k-1))
            (X k) x - X (k-1) x)) * indicator_fn a x) +
      simple_expectation p
        (\x. (X (SUC n) x - simple_cond_exp p (FF n) (X (SUC n)) x) *
            indicator_fn a x)`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SIMPLE_EXPECTATION_ADD THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [USE_THEN "M_rv" (ACCEPT_TAC o SPEC `n:num`);
      ASM_REWRITE_TAC[]];
     MATCH_MP_TAC SIMPLE_RV_MUL THEN REWRITE_TAC[ETA_AX] THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_RV_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]; ALL_TAC] THEN
   (* E[(X(SUC n) - CE)*1_a] = 0 *)
   SUBGOAL_THEN
     `simple_expectation p
        (\x:A. ((X:num->A->real) (SUC n) x -
          simple_cond_exp p ((FF:num->(A->bool)->bool) n)
            (X (SUC n)) x) * indicator_fn a x) = &0`
     SUBST1_TAC THENL
   [MATCH_MP_TAC COND_EXP_INDICATOR_DIFF_ZERO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  CONJ_TAC THENL
  [(* simple_adapted p FF A *)
   REWRITE_TAC[simple_adapted; adapted] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   CONJ_TAC THENL
   [(* adapted: !n. measurable_wrt p (FF n) (A n) *)
    GEN_TAC THEN
    MATCH_MP_TAC MEASURABLE_WRT_SUM_FILTRATION_1 THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_MESON_TAC[];
    (* FINITE range of A n *)
    GEN_TAC THEN
    USE_THEN "An_rv" (MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[simple_rv] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    MESON_TAC[]];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [(* A 0 x = &0: sum(1..0) = &0 *)
   GEN_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
   COND_CASES_TAC THENL [ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`]; REFL_TAC];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [(* A (SUC n) x >= A n x *)
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
   REWRITE_TAC[real_ge; ARITH_RULE `SUC n - 1 = n`] THEN
   MATCH_MP_TAC(REAL_ARITH `x <= y ==> a <= a + (y - x)`) THEN
   MATCH_MP_TAC SUBMARTINGALE_COND_EXP_GE THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* X n x = M n x + A n x: trivial algebra *)
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* CLT COMPLETION: CONVERGENCE IN DISTRIBUTION TO STANDARD NORMAL            *)
(* ========================================================================= *)


(* --- Phase 1: Parameterized Gaussian Integral and Fourier Transform --- *)

(* Helper: stretching an integral over all of R by a positive factor *)
let HAS_REAL_INTEGRAL_STRETCH_UNIV = prove
 (`!(f:real->real) i m.
      (f has_real_integral i) (:real) /\ &0 < m
      ==> ((\x. f(m * x)) has_real_integral inv(m) * i) (:real)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_real_integral; o_DEF; IMAGE_LIFT_UNIV] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\v:real^1. lift((f:real->real)(drop v))`;
    `lift(i:real)`;
    `(:real^1)`;
    `m:real`;
    `vec 0:real^1`] HAS_INTEGRAL_AFFINITY) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_RID; VECTOR_MUL_RZERO; VECTOR_NEG_0;
              DIMINDEX_1; REAL_POW_1; DROP_CMUL; LIFT_CMUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < m ==> abs m = m`] THEN
  SUBGOAL_THEN `IMAGE (\v:real^1. inv m % v) (:real^1) = (:real^1)`
    ASSUME_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
   GEN_TAC THEN EXISTS_TAC `m % (x:real^1)` THEN
   REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
   ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
   ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* GAUSSIAN INTEGRAL PROOF                                                   *)
(* Proved via the H(a)+J(a)=pi/4 approach (no gamma.ml needed)  *)
(* Fully proved (no CHEAT_TAC in this section)                               *)
(* ========================================================================= *)


(* FTC for squaring an integral *)
let FTC_SQUARE_DERIV = prove
 (`!f a b.
     f real_continuous_on real_interval[a,b]
     ==> !x. x IN real_interval[a,b]
         ==> ((\u. real_integral (real_interval[a,u]) f pow 2)
              has_real_derivative
              (&2 * real_integral (real_interval[a,x]) f * f x))
             (atreal x within real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`]
    REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    MP_TAC(ISPEC `2` (MATCH_MP HAS_REAL_DERIVATIVE_POW_WITHIN th))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1]);;

let FTC_SQUARE = prove
 (`!f a b. f real_continuous_on real_interval[a,b] /\ a <= b
   ==> real_integral (real_interval[a,b]) f pow 2 =
       real_integral (real_interval[a,b])
         (\x. &2 * real_integral (real_interval[a,x]) f * f x)`,
  REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,b]) (f:real->real) pow 2 =
    real_integral (real_interval[a,b]) f pow 2 -
    real_integral (real_interval[a,a]) f pow 2`
   SUBST1_TAC THENL
  [SUBGOAL_THEN `real_integral (real_interval[a,a]) (f:real->real) = &0`
    SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_NULL THEN REWRITE_TAC[REAL_LE_REFL];
    REWRITE_TAC[] THEN REAL_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\u:real. real_integral (real_interval[a,u]) (f:real->real) pow 2`;
    `\x:real. &2 * real_integral (real_interval[a,x]) (f:real->real) * f x`;
    `a:real`; `b:real`]
   REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`] FTC_SQUARE_DERIV) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
   ASM_REWRITE_TAC[];
   SIMP_TAC[]]);;

(* Arctan integral *)
let ARCTAN_INTEGRAL = prove
 (`((\t. inv(&1 + t pow 2)) has_real_integral (pi / &4))
   (real_interval [&0, &1])`,
  SUBGOAL_THEN `pi / &4 = atn(&1) - atn(&0)` SUBST1_TAC THENL
  [REWRITE_TAC[ATN_1; ATN_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATN]);;

(* Antiderivative of x*exp(-cx^2) *)
let EXP_QUAD_ANTIDERIV = prove
 (`!c a b. &0 < c /\ a <= b
   ==> ((\x. x * exp(--(c * x pow 2)))
        has_real_integral
        (inv(&2 * c) * (exp(--(c * a pow 2)) - exp(--(c * b pow 2)))))
       (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `inv(&2 * c) * (exp(--(c * a pow 2)) - exp(--(c * b pow 2))) =
     (--inv(&2 * c) * exp(--(c * b pow 2))) -
     (--inv(&2 * c) * exp(--(c * a pow 2)))`
    SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  SUBGOAL_THEN `~(&2 * c = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `x * exp(--(c * x pow 2)) =
     --inv(&2 * c) * (--(c * &2 * x) * exp(--(c * x pow 2)))`
    SUBST1_TAC THENL
  [UNDISCH_TAC `~(&2 * c = &0)` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  REAL_DIFF_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_1; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

(* exp(-x^2) continuity and integrability *)
let EXP_NEG_X2_INTEGRABLE = prove
 (`!a b. (\x. exp(--(x pow 2))) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC);;

let EXP_NEG_X2_CONTINUOUS = prove
 (`(\x. exp(--(x pow 2))) real_continuous_on real_interval[a,b]`,
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC);;

(* Limit building blocks *)
let REALLIM_EXP_NEG = prove
 (`((\x. exp(--x)) ---> &0) at_posinfinity`,
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `inv(e) + &1` THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_EXP_NEG] THEN
  SUBGOAL_THEN `abs(inv(exp x)) = inv(exp x)` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_INV THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(e)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(e) + &1` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(inv(e) + &1)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 + x)` THEN
   CONJ_TAC THENL
   [MP_TAC(ISPECL [`&1 + x`; `exp x`] REAL_LE_INV2) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
     SIMP_TAC[]];
    MP_TAC(ISPECL [`inv(e) + &1`; `&1 + x`] REAL_LE_INV2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
   SUBGOAL_THEN `inv(inv e + &1) * (inv e + &1) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `e * inv e = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `inv(inv e + &1) * (inv e + &1) < e * (inv e + &1)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ]]]);;

let REALLIM_EXP_NEG_SQ = prove
 (`((\x. exp(--(x pow 2))) ---> &0) at_posinfinity`,
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real`
    (REWRITE_RULE[REALLIM_AT_POSINFINITY] REALLIM_EXP_NEG)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real` ASSUME_TAC) THEN
  EXISTS_TAC `max (&1) N` THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `y pow 2 >= N` ASSUME_TAC THENL
  [REWRITE_TAC[real_ge] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `y:real` THEN
   CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_2] THEN
    MP_TAC(ISPECL [`y:real`; `&1`; `y:real`] REAL_LE_LMUL) THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
   ASM_MESON_TAC[]]);;

(* Integrand bound *)
let INTEGRAND_BOUND = prove
 (`!B t. &0 <= t /\ t <= &1
    ==> exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2) <=
        exp(--(B pow 2))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(B pow 2)) * inv(&1 + t pow 2)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    MP_TAC(SPEC `&1 + (t:real) pow 2` (SPEC `&1`
      (SPEC `(B:real) pow 2` REAL_LE_LMUL))) THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
    [REWRITE_TAC[REAL_LE_POW_2];
     MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_INV THEN
    MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
   MP_TAC(SPEC `&1` (SPEC `inv(&1 + (t:real) pow 2)`
     (SPEC `exp(--((B:real) pow 2))` REAL_LE_LMUL))) THEN
   REWRITE_TAC[REAL_MUL_RID] THEN
   DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
    MATCH_MP_TAC REAL_INV_LE_1 THEN
    MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]]);;

(* H(B) -> 0 *)
let H_LIMIT_ZERO = prove
 (`((\B. real_integral (real_interval[&0,&1])
          (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2)))
    ---> &0) at_posinfinity`,
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\B:real. exp(--(B pow 2))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_AT_POSINFINITY] THEN
   EXISTS_TAC `&0` THEN X_GEN_TAC `B:real` THEN DISCH_TAC THEN
   SUBGOAL_THEN
     `(\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2))
      real_integrable_on real_interval[&0,&1]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= real_integral (real_interval[&0,&1])
     (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
     MATCH_MP_TAC REAL_LE_INV THEN
     MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `abs(real_integral (real_interval[&0,&1])
       (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2))) =
      real_integral (real_interval[&0,&1])
       (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2))`
     SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `real_integral (real_interval[&0,&1])
       (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2)) <=
      exp(--(B pow 2)) * (&1 - &0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UBOUND THEN
    REPEAT CONJ_TAC THENL
    [REAL_ARITH_TAC;
     ASM_REWRITE_TAC[];
     X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
     STRIP_TAC THEN MATCH_MP_TAC INTEGRAND_BOUND THEN
     ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_ARITH `a * (&1 - &0) = a`]];
   ACCEPT_TAC REALLIM_EXP_NEG_SQ]);;

(* GAUSS_SUBSTITUTION: integral[0,c] exp(-t^2) dt = integral[0,1] c*exp(-c^2*u^2) du *)
let GAUSS_SUBSTITUTION = prove
 (`!x. &0 < x ==>
   ((\u. x * exp(--(x pow 2 * u pow 2)))
    has_real_integral
    real_integral (real_interval[&0,x]) (\t. exp(--(t pow 2))))
   (real_interval[&0,&1])`,
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\t:real. exp(--(t pow 2))`;
    `\u:real. c * u`;
    `\u:real. c:real`;
    `&0`; `&1`; `&0`; `c:real`; `{}:real->bool`]
    HAS_REAL_INTEGRAL_SUBSTITUTION) THEN
  REWRITE_TAC[COUNTABLE_EMPTY; DIFF_EMPTY] THEN
  BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID] THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
     GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC];
   SUBGOAL_THEN
     `(\u. exp(--((c * u) pow 2)) * c) = (\u. c * exp(--(c pow 2 * u pow 2)))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:real` THEN
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
    SIMP_TAC[]]]);;

(* INNER_X_INTEGRAL: integral[0,B] 2*x*exp(-(1+u^2)*x^2) dx *)
let INNER_X_INTEGRAL = prove
 (`!u B. &0 <= u /\ &0 < B ==>
   ((\x. &2 * x * exp(--((&1 + u pow 2) * x pow 2)))
    has_real_integral
    inv(&1 + u pow 2) * (&1 - exp(--((&1 + u pow 2) * B pow 2))))
   (real_interval[&0,B])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + u pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `u:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`&1 + u pow 2`; `&0`; `B:real`] EXP_QUAD_ANTIDERIV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&2` (MATCH_MP HAS_REAL_INTEGRAL_LMUL th))) THEN
  SUBGOAL_THEN
    `(\x. &2 * (x * exp(--((&1 + u pow 2) * x pow 2)))) =
     (\x. &2 * x * exp(--((&1 + u pow 2) * x pow 2)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `&2 * (inv(&2 * (&1 + u pow 2)) *
     (exp(--((&1 + u pow 2) * &0 pow 2)) -
      exp(--((&1 + u pow 2) * B pow 2)))) =
     inv(&1 + u pow 2) * (&1 - exp(--((&1 + u pow 2) * B pow 2)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_POW_2; REAL_MUL_RZERO; REAL_MUL_LZERO;
               REAL_NEG_0; REAL_EXP_0] THEN
   UNDISCH_TAC `&0 < &1 + u pow 2` THEN CONV_TAC REAL_FIELD;
   SIMP_TAC[]]);;

(* === Helper lemmas for J_EQUALS_OUTER === *)

let LIFT_ZERO = prove
 (`lift(&0) :real^1 = vec 0`,
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
  MESON_TAC[LIFT_DROP; LIFT_EQ]);;

let REAL_INTEGRAL_REFL = prove
 (`!(f:real->real) a. real_integral (real_interval[a,a]) f = &0`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[has_real_integral; IMAGE_LIFT_REAL_INTERVAL; LIFT_ZERO] THEN
  REWRITE_TAC[HAS_INTEGRAL_REFL]);;

let EXP_NEG_ADD = prove
 (`!a b. exp(--a) * exp(--b) = exp(--(a + b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let IMAGE_LIFT_REAL_INTERVAL = prove
 (`!a b. IMAGE lift (real_interval[a,b]) = interval[lift a, lift b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INTERVAL_INTERVAL; GSYM IMAGE_o] THEN
  SUBGOAL_THEN `lift o (drop:real^1->real) = I` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_I]);;

let LIFT_DROP_FSTCART = prove
 (`(\z:real^(1,1)finite_sum. lift(drop(fstcart z))) = fstcart`,
  REWRITE_TAC[FUN_EQ_THM; LIFT_DROP]);;

let LIFT_DROP_SNDCART = prove
 (`(\z:real^(1,1)finite_sum. lift(drop(sndcart z))) = sndcart`,
  REWRITE_TAC[FUN_EQ_THM; LIFT_DROP]);;

let LIFT_EXP_DROP_CONTINUOUS = prove
 (`!s:real^1->bool. (lift o exp o drop) continuous_on s`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(:real^1)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_UNIV] THEN
  REWRITE_TAC[GSYM REAL_CONTINUOUS_ON; REAL_CONTINUOUS_ON_EXP]);;

let EXP_NEG_SQ_REAL_CONTINUOUS = prove
 (`!B. (\t. exp(--(t pow 2))) real_continuous_on real_interval[&0,B]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC);;

let INNER_INTEGRAND_INTEGRABLE = prove
 (`!x:real. (\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2)))
            real_integrable_on real_interval[&0,&1]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC THEN
  MP_TAC(SPEC `x':real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let OUTER_INTEGRAND_INTEGRABLE = prove
 (`!B:real u. (\x. &2 * x * exp(--((&1 + u pow 2) * x pow 2)))
              real_integrable_on real_interval[&0,B]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let GAUSS_INTEGRAL_DERIV = prove
 (`!B x. x IN real_interval[&0,B] ==>
   ((\u. real_integral(real_interval[&0,u]) (\t. exp(--(t pow 2))))
    has_real_derivative exp(--(x pow 2)))
   (atreal x within real_interval[&0,B])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t:real. exp(--(t pow 2))`; `&0`; `B:real`]
    REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  REWRITE_TAC[EXP_NEG_SQ_REAL_CONTINUOUS] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[]);;

let GAUSS_SQ_FTC = prove
 (`!B. &0 <= B ==>
   ((\x. &2 * real_integral(real_interval[&0,x])
                  (\t. exp(--(t pow 2))) * exp(--(x pow 2)))
    has_real_integral
    (real_integral(real_interval[&0,B]) (\t. exp(--(t pow 2))) pow 2))
   (real_interval[&0,B])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x:real. real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2))) pow 2`;
    `\x:real. &2 * real_integral(real_interval[&0,x])
                    (\t. exp(--(t pow 2))) * exp(--(x pow 2))`;
    `&0`; `B:real`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  BETA_TAC THEN
  REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_POW_ZERO; ARITH; REAL_SUB_RZERO] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `(\x. real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2))) pow 2) =
     (\x. real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2))) *
          real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; REAL_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN
    `&2 * real_integral (real_interval[&0,x]) (\t. exp(--(t pow 2))) *
     exp(--(x pow 2)) =
     real_integral (real_interval[&0,x]) (\t. exp(--(t pow 2))) *
     exp(--(x pow 2)) +
     exp(--(x pow 2)) *
     real_integral (real_interval[&0,x]) (\t. exp(--(t pow 2)))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x:real. real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2)))`;
    `exp(--(x pow 2))`;
    `\x:real. real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2)))`;
    `exp(--(x pow 2))`; `x:real`; `real_interval[&0,B]`]
   HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN BETA_TAC THEN
  DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC GAUSS_INTEGRAL_DERIV THEN ASM_REWRITE_TAC[]);;

let GAUSS_INNER_REWRITE = prove
 (`!x. &0 < x ==>
   ((\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2)))
    has_real_integral
    (&2 * real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2))) *
     exp(--(x pow 2))))
   (real_interval[&0,&1])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` GAUSS_SUBSTITUTION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&2 * exp(--(x pow 2))`
    (MATCH_MP HAS_REAL_INTEGRAL_LMUL th))) THEN BETA_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`\u:real. (&2 * exp(--(x pow 2))) * (x * exp(--(x pow 2 * u pow 2)))`;
     `\u:real. &2 * x * exp(--((&1 + u pow 2) * x pow 2))`;
     `(&2 * exp(--(x pow 2))) *
      real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2)))`;
     `real_interval[&0,&1]`] HAS_REAL_INTEGRAL_EQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [CONJ_TAC THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `(&2 * exp(--(x pow 2))) * (x * exp(--(x pow 2 * u pow 2))) =
       &2 * x * (exp(--(x pow 2)) * exp(--(x pow 2 * u pow 2)))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_NEG_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(&2 * exp(--(x pow 2))) *
     real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2))) =
     &2 * real_integral(real_interval[&0,x]) (\t. exp(--(t pow 2))) *
     exp(--(x pow 2))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]);;

let INNER_VEC_CONV = prove
 (`!x:real.
   integral (interval[lift(&0),lift(&1)])
     (\u:real^1. lift(&2 * x * exp(--((&1 + drop u pow 2) * x pow 2)))) =
   lift(real_integral (real_interval[&0,&1])
     (\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2))))`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(MATCH_MP REAL_INTEGRAL (SPEC `x:real` INNER_INTEGRAND_INTEGRABLE)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; LIFT_DROP; IMAGE_LIFT_REAL_INTERVAL]) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]);;

let OUTER_VEC_CONV = prove
 (`!B u:real.
   integral (interval[lift(&0),lift B])
     (\x:real^1. lift(&2 * drop x * exp(--((&1 + u pow 2) * drop x pow 2)))) =
   lift(real_integral (real_interval[&0,B])
     (\x. &2 * x * exp(--((&1 + u pow 2) * x pow 2))))`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(MATCH_MP REAL_INTEGRAL
    (SPECL [`B:real`; `u:real`] OUTER_INTEGRAND_INTEGRABLE)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; LIFT_DROP; IMAGE_LIFT_REAL_INTERVAL]) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]);;

let GAUSS_2D_CONTINUOUS = prove
 (`!B. (\z. lift(&2 * drop(fstcart z) *
             exp(--((&1 + drop(sndcart z) pow 2) * drop(fstcart z) pow 2))))
       continuous_on
       (interval[pastecart (lift(&0)) (lift(&0)):real^(1,1)finite_sum,
                 pastecart (lift B) (lift(&1))])`,
  GEN_TAC THEN
  SUBGOAL_THEN
    `(\z. lift(&2 * drop(fstcart z) *
             exp(--((&1 + drop(sndcart z) pow 2) * drop(fstcart z) pow 2)))) =
     (\z:real^(1,1)finite_sum. (&2 * drop(fstcart z)) %
             lift(exp(--((&1 + drop(sndcart z) pow 2) * drop(fstcart z) pow 2))))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL] THEN
   GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
  [SUBGOAL_THEN
     `(lift o (\z:real^(1,1)finite_sum. &2 * drop(fstcart z))) =
      (\z. &2 % (fstcart z:real^1))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL; LIFT_DROP]; ALL_TAC] THEN
   MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
   MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `(\z:real^(1,1)finite_sum.
       lift(exp(--((&1 + drop(sndcart z) pow 2) * drop(fstcart z) pow 2)))) =
     ((lift o exp o drop) :real^1->real^1) o
     (\z. lift(--((&1 + drop(sndcart z) pow 2) * drop(fstcart z) pow 2)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
  [SUBGOAL_THEN
     `(\z:real^(1,1)finite_sum.
        lift(--((&1 + drop(sndcart z) pow 2) * drop(fstcart z) pow 2))) =
      (\z. --(lift((&1 + drop(sndcart z) pow 2) * drop(fstcart z) pow 2)))`
     SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_NEG]; ALL_TAC] THEN
   MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
   SUBGOAL_THEN
     `(\z:real^(1,1)finite_sum.
        lift((&1 + drop(sndcart z) pow 2) * drop(fstcart z) pow 2)) =
      (\z. (&1 + drop(sndcart z) pow 2) % lift(drop(fstcart z) pow 2))`
     SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL]; ALL_TAC] THEN
   MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN
      `(lift o (\z:real^(1,1)finite_sum. &1 + drop(sndcart z) pow 2)) =
       (\z. lift(&1) + lift(drop(sndcart z) pow 2))` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_ADD]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_DROP_SNDCART] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_DROP_FSTCART] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART]];
   REWRITE_TAC[LIFT_EXP_DROP_CONTINUOUS]]);;


(* Integrability of H and J outer integrands - moved before J_EQUALS_OUTER *)
let INTEGRAND_SUM_EQ_INV = prove
 (`!B t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2) +
         inv(&1 + t pow 2) * (&1 - exp(--((&1 + t pow 2) * B pow 2))) =
         inv(&1 + t pow 2)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `B pow 2 * (&1 + t pow 2) = (&1 + t pow 2) * B pow 2`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
    `x * a + a * (&1 - x) = a ==> x * a + a * (&1 - x) = a`) THEN
  CONV_TAC REAL_RING);;

let H_INTEGRAND_INTEGRABLE = prove
 (`!B. (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2))
       real_integrable_on real_interval[&0,&1]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let J_OUTER_INTEGRAND_INTEGRABLE = prove
 (`!B. (\u. inv(&1 + u pow 2) * (&1 - exp(--((&1 + u pow 2) * B pow 2))))
       real_integrable_on real_interval[&0,&1]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

(* J_EQUALS_OUTER: J(B) = integral[0,1] inv(1+u^2)*(1-exp(-(1+u^2)*B^2)) du *)
(* Proved via Fubini (INTEGRAL_SWAP_CONTINUOUS), GAUSS_SUBSTITUTION, INNER_X_INTEGRAL *)
let J_EQUALS_OUTER = prove
 (`!B. &0 < B ==>
   real_integral (real_interval[&0,B])
     (\x. exp(--(x pow 2))) pow 2 =
   real_integral (real_interval[&0,&1])
     (\u. inv(&1 + u pow 2) * (&1 - exp(--((&1 + u pow 2) * B pow 2))))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Step 1: GAUSS_SQ_FTC *)
  MP_TAC(SPEC `B:real` GAUSS_SQ_FTC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  (* Step 2: Integrand equality *)
  SUBGOAL_THEN
    `!x:real. x IN real_interval[&0,B] ==>
     &2 * real_integral (real_interval[&0,x]) (\t. exp(--(t pow 2))) *
       exp(--(x pow 2)) =
     real_integral (real_interval[&0,&1])
       (\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2)))`
    ASSUME_TAC THENL
  [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
   ASM_CASES_TAC `&0 < x` THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC GAUSS_INNER_REWRITE THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `x = &0` SUBST_ALL_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_INTEGRAL_REFL;
                REAL_INTEGRAL_0]];
   ALL_TAC] THEN
  (* Step 3: h has_real_integral G(B)^2 *)
  SUBGOAL_THEN
    `((\x. real_integral (real_interval[&0,&1])
       (\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2))))
     has_real_integral
     (real_integral (real_interval[&0,B]) (\x. exp(--(x pow 2))) pow 2))
     (real_interval[&0,B])`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL
     [`\x:real. &2 * real_integral (real_interval[&0,x])
                 (\t. exp(--(t pow 2))) * exp(--(x pow 2))`;
      `\x:real. real_integral (real_interval[&0,&1])
                 (\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2)))`;
      `real_integral (real_interval[&0,B]) (\x. exp(--(x pow 2))) pow 2`;
      `real_interval[&0,B]`]
     HAS_REAL_INTEGRAL_EQ) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    SIMP_TAC[]];
   ALL_TAC] THEN
  (* Step 4: h real_integrable *)
  SUBGOAL_THEN
    `(\x. real_integral (real_interval[&0,&1])
       (\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2))))
     real_integrable_on real_interval[&0,B]`
    ASSUME_TAC THENL
  [REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Step 5: G(B)^2 = real_integral[0,B] h *)
  SUBGOAL_THEN
    `real_integral (real_interval[&0,B]) (\x. exp(--(x pow 2))) pow 2 =
     real_integral (real_interval[&0,B])
       (\x. real_integral (real_interval[&0,&1])
         (\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2))))`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 6: Convert to vector form *)
  MP_TAC(MATCH_MP REAL_INTEGRAL (ASSUME
    `(\x. real_integral (real_interval[&0,&1])
       (\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2))))
     real_integrable_on real_interval[&0,B]`)) THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  DISCH_TAC THEN
  (* Step 7: lift o h o drop = vec inner form *)
  SUBGOAL_THEN
    `(lift o (\x. real_integral (real_interval[&0,&1])
       (\u. &2 * x * exp(--((&1 + u pow 2) * x pow 2)))) o drop) =
     (\x:real^1. integral (interval[lift(&0),lift(&1)])
       (\u:real^1. lift(&2 * drop x * exp(--((&1 + drop u pow 2) *
                                             drop x pow 2)))))`
    ASSUME_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:real^1` THEN
   REWRITE_TAC[GSYM INNER_VEC_CONV; LIFT_DROP];
   ALL_TAC] THEN
  (* Step 8: Vector Fubini *)
  SUBGOAL_THEN
    `integral (interval[lift(&0),lift B])
      (\x:real^1. integral (interval[lift(&0),lift(&1)])
        (\u:real^1. lift(&2 * drop x *
          exp(--((&1 + drop u pow 2) * drop x pow 2))))) =
     integral (interval[lift(&0),lift(&1)])
      (\u:real^1. integral (interval[lift(&0),lift B])
        (\x:real^1. lift(&2 * drop x *
          exp(--((&1 + drop u pow 2) * drop x pow 2)))))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL
     [`\x u:real^1. lift(&2 * drop x *
        exp(--((&1 + drop u pow 2) * drop x pow 2)))`;
      `lift(&0):real^1`; `lift(B:real):real^1`;
      `lift(&0):real^1`; `lift(&1):real^1`]
     INTEGRAL_SWAP_CONTINUOUS) THEN
   REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
   DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GAUSS_2D_CONTINUOUS];
   ALL_TAC] THEN
  (* Step 9: Chain everything *)
  ASM_REWRITE_TAC[] THEN
  (* Step 10: Use OUTER_VEC_CONV *)
  REWRITE_TAC[OUTER_VEC_CONV] THEN
  (* Step 11: inner x-integral = k(u) for u in [0,1] *)
  SUBGOAL_THEN
    `!u:real^1. u IN interval[lift(&0), lift(&1)] ==>
     real_integral (real_interval[&0,B])
       (\x. &2 * x * exp(--((&1 + drop u pow 2) * x pow 2))) =
     inv(&1 + drop u pow 2) * (&1 - exp(--((&1 + drop u pow 2) * B pow 2)))`
    ASSUME_TAC THENL
  [X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
   STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   MATCH_MP_TAC INNER_X_INTEGRAL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 12: k integrable on [0,1] *)
  MP_TAC(SPEC `B:real` J_OUTER_INTEGRAND_INTEGRABLE) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
    `(\u. inv(&1 + u pow 2) * (&1 - exp(--((&1 + u pow 2) * B pow 2))))
     real_integrable_on real_interval[&0,&1]`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 13: Get (lift o k o drop) integrable *)
  SUBGOAL_THEN
    `(lift o (\u. inv(&1 + u pow 2) *
       (&1 - exp(--((&1 + u pow 2) * B pow 2)))) o drop)
     integrable_on interval[lift(&0),lift(&1)]`
    ASSUME_TAC THENL
  [MP_TAC(SPEC `B:real` J_OUTER_INTEGRAND_INTEGRABLE) THEN
   REWRITE_TAC[real_integrable_on; has_real_integral;
               IMAGE_LIFT_REAL_INTERVAL; integrable_on] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  (* Get has_integral for (lift o k o drop) *)
  MP_TAC(MATCH_MP INTEGRABLE_INTEGRAL (ASSUME
    `(lift o (\u. inv(&1 + u pow 2) *
       (&1 - exp(--((&1 + u pow 2) * B pow 2)))) o drop)
     integrable_on interval[lift(&0),lift(&1)]`)) THEN
  DISCH_TAC THEN
  (* Pointwise equality on [0,1] *)
  SUBGOAL_THEN
    `!u:real^1. u IN interval[lift(&0),lift(&1)] ==>
     (lift o (\u. inv(&1 + u pow 2) *
       (&1 - exp(--((&1 + u pow 2) * B pow 2)))) o drop) u =
     lift(real_integral (real_interval[&0,B])
       (\x. &2 * x * exp(--((&1 + drop u pow 2) * x pow 2))))`
    ASSUME_TAC THENL
  [X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
   STRIP_TAC THEN REWRITE_TAC[o_THM; LIFT_DROP] THEN
   AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   MATCH_MP_TAC INNER_X_INTEGRAL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Use HAS_INTEGRAL_EQ to transfer *)
  MP_TAC(ISPECL
    [`(lift o (\u. inv(&1 + u pow 2) *
       (&1 - exp(--((&1 + u pow 2) * B pow 2)))) o drop)`;
     `(\u:real^1. lift(real_integral (real_interval[&0,B])
       (\x. &2 * x * exp(--((&1 + drop u pow 2) * x pow 2)))))`;
     `integral (interval[lift(&0),lift(&1)])
       (lift o (\u. inv(&1 + u pow 2) *
         (&1 - exp(--((&1 + u pow 2) * B pow 2)))) o drop)`;
     `interval[lift(&0),lift(&1)]`]
    HAS_INTEGRAL_EQ) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP INTEGRAL_UNIQUE th]) THEN
  (* Step 14: Convert back to real_integral *)
  MP_TAC(MATCH_MP REAL_INTEGRAL (ASSUME
    `(\u. inv(&1 + u pow 2) * (&1 - exp(--((&1 + u pow 2) * B pow 2))))
     real_integrable_on real_interval[&0,&1]`)) THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

(* H_PLUS_J: core identity proved from J_EQUALS_OUTER + ARCTAN_INTEGRAL *)
let H_PLUS_J = prove
 (`!B. &0 < B
   ==> real_integral (real_interval[&0,&1])
         (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2)) +
       real_integral (real_interval[&0,B])
         (\x. exp(--(x pow 2))) pow 2 = pi / &4`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP J_EQUALS_OUTER) THEN
  MP_TAC(ISPECL
    [`\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2)`;
     `\u. inv(&1 + u pow 2) * (&1 - exp(--((&1 + u pow 2) * B pow 2)))`;
     `real_interval[&0,&1]`]
    REAL_INTEGRAL_ADD) THEN
  REWRITE_TAC[H_INTEGRAND_INTEGRABLE; J_OUTER_INTEGRAND_INTEGRABLE] THEN
  DISCH_THEN(SUBST1_TAC o GSYM) THEN
  SUBGOAL_THEN
    `(\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2) +
          inv(&1 + t pow 2) * (&1 - exp(--((&1 + t pow 2) * B pow 2)))) =
     (\t. inv(&1 + t pow 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; INTEGRAND_SUM_EQ_INV]; ALL_TAC] THEN
  MP_TAC ARCTAN_INTEGRAL THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP REAL_INTEGRAL_UNIQUE th]));;

(* Helper lemmas for convergence *)
let IB_NONNEG = prove
 (`!B. &0 <= B ==>
   &0 <= real_integral (real_interval[&0,B]) (\x. exp(--(x pow 2)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_POS THEN
  REWRITE_TAC[EXP_NEG_X2_INTEGRABLE] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  REWRITE_TAC[REAL_EXP_POS_LT]);;

let IB_SQ_EQ = prove
 (`!B. &0 < B ==>
   real_integral (real_interval[&0,B])
     (\x. exp(--(x pow 2))) pow 2 =
   pi / &4 -
   real_integral (real_interval[&0,&1])
     (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `B:real` H_PLUS_J) THEN
  ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let HB_NONNEG = prove
 (`!B. &0 <=
   real_integral (real_interval[&0,&1])
     (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2))`,
  GEN_TAC THEN
  SUBGOAL_THEN
    `(\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2))
     real_integrable_on real_interval[&0,&1]` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
   MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
   REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
   REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC THEN
   MATCH_MP_TAC REAL_LT_IMP_NZ THEN
   MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
   MATCH_MP_TAC REAL_LE_INV THEN
   MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

let SQRT_PI_HALF_SQ = prove
 (`(sqrt(pi) / &2) pow 2 = pi / &4`,
  SUBGOAL_THEN `sqrt(pi) pow 2 = pi` ASSUME_TAC THENL
  [MATCH_MP_TAC SQRT_POW_2 THEN
   MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* Main convergence: I(B) --> sqrt(pi)/2 *)
let HALF_GAUSSIAN_CONVERGES = prove
 (`((\B. real_integral (real_interval[&0,B])
          (\x. exp(--(x pow 2)))) ---> sqrt(pi) / &2) at_posinfinity`,
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(pi) / &2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPEC `e * sqrt(pi) / &2`
    (REWRITE_RULE[REALLIM_AT_POSINFINITY] H_LIMIT_ZERO)) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real` ASSUME_TAC) THEN
  EXISTS_TAC `max (&1) N` THEN
  X_GEN_TAC `B:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `B >= N` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
    `I_B = real_integral (real_interval[&0,B]) (\x. exp(--(x pow 2)))` THEN
  ABBREV_TAC
    `H_B = real_integral (real_interval[&0,&1])
      (\t. exp(--(B pow 2 * (&1 + t pow 2))) * inv(&1 + t pow 2))` THEN
  SUBGOAL_THEN `&0 <= I_B` ASSUME_TAC THENL
  [EXPAND_TAC "I_B" THEN MATCH_MP_TAC IB_NONNEG THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `I_B pow 2 = pi / &4 - H_B` ASSUME_TAC THENL
  [EXPAND_TAC "I_B" THEN EXPAND_TAC "H_B" THEN
   MATCH_MP_TAC IB_SQ_EQ THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= H_B` ASSUME_TAC THENL
  [EXPAND_TAC "H_B" THEN REWRITE_TAC[HB_NONNEG]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(H_B - &0) < e * sqrt(pi) / &2` ASSUME_TAC THENL
  [EXPAND_TAC "H_B" THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `B:real`) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `H_B < e * sqrt(pi) / &2` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt(pi) / &2) pow 2 = pi / &4` ASSUME_TAC THENL
  [REWRITE_TAC[SQRT_PI_HALF_SQ]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(I_B - sqrt(pi) / &2) * (I_B + sqrt(pi) / &2) = --H_B`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
     `(I_B - sqrt(pi) / &2) * (I_B + sqrt(pi) / &2) =
      I_B pow 2 - (sqrt(pi) / &2) pow 2`
     SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(pi) / &2 <= I_B + sqrt(pi) / &2` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < I_B + sqrt(pi) / &2` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `I_B - sqrt(pi) / &2 <= &0` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `~(&0 < x) ==> x <= &0`) THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `&0 < (I_B - sqrt(pi) / &2) * (I_B + sqrt(pi) / &2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(I_B - sqrt(pi) / &2) = sqrt(pi) / &2 - I_B`
    ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(I_B - sqrt(pi) / &2) * (I_B + sqrt(pi) / &2) = H_B`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
     `(sqrt(pi) / &2 - I_B) * (I_B + sqrt(pi) / &2) =
      (sqrt(pi) / &2) pow 2 - I_B pow 2`
     SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `abs(I_B - sqrt(pi) / &2) * (sqrt(pi) / &2) <=
     abs(I_B - sqrt(pi) / &2) * (I_B + sqrt(pi) / &2)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN
   REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `abs(I_B - sqrt(pi) / &2) * (sqrt(pi) / &2) < e * sqrt(pi) / &2`
    ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
  EXISTS_TAC `sqrt(pi) / &2` THEN ASM_REWRITE_TAC[]);;

(* Final assembly: GAUSSIAN_INTEGRAL *)
let GAUSSIAN_INTEGRAL = prove
 (`((\x. exp(--(x pow 2))) has_real_integral sqrt pi) (:real)`,
  REWRITE_TAC[HAS_REAL_INTEGRAL_ALT; IN_UNIV] THEN
  CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[ETA_AX; EXP_NEG_X2_INTEGRABLE];
   ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e / &2`
    (REWRITE_RULE[REALLIM_AT_POSINFINITY] HALF_GAUSSIAN_CONVERGES)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real` ASSUME_TAC) THEN
  EXISTS_TAC `max (&1) N` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `a <= --(max (&1) N) /\ max (&1) N <= b` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC) THEN
   REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a <= b:real` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN
  SUBGOAL_THEN
    `real_integral (real_interval[a,b]) (\x. exp(--(x pow 2))) =
     real_integral (real_interval[a,&0]) (\x. exp(--(x pow 2))) +
     real_integral (real_interval[&0,b]) (\x. exp(--(x pow 2)))`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
   ASM_REWRITE_TAC[EXP_NEG_X2_INTEGRABLE] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `real_integral (real_interval[a,&0]) (\x. exp(--(x pow 2))) =
     real_integral (real_interval[&0,--a]) (\x. exp(--(x pow 2)))`
    SUBST1_TAC THENL
  [MP_TAC(ISPECL [`\x:real. exp(--(x pow 2))`;
                   `real_interval[&0,--a]`]
     REAL_INTEGRAL_REFLECT_GEN) THEN
   SIMP_TAC[] THEN
   SUBGOAL_THEN `(!x:real. exp(--((--x) pow 2)) = exp(--(x pow 2)))`
     (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_POW_NEG; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `IMAGE (--) (real_interval[&0,--a]) = real_interval[a,&0]`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
    [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
     STRIP_TAC THEN EXISTS_TAC `--y:real` THEN ASM_REAL_ARITH_TAC];
    SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN `--a >= N` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b >= N` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `abs(real_integral (real_interval[&0,--a])
           (\x. exp(--(x pow 2))) - sqrt(pi) / &2) < e / &2`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `--a:real`) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `abs(real_integral (real_interval[&0,b])
           (\x. exp(--(x pow 2))) - sqrt(pi) / &2) < e / &2`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `sqrt pi = sqrt(pi) / &2 + sqrt(pi) / &2`
    SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Scaled Gaussian integral: integrate exp(-at^2/2) over all of R *)
let GAUSSIAN_INTEGRAL_SCALED = prove
 (`!a. &0 < a
   ==> ((\t. exp(--(a * t pow 2 / &2))) has_real_integral
        sqrt(&2 * pi / a)) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(a / &2)` ASSUME_TAC THENL
  [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Replace the result with the equivalent form *)
  SUBGOAL_THEN `sqrt(&2 * pi / a) = inv(sqrt(a / &2)) * sqrt pi`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN
   ONCE_REWRITE_TAC[GSYM SQRT_INV] THEN
   REWRITE_TAC[GSYM SQRT_MUL] THEN AP_TERM_TAC THEN
   UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  (* Show integrands are equal up to substitution *)
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\x:real. exp(--((sqrt(a / &2) * x) pow 2))` THEN
  CONJ_TAC THENL
  [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_UNIV] THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_MUL] THEN
   ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_DIV; REAL_LT_IMP_LE;
                REAL_ARITH `&0 < &2`] THEN
   REAL_ARITH_TAC;
   (* Apply the stretching lemma to the Gaussian integral *)
   MATCH_MP_TAC HAS_REAL_INTEGRAL_STRETCH_UNIV THEN
   ASM_REWRITE_TAC[GAUSSIAN_INTEGRAL]]);;

(* Gaussian * cosine is integrable *)
let GAUSSIAN_COS_INTEGRABLE = prove
 (`!a b. &0 < a
   ==> (\t. exp(--(a * t pow 2 / &2)) * cos(b * t))
       real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\t:real. exp(--(a * t pow 2 / &2))` THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
   MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
   REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
   REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
   REWRITE_TAC[real_integrable_on] THEN
   EXISTS_TAC `sqrt(&2 * pi / a)` THEN
   ASM_SIMP_TAC[GAUSSIAN_INTEGRAL_SCALED];
   GEN_TAC THEN REWRITE_TAC[IN_UNIV; REAL_ABS_MUL] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `exp(--(a * x pow 2 / &2)) * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; COS_BOUND] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`; REAL_EXP_POS_LE];
    REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]]]);;

(* y * exp(-y) <= 1 for y >= 0 *)
let REAL_EXP_DECAY_BOUND = prove
 (`!y. &0 <= y ==> y * exp(--y) <= &1`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp y * exp(--y)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
   MP_TAC(SPEC `y:real` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
   REWRITE_TAC[GSYM REAL_EXP_ADD] THEN
   SUBGOAL_THEN `y + --y = &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; REWRITE_TAC[REAL_EXP_0; REAL_LE_REFL]]]);;

(* Pointwise bound: x^2 * exp(-ax^2/2) <= (4/a) * exp(-(a/2)*x^2/2) *)
(* Proof: split exp(-ax^2/2) = exp(-ax^2/4)^2, cancel one factor,    *)
(* then x^2*exp(-ax^2/4) = (4/a)*((ax^2/4)*exp(-ax^2/4)) <= 4/a     *)
(* by REAL_EXP_DECAY_BOUND.                                          *)
(* NOTE: / has higher precedence than * in HOL Light, so              *)
(* a * x pow 2 / &4 parses as a * (x^2/4), NOT (a*x^2)/4.           *)
let GAUSSIAN_T2_POINTWISE_BOUND = prove
 (`!a x. &0 < a
   ==> x pow 2 * exp(--(a * x pow 2 / &2)) <=
       (&4 / a) * exp(--((a / &2) * x pow 2 / &2))`,
  REPEAT STRIP_TAC THEN
  (* Simplify RHS exponent: (a/2)*x^2/2 = a*x^2/4 *)
  SUBGOAL_THEN `(a / &2) * x pow 2 / &2 = a * x pow 2 / &4`
    (fun th -> REWRITE_TAC[th]) THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  (* Split exp(-ax^2/2) = exp(-ax^2/4) * exp(-ax^2/4) *)
  SUBGOAL_THEN `exp(--(a * x pow 2 / &2)) =
                exp(--(a * x pow 2 / &4)) * exp(--(a * x pow 2 / &4))`
    SUBST1_TAC THENL
  [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Reassociate: x^2 * (e * e) = (x^2 * e) * e *)
  ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN
  (* Cancel exp(-ax^2/4) from both sides *)
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
  [ALL_TAC; REWRITE_TAC[REAL_EXP_POS_LE]] THEN
  (* Goal: x^2 * exp(-ax^2/4) <= 4/a *)
  (* Key step: x^2*e = (4/a) * ((a*(x^2/4)) * e), then use DECAY_BOUND *)
  (* Note: a * x pow 2 / &4 parses as a * (x^2/4) in HOL Light       *)
  SUBGOAL_THEN `x pow 2 * exp(--(a * x pow 2 / &4)) =
                (&4 / a) *
                ((a * x pow 2 / &4) * exp(--(a * x pow 2 / &4)))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `~(a = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  (* Goal: (4/a) * ((a*(x^2/4)) * exp(-ax^2/4)) <= 4/a *)
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_IMP_LE THEN
   MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
   (* Goal: (a*(x^2/4))*exp(--(a*(x^2/4))) <= 1 *)
   MATCH_MP_TAC REAL_EXP_DECAY_BOUND THEN
   (* Goal: 0 <= a * (x^2/4) *)
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC]]);;

(* t^2 * Gaussian is integrable *)
let GAUSSIAN_T2_INTEGRABLE = prove
 (`!a. &0 < a
   ==> (\t. t pow 2 * exp(--(a * t pow 2 / &2)))
       real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\t:real. (&4 / a) * exp(--((a / &2) * t pow 2 / &2))` THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
   MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
   REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
   REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
   MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
   REWRITE_TAC[real_integrable_on] THEN
   EXISTS_TAC `sqrt(&2 * pi / (a / &2))` THEN
   MATCH_MP_TAC GAUSSIAN_INTEGRAL_SCALED THEN ASM_REAL_ARITH_TAC;
   GEN_TAC THEN REWRITE_TAC[IN_UNIV] THEN
   SUBGOAL_THEN `abs(x pow 2 * exp(--(a * x pow 2 / &2))) =
                  x pow 2 * exp(--(a * x pow 2 / &2))`
     SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_EXP_POS_LE]; ALL_TAC] THEN
   ASM_SIMP_TAC[GAUSSIAN_T2_POINTWISE_BOUND]]);;

(* Helper: |x| <= 1 + x^2 *)
let ABS_LE_1_PLUS_POW2 = prove
 (`!x:real. abs x <= &1 + x pow 2`,
  GEN_TAC THEN
  DISJ_CASES_TAC (SPEC `abs(x:real)` (REAL_ARITH `!u. u <= &1 \/ &1 <= u`)) THENL
  [MP_TAC (SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs x * abs x` THEN
   CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_POW_2; REAL_POW2_ABS] THEN
    MP_TAC (SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]]);;

(* t * Gaussian * sin is integrable *)
(* Dominator: exp(-at^2/2) + t^2*exp(-at^2/2) since |t|*exp <= (1+t^2)*exp *)
let GAUSSIAN_T_SIN_INTEGRABLE = prove
 (`!a b. &0 < a
   ==> (\t. t * exp(--(a * t pow 2 / &2)) * sin(b * t))
       real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\t:real. exp(--(a * t pow 2 / &2)) +
                       t pow 2 * exp(--(a * t pow 2 / &2))` THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
   MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
   REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
   REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
   MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN CONJ_TAC THENL
   [REWRITE_TAC[real_integrable_on] THEN
    EXISTS_TAC `sqrt(&2 * pi / a)` THEN
    ASM_SIMP_TAC[GAUSSIAN_INTEGRAL_SCALED];
    ASM_SIMP_TAC[GAUSSIAN_T2_INTEGRABLE]];
   GEN_TAC THEN REWRITE_TAC[IN_UNIV] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `abs x * exp(--(a * x pow 2 / &2))` THEN CONJ_TAC THENL
   [(* |t*exp*sin| <= |t|*exp: simplify abs, factor, use |sin| <= 1 *)
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(exp(--(a * x pow 2 / &2))) = exp(--(a * x pow 2 / &2))`
      SUBST1_TAC THENL
    [REWRITE_TAC[REAL_ABS_REFL; REAL_EXP_POS_LE]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE; SIN_BOUND];
    (* |t|*exp <= (1+t^2)*exp = exp + t^2*exp *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + x pow 2) * exp(--(a * x pow 2 / &2))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[ABS_LE_1_PLUS_POW2]; REWRITE_TAC[REAL_EXP_POS_LE]];
     REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID; REAL_LE_REFL]]]]);;

(* Taylor bound for cosine: |cos(x+h) - cos(x) + h*sin(x)| <= h^2 *)
let COS_TAYLOR2_BOUND = prove
 (`!x h. abs(cos(x + h) - cos x + h * sin x) <= h pow 2`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL
    [`\(i:num) (t:real).
       if i = 0 then cos t
       else if i = 1 then --(sin t)
       else --(cos t)`;
     `1`; `(:real)`; `&1`] REAL_TAYLOR) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [(* Derivative conditions for i <= 1 *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 0 \/ i = 1` DISJ_CASES_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; ARITH_RULE `1 + 1 = 2`;
                     ARITH_RULE `0 = 0 <=> T`; ARITH_RULE `1 = 0 <=> F`;
                     ARITH_RULE `1 = 1 <=> T`; ARITH_RULE `~(2 = 0)`;
                     ARITH_RULE `~(2 = 1)`] THEN
    REWRITE_TAC[WITHINREAL_UNIV] THENL
    [(* i=0: cos has_real_derivative --sin *)
     REWRITE_TAC[ETA_AX; HAS_REAL_DERIVATIVE_COS];
     (* i=1: (\t. --sin t) has_real_derivative --cos *)
     MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
     REWRITE_TAC[ETA_AX; HAS_REAL_DERIVATIVE_SIN]];
    (* Bound: |--cos(u)| <= 1 *)
    X_GEN_TAC `u:real` THEN
    REWRITE_TAC[ARITH_RULE `1 + 1 = 2`; ARITH_RULE `~(2 = 0)`;
                 ARITH_RULE `~(2 = 1)`] THEN
    REWRITE_TAC[REAL_ABS_NEG; COS_BOUND]];
   ALL_TAC] THEN
  (* Apply with w=x, z=x+h *)
  DISCH_THEN (MP_TAC o SPECL [`x:real`; `x + h:real`]) THEN
  REWRITE_TAC[REAL_ARITH `(x + h) - x = h:real`] THEN
  (* Simplify sum(0..1) *)
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_SING_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[FACT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CONJUNCT1 real_pow; REAL_POW_1; REAL_MUL_LID; REAL_MUL_RID;
              REAL_DIV_1; REAL_ADD_RID] THEN
  (* Hypothesis: abs(cos(x+h) - (cos x + --sin x * h)) <= abs h pow 2 / &2
     Goal: abs(cos(x+h) - cos x + h * sin x) <= h pow 2 *)
  DISCH_TAC THEN
  SUBGOAL_THEN `cos(x + h) - cos x + h * sin x =
                cos(x + h) - (cos x + --(sin x) * h)` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs h pow 2 / &2` THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   SUBGOAL_THEN `abs h pow 2 = h pow 2` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_ABS_POW] THEN
    REWRITE_TAC[REAL_ABS_REFL; REAL_LE_POW_2]; ALL_TAC] THEN
   MP_TAC (SPEC `h:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

(* General bound on the antiderivative *)
let GAUSSIAN_ANTIDERIV_BOUND = prove
 (`!a b t. &0 < a
   ==> abs(--inv(a) * exp(--(a * t pow 2 / &2)) * sin(b * t))
       <= inv(a) * exp(--(a * t pow 2 / &2))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN
  SUBGOAL_THEN `abs(inv a) = inv a` SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_INV THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(exp(--(a * t pow 2 / &2))) = exp(--(a * t pow 2 / &2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_REFL; REAL_EXP_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
   GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN
   REWRITE_TAC[REAL_EXP_POS_LE; SIN_BOUND]]);;

(* Helper: derivative of the antiderivative F(t) = --inv(a)*exp(-at^2/2)*sin(bt) *)
let GAUSSIAN_FT_ANTIDERIV_DERIV = prove
 (`!a b t. &0 < a ==>
   ((\t. --inv(a) * exp(--(a * t pow 2 / &2)) * sin(b * t))
    has_real_derivative
    (t * exp(--(a * t pow 2 / &2)) * sin(b * t) -
     b / a * exp(--(a * t pow 2 / &2)) * cos(b * t)))
   (atreal t)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD);;

(* For x > 0, exp(-x) < inv(x). Used for the IBP antiderivative decay. *)
let REAL_EXP_NEG_LT_INV = prove
 (`!x. &0 < x ==> exp(--x) < inv x`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `x < exp(x)` MP_TAC THENL
  [MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
   DISCH_TAC THEN REWRITE_TAC[REAL_EXP_NEG] THEN
   MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[]]);;

(* For large |t|, inv(a)*exp(-a*t^2/2) is arbitrarily small *)
let GAUSSIAN_EXP_DECAY = prove
 (`!a e. &0 < a /\ &0 < e
   ==> ?B. &0 < B /\
           !t. B <= abs(t) ==> inv(a) * exp(--(a * t pow 2 / &2)) < e`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(&1 + &2 / ((a:real) pow 2 * (e:real))):real` THEN
  ABBREV_TAC `B = (&1 + &2 / ((a:real) pow 2 * (e:real))):real` THEN
  SUBGOAL_THEN `&0 < (a:real) pow 2 * (e:real)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL
  [EXPAND_TAC "B" THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
   MATCH_MP_TAC REAL_LE_DIV THEN
   ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL
  [UNDISCH_TAC `&1 <= B` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `&0 < B` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `B pow 2 <= t pow 2` ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
   MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_POS];
    UNDISCH_TAC `&0 < B` THEN UNDISCH_TAC `B <= abs(t)` THEN
    REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `B <= B pow 2` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN
   GEN_REWRITE_TAC (LAND_CONV) [GSYM REAL_MUL_RID] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < B` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&1 <= B` THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a:real) * (B:real) / &2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
    [UNDISCH_TAC `&0 < B` THEN REAL_ARITH_TAC;
     REAL_ARITH_TAC]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a:real) * (e:real)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN
   UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Step 1: Establish B <= t^2 *)
  SUBGOAL_THEN `(B:real) <= t pow 2` ASSUME_TAC THENL
  [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  (* Step 2: Part 1 - inv(a)*exp(-at^2/2) <= inv(a)*exp(-aB/2) *)
  SUBGOAL_THEN
    `inv((a:real)) * exp(--(a * t pow 2 / &2)) <=
     inv(a) * exp(--(a * (B:real) / &2))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &2`;
                 REAL_LE_LMUL_EQ]];
   ALL_TAC] THEN
  (* Step 3: Part 2 - inv(a)*exp(-aB/2) < e *)
  SUBGOAL_THEN `~((a:real) = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((e:real) = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv((a:real) * e) <= a * B / &2` ASSUME_TAC THENL
  [EXPAND_TAC "B" THEN
   SUBGOAL_THEN
     `(a:real) * (&1 + &2 / (a pow 2 * e)) / &2 = a / &2 + inv(a * e)`
     SUBST1_TAC THENL
   [UNDISCH_TAC `~((a:real) = &0)` THEN
    UNDISCH_TAC `~((e:real) = &0)` THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> y <= x + y`) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN `exp(--((a:real) * B / &2)) < a * e` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_TRANS THEN
   EXISTS_TAC `inv((a:real) * B / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EXP_NEG_LT_INV THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(inv((a:real) * e))` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
     REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL]]];
   ALL_TAC] THEN
  (* Step 4: Combine via REAL_LET_TRANS *)
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(inv((a:real)) * exp(--((a:real) * (B:real) / &2))):real` THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   SUBGOAL_THEN `(e:real) = inv(a) * (a * e)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID];
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]]]]);;

(* IBP identity: integral of t * exp(-at^2/2) * sin(bt) = (b/a) * I(b) *)
(* Proof: F(t) = --inv(a)*exp(-at^2/2)*sin(bt) has derivative = integrand, *)
(* F -> 0 at infinity, so by FTC + HAS_REAL_INTEGRAL_ALT, integral F' = 0  *)
let GAUSSIAN_FT_IBP = prove
 (`!a b. &0 < a
   ==> real_integral (:real) (\t. t * exp(--(a * t pow 2 / &2)) * sin(b * t)) =
       (b / a) * real_integral (:real) (\t. exp(--(a * t pow 2 / &2)) * cos(b * t))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f = \t:real. t * exp(--(a * t pow 2 / &2)) * sin(b * t)` THEN
  ABBREV_TAC `g = \t:real. exp(--(a * t pow 2 / &2)) * cos(b * t)` THEN
  ABBREV_TAC `Fa = \t:real. --inv(a) * exp(--(a * t pow 2 / &2)) * sin(b * t)` THEN
  (* Step 1: Both integrands are integrable *)
  SUBGOAL_THEN `(f:real->real) real_integrable_on (:real)` ASSUME_TAC THENL
  [EXPAND_TAC "f" THEN ASM_SIMP_TAC[GAUSSIAN_T_SIN_INTEGRABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real->real) real_integrable_on (:real)` ASSUME_TAC THENL
  [EXPAND_TAC "g" THEN ASM_SIMP_TAC[GAUSSIAN_COS_INTEGRABLE]; ALL_TAC] THEN
  (* Step 2: Fa'(t) = f(t) - (b/a)*g(t) everywhere *)
  SUBGOAL_THEN
    `!t. ((Fa:real->real) has_real_derivative
          ((f:real->real) t - b / a * (g:real->real) t)) (atreal t)`
    ASSUME_TAC THENL
  [X_GEN_TAC `t:real` THEN EXPAND_TAC "f" THEN EXPAND_TAC "g" THEN
   EXPAND_TAC "Fa" THEN ASM_SIMP_TAC[GAUSSIAN_FT_ANTIDERIV_DERIV];
   ALL_TAC] THEN
  (* Step 3: |Fa(t)| <= inv(a) * exp(-at^2/2) *)
  SUBGOAL_THEN
    `!t. abs((Fa:real->real) t) <= inv(a) * exp(--(a * t pow 2 / &2))`
    ASSUME_TAC THENL
  [X_GEN_TAC `t:real` THEN EXPAND_TAC "Fa" THEN
   ASM_SIMP_TAC[GAUSSIAN_ANTIDERIV_BOUND];
   ALL_TAC] THEN
  (* Step 4: Fa' is integrable on every finite interval *)
  SUBGOAL_THEN
    `!c d. (\t. (f:real->real) t - b / a * (g:real->real) t)
           real_integrable_on real_interval[c,d]`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
   ALL_TAC] THEN
  (* Step 5: FTC on [c,d] gives integral = Fa(d) - Fa(c) *)
  SUBGOAL_THEN
    `!c d. c <= d ==>
     ((\t. (f:real->real) t - b / a * (g:real->real) t)
      has_real_integral ((Fa:real->real) d - Fa c)) (real_interval[c,d])`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR THEN
   ASM_REWRITE_TAC[] THEN
   EXPAND_TAC "Fa" THEN
   MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
   REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
   REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
   ALL_TAC] THEN
  (* Step 6: integral value on [c,d] when c <= d *)
  SUBGOAL_THEN
    `!c d. c <= d ==>
     real_integral (real_interval[c,d])
       (\t. (f:real->real) t - b / a * (g:real->real) t) =
     (Fa:real->real) d - Fa c`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* Step 7: (h has_real_integral 0) on (:real) *)
  (* Use: Fa(t) -> 0 as |t| -> infinity, so integral -> 0 *)
  SUBGOAL_THEN
    `((\t. (f:real->real) t - b / a * (g:real->real) t)
      has_real_integral (&0)) (:real)`
    ASSUME_TAC THENL
  [REWRITE_TAC[HAS_REAL_INTEGRAL_ALT; IN_UNIV; REAL_SUB_RZERO] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
   X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   (* Use decay lemma: Fa -> 0 at infinity *)
   MP_TAC(SPECL [`a:real`; `e / &2`] GAUSSIAN_EXP_DECAY) THEN
   ASM_REWRITE_TAC[REAL_HALF] THEN
   DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
   MAP_EVERY X_GEN_TAC [`c:real`; `d:real`] THEN DISCH_TAC THEN
   SUBGOAL_THEN `c <= --B /\ B <= d` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_REAL_INTERVAL]) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c <= d:real` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH
     `abs d < e / &2 /\ abs c < e / &2 ==> abs(d - c) < e`) THEN
   CONJ_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THENL
   [EXISTS_TAC `inv(a) * exp(--(a * d pow 2 / &2))`;
    EXISTS_TAC `inv(a) * exp(--(a * c pow 2 / &2))`] THEN
   (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Conclude: real_integral f = b/a * real_integral g *)
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_UNIQUE THEN
  EXISTS_TAC `\t. (f:real->real) t - b / a * (g:real->real) t` THEN
  EXISTS_TAC `(:real)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[]];
   ASM_REWRITE_TAC[]]);;

(* Differentiation under the integral for the Gaussian cosine integral.    *)
(* Key step: Taylor bound |cos(x+h)-cos(x)+h*sin(x)| <= h^2 gives        *)
(* |I(y)-I(b)-l*(y-b)| <= (y-b)^2 * C where C = integral t^2*exp(-at^2/2) *)
let GAUSSIAN_COS_INTEGRAL_HAS_DERIV = prove
 (`!a b. &0 < a ==>
   ((\b. real_integral (:real) (\t. exp(--(a * t pow 2 / &2)) * cos(b * t)))
    has_real_derivative
    (--(real_integral (:real)
      (\t. t * exp(--(a * t pow 2 / &2)) * sin(b * t)))))
   (atreal b)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
    `C = real_integral (:real)
      (\t. t pow 2 * exp(--(a * t pow 2 / &2)))` THEN
  (* C >= 0 *)
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
  [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
   ASM_SIMP_TAC[GAUSSIAN_T2_INTEGRABLE; IN_UNIV] THEN GEN_TAC THEN
   MATCH_MP_TAC REAL_LE_MUL THEN
   REWRITE_TAC[REAL_LE_POW_2; REAL_EXP_POS_LE];
   ALL_TAC] THEN
  (* Key error bound: |I(y)-I(b)+(y-b)*integral(t*exp*sin)| <= (y-b)^2*C *)
  SUBGOAL_THEN
    `!y. abs(real_integral (:real)
             (\t. exp(--(a * t pow 2 / &2)) * cos(y * t)) -
            real_integral (:real)
             (\t. exp(--(a * t pow 2 / &2)) * cos(b * t)) +
            (y - b) * real_integral (:real)
             (\t. t * exp(--(a * t pow 2 / &2)) * sin(b * t)))
        <= (y - b) pow 2 * C`
    ASSUME_TAC THENL
  [X_GEN_TAC `y:real` THEN
   (* Establish integrability assumptions *)
   SUBGOAL_THEN
     `(\t. exp(--(a * t pow 2 / &2)) * cos(y * t))
      real_integrable_on (:real) /\
      (\t. exp(--(a * t pow 2 / &2)) * cos(b * t))
      real_integrable_on (:real) /\
      (\t. t * exp(--(a * t pow 2 / &2)) * sin(b * t))
      real_integrable_on (:real)`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GAUSSIAN_COS_INTEGRABLE; GAUSSIAN_T_SIN_INTEGRABLE];
    ALL_TAC] THEN
   (* Express error as single integral *)
   SUBGOAL_THEN
     `real_integral (:real)
        (\t. exp(--(a * t pow 2 / &2)) * cos(y * t)) -
      real_integral (:real)
        (\t. exp(--(a * t pow 2 / &2)) * cos(b * t)) +
      (y - b) * real_integral (:real)
        (\t. t * exp(--(a * t pow 2 / &2)) * sin(b * t)) =
      real_integral (:real)
        (\t. exp(--(a * t pow 2 / &2)) *
             (cos(y * t) - cos(b * t) + (y - b) * t * sin(b * t)))`
     SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_INTEGRAL_SUB] THEN
    SUBGOAL_THEN
      `(y - b) * real_integral (:real)
        (\t. t * exp(--(a * t pow 2 / &2)) * sin(b * t)) =
       real_integral (:real)
        (\t. (y - b) * (t * exp(--(a * t pow 2 / &2)) * sin(b * t)))`
      SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_ADD; REAL_INTEGRABLE_SUB;
                  REAL_INTEGRABLE_LMUL] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
   (* Bound via REAL_INTEGRAL_ABS_BOUND_INTEGRAL *)
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `real_integral (:real)
     (\t. (y - b) pow 2 *
          (t pow 2 * exp(--(a * t pow 2 / &2))))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    CONJ_TAC THENL
    [(* Integrability of error integrand *)
     SUBGOAL_THEN
       `(\t. exp(--(a * t pow 2 / &2)) *
             (cos(y * t) - cos(b * t) + (y - b) * t * sin(b * t))) =
        (\t. (exp(--(a * t pow 2 / &2)) * cos(y * t) -
              exp(--(a * t pow 2 / &2)) * cos(b * t)) +
             (y - b) * (t * exp(--(a * t pow 2 / &2)) * sin(b * t)))`
       SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
     MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[]];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [(* Integrability of bound function *)
     MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
     ASM_SIMP_TAC[GAUSSIAN_T2_INTEGRABLE];
     ALL_TAC] THEN
    (* Pointwise bound *)
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_UNIV] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_EXP] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `exp(--(a * t pow 2 / &2)) *
       ((y - b:real) pow 2 * t pow 2)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
     MP_TAC(SPECL [`b * t:real`; `(y - b) * t:real`]
       COS_TAYLOR2_BOUND) THEN
     REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN
     REWRITE_TAC[REAL_ARITH `b + y - b:real = y`] THEN
     REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
     REAL_ARITH_TAC];
    (* Simplify bound integral to (y-b)^2 * C *)
    EXPAND_TAC "C" THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; GAUSSIAN_T2_INTEGRABLE] THEN
    REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* Convert to limit form *)
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `e / (C + &1)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y - b = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Rewrite: quotient - l = error / (y - b) *)
  SUBGOAL_THEN
    `(real_integral (:real)
       (\t. exp(--(a * t pow 2 / &2)) * cos(y * t)) -
      real_integral (:real)
       (\t. exp(--(a * t pow 2 / &2)) * cos(b * t))) /
     (y - b) -
     (--(real_integral (:real)
       (\t. t * exp(--(a * t pow 2 / &2)) * sin(b * t))))
     = (real_integral (:real)
         (\t. exp(--(a * t pow 2 / &2)) * cos(y * t)) -
        real_integral (:real)
         (\t. exp(--(a * t pow 2 / &2)) * cos(b * t)) +
        (y - b) * real_integral (:real)
         (\t. t * exp(--(a * t pow 2 / &2)) * sin(b * t))) /
       (y - b)`
    SUBST1_TAC THENL
  [UNDISCH_TAC `~(y - b = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  (* Apply bound: abs(error/(y-b)) <= abs(y-b)*C < e *)
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(y - b) * C` THEN CONJ_TAC THENL
  [(* abs(error/(y-b)) <= abs(y-b)*C *)
   REWRITE_TAC[REAL_ABS_DIV] THEN
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `(y - b:real) pow 2 * C` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o SPEC `y:real`);
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC];
   (* abs(y-b)*C < e *)
   MATCH_MP_TAC REAL_LTE_TRANS THEN
   EXISTS_TAC `abs(y - b) * (C + &1)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LMUL; REAL_ARITH `C < C + &1`]; ALL_TAC] THEN
   SUBGOAL_THEN `~(C + &1 = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
     `abs(y - b) * (C + &1) <= e / (C + &1) * (C + &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE;
                 REAL_ARITH `&0 <= x ==> &0 <= x + &1`];
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LE_REFL]]]
  );;

(* GAUSSIAN_COS_INTEGRAL_HAS_DERIV_REAL: alternative proof sketch, not needed.
   The proved GAUSSIAN_COS_INTEGRAL_HAS_DERIV (above) suffices.
   Keeping a brief note instead of the full commented-out proof attempt. *)

(* If x * e = c and e != 0, then x = c * inv(e) *)
let REAL_EQ_RDIV_CANCEL = prove
 (`!(x:real) c e. ~(e = &0) /\ x * e = c ==> x = c * inv e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_RID]);;

(* Zero derivative on all reals means constant *)
let HAS_REAL_DERIVATIVE_ZERO_CONSTANT = prove
 (`!f c (a:real).
    f a = c /\
    (!x. (f has_real_derivative (&0)) (atreal x))
    ==> !x. f x = c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->real`; `(:real)`; `c:real`; `a:real`]
    HAS_REAL_DERIVATIVE_ZERO_UNIQUE) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real` THEN
  REWRITE_TAC[WITHINREAL_UNIV] THEN
  ASM_REWRITE_TAC[]);;

(* Gaussian Fourier Transform (cosine part) *)
(* Proof strategy: ODE approach. Show F(b) = I(b)*exp(b^2/(2a)) is constant *)
(* by proving I'(b) = -(b/a)*I(b) using Taylor error + IBP identity,        *)
(* then MVT shows F is constant, and F(0) = sqrt(2pi/a).                    *)
let GAUSSIAN_FT = prove
 (`!a b. &0 < a
   ==> ((\t. exp(--(a * t pow 2 / &2)) * cos(b * t)) has_real_integral
        sqrt(&2 * pi / a) * exp(--(b pow 2 / (&2 * a)))) (:real)`,
  REPEAT STRIP_TAC THEN
  (* The function is integrable *)
  SUBGOAL_THEN
    `(\t. exp(--(a * t pow 2 / &2)) * cos(b * t)) real_integrable_on (:real)`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[GAUSSIAN_COS_INTEGRABLE]; ALL_TAC] THEN
  (* Suffices to show the integral value equals the RHS *)
  SUBGOAL_THEN
    `real_integral (:real) (\t. exp(--(a * t pow 2 / &2)) * cos(b * t)) =
     sqrt(&2 * pi / a) * exp(--(b pow 2 / (&2 * a)))`
    (fun th -> ASM_MESON_TAC[th; REAL_INTEGRABLE_INTEGRAL;
       HAS_REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL]) THEN
  (* Abbreviate I(b) *)
  ABBREV_TAC `Ib = \u:real. real_integral (:real)
    (\t. exp(--(a * t pow 2 / &2)) * cos(u * t))` THEN
  SUBGOAL_THEN `real_integral (:real)
    (\t. exp(--(a * t pow 2 / &2)) * cos(b * t)) = (Ib:real->real) b`
    SUBST1_TAC THENL
  [EXPAND_TAC "Ib" THEN REWRITE_TAC[]; ALL_TAC] THEN
  (* Abbreviate F(b) *)
  ABBREV_TAC `Fb = \u:real. (Ib:real->real) u * exp(u pow 2 / (&2 * a))` THEN
  (* Step 1: Ib(0) = sqrt(2pi/a) *)
  SUBGOAL_THEN `(Ib:real->real) (&0) = sqrt(&2 * pi / a)` ASSUME_TAC THENL
  [EXPAND_TAC "Ib" THEN
   REWRITE_TAC[REAL_MUL_LZERO; COS_0; REAL_MUL_RID] THEN
   ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE; GAUSSIAN_INTEGRAL_SCALED]; ALL_TAC] THEN
  (* Step 2: Fb(0) = sqrt(2pi/a) *)
  SUBGOAL_THEN `(Fb:real->real) (&0) = sqrt(&2 * pi / a)` ASSUME_TAC THENL
  [EXPAND_TAC "Fb" THEN
   REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_MUL_LZERO; real_div;
               REAL_MUL_LZERO; REAL_EXP_0; REAL_MUL_RID] THEN
   REWRITE_TAC[GSYM real_div] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Step 3: Fb has derivative 0 everywhere *)
  SUBGOAL_THEN
    `!x:real. ((Fb:real->real) has_real_derivative (&0)) (atreal x)`
    ASSUME_TAC THENL
  [X_GEN_TAC `u:real` THEN EXPAND_TAC "Fb" THEN
   (* Step 3a-0: IBP identity *)
   SUBGOAL_THEN
     `real_integral (:real)
       (\t. t * exp(--(a * t pow 2 / &2)) * sin(u * t)) =
      u / a * (Ib:real->real) u` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GAUSSIAN_FT_IBP] THEN
    EXPAND_TAC "Ib" THEN REWRITE_TAC[];
    ALL_TAC] THEN
   (* Step 3a-i: derivative of Ib via differentiation under integral *)
   SUBGOAL_THEN
     `((Ib:real->real) has_real_derivative
      (--real_integral (:real)
         (\t. t * exp(--(a * t pow 2 / &2)) * sin(u * t))))
      (atreal u)` ASSUME_TAC THENL
   [EXPAND_TAC "Ib" THEN ASM_SIMP_TAC[GAUSSIAN_COS_INTEGRAL_HAS_DERIV];
    ALL_TAC] THEN
   (* Step 3a-i': combine: Ib' = -(u/a * Ib u) *)
   SUBGOAL_THEN
     `((Ib:real->real) has_real_derivative
       (--(u / a * (Ib:real->real) u))) (atreal u)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   (* Step 3a-ii: derivative of exp(u^2/(2a)) at u *)
   SUBGOAL_THEN
     `((\u:real. exp(u pow 2 / (&2 * a))) has_real_derivative
       (u / a * exp(u pow 2 / (&2 * a)))) (atreal u)` ASSUME_TAC THENL
   [REAL_DIFF_TAC THEN
    UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   (* Step 3a-iii: product rule + cancellation *)
   SUBGOAL_THEN
     `&0 = (Ib:real->real) u * (u / a * exp(u pow 2 / (&2 * a))) +
           (--(u / a * (Ib:real->real) u)) * exp(u pow 2 / (&2 * a))`
     SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3b: Fb is constant *)
  SUBGOAL_THEN `!x:real. (Fb:real->real) x = Fb (&0)` ASSUME_TAC THENL
  [ASM_MESON_TAC[HAS_REAL_DERIVATIVE_ZERO_CONSTANT]; ALL_TAC] THEN
  (* Step 4: derive Ib(b) = sqrt(2pi/a) * exp(-b^2/(2a)) *)
  (* Rewrite exp(--x) = inv(exp x) so MATCH_MP_TAC can find e *)
  REWRITE_TAC[REAL_EXP_NEG] THEN
  MATCH_MP_TAC REAL_EQ_RDIV_CANCEL THEN
  CONJ_TAC THENL
  [REWRITE_TAC[REAL_EXP_NZ]; ALL_TAC] THEN
  (* Goal: Ib b * exp(b^2/(2a)) = sqrt(2pi/a) *)
  (* This is Fb(b) which equals Fb(0) = sqrt(2pi/a) *)
  SUBGOAL_THEN `(Ib:real->real) b * exp(b pow 2 / (&2 * a)) = (Fb:real->real) b`
    SUBST1_TAC THENL
  [EXPAND_TAC "Fb" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* Gaussian Fourier Transform (sine part = 0 by odd symmetry) *)

let GAUSSIAN_FT_SIN = prove
 (`!a b. &0 < a
   ==> ((\t. exp(--(a * t pow 2 / &2)) * sin(b * t)) has_real_integral
        &0) (:real)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f = \t:real. exp(--(a * t pow 2 / &2)) * sin(b * t)` THEN
  (* f is integrable: measurable + bounded by integrable Gaussian *)
  SUBGOAL_THEN `f real_integrable_on (:real)` ASSUME_TAC THENL
  [EXPAND_TAC "f" THEN
   MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
   EXISTS_TAC `\t:real. exp(--(a * t pow 2 / &2))` THEN REPEAT CONJ_TAC THENL
   [(* measurable: differentiable => continuous => measurable *)
    MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
    (* majorant is integrable *)
    REWRITE_TAC[real_integrable_on] THEN
    EXISTS_TAC `sqrt(&2 * pi / a)` THEN
    ASM_SIMP_TAC[GAUSSIAN_INTEGRAL_SCALED];
    (* pointwise bound: |f(t)| <= exp(-at^2/2) *)
    GEN_TAC THEN REWRITE_TAC[IN_UNIV; REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(a * x pow 2 / &2)) * &1` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL2 THEN
     REWRITE_TAC[REAL_ABS_POS; SIN_BOUND] THEN
     REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`; REAL_EXP_POS_LE];
     REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]]];
   ALL_TAC] THEN
  (* f has_real_integral (real_integral R f) *)
  SUBGOAL_THEN `(f has_real_integral real_integral (:real) f) (:real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* f is odd: f(-t) = -f(t) *)
  SUBGOAL_THEN `!t:real. (f:real->real)(--t) = --(f t)` ASSUME_TAC THENL
  [EXPAND_TAC "f" THEN GEN_TAC THEN
   REWRITE_TAC[REAL_POW_NEG; ARITH; SIN_NEG; REAL_MUL_RNEG]; ALL_TAC] THEN
  (* By reflection + oddness: (\t. -f(t)) has_real_integral I *)
  SUBGOAL_THEN `((\t:real. --((f:real->real) t)) has_real_integral
                 real_integral (:real) f) (:real)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:real->real`; `real_integral (:real) (f:real->real)`;
                   `(:real)`] HAS_REAL_INTEGRAL_REFLECT_GEN) THEN
   SUBGOAL_THEN `IMAGE ((--):real->real) (:real) = (:real)` (fun th ->
     REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN GEN_TAC THEN
    EXISTS_TAC `--x:real` THEN REWRITE_TAC[REAL_NEG_NEG]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
  (* By negation: (\t. -f(t)) has_real_integral (-I) *)
  SUBGOAL_THEN `((\t:real. --((f:real->real) t)) has_real_integral
                 --(real_integral (:real) f)) (:real)` ASSUME_TAC THENL
  [MATCH_MP_TAC HAS_REAL_INTEGRAL_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* I = -I => I = 0, then f has_real_integral 0 *)
  SUBGOAL_THEN `real_integral (:real) f = &0` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `x = --x ==> x = &0`) THEN
   ASM_MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE]; ALL_TAC] THEN
  ASM_MESON_TAC[REAL_INTEGRABLE_INTEGRAL]);;

(* --- Phase 2: Standard Normal Distribution --- *)

let std_normal_density = new_definition
  `std_normal_density (x:real) =
   inv(sqrt(&2 * pi)) * exp(--(x pow 2 / &2))`;;

let std_normal_cdf = new_definition
  `std_normal_cdf (x:real) =
   real_integral {t | t <= x} std_normal_density`;;

(* Density is strictly positive *)
let STD_NORMAL_DENSITY_POS = prove
 (`!x. &0 < std_normal_density x`,
  GEN_TAC THEN REWRITE_TAC[std_normal_density] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
   MP_TAC PI_POS THEN REAL_ARITH_TAC;
   REWRITE_TAC[REAL_EXP_POS_LT]]);;

(* Density is non-negative *)
let STD_NORMAL_DENSITY_NONNEG = prove
 (`!x. &0 <= std_normal_density x`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  REWRITE_TAC[STD_NORMAL_DENSITY_POS]);;

(* Density integrates to 1 *)
let STD_NORMAL_DENSITY_INTEGRAL = prove
 (`(std_normal_density has_real_integral &1) (:real)`,
  (* Step 1: Unfold std_normal_density to its lambda definition *)
  SUBGOAL_THEN `std_normal_density =
    (\x. inv(sqrt(&2 * pi)) * exp(--(x pow 2 / &2)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; std_normal_density]; ALL_TAC] THEN
  (* Step 2: Establish inv(sqrt(2*pi)) * sqrt(2*pi) = 1 *)
  SUBGOAL_THEN `inv(sqrt(&2 * pi)) * sqrt(&2 * pi) = &1` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_MUL_LINV THEN
   MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
   MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Step 3: Get Gaussian integral for a=1 *)
  MP_TAC(SPEC `&1` GAUSSIAN_INTEGRAL_SCALED) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; REAL_DIV_1] THEN
  (* Step 4: Apply HAS_REAL_INTEGRAL_LMUL via forward reasoning *)
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `inv(sqrt(&2 * pi))` (MATCH_MP HAS_REAL_INTEGRAL_LMUL th))) THEN
  REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

(* Density is integrable on all of R *)
let STD_NORMAL_DENSITY_INTEGRABLE = prove
 (`std_normal_density real_integrable_on (:real)`,
  MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRAL]);;

(* Density is integrable on any half-line {t | t <= x} *)
let STD_NORMAL_DENSITY_INTEGRABLE_HALFLINE = prove
 (`!x. std_normal_density real_integrable_on {t | t <= x}`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`std_normal_density`; `(:real)`; `{t:real | t <= x}`]
    REAL_INTEGRABLE_ON_SUBINTERVAL_GEN) THEN
  REWRITE_TAC[SUBSET_UNIV; IS_REALINTERVAL_CLAUSES;
              STD_NORMAL_DENSITY_INTEGRABLE]);;

(* CDF is monotone non-decreasing *)
let STD_NORMAL_CDF_MONO = prove
 (`!x y. x <= y ==> std_normal_cdf x <= std_normal_cdf y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[std_normal_cdf] THEN
  MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
  REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE_HALFLINE;
              IN_ELIM_THM; STD_NORMAL_DENSITY_NONNEG] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* CDF is bounded between 0 and 1 *)
let STD_NORMAL_CDF_BOUNDS = prove
 (`!x. &0 <= std_normal_cdf x /\ std_normal_cdf x <= &1`,
  GEN_TAC THEN REWRITE_TAC[std_normal_cdf] THEN CONJ_TAC THENL
  [(* Lower bound: 0 <= integral *)
   MATCH_MP_TAC REAL_INTEGRAL_POS THEN
   REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE_HALFLINE;
               IN_ELIM_THM; STD_NORMAL_DENSITY_NONNEG];
   (* Upper bound: integral <= 1 *)
   MP_TAC(ISPECL [`std_normal_density`; `{t:real | t <= x}`;
                   `(:real)`;
                   `real_integral {t:real | t <= x} std_normal_density`;
                   `&1`] HAS_REAL_INTEGRAL_SUBSET_LE) THEN
   REWRITE_TAC[SUBSET_UNIV; STD_NORMAL_DENSITY_INTEGRAL;
               IN_UNIV; STD_NORMAL_DENSITY_NONNEG] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
   REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE_HALFLINE]]);;

(* Density is bounded above *)
let STD_NORMAL_DENSITY_BOUND = prove
 (`!x. std_normal_density x <= inv(sqrt(&2 * pi))`,
  GEN_TAC THEN REWRITE_TAC[std_normal_density] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
   MP_TAC PI_POS THEN REAL_ARITH_TAC;
   GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
   REWRITE_TAC[REAL_EXP_MONO_LE] THEN
   REWRITE_TAC[REAL_NEG_LE0] THEN
   MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
   REWRITE_TAC[REAL_LE_POW_2]]);;

(* CDF splitting: integral from x to y *)
let STD_NORMAL_CDF_INTERVAL = prove
 (`!x y. x <= y ==>
    std_normal_cdf y =
    std_normal_cdf x + real_integral (real_interval[x,y]) std_normal_density`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[std_normal_cdf] THEN
  SUBGOAL_THEN `(std_normal_density has_real_integral
    real_integral {t:real | t <= y} std_normal_density) {t | t <= y}`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
   REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE_HALFLINE]; ALL_TAC] THEN
  SUBGOAL_THEN `(std_normal_density has_real_integral
    (real_integral {t:real | t <= x} std_normal_density +
     real_integral (real_interval[x,y]) std_normal_density)) {t | t <= y}`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `{t:real | t <= y} = {t | t <= x} UNION real_interval[x,y]`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC HAS_REAL_INTEGRAL_UNION THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE_HALFLINE]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE; SUBSET_UNIV]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{x:real}` THEN
   REWRITE_TAC[REAL_NEGLIGIBLE_SING; SUBSET; IN_INTER; IN_SING;
               IN_ELIM_THM; IN_REAL_INTERVAL] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE]);;

(* CDF is continuous *)
let STD_NORMAL_CDF_CONTINUOUS = prove
 (`!x. std_normal_cdf real_continuous atreal x`,
  GEN_TAC THEN REWRITE_TAC[real_continuous_atreal] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2 * pi)` ASSUME_TAC THENL
  [MATCH_MP_TAC SQRT_POS_LT THEN
   MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
   REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&2 * pi))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `e * sqrt(&2 * pi)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `inv(sqrt(&2 * pi)) * abs(y - x)` THEN
  CONJ_TAC THENL
  [(* Lipschitz bound: |F(y) - F(x)| <= inv(sqrt(2pi)) * |y - x| *)
   DISJ_CASES_TAC(REAL_ARITH `x <= y \/ y <= x:real`) THENL
   [(* Case x <= y *)
    SUBGOAL_THEN `abs(std_normal_cdf y - std_normal_cdf x) =
      abs(real_integral (real_interval[x,y]) std_normal_density)` SUBST1_TAC THENL
    [MP_TAC(SPECL [`x:real`; `y:real`] STD_NORMAL_CDF_INTERVAL) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv(sqrt(&2 * pi)) * abs(y - x) =
                   inv(sqrt(&2 * pi)) * (y - x)` SUBST1_TAC THENL
    [AP_TERM_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(ISPEC `std_normal_density` HAS_REAL_INTEGRAL_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
     MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
     EXISTS_TAC `(:real)` THEN
     REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE; SUBSET_UNIV];
     GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
     MP_TAC(SPEC `x':real` STD_NORMAL_DENSITY_NONNEG) THEN
     MP_TAC(SPEC `x':real` STD_NORMAL_DENSITY_BOUND) THEN REAL_ARITH_TAC];
    (* Case y <= x *)
    SUBGOAL_THEN `abs(std_normal_cdf y - std_normal_cdf x) =
      abs(real_integral (real_interval[y,x]) std_normal_density)` SUBST1_TAC THENL
    [MP_TAC(SPECL [`y:real`; `x:real`] STD_NORMAL_CDF_INTERVAL) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv(sqrt(&2 * pi)) * abs(y - x) =
                   inv(sqrt(&2 * pi)) * (x - y)` SUBST1_TAC THENL
    [AP_TERM_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(ISPEC `std_normal_density` HAS_REAL_INTEGRAL_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
     MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
     EXISTS_TAC `(:real)` THEN
     REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE; SUBSET_UNIV];
     GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
     MP_TAC(SPEC `x':real` STD_NORMAL_DENSITY_NONNEG) THEN
     MP_TAC(SPEC `x':real` STD_NORMAL_DENSITY_BOUND) THEN REAL_ARITH_TAC]];
   (* inv(sqrt(2pi)) * |y-x| < e *)
   SUBGOAL_THEN `inv(sqrt(&2 * pi)) * (e * sqrt(&2 * pi)) = e`
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [SUBGOAL_THEN `~(sqrt(&2 * pi) = &0)` MP_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]]);;

(* Density symmetry *)
let STD_NORMAL_DENSITY_SYM = prove
 (`!x. std_normal_density(--x) = std_normal_density x`,
  GEN_TAC THEN REWRITE_TAC[std_normal_density] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_NEG; ARITH] THEN REAL_ARITH_TAC);;

(* Density is integrable on the upper halfline *)
let STD_NORMAL_DENSITY_INTEGRABLE_UPPER_HALFLINE = prove
 (`std_normal_density real_integrable_on {t | &0 <= t}`,
  MP_TAC(ISPECL [`std_normal_density`; `(:real)`; `{t:real | &0 <= t}`]
    REAL_INTEGRABLE_ON_SUBINTERVAL_GEN) THEN
  REWRITE_TAC[SUBSET_UNIV; STD_NORMAL_DENSITY_INTEGRABLE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* --- Phase 3: CLT Bridge --- *)

(* The characteristic function of the standard normal distribution
   is exp(-t^2/2). This connects GAUSSIAN_FT to the CLT. *)

(* Helper: inv(sqrt(2*pi)) * sqrt(2*pi) = 1 *)
let SQRT_2PI_INV = prove
 (`inv(sqrt(&2 * pi)) * sqrt(&2 * pi) = &1`,
  MATCH_MP_TAC REAL_MUL_LINV THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
  MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

(* Cancellation respecting right-association of * *)
let SQRT_2PI_CANCEL = prove
 (`!x:real. inv(sqrt(&2 * pi)) * sqrt(&2 * pi) * x = x`,
  GEN_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC; SQRT_2PI_INV; REAL_MUL_LID]);;

(* Real part: integral of std_normal_density * cos(t*x) *)
let STD_NORMAL_CHAR_FN_RE = prove
 (`!t. ((\x. std_normal_density x * cos(t * x)) has_real_integral
        exp(--(t pow 2 / &2))) (:real)`,
  GEN_TAC THEN REWRITE_TAC[std_normal_density] THEN
  REWRITE_TAC[REAL_ARITH `(a * b) * c:real = a * (b * c)`] THEN
  MP_TAC(REWRITE_RULE[REAL_MUL_LID; REAL_DIV_1;
    REAL_ARITH `&2 * &1:real = &2`]
    (MP (SPECL [`&1`; `t:real`] GAUSSIAN_FT) REAL_LT_01)) THEN
  DISCH_THEN(fun th ->
    ACCEPT_TAC(REWRITE_RULE[SQRT_2PI_CANCEL]
      (BETA_RULE
        (SPEC `inv(sqrt(&2 * pi))` (MATCH_MP HAS_REAL_INTEGRAL_LMUL th))))));;

(* Imaginary part: integral of std_normal_density * sin(t*x) = 0 *)
let STD_NORMAL_CHAR_FN_IM = prove
 (`!t. ((\x. std_normal_density x * sin(t * x)) has_real_integral
        &0) (:real)`,
  GEN_TAC THEN REWRITE_TAC[std_normal_density] THEN
  REWRITE_TAC[REAL_ARITH `(a * b) * c:real = a * (b * c)`] THEN
  MP_TAC(REWRITE_RULE[REAL_MUL_LID; REAL_DIV_1]
    (MP (SPECL [`&1`; `t:real`] GAUSSIAN_FT_SIN) REAL_LT_01)) THEN
  DISCH_THEN(fun th ->
    ACCEPT_TAC(REWRITE_RULE[REAL_MUL_RZERO]
      (BETA_RULE
        (SPEC `inv(sqrt(&2 * pi))` (MATCH_MP HAS_REAL_INTEGRAL_LMUL th))))));;


(* --- Helper lemmas for mean zero proof --- *)

(* |x| <= exp(x^2/4): from AM-GM (|x| <= 1 + x^2/4) and 1+y <= exp(y) *)
let ABS_LE_EXP_QUARTER = prove
 (`!x:real. abs(x) <= exp(x pow 2 / &4)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 + x pow 2 / &4` THEN CONJ_TAC THENL
  [SUBGOAL_THEN `&0 <= (x / &2 - &1) pow 2 /\ &0 <= (x / &2 + &1) pow 2`
     MP_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
   REWRITE_TAC[REAL_EXP_LE_X]]);;

(* |x * exp(-x^2/2)| <= exp(-x^2/4) *)
let ABS_X_GAUSSIAN_BOUND = prove
 (`!x:real. abs(x * exp(--(x pow 2 / &2))) <= exp(--(x pow 2 / &4))`,
  GEN_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(exp(--(x pow 2 / &2))) = exp(--(x pow 2 / &2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_REFL] THEN
   MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT];
   ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(x pow 2 / &4)) =
                exp(x pow 2 / &4) * exp(--(x pow 2 / &2))`
    SUBST1_TAC THENL
  [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
  [REWRITE_TAC[ABS_LE_EXP_QUARTER];
   MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_EXP_POS_LT]]);;

(* exp(-x^2/4) is integrable on (:real), from GAUSSIAN_INTEGRAL_SCALED *)
let GAUSSIAN_QUARTER_INTEGRABLE = prove
 (`(\t. exp(--(t pow 2 / &4))) real_integrable_on (:real)`,
  MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
  EXISTS_TAC `sqrt(&2 * pi / (&1 / &2))` THEN
  MP_TAC(SPEC `&1 / &2` GAUSSIAN_INTEGRAL_SCALED) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 * t pow 2 / &2 = t pow 2 / &4`]);;

(* x * exp(-x^2/2) is integrable on (:real), by domination *)
let X_GAUSSIAN_INTEGRABLE = prove
 (`(\x. x * exp(--(x pow 2 / &2))) real_integrable_on (:real)`,
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\t. exp(--(t pow 2 / &4))` THEN
  REWRITE_TAC[GAUSSIAN_QUARTER_INTEGRABLE; IN_UNIV;
              ABS_X_GAUSSIAN_BOUND] THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVALS_IMP_REAL_MEASURABLE THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC);;

(* IMAGE (--) (:real) = (:real) *)
let IMAGE_NEG_UNIV_REAL = prove
 (`IMAGE (--) (:real) = (:real)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  GEN_TAC THEN EXISTS_TAC `--x:real` THEN REWRITE_TAC[REAL_NEG_NEG]);;

(* Mean of standard normal is 0
   Proof: x*density(x) is odd (by STD_NORMAL_DENSITY_SYM), integrable
   (by domination with exp(-x^2/4)), so its integral k satisfies
   k = --k by reflection, hence k = 0. *)
let STD_NORMAL_MEAN_ZERO = prove
 (`((\x. x * std_normal_density x) has_real_integral &0) (:real)`,
  SUBGOAL_THEN `(\x. x * std_normal_density x) real_integrable_on (:real)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `(\x. x * std_normal_density x) =
    (\x. inv(sqrt(&2 * pi)) * (x * exp(--(x pow 2 / &2))))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; std_normal_density] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN REWRITE_TAC[X_GAUSSIAN_INTEGRABLE]];
   ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INTEGRABLE_INTEGRAL) THEN
  ABBREV_TAC `k = real_integral (:real) (\x. x * std_normal_density x)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
    `((\x. --(x * std_normal_density x)) has_real_integral k) (:real)`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
    `(\x. --(x * std_normal_density x)) =
     (\x. (--x) * std_normal_density(--x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; STD_NORMAL_DENSITY_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(ISPECL [`\x:real. x * std_normal_density x`; `k:real`; `(:real)`]
     HAS_REAL_INTEGRAL_REFLECT_GEN) THEN
   REWRITE_TAC[IMAGE_NEG_UNIV_REAL] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\x. --(x * std_normal_density x)) has_real_integral (--k)) (:real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC HAS_REAL_INTEGRAL_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `k:real = &0` SUBST_ALL_TAC THENL
  [SUBGOAL_THEN `k:real = --k` MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_UNIQUE THEN
    EXISTS_TAC `\x:real. --(x * std_normal_density x)` THEN
    EXISTS_TAC `(:real)` THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC];
   ASM_REWRITE_TAC[]]);;

(* Mean of standard normal - integral form *)
let STD_NORMAL_MEAN_ZERO_INTEGRAL = prove
 (`real_integral (:real) (\x. x * std_normal_density x) = &0`,
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[STD_NORMAL_MEAN_ZERO]);;

(* --- Helper lemmas for second moment proof --- *)

(* Derivative of -x * exp(-x^2/2) *)
let DERIV_NEG_X_GAUSSIAN = prove
 (`!x. ((\x. --x * exp(--(x pow 2 / &2))) has_real_derivative
        ((x pow 2 - &1) * exp(--(x pow 2 / &2)))) (atreal x)`,
  GEN_TAC THEN REAL_DIFF_TAC THEN CONV_TAC REAL_FIELD);;

(* Integral of (x^2-1)*exp(-x^2/2) over (:real) is 0.
   Proof: By FTC on [a,b], integral = F(b)-F(a) where F(x) = -x*exp(-x^2/2).
   F(x) -> 0 as |x| -> infinity, so the integral is 0. *)
let X2_MINUS_1_GAUSSIAN_HAS_INTEGRAL_0 = prove
 (`((\x. (x pow 2 - &1) * exp(--(x pow 2 / &2))) has_real_integral &0)
   (:real)`,
  REWRITE_TAC[HAS_REAL_INTEGRAL_ALT; IN_UNIV] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
   MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
   REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
   REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
   ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&1 / &2`; `e:real`] GAUSSIAN_EXP_DECAY) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 * t pow 2 / &2 = t pow 2 / &4`] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `a <= --B /\ B <= b` STRIP_ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_REAL_INTERVAL]) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a <= b:real` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `real_integral (real_interval[a,b])
       (\x. (x pow 2 - &1) * exp(--(x pow 2 / &2))) =
     (--b * exp(--(b pow 2 / &2))) - (--a * exp(--(a pow 2 / &2)))`
    SUBST1_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR THEN
   ASM_REWRITE_TAC[DERIV_NEG_X_GAUSSIAN] THEN
   MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
   REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
   REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH
    `abs fb < e / &2 /\ abs fa < e / &2
     ==> abs(fb - fa) < e`) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `exp(--(b pow 2 / &4))` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `--b * x:real = --(b * x)`] THEN
    REWRITE_TAC[REAL_ABS_NEG; ABS_X_GAUSSIAN_BOUND];
    SUBGOAL_THEN `&2 * exp(--(b pow 2 / &4)) < e` MP_TAC THENL
    [FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `b:real`) THEN
     ASM_REAL_ARITH_TAC;
     MP_TAC(SPEC `b pow 2 / &4` REAL_EXP_POS_LE) THEN
     REAL_ARITH_TAC]];
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `exp(--(a pow 2 / &4))` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `--a * x:real = --(a * x)`] THEN
    REWRITE_TAC[REAL_ABS_NEG; ABS_X_GAUSSIAN_BOUND];
    SUBGOAL_THEN `&2 * exp(--(a pow 2 / &4)) < e` MP_TAC THENL
    [FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `a:real`) THEN
     ASM_REAL_ARITH_TAC;
     MP_TAC(SPEC `a pow 2 / &4` REAL_EXP_POS_LE) THEN
     REAL_ARITH_TAC]]]);;

(* x^2 * exp(-x^2/2) has integral sqrt(2*pi) over (:real).
   Proof: x^2*exp = (x^2-1)*exp + exp, and integral of (x^2-1)*exp = 0,
   integral of exp = sqrt(2*pi). *)
let X2_GAUSSIAN_HAS_INTEGRAL = prove
 (`((\x. x pow 2 * exp(--(x pow 2 / &2))) has_real_integral sqrt(&2 * pi))
   (:real)`,
  SUBGOAL_THEN
    `(\x. x pow 2 * exp(--(x pow 2 / &2))) =
     (\x. (x pow 2 - &1) * exp(--(x pow 2 / &2)) +
          exp(--(x pow 2 / &2)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 * pi) = &0 + sqrt(&2 * pi)` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
  [REWRITE_TAC[X2_MINUS_1_GAUSSIAN_HAS_INTEGRAL_0];
   MP_TAC(SPEC `&1` GAUSSIAN_INTEGRAL_SCALED) THEN
   ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_LID; REAL_DIV_1]]);;

(* Second moment of standard normal is 1 *)
let STD_NORMAL_SECOND_MOMENT = prove
 (`((\x. x pow 2 * std_normal_density x) has_real_integral &1) (:real)`,
  SUBGOAL_THEN
    `(\x. x pow 2 * std_normal_density x) =
     (\x. inv(sqrt(&2 * pi)) * (x pow 2 * exp(--(x pow 2 / &2))))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; std_normal_density] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&1 = inv(sqrt(&2 * pi)) * sqrt(&2 * pi)` SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV THEN
   MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
   MATCH_MP_TAC SQRT_POS_LT THEN
   MP_TAC PI_POS THEN REAL_ARITH_TAC;
   MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   REWRITE_TAC[X2_GAUSSIAN_HAS_INTEGRAL]]);;

(* Second moment integral form *)
let STD_NORMAL_SECOND_MOMENT_INTEGRAL = prove
 (`real_integral (:real) (\x. x pow 2 * std_normal_density x) = &1`,
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[STD_NORMAL_SECOND_MOMENT]);;

(* ========================================================================= *)
(* TIGHTNESS FROM BOUNDED SECOND MOMENTS                                     *)
(* ========================================================================= *)

(* Helper: |x| >= M iff x^2 >= M^2, for M >= 0 *)
let ABS_GE_IFF_POW2_GE = prove
 (`!x M. &0 <= M ==> (abs(x) >= M <=> x pow 2 >= M pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_ge] THEN
  SUBGOAL_THEN `M = abs(M:real)` SUBST1_TAC THENL
  [ASM_REAL_ARITH_TAC;
   REWRITE_TAC[REAL_LE_SQUARE_ABS; REAL_POW2_ABS]]);;

(* Markov-type bound: P(|X| >= M) <= E[X^2] / M^2 *)
let MARKOV_SECOND_MOMENT = prove
 (`!p:A prob_space (X:A->real) M.
     simple_rv p X /\ &0 < M
     ==> prob p {a | a IN prob_carrier p /\ abs(X a) >= M} <=
         simple_expectation p (\x. X x pow 2) / M pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{a:A | a IN prob_carrier p /\ abs((X:A->real) a) >= M} =
     {a | a IN prob_carrier p /\ (\a. X a pow 2) a >= M pow 2}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:A` THEN
   BETA_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC ABS_GE_IFF_POW2_GE THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\a:A. (X:A->real) a pow 2)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC SIMPLE_RV_SQUARE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MARKOV_INEQUALITY_SIMPLE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [X_GEN_TAC `a:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_POW_2];
   ASM_SIMP_TAC[REAL_POW_LT]]);;

(* Tightness from uniformly bounded second moments *)
let SIMPLE_TIGHTNESS_FROM_SECOND_MOMENTS = prove
 (`!p:A prob_space (X:num->A->real) C.
     (!n. simple_rv p (X n)) /\
     &0 < C /\
     (!n. simple_expectation p (\x. (X:num->A->real) n x pow 2) <= C)
     ==>
     !e. &0 < e ==>
       ?M. &0 < M /\
       !n:num.
         prob (p:A prob_space) {a | a IN prob_carrier p /\
                                     abs((X:num->A->real) n a) >= M} < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `M = sqrt(C / e) + &1` THEN
  EXISTS_TAC `M:real` THEN
  SUBGOAL_THEN `&0 <= sqrt(C / e)` ASSUME_TAC THENL
  [MATCH_MP_TAC SQRT_POS_LE THEN
   MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
  [EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `C / e < (M:real) pow 2` ASSUME_TAC THENL
  [EXPAND_TAC "M" THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `sqrt(C / e) pow 2` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SQRT_POW_2 THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (M:real) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(C:real) / (M:real) pow 2 < e` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `(e:real) * (C / e)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN
    `prob (p:A prob_space) {a | a IN prob_carrier p /\
       abs((X:num->A->real) n a) >= M} <=
     simple_expectation p (\x. X n x pow 2) / (M:real) pow 2`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL
     [`p:A prob_space`; `(X:num->A->real) n`; `M:real`]
     MARKOV_SECOND_MOMENT) THEN
   REWRITE_TAC[ETA_AX] THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; SIMP_TAC[]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\x. (X:num->A->real) n x pow 2) /
     (M:real) pow 2 <= (C:real) / (M:real) pow 2`
    ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(C:real) / (M:real) pow 2` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space) (\x. (X:num->A->real) n x pow 2) / (M:real) pow 2` THEN
  ASM_REWRITE_TAC[]);;

(* Convergence set is measurable: the set of points where X_n -> L
   pointwise is a measurable event. Proof: express the convergence set as
   INTERS_k liminf_events (\n. {x | |X_n(x) - L(x)| < inv(k+1)}) and use
   closure of sigma-algebras under countable operations. *)
let CONVERGENCE_SET_IN_EVENTS = prove
 (`!p:A prob_space (X:num->A->real) (L:A->real).
     (!n. random_variable p (X n)) /\ random_variable p L
     ==> {x | x IN prob_carrier p /\
              ((\n. X n x) ---> L x) sequentially} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  (* Step 1: Each {x | |X n x - L x| < inv(&k+1)} is an event *)
  SUBGOAL_THEN `!n:num k:num.
    {x:A | x IN prob_carrier p /\
      abs ((X:num->A->real) n x - (L:A->real) x) < inv(&k + &1)}
    IN prob_events (p:A prob_space)` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN prob_carrier p /\
       abs ((X:num->A->real) n x - (L:A->real) x) < inv(&k + &1)} =
      {x | x IN prob_carrier p /\
       --(inv(&k + &1)) < X n x - L x /\ X n x - L x < inv(&k + &1)}`
     SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC RANDOM_VARIABLE_OPEN_INTERVAL THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    ASM_REWRITE_TAC[ETA_AX]];
   ALL_TAC] THEN
  (* Step 2: Show convergence set = INTERS of liminf events *)
  SUBGOAL_THEN
    `{x:A | x IN prob_carrier p /\
       ((\n. (X:num->A->real) n x) ---> (L:A->real) x) sequentially} =
     INTERS {liminf_events
       (\n. {x:A | x IN prob_carrier p /\
         abs (X n x - L x) < inv(&k + &1)}) | k IN (:num)}`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `w:A` THEN EQ_TAC THENL
   [(* Forward: convergence => in INTERS of liminf *)
    REWRITE_TAC[IN_ELIM_THM; IN_INTERS; FORALL_IN_GSPEC; IN_UNIV] THEN
    STRIP_TAC THEN
    X_GEN_TAC `k:num` THEN
    REWRITE_TAC[LIMINF_EVENTS_ALT; IN_ELIM_THM] THEN
    UNDISCH_TAC
      `((\n. (X:num->A->real) n (w:A)) ---> (L:A->real) w) sequentially` THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&k + &1)`) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN
    X_GEN_TAC `nn:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     FIRST_X_ASSUM(MP_TAC o SPEC `nn:num`) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    (* Backward: in INTERS of liminf => convergence *)
    REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(w:A) IN prob_carrier (p:A prob_space)` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
     REWRITE_TAC[LIMINF_EVENTS_ALT; IN_ELIM_THM] THEN
     DISCH_THEN(X_CHOOSE_THEN `mm:num` (MP_TAC o SPEC `mm:num`)) THEN
     REWRITE_TAC[GE; LE_REFL; IN_ELIM_THM] THEN SIMP_TAC[];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV_SUC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    REWRITE_TAC[LIMINF_EVENTS_ALT; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `mm:num`) THEN
    EXISTS_TAC `mm:num` THEN
    X_GEN_TAC `nn:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `nn:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GE]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `inv(&k + &1)` THEN ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 3: Show RHS is an event *)
  MATCH_MP_TAC PROB_INDEXED_INTER_IN_EVENTS THEN
  GEN_TAC THEN
  MATCH_MP_TAC LIMINF_EVENTS_IN_EVENTS THEN
  GEN_TAC THEN ASM_REWRITE_TAC[]);;

(* Helper: INTERS of tail unions SUBSET complement of convergence set *)
let INTERS_TAIL_UNIONS_SUBSET_COMPL = prove
 (`!p:A prob_space (X:num->A->real) (L:A->real) (e:real).
     &0 < e /\
     (!n. {x:A | x IN prob_carrier p /\
       abs (X n x - L x) >= e} IN prob_events p)
     ==>
     INTERS {UNIONS {{x:A | x IN prob_carrier p /\
       abs (X n' x - L x) >= e} | n' >= n} | n IN (:num)}
     SUBSET
     prob_carrier p DIFF
       {x:A | x IN prob_carrier p /\
         ((\n. X n x) ---> L x) sequentially}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTERS; IN_DIFF; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  CONJ_TAC THENL
  [FIRST_ASSUM(MP_TAC o SPEC
    `UNIONS {{x:A | x IN prob_carrier (p:A prob_space) /\
      abs ((X:num->A->real) n' x - (L:A->real) x) >= e} | n' >= 0}`) THEN
   ANTS_TAC THENL
   [EXISTS_TAC `0` THEN REFL_TAC; ALL_TAC] THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
   FIRST_X_ASSUM SUBST1_TAC THEN
   REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `e:real`)) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
   FIRST_ASSUM(MP_TAC o SPEC
     `UNIONS {{x:A | x IN prob_carrier (p:A prob_space) /\
       abs ((X:num->A->real) n' x - (L:A->real) x) >= e} | n' >= N}`) THEN
   ANTS_TAC THENL
   [EXISTS_TAC `N:num` THEN REFL_TAC; ALL_TAC] THEN
   REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
   FIRST_X_ASSUM SUBST1_TAC THEN
   REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
   UNDISCH_TAC `m >= N:num` THEN REWRITE_TAC[GE] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* SUBSEQUENCE CONVERGENCE TOOLS                                             *)
(* ========================================================================= *)

(* Every bounded real sequence has a convergent subsequence *)
let BOUNDED_REAL_SEQ_HAS_CONVERGENT_SUBSEQ = prove
 (`!f:num->real b.
     (!n. abs(f n) <= b)
     ==> ?l r. (!m n. m < n ==> r m < r n) /\
               ((\k. f(r k)) ---> l) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `f:num->real` MONOTONE_SUBSEQUENCE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THENL
  [MP_TAC(SPECL [`\k:num. (f:num->real)(r k)`; `b:real`]
    CONVERGENT_BOUNDED_MONOTONE) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN ASM_REWRITE_TAC[];
     DISJ1_TAC THEN ASM_MESON_TAC[LE_REFL; NOT_LT; LT_IMP_LE]];
    ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
   EXISTS_TAC `l:real` THEN EXISTS_TAC `r:num->num` THEN
   ASM_REWRITE_TAC[REALLIM_SEQUENTIALLY];
   MP_TAC(SPECL [`\k:num. (f:num->real)(r k)`; `b:real`]
    CONVERGENT_BOUNDED_MONOTONE) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN ASM_REWRITE_TAC[];
     DISJ2_TAC THEN ASM_MESON_TAC[LE_REFL; NOT_LT; LT_IMP_LE]];
    ALL_TAC] THEN
   REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
   DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
   EXISTS_TAC `l:real` THEN EXISTS_TAC `r:num->num` THEN
   ASM_REWRITE_TAC[REALLIM_SEQUENTIALLY]]);;

(* Extract strictly increasing sequence from cofinal property *)
let INFINITE_EXTRACT_SUBSEQ = prove
 (`!P:num->bool. (!N:num. ?n. N <= n /\ P n)
     ==> ?r:num->num. (!m n. m < n ==> r m < r n) /\ (!k. P (r k))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m:num. ?n. m < n /\ (P:num->bool) n` ASSUME_TAC THENL
  [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `m + 1`) THEN
   DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!m:num. m < (@n. m < n /\ (P:num->bool) n) /\ P(@n. m < n /\ P n)`
    ASSUME_TAC THENL
  [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
   DISCH_THEN(X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPECL [`\n:num. m < n /\ (P:num->bool) n`; `w:num`] SELECT_AX) THEN
   BETA_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`@n:num. 0 < n /\ P n`;
    `\(prev:num) (k:num). @n:num. prev < n /\ P n`] num_RECURSION) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:num->num` THEN
  SUBGOAL_THEN `!k:num. (r:num->num) k < r(SUC k)` ASSUME_TAC THENL
  [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
   ASM_REWRITE_TAC[] THEN ARITH_TAC;
   INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* Subsequence convergence principle:
   If every subsequence has a sub-subsequence converging to L,
   then the full sequence converges to L *)
let REALLIM_SUBSEQ_SAME_LIMIT = prove
 (`!f:num->real L b.
     (!n. abs(f n) <= b) /\
     (!r:num->num. (!m n. m < n ==> r m < r n)
          ==> ?s:num->num. (!m n. m < n ==> s m < s n) /\
                  ((\k. f(r(s k))) ---> L) sequentially)
     ==> (f ---> L) sequentially`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `?N:num. !n. N <= n ==> abs((f:num->real) n - L) < e` THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!N:num. ?n. N <= n /\ ~(abs((f:num->real) n - L) < e)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `?r1:num->num. (!m n:num. m < n ==> r1 m < r1 n) /\
                   (!k:num. ~(abs((f:num->real)(r1 k) - L) < e))`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPEC `\n:num. ~(abs((f:num->real) n - L) < e)` INFINITE_EXTRACT_SUBSEQ) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r1:num->num`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:num->num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC
    `((\k:num. (f:num->real)((r1:num->num)((s1:num->num) k))) ---> (L:real)) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M:num`) THEN
  REWRITE_TAC[LE_REFL] THEN BETA_TAC THEN
  ASM_MESON_TAC[]);;


(* ========================================================================= *)
(* LIMIT IDENTIFICATION TOOLS                                                *)
(* ========================================================================= *)

(* General lemma: if f is continuous at x and f(x-h) <= l <= f(x+h)
   for all h > 0, then l = f(x). *)
let CONTINUOUS_LIMIT_SANDWICH = prove
 (`!f x l. f real_continuous (atreal x) /\
           (!h. &0 < h ==> f(x - h) <= l /\ l <= f(x + h))
           ==> l = f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= l /\ l <= a ==> l = a`) THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `(f:real->real) real_continuous (atreal x)` THEN
   REWRITE_TAC[real_continuous_atreal] THEN
   DISCH_THEN(MP_TAC o SPEC `(f:real->real) x - l`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x - d / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `d / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `(f:real->real) real_continuous (atreal x)` THEN
   REWRITE_TAC[real_continuous_atreal] THEN
   DISCH_THEN(MP_TAC o SPEC `l - (f:real->real) x`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `x + d / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `d / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC]);;

(* Strictly increasing num->num satisfies r(k) >= k *)
let STRICTLY_INCREASING_GE = prove
 (`!(r:num->num). (!m n. m < n ==> r m < r n) ==> !k. k <= r k`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
  [ARITH_TAC;
   FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `SUC k`]) THEN
   REWRITE_TAC[LT] THEN ASM_ARITH_TAC]);;

(* Subsequences of convergent real sequences converge to the same limit *)
let REALLIM_SUBSEQUENCE = prove
 (`!(f:num->real) l (r:num->num).
     (f ---> l) sequentially /\ (!m n. m < n ==> r m < r n)
     ==> ((\k. f(r k)) ---> l) sequentially`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPEC `r:num->num` STRICTLY_INCREASING_GE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
  ASM_ARITH_TAC);;

(* ---- Helper lemmas for the sandwich argument ---- *)

(* CDF as expectation of indicator *)
let SIMPLE_CDF_AS_EXPECTATION = prove
 (`!p:A prob_space (X:A->real) x.
     simple_rv p X
     ==> simple_cdf p X x =
         simple_expectation p (\a. if X a <= x then &1 else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simple_cdf] THEN
  CONV_TAC SYM_CONV THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\a:A. if (X:A->real) a <= x then &1 else &0) =
     simple_expectation p (indicator_fn {a | a IN prob_carrier p /\ X a <= x})`
    SUBST1_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN
   X_GEN_TAC `a:A` THEN DISCH_TAC THEN
   REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC SIMPLE_EXPECTATION_INDICATOR THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [simple_rv]) THEN
  REWRITE_TAC[random_variable] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REWRITE_TAC[]);;

(* E[g(X)] <= F(x) when g(y) <= 1 for y<=x and g(y) <= 0 for y>x *)
let EXPECTATION_LE_CDF = prove
 (`!p:A prob_space (X:A->real) (g:real->real) x.
     simple_rv p X /\
     (!y. y <= x ==> g y <= &1) /\
     (!y. y > x ==> g y <= &0)
     ==> simple_expectation p (\a. g(X a)) <= simple_cdf p X x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(SPEC `x:real` (MATCH_MP SIMPLE_CDF_AS_EXPECTATION th))) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\a:A. (g:real->real) ((X:A->real) a)`;
     `\a:A. if (X:A->real) a <= x then &1 else &0`]
    SIMPLE_EXPECTATION_MONO) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_REAL_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                   `\y:real. if y <= x then &1 else &0`]
      SIMPLE_RV_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
   X_GEN_TAC `a:A` THEN DISCH_TAC THEN
   ASM_CASES_TAC `(X:A->real) a <= x` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
   SIMP_TAC[]]);;

(* F(x) <= E[g(X)] when g(y) >= 1 for y<=x and g(y) >= 0 for y>x *)
let CDF_LE_EXPECTATION = prove
 (`!p:A prob_space (X:A->real) (g:real->real) x.
     simple_rv p X /\
     (!y. y <= x ==> &1 <= g y) /\
     (!y. y > x ==> &0 <= g y)
     ==> simple_cdf p X x <= simple_expectation p (\a. g(X a))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    MP_TAC(SPEC `x:real` (MATCH_MP SIMPLE_CDF_AS_EXPECTATION th))) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\a:A. if (X:A->real) a <= x then &1 else &0`;
     `\a:A. (g:real->real) ((X:A->real) a)`]
    SIMPLE_EXPECTATION_MONO) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                   `\y:real. if y <= x then &1 else &0`]
      SIMPLE_RV_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_REAL_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   X_GEN_TAC `a:A` THEN DISCH_TAC THEN
   ASM_CASES_TAC `(X:A->real) a <= x` THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC];
   SIMP_TAC[]]);;

(* Standard normal density is continuous at every point *)
let STD_NORMAL_DENSITY_CONTINUOUS = prove
 (`!x. std_normal_density real_continuous atreal x`,
  GEN_TAC THEN
  SUBGOAL_THEN `std_normal_density =
    (\x. inv(sqrt(&2 * pi)) * exp(--(x pow 2 / &2)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; std_normal_density]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
  MP_TAC(ISPECL [`\x:real. --(x pow 2 / &2)`; `exp`; `x:real`]
    (REWRITE_RULE[o_DEF] REAL_CONTINUOUS_ATREAL_COMPOSE)) THEN
  BETA_TAC THEN
  DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_CONTINUOUS_NEG THEN
   MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_POW THEN
    REWRITE_TAC[REAL_CONTINUOUS_AT_ID];
    CONJ_TAC THENL
    [REWRITE_TAC[REAL_CONTINUOUS_CONST]; REAL_ARITH_TAC]];
   REWRITE_TAC[REAL_CONTINUOUS_AT_EXP]]);;

(* Product of bounded continuous function with density is integrable *)
let BOUNDED_CONT_TIMES_DENSITY_INTEGRABLE = prove
 (`!g:real->real.
    (!y. g real_continuous atreal y) /\
    (?B. !y. abs(g y) <= B)
    ==> (\y. g y * std_normal_density y) real_integrable_on (:real)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\y:real. B * std_normal_density y` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
   CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT
                  REAL_OPEN_UNIV; IN_UNIV] THEN
    GEN_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
    ASM_REWRITE_TAC[STD_NORMAL_DENSITY_CONTINUOUS];
    REWRITE_TAC[REAL_CLOSED_UNIV]];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
   REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE];
   ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[IN_UNIV] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(std_normal_density x) = std_normal_density x`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_ABS_REFL; STD_NORMAL_DENSITY_NONNEG]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[STD_NORMAL_DENSITY_NONNEG] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* DENSITY SYMMETRY AND FOURIER TRANSFORM PROPERTIES                         *)
(* ========================================================================= *)

(* std_normal_density is an even function *)
let STD_NORMAL_DENSITY_EVEN = prove
 (`!y. std_normal_density(--y) = std_normal_density y`,
  GEN_TAC THEN REWRITE_TAC[std_normal_density] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_NEG; ARITH]);;

(* Reflection of the whole real line is itself *)
let IMAGE_NEG_UNIV = prove
 (`IMAGE (--) (:real) = (:real)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  GEN_TAC THEN EXISTS_TAC `--x:real` THEN
  REWRITE_TAC[REAL_NEG_NEG]);;

(* sin(ty) * density is integrable *)
let SIN_DENSITY_INTEGRABLE = prove
 (`!t. (\y. sin(t * y) * std_normal_density y) real_integrable_on (:real)`,
  GEN_TAC THEN
  MATCH_MP_TAC BOUNDED_CONT_TIMES_DENSITY_INTEGRABLE THEN
  CONJ_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`\y:real. t * y`; `sin`; `y:real`]
     (REWRITE_RULE[o_DEF] REAL_CONTINUOUS_ATREAL_COMPOSE)) THEN
   BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_AT_ID];
    REWRITE_TAC[REAL_CONTINUOUS_AT_SIN]];
   EXISTS_TAC `&1` THEN REWRITE_TAC[SIN_BOUND]]);;

(* ========================================================================= *)
(* WEAK CONVERGENCE FROM CHAR FN CONVERGENCE                                 *)
(* ========================================================================= *)

(* Weak convergence from characteristic function convergence.
   This is the portmanteau theorem direction: char fn convergence + tightness
   implies weak convergence (convergence of expectations of bounded
   continuous functions).

   Proof approach: For bounded continuous g, eps > 0:
   1. Tightness gives M with P(|X_n| > M) small
   2. Trig polynomial T approximates g on [-M,M] (Weierstrass)
   3. E[T(X_n)] -> int(T*density) by char fn hypothesis + Gaussian FT
   4. Errors from approximation + tails controlled by eps argument

   Key sub-lemma: trigonometric polynomial approximation on compact
   intervals. Uses WEIERSTRASS_TRIG_POLYNOMIAL (from fourier.ml) for
   approximation on [-pi,pi], then scales by B/(B+eps/2) to get global
   bound |T| <= B while preserving approximation quality. *)

(* Periodicity of sin and cos with natural number multiples of 2*pi *)
let SIN_PERIODIC_N = prove
 (`!k:num. !x. sin(x + &2 * &k * pi) = sin(x)`,
  INDUCT_TAC THENL
  [REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID];
   GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC;
    REAL_ARITH `&2 * (k + &1) * p = &2 * k * p + &2 * p`] THEN
   REWRITE_TAC[REAL_ADD_ASSOC; SIN_PERIODIC] THEN ASM_REWRITE_TAC[]]);;

let COS_PERIODIC_N = prove
 (`!k:num. !x. cos(x + &2 * &k * pi) = cos(x)`,
  INDUCT_TAC THENL
  [REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID];
   GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC;
    REAL_ARITH `&2 * (k + &1) * p = &2 * k * p + &2 * p`] THEN
   REWRITE_TAC[REAL_ADD_ASSOC; COS_PERIODIC] THEN ASM_REWRITE_TAC[]]);;

(* A 2*pi-periodic function bounded on [-pi,pi] is bounded everywhere *)
let PERIODIC_REAL_BOUND = prove
 (`!(fn:real->real) (B:real). (!x. fn(x + &2 * pi) = fn x) /\
         (!x. x IN real_interval[--pi,pi] ==> abs(fn x) <= B)
         ==> !x. abs(fn x) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL
  [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* Shift x into [-pi, pi] *)
  (* Step 1: find N such that x + 2*N*pi > 0 *)
  MP_TAC(SPEC `--(x:real)` (MATCH_MP (SPEC `&2 * pi` REAL_ARCH)
    (ASSUME `&0 < &2 * pi`))) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  ABBREV_TAC `y = x + &2 * &N * pi` THEN
  SUBGOAL_THEN `&0 < (y:real)` ASSUME_TAC THENL
  [EXPAND_TAC "y" THEN
   UNDISCH_TAC `--(x:real) < &N * (&2 * pi)` THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Step 2: find m such that y - 2*m*pi in [-pi, pi] *)
  MP_TAC(SPEC `(y:real) - pi` (MATCH_MP (SPEC `&2 * pi` REAL_ARCH)
    (ASSUME `&0 < &2 * pi`))) THEN
  DISCH_THEN(X_CHOOSE_TAC `K:num`) THEN
  MP_TAC(fst(EQ_IMP_RULE(BETA_RULE
    (SPEC `\m:num. (y:real) - &2 * &m * pi < pi` num_WOP)))) THEN
  ANTS_TAC THENL
  [EXISTS_TAC `K:num` THEN
   UNDISCH_TAC `(y:real) - pi < &K * (&2 * pi)` THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m0:num` STRIP_ASSUME_TAC) THEN
  (* fn(x) = fn(y) by forward periodicity *)
  SUBGOAL_THEN `(fn:real->real) x = fn y` SUBST1_TAC THENL
  [EXPAND_TAC "y" THEN
   SUBGOAL_THEN `!n:num. !z:real. (fn:real->real)(z) = fn(z + &2 * &n * pi)`
     MP_TAC THENL
   [INDUCT_TAC THENL
    [REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID];
     GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC;
      REAL_ARITH `&2 * (k + &1) * p = &2 * k * p + &2 * p`] THEN
     REWRITE_TAC[REAL_ADD_ASSOC] THEN
     ONCE_REWRITE_TAC[ASSUME
       `!x:real. (fn:real->real)(x + &2 * pi) = fn x`] THEN
     ASM_MESON_TAC[]];
    DISCH_THEN(MP_TAC o SPECL [`N:num`; `x:real`]) THEN
    MESON_TAC[]]; ALL_TAC] THEN
  (* fn(y) = fn(y - 2*m0*pi) by backward periodicity *)
  SUBGOAL_THEN `(fn:real->real) y = fn(y - &2 * &m0 * pi)` SUBST1_TAC THENL
  [SUBGOAL_THEN `!n:num. !z:real. (fn:real->real)(z) = fn(z + &2 * &n * pi)`
     MP_TAC THENL
   [INDUCT_TAC THENL
    [REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID];
     GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC;
      REAL_ARITH `&2 * (k + &1) * p = &2 * k * p + &2 * p`] THEN
     REWRITE_TAC[REAL_ADD_ASSOC] THEN
     ONCE_REWRITE_TAC[ASSUME
       `!x:real. (fn:real->real)(x + &2 * pi) = fn x`] THEN
     ASM_MESON_TAC[]];
    DISCH_THEN(MP_TAC o SPECL [`m0:num`; `(y:real) - &2 * &m0 * pi`]) THEN
    REWRITE_TAC[REAL_SUB_ADD] THEN MESON_TAC[]];
   ALL_TAC] THEN
  (* y - 2*m0*pi in [-pi, pi] *)
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ASM_CASES_TAC `m0 = 0` THENL
  [SUBGOAL_THEN `(y:real) < pi` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real) - &2 * &m0 * pi < pi` THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_SUB_RZERO];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
   MP_TAC(ASSUME `&0 < (y:real)`) THEN
   MP_TAC(ASSUME `(y:real) < pi`) THEN
   MP_TAC PI_POS THEN REAL_ARITH_TAC;
   SUBGOAL_THEN `--pi <= (y:real) - &2 * &m0 * pi` MP_TAC THENL
   [SUBGOAL_THEN `1 <= m0` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m0 - 1`) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= m ==> m - 1 < m`] THEN
    REWRITE_TAC[REAL_NOT_LT] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `(y:real) - &2 * &m0 * pi < pi` THEN
    REAL_ARITH_TAC]]);;

let SCALED_APPROX_BOUND = prove
 (`!h s c e2.
    abs(h - s) < e2 /\ (&1 - c) * abs(s) <= e2 /\ &0 <= &1 - c
    ==> abs(h - c * s) < e2 + e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:real) - c * s = (h - s) + (&1 - c) * s`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs((h:real) - s) + abs((&1 - c) * s)` THEN
  REWRITE_TAC[REAL_ABS_TRIANGLE] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(&1 - c) = &1 - c` SUBST1_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BOUNDED_CONTINUOUS_TRIG_APPROX = prove
 (`!g:real->real B M e.
    (!y. g real_continuous atreal y) /\ (!y. abs(g y) <= B) /\
    &0 < B /\ &0 < M /\ &0 < e
    ==> ?n:num a b f.
      (!y. abs(y) <= M
           ==> abs(g y - sum(0..n) (\k. a k * cos(f k * y) +
                                         b k * sin(f k * y))) < e) /\
      (!y. abs(sum(0..n) (\k. a k * cos(f k * y) +
                               b k * sin(f k * y))) <= B)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = M + &1` THEN
  SUBGOAL_THEN `&0 < L /\ ~(L = &0)` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "L" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC PI_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(pi = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Define h on [-pi, pi]: h(t) = g(L*t/pi) * window(t) *)
  ABBREV_TAC
   `h = \t. (g:real->real)(L * t / pi) *
            max (&0) (min (&1) (L * (pi - abs t) / pi))` THEN
  (* h continuous on [-pi, pi] *)
  SUBGOAL_THEN
   `(h:real->real) real_continuous_on real_interval[--pi, pi]`
  ASSUME_TAC THENL
  [EXPAND_TAC "h" THEN
   MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[o_DEF] REAL_CONTINUOUS_ON_COMPOSE) THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN `(\t:real. L * t / pi) = (\t. (L / pi) * t)`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID]];
     MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `(:real)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
     SIMP_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT;
              REAL_OPEN_UNIV; IN_UNIV] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MAX THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MIN THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN `(\t:real. L * (pi - abs t) / pi) =
                  (\t. (L / pi) * (pi - abs t))` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
     MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
     REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
     GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
     MATCH_MP_TAC REAL_CONTINUOUS_ON_ABS THEN
     REWRITE_TAC[REAL_CONTINUOUS_ON_ID]]];
   ALL_TAC] THEN
  (* h(-pi) = h(pi) *)
  SUBGOAL_THEN `(h:real->real)(--pi) = h(pi)` ASSUME_TAC THENL
  [EXPAND_TAC "h" THEN
   SUBGOAL_THEN `abs(pi) = pi /\ abs(--pi) = pi`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
   SUBGOAL_THEN `&0 / pi = &0` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[REAL_DIV_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* |h(t)| <= B on [-pi, pi] *)
  SUBGOAL_THEN `!t. t IN real_interval[--pi,pi] ==> abs(h t) <= B`
  ASSUME_TAC THENL
  [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
   DISCH_TAC THEN EXPAND_TAC "h" THEN
   REWRITE_TAC[REAL_ABS_MUL] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
    [ASM_MESON_TAC[]; REAL_ARITH_TAC]; REAL_ARITH_TAC];
   ALL_TAC] THEN
  (* h(pi*y/L) = g(y) for |y| <= M *)
  SUBGOAL_THEN `!y. abs y <= M ==> h(pi * y / L) = (g:real->real) y`
  ASSUME_TAC THENL
  [X_GEN_TAC `y:real` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
   SUBGOAL_THEN `L * (pi * y / L) / pi = y` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD
     `&0 < p /\ &0 < L ==> L * (p * y / L) / p = y`) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(pi * y / L) = pi * abs y / L` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs pi = pi` SUBST1_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs L = L` SUBST1_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REFL_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `L * (pi - pi * abs y / L) / pi = L - abs y`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `pi - pi * abs y / L = pi * (&1 - abs y / L)`
    SUBST1_TAC THENL
    [REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_FIELD
      `~(p = &0) /\ ~(q = &0) ==> q * (p * (&1 - y / q)) / p = q - y`) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `&1 <= L - abs y` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `min (&1) (L - abs y) = &1` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  (* Apply WEIERSTRASS_TRIG_POLYNOMIAL with e/2 *)
  MP_TAC(SPECL [`h:real->real`; `e / &2`] WEIERSTRASS_TRIG_POLYNOMIAL) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (X_CHOOSE_THEN `aw:num->real`
   (X_CHOOSE_THEN `bw:num->real` ASSUME_TAC))) THEN
  (* |T(x)| <= B + e/2 on [-pi,pi] *)
  SUBGOAL_THEN
   `!x. x IN real_interval[--pi,pi]
        ==> abs(sum(0..N) (\k. aw k * sin(&k * x) +
                                bw k * cos(&k * x))) < B + e / &2`
  ASSUME_TAC THENL
  [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
   SUBGOAL_THEN `abs((h:real->real) x) <= B` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
    `abs(h x - sum(0..N) (\k. aw k * sin(&k * x) +
                                bw k * cos(&k * x))) < e / &2` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  (* T is 2*pi periodic *)
  SUBGOAL_THEN
   `!x. sum(0..N) (\k. aw k * sin(&k * (x + &2 * pi)) +
                         bw k * cos(&k * (x + &2 * pi))) =
        sum(0..N) (\k. aw k * sin(&k * x) + bw k * cos(&k * x))`
  ASSUME_TAC THENL
  [GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN
   REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[REAL_ARITH `k * (x + &2 * p) = k * x + &2 * k * p`] THEN
   REWRITE_TAC[SIN_PERIODIC_N; COS_PERIODIC_N]; ALL_TAC] THEN
  (* |T(x)| <= B + e/2 on ALL of R (by periodicity) *)
  SUBGOAL_THEN
   `!x. abs(sum(0..N) (\k. aw k * sin(&k * x) +
                             bw k * cos(&k * x))) <= B + e / &2`
  ASSUME_TAC THENL
  [MATCH_MP_TAC PERIODIC_REAL_BOUND THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[]]; ALL_TAC] THEN
  (* Scale factor c = B / (B + e/2) *)
  ABBREV_TAC `c = B / (B + e / &2)` THEN
  SUBGOAL_THEN `&0 < B + e / &2` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(B + e / &2 = &0)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
  [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL
  [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (B + e / &2) = B` ASSUME_TAC THENL
  [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_DIV_RMUL]; ALL_TAC] THEN
  (* Provide witnesses: n=N, a(k)=c*bw(k), b(k)=c*aw(k), f(k)=k*pi/L *)
  MAP_EVERY EXISTS_TAC
   [`N:num`; `\k:num. (c:real) * (bw:num->real) k`;
    `\k:num. (c:real) * (aw:num->real) k`;
    `\k:num. &k * pi / (L:real)`] THEN
  (* Rewrite the trig polynomial *)
  SUBGOAL_THEN
   `!y. sum(0..N) (\k. (c * bw k) * cos ((&k * pi / L) * y) +
                        (c * aw k) * sin ((&k * pi / L) * y)) =
        c * sum(0..N) (\k. aw k * sin(&k * (pi * y / L)) +
                            bw k * cos(&k * (pi * y / L)))`
  ASSUME_TAC THENL
  [GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
   MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
   REWRITE_TAC[REAL_MUL_AC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [(* Approximation: |g(y) - c*T(pi*y/L)| < e for |y| <= M *)
   X_GEN_TAC `y:real` THEN DISCH_TAC THEN
   SUBGOAL_THEN `pi * y / L IN real_interval[--pi,pi]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN
    SUBGOAL_THEN `abs(pi * y / L) <= pi * M / L` MP_TAC THENL
    [REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL] THEN
     SUBGOAL_THEN `abs pi = pi` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `abs L = L` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_LMUL_EQ];
     SUBGOAL_THEN `pi * M / L < pi` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `p * M / L < p <=> &0 < p * (&1 - M / L)`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "L" THEN
      ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LDIV_EQ;
                   REAL_ARITH `&0 < M ==> &0 < M + &1`;
                   REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]; ALL_TAC] THEN
   (* g(y) = h(pi*y/L), then use WEIERSTRASS and SCALED_APPROX_BOUND *)
   SUBGOAL_THEN `(g:real->real) y = h(pi * y / L)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `x < e / &2 + e / &2 ==> x < (e:real)`) THEN
   MATCH_MP_TAC SCALED_APPROX_BOUND THEN
   REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 - c) * (B + e / &2)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
     SUBGOAL_THEN `(&1 - c) * (B + e / &2) = e / &2`
      SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(&1 - c) * x = x - c * x`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]]];
    ASM_REAL_ARITH_TAC];
   (* Global bound: |c*T(pi*y/L)| <= B for all y *)
   X_GEN_TAC `y:real` THEN REWRITE_TAC[REAL_ABS_MUL] THEN
   SUBGOAL_THEN `abs c = c` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * (B + e / &2)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[REAL_LE_REFL]]]);;


(* Expectation of a single trig term a*cos(f*X) + b*sin(f*X) decomposes
   into char fn values *)
let SIMPLE_EXPECTATION_TRIG_TERM = prove
 (`!p:A prob_space (Y:A->real) a b t.
     simple_rv p Y
     ==> simple_expectation p (\x. a * cos(t * Y x) + b * sin(t * Y x)) =
         a * char_fn_re p Y t + b * char_fn_im p Y t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[char_fn_re; char_fn_im] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. cos(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `\y:real. cos(t * y)`]
    SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\x:A. sin(t * (Y:A->real) x))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `Y:A->real`; `\y:real. sin(t * y)`]
    SIMPLE_RV_REAL_COMPOSE) THEN
   ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  (* E[a*cos + b*sin] = E[a*cos] + E[b*sin] *)
  MP_TAC(ISPECL [`p:A prob_space`;
                  `\x:A. a * cos(t * (Y:A->real) x)`;
                  `\x:A. b * sin(t * (Y:A->real) x)`]
    SIMPLE_EXPECTATION_ADD) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
                    `\x:A. cos(t * (Y:A->real) x)`; `a:real`]
      SIMPLE_RV_CMUL) THEN
    BETA_TAC THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`p:A prob_space`;
                    `\x:A. sin(t * (Y:A->real) x)`; `b:real`]
      SIMPLE_RV_CMUL) THEN
    BETA_TAC THEN ASM_SIMP_TAC[]];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  (* E[a*cos] = a * E[cos] *)
  MP_TAC(ISPECL [`p:A prob_space`;
                  `\x:A. cos(t * (Y:A->real) x)`; `a:real`]
    SIMPLE_EXPECTATION_CMUL) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  (* E[b*sin] = b * E[sin] *)
  MP_TAC(ISPECL [`p:A prob_space`;
                  `\x:A. sin(t * (Y:A->real) x)`; `b:real`]
    SIMPLE_EXPECTATION_CMUL) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REFL_TAC);;

(* Trig polynomial expectations converge to the Gaussian integral.
   Key intermediate lemma for weak convergence. *)
let TRIG_POLY_WEAK_CONVERGENCE = prove
 (`!p:A prob_space (X:num->A->real) m (a:num->real) (b:num->real) (freq:num->real).
     (!n. simple_rv p (X n)) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
          sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> &0) sequentially)
     ==> ((\n. simple_expectation p
                (\x. sum(0..m) (\k. a k * cos(freq k * X n x) +
                                     b k * sin(freq k * X n x)))) --->
          sum(0..m) (\k. a k * exp(--(freq k pow 2 / &2))))
         sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: E[trig_poly(X_n)] = sum of char fn values for each n (admitted) *)
  SUBGOAL_THEN
    `!n:num. simple_expectation (p:A prob_space)
       (\x:A. sum(0..m) (\k. (a:num->real) k * cos((freq:num->real) k * (X:num->A->real) n x) +
                               (b:num->real) k * sin(freq k * X n x))) =
     sum(0..m) (\k. a k * char_fn_re p (X n) (freq k) +
                     b k * char_fn_im p (X n) (freq k))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`;
                    `\k:num. \x:A. (a:num->real) k * cos((freq:num->real) k * (X:num->A->real) n x) +
                                    (b:num->real) k * sin(freq k * X n x)`;
                    `m:num`]
     SIMPLE_EXPECTATION_SUM_NUMSEG) THEN
   BETA_TAC THEN
   ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    (* Need: simple_rv p (\x. a i * cos(freq i * X n x) + b i * sin(freq i * X n x)) *)
    MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`;
                    `\y:real. cos((freq:num->real) i * y)`]
      SIMPLE_RV_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`;
                    `\y:real. sin((freq:num->real) i * y)`]
      SIMPLE_RV_REAL_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                    `\x:A. cos((freq:num->real) i * (X:num->A->real) n x)`;
                    `(a:num->real) i`] SIMPLE_RV_CMUL) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                    `\x:A. sin((freq:num->real) i * (X:num->A->real) n x)`;
                    `(b:num->real) i`] SIMPLE_RV_CMUL) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                    `\x:A. (a:num->real) i * cos((freq:num->real) i * (X:num->A->real) n x)`;
                    `\x:A. (b:num->real) i * sin((freq:num->real) i * (X:num->A->real) n x)`]
      SIMPLE_RV_ADD) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC SUM_EQ_NUMSEG THEN
   X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`;
                    `(a:num->real) k`; `(b:num->real) k`; `(freq:num->real) k`]
     SIMPLE_EXPECTATION_TRIG_TERM) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: Rewrite the convergence using the decomposition *)
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n:num. sum(0..m) (\k. (a:num->real) k * char_fn_re (p:A prob_space) ((X:num->A->real) n) ((freq:num->real) k) +
                                       (b:num->real) k * char_fn_im p (X n) (freq k))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
   EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: Sum of convergent sequences converges *)
  MATCH_MP_TAC REALLIM_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `(a:num->real) k * exp (--((freq:num->real) k pow 2 / &2)) =
    a k * exp (--(freq k pow 2 / &2)) + (b:num->real) k * &0` SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
  [MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]]);;

(* Gaussian integral of a single trig term: uses forward reasoning with
   explicit ISPECL to avoid higher-order matching issues *)
let HAS_INTEGRAL_TRIG_TERM = prove
 (`!a b t.
    ((\y. (a * cos(t * y) + b * sin(t * y)) *
          std_normal_density y) has_real_integral
     (a * exp(--(t pow 2 / &2))))
    (:real)`,
  REPEAT GEN_TAC THEN
  (* Rewrite goal function and value *)
  SUBGOAL_THEN
    `(\y:real. ((a:real) * cos((t:real) * y) + (b:real) * sin(t * y)) *
          std_normal_density y) =
     (\y. a * (std_normal_density y * cos(t * y)) +
          b * (std_normal_density y * sin(t * y)))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(a:real) * exp(--((t:real) pow 2 / &2)) =
     a * exp(--(t pow 2 / &2)) + (b:real) * &0`
    SUBST1_TAC THENL
  [REAL_ARITH_TAC; ALL_TAC] THEN
  (* Prove a * (density * cos) has integral a * exp *)
  SUBGOAL_THEN
    `((\y:real. (a:real) * (std_normal_density y * cos((t:real) * y)))
      has_real_integral (a * exp(--(t pow 2 / &2)))) (:real)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`\y:real. std_normal_density y * cos((t:real) * y)`;
                   `exp(--((t:real) pow 2 / &2))`;
                   `(:real)`;
                   `a:real`] HAS_REAL_INTEGRAL_LMUL) THEN
   REWRITE_TAC[STD_NORMAL_CHAR_FN_RE] THEN BETA_TAC THEN
   DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
  (* Prove b * (density * sin) has integral b * 0 *)
  SUBGOAL_THEN
    `((\y:real. (b:real) * (std_normal_density y * sin((t:real) * y)))
      has_real_integral (b * &0)) (:real)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`\y:real. std_normal_density y * sin((t:real) * y)`;
                   `&0`;
                   `(:real)`;
                   `b:real`] HAS_REAL_INTEGRAL_LMUL) THEN
   REWRITE_TAC[STD_NORMAL_CHAR_FN_IM] THEN BETA_TAC THEN
   DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
  (* Combine with HAS_REAL_INTEGRAL_ADD *)
  MP_TAC(ISPECL
    [`\y:real. (a:real) * (std_normal_density y * cos((t:real) * y))`;
     `\y:real. (b:real) * (std_normal_density y * sin((t:real) * y))`;
     `(a:real) * exp(--((t:real) pow 2 / &2))`;
     `(b:real) * &0`;
     `(:real)`] HAS_REAL_INTEGRAL_ADD) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN ACCEPT_TAC);;

(* Full trig polynomial Gaussian integral - uses HAS_INTEGRAL_TRIG_TERM *)
let GAUSSIAN_INTEGRAL_TRIG_POLY = prove
 (`!m:num (a:num->real) (b:num->real) (freq:num->real).
    ((\y. sum(0..m) (\k. a k * cos(freq k * y) +
                          b k * sin(freq k * y)) *
          std_normal_density y) has_real_integral
     sum(0..m) (\k. a k * exp(--(freq k pow 2 / &2))))
    (:real)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `(\y:real. sum(0..m) (\k. (a:num->real) k * cos((freq:num->real) k * y) +
                          (b:num->real) k * sin(freq k * y)) *
          std_normal_density y) =
     (\y. sum(0..m) (\k. (a k * cos(freq k * y) +
                           b k * sin(freq k * y)) *
                          std_normal_density y))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[GSYM SUM_RMUL]; ALL_TAC] THEN
  MP_TAC(INST
    [`\k:num. (a:num->real) k * exp(--((freq:num->real) k pow 2 / &2))`,
     `i:num->real`]
    (ISPECL
      [`\k:num. \y:real. ((a:num->real) k * cos((freq:num->real) k * y) +
                           (b:num->real) k * sin(freq k * y)) *
                          std_normal_density y`;
       `(:real)`;
       `0..m`]
      HAS_REAL_INTEGRAL_SUM)) THEN
  BETA_TAC THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  ANTS_TAC THENL
  [REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC[HAS_INTEGRAL_TRIG_TERM];
   DISCH_THEN ACCEPT_TAC]);;

(* Helper lemma for Step C of WEAK_CONVERGENCE_FROM_CHAR_FN:
   Pointwise trig approximation bound + second moment bound
   implies expectation error bound *)
let STEP_C_BOUND = prove
 (`!p:A prob_space (X:num->A->real) (g:real->real) (T':real->real) BB CC e M.
     (!n. simple_rv p (X n)) /\
     &0 < CC /\
     (!n. simple_expectation p (\x. X n x pow 2) <= CC) /\
     (!y. abs(g y) <= BB) /\
     (!y. abs(T' y) <= BB) /\
     &0 < BB /\ &0 < e /\ &0 < M /\
     (!y. abs y <= M ==> abs(g y - T' y) < e / &6)
     ==> !n:num. abs(simple_expectation p (\a. g(X n a)) -
              simple_expectation p (\a. T'(X n a))) <=
         e / &6 + &2 * BB * CC / M pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\a:A. (g:real->real)((X:num->A->real) n a))` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`; `g:real->real`] SIMPLE_RV_REAL_COMPOSE) THEN
   REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\a:A. (T':real->real)((X:num->A->real) n a))` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`; `T':real->real`] SIMPLE_RV_REAL_COMPOSE) THEN
   REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_rv (p:A prob_space) (\a:A. (X:num->A->real) n a pow 2)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`; `\y:real. y pow 2`] SIMPLE_RV_REAL_COMPOSE) THEN
   BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space) (\a:A. (g:real->real)((X:num->A->real) n a)) -
     simple_expectation p (\a. (T':real->real)(X n a)) =
     simple_expectation p (\a. g(X n a) - T'(X n a))`
    (fun th -> REWRITE_TAC[th]) THENL
  [CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC SIMPLE_EXPECTATION_SUB THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\a:A. abs((g:real->real)((X:num->A->real) n a) - (T':real->real)(X n a)))` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_ABS_LE THEN
   MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `simple_expectation (p:A prob_space)
    (\a:A. e / &6 + &2 * BB * (X:num->A->real) n a pow 2 / M pow 2)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SIMPLE_EXPECTATION_MONO THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ABS THEN MATCH_MP_TAC SIMPLE_RV_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_ADD THEN CONJ_TAC THENL
    [REWRITE_TAC[SIMPLE_RV_CONST]; ALL_TAC] THEN
    MATCH_MP_TAC SIMPLE_RV_CMUL THEN
    SUBGOAL_THEN `(\a:A. BB * (X:num->A->real) n a pow 2 / M pow 2) =
                  (\a. (\y:real. BB * y pow 2 / M pow 2) (X n a))` SUBST1_TAC THENL
    [REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) n`;
                   `\y:real. BB * y pow 2 / M pow 2`] SIMPLE_RV_REAL_COMPOSE) THEN
    BETA_TAC THEN REWRITE_TAC[ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
   ASM_CASES_TAC `abs((X:num->A->real) n (a:A)) <= M` THENL
   [MATCH_MP_TAC(REAL_ARITH `x < ep /\ &0 <= r ==> x <= ep + r`) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[REAL_POW_LT]]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * BB * (X:num->A->real) n (a:A) pow 2 / M pow 2` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * BB` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
        `abs x <= B /\ abs y <= B ==> abs(x - y) <= &2 * B`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC;
       GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
       MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
        REWRITE_TAC[REAL_MUL_LID; GSYM REAL_LE_SQUARE_ABS] THEN
        UNDISCH_TAC `~(abs((X:num->A->real) n (a:A)) <= M)` THEN
        UNDISCH_TAC `&0 < M` THEN REAL_ARITH_TAC]]];
     UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* E[e/6 + 2*BB*X^2/M^2] = e/6 + 2*BB*E[X^2]/M^2 *)
  SUBGOAL_THEN
    `simple_expectation (p:A prob_space)
      (\a:A. e / &6 + &2 * BB * (X:num->A->real) n a pow 2 / M pow 2) =
     e / &6 + &2 * BB * simple_expectation p (\a. X n a pow 2) / M pow 2`
    SUBST1_TAC THENL
  [REWRITE_TAC[real_div] THEN
   SUBGOAL_THEN `(\a:A. e * inv(&6) + &2 * BB * (X:num->A->real) n a pow 2 * inv(M pow 2)) =
                 (\a. e * inv(&6) + &2 * BB * (inv(M pow 2) * X n a pow 2))`
     SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\a:A. inv(M pow 2) * (X:num->A->real) n a pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\a:A. BB * inv(M pow 2) * (X:num->A->real) n a pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `simple_rv (p:A prob_space)
     (\a:A. &2 * BB * inv(M pow 2) * (X:num->A->real) n a pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`p:A prob_space`;
     `\a:A. e * inv(&6)`;
     `\a:A. &2 * BB * inv(M pow 2) * (X:num->A->real) n a pow 2`]
     SIMPLE_EXPECTATION_ADD) THEN
   ASM_REWRITE_TAC[SIMPLE_RV_CONST] THEN BETA_TAC THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   REWRITE_TAC[SIMPLE_EXPECTATION_CONST] THEN
   AP_TERM_TAC THEN
   ASM_SIMP_TAC[SIMPLE_EXPECTATION_CMUL] THEN
   REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> a + x <= a + y`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
  [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT]);;

(* Helper lemma for Step D of WEAK_CONVERGENCE_FROM_CHAR_FN:
   Pointwise trig approximation bound implies integral error bound
   against standard normal density *)
let STEP_D_BOUND = prove
 (`!g:real->real (T':real->real) BB e M L.
     (!y. g real_continuous atreal y) /\
     (!y. abs(g y) <= BB) /\
     (!y. abs(T' y) <= BB) /\
     &0 < BB /\ &0 < e /\ &0 < M /\
     (!y. abs y <= M ==> abs(g y - T' y) < e / &6) /\
     ((\y. T' y * std_normal_density y) has_real_integral L) (:real)
     ==> abs(L - real_integral (:real) (\y. g y * std_normal_density y)) <=
         e / &6 + &2 * BB / M pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(\y. (g:real->real) y * std_normal_density y) real_integrable_on (:real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
   MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    REWRITE_TAC[REAL_CLOSED_UNIV] THEN
    ASM_SIMP_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT;
                  REAL_OPEN_UNIV; IN_UNIV]; ALL_TAC] THEN
   CONJ_TAC THENL
   [REWRITE_TAC[real_bounded; IN_IMAGE; IN_UNIV] THEN
    EXISTS_TAC `BB:real` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[absolutely_real_integrable_on] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRAL];
    SUBGOAL_THEN `(\x:real. abs(std_normal_density x)) = std_normal_density`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
     REWRITE_TAC[STD_NORMAL_DENSITY_NONNEG];
     MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
     EXISTS_TAC `&1` THEN REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRAL]]];
   ALL_TAC] THEN
  SUBGOAL_THEN `L = real_integral (:real)
    (\y. (T':real->real) y * std_normal_density y)` SUBST1_TAC THENL
  [MATCH_MP_TAC(GSYM REAL_INTEGRAL_UNIQUE) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `(\y. (T':real->real) y * std_normal_density y)
    real_integrable_on (:real)` ASSUME_TAC THENL
  [MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
   EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `real_integral (:real) (\y. (T':real->real) y * std_normal_density y) -
     real_integral (:real) (\y. (g:real->real) y * std_normal_density y) =
     real_integral (:real) (\y. T' y * std_normal_density y -
                                g y * std_normal_density y)`
    SUBST1_TAC THENL
  [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_SUB THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\y:real. (T':real->real) y * std_normal_density y -
               (g:real->real) y * std_normal_density y) =
     (\y. (T' y - g y) * std_normal_density y)`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (:real)
    (\y. (e / &6 + &2 * BB * y pow 2 / M pow 2) *
         std_normal_density y)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN CONJ_TAC THENL
   [SUBGOAL_THEN
      `(\y:real. ((T':real->real) y - (g:real->real) y) *
                 std_normal_density y) =
       (\y. T' y * std_normal_density y - g y * std_normal_density y)`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN
      `(\y:real. (e / &6 + &2 * BB * y pow 2 / M pow 2) *
                 std_normal_density y) =
       (\y. e / &6 * std_normal_density y +
            &2 * BB / M pow 2 * (y pow 2 * std_normal_density y))`
      SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRAL];
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_INTEGRABLE THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[STD_NORMAL_SECOND_MOMENT]]];
    ALL_TAC] THEN
   REWRITE_TAC[IN_UNIV] THEN X_GEN_TAC `y:real` THEN BETA_TAC THEN
   REWRITE_TAC[REAL_ABS_MUL] THEN
   SUBGOAL_THEN `abs(std_normal_density y) = std_normal_density y`
     SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
    REWRITE_TAC[STD_NORMAL_DENSITY_NONNEG]; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ASM_CASES_TAC `abs(y:real) <= M` THENL
    [MATCH_MP_TAC(REAL_ARITH `x < ep /\ &0 <= r ==> x <= ep + r`) THEN
     CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC;
       MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN
        REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[REAL_POW_LT]]]];
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `&2 * BB * y pow 2 / M pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * BB` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC(REAL_ARITH
         `abs x <= B /\ abs y <= B ==> abs(x - y) <= &2 * B`) THEN
       ASM_REWRITE_TAC[];
       MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
        [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
         ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
         REWRITE_TAC[REAL_MUL_LID; GSYM REAL_LE_SQUARE_ABS] THEN
         UNDISCH_TAC `~(abs(y:real) <= M)` THEN
         UNDISCH_TAC `&0 < M` THEN REAL_ARITH_TAC]]];
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]];
    REWRITE_TAC[STD_NORMAL_DENSITY_NONNEG]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `((\y:real. (e / &6 + &2 * BB * y pow 2 / M pow 2) *
               std_normal_density y)
      has_real_integral (e / &6 + &2 * BB / M pow 2)) (:real)`
    (fun th -> REWRITE_TAC[MATCH_MP REAL_INTEGRAL_UNIQUE th;
                            REAL_LE_REFL]) THEN
  SUBGOAL_THEN
    `(\y:real. (e / &6 + &2 * BB * y pow 2 / M pow 2) *
              std_normal_density y) =
     (\y. e / &6 * std_normal_density y +
          &2 * BB / M pow 2 * (y pow 2 * std_normal_density y))`
    SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `e / &6 + &2 * BB / M pow 2 =
                e / &6 * &1 + &2 * BB / M pow 2 * &1`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
  [MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRAL];
   MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
   REWRITE_TAC[STD_NORMAL_SECOND_MOMENT]]);;

let WEAK_CONVERGENCE_FROM_CHAR_FN = prove
 (`!p:A prob_space (X:num->A->real) (g:real->real).
     (!n. simple_rv p (X n)) /\
     (?C. &0 < C /\ !n. simple_expectation p (\x. X n x pow 2) <= C) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
          sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> &0) sequentially) /\
     (!y. g real_continuous atreal y) /\
     (?B. &0 < B /\ !y. abs(g y) <= B)
     ==> ((\n. simple_expectation p (\a:A. g(X n a))) --->
          real_integral (:real) (\y. g y * std_normal_density y))
         sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `CC:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `BB:real` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `M = sqrt(&12 * BB * (CC + &1) / e) + &1` THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
  [EXPAND_TAC "M" THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
   MATCH_MP_TAC SQRT_POS_LE THEN
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < CC` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]]]; ALL_TAC] THEN
  (* Apply BOUNDED_CONTINUOUS_TRIG_APPROX *)
  MP_TAC(SPECL [`g:real->real`; `BB:real`; `M:real`; `e / &6`]
    BOUNDED_CONTINUOUS_TRIG_APPROX) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num`
    (X_CHOOSE_THEN `aa:num->real`
      (X_CHOOSE_THEN `bb:num->real`
        (X_CHOOSE_THEN `ff:num->real` STRIP_ASSUME_TAC)))) THEN
  (* Key bound: 2*BB*(CC+1)/M^2 < e/6 *)
  SUBGOAL_THEN `&2 * BB * (CC + &1) / M pow 2 < e / &6` ASSUME_TAC THENL
  [SUBGOAL_THEN `~(e = &0) /\ ~(BB = &0) /\ ~(CC + &1 = &0)` STRIP_ASSUME_TAC
   THENL
   [UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < BB` THEN
    UNDISCH_TAC `&0 < CC` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < &12 * BB * (CC + &1) / e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
    [REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < CC` THEN REAL_ARITH_TAC]]; ALL_TAC] THEN
   SUBGOAL_THEN `&12 * BB * (CC + &1) / e < M pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &12 * BB * (CC + &1) / e` ASSUME_TAC THENL
    [UNDISCH_TAC `&0 < &12 * BB * (CC + &1) / e` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&12 * BB * (CC + &1) / e) pow 2 =
                   &12 * BB * (CC + &1) / e` (SUBST1_TAC o GSYM) THENL
    [ASM_SIMP_TAC[SQRT_POW2]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt(&12 * BB * (CC + &1) / e)` ASSUME_TAC THENL
    [MATCH_MP_TAC SQRT_POS_LE THEN
     UNDISCH_TAC `&0 < &12 * BB * (CC + &1) / e` THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sqrt (&12 * BB * (CC + &1) / e) + &1 = M` THEN
    UNDISCH_TAC `&0 <= sqrt(&12 * BB * (CC + &1) / e)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[real_div] THEN
   SUBGOAL_THEN
     `e * inv(&6) = &2 * BB * (CC + &1) * inv(&12 * BB * (CC + &1) * inv e)`
     SUBST1_TAC THENL
   [UNDISCH_TAC `~(e = &0)` THEN UNDISCH_TAC `~(BB = &0)` THEN
    UNDISCH_TAC `~(CC + &1 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_MUL;
                REAL_ARITH `&0 < CC ==> &0 < CC + &1`;
                REAL_OF_NUM_LT; ARITH] THEN
   MATCH_MP_TAC REAL_LT_INV2 THEN
   ASM_REWRITE_TAC[GSYM real_div];
   ALL_TAC] THEN
  (* Step A: E[T(X_n)] -> L *)
  ABBREV_TAC `L = sum(0..nn)
    (\k. (aa:num->real) k * exp(--((ff:num->real) k pow 2 / &2)))` THEN
  SUBGOAL_THEN
    `((\n. simple_expectation (p:A prob_space)
       (\x:A. sum(0..nn)
         (\k. (aa:num->real) k * cos((ff:num->real) k * (X:num->A->real) n x) +
              (bb:num->real) k * sin(ff k * X n x)))) --->
      L) sequentially`
    ASSUME_TAC THENL
  [EXPAND_TAC "L" THEN
   MATCH_MP_TAC TRIG_POLY_WEAK_CONVERGENCE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step B: L = integral of T times density *)
  SUBGOAL_THEN
    `L = real_integral (:real)
      (\y. sum(0..nn)
        (\k. (aa:num->real) k * cos((ff:num->real) k * y) +
             (bb:num->real) k * sin(ff k * y)) *
        std_normal_density y)`
    ASSUME_TAC THENL
  [EXPAND_TAC "L" THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
   REWRITE_TAC[GAUSSIAN_INTEGRAL_TRIG_POLY]; ALL_TAC] THEN
  (* Steps C and D: error bounds *)
  SUBGOAL_THEN
    `!n:num. abs(simple_expectation (p:A prob_space)
       (\a:A. (g:real->real)((X:num->A->real) n a)) -
      simple_expectation p
       (\a:A. sum(0..nn)
         (\k. (aa:num->real) k * cos((ff:num->real) k * X n a) +
              (bb:num->real) k * sin(ff k * X n a)))) <=
      e / &6 + &2 * BB * CC / M pow 2`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL
     [`p:A prob_space`; `X:num->A->real`; `g:real->real`;
      `\y:real. sum(0..nn)
        (\k. (aa:num->real) k * cos((ff:num->real) k * y) +
             (bb:num->real) k * sin(ff k * y))`;
      `BB:real`; `CC:real`; `e:real`; `M:real`] STEP_C_BOUND) THEN
   BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `abs(L - real_integral (:real)
      (\y. (g:real->real) y * std_normal_density y)) <=
      e / &6 + &2 * BB / M pow 2`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL
     [`g:real->real`;
      `\y:real. sum(0..nn)
        (\k. (aa:num->real) k * cos((ff:num->real) k * y) +
             (bb:num->real) k * sin(ff k * y))`;
      `BB:real`; `e:real`; `M:real`; `L:real`] STEP_D_BOUND) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [EXPAND_TAC "L" THEN ASM_REWRITE_TAC[GAUSSIAN_INTEGRAL_TRIG_POLY];
    DISCH_THEN ACCEPT_TAC];
   ALL_TAC] THEN
  (* Step E: From convergence of E[T(X_n)] to L, get N *)
  FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY] o
    check (fun th -> free_in `nn:num` (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  (* Step F1: |E[g(X_n)] - E[T(X_n)]| < e/3 *)
  SUBGOAL_THEN `abs(simple_expectation (p:A prob_space)
    (\a:A. (g:real->real)((X:num->A->real) n a)) -
    simple_expectation p
    (\a:A. sum(0..nn)
      (\k. (aa:num->real) k * cos((ff:num->real) k * X n a) +
           (bb:num->real) k * sin(ff k * X n a)))) < e / &3`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `e / &6 + &2 * BB * CC / M pow 2` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `x < e / &6 ==> e / &6 + x < e / &3`) THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `&2 * BB * (CC + &1) / M pow 2` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
     ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN
     REAL_ARITH_TAC]];
   ALL_TAC] THEN
  (* Step F2: |E[T(X_n)] - L| < e/3 *)
  SUBGOAL_THEN `abs(simple_expectation (p:A prob_space)
    (\a:A. sum(0..nn)
      (\k. (aa:num->real) k * cos((ff:num->real) k * (X:num->A->real) n a) +
           (bb:num->real) k * sin(ff k * X n a))) -
    L) < e / &3`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
   ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step F3: |L - int(g*density)| < e/3 *)
  SUBGOAL_THEN `abs(L - real_integral (:real)
    (\y. (g:real->real) y * std_normal_density y)) < e / &3`
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `e / &6 + &2 * BB / M pow 2` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `x < e / &6 ==> e / &6 + x < e / &3`) THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `&2 * BB * (CC + &1) / M pow 2` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[real_div] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [UNDISCH_TAC `&0 < BB` THEN REAL_ARITH_TAC;
     GEN_REWRITE_TAC (LAND_CONV) [GSYM REAL_MUL_LID] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < CC` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_SIMP_TAC[REAL_POW_LT]]]];
   ALL_TAC] THEN
  ABBREV_TAC `eg = simple_expectation (p:A prob_space)
    (\a:A. (g:real->real)((X:num->A->real) n a))` THEN
  ABBREV_TAC `et = simple_expectation (p:A prob_space)
    (\a:A. sum(0..nn)
      (\k. (aa:num->real) k * cos((ff:num->real) k * (X:num->A->real) n a) +
           (bb:num->real) k * sin(ff k * X n a)))` THEN
  ABBREV_TAC `ig = real_integral (:real)
    (\y. (g:real->real) y * std_normal_density y)` THEN
  ASM_REAL_ARITH_TAC);;

(* Integral of bounded [0,1]-valued continuous function against std normal
   density is bounded by std_normal_cdf *)
let INTEGRAL_BOUNDED_LE_CDF = prove
 (`!(g:real->real) b.
     (!y. &0 <= g y /\ g y <= &1) /\ (!y. y > b ==> g y = &0) /\
     (!y. g real_continuous atreal y)
     ==> real_integral (:real) (\y. g y * std_normal_density y) <= std_normal_cdf b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real. g y * std_normal_density y) real_integrable_on (:real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC BOUNDED_CONT_TIMES_DENSITY_INTEGRABLE THEN
   ASM_REWRITE_TAC[] THEN EXISTS_TAC `&1` THEN
   GEN_TAC THEN
   UNDISCH_TAC `!y:real. &0 <= g y /\ g y <= &1` THEN
   DISCH_THEN(MP_TAC o SPEC `y:real`) THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[std_normal_cdf] THEN
  MP_TAC(ISPECL
    [`\y:real. g y * std_normal_density y`;
     `\y:real. if y IN {t | t <= b} then std_normal_density y else &0`;
     `(:real)`;
     `real_integral (:real) (\y:real. g y * std_normal_density y)`;
     `real_integral (:real) (\y:real. if y IN {t | t <= b} then std_normal_density y else &0)`]
    HAS_REAL_INTEGRAL_LE) THEN
  BETA_TAC THEN
  REWRITE_TAC[REAL_INTEGRAL_RESTRICT_UNIV] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE_HALFLINE];
    ALL_TAC] THEN
   GEN_TAC THEN REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
   ASM_CASES_TAC `x <= b` THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * std_normal_density x` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL THEN
     REWRITE_TAC[STD_NORMAL_DENSITY_NONNEG] THEN
     UNDISCH_TAC `!y:real. &0 <= g y /\ g y <= &1` THEN
     DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC;
     REWRITE_TAC[REAL_MUL_LID; REAL_LE_REFL]];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g:real->real) x = &0` SUBST1_TAC THENL
    [UNDISCH_TAC `!y:real. y > b ==> g y = &0` THEN
     DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]]];
   SIMP_TAC[]]);;

(* std_normal_cdf bounded by integral of bounded [0,1]-valued continuous
   function *)
let CDF_LE_INTEGRAL_BOUNDED = prove
 (`!(g:real->real) a.
     (!y. &0 <= g y /\ g y <= &1) /\ (!y. y <= a ==> g y = &1) /\
     (!y. g real_continuous atreal y)
     ==> std_normal_cdf a <= real_integral (:real) (\y. g y * std_normal_density y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real. g y * std_normal_density y) real_integrable_on (:real)`
    ASSUME_TAC THENL
  [MATCH_MP_TAC BOUNDED_CONT_TIMES_DENSITY_INTEGRABLE THEN
   ASM_REWRITE_TAC[] THEN EXISTS_TAC `&1` THEN
   GEN_TAC THEN
   UNDISCH_TAC `!y:real. &0 <= g y /\ g y <= &1` THEN
   DISCH_THEN(MP_TAC o SPEC `y:real`) THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[std_normal_cdf] THEN
  MP_TAC(ISPECL
    [`\y:real. if y IN {t | t <= a} then std_normal_density y else &0`;
     `\y:real. g y * std_normal_density y`;
     `(:real)`;
     `real_integral (:real) (\y:real. if y IN {t | t <= a} then std_normal_density y else &0)`;
     `real_integral (:real) (\y:real. g y * std_normal_density y)`]
    HAS_REAL_INTEGRAL_LE) THEN
  BETA_TAC THEN
  REWRITE_TAC[REAL_INTEGRAL_RESTRICT_UNIV] THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
    REWRITE_TAC[STD_NORMAL_DENSITY_INTEGRABLE_HALFLINE];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   GEN_TAC THEN REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
   ASM_CASES_TAC `x <= a` THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!y:real. y <= a ==> g y = &1` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_LID; REAL_LE_REFL];
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[STD_NORMAL_DENSITY_NONNEG] THEN
    UNDISCH_TAC `!y:real. &0 <= g y /\ g y <= &1` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC];
   SIMP_TAC[]]
);;


(* Char fn uniqueness for the standard normal:
   If char fns converge to exp(-t^2/2) and CDFs converge at x to l,
   then l = std_normal_cdf(x).

   Uses a sandwich argument with piecewise linear test functions. *)
let CHAR_FN_DETERMINES_NORMAL_CDF_LIMIT = prove
 (`!p:A prob_space (X:num->A->real) x l.
     (!n. simple_rv p (X n)) /\
     (?C. &0 < C /\ !n. simple_expectation p (\x. X n x pow 2) <= C) /\
     (!t. ((\n. char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
          sequentially) /\
     (!t. ((\n. char_fn_im p (X n) t) ---> &0) sequentially) /\
     ((\n. simple_cdf p (X n) x) ---> l) sequentially
     ==> l = std_normal_cdf x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_LIMIT_SANDWICH THEN
  REWRITE_TAC[STD_NORMAL_CDF_CONTINUOUS] THEN
  X_GEN_TAC `h:real` THEN DISCH_TAC THEN
  CONJ_TAC THENL
  [(* ---- Lower bound: std_normal_cdf(x - h) <= l ---- *)
   ABBREV_TAC
     `g_low = \y:real. max (&0) (min (&1) (&1 - (y - (x - h)) / h))` THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC
     `real_integral (:real)
        (\y:real. g_low y * std_normal_density y)` THEN
   CONJ_TAC THENL
   [(* Phi(x-h) <= int g_low*density *)
    MATCH_MP_TAC CDF_LE_INTEGRAL_BOUNDED THEN
    EXPAND_TAC "g_low" THEN CONJ_TAC THENL
    [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
     SUBGOAL_THEN `&1 <= &1 - (y - (x - h)) / h` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&1 <= &1 - z <=> z <= &0`;
                    REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
     GEN_TAC THEN
     MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_CONST];
      MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_CONTINUOUS_CONST];
       MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_CONST];
        MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN CONJ_TAC THENL
        [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
         REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
         CONJ_TAC THENL
         [REWRITE_TAC[REAL_CONTINUOUS_CONST];
          ASM_REAL_ARITH_TAC]]]]]];
    ALL_TAC] THEN
   (* int g_low*density <= l: by limit comparison *)
   MP_TAC(ISPECL
     [`sequentially`;
      `\n:num. simple_expectation (p:A prob_space)
                 (\a:A. (g_low:real->real) ((X:num->A->real) n a))`;
      `\n:num. simple_cdf (p:A prob_space) ((X:num->A->real) n) x`;
      `real_integral (:real)
         (\y:real. (g_low:real->real) y * std_normal_density y)`;
      `l:real`]
     REALLIM_LE) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    CONJ_TAC THENL
    [(* E[g_low(X_n)] --> int g_low*density *)
     MATCH_MP_TAC WEAK_CONVERGENCE_FROM_CHAR_FN THEN
     ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL
     [(* ?C existential *)
      EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
     CONJ_TAC THENL
     [(* g_low continuous *)
      EXPAND_TAC "g_low" THEN GEN_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_CONTINUOUS_CONST];
       MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_CONST];
        MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_CONTINUOUS_CONST];
         MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
          REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
          CONJ_TAC THENL
          [REWRITE_TAC[REAL_CONTINUOUS_CONST];
           ASM_REAL_ARITH_TAC]]]]];
      (* g_low bounded *)
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
      GEN_TAC THEN EXPAND_TAC "g_low" THEN REAL_ARITH_TAC];
     ALL_TAC] THEN
    (* E[g_low(X_n)] <= F_n(x) eventually *)
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC EXPECTATION_LE_CDF THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "g_low" THEN CONJ_TAC THENL
    [(* g_low(y) <= 1 for y <= x *)
     GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
     (* g_low(y) <= 0 for y > x *)
     X_GEN_TAC `y:real` THEN DISCH_TAC THEN
     SUBGOAL_THEN `&1 - (y - (x - h)) / h < &0` MP_TAC THENL
     [SUBGOAL_THEN `&1 < (y - (x - h)) / h`
        (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]];
    SIMP_TAC[]];

   (* ---- Upper bound: l <= std_normal_cdf(x + h) ---- *)
   ABBREV_TAC
     `g_up = \y:real. max (&0) (min (&1) ((x + h - y) / h))` THEN
   MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC
     `real_integral (:real)
        (\y:real. g_up y * std_normal_density y)` THEN
   CONJ_TAC THENL
   [(* l <= int g_up*density: by limit comparison *)
    MP_TAC(ISPECL
      [`sequentially`;
       `\n:num. simple_cdf (p:A prob_space) ((X:num->A->real) n) x`;
       `\n:num. simple_expectation (p:A prob_space)
                  (\a:A. (g_up:real->real) ((X:num->A->real) n a))`;
       `l:real`;
       `real_integral (:real)
          (\y:real. (g_up:real->real) y * std_normal_density y)`]
      REALLIM_LE) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
     CONJ_TAC THENL
     [(* E[g_up(X_n)] --> int g_up*density *)
      MATCH_MP_TAC WEAK_CONVERGENCE_FROM_CHAR_FN THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
      [(* ?C existential *)
       EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
      CONJ_TAC THENL
      [(* g_up continuous *)
       EXPAND_TAC "g_up" THEN GEN_TAC THEN
       MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_CONST];
        MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_CONTINUOUS_CONST];
         MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN CONJ_TAC THENL
          [REWRITE_TAC[REAL_CONTINUOUS_CONST];
           MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
           REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_AT_ID]];
          CONJ_TAC THENL
          [REWRITE_TAC[REAL_CONTINUOUS_CONST];
           ASM_REAL_ARITH_TAC]]]];
       (* g_up bounded *)
       EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
       GEN_TAC THEN EXPAND_TAC "g_up" THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
     (* F_n(x) <= E[g_up(X_n)] eventually *)
     REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
     EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     MATCH_MP_TAC CDF_LE_EXPECTATION THEN ASM_REWRITE_TAC[] THEN
     EXPAND_TAC "g_up" THEN CONJ_TAC THENL
     [(* g_up(y) >= 1 for y <= x *)
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&1 <= (x + h - y) / h` MP_TAC THENL
      [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
       REAL_ARITH_TAC];
      (* g_up(y) >= 0 for y > x *)
      GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC];
     SIMP_TAC[]];

    (* int g_up*density <= Phi(x+h) *)
    MATCH_MP_TAC INTEGRAL_BOUNDED_LE_CDF THEN
    EXPAND_TAC "g_up" THEN CONJ_TAC THENL
    [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
     SUBGOAL_THEN `(x + h - y) / h < &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
     GEN_TAC THEN
     MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_CONST];
      MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_CONTINUOUS_CONST];
       MATCH_MP_TAC REAL_CONTINUOUS_DIV_ATREAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_CONTINUOUS_CONST];
         MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
         REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_AT_ID]];
        CONJ_TAC THENL
        [REWRITE_TAC[REAL_CONTINUOUS_CONST];
         ASM_REAL_ARITH_TAC]]]]]]]);;

(* ========================================================================= *)
(* LEVY CONTINUITY THEOREM (bridge from char fn to distribution)             *)
(* ========================================================================= *)

(* Levy's continuity theorem (one direction, specialized for CLT):
   If the characteristic functions converge pointwise to the
   characteristic function of N(0,1), and second moments are bounded,
   then the CDFs converge to the standard normal CDF.

   The bounded second moment hypothesis gives tightness via
   SIMPLE_TIGHTNESS_FROM_SECOND_MOMENTS. The CDF convergence step (Step 2)
   uses Helly's selection theorem + Fourier uniqueness. *)
let SIMPLE_LEVY_CONTINUITY_CLT = prove
 (`!p:A prob_space (X:num->A->real).
    (!n. simple_rv p (X n)) /\
    (?C. &0 < C /\
         !n. simple_expectation p (\x. (X:num->A->real) n x pow 2) <= C) /\
    (!t. ((\n. char_fn_re p (X n) t) ---> exp(--(t pow 2 / &2)))
         sequentially) /\
    (!t. ((\n. char_fn_im p (X n) t) ---> &0) sequentially)
    ==> !x. ((\n. simple_cdf p (X n) x) ---> std_normal_cdf x) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN
  (* Step 1: Tightness from bounded second moments *)
  SUBGOAL_THEN
    `!e. &0 < e ==>
     ?M. &0 < M /\
     ?N:num. !n. N <= n ==>
       prob (p:A prob_space) {a | a IN prob_carrier p /\
                                   abs((X:num->A->real) n a) >= M} < e`
    ASSUME_TAC THENL
  [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `C:real`]
     SIMPLE_TIGHTNESS_FROM_SECOND_MOMENTS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: Apply subsequence convergence principle
     By REALLIM_SUBSEQ_SAME_LIMIT, it suffices to show every subsequence
     has a sub-subsequence with CDFs converging to std_normal_cdf at x *)
  MATCH_MP_TAC(ISPECL
    [`\n:num. simple_cdf (p:A prob_space) ((X:num->A->real) n) x`;
     `std_normal_cdf x`; `&1`] REALLIM_SUBSEQ_SAME_LIMIT) THEN
  BETA_TAC THEN CONJ_TAC THENL
  [(* CDFs are bounded by 1 in absolute value *)
   GEN_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= &1 ==> abs a <= &1`) THEN
   MATCH_MP_TAC SIMPLE_CDF_BOUNDS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* For each subsequence r, find convergent sub-subsequence *)
  X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
  (* Step 2a: By Bolzano-Weierstrass, extract convergent sub-subsequence *)
  MP_TAC(ISPECL
    [`\k:num. simple_cdf (p:A prob_space) ((X:num->A->real) ((r:num->num) k)) x`;
     `&1`] BOUNDED_REAL_SEQ_HAS_CONVERGENT_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
  [GEN_TAC THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= &1 ==> abs a <= &1`) THEN
   MATCH_MP_TAC SIMPLE_CDF_BOUNDS THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real`
    (X_CHOOSE_THEN `s:num->num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s:num->num` THEN ASM_REWRITE_TAC[] THEN
  (* Step 2b: The subsequential limit must equal std_normal_cdf x.
     Apply CHAR_FN_DETERMINES_NORMAL_CDF_LIMIT to the sub-subsequence. *)
  SUBGOAL_THEN `l:real = std_normal_cdf x` SUBST_ALL_TAC THENL
  [MP_TAC(ISPECL
     [`p:A prob_space`;
      `\k:num. (X:num->A->real) ((r:num->num) ((s:num->num) k))`;
      `x:real`; `l:real`]
     CHAR_FN_DETERMINES_NORMAL_CDF_LIMIT) THEN
   BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
    [GEN_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [(* char_fn_re convergence along r o s *)
     X_GEN_TAC `t:real` THEN
     MP_TAC(ISPECL
       [`\n:num. char_fn_re (p:A prob_space) ((X:num->A->real) n) t`;
        `exp(--(t pow 2 / &2))`;
        `\k:num. (r:num->num) ((s:num->num) k)`]
       REALLIM_SUBSEQUENCE) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [(* char_fn_im convergence along r o s *)
     X_GEN_TAC `t:real` THEN
     MP_TAC(ISPECL
       [`\n:num. char_fn_im (p:A prob_space) ((X:num->A->real) n) t`;
        `&0`;
        `\k:num. (r:num->num) ((s:num->num) k)`]
       REALLIM_SUBSEQUENCE) THEN
     BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[]];
   ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* CENTRAL LIMIT THEOREM - CONVERGENCE IN DISTRIBUTION                       *)
(* ========================================================================= *)

(* Characteristic function scaling under division *)
let CHAR_FN_RE_DIV = prove
 (`!p:A prob_space (X:A->real) c t.
     char_fn_re p (\x. X x / c) t = char_fn_re p X (t / c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[char_fn_re; real_div] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

let CHAR_FN_IM_DIV = prove
 (`!p:A prob_space (X:A->real) c t.
     char_fn_im p (\x. X x / c) t = char_fn_im p X (t / c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[char_fn_im; real_div] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

(* Simple RV closure under division *)
let SIMPLE_RV_DIV = prove
 (`!p:A prob_space X c.
     simple_rv p X ==> simple_rv p (\x. X x / c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. (X:A->real) x / c) = (\x. inv(c) * X x)` SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM; real_div] THEN GEN_TAC THEN REAL_ARITH_TAC;
   MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]]);;

let SIMPLE_RV_SUM_DIV = prove
 (`!p:A prob_space (X:num->A->real) n c.
     (!k. simple_rv p (X k))
     ==> simple_rv p (\a. sum(0..n) (\i. X i a) / c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_RV_DIV THEN
  MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[]);;

(* CLT: The standardized sum of IID random variables with mean 0 and
   finite variance converges in distribution to the standard normal.
   This combines CLT_VARIANCE_FORM with SIMPLE_LEVY_CONTINUITY_CLT. *)
let CLT_CONVERGENCE_IN_DISTRIBUTION = prove
 (`!p:A prob_space (X:num->A->real).
    (!n. simple_rv p (X n)) /\
    (!i. simple_expectation p (X i) = &0) /\
    &0 < simple_variance p (X 0) /\
    (!i. simple_variance p (X i) = simple_variance p (X 0)) /\
    (!i j. ~(i = j) ==> indep_rv p (X i) (X j)) /\
    (!i t. char_fn_re p (X i) t = char_fn_re p (X 0) t /\
           char_fn_im p (X i) t = char_fn_im p (X 0) t) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> !x. ((\n. simple_cdf p
                (\a. sum(0..n) (\i. X i a) /
                     (sqrt(simple_variance p (X 0)) * sqrt(&(SUC n)))) x)
             ---> std_normal_cdf x) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`p:A prob_space`;
     `\n:num. \a:A. sum(0..n) (\i. (X:num->A->real) i a) /
                    (sqrt(simple_variance p (X 0)) * sqrt(&(SUC n)))`]
    SIMPLE_LEVY_CONTINUITY_CLT) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
  [FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   ABBREV_TAC `sigma2 = simple_variance (p:A prob_space) ((X:num->A->real) 0)` THEN
   REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SIMPLE_RV_SUM_DIV THEN ASM_REWRITE_TAC[];

    (* Bounded second moments for standardized sums: E[S_n^2] <= 2 *)
    EXISTS_TAC `&2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 < sigma2` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt sigma2` ASSUME_TAC THENL
    [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt(&(SUC n))` ASSUME_TAC THENL
    [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
     ALL_TAC] THEN
    SUBGOAL_THEN `~(sqrt sigma2 * sqrt(&(SUC n)) = &0)` ASSUME_TAC THENL
    [MATCH_MP_TAC (REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
     MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `simple_rv (p:A prob_space) (\a:A. sum(0..n) (\i. (X:num->A->real) i a))`
      ASSUME_TAC THENL
    [MATCH_MP_TAC SIMPLE_RV_SUM_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                    `\a:A. sum(0..n) (\i. (X:num->A->real) i a)`;
                    `sqrt sigma2 * sqrt(&(SUC n))`]
      SIMPLE_EXPECTATION_POW2_DIV) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
         (\a:A. sum(0..n) (\i. (X:num->A->real) i a)) = &0`
      ASSUME_TAC THENL
    [MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `n:num`]
        SIMPLE_EXPECTATION_SUM_ZERO) THEN
     ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `simple_expectation (p:A prob_space)
         (\x:A. (sum(0..n) (\i. (X:num->A->real) i x)) pow 2) =
       simple_variance p (\a. sum(0..n) (\i. X i a))`
      SUBST1_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIMPLE_VARIANCE_MEAN_ZERO THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `simple_variance (p:A prob_space)
         (\a:A. sum(0..n) (\i. (X:num->A->real) i a)) = &(SUC n) * sigma2`
      SUBST1_TAC THENL
    [EXPAND_TAC "sigma2" THEN
     MATCH_MP_TAC SIMPLE_VARIANCE_SUM_IID THEN
     REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_COVARIANCE_INDEP THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `(sqrt sigma2 * sqrt (&(SUC n))) pow 2 = sigma2 * &(SUC n)`
      SUBST1_TAC THENL
    [REWRITE_TAC[REAL_POW_MUL] THEN
     SUBGOAL_THEN `sqrt sigma2 pow 2 = sigma2` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `sqrt (&(SUC n)) pow 2 = &(SUC n)` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
     REWRITE_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sigma2 * &(SUC n)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN
     ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_0];
     ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&(SUC n) * sigma2 = sigma2 * &(SUC n)` SUBST1_TAC THENL
    [MESON_TAC[REAL_MUL_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC (REAL_ARITH `&0 <= x ==> x <= &2 * x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POS]];

    X_GEN_TAC `t:real` THEN EXPAND_TAC "sigma2" THEN
    REWRITE_TAC[CHAR_FN_RE_DIV] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `t:real`]
      CLT_VARIANCE_FORM) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]];
    X_GEN_TAC `t:real` THEN EXPAND_TAC "sigma2" THEN
    REWRITE_TAC[CHAR_FN_IM_DIV] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `X:num->A->real`; `t:real`]
      CLT_VARIANCE_FORM) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]];
   SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Agreement theorems: general definitions equal simple definitions          *)
(* ------------------------------------------------------------------------- *)

let GEN_CDF_SIMPLE_AGREE = prove
 (`!p:A prob_space X x. gen_cdf p X x = simple_cdf p X x`,
  REWRITE_TAC[gen_cdf; simple_cdf]);;

(* Agreement: gen_char_fn_re = char_fn_re for simple RVs *)
let GEN_CHAR_FN_RE_SIMPLE = prove
 (`!p:A prob_space X t. simple_rv p X ==> gen_char_fn_re p X t = char_fn_re p X t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gen_char_fn_re; char_fn_re] THEN
  MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
  MATCH_MP_TAC SIMPLE_RV_REAL_COMPOSE THEN
  MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]);;

(* Agreement: gen_char_fn_im = char_fn_im for simple RVs *)
let GEN_CHAR_FN_IM_SIMPLE = prove
 (`!p:A prob_space X t. simple_rv p X ==> gen_char_fn_im p X t = char_fn_im p X t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gen_char_fn_im; char_fn_im] THEN
  MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN
  MATCH_MP_TAC SIMPLE_RV_REAL_COMPOSE THEN
  MATCH_MP_TAC SIMPLE_RV_CMUL THEN ASM_REWRITE_TAC[]);;

(* General CLT: stated with general definitions, reduces to simple CLT *)
let GENERAL_CLT = prove
 (`!p:A prob_space (X:num->A->real).
    (!n. simple_rv p (X n)) /\
    (!i. expectation p (X i) = &0) /\
    &0 < variance p (X 0) /\
    (!i. variance p (X i) = variance p (X 0)) /\
    (!i j. ~(i = j) ==> indep_rv p (X i) (X j)) /\
    (!i t. gen_char_fn_re p (X i) t = gen_char_fn_re p (X 0) t /\
           gen_char_fn_im p (X i) t = gen_char_fn_im p (X 0) t) /\
    (!n k. k < n ==> indep_rv p (\x. sum(0..k) (\i. X i x)) (X (SUC k)))
    ==> !x. ((\n. gen_cdf p
                (\a. sum(0..n) (\i. X i a) /
                     (sqrt(variance p (X 0)) * sqrt(&(SUC n)))) x)
             ---> std_normal_cdf x) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Rewrite gen_cdf to simple_cdf *)
  REWRITE_TAC[GEN_CDF_SIMPLE_AGREE] THEN
  (* Rewrite variance to simple_variance *)
  SUBGOAL_THEN `variance (p:A prob_space) ((X:num->A->real) 0) =
                simple_variance p (X 0)` SUBST1_TAC THENL
  [MATCH_MP_TAC VARIANCE_SIMPLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Apply the simple CLT *)
  MATCH_MP_TAC CLT_CONVERGENCE_IN_DISTRIBUTION THEN
  (* Establish intermediate agreement facts *)
  SUBGOAL_THEN `!i:num. simple_expectation (p:A prob_space)
    ((X:num->A->real) i) = expectation p (X i)` ASSUME_TAC THENL
  [GEN_TAC THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC EXPECTATION_SIMPLE_AGREE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!i:num. simple_variance (p:A prob_space)
    ((X:num->A->real) i) = variance p (X i)` ASSUME_TAC THENL
  [GEN_TAC THEN CONV_TAC SYM_CONV THEN
   MATCH_MP_TAC VARIANCE_SIMPLE THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `!i:num t:real.
    char_fn_re (p:A prob_space) ((X:num->A->real) i) t =
      gen_char_fn_re p (X i) t /\
    char_fn_im p (X i) t = gen_char_fn_im p (X i) t` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEN_CHAR_FN_RE_SIMPLE THEN
    ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEN_CHAR_FN_IM_SIMPLE THEN
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [ASM_REWRITE_TAC[];
   GEN_TAC THEN ASM_MESON_TAC[];
   ASM_MESON_TAC[];
   GEN_TAC THEN ASM_MESON_TAC[];
   ASM_REWRITE_TAC[];
   REPEAT GEN_TAC THEN ASM_MESON_TAC[];
   ASM_REWRITE_TAC[]]);;

