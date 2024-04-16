(* ========================================================================= *)
(* Integer-only version of divstep with d = 2 * delta                        *)
(* ========================================================================= *)

needs "Divstep/divstep.ml";;

(* ------------------------------------------------------------------------- *)
(* A few ad-hoc results about integer 2x2 vectors and matrices.              *)
(* These are analogs of things in Multivariate/vectors.ml but for integers.  *)
(* ------------------------------------------------------------------------- *)

let FORALL_2 = prove
 (`!P. (!i. 1 <= i /\ i <= 2 ==> P i) <=> P 1 /\ P 2`,
  MESON_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`]);;

let VECTOR_2 = prove
 (`(vector[x;y]:A^2)$1 = x /\
   (vector[x;y]:A^2)$2 = y`,
  SIMP_TAC[vector; LAMBDA_BETA; DIMINDEX_2; ARITH; LENGTH; EL] THEN
  REWRITE_TAC[num_CONV `1`; HD; TL; EL]);;

let ISUM_2 = prove
 (`!t. isum(1..2) t = t(1) + t(2)`,
  REWRITE_TAC[num_CONV `2`; NUMSEG_CLAUSES; NUMSEG_SING] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[ISUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; IN_SING] THEN
  CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC);;

let imat_I = define
  `imat_I:int^2^2 = lambda i j. if i = j then &1 else &0`;;

let imat_mul = define
  `(imat_mul:int^2^2->int^2^2->int^2^2) m n =
        lambda i j. isum(1..2) (\k. m$i$k * n$k$j)`;;

let imat_vmul = define
  `(imat_vmul:int^2^2->int^2->int^2) m v =
        lambda i. isum(1..2) (\j. m$i$j * v$j)`;;

let IMAT_I = prove
 (`imat_vmul imat_I = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM; imat_vmul; imat_I] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_2; ARITH; FORALL_2; ISUM_2] THEN
  INT_ARITH_TAC);;

let IMAT_MUL = prove
 (`!m1 m2. imat_vmul (imat_mul m1 m2) = imat_vmul m1 o imat_vmul m2`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; imat_vmul; imat_mul] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_2; ARITH; FORALL_2; ISUM_2] THEN
  INT_ARITH_TAC);;

let IMAT_MUL_LID = prove
 (`!m. imat_mul imat_I m = m`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; imat_I; LAMBDA_BETA;
           imat_mul; ARITH; ISUM_2] THEN
  INT_ARITH_TAC);;

let IMAT_MUL_ASSOC = prove
 (`!m1 m2 m3. imat_mul m1 (imat_mul m2 m3) = imat_mul (imat_mul m1 m2) m3`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; imat_I; LAMBDA_BETA;
           imat_mul; ARITH; ISUM_2] THEN
  INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A integer-only divstep with d scaled up by a factor of 2. To maintain     *)
(* the connection with "divstep", the initial d should be odd, in which      *)
(* case it stays odd (so the d >= 0 versus d > 0 distinction makes no        *)
(* difference). In practice we assume the iterations start with d = 1,       *)
(* corresponding to the real delta = 1/2 in the canonical "divstep", which   *)
(* seems to give the best bounds.                                            *)
(* ------------------------------------------------------------------------- *)

let idivstep = new_definition
  `idivstep(d:int,f:int,g:int) =
        if d >= &0 /\ g rem &2 = &1
        then &2 - d, g, (g - f) div &2
        else &2 + d, f, (g + (g rem &2) * f) div &2`;;

let IDIVSTEP_STAYS_ODD = prove
 (`!d f g d' f' g'.
         d rem &2 = &1 /\ idivstep(d,f,g) = d',f',g' ==> d' rem &2 = &1`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[idivstep] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ONCE_REWRITE_TAC[GSYM INT_ADD_REM; GSYM INT_SUB_REM] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let IDIVSTEP_STAYS_ZERO = prove
 (`!d f g d' f' g'.
         g = &0 /\ idivstep(d,f,g) = d',f',g' ==> g' = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[idivstep] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[PAIR_EQ; INT_MUL_LZERO] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Iterated and componentwise versions of idivstep                           *)
(* ------------------------------------------------------------------------- *)

let divstep_d = define
 `divstep_d n t = FST(ITER n idivstep t)`;;

let divstep_f = define
 `divstep_f n t = FST(SND(ITER n idivstep t))`;;

let divstep_g = define
 `divstep_g n t = SND(SND(ITER n idivstep t))`;;

let DIVSTEP_DFG = prove
 (`(divstep_d n t,divstep_f n t,divstep_g n t) = ITER n idivstep t`,
  REWRITE_TAC[divstep_d; divstep_f; divstep_g]);;

let DIVSTEP_D = prove
 (`divstep_d 0 (d,f,g) = d /\
   divstep_d (SUC n) t =
   if divstep_d n t >= &0 /\ divstep_g n t rem &2 = &1
   then &2 - divstep_d n t else &2 + divstep_d n t`,
  REWRITE_TAC[ITER; divstep_d; divstep_g] THEN
  SPEC_TAC(`ITER n idivstep t`,`p:int#int#int`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; idivstep] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let DIVSTEP_F = prove
 (`divstep_f 0 (d,f,g) = f /\
   divstep_f (SUC n) t =
   if divstep_d n t >= &0 /\ divstep_g n t rem &2 = &1
   then divstep_g n t else divstep_f n t`,
  REWRITE_TAC[ITER; divstep_d; divstep_f; divstep_g] THEN
  SPEC_TAC(`ITER n idivstep t`,`p:int#int#int`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; idivstep] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let DIVSTEP_G = prove
 (`divstep_g 0 (d,f,g) = g /\
   divstep_g (SUC n) t =
   if divstep_d n t >= &0 /\ divstep_g n t rem &2 = &1
   then (divstep_g n t - divstep_f n t) div &2
   else (divstep_g n t + divstep_g n t rem &2 * divstep_f n t) div &2`,
  REWRITE_TAC[ITER; divstep_d; divstep_f; divstep_g] THEN
  SPEC_TAC(`ITER n idivstep t`,`p:int#int#int`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; idivstep] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let DIVSTEP_DFG_ADD = prove
 (`divstep_d (m + n) t =
   divstep_d m (divstep_d n t,divstep_f n t,divstep_g n t) /\
   divstep_f (m + n) t =
   divstep_f m (divstep_d n t,divstep_f n t,divstep_g n t) /\
   divstep_g (m + n) t =
   divstep_g m (divstep_d n t,divstep_f n t,divstep_g n t)`,
  REWRITE_TAC[divstep_d; divstep_f; divstep_g] THEN
  REWRITE_TAC[GSYM PAIR_EQ; ITER_ADD]);;

(* ------------------------------------------------------------------------- *)
(* The basic invariance and bound properties, often similar to pure divstep. *)
(* ------------------------------------------------------------------------- *)

let DIVSTEP_D_PARITY = prove
 (`!n d f g. divstep_d n (d,f,g) rem &2 = d rem &2`,
  REWRITE_TAC[MESON[INT_REM_2_DIVIDES; INT_REDUCE_CONV `&1:int = &0`]
        `x rem &2 = y rem &2 <=> (&2 divides x <=> &2 divides y)`] THEN
  INDUCT_TAC THEN REWRITE_TAC[DIVSTEP_D] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[INTEGER_RULE `p divides (p + x:int) <=> p divides x`] THEN
  REWRITE_TAC[INTEGER_RULE `p divides (p - x:int) <=> p divides x`] THEN
  ASM_REWRITE_TAC[]);;

let DIVSTEP_D_BOUND = prove
 (`!n d f g. abs(abs(divstep_d n (d,f,g)) - abs(d)) <= &2 * &n`,
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[DIVSTEP_D; GSYM INT_OF_NUM_SUC] THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_F_ODD = prove
 (`!n d f g. f rem &2 = &1 ==> divstep_f n (d,f,g) rem &2 = &1`,
  INDUCT_TAC THEN REWRITE_TAC[DIVSTEP_F] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let DIVSTEP_G_ZERO = prove
 (`!n d f g. g = &0 ==> divstep_g n (d,f,g) = &0`,
  INDUCT_TAC THEN REWRITE_TAC[DIVSTEP_G] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  ASM_SIMP_TAC[INT_MUL_LZERO; INT_ADD_RID] THEN
  CONV_TAC INT_REDUCE_CONV);;

let DIVSTEP_FG_GCD = prove
 (`!n d f g.
        f rem &2 = &1
        ==> gcd(divstep_f n (d,f,g),divstep_g n (d,f,g)) = gcd(f,g)`,
  let lemma = prove
   (`!m n. m rem &2 = &1 /\ n rem &2 = &0 ==> gcd(m,n div &2) = gcd(m,n)`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INT_REM_EQ_0]) THEN
    REWRITE_TAC[GSYM(CONJUNCT1 INT_MUL_DIV_EQ)] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SYM th]) THEN
    MATCH_MP_TAC INT_GCD_EQ THEN GEN_TAC THEN MATCH_MP_TAC(INTEGER_RULE
     `coprime(k:int,m)
      ==> (d divides m /\ d divides p <=>
           d divides m /\ d divides (k * p))`) THEN
    MP_TAC(SPECL [`m:int`; `&2:int`] INT_DIVISION_SIMP) THEN
    ASM_REWRITE_TAC[] THEN SPEC_TAC(`&2:int`,`p:int`) THEN
    CONV_TAC INTEGER_RULE) in
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[DIVSTEP_F; DIVSTEP_G] THEN
   DISJ_CASES_TAC(SPEC `divstep_g n (d,f,g)` INT_REM_2_CASES) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) lemma o lhand o snd) THEN
  ONCE_REWRITE_TAC[GSYM INT_SUB_REM; GSYM INT_ADD_REM] THEN
  ASM_SIMP_TAC[DIVSTEP_F_ODD; INT_MUL_LID; INT_MUL_LZERO] THEN
  CONV_TAC INT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC INT_GCD_EQ THEN CONV_TAC INTEGER_RULE);;

let DIVSTEP_F_BOUNDS,DIVSTEP_G_BOUNDS = (CONJ_PAIR o prove)
 (`(!B n d f g.
        --B <= f /\ f < B /\ --B <= g /\ g < B
        ==> --B <= divstep_f n (d,f,g) /\ divstep_f n (d,f,g) < B) /\
   (!B n d f g.
        --B <= f /\ f < B /\ --B <= g /\ g < B
        ==> --B <= divstep_g n (d,f,g) /\ divstep_g n (d,f,g) < B)`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  GEN_TAC THEN
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[DIVSTEP_F; DIVSTEP_G] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_DIV_LT_EQ; INT_LE_DIV_EQ; INT_ARITH `&0:int < &2`] THEN
  DISJ_CASES_THEN SUBST1_TAC (SPEC `divstep_g n (d,f,g)` INT_REM_2_CASES) THEN
  ASM_INT_ARITH_TAC);;

let DIVSTEP_F_BOUNDS_LT,DIVSTEP_G_BOUNDS_LT = (CONJ_PAIR o prove)
 (`(!B n d f g.
        --B < f /\ f < B /\ --B < g /\ g < B
        ==> --B < divstep_f n (d,f,g) /\ divstep_f n (d,f,g) < B) /\
   (!B n d f g.
        --B < f /\ f < B /\ --B < g /\ g < B
        ==> --B < divstep_g n (d,f,g) /\ divstep_g n (d,f,g) < B)`,
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  GEN_TAC THEN
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[DIVSTEP_F; DIVSTEP_G] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_DIV_LT_EQ; INT_LT_DIV_EQ; INT_ARITH `&0:int < &2`] THEN
  DISJ_CASES_THEN SUBST1_TAC (SPEC `divstep_g n (d,f,g)` INT_REM_2_CASES) THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The precise connection with with divstep, when starting at delta = 1/2.   *)
(* ------------------------------------------------------------------------- *)

let ITER_DIVSTEP_INTEGER = prove
 (`!f g n.
        ITER n divstep (&1 / &2,f,g) =
        (real_of_int(divstep_d n (&1,f,g)) / &2,
         divstep_f n (&1,f,g),
         divstep_g n (&1,f,g))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[divstep; ITER; DIVSTEP_D; DIVSTEP_F; DIVSTEP_G] THEN
  ASM_REWRITE_TAC[int_of_num_th; divstep] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 > &0 <=> x > &0`] THEN
  REWRITE_TAC[REAL_ARITH `&1 - x / &2 = (&2 - x) / &2`] THEN
  REWRITE_TAC[REAL_ARITH `&1 + x / &2 = (&2 + x) / &2`] THEN
  REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
  REWRITE_TAC[INT_ARITH `(x:int > &0) <=> ~(x = &0) /\ x >= &0`] THEN
  MP_TAC(SPECL [`n:num`; `&1:int`; `f:int`; `g:int`] DIVSTEP_D_PARITY) THEN
  ASM_CASES_TAC `divstep_d n (&1,f,g) = &0` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  DISCH_THEN(K ALL_TAC) THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Extended version of divstep with matrix updates                           *)
(* ------------------------------------------------------------------------- *)

let divstep_mat = define
 `divstep_mat 0 t = imat_I /\
  divstep_mat (SUC n) t =
    imat_mul
     (if divstep_d n t >= &0 /\ divstep_g n t rem &2 = &1
      then vector[vector[&0; &2]; vector[-- &1; &1]]
      else vector[vector[&2; &0];vector[divstep_g n t rem &2; &1]])
     (divstep_mat n t)`;;

let DIVSTEP_MAT = prove
 (`!d f g n.
        f rem &2 = &1
        ==> imat_vmul (divstep_mat n (d,f,g)) (vector[f;g]) =
            vector[&2 pow n * divstep_f n (d,f,g);
                   &2 pow n * divstep_g n (d,f,g)]`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[divstep_mat; DIVSTEP_F; DIVSTEP_G; IMAT_I; I_THM;
                  INT_POW; INT_MUL_LID] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IMAT_MUL; o_THM] THEN
  SIMP_TAC[imat_vmul; ISUM_2; FORALL_2; VECTOR_2; LAMBDA_BETA;
           DIMINDEX_2; CART_EQ] THEN
  (CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN
  REWRITE_TAC[INT_ARITH `(a:int) * x pow n = x pow n * a`] THEN
  REWRITE_TAC[INT_ARITH `(a:int) * x pow n * b = x pow n * a * b`] THEN
  REWRITE_TAC[GSYM INT_ADD_LDISTRIB; GSYM INT_SUB_LDISTRIB] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[INT_ARITH `-- &1 * x + &1 * y:int = y - x`] THEN
  REWRITE_TAC[INT_ARITH `x + &1 * y:int = y + x`] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[INT_MUL_DIV_EQ] THEN
  REWRITE_TAC[INT_2_DIVIDES_ADD; INT_2_DIVIDES_SUB; INT_2_DIVIDES_MUL] THEN
  REWRITE_TAC[GSYM(CONJUNCT1 INT_REM_2_DIVIDES)] THEN
  ASM_SIMP_TAC[DIVSTEP_F_ODD; INT_REM_REM] THEN INT_ARITH_TAC);;

let DIVSTEP_MAT_BOUNDS = prove
 (`!n t.
    --(&2 pow n) < divstep_mat n t$1$1 /\ divstep_mat n t$1$1 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$1$2 /\ divstep_mat n t$1$2 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$2$1 /\ divstep_mat n t$2$1 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$2$2 /\ divstep_mat n t$2$2 <= &2 pow n`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[divstep_mat; imat_I] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONV_TAC INT_REDUCE_CONV THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[imat_mul; LAMBDA_BETA; DIMINDEX_2; ARITH; ISUM_2; VECTOR_2] THEN
  DISJ_CASES_THEN SUBST1_TAC (SPEC `divstep_g n t` INT_REM_2_CASES) THEN
  REWRITE_TAC[INT_POW] THEN ASM_INT_ARITH_TAC);;

let DIVSTEP_MAT_ABS_BOUNDS = prove
 (`!n t.
    --(&2 pow n) < divstep_mat n t$1$1 /\ divstep_mat n t$1$1 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$1$2 /\ divstep_mat n t$1$2 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$2$1 /\ divstep_mat n t$2$1 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$2$2 /\ divstep_mat n t$2$2 <= &2 pow n /\
    abs(divstep_mat n t$1$1) + abs(divstep_mat n t$1$2) <= &2 pow n /\
    abs(divstep_mat n t$2$1) + abs(divstep_mat n t$2$2) <= &2 pow n`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[divstep_mat; imat_I] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  CONV_TAC INT_REDUCE_CONV THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[imat_mul; LAMBDA_BETA; DIMINDEX_2; ARITH; ISUM_2; VECTOR_2] THEN
  DISJ_CASES_THEN SUBST1_TAC (SPEC `divstep_g n t` INT_REM_2_CASES) THEN
  REWRITE_TAC[INT_POW] THEN ASM_INT_ARITH_TAC);;

let DIVSTEP_MAT_ADD = prove
 (`divstep_mat (m + n) t =
   imat_mul (divstep_mat m (divstep_d n t,divstep_f n t,divstep_g n t))
            (divstep_mat n t)`,
  SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; divstep_mat; DIVSTEP_DFG_ADD; IMAT_MUL_LID] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IMAT_MUL_LID; IMAT_MUL_ASSOC]);;

let DIVSTEP_MAT_DIAGONAL = prove
 (`!d f n.
        divstep_mat n (d,f,&0) $1$2 = &0 /\
        divstep_mat n (d,f,&0) $2$1 = &0`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[divstep_mat; imat_I; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  SIMP_TAC[DIVSTEP_G_ZERO] THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_SIMP_TAC[imat_mul; VECTOR_2; ISUM_2; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  INT_ARITH_TAC);;

let DIVSTEP_MAT_DIAGONAL_1 = prove
 (`!d f g n. g = &0 ==> divstep_mat n (d,f,g) $1$2 = &0`,
  MESON_TAC[DIVSTEP_MAT_DIAGONAL]);;

let DIVSTEP_MAT_DIAGONAL_2 = prove
 (`!d f g n. g = &0 ==> divstep_mat n (d,f,g) $2$1 = &0`,
  MESON_TAC[DIVSTEP_MAT_DIAGONAL]);;

(* ------------------------------------------------------------------------- *)
(* Invariance of divstep_d and divstep_mat under congruences.                *)
(* ------------------------------------------------------------------------- *)

let DIVSTEP_CONGRUENCE = prove
 (`!m d f g f' g' n.
        (f == f') (mod (&2 pow m)) /\ (g == g') (mod (&2 pow m)) /\ n <= m
        ==> divstep_d n (d,f,g) = divstep_d n (d,f',g') /\
            divstep_mat n (d,f,g) = divstep_mat n (d,f',g') /\
            (divstep_f n (d,f,g) == divstep_f n (d,f',g'))
            (mod (&2 pow (m - n))) /\
            (divstep_g n (d,f,g) == divstep_g n (d,f',g'))
            (mod (&2 pow (m - n)))`,
  REPLICATE_TAC 6 GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[divstep_mat; DIVSTEP_D; DIVSTEP_F; DIVSTEP_G; SUB_0] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `SUC n <= m ==> n <= m`)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `m - n = SUC(m - SUC n)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[INT_POW]] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN(SUBST1_TAC o REWRITE_RULE[GSYM INT_REM_EQ] o
    MATCH_MP (INTEGER_RULE
     `(a == b) (mod (c * d:int)) ==> (a == b) (mod c)`))) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC INT_CONG_DIV2) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN CONV_TAC INTEGER_RULE);;

let DIVSTEP_D_CONGRUENCE = prove
 (`!d f g f' g' n.
        (f == f') (mod (&2 pow n)) /\ (g == g') (mod (&2 pow n))
        ==> divstep_d n (d,f,g) = divstep_d n (d,f',g')`,
  MESON_TAC[DIVSTEP_CONGRUENCE; LE_REFL]);;

let DIVSTEP_D_CONGRUENCE_GEN = prove
 (`!d f g d' f' g' n.
        d = d' /\ (f == f') (mod (&2 pow n)) /\ (g == g') (mod (&2 pow n))
        ==> divstep_d n (d,f,g) = divstep_d n (d',f',g')`,
  MESON_TAC[DIVSTEP_CONGRUENCE; LE_REFL]);;

let DIVSTEP_MAT_CONGRUENCE = prove
 (`!d f g f' g' n.
        (f == f') (mod (&2 pow n)) /\ (g == g') (mod (&2 pow n))
        ==> divstep_mat n (d,f,g) = divstep_mat n (d,f',g')`,
  MESON_TAC[DIVSTEP_CONGRUENCE; LE_REFL]);;

let DIVSTEP_MAT_CONGRUENCE_GEN = prove
 (`!d f g d' f' g' n.
        d = d' /\ (f == f') (mod (&2 pow n)) /\ (g == g') (mod (&2 pow n))
        ==> divstep_mat n (d,f,g) = divstep_mat n (d',f',g')`,
  MESON_TAC[DIVSTEP_CONGRUENCE; LE_REFL]);;

let DIVSTEP_D_MOD = prove
 (`!m n d f g.
        m <= n
        ==> divstep_d m (d,f rem &2 pow n,g rem &2 pow n) =
            divstep_d m (d,f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVSTEP_D_CONGRUENCE THEN
  CONJ_TAC THEN MATCH_MP_TAC(INTEGER_RULE
   `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow n` THEN
  ASM_REWRITE_TAC[INT_CONG_LREM; INT_CONG_REFL] THEN
  ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP]);;

let DIVSTEP_MAT_MOD = prove
 (`!m n d f g.
        m <= n
        ==> divstep_mat m (d,f rem &2 pow n,g rem &2 pow n) =
            divstep_mat m (d,f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVSTEP_MAT_CONGRUENCE THEN
  CONJ_TAC THEN MATCH_MP_TAC(INTEGER_RULE
   `!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow n` THEN
  ASM_REWRITE_TAC[INT_CONG_LREM; INT_CONG_REFL] THEN
  ASM_SIMP_TAC[INT_DIVIDES_POW_LE_IMP]);;

(* ------------------------------------------------------------------------- *)
(* Invariance of divstep_d and divstep_mat under negation.                   *)
(* ------------------------------------------------------------------------- *)

let [DIVSTEP_D_NEG; DIVSTEP_MAT_NEG; DIVSTEP_F_NEG; DIVSTEP_G_NEG] =
 (CONJUNCTS o prove)
 (`(!n d f g.
      f rem &2 = &1 ==> divstep_d n (d,--f,--g) = divstep_d n (d,f,g)) /\
   (!n d f g.
      f rem &2 = &1 ==>  divstep_mat n (d,--f,--g) = divstep_mat n (d,f,g)) /\
   (!n d f g.
      f rem &2 = &1 ==> divstep_f n (d,--f,--g) = --(divstep_f n (d,f,g))) /\
   (!n d f g.
      f rem &2 = &1 ==> divstep_g n (d,--f,--g) = --(divstep_g n (d,f,g)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN
  REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
  ASM_CASES_TAC `f rem &2 = &1` THEN ASM_REWRITE_TAC[] THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[DIVSTEP_D; DIVSTEP_F; DIVSTEP_G; divstep_mat] THEN
  REWRITE_TAC[INT_REM_2_NEG] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `--x - --y:int = --(x - y)`] THEN
  REWRITE_TAC[INT_ARITH `--x + y * --z:int = --(x + y * z)`] THEN
  ASM_REWRITE_TAC[INT_DIV_LNEG] THEN REWRITE_TAC[INT_REM_2_DIVIDES] THEN
  REWRITE_TAC[INT_2_DIVIDES_ADD; INT_2_DIVIDES_SUB; INT_2_DIVIDES_MUL] THEN
  REWRITE_TAC[GSYM(CONJUNCT1 INT_REM_2_DIVIDES)] THEN
  ASM_SIMP_TAC[INT_REM_REM; DIVSTEP_F_ODD] THEN
  CONV_TAC INT_REDUCE_CONV);;

let DIVSTEP_CONGRUENCE_NEG = prove
 (`!m d f g f' g' n.
        (f == --f') (mod (&2 pow m)) /\ (g == --g') (mod (&2 pow m)) /\
        f rem &2 = &1 /\ n <= m
        ==> divstep_d n (d,f,g) = divstep_d n (d,f',g') /\
            divstep_mat n (d,f,g) = divstep_mat n (d,f',g') /\
            (divstep_f n (d,f,g) == --(divstep_f n (d,f',g')))
            (mod (&2 pow (m - n))) /\
            (divstep_g n (d,f,g) == --(divstep_g n (d,f',g')))
            (mod (&2 pow (m - n)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC(SPECL
    [`m:num`; `d:int`; `--f:int`; `--g:int`; `f':int`; `g':int`; `n:num`]
    DIVSTEP_CONGRUENCE) THEN
  ASM_SIMP_TAC[DIVSTEP_D_NEG; DIVSTEP_MAT_NEG;
               DIVSTEP_F_NEG; DIVSTEP_G_NEG] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
  `(--x:int == y) (mod p) <=> (x == --y) (mod p)`]);;

(* ------------------------------------------------------------------------- *)
(* A slightly different version called "hddivstep" and analyzed here         *)
(* https://github.com/sipa/safegcd-bounds                                    *)
(* This uses > and so corresponds more exactly to the canonical divstep      *)
(* regardless of the parity of d. But when d is odd, it is the same as       *)
(* the main "idivstep" here.                                                 *)
(* ------------------------------------------------------------------------- *)

let hdivstep = new_definition
  `hdivstep(d:int,f:int,g:int) =
        if d > &0 /\ g rem &2 = &1
        then &2 - d, g, (g - f) div &2
        else &2 + d, f, (g + (g rem &2) * f) div &2`;;

let HDIVSTEP_DIVSTEP = prove
 (`hdivstep(d,f,g) = d',f',g' <=>
   divstep(real_of_int d / &2,f,g) = real_of_int d' / &2,f',g'`,
  REWRITE_TAC[hdivstep; divstep] THEN
  REWRITE_TAC[REAL_ARITH `(x:real) / &2 > &0 <=> x > &0`] THEN
  REWRITE_TAC[int_gt; int_of_num_th] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ARITH `&1 - x / &2 = y / &2 <=> &2 - x = y`;
              REAL_ARITH `&1 + x / &2 = y / &2 <=> &2 + x = y`] THEN
  REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES]);;

let HDIVSTEP_IDIVSTEP = prove
 (`!d f g. d rem &2 = &1 ==> hdivstep(d,f,g) = idivstep(d,f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[idivstep; hdivstep] THEN
  REWRITE_TAC[INT_ARITH `d >= &0 <=> d:int = &0 \/ d > &0`] THEN
  ASM_CASES_TAC `d:int = &0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV);;
