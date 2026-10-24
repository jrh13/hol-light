(* ========================================================================= *)
(* Puiseux's theorem: the field of Puiseux series over an algebraically      *)
(* closed field of characteristic zero is algebraically closed.              *)
(*                                                                           *)
(* Plan:                                                                     *)
(*  1. The stretch t |-> t^d as a ring endomorphism of K[[t]], injective     *)
(*     for d > 0.                                                            *)
(*  2. Hensel's lemma for K[[t]][Y] (coprime factorizations lift).           *)
(*  3. Newton-Puiseux: after a Tschirnhaus shift and a Newton-polygon        *)
(*     rescaling, the reduction mod t of a monic polynomial over K[[t]] has  *)
(*     two coprime factors, so Hensel splits it and induction on degree      *)
(*     gives a root in some K[[t^(1/d)]].                                    *)
(*  4. K[[t^(1/oo)]], the union of the K[[t^(1/d)]], as a quotient of the    *)
(*     ring of eventually coherent sequences; every monic polynomial over    *)
(*     it has a root.                                                        *)
(*  5. The Puiseux field is its field of fractions, hence algebraically      *)
(*     closed by a general criterion for fraction fields of domains.         *)
(*                                                                           *)
(* Thus puiseux_powser is the direct-limit domain, while puiseux_ring is its *)
(* fraction field (the traditional field of Puiseux series).                 *)
(*                                                                           *)
(* Main theorem: ALGEBRAICALLY_CLOSED_PUISEUX_RING.                          *)
(* ========================================================================= *)

needs "Library/fieldtheory.ml";;

(* ------------------------------------------------------------------------- *)
(* The stretch f(t) |-> f(t^d) on univariate power series.                   *)
(* ------------------------------------------------------------------------- *)

let powser_stretch = new_definition
 `powser_stretch (r:A ring) d (f:(1->num)->A) =
        \m. if d divides m one then f (\v. m one DIV d) else ring_0 r`;;

let COEFF_POWSER_STRETCH = prove
 (`!(r:A ring) d f n.
        coeff n (powser_stretch r d f) =
        if d divides n then coeff (n DIV d) f else ring_0 r`,
  REWRITE_TAC[coeff; powser_stretch]);;

let POWSER_STRETCH_IN_CARRIER = prove
 (`!(r:A ring) d f.
        f IN ring_carrier(powser_ring r (:1))
        ==> powser_stretch r d f IN ring_carrier(powser_ring r (:1))`,
  REWRITE_TAC[GSYM RING_POWERSERIES; RING_POWERSERIES_COEFF] THEN
  REWRITE_TAC[COEFF_POWSER_STRETCH] THEN MESON_TAC[RING_0]);;

let POWSER_STRETCH_MUL = prove
 (`!(r:A ring) d f g.
        ~(d = 0) /\ ring_powerseries r f /\ ring_powerseries r g
        ==> powser_stretch r d (poly_mul r f g) =
            poly_mul r (powser_stretch r d f) (powser_stretch r d g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FUN_EQ_COEFF] THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[COEFF_POWSER_STRETCH; COEFF_POLY_MUL] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
      GEN_REWRITE_RULE I [divides]) THEN
    ASM_SIMP_TAC[DIV_MULT] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ring_sum r (IMAGE (\b. d * b) (0..m))
       (\a. ring_mul (r:A ring)
          (if d divides a then coeff (a DIV d) f else ring_0 r)
          (if d divides (d * m - a) then coeff ((d * m - a) DIV d) g
           else ring_0 r))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[RING_SUM_IMAGE; EQ_MULT_LCANCEL] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_NUMSEG; o_THM] THEN
      SIMP_TAC[GSYM LEFT_SUB_DISTRIB; DIVIDES_RMUL; DIVIDES_REFL] THEN
      ASM_SIMP_TAC[DIV_MULT];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_SUPERSET THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; IN_IMAGE] THEN
      ASM_SIMP_TAC[LE_MULT_LCANCEL; LE_0] THEN
      X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `(d:num) divides a` THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `b:num` SUBST_ALL_TAC o
          GEN_REWRITE_RULE I [divides]) THEN
        ASM_MESON_TAC[LE_MULT_LCANCEL];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_MUL_LZERO THEN
        COND_CASES_TAC THEN REWRITE_TAC[RING_0] THEN
        ASM_MESON_TAC[RING_POWERSERIES_COEFF]]];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
    X_GEN_TAC `a:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(d:num) divides a` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~((d:num) divides (n - a))` (fun th -> REWRITE_TAC[th])
      THENL
       [ASM_MESON_TAC[DIVIDES_ADD; ARITH_RULE `a <= n ==> a + (n - a) = n`];
        MATCH_MP_TAC RING_MUL_RZERO THEN
        ASM_MESON_TAC[RING_POWERSERIES_COEFF]];
      MATCH_MP_TAC RING_MUL_LZERO THEN
      COND_CASES_TAC THEN REWRITE_TAC[RING_0] THEN
      ASM_MESON_TAC[RING_POWERSERIES_COEFF]]]);;

let POWSER_STRETCH_STRETCH = prove
 (`!(r:A ring) d e f.
        powser_stretch r d (powser_stretch r e f) =
        powser_stretch r (d * e) f`,
  REWRITE_TAC[GSYM FUN_EQ_COEFF; COEFF_POWSER_STRETCH] THEN
  REWRITE_TAC[GSYM DIVIDES_DIVIDES_DIV_EQ; DIV_DIV] THEN MESON_TAC[]);;

let POWSER_STRETCH_1 = prove
 (`!(r:A ring) f. powser_stretch r 1 f = f`,
  REWRITE_TAC[GSYM FUN_EQ_COEFF; COEFF_POWSER_STRETCH; DIVIDES_1; DIV_1]);;

let RING_HOMOMORPHISM_POWSER_STRETCH = prove
 (`!(r:A ring) d.
        ring_homomorphism (powser_ring r (:1),powser_ring r (:1))
                          (powser_stretch r d)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d = 0` THENL
   [(* the degenerate case d = 0 keeps just the constant term *)
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_HOMOMORPHISM_EQ THEN
    EXISTS_TAC `(poly_const r:A->(1->num)->A) o coeff 0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `r:A ring` THEN
      REWRITE_TAC[POWSER_RING_HOMOMORPHISM_COEFF_0;
                  RING_HOMOMORPHISM_POWSER_CONST];
      REWRITE_TAC[GSYM FUN_EQ_COEFF; COEFF_POWSER_STRETCH; COEFF_POLY_CONST;
                  o_THM; DIVIDES_ZERO; DIV_ZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[RING_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[GSYM RING_POWERSERIES; POWSER_RING_CLAUSES] THEN
  ASM_SIMP_TAC[POWSER_STRETCH_MUL] THEN
  REWRITE_TAC[RING_POWERSERIES_COEFF; GSYM FUN_EQ_COEFF] THEN
  REWRITE_TAC[COEFF_POWSER_STRETCH; COEFF_POLY_ADD; COEFF_POLY_1] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[RING_0];
    X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[DIVIDES_0; DIV_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[DIV_EQ_0; GSYM NOT_LE; DIVIDES_LE_IMP];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_ADD_LZERO; RING_0]]);;

let RING_MONOMORPHISM_POWSER_STRETCH = prove
 (`!(r:A ring) d.
        ~(d = 0)
        ==> ring_monomorphism (powser_ring r (:1),powser_ring r (:1))
                              (powser_stretch r d)`,
  SIMP_TAC[ring_monomorphism; RING_HOMOMORPHISM_POWSER_STRETCH] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FUN_EQ_COEFF] THEN
  X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `coeff (d * n):((1->num)->A)->A`) THEN
  ASM_SIMP_TAC[COEFF_POWSER_STRETCH; DIVIDES_RMUL; DIVIDES_REFL;
               DIV_MULT]);;

let POWSER_STRETCH_VARPOW = prove
 (`!(r:A ring) d m.
        ~(d = 0)
        ==> powser_stretch r d (poly_pow r (poly_var r one) m) =
            poly_pow r (poly_var r one) (d * m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FUN_EQ_COEFF] THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[COEFF_POWSER_STRETCH; COEFF_POLY_VARPOW] THEN
  ASM_CASES_TAC `(d:num) divides n` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `c:num` SUBST1_TAC o
      REWRITE_RULE[divides]) THEN
    ASM_SIMP_TAC[DIV_MULT; EQ_MULT_LCANCEL];
    ASM_MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]]);;

let POWSER_STRETCH_VAR = prove
 (`!(r:A ring) d.
        ~(d = 0)
        ==> powser_stretch r d (poly_var r one) =
            poly_pow r (poly_var r one) d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `d:num`; `1`] POWSER_STRETCH_VARPOW) THEN
  ASM_SIMP_TAC[MULT_CLAUSES; poly_pow; RING_POW_1; POWSER_VAR_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* A univariate polynomial from a finitely supported coefficient sequence.   *)
(* ------------------------------------------------------------------------- *)

let POLY_FROM_COEFFS = prove
 (`!(r:A ring) (c:num->A) n.
        (!i. c i IN ring_carrier r) /\ (!i. n < i ==> c i = ring_0 r)
        ==> (\m:1->num. c (m one)) IN ring_carrier(poly_ring r (:1)) /\
            poly_deg r (\m:1->num. c (m one)) <= n /\
            (~(c n = ring_0 r) ==> poly_deg r (\m:1->num. c (m one)) = n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_powerseries r (\m:1->num. (c:num->A) (m one)) /\
    !i. ~(coeff i (\m:1->num. c (m one)) = ring_0 r) ==> i <= n`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RING_POWERSERIES_COEFF; coeff] THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    ASM_SIMP_TAC[NOT_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RING_POLYNOMIAL_COEFF_BOUND THEN ASM_MESON_TAC[];
    MATCH_MP_TAC POLY_DEG_LE_COEFF THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC POLY_DEG_EQ_COEFF THEN
    ASM_REWRITE_TAC[coeff]]);;

(* ------------------------------------------------------------------------- *)
(* Hensel's lemma. A polynomial over K[[t]] is viewed through its "layers",  *)
(* the polynomials over K given by the coefficients of t^j.                  *)
(* ------------------------------------------------------------------------- *)

let LAYER_IN_POLY_RING = prove
 (`!(k:A ring) (p:(1->num)->(1->num)->A) j.
        p IN ring_carrier(poly_ring (powser_ring k (:1)) (:1))
        ==> (coeff j o p) IN ring_carrier(poly_ring k (:1)) /\
            poly_deg k (coeff j o p) <= poly_deg (powser_ring k (:1)) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_powerseries k (coeff j o (p:(1->num)->(1->num)->A)) /\
    !i. ~(coeff i (coeff j o p) = ring_0 k)
        ==> i <= poly_deg (powser_ring k (:1)) p`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RING_POWERSERIES_COEFF; COEFF_COMPOSE] THEN
    CONJ_TAC THEN GEN_TAC THENL
     [ASM_MESON_TAC[COEFF_IN_CARRIER; RING_POWERSERIES; COEFF_IN_CARRIER_ALT];
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LE] THEN
      ASM_SIMP_TAC[ISPEC `powser_ring (k:A ring) (:1)` COEFF_ABOVE_DEG;
                   POWSER_RING; COEFF_POLY_0]];
    ASM_MESON_TAC[RING_POLYNOMIAL_COEFF_BOUND; POLY_DEG_LE_COEFF]]);;

let COEFF_LAYER_POLY_MUL = prove
 (`!(k:A ring) (p:(1->num)->(1->num)->A) q j.
        p IN ring_carrier(poly_ring (powser_ring k (:1)) (:1)) /\
        q IN ring_carrier(poly_ring (powser_ring k (:1)) (:1))
        ==> coeff j o poly_mul (powser_ring k (:1)) p q =
            ring_sum (poly_ring k (:1)) (0..j)
              (\i. poly_mul k (coeff i o p) (coeff (j - i) o q))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FUN_EQ_COEFF] THEN
  X_GEN_TAC `i:num` THEN
  SUBGOAL_THEN
   `!a. ring_powerseries k (coeff a (p:(1->num)->(1->num)->A)) /\
        ring_powerseries k (coeff a (q:(1->num)->(1->num)->A)) /\
        ring_polynomial k (coeff a o p) /\ ring_polynomial k (coeff a o q)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_POWERSERIES; COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL;
                  LAYER_IN_POLY_RING];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COEFF_POLY_SUM; FINITE_NUMSEG; RING_POLYNOMIAL_MUL] THEN
  REWRITE_TAC[COEFF_COMPOSE; COEFF_POLY_MUL; POWSER_RING_CLAUSES] THEN
  ASM_SIMP_TAC[COEFF_POWSER_SUM; FINITE_NUMSEG; RING_POWERSERIES_MUL;
               COEFF_POLY_MUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; RING_MUL; COEFF_IN_CARRIER]);;

let POLY_OF_LAYERS = prove
 (`!(k:A ring) (u:num->(1->num)->A) d.
        (!j. u j IN ring_carrier(poly_ring k (:1)) /\ poly_deg k (u j) <= d)
        ==> (\m n. coeff (m one) (u (n one))) IN
              ring_carrier(poly_ring (powser_ring k (:1)) (:1)) /\
            (!j. coeff j o (\m n. coeff (m one) (u (n one))) = u j) /\
            poly_deg (powser_ring k (:1))
                     (\m n. coeff (m one) (u (n one))) <= d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `q /\ p /\ r ==> p /\ q /\ r`) THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM FUN_EQ_COEFF; COEFF_COMPOSE; coeff]; ALL_TAC] THEN
  MP_TAC(ISPECL [`powser_ring (k:A ring) (:1)`;
                 `\i (n:1->num). coeff i ((u:num->(1->num)->A) (n one))`;
                 `d:num`] POLY_FROM_COEFFS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[GSYM RING_POWERSERIES; RING_POWERSERIES_COEFF; POWSER_RING;
              GSYM FUN_EQ_COEFF; COEFF_POLY_0] THEN
  ONCE_REWRITE_TAC[COEFF] THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL; COEFF_ABOVE_DEG;
                LET_TRANS]);;

let POLY_EQ_LAYERS = prove
 (`!(p:(1->num)->(1->num)->A) q.
        p = q <=> !j. coeff j o p = coeff j o q`,
  REWRITE_TAC[GSYM FUN_EQ_COEFF; COEFF_COMPOSE] THEN MESON_TAC[]);;

let POLY_COPRIME_SPLIT = prove
 (`!(k:A ring) f0 g0 h n.
        field k /\ ring_coprime (poly_ring k (:1)) (f0,g0) /\
        ~(f0 = poly_0 k) /\ h IN ring_carrier(poly_ring k (:1)) /\
        poly_deg k h <= n /\ poly_deg k f0 + poly_deg k g0 <= n
        ==> ?u v. u IN ring_carrier(poly_ring k (:1)) /\
                  v IN ring_carrier(poly_ring k (:1)) /\
                  (u = poly_0 k \/ poly_deg k u < poly_deg k f0) /\
                  poly_deg k f0 + poly_deg k v <= n /\
                  ring_add (poly_ring k (:1))
                    (ring_mul (poly_ring k (:1)) f0 v)
                    (ring_mul (poly_ring k (:1)) g0 u) = h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_COPRIME_IN_CARRIER) THEN
  MP_TAC(ISPECL [`poly_ring (k:A ring) (:1)`; `f0:(1->num)->A`;
                 `g0:(1->num)->A`] BEZOUT_RING_COPRIME) THEN
  ASM_SIMP_TAC[PID_IMP_BEZOUT_RING; PID_POLY_RING] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:(1->num)->A` (X_CHOOSE_THEN `y:(1->num)->A`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(f0:(1->num)->A = ring_0(poly_ring k (:1)))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[POLY_RING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `ring_mul (poly_ring k (:1)) h (y:(1->num)->A)`;
                 `f0:(1->num)->A`] POLY_DIVISION) THEN
  ASM_SIMP_TAC[RING_MUL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:(1->num)->A` (X_CHOOSE_THEN `u:(1->num)->A`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  ABBREV_TAC `v = ring_add (poly_ring k (:1))
                    (ring_mul (poly_ring k (:1)) h x)
                    (ring_mul (poly_ring k (:1)) g0 (w:(1->num)->A))` THEN
  SUBGOAL_THEN `(v:(1->num)->A) IN ring_carrier(poly_ring k (:1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN ASM_SIMP_TAC[RING_ADD; RING_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_add (poly_ring k (:1))
                  (ring_mul (poly_ring k (:1)) f0 v)
                  (ring_mul (poly_ring k (:1)) g0 (u:(1->num)->A)) = h /\
                ring_mul (poly_ring k (:1)) f0 v =
                ring_sub (poly_ring k (:1)) h
                  (ring_mul (poly_ring k (:1)) g0 u)`
  (DESTRUCT_TAC "split fv") THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
     `ring_add (r:B ring) (ring_mul r f0 x) (ring_mul r g0 y) = ring_1 r /\
      ring_add r (ring_mul r w f0) u = ring_mul r h y /\
      ring_add r (ring_mul r h x) (ring_mul r g0 w) = v
      ==> ring_add r (ring_mul r f0 v) (ring_mul r g0 u) = h /\
          ring_mul r f0 v = ring_sub r h (ring_mul r g0 u)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:(1->num)->A`; `v:(1->num)->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[POLY_RING]; ALL_TAC] THEN
  ASM_CASES_TAC `v = ring_0(poly_ring k (:1)):(1->num)->A` THENL
   [ASM_REWRITE_TAC[POLY_RING; POLY_DEG_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `f0:(1->num)->A`; `v:(1->num)->A`]
    POLY_DEG_MUL) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_POLYNOMIAL] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[POLY_RING]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REMOVE_THEN "fv" (SUBST1_TAC o REWRITE_RULE[POLY_RING_CLAUSES]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_SUB_LE o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[RING_POLYNOMIAL_MUL; RING_POLYNOMIAL]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `b <= n /\ c <= n ==> a <= MAX b c ==> a <= n`) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[RING_POLYNOMIAL]; ASM_ARITH_TAC];
    ASM_SIMP_TAC[POLY_RING; POLY_MUL_0; POLY_DEG_0; LE_0; RING_POLYNOMIAL]]);;

let HENSEL_LIFTING = prove
 (`!(k:A ring) q f0 g0.
        field k /\
        q IN ring_carrier(poly_ring (powser_ring k (:1)) (:1)) /\
        monic k f0 /\ ring_coprime (poly_ring k (:1)) (f0,g0) /\
        coeff 0 o q = poly_mul k f0 g0
        ==> ?f g. f IN ring_carrier(poly_ring (powser_ring k (:1)) (:1)) /\
                  g IN ring_carrier(poly_ring (powser_ring k (:1)) (:1)) /\
                  poly_mul (powser_ring k (:1)) f g = q /\
                  coeff 0 o f = f0 /\ coeff 0 o g = g0 /\
                  monic (powser_ring k (:1)) f /\
                  poly_deg (powser_ring k (:1)) f = poly_deg k f0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RING_COPRIME_IN_CARRIER) THEN
  SUBGOAL_THEN `~(f0 = poly_0 k:(1->num)->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MONIC_IMP_NONZERO; FIELD_IMP_NONTRIVIAL_RING;
                  RING_POLYNOMIAL];
    ALL_TAC] THEN
  (* A uniform bound N for the degrees of all the layers involved *)
  ABBREV_TAC
   `N = poly_deg (powser_ring k (:1)) (q:(1->num)->(1->num)->A) +
        poly_deg k (f0:(1->num)->A) + poly_deg k (g0:(1->num)->A)` THEN
  SUBGOAL_THEN
   `(!j. poly_deg k (coeff j o (q:(1->num)->(1->num)->A)) <= N) /\
    poly_deg k (f0:(1->num)->A) + poly_deg k (g0:(1->num)->A) <= N`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LAYER_IN_POLY_RING; LE_ADD; LE_TRANS; ADD_SYM]; ALL_TAC] THEN
  (* The layers H(n) = (f_n,g_n) of the factors, chosen recursively so    *)
  (* that f0 g_n + g0 f_n = E H n, the n-th layer of q minus the products *)
  (* f_i g_(n-i) with 0 < i < n                                           *)
  ABBREV_TAC
   `E = \(H:num->((1->num)->A)#((1->num)->A)) n.
          ring_sub (poly_ring k (:1)) (coeff n o (q:(1->num)->(1->num)->A))
            (ring_sum (poly_ring k (:1)) (1..n-1)
              (\i. ring_mul (poly_ring k (:1))
                     (FST(H i)) (SND(H(n - i)))))` THEN
  MP_TAC(ISPEC
   `\(H:num->((1->num)->A)#((1->num)->A)) n
     (y:((1->num)->A)#((1->num)->A)).
       FST y IN ring_carrier(poly_ring k (:1)) /\
       SND y IN ring_carrier(poly_ring k (:1)) /\
       poly_deg k (FST y) <= poly_deg k (f0:(1->num)->A) /\
       poly_deg k f0 + poly_deg k (SND y) <= N /\
       (n = 0 ==> y = (f0,g0)) /\
       (~(n = 0)
        ==> (FST y = poly_0 k \/ poly_deg k (FST y) < poly_deg k f0) /\
            ring_add (poly_ring k (:1))
              (ring_mul (poly_ring k (:1)) f0 (SND y))
              (ring_mul (poly_ring k (:1)) g0 (FST y)) = E H n)`
   (MATCH_MP WF_REC_EXISTS WF_num)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:num->((1->num)->A)#((1->num)->A)`;
                           `b:num->((1->num)->A)#((1->num)->A)`; `n:num`;
                           `y:((1->num)->A)#((1->num)->A)`] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(E:(num->((1->num)->A)#((1->num)->A))->num->(1->num)->A)
                    a n = E b n`
       (fun th -> REWRITE_TAC[th]) THEN
      EXPAND_TAC "E" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN BINOP_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`H:num->((1->num)->A)#((1->num)->A)`; `n:num`] THEN
    DISCH_TAC THEN ASM_CASES_TAC `n = 0` THENL
     [EXISTS_TAC `(f0:(1->num)->A,g0:(1->num)->A)` THEN
      ASM_REWRITE_TAC[LE_REFL];
      ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN
     `!i. i IN 1..n-1
          ==> ring_mul (poly_ring k (:1))
                (FST((H:num->((1->num)->A)#((1->num)->A)) i)) (SND(H(n - i)))
              IN ring_carrier(poly_ring k (:1)) /\
              poly_deg k (ring_mul (poly_ring k (:1))
                (FST(H i)) (SND(H(n - i)))) <= N`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n - i:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      ASM_SIMP_TAC[RING_MUL; POLY_RING_CLAUSES] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL] THEN
      MATCH_MP_TAC(ARITH_RULE `a + b <= n ==> x <= a + b ==> x <= n`) THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `poly_deg k (f0:(1->num)->A) +
                  poly_deg k (SND((H:num->((1->num)->A)#((1->num)->A))
                                  (n - i)))` THEN
      ASM_REWRITE_TAC[LE_ADD_RCANCEL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `f0:(1->num)->A`; `g0:(1->num)->A`;
                   `(E:(num->((1->num)->A)#((1->num)->A))->num->(1->num)->A)
                    H n`; `N:num`] POLY_COPRIME_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "E" THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUB THEN ASM_SIMP_TAC[LAYER_IN_POLY_RING; RING_SUM];
        MATCH_MP_TAC POLY_DEG_RING_SUB_LE THEN
        ASM_SIMP_TAC[LAYER_IN_POLY_RING; RING_SUM; POLY_DEG_RING_SUM_LE;
                     FINITE_NUMSEG]];
      REWRITE_TAC[EXISTS_PAIR_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `u:(1->num)->A` THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `v:(1->num)->A` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[POLY_DEG_0; LE_0; LT_IMP_LE]];
    DISCH_THEN(X_CHOOSE_THEN `H:num->((1->num)->A)#((1->num)->A)`
      (LABEL_TAC "inv"))] THEN
  SUBGOAL_THEN `(H:num->((1->num)->A)#((1->num)->A)) 0 = (f0,g0)`
  ASSUME_TAC THENL
   [USE_THEN "inv" (MP_TAC o SPEC `0`) THEN SIMP_TAC[]; ALL_TAC] THEN
  (* The layers of f g are those of q *)
  SUBGOAL_THEN
   `!n. ring_sum (poly_ring k (:1)) (0..n)
          (\i. ring_mul (poly_ring k (:1))
                 (FST((H:num->((1->num)->A)#((1->num)->A)) i))
                 (SND(H(n - i)))) = coeff n o q`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[NUMSEG_SING; RING_SUM_SING; SUB_REFL] THEN
      ASM_SIMP_TAC[RING_MUL; POLY_RING];
      ALL_TAC] THEN
    USE_THEN "inv" (MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[ASSUME `~(n = 0)`] THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_SIMP_TAC[RING_SUM_CLAUSES_LEFT; LE_0; RING_MUL; SUB_0;
                 ADD_CLAUSES] THEN
    ASM_SIMP_TAC[RING_SUM_CLAUSES_RIGHT; LE_1; RING_MUL; SUB_REFL] THEN
    ASM_SIMP_TAC[RING_MUL; RING_SUM; LE_1;
                 ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
     `ring_add (r:B ring) (ring_mul r a b) (ring_mul r c d) = ring_sub r q s
      ==> ring_add r (ring_mul r a b) (ring_add r s (ring_mul r d c)) =
          q`)) THEN
    ASM_SIMP_TAC[RING_SUM; LAYER_IN_POLY_RING];
    ALL_TAC] THEN
  (* Assemble the layers into f and g *)
  MP_TAC(ISPECL
   [`k:A ring`; `\j. FST((H:num->((1->num)->A)#((1->num)->A)) j)`;
    `poly_deg k (f0:(1->num)->A)`] POLY_OF_LAYERS) THEN
  MP_TAC(ISPECL
   [`k:A ring`; `\j. SND((H:num->((1->num)->A)#((1->num)->A)) j)`;
    `N - poly_deg k (f0:(1->num)->A)`] POLY_OF_LAYERS) THEN
  ASM_SIMP_TAC[ARITH_RULE `a + b <= N ==> b <= N - a`] THEN
  ABBREV_TAC `f = \m n. coeff (m one)
                     (FST((H:num->((1->num)->A)#((1->num)->A)) (n one)))` THEN
  ABBREV_TAC `g = \m n. coeff (m one)
                     (SND((H:num->((1->num)->A)#((1->num)->A)) (n one)))` THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`f:(1->num)->(1->num)->A`; `g:(1->num)->(1->num)->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[POLY_EQ_LAYERS] THEN
    ASM_SIMP_TAC[COEFF_LAYER_POLY_MUL] THEN
    X_GEN_TAC `j:num` THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `j:num` th)]) THEN
    REWRITE_TAC[POLY_RING];
    ALL_TAC] THEN
  (* f is monic of degree deg f0, its higher layers having lower degree *)
  SUBGOAL_THEN
   `coeff (poly_deg k (f0:(1->num)->A)) (f:(1->num)->(1->num)->A) =
    ring_1(powser_ring k (:1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[POWSER_RING; GSYM FUN_EQ_COEFF; COEFF_POLY_1] THEN
    X_GEN_TAC `j:num` THEN GEN_REWRITE_TAC LAND_CONV [GSYM COEFF_COMPOSE] THEN
    ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[GSYM monic] THEN
    USE_THEN "inv" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `~(j = 0)`] o
      SPEC `j:num`) THEN
    ASM_REWRITE_TAC[COEFF_POLY_0] THEN MATCH_MP_TAC COEFF_ABOVE_DEG THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC POLY_DEG_EQ_FROM_LE THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL; INTEGRAL_DOMAIN_NONTRIVIAL;
                 INTEGRAL_DOMAIN_POWSER_RING; FIELD_IMP_INTEGRAL_DOMAIN];
    ASM_SIMP_TAC[monic]]);;

(* ------------------------------------------------------------------------- *)
(* Coefficients of (X + c)^i, and a factorization lemma over an              *)
(* algebraically closed field of characteristic zero: a polynomial with      *)
(* vanishing subleading coefficient that is not a monomial c X^n splits into *)
(* two coprime factors of positive degree, the first one monic.              *)
(* ------------------------------------------------------------------------- *)

let COEFF_POLY_LINEAR_POW = prove
 (`!(r:A ring) c i j.
        c IN ring_carrier r
        ==> coeff j (poly_pow r (poly_add r (poly_var r one)
                                          (poly_const r c)) i) =
            ring_mul r (ring_of_num r (binom(i,j))) (ring_pow r c (i - j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`powser_ring (r:A ring) (:1)`; `i:num`;
                 `poly_var (r:A ring) one`; `poly_const r (c:A):(1->num)->A`]
    RING_BINOMIAL_THEOREM) THEN
  ASM_REWRITE_TAC[POWSER_VAR_UNIV; POWSER_CONST; POWSER_RING_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POWSER_SUM o lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; RING_OF_NUM_POWSER_RING] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_POWERSERIES_MUL; RING_POWERSERIES_POW; RING_OF_NUM;
                 RING_POWERSERIES_VAR; RING_POWERSERIES_CONST];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!m. poly_pow r (poly_const r c) m =
        poly_const r (ring_pow r c m):(1->num)->A`
  (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`r:A ring`; `powser_ring (r:A ring) (:1)`;
                   `poly_const (r:A ring):A->(1->num)->A`]
                  RING_HOMOMORPHISM_POW) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_POWSER_CONST; POWSER_RING_CLAUSES];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COEFF_POLY_LMUL; COEFF_POLY_RMUL; RING_POWERSERIES_MUL;
               RING_POWERSERIES_POW; RING_POWERSERIES_VAR; COEFF_POLY_VARPOW;
               RING_POWERSERIES_CONST; RING_OF_NUM; RING_POW] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `ring_sum r (0..i)
      (\a. if a = j
           then ring_mul r (ring_of_num r (binom(i,j)))
                           (ring_pow r (c:A) (i - j))
           else ring_0 r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `a:num = j` THEN
    ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_LZERO; RING_MUL_RZERO; RING_POW;
                 RING_OF_NUM];
    ASM_SIMP_TAC[RING_SUM_DELTA; IN_NUMSEG; LE_0; RING_MUL; RING_OF_NUM;
                 RING_POW] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[BINOM_LT; GSYM NOT_LE; RING_OF_NUM_0;
                                     RING_MUL_LZERO; RING_POW]]);;

let ALGEBRAICALLY_CLOSED_FIELD_COPRIME_FACTORS = prove
 (`!(k:A ring) q i.
        algebraically_closed_field k /\ ring_char k = 0 /\
        q IN ring_carrier(poly_ring k (:1)) /\
        coeff (poly_deg k q - 1) q = ring_0 k /\
        i < poly_deg k q /\ ~(coeff i q = ring_0 k)
        ==> ?f g. f IN ring_carrier(poly_ring k (:1)) /\
                  g IN ring_carrier(poly_ring k (:1)) /\
                  monic k f /\ ring_coprime (poly_ring k (:1)) (f,g) /\
                  0 < poly_deg k f /\ poly_deg k f < poly_deg k q /\
                  poly_mul k f g = q`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `n = poly_deg k (q:(1->num)->A)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(MP_TAC o SPEC `q:(1->num)->A` o CONJUNCT2 o
    GEN_REWRITE_RULE I [algebraically_closed_field]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L = poly_sub k (poly_var k one) (poly_const k (a:A))` THEN
  SUBGOAL_THEN `(L:(1->num)->A) IN ring_carrier(poly_ring k (:1)) /\
                poly_deg k L = 1 /\ monic k L`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    ASM_SIMP_TAC[POLY_X_MINUS_A_IN_CARRIER; POLY_DEG_X_MINUS_A;
                 FIELD_IMP_NONTRIVIAL_RING; monic] THEN
    EXPAND_TAC "L" THEN
    REWRITE_TAC[COEFF_POLY_SUB; COEFF_POLY_VAR; COEFF_POLY_CONST;
                ARITH_EQ] THEN
    ASM_SIMP_TAC[RING_SUB_RZERO; RING_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q:(1->num)->A = poly_0 k)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(coeff i (q:(1->num)->A) = ring_0 k)` THEN
    ASM_REWRITE_TAC[COEFF_POLY_0];
    ALL_TAC] THEN
  (* The maximal power of L dividing q *)
  MP_TAC(ISPEC `\m. ring_divides (poly_ring k (:1))
                     (ring_pow (poly_ring k (:1)) L m) (q:(1->num)->A)`
         num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ring_pow; RING_DIVIDES_1];
      EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `(:1)`;
                     `ring_pow (poly_ring k (:1)) L m:(1->num)->A`;
                     `q:(1->num)->A`] POLY_DEG_DIVIDES_LE) THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
      REWRITE_TAC[POLY_RING_CLAUSES] THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; POLY_DEG_POW; RING_POLYNOMIAL;
                   MULT_CLAUSES]];
    DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))] THEN
  GEN_REWRITE_TAC LAND_CONV [ring_divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(1->num)->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o SYM)) o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_POW_1] THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC POLY_DIVIDES_X_MINUS_ROOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_divides (poly_ring k (:1)) L (h:(1->num)->A))`
  ASSUME_TAC THENL
   [REWRITE_TAC[ring_divides] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h':(1->num)->A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m + 1`) THEN
    REWRITE_TAC[ARITH_RULE `~(m + 1 <= m)`; ring_divides] THEN
    ASM_SIMP_TAC[RING_POW] THEN EXISTS_TAC `h':(1->num)->A` THEN
    UNDISCH_TAC `ring_mul (poly_ring k (:1)) (ring_pow (poly_ring k (:1)) L m)
                   h = (q:(1->num)->A)` THEN
    ASM_SIMP_TAC[RING_POW_ADD; RING_POW_1; RING_MUL_ASSOC; RING_POW] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_coprime (poly_ring k (:1))
                  (ring_pow (poly_ring k (:1)) L m,h:(1->num)->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_COPRIME_LPOW THEN
    ASM_SIMP_TAC[PID_IMP_BEZOUT_RING; PID_POLY_RING;
                 INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_IRREDUCIBLE_COPRIME_EQ o
      snd) THEN
    ASM_SIMP_TAC[POLY_DEG_1_IMP_IRREDUCIBLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_deg k (ring_pow (poly_ring k (:1)) L m:(1->num)->A) = m /\
    monic k (ring_pow (poly_ring k (:1)) L m)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLY_RING_CLAUSES; POLY_DEG_POW; MONIC_POLY_POW;
                 RING_POLYNOMIAL; FIELD_IMP_INTEGRAL_DOMAIN; MULT_CLAUSES];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`ring_pow (poly_ring k (:1)) L m:(1->num)->A`; `h:(1->num)->A`] THEN
  ASM_SIMP_TAC[RING_POW; LE_1] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[POLY_RING]] THEN
  (* It remains to show m < n, i.e. that q is not c (X - a)^n *)
  SUBGOAL_THEN `~(ring_pow (poly_ring k (:1)) L m = poly_0 (k:A ring)) /\
                ~(h:(1->num)->A = poly_0 k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MONIC_IMP_NONZERO THEN
      ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING; RING_POLYNOMIAL; RING_POW];
      DISCH_TAC THEN
      UNDISCH_TAC `ring_mul (poly_ring k (:1))
                    (ring_pow (poly_ring k (:1)) L m) h = (q:(1->num)->A)` THEN
      ASM_SIMP_TAC[POLY_RING; POLY_MUL_0; RING_POLYNOMIAL; RING_POW] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `ring_pow (poly_ring k (:1)) L m:(1->num)->A`;
                 `h:(1->num)->A`] POLY_DEG_MUL) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_POLYNOMIAL; RING_POW] THEN
  SUBGOAL_THEN
   `poly_mul k (ring_pow (poly_ring k (:1)) L m) h = (q:(1->num)->A)`
  SUBST1_TAC THENL [ASM_MESON_TAC[POLY_RING]; ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `poly_deg k (h:(1->num)->A) = 0` THENL
   [ALL_TAC; ASM_ARITH_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `h:(1->num)->A`] POLY_DEG_EQ_0) THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `m:num = n` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `L = poly_add k (poly_var k one) (poly_const k (ring_neg k (a:A)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[POLY_SUB; POLY_CONST_NEG]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. coeff j (q:(1->num)->A) =
        ring_mul k (ring_mul k (ring_of_num k (binom(n,j)))
                               (ring_pow k (ring_neg k a) (n - j))) c`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    UNDISCH_TAC `ring_mul (poly_ring k (:1)) (ring_pow (poly_ring k (:1)) L n)
                   h = (q:(1->num)->A)` THEN
    ASM_REWRITE_TAC[POLY_RING_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_RMUL o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_POWERSERIES_POW; RING_POWERSERIES_ADD;
                   RING_POWERSERIES_VAR; RING_POWERSERIES_CONST; RING_NEG];
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[COEFF_POLY_LINEAR_POW; RING_NEG]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `~(c:A = ring_0 k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[POLY_CONST_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `a:A = ring_0 k` SUBST_ALL_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `n - 1`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `n - (n - 1) = 1 /\ binom(n,n - 1) = n`
     (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[BINOM_SYM; BINOM_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SYM) THEN
    ASM_SIMP_TAC[RING_POW_1; RING_NEG; RING_MUL; RING_OF_NUM] THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN;
                 RING_OF_NUM; RING_NEG; RING_MUL; RING_OF_NUM_EQ_0;
                 DIVIDES_ZERO; RING_NEG_EQ_0;
                 ARITH_RULE `1 <= n ==> ~(n = 0)`];
    ALL_TAC] THEN
  UNDISCH_TAC `~(coeff i (q:(1->num)->A) = ring_0 k)` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RING_NEG_0; RING_POW_ZERO; ARITH_RULE `i < n ==> ~(n - i = 0)`;
               RING_MUL_RZERO; RING_MUL_LZERO; RING_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Taylor shifts p(Y) |-> p(Y + c), and the Tschirnhaus transformation that  *)
(* kills the subleading coefficient of a monic polynomial of degree n over a *)
(* ring in which n is invertible.                                            *)
(* ------------------------------------------------------------------------- *)

let POLY_TAYLOR_SHIFT = prove
 (`!(r:A ring) p c.
        p IN ring_carrier(poly_ring r (:1)) /\ c IN ring_carrier r
        ==> ?s. s IN ring_carrier(poly_ring r (:1)) /\
                (!j. coeff j s =
                     ring_sum r (0..poly_deg r p)
                       (\i. ring_mul r (coeff i p)
                              (ring_mul r (ring_of_num r (binom(i,j)))
                                          (ring_pow r c (i - j))))) /\
                (!(r':B ring) h y.
                     ring_homomorphism(r,r') h /\ y IN ring_carrier r'
                     ==> poly_eval r' (h o s) y =
                         poly_eval r' (h o p) (ring_add r' y (h c)))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `ring_sum (poly_ring r (:1)) (0..poly_deg r p)
      (\i. ring_mul (poly_ring r (:1)) (poly_const r (coeff i p))
             (ring_pow (poly_ring r (:1))
               (ring_add (poly_ring r (:1)) (poly_var r one) (poly_const r c))
               i)):(1->num)->A` THEN
  REWRITE_TAC[RING_SUM] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN
    W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_SUM o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG; RING_POLYNOMIAL] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; RING_POW; RING_ADD; POLY_CONST; POLY_VAR_UNIV;
                   COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[POLY_RING_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_LMUL o lhand o snd) THEN
    ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL; RING_POWERSERIES_POW;
                 RING_POWERSERIES_ADD; RING_POWERSERIES_VAR;
                 RING_POWERSERIES_CONST] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[COEFF_POLY_LINEAR_POW];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r':B ring`; `h:A->B`; `y:B`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[poly_eval;
   GSYM(ISPECL [`r:A ring`; `r':B ring`; `h:A->B`] POLY_EXTEND_EVALUATE)] THEN
  SUBGOAL_THEN `(h:A->B) c IN ring_carrier r' /\
                !i. h(coeff i (p:(1->num)->A)) IN ring_carrier r'`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; COEFF_IN_CARRIER_ALT;
                  RING_POLYNOMIAL];
    ASM_SIMP_TAC[POLY_EXTEND_UNIVARIATE; RING_ADD]] THEN
  MP_TAC(ISPECL [`r:A ring`; `r':B ring`; `(:1)`; `h:A->B`; `(\v. y):1->B`]
    RING_HOMOMORPHISM_POLY_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
    (MATCH_MP RING_HOMOMORPHISM_SUM th) o lhand o snd)) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; RING_MUL; RING_POW; RING_ADD; POLY_CONST;
               POLY_VAR_UNIV; COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
    MATCH_MP RING_HOMOMORPHISM_POW th; MATCH_MP RING_HOMOMORPHISM_ADD th;
    RING_POW; RING_ADD; POLY_CONST; POLY_VAR_UNIV; COEFF_IN_CARRIER_ALT;
    RING_POLYNOMIAL]) THEN
  ASM_SIMP_TAC[POLY_EXTEND_CONST; POLY_EXTEND_VAR; COEFF_IN_CARRIER_ALT;
               RING_POLYNOMIAL]);;

let TSCHIRNHAUS = prove
 (`!(r:A ring) p.
        p IN ring_carrier(poly_ring r (:1)) /\ monic r p /\
        ~(poly_deg r p = 0) /\ ring_unit r (ring_of_num r (poly_deg r p))
        ==> ?c s. c IN ring_carrier r /\
                  s IN ring_carrier(poly_ring r (:1)) /\
                  monic r s /\ poly_deg r s = poly_deg r p /\
                  coeff (poly_deg r p - 1) s = ring_0 r /\
                  !(r':B ring) h y.
                        ring_homomorphism(r,r') h /\ y IN ring_carrier r'
                        ==> poly_eval r' (h o s) y =
                            poly_eval r' (h o p) (ring_add r' y (h c))`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `n = poly_deg r (p:(1->num)->A)` THEN
  ABBREV_TAC `c = ring_neg r (ring_mul r (ring_inv r (ring_of_num r n))
                       (coeff (n - 1) (p:(1->num)->A)))` THEN
  SUBGOAL_THEN `~(ring_1 r = ring_0 (r:A ring))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM TRIVIAL_RING_10] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`] TRIVIAL_RING_POLY_0) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[POLY_DEG_0]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. coeff i (p:(1->num)->A) IN ring_carrier r`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:A) IN ring_carrier r` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    ASM_SIMP_TAC[RING_NEG; RING_MUL; RING_INV; RING_OF_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i < j
          ==> ring_mul r (coeff i (p:(1->num)->A))
               (ring_mul r (ring_of_num r (binom(i,j)))
                           (ring_pow r c (i - j))) =
              ring_0 r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[BINOM_LT; RING_OF_NUM_0; RING_MUL_LZERO; RING_MUL_RZERO;
                 RING_POW];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `c:A`] POLY_TAYLOR_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(1->num)->A` (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "coeff") ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`c:A`; `s:(1->num)->A`] THEN
  SUBGOAL_THEN `!j. n < j ==> coeff j (s:(1->num)->A) = ring_0 r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "coeff" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN
    REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `coeff n (s:(1->num)->A) = ring_1 r` ASSUME_TAC THENL
   [USE_THEN "coeff" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ring_sum r (0..n)
                  (\i. if i = n then ring_1 r else ring_0(r:A ring))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN COND_CASES_TAC THENL
       [ASM_REWRITE_TAC[BINOM_REFL; SUB_REFL; ring_pow; RING_OF_NUM_1] THEN
        UNDISCH_TAC `monic r (p:(1->num)->A)` THEN
        ASM_REWRITE_TAC[monic] THEN
        DISCH_THEN SUBST1_TAC THEN SIMP_TAC[RING_MUL_LID; RING_1];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      REWRITE_TAC[RING_SUM_DELTA; IN_NUMSEG; LE_0; LE_REFL; RING_1]];
    ALL_TAC] THEN
  SUBGOAL_THEN `coeff (n - 1) (s:(1->num)->A) = ring_0 r` ASSUME_TAC THENL
   [USE_THEN "coeff" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ring_sum r {n - 1, n}
     (\i. ring_mul r (coeff i (p:(1->num)->A))
            (ring_mul r (ring_of_num r (binom(i,n - 1)))
                        (ring_pow r c (i - (n - 1)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_SUPERSET THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_NUMSEG; IN_INSERT;
                  NOT_IN_EMPTY] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[RING_SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY] THEN
    SUBGOAL_THEN `n - (n - 1) = 1 /\ binom(n,n - 1) = n /\ ~(n - 1 = n)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[BINOM_SYM; BINOM_1; LE_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[BINOM_REFL; SUB_REFL; ring_pow; RING_OF_NUM_1] THEN
    ASM_SIMP_TAC[RING_POW_1] THEN
    ASM_SIMP_TAC[RING_MUL; RING_1; RING_OF_NUM] THEN
    SUBGOAL_THEN `coeff n (p:(1->num)->A) = ring_1 r` SUBST1_TAC
    THENL [ASM_MESON_TAC[monic]; ALL_TAC] THEN
    EXPAND_TAC "c" THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
     `ring_mul (r:B ring) n m = ring_1 r
      ==> ring_add r (ring_mul r a (ring_mul r (ring_1 r) (ring_1 r)))
            (ring_add r (ring_mul r (ring_1 r)
                           (ring_mul r n (ring_neg r (ring_mul r m a))))
                        (ring_0 r)) =
          ring_0 r`)) THEN
    ASM_SIMP_TAC[RING_MUL_RINV; RING_INV; RING_OF_NUM];
    ALL_TAC] THEN
  REMOVE_THEN "coeff" (K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `poly_deg r (s:(1->num)->A) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC POLY_DEG_EQ_COEFF THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_IMP_POWERSERIES; RING_POLYNOMIAL] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    ASM_SIMP_TAC[NOT_LE];
    ASM_REWRITE_TAC[monic]]);;

(* ------------------------------------------------------------------------- *)
(* Newton-polygon rescaling over K[[t]]. Write p^(c) for p with its          *)
(* coefficients stretched by c. If the i-th coefficient of p^(sg) has order  *)
(* at least (n - i) r, then p^(sg)(t^r Y) = t^(r n) q(Y) for a polynomial q  *)
(* over K[[t]], and likewise after any further stretch. NEWTON_SLOPE finds   *)
(* such a slope r for sg = n!, attained at some i0 < n.                      *)
(* ------------------------------------------------------------------------- *)

let NEWTON_RESCALE = prove
 (`!(k:A ring) p n sg r.
        p IN ring_carrier(poly_ring (powser_ring k (:1)) (:1)) /\
        poly_deg (powser_ring k (:1)) p <= n /\
        (!i j. i <= n /\ j < (n - i) * r
               ==> coeff j (powser_stretch k sg (coeff i p)) = ring_0 k)
        ==> ?q. q IN ring_carrier(poly_ring (powser_ring k (:1)) (:1)) /\
                poly_deg (powser_ring k (:1)) q <= n /\
                (!i j. coeff j (coeff i q) =
                       coeff (j + (n - i) * r)
                             (powser_stretch k sg (coeff i p))) /\
                !e z. ~(e = 0) /\ z IN ring_carrier(powser_ring k (:1))
                      ==> poly_eval (powser_ring k (:1))
                            (powser_stretch k (sg * e) o p)
                            (ring_mul (powser_ring k (:1))
                              (ring_pow (powser_ring k (:1))
                                        (poly_var k one) (r * e)) z) =
                          ring_mul (powser_ring k (:1))
                            (ring_pow (powser_ring k (:1))
                                      (poly_var k one) (e * r * n))
                            (poly_eval (powser_ring k (:1))
                                       (powser_stretch k e o q) z)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `R = powser_ring (k:A ring) (:1)` THEN
  SUBGOAL_THEN `!d. ring_homomorphism(R,R) (powser_stretch (k:A ring) d)`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[RING_HOMOMORPHISM_POWSER_STRETCH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!d f. f IN ring_carrier R
                      ==> powser_stretch (k:A ring) d f IN ring_carrier R`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[POWSER_STRETCH_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `(!i. coeff i (p:(1->num)->(1->num)->A) IN ring_carrier R) /\
                (!i. n < i ==> coeff i p = ring_0 R)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_SIMP_TAC[RING_POLYNOMIAL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* q has coefficients t^-((n - i) r) p_i(t^sg) *)
  MP_TAC(ISPECL
   [`R:((1->num)->A)ring`;
    `\i (m:1->num).
       coeff (m one + (n - i) * r)
             (powser_stretch k sg (coeff i (p:(1->num)->(1->num)->A)))`;
    `n:num`] POLY_FROM_COEFFS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXPAND_TAC "R" THEN
    REWRITE_TAC[GSYM RING_POWERSERIES; RING_POWERSERIES_COEFF; POWSER_RING;
                GSYM FUN_EQ_COEFF; COEFF_POLY_0] THEN
    ONCE_REWRITE_TAC[COEFF] THEN REWRITE_TAC[] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC COEFF_IN_CARRIER THEN ASM_SIMP_TAC[RING_POWERSERIES];
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN
       `powser_stretch k sg (ring_0 R) = ring_0 (R:((1->num)->A)ring)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "R" THEN REWRITE_TAC[POWSER_RING; COEFF_POLY_0]]];
    ABBREV_TAC
     `q = \m m':1->num. coeff (m' one + (n - m one) * r)
              (powser_stretch k sg (coeff (m one) (p:(1->num)->(1->num)->A)))`
    THEN STRIP_TAC] THEN
  EXISTS_TAC `q:(1->num)->(1->num)->A` THEN
  MATCH_MP_TAC(TAUT `c /\ (c ==> a /\ b /\ d) ==> a /\ b /\ c /\ d`) THEN
  CONJ_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC[coeff]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`e:num`; `z:(1->num)->A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `poly_var k one IN ring_carrier R /\
    !m. powser_stretch (k:A ring) e (ring_pow R (poly_var k one) m) =
        ring_pow R (poly_var k one) (e * m)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    ASM_SIMP_TAC[POWSER_VAR_UNIV; POWSER_RING_CLAUSES; POWSER_STRETCH_VARPOW];
    ABBREV_TAC `t = poly_var (k:A ring) one`] THEN
  SUBGOAL_THEN
   `!i. i <= n
        ==> powser_stretch k sg (coeff i (p:(1->num)->(1->num)->A)) =
            ring_mul R (ring_pow R t ((n - i) * r)) (coeff i q)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["t"; "R"] THEN
    REWRITE_TAC[POWSER_RING_CLAUSES; GSYM FUN_EQ_COEFF] THEN
    X_GEN_TAC `j:num` THEN
    W(MP_TAC o PART_MATCH (lhand o rand) COEFF_POLY_VARPOW_MUL o
      rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_POWERSERIES; COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[SUB_ADD; GSYM NOT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d f. f IN ring_carrier(poly_ring R (:1)) /\ poly_deg R f <= n
          ==> !x. x IN ring_carrier R
                  ==> poly_eval R (powser_stretch k d o f) x =
                      ring_sum R (0..n)
                        (\i. ring_mul R
                               (powser_stretch (k:A ring) d (coeff i f))
                               (ring_pow R x i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_COEFF o lhand o snd) THEN
    REWRITE_TAC[COEFF_COMPOSE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[RING_POLYNOMIAL_COMPOSE; POLY_DEG_HOMOMORPHIC_IMAGE;
                  RING_POLYNOMIAL; LE_TRANS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL; RING_POW] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_POW; RING_MUL; COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `sg * e:num = e * sg` SUBST1_TAC THENL
   [ARITH_TAC; REWRITE_TAC[GSYM POWSER_STRETCH_STRETCH]] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`R:((1->num)->A)ring`; `R:((1->num)->A)ring`;
                 `powser_stretch (k:A ring) e`] RING_HOMOMORPHISM_MUL) THEN
  ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL] THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[th; RING_POW; COEFF_IN_CARRIER_ALT;
                                    RING_POLYNOMIAL]) THEN
  ASM_SIMP_TAC[RING_MUL_POW; RING_POW; RING_POW_POW; COEFF_IN_CARRIER_ALT;
               RING_POLYNOMIAL] THEN
  SUBGOAL_THEN `e * r * n = e * (n - i) * r + (r * e) * i` SUBST1_TAC THENL
   [UNDISCH_TAC `i <= n` THEN REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[ADD_SUB2] THEN ARITH_TAC;
    ASM_SIMP_TAC[RING_POW_ADD]] THEN
  REWRITE_TAC[MULT_ASSOC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
   `ring_mul (r:B ring) (ring_mul r a s) (ring_mul r b w) =
    ring_mul r (ring_mul r a b) (ring_mul r s w)`)) THEN
  ASM_SIMP_TAC[RING_POW; COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL]);;

let NEWTON_SLOPE = prove
 (`!(k:A ring) (a:num->(1->num)->A) n.
        (?i. i < n /\ ~(a i = poly_0 k))
        ==> ?r i0. i0 < n /\
                   ~(coeff ((n - i0) * r) (powser_stretch k (FACT n) (a i0)) =
                     ring_0 k) /\
                   !i j. i <= n /\ j < (n - i) * r
                         ==> coeff j (powser_stretch k (FACT n) (a i)) =
                             ring_0 k`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i1:num` STRIP_ASSUME_TAC) THEN
  (* The order v(i) of each nonzero a(i) *)
  SUBGOAL_THEN
   `!i. ?v. ~((a:num->(1->num)->A) i = poly_0 k)
            ==> ~(coeff v (a i) = ring_0 k) /\
                !j. j < v ==> coeff j (a i) = ring_0 k`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `(a:num->(1->num)->A) i = poly_0 k` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM FUN_EQ_COEFF]) THEN
    REWRITE_TAC[COEFF_POLY_0; NOT_FORALL_THM] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `v:num->num`)] THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> (n - i) * (FACT n DIV (n - i) * (v:num->num) i) = FACT n * v i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[MULT_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
    MATCH_MP_TAC DIVIDES_FACT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* Minimize v(i) n!/(n - i), a rescaled version of the slope v(i)/(n - i) *)
  MP_TAC(ISPEC `\m. ?i. i < n /\ ~((a:num->(1->num)->A) i = poly_0 k) /\
                        FACT n DIV (n - i) * v i = m` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`FACT n DIV (n - i1) * (v:num->num) i1`;
                          `i1:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i0:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:num`; `i0:num`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "r" THEN
    ASM_SIMP_TAC[COEFF_POWSER_STRETCH; DIVIDES_RMUL; DIVIDES_REFL; DIV_MULT;
                 FACT_NZ];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = n` THENL
   [UNDISCH_TAC `j < (n - i) * r` THEN
    ASM_REWRITE_TAC[SUB_REFL; MULT_CLAUSES; LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `i < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COEFF_POWSER_STRETCH] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j':num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [divides]) THEN
  SIMP_TAC[DIV_MULT; FACT_NZ] THEN
  ASM_CASES_TAC `(a:num->(1->num)->A) i = poly_0 k` THEN
  ASM_REWRITE_TAC[COEFF_POLY_0] THEN
  ASM_CASES_TAC `j' < (v:num->num) i` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `r <= FACT n DIV (n - i) * (v:num->num) i` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `FACT n DIV (n - i) * (v:num->num) i`) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n - i) * r <= FACT n * j'` MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(n - i) * (FACT n DIV (n - i) * (v:num->num) i)` THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Newton-Puiseux theorem: a monic polynomial of positive degree over    *)
(* K[[t]] acquires a root in K[[t]] after the substitution t |-> t^d.        *)
(* ------------------------------------------------------------------------- *)

let NEWTON_PUISEUX_MONIC = prove
 (`!(k:A ring) p.
        algebraically_closed_field k /\ ring_char k = 0 /\
        p IN ring_carrier(poly_ring (powser_ring k (:1)) (:1)) /\
        monic (powser_ring k (:1)) p /\ ~(poly_deg (powser_ring k (:1)) p = 0)
        ==> ?d y. 0 < d /\ y IN ring_carrier(powser_ring k (:1)) /\
                  poly_eval (powser_ring k (:1)) (powser_stretch k d o p) y =
                  ring_0 (powser_ring k (:1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  ABBREV_TAC `R = powser_ring (k:A ring) (:1)` THEN
  SUBGOAL_THEN
   `!n q. q IN ring_carrier(poly_ring R (:1)) /\ monic R q /\
          poly_deg R q = n /\ ~(n = 0)
          ==> ?d y. 0 < d /\ y IN ring_carrier R /\
                    poly_eval R (powser_stretch (k:A ring) d o q) y = ring_0 R`
  (fun th -> MP_TAC(SPECL [`poly_deg R (p:(1->num)->(1->num)->A)`;
                           `p:(1->num)->(1->num)->A`] th) THEN
             ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  X_GEN_TAC `p0:(1->num)->(1->num)->A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d. ring_homomorphism(R,R) (powser_stretch (k:A ring) d)`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[RING_HOMOMORPHISM_POWSER_STRETCH];
    ALL_TAC] THEN
  (* Tschirnhaus: reduce to s(Y) = p0(Y + c) with zero subleading term *)
  MP_TAC(SPECL [`R:((1->num)->A)ring`; `p0:(1->num)->(1->num)->A`]
   (INST_TYPE [`:(1->num)->A`,`:A`; `:(1->num)->A`,`:B`] TSCHIRNHAUS)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXPAND_TAC "R" THEN
    ASM_SIMP_TAC[RING_UNIT_POWSER_RING; RING_OF_NUM; RING_OF_NUM_POWSER_RING;
                 FIELD_UNIT] THEN
    REWRITE_TAC[poly_const; RING_OF_NUM] THEN
    ASM_SIMP_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c:(1->num)->A`; `s:(1->num)->(1->num)->A`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?d y. 0 < d /\ y IN ring_carrier R /\
          poly_eval R (powser_stretch (k:A ring) d o s) y = ring_0 R`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`d:num`; `y:(1->num)->A`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`d:num`; `ring_add R y (powser_stretch (k:A ring) d c)`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`R:((1->num)->A)ring`; `powser_stretch (k:A ring) d`;
      `y:(1->num)->A`]) THEN
    ASM_MESON_TAC[RING_ADD; RING_HOMOMORPHISM_IN_CARRIER]] THEN
  (* If s has zero constant term, 0 is a root *)
  ASM_CASES_TAC `coeff 0 (s:(1->num)->(1->num)->A) = ring_0 R` THENL
   [MAP_EVERY EXISTS_TAC [`1`; `ring_0 R:(1->num)->A`] THEN
    REWRITE_TAC[ARITH; RING_0] THEN
    SUBGOAL_THEN `powser_stretch (k:A ring) 1 o (s:(1->num)->(1->num)->A) = s`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; POWSER_STRETCH_1]; ALL_TAC] THEN
    ASM_SIMP_TAC[POLY_EVAL_AT_0];
    ALL_TAC] THEN
  (* Otherwise rescale along the Newton polygon *)
  MP_TAC(ISPECL [`k:A ring`; `\i. coeff i (s:(1->num)->(1->num)->A)`; `n:num`]
         NEWTON_SLOPE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXISTS_TAC `0` THEN
    UNDISCH_TAC `~(coeff 0 (s:(1->num)->(1->num)->A) = ring_0 R)` THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[POWSER_RING] THEN SIMP_TAC[] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `r:num`
      (X_CHOOSE_THEN `i0:num` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`k:A ring`; `s:(1->num)->(1->num)->A`; `n:num`; `FACT n`;
                 `r:num`] NEWTON_RESCALE) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->(1->num)->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `coeff n (s:(1->num)->(1->num)->A) = ring_1 R` ASSUME_TAC THENL
   [ASM_MESON_TAC[monic]; ALL_TAC] THEN
  SUBGOAL_THEN `coeff n (q:(1->num)->(1->num)->A) = ring_1 R` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FUN_EQ_COEFF] THEN
    ASM_REWRITE_TAC[SUB_REFL; MULT_CLAUSES; ADD_CLAUSES] THEN
    MP_TAC(ISPECL [`R:((1->num)->A)ring`; `R:((1->num)->A)ring`;
                   `powser_stretch (k:A ring) (FACT n)`]
                  RING_HOMOMORPHISM_1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_1 R = ring_0 (R:((1->num)->A)ring))` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_NONTRIVIAL; INTEGRAL_DOMAIN_POWSER_RING;
                 FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg R (q:(1->num)->(1->num)->A) = n /\ monic R q`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLY_DEG_EQ_FROM_LE THEN ASM_REWRITE_TAC[RING_POLYNOMIAL];
      ASM_SIMP_TAC[monic]];
    ALL_TAC] THEN
  (* The reduction of q mod t splits into two coprime factors *)
  ABBREV_TAC `qb = coeff 0 o (q:(1->num)->(1->num)->A)` THEN
  SUBGOAL_THEN
   `qb IN ring_carrier(poly_ring (k:A ring) (:1)) /\ poly_deg k qb = n`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `q:(1->num)->(1->num)->A`; `0`]
      LAYER_IN_POLY_RING) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC POLY_DEG_EQ_FROM_LE THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN EXPAND_TAC "qb" THEN
    REWRITE_TAC[COEFF_COMPOSE;
                ASSUME `coeff n (q:(1->num)->(1->num)->A) = ring_1 R`] THEN
    EXPAND_TAC "R" THEN
    ASM_SIMP_TAC[POWSER_RING; COEFF_POLY_1; FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. coeff i qb = coeff 0 (coeff i (q:(1->num)->(1->num)->A))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qb" THEN REWRITE_TAC[COEFF_COMPOSE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `qb:(1->num)->A`; `i0:num`]
         ALGEBRAICALLY_CLOSED_FIELD_COPRIME_FACTORS) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `powser_stretch (k:A ring) (FACT n) (ring_0 R) = ring_0 R`
     SUBST1_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[POWSER_RING; COEFF_POLY_0];
    DISCH_THEN(X_CHOOSE_THEN `f0:(1->num)->A` (X_CHOOSE_THEN `g0:(1->num)->A`
      STRIP_ASSUME_TAC))] THEN
  (* Lift by Hensel and apply induction to the factor of lower degree *)
  MP_TAC(ISPECL [`k:A ring`; `q:(1->num)->(1->num)->A`; `f0:(1->num)->A`;
                 `g0:(1->num)->A`] HENSEL_LIFTING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(1->num)->(1->num)->A`
   (X_CHOOSE_THEN `g:(1->num)->(1->num)->A` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "IH" (MP_TAC o SPEC `poly_deg k (f0:(1->num)->A)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `f:(1->num)->(1->num)->A`) THEN
  ASM_SIMP_TAC[LE_1; ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` (X_CHOOSE_THEN `z:(1->num)->A`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`FACT n * e`;
    `ring_mul R (ring_pow R (poly_var k one) (r * e)) (z:(1->num)->A)`] THEN
  ASM_SIMP_TAC[LT_MULT; FACT_LT; LE_1; ARITH_RULE `0 < e ==> ~(e = 0)`] THEN
  SUBGOAL_THEN `poly_var k one IN ring_carrier (R:((1->num)->A)ring)`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[POWSER_VAR_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL; RING_POW] THEN
  SUBGOAL_THEN `ring_homomorphism(R,R) (powser_stretch (k:A ring) e)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `poly_mul R f g = (q:(1->num)->(1->num)->A)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`R:((1->num)->A)ring`; `R:((1->num)->A)ring`;
                 `powser_stretch (k:A ring) e`; `f:(1->num)->(1->num)->A`;
                 `g:(1->num)->(1->num)->A`] POLY_COMPOSE_HOMOMORPHISM_MUL) THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL_IMP_POWERSERIES; RING_POLYNOMIAL] THEN
  DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_MUL o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[RING_POLYNOMIAL_COMPOSE; RING_POLYNOMIAL];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO; POLY_EVAL; RING_POW]);;

(* ------------------------------------------------------------------------- *)
(* The domain K[[t^(1/oo)]] of Puiseux power series, as the direct limit of  *)
(* K[[t]] --stretch--> K[[t]]. A sequence x with x(d) in K[[t]] stands for   *)
(* the series x(d)(t^(1/d)); it is coherent if from some level d on the      *)
(* entries agree, i.e. x(c e) = x(e)(t^c) whenever d divides e. Coherent     *)
(* sequences are taken modulo those that eventually vanish.                  *)
(* ------------------------------------------------------------------------- *)

let puiseux_coherent = new_definition
 `puiseux_coherent (k:A ring) =
    {x:num->(1->num)->A |
       (!n. x n IN ring_carrier(powser_ring k (:1))) /\
       ?d. 0 < d /\
           !e c. 0 < e /\ 0 < c /\ d divides e
                 ==> x(c * e) = powser_stretch k c (x e)}`;;

let puiseux_null = new_definition
 `puiseux_null (k:A ring) =
    {x:num->(1->num)->A |
       (!n. x n IN ring_carrier(powser_ring k (:1))) /\
       ?d. 0 < d /\
           !e. 0 < e /\ d divides e ==> x e = ring_0(powser_ring k (:1))}`;;

let puiseux_powser = new_definition
 `puiseux_powser (k:A ring) =
    quotient_ring
     (subring_generated (product_ring (:num) (\n. powser_ring k (:1)))
                        (puiseux_coherent k))
     (puiseux_null k)`;;

let puiseux_ring = new_definition
 `puiseux_ring (k:A ring) = fraction_ring (puiseux_powser k)`;;

let IN_PUISEUX_COHERENT = prove
 (`!(k:A ring) x.
        x IN puiseux_coherent k <=>
        (!n. x n IN ring_carrier(powser_ring k (:1))) /\
        ?d. 0 < d /\
            !e c. 0 < e /\ 0 < c /\ d divides e
                  ==> x(c * e) = powser_stretch k c (x e)`,
  REWRITE_TAC[puiseux_coherent; IN_ELIM_THM]);;

let IN_PUISEUX_NULL = prove
 (`!(k:A ring) x.
        x IN puiseux_null k <=>
        (!n. x n IN ring_carrier(powser_ring k (:1))) /\
        ?d. 0 < d /\
            !e. 0 < e /\ d divides e ==> x e = ring_0(powser_ring k (:1))`,
  REWRITE_TAC[puiseux_null; IN_ELIM_THM]);;

let PUISEUX_COHERENT_SUBRING = prove
 (`!k:A ring. puiseux_coherent k subring_of
                product_ring (:num) (\n. powser_ring k (:1))`,
  let COHERENT_BINOP_TAC homth =
    MAP_EVERY X_GEN_TAC [`x:num->(1->num)->A`; `y:num->(1->num)->A`] THEN
    DISCH_THEN(DESTRUCT_TAC "(cx @d1. d1 hx) (cy @d2. d2 hy)") THEN
    EXISTS_TAC `d1 * d2:num` THEN ASM_SIMP_TAC[LT_MULT] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(d1:num) divides e /\ d2 divides e` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[DIVIDES_LMUL2; DIVIDES_RMUL2]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`powser_ring (k:A ring) (:1)`;
                   `powser_ring (k:A ring) (:1)`;
                   `powser_stretch (k:A ring) c`] homth) THEN
    ASM_SIMP_TAC[] in
  GEN_TAC THEN
  REWRITE_TAC[subring_of; puiseux_coherent; PRODUCT_RING; SUBSET; IN_ELIM_THM;
              IN_CARTESIAN_PRODUCT; EXTENSIONAL_UNIV; IN_UNIV;
              RESTRICTION_UNIV] THEN
  SIMP_TAC[RING_0; RING_1; RING_NEG; RING_ADD; RING_MUL] THEN
  ASSUME_TAC(ISPEC `k:A ring` RING_HOMOMORPHISM_POWSER_STRETCH) THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `1` THEN REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `1` THEN REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_HOMOMORPHISM_1 THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:num->(1->num)->A` THEN STRIP_TAC THEN EXISTS_TAC `d:num` THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`powser_ring (k:A ring) (:1)`;
                   `powser_ring (k:A ring) (:1)`;
                   `powser_stretch (k:A ring) c`] RING_HOMOMORPHISM_NEG) THEN
    ASM_SIMP_TAC[];
    COHERENT_BINOP_TAC RING_HOMOMORPHISM_ADD;
    COHERENT_BINOP_TAC RING_HOMOMORPHISM_MUL]);;

let PUISEUX_NULL_IDEAL = prove
 (`!k:A ring.
        ring_ideal
         (subring_generated (product_ring (:num) (\n. powser_ring k (:1)))
                            (puiseux_coherent k))
         (puiseux_null k)`,
  GEN_TAC THEN
  SIMP_TAC[ring_ideal; CARRIER_SUBRING_GENERATED_SUBRING;
           PUISEUX_COHERENT_SUBRING] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
  REWRITE_TAC[puiseux_null; puiseux_coherent; PRODUCT_RING; SUBSET;
              IN_ELIM_THM; RESTRICTION_UNIV] THEN
  SIMP_TAC[RING_0; RING_NEG; RING_ADD; RING_MUL] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:num->(1->num)->A` THEN STRIP_TAC THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[DIVIDES_LMUL; LT_MULT] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN
    REWRITE_TAC[RING_HOMOMORPHISM_POWSER_STRETCH];
    EXISTS_TAC `1` THEN REWRITE_TAC[ARITH];
    X_GEN_TAC `x:num->(1->num)->A` THEN STRIP_TAC THEN EXISTS_TAC `d:num` THEN
    ASM_SIMP_TAC[RING_NEG_0];
    MAP_EVERY X_GEN_TAC [`x:num->(1->num)->A`; `y:num->(1->num)->A`] THEN
    DISCH_THEN(DESTRUCT_TAC "(cx @d1. d1 hx) (cy @d2. d2 hy)") THEN
    EXISTS_TAC `d1 * d2:num` THEN ASM_SIMP_TAC[LT_MULT] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(d1:num) divides e /\ d2 divides e` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[DIVIDES_LMUL2; DIVIDES_RMUL2]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_ADD_LZERO; RING_0];
    MAP_EVERY X_GEN_TAC [`x:num->(1->num)->A`; `y:num->(1->num)->A`] THEN
    DISCH_THEN(DESTRUCT_TAC "(cx _) (cy @d2. d2 hy)") THEN
    EXISTS_TAC `d2:num` THEN ASM_SIMP_TAC[RING_MUL_RZERO]]);;

let INTEGRAL_DOMAIN_PUISEUX_POWSER = prove
 (`!k:A ring. integral_domain k ==> integral_domain(puiseux_powser k)`,
  GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[puiseux_powser; INTEGRAL_DOMAIN_QUOTIENT_RING;
           PUISEUX_NULL_IDEAL] THEN
  ASM_SIMP_TAC[prime_ideal; proper_ideal; PUISEUX_NULL_IDEAL; PSUBSET;
               RING_IDEAL_IMP_SUBSET] THEN
  SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; PUISEUX_COHERENT_SUBRING] THEN
  REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
  SUBGOAL_THEN `integral_domain (powser_ring (k:A ring) (:1))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INTEGRAL_DOMAIN_POWSER_RING]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_FORALL_THM] THEN
    EXISTS_TAC `\n:num. ring_1(powser_ring (k:A ring) (:1))` THEN
    REWRITE_TAC[puiseux_null; puiseux_coherent; IN_ELIM_THM; RING_1] THEN
    MATCH_MP_TAC(TAUT `~p /\ q ==> ~(p <=> q)`) THEN CONJ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:num`) THEN
      ASM_REWRITE_TAC[DIVIDES_REFL] THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_NONTRIVIAL];
      EXISTS_TAC `1` THEN REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_HOMOMORPHISM_1 THEN
      REWRITE_TAC[RING_HOMOMORPHISM_POWSER_STRETCH]];
    ALL_TAC] THEN
  REWRITE_TAC[puiseux_null; puiseux_coherent; IN_ELIM_THM; PRODUCT_RING;
              RESTRICTION_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`x:num->(1->num)->A`; `y:num->(1->num)->A`] THEN
  DISCH_THEN(DESTRUCT_TAC "(cx @d1. d1 hx) (cy _) (_ @d3. d3 hxy)") THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `(~p ==> q) ==> p \/ q`) THEN
  DISCH_THEN(LABEL_TAC "nx") THEN
  EXISTS_TAC `d1 * d3:num` THEN ASM_SIMP_TAC[LT_MULT] THEN
  X_GEN_TAC `e:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d1:num) divides e /\ d3 divides e` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_LMUL2; DIVIDES_RMUL2]; ALL_TAC] THEN
  SUBGOAL_THEN `~((x:num->(1->num)->A) e = ring_0(powser_ring k (:1)))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN REMOVE_THEN "nx" MP_TAC THEN
    REWRITE_TAC[] THEN EXISTS_TAC `e:num` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e':num` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `c:num` SUBST_ALL_TAC)) THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN
    SUBGOAL_THEN `0 < c` ASSUME_TAC THENL
     [UNDISCH_TAC `0 < e * c` THEN SIMP_TAC[LT_MULT]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN
    REWRITE_TAC[RING_HOMOMORPHISM_POWSER_STRETCH];
    ALL_TAC] THEN
  REMOVE_THEN "hxy" (MP_TAC o SPEC `e:num`) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* The embedding of K[[t^(1/d)]] in K[[t^(1/oo)]]: a series y(t) is sent to  *)
(* the sequence whose entry at level m is y(t^(m DIV d)), coherent from      *)
(* level d on. These embeddings are injective ring homomorphisms compatible  *)
(* with stretching, and any finitely many elements of K[[t^(1/oo)]] lie in   *)
(* the image of a single one.                                                *)
(* ------------------------------------------------------------------------- *)

let PUISEUX_COHERENT_LEVEL = prove
 (`!(k:A ring) d y.
        0 < d /\ y IN ring_carrier(powser_ring k (:1))
        ==> (\m. powser_stretch k (m DIV d) y) IN puiseux_coherent k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_PUISEUX_COHERENT] THEN
  ASM_SIMP_TAC[POWSER_STRETCH_IN_CARRIER; POWSER_STRETCH_STRETCH] THEN
  EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`e:num`; `c:num`] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num` SUBST1_TAC o
    REWRITE_RULE[divides] o last o CONJUNCTS) THEN
  SUBGOAL_THEN `c * d * f = d * (c * f)` SUBST1_TAC THENL
   [ARITH_TAC; ASM_SIMP_TAC[DIV_MULT; LE_1]]);;

let RING_HOMOMORPHISM_PUISEUX_PROJECTION = prove
 (`!(k:A ring) e.
        ring_homomorphism
         (subring_generated (product_ring (:num) (\n. powser_ring k (:1)))
                            (puiseux_coherent k),
          powser_ring k (:1))
         (\x. x e)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_FROM_SUBRING_GENERATED THEN
  MP_TAC(ISPECL [`\n:num. powser_ring (k:A ring) (:1)`; `(:num)`; `e:num`]
    RING_HOMOMORPHISM_PRODUCT_PROJECTION) THEN
  REWRITE_TAC[IN_UNIV]);;

let PUISEUX_COSET_EQ = prove
 (`!(k:A ring) x y.
        x IN puiseux_coherent k /\ y IN puiseux_coherent k
        ==> (ring_coset
              (subring_generated (product_ring (:num) (\n. powser_ring k (:1)))
                                 (puiseux_coherent k))
              (puiseux_null k) x =
             ring_coset
              (subring_generated (product_ring (:num) (\n. powser_ring k (:1)))
                                 (puiseux_coherent k))
              (puiseux_null k) y <=>
             ?d. 0 < d /\ !e. 0 < e /\ d divides e ==> x e = y e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_HOMOMORPHISM_PUISEUX_PROJECTION) THEN
  MP_TAC(ISPEC `k:A ring` PUISEUX_NULL_IDEAL) THEN
  MP_TAC(ISPEC `k:A ring` PUISEUX_COHERENT_SUBRING) THEN
  ABBREV_TAC
   `S = subring_generated (product_ring (:num) (\n. powser_ring k (:1)))
                          (puiseux_coherent (k:A ring))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `ring_carrier S = puiseux_coherent (k:A ring)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_COSET_EQ o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_PUISEUX_NULL] THEN
  SUBGOAL_THEN
   `!e. ring_sub S x y e =
        ring_sub (powser_ring k (:1)) ((x:num->(1->num)->A) e) (y e)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_SUB o
      SPEC `e:num` o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_PUISEUX_COHERENT]) THEN
  ASM_SIMP_TAC[RING_SUB; RING_SUB_EQ_0]);;

let puiseux_embed = new_definition
 `puiseux_embed (k:A ring) d (y:(1->num)->A) =
    ring_coset
     (subring_generated (product_ring (:num) (\n. powser_ring k (:1)))
                        (puiseux_coherent k))
     (puiseux_null k) (\m. powser_stretch k (m DIV d) y)`;;

let RING_HOMOMORPHISM_PUISEUX_EMBED = prove
 (`!(k:A ring) d.
        0 < d
        ==> ring_homomorphism (powser_ring k (:1),puiseux_powser k)
                              (puiseux_embed k d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `puiseux_embed (k:A ring) d =
    ring_coset
     (subring_generated (product_ring (:num) (\n. powser_ring k (:1)))
                        (puiseux_coherent k))
     (puiseux_null k) o (\y m. powser_stretch k (m DIV d) y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; puiseux_embed]; ALL_TAC] THEN
  REWRITE_TAC[puiseux_powser] THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
  EXISTS_TAC
   `subring_generated (product_ring (:num) (\n. powser_ring k (:1)))
                      (puiseux_coherent (k:A ring))` THEN
  SIMP_TAC[RING_HOMOMORPHISM_RING_COSET; PUISEUX_NULL_IDEAL] THEN
  SIMP_TAC[RING_HOMOMORPHISM_INTO_SUBRING_EQ; PUISEUX_COHERENT_SUBRING] THEN
  REWRITE_TAC[RING_HOMOMORPHISM_COMPONENTWISE_UNIV; ETA_AX;
              RING_HOMOMORPHISM_POWSER_STRETCH] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[PUISEUX_COHERENT_LEVEL]);;

let RING_MONOMORPHISM_PUISEUX_EMBED = prove
 (`!(k:A ring) d.
        0 < d
        ==> ring_monomorphism (powser_ring k (:1),puiseux_powser k)
                              (puiseux_embed k d)`,
  SIMP_TAC[ring_monomorphism; RING_HOMOMORPHISM_PUISEUX_EMBED] THEN
  MAP_EVERY X_GEN_TAC [`k:A ring`; `d:num`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:(1->num)->A`; `y:(1->num)->A`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[puiseux_embed; PUISEUX_COSET_EQ; PUISEUX_COHERENT_LEVEL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d * e:num`) THEN
  ASM_SIMP_TAC[LT_MULT; DIVIDES_LMUL; DIVIDES_REFL; DIV_MULT; LE_1] THEN
  MP_TAC(ISPECL [`k:A ring`; `e:num`] RING_MONOMORPHISM_POWSER_STRETCH) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ring_monomorphism]] THEN
  ASM_MESON_TAC[]);;

let PUISEUX_EMBED_STRETCH = prove
 (`!(k:A ring) c d y.
        0 < c /\ 0 < d /\ y IN ring_carrier(powser_ring k (:1))
        ==> puiseux_embed k (c * d) (powser_stretch k c y) =
            puiseux_embed k d y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[puiseux_embed] THEN
  ASM_SIMP_TAC[PUISEUX_COSET_EQ; PUISEUX_COHERENT_LEVEL; LT_MULT;
               POWSER_STRETCH_IN_CARRIER] THEN
  EXISTS_TAC `c * d:num` THEN ASM_SIMP_TAC[LT_MULT] THEN
  X_GEN_TAC `e:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num` SUBST1_TAC o
    REWRITE_RULE[divides] o CONJUNCT2) THEN
  REWRITE_TAC[POWSER_STRETCH_STRETCH] THEN
  SUBGOAL_THEN `(c * d) * f = d * (c * f)` (fun th ->
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [th])
  THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT; LE_1; MULT_EQ_0] THEN REWRITE_TAC[MULT_SYM]);;

let PUISEUX_EMBED_VAR_POW = prove
 (`!(k:A ring) d.
        0 < d
        ==> ring_pow (puiseux_powser k)
                     (puiseux_embed k d (poly_var k one)) d =
            puiseux_embed k 1 (poly_var k one)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `d:num`; `1`; `poly_var (k:A ring) one`]
                PUISEUX_EMBED_STRETCH) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ARITH; POWSER_VAR_UNIV] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[POWSER_STRETCH_VAR; LE_1] THEN
  MP_TAC(ISPECL [`powser_ring (k:A ring) (:1)`; `puiseux_powser (k:A ring)`;
                 `puiseux_embed (k:A ring) d`] RING_HOMOMORPHISM_POW) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_PUISEUX_EMBED] THEN
  DISCH_THEN(MP_TAC o SPECL [`poly_var (k:A ring) one`; `d:num`]) THEN
  REWRITE_TAC[POWSER_VAR_UNIV; POWSER_RING_CLAUSES] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let PUISEUX_EMBED_EXISTS = prove
 (`!(k:A ring) x.
        x IN ring_carrier(puiseux_powser k)
        ==> ?d y. 0 < d /\ y IN ring_carrier(powser_ring k (:1)) /\
                  puiseux_embed k d y = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[puiseux_powser] THEN
  SIMP_TAC[QUOTIENT_RING_CARRIER; PUISEUX_NULL_IDEAL] THEN
  SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; PUISEUX_COHERENT_SUBRING] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:num->(1->num)->A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_PUISEUX_COHERENT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`d:num`; `(z:num->(1->num)->A) d`] THEN
  ASM_SIMP_TAC[puiseux_embed; PUISEUX_COSET_EQ; PUISEUX_COHERENT_LEVEL] THEN
  EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `e DIV d * d = e` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_DIV_MULT]; ALL_TAC] THEN
  SUBGOAL_THEN `0 < e DIV d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_1; DIV_EQ_0; NOT_LT; DIVIDES_LE_IMP]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`d:num`; `e DIV d`] o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[DIVIDES_REFL] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let PUISEUX_EMBED_COMMON = prove
 (`!(k:A ring) n x.
        (!i. i <= n ==> x i IN ring_carrier(puiseux_powser k))
        ==> ?d y. 0 < d /\
                  !i. i <= n ==> y i IN ring_carrier(powser_ring k (:1)) /\
                                 puiseux_embed k d (y i) = x i`,
  GEN_TAC THEN INDUCT_TAC THEN
  X_GEN_TAC `x:num->(num->(1->num)->A)->bool` THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `(x:num->(num->(1->num)->A)->bool) 0`]
                  PUISEUX_EMBED_EXISTS) THEN
    ASM_SIMP_TAC[LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `y:(1->num)->A`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`d:num`; `\i:num. (y:(1->num)->A)`] THEN
    ASM_SIMP_TAC[LE];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num->(num->(1->num)->A)->bool`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LE]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:num` (X_CHOOSE_THEN `y:num->(1->num)->A`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`k:A ring`; `(x:num->(num->(1->num)->A)->bool) (SUC n)`]
                  PUISEUX_EMBED_EXISTS) THEN
    ASM_SIMP_TAC[LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:num` (X_CHOOSE_THEN `z:(1->num)->A`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`d2 * d1:num`;
      `\i. if i <= n then powser_stretch k d2 ((y:num->(1->num)->A) i)
           else powser_stretch k d1 z`] THEN
    ASM_SIMP_TAC[LT_MULT] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[LE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC n <= n <=> F`; POWSER_STRETCH_IN_CARRIER;
                 PUISEUX_EMBED_STRETCH] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[PUISEUX_EMBED_STRETCH]]);;

(* ------------------------------------------------------------------------- *)
(* Every monic polynomial of positive degree over K[[t^(1/oo)]] has a root:  *)
(* its coefficients come from a common K[[t^(1/D)]], and Newton-Puiseux      *)
(* gives a root there after a further stretch.                               *)
(* ------------------------------------------------------------------------- *)

let PUISEUX_POWSER_MONIC_ROOT = prove
 (`!(k:A ring) p.
        algebraically_closed_field k /\ ring_char k = 0 /\
        p IN ring_carrier(poly_ring (puiseux_powser k) (:1)) /\
        monic (puiseux_powser k) p /\ ~(poly_deg (puiseux_powser k) p = 0)
        ==> ?x. x IN ring_carrier(puiseux_powser k) /\
                poly_eval (puiseux_powser k) p x = ring_0(puiseux_powser k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[monic] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPEC `k:A ring` NEWTON_PUISEUX_MONIC) THEN
  MP_TAC(ISPEC `k:A ring` PUISEUX_EMBED_STRETCH) THEN
  MP_TAC(ISPEC `k:A ring` RING_MONOMORPHISM_PUISEUX_EMBED) THEN
  MP_TAC(ISPEC `k:A ring` RING_HOMOMORPHISM_POWSER_STRETCH) THEN
  (* The coefficients of p come from K[[t]] at a common level D *)
  MP_TAC(ISPECL
   [`k:A ring`;
    `poly_deg (puiseux_powser k) (p:(1->num)->(num->(1->num)->A)->bool)`;
    `\i. coeff i (p:(1->num)->(num->(1->num)->A)->bool)`]
   PUISEUX_EMBED_COMMON) THEN
  ABBREV_TAC `R = powser_ring (k:A ring) (:1)` THEN
  ABBREV_TAC `P = puiseux_powser (k:A ring)` THEN
  ABBREV_TAC `n = poly_deg P (p:(1->num)->(num->(1->num)->A)->bool)` THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:num` (X_CHOOSE_THEN `y:num->(1->num)->A`
    STRIP_ASSUME_TAC)) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `ring_monomorphism (R,P) (puiseux_embed (k:A ring) D)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `(y:num->(1->num)->A) n = ring_1 R` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o
      GEN_REWRITE_RULE I [ring_monomorphism]) THEN
    ASM_SIMP_TAC[RING_1; LE_REFL] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]);
    ALL_TAC] THEN
  (* so they form a monic polynomial q over K[[t]] of the same degree *)
  ABBREV_TAC `q = \m:1->num. if m one <= n then (y:num->(1->num)->A) (m one)
                             else ring_0 R` THEN
  SUBGOAL_THEN
   `!i. coeff i (q:(1->num)->(1->num)->A) = if i <= n then y i else ring_0 R`
  ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC[coeff]; ALL_TAC] THEN
  MP_TAC(ISPECL [`R:((1->num)->A)ring`;
                 `\i. if i <= n then (y:num->(1->num)->A) i else ring_0 R`;
                 `n:num`] POLY_FROM_COEFFS) THEN
  ASM_SIMP_TAC[LE_REFL; ARITH_RULE `n < i ==> ~(i <= n)`] THEN ANTS_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[RING_0];
    EXPAND_TAC "R" THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_NONTRIVIAL; INTEGRAL_DOMAIN_POWSER_RING;
                 FIELD_IMP_INTEGRAL_DOMAIN] THEN
    STRIP_TAC] THEN
  (* By Newton-Puiseux q has a root z after the stretch by some e *)
  FIRST_X_ASSUM(MP_TAC o SPEC `q:(1->num)->(1->num)->A`) THEN
  ASM_REWRITE_TAC[monic; LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num` (X_CHOOSE_THEN `z:(1->num)->A`
    STRIP_ASSUME_TAC)) THEN
  (* and p is the image of that stretched q at level e D *)
  SUBGOAL_THEN `ring_homomorphism (R,P) (puiseux_embed (k:A ring) (e * D))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_MONOMORPHISM_IMP_HOMOMORPHISM THEN
    ASM_SIMP_TAC[LT_MULT];
    ALL_TAC] THEN
  SUBGOAL_THEN `powser_stretch (k:A ring) e (ring_0 R) = ring_0 R /\
                puiseux_embed k (e * D) (ring_0 R) = ring_0 P`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_0]; ALL_TAC] THEN
  EXISTS_TAC `puiseux_embed (k:A ring) (e * D) z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
    EXISTS_TAC `R:((1->num)->A)ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:(1->num)->(num->(1->num)->A)->bool) =
    puiseux_embed (k:A ring) (e * D) o
    (powser_stretch k e o (q:(1->num)->(1->num)->A))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM FUN_EQ_COEFF; COEFF_COMPOSE] THEN X_GEN_TAC `i:num` THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC COEFF_ABOVE_DEG THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `powser_stretch (k:A ring) e o q IN ring_carrier(poly_ring R (:1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `R:((1->num)->A)ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:((1->num)->A)ring`; `P:((num->(1->num)->A)->bool)ring`;
                 `z:(1->num)->A`; `puiseux_embed (k:A ring) (e * D)`;
                 `powser_stretch (k:A ring) e o (q:(1->num)->(1->num)->A)`]
                POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* If every monic polynomial of positive degree over an integral domain has  *)
(* a root in it, then its field of fractions is algebraically closed.        *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAICALLY_CLOSED_FRACTION_RING = prove
 (`!r:A ring.
        integral_domain r /\
        (!p. p IN ring_carrier(poly_ring r (:1)) /\ monic r p /\
             ~(poly_deg r p = 0)
             ==> ?x. x IN ring_carrier r /\ poly_eval r p x = ring_0 r)
        ==> algebraically_closed_field(fraction_ring r)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "roots")) THEN
  ABBREV_TAC `L = fraction_ring (r:A ring)` THEN
  ABBREV_TAC `h = ring_fractionate (r:A ring) {a | ring_regular r a}` THEN
  SUBGOAL_THEN `field (L:(A#A->bool)ring) /\
                ring_monomorphism (r,L) (h:A->A#A->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "h"] THEN
    ASM_REWRITE_TAC[FRACTION_FIELD; RING_MONOMORPHISM_FRACTIONATE];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(fun th -> MAP_EVERY (ASSUME_TAC o C MATCH_MP th)
   [RING_HOMOMORPHISM_0; RING_HOMOMORPHISM_1; RING_HOMOMORPHISM_MUL;
    RING_HOMOMORPHISM_POW]) THEN
  SUBGOAL_THEN
   `!z. z IN ring_carrier r ==> (h:A->A#A->bool) z IN ring_carrier L`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[algebraically_closed_field] THEN
  X_GEN_TAC `p:(1->num)->A#A->bool` THEN STRIP_TAC THEN
  (* Clear denominators: c p = h o g with g of degree k + 1 over r *)
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A#A->bool`]
         POLY_CLEAR_DENOMINATORS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DESTRUCT_TAC "@c g. c cnz g clear") THEN
  SUBGOAL_THEN
   `poly_deg r (g:(1->num)->A) = poly_deg L (p:(1->num)->A#A->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `L:(A#A->bool)ring`; `h:A->A#A->bool`;
                   `g:(1->num)->A`] POLY_DEG_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "clear" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[POLY_RING] THEN MATCH_MP_TAC POLY_DEG_CMUL THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_POLYNOMIAL;
                 RING_MONOMORPHISM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. poly_deg r (g:(1->num)->A) = SUC k /\
                    poly_deg L (p:(1->num)->A#A->bool) = SUC k`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[num_CASES]; ALL_TAC] THEN
  ABBREV_TAC `a = coeff (SUC k) (g:(1->num)->A)` THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier r /\ ~(a = ring_0 r)` STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "a" THEN
    ASM_SIMP_TAC[COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL] THEN
    MP_TAC(ISPECL [`r:A ring`; `g:(1->num)->A`] POLY_TOP_NONZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `poly_deg (r:A ring):((1->num)->A)->num`) THEN
    ASM_REWRITE_TAC[POLY_RING; POLY_DEG_0; NOT_SUC];
    ALL_TAC] THEN
  (* The monic polynomial m(X) = a^k g(X/a) over r *)
  ABBREV_TAC
   `m = \i:1->num. if i one = SUC k then ring_1 r
                  else ring_mul r (coeff (i one) (g:(1->num)->A))
                                  (ring_pow r a (k - i one))` THEN
  SUBGOAL_THEN
   `!j. coeff j (m:(1->num)->A) =
        if j = SUC k then ring_1 r
        else ring_mul r (coeff j (g:(1->num)->A)) (ring_pow r a (k - j))`
  ASSUME_TAC THENL [EXPAND_TAC "m" THEN REWRITE_TAC[coeff]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`r:A ring`;
    `\j. if j = SUC k then ring_1 r
         else ring_mul r (coeff j (g:(1->num)->A)) (ring_pow r a (k - j))`;
    `SUC k`] POLY_FROM_COEFFS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN GEN_TAC THENL
     [COND_CASES_TAC THEN
      ASM_SIMP_TAC[RING_1; RING_MUL; RING_POW; COEFF_IN_CARRIER_ALT;
                   RING_POLYNOMIAL];
      DISCH_TAC THEN ASM_SIMP_TAC[ARITH_RULE `SUC k < i ==> ~(i = SUC k)`] THEN
      SUBGOAL_THEN `coeff i (g:(1->num)->A) = ring_0 r` SUBST1_TAC THENL
       [MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC[RING_POLYNOMIAL];
        ASM_SIMP_TAC[RING_MUL_LZERO; RING_POW]]];
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_NONTRIVIAL] THEN STRIP_TAC] THEN
  REMOVE_THEN "roots" (MP_TAC o SPEC `m:(1->num)->A`) THEN
  ASM_REWRITE_TAC[monic; NOT_SUC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  (* The root of p is y = h(x) / h(a) *)
  ABBREV_TAC `u = (h:A->A#A->bool) a` THEN
  SUBGOAL_THEN `(u:A#A->bool) IN ring_carrier L /\ ~(u = ring_0 L) /\
                ring_unit L u`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[FIELD_UNIT; RING_MONOMORPHISM_EQ_0];
    ALL_TAC] THEN
  ABBREV_TAC `y = ring_mul L (ring_inv L u) ((h:A->A#A->bool) x)` THEN
  SUBGOAL_THEN `(y:A#A->bool) IN ring_carrier L /\
                (h:A->A#A->bool) x = ring_mul L u y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV; RING_MUL_ASSOC; RING_MUL_RINV;
                 RING_MUL_LID];
    ALL_TAC] THEN
  EXISTS_TAC `y:A#A->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `poly_eval L ((h:A->A#A->bool) o g) y = ring_0 L` MP_TAC THENL
   [ALL_TAC;
    REMOVE_THEN "clear" (SUBST1_TAC o SYM) THEN REWRITE_TAC[POLY_RING] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_MUL o
      lhand o lhand o snd) THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_CONST; RING_POLYNOMIAL; POLY_EVAL_CONST] THEN
    DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN;
                 POLY_EVAL; RING_MONOMORPHISM_EQ_0]] THEN
  (* Since u^k g(y) = m(u y) = m(x) termwise *)
  SUBGOAL_THEN
   `!q z. q IN ring_carrier(poly_ring r (:1)) /\ poly_deg r q <= SUC k /\
          z IN ring_carrier L
          ==> poly_eval L ((h:A->A#A->bool) o q) z =
              ring_sum L (0..SUC k)
                (\i. ring_mul L (coeff i (h o q)) (ring_pow L z i))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_EVAL_COEFF THEN
    ASM_MESON_TAC[RING_POLYNOMIAL_COMPOSE; POLY_DEG_HOMOMORPHIC_IMAGE;
                  RING_POLYNOMIAL; LE_TRANS];
    REWRITE_TAC[COEFF_COMPOSE] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `ring_mul L (ring_pow L u k) (poly_eval L ((h:A->A#A->bool) o g) y) =
    poly_eval L (h o m) (ring_mul L u y)`
  MP_TAC THENL
   [ASM_SIMP_TAC[LE_REFL; RING_MUL] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_POW; RING_MUL; COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[ring_pow; RING_MUL_POW];
      SUBGOAL_THEN
       `ring_pow L u k =
        ring_mul L (ring_pow L u (k - i)) (ring_pow L (u:A#A->bool) i)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM RING_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        ASM_SIMP_TAC[RING_POW; COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL;
                     RING_MUL_POW]]] THEN
    W(fun (_,w) -> MATCH_MP_TAC(RING_RULE w)) THEN
    ASM_SIMP_TAC[RING_POW; COEFF_IN_CARRIER_ALT; RING_POLYNOMIAL];
    MP_TAC(ISPECL [`r:A ring`; `L:(A#A->bool)ring`; `x:A`; `h:A->A#A->bool`;
                   `m:(1->num)->A`] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN; RING_POW;
                 POLY_EVAL; FIELD_POW_EQ_0]]);;

(* ------------------------------------------------------------------------- *)
(* Puiseux's theorem.                                                        *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAICALLY_CLOSED_PUISEUX_RING = prove
 (`!k:A ring.
        algebraically_closed_field k /\ ring_char k = 0
        ==> algebraically_closed_field(puiseux_ring k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[puiseux_ring] THEN
  MATCH_MP_TAC ALGEBRAICALLY_CLOSED_FRACTION_RING THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_PUISEUX_POWSER; FIELD_IMP_INTEGRAL_DOMAIN;
               ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD;
               PUISEUX_POWSER_MONIC_ROOT]);;

(* ------------------------------------------------------------------------- *)
(* A sanity check on the construction: K[[t]] embeds in the Puiseux field,   *)
(* where t has a d-th root for every d > 0.                                  *)
(* ------------------------------------------------------------------------- *)

let PUISEUX_RING_ROOTS_OF_T = prove
 (`!k:A ring.
        ?h. ring_monomorphism (powser_ring k (:1),puiseux_ring k) h /\
            !d. 0 < d
                ==> ?x. x IN ring_carrier(puiseux_ring k) /\
                        ring_pow (puiseux_ring k) x d = h(poly_var k one)`,
  GEN_TAC THEN REWRITE_TAC[puiseux_ring] THEN
  MP_TAC(ISPEC `puiseux_powser (k:A ring)` RING_MONOMORPHISM_FRACTIONATE) THEN
  MP_TAC(ISPEC `k:A ring` PUISEUX_EMBED_VAR_POW) THEN
  MP_TAC(ISPEC `k:A ring` RING_MONOMORPHISM_PUISEUX_EMBED) THEN
  ABBREV_TAC `P = puiseux_powser (k:A ring)` THEN
  ABBREV_TAC
   `f = ring_fractionate (P:((num->(1->num)->A)->bool)ring)
                         {a | ring_regular P a}` THEN
  REPEAT DISCH_TAC THEN
  EXISTS_TAC
   `(f:((num->(1->num)->A)->bool)->
       ((num->(1->num)->A)->bool)#((num->(1->num)->A)->bool)->bool) o
    puiseux_embed (k:A ring) 1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN
    EXISTS_TAC `P:((num->(1->num)->A)->bool)ring` THEN
    ASM_SIMP_TAC[ARITH];
    X_GEN_TAC `d:num` THEN DISCH_TAC THEN
    EXISTS_TAC
     `(f:((num->(1->num)->A)->bool)->
         ((num->(1->num)->A)->bool)#((num->(1->num)->A)->bool)->bool)
      (puiseux_embed k d (poly_var k one))` THEN
    SUBGOAL_THEN
     `puiseux_embed (k:A ring) d (poly_var k one) IN ring_carrier P`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC `powser_ring (k:A ring) (:1)` THEN
      ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM; POWSER_VAR_UNIV];
      ALL_TAC] THEN
    FIRST_X_ASSUM(ASSUME_TAC o
      MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
      EXISTS_TAC `P:((num->(1->num)->A)->bool)ring` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW th)]) THEN
      ASM_SIMP_TAC[o_THM]]]);;
