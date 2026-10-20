(* ========================================================================= *)
(* 4CT/general.ml                                                            *)
(*                                                                           *)
(* General lemmas used throughout the development, about arithmetic,         *)
(* iteration, permutations and transpositions, periods of orbits, finite     *)
(* sets and lists; their statements and proofs involve only HOL Light and    *)
(* its libraries.  Several are small variants of library theorems (noted     *)
(* in the proofs) kept under their own names for their many uses.            *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/permutations.ml";;
needs "Library/isum.ml";;

parse_as_infix("::",(23,"right"));;
override_interface("::",`CONS`);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic, divisibility and boolean indicators.                          *)
(* ------------------------------------------------------------------------- *)

let IF_F = prove
 (`!c a. (if c then a else F) <=> c /\ a`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[]);;

let IN_NOTIN_NEQ =
  prove(`!(x:A) y s. x IN s /\ ~(y IN s) ==> ~(x = y)`, MESON_TAC[]);;

let SUM_DISTINCT_SYM = prove
 (`!(a:B) (b:A). ~(INR a = INL b)`, MESON_TAC[distinctness "sum"]);;

let NOT_DIVIDES_LT = prove
 (`!d k. 0 < k /\ k < d ==> ~(d divides k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `k:num`] DIVIDES_LE) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TWO_DIV_TWO =
 prove(`2 divides 2`, REWRITE_TAC[divides] THEN EXISTS_TAC `1` THEN
 ARITH_TAC);;

let DIVIDES_2_NOT_1 = prove
 (`!n. n divides 2 /\ ~(n = 1) ==> n = 2`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `2:num`] DIVIDES_LE_STRONG) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* For positive m, ~(m divides 2) iff 2 < m.                                 *)
let NOT_DIVIDES_2 = prove
 (`!m. 0 < m ==> (~(m divides 2) <=> 2 < m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LT] THEN
    DISCH_TAC THEN SUBGOAL_THEN `m = 1 \/ m = 2` STRIP_ASSUME_TAC THEN
    ASM_REWRITE_TAC[] THEN TRY(CONV_TAC NUMBER_RULE) THEN ASM_ARITH_TAC;
    MESON_TAC[DIVIDES_LE; ARITH_RULE `~(2 = 0) /\ (2 < m ==> ~(m <= 2))`]]);;

let GENUS_ARITH_LEMMA = prove
 (`!lhs' rhs' lhs rhs.
    lhs' + rhs <= lhs + rhs'
    ==> (lhs' - rhs') DIV 2 <= (lhs - rhs) DIV 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC);;

let EVEN_GENUS_CONCLUDE = prove
 (`!c d g:num. c = 2 * g + d ==> c = 2 * ((c - d) DIV 2) + d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c - d = 2 * g:num` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[ARITH_RULE `(2 * g) DIV 2 = g`]] THEN
  ASM_ARITH_TAC);;

let MOD_CYCLE_REVERSE = prove
 (`!n i. ~(n = 0) /\ i < n
         ==> (n - 1 - (i + 1) MOD n + 1) MOD n = n - 1 - i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i + 1 < n \/ i + 1 = n` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i + 1 < n ==> n - 1 - (i + 1) + 1 < n`]
    THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[MOD_REFL; ARITH_RULE `~(n = 0) ==> n - 1 - 0 + 1 = n`] THEN
    ASM_ARITH_TAC]);;

let MOD_SUC_STEP = prove
 (`!i k n. 0 < n ==> ((i + k) MOD n + 1) MOD n = (i + SUC k) MOD n`,
  REWRITE_TAC[ADD1; ADD_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV MOD_DOWN_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Iteration.  ITERk is ITER k f z = f(...(f z)) for a numeral k, generated  *)
(* by ITER_NUMERAL_RULE; ITER_SHIFT, ITER_SUC_INNER and ITER_FIXED are       *)
(* forms of the library's ITER_ALT and ITER_FIXPOINT.                        *)
(* ------------------------------------------------------------------------- *)

let ITER_NUMERAL_RULE k =
  let f = `f:A->A` and z = `z:A` in
  let rec fpow j = if j = 0 then z else mk_comb(f,fpow(j - 1)) in
  prove(mk_eq(list_mk_icomb "ITER" [mk_small_numeral k; f; z],fpow k),
        CONV_TAC(LAND_CONV(TOP_DEPTH_CONV num_CONV)) THEN REWRITE_TAC[ITER]);;

let ITER2 = ITER_NUMERAL_RULE 2;;
let ITER3 = ITER_NUMERAL_RULE 3;;
let ITER4 = ITER_NUMERAL_RULE 4;;
let ITER5 = ITER_NUMERAL_RULE 5;;
let ITER6 = ITER_NUMERAL_RULE 6;;
let ITER7 = ITER_NUMERAL_RULE 7;;
let ITER8 = ITER_NUMERAL_RULE 8;;

let ITER_2 = prove (`!(f:A->A) z. ITER 2 f z = f(f z)`,
  REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; ITER]);;

let ITER_2_COMMUTE = prove
 (`!(f:A->A) m z. f (f (ITER m f z)) = ITER m f (f (f z))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM ITER_2; ITER_ADD] THEN
  REWRITE_TAC[ARITH_RULE `2 + m = m + 2`]);;

let ITER_NODE_TWICE = prove
 (`!(f:A->A) m y. f (f (ITER m f y)) = ITER (m + 2) f y`,
  REWRITE_TAC[ARITH_RULE `m + 2 = SUC(SUC m)`; ITER]);;

let ITER_SHIFT = prove
 (`!f k (x:A). ITER k f (f x) = ITER (SUC k) f x`,
  REWRITE_TAC[ITER_ALT]);;

let ITER_SUC_INNER = prove
 (`!k (f:A->A) w. ITER (SUC k) f w = ITER k f (f w)`,
  REWRITE_TAC[ITER_ALT]);;

let ITER_COMMUTE = prove
 (`!n (f:A->A) x. ITER n f (f x) = f (ITER n f x)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER]);;

(* Iterates of the identity.                                                 *)
let ITER_I' =
 prove(`!n x:A. ITER n I x = x`, INDUCT_TAC THEN
 ASM_REWRITE_TAC[ITER; I_THM]);;

let ITER_FIXED = prove
 (`!(f:A->A) x. f x = x ==> !n. ITER n f x = x`,
  SIMP_TAC[ITER_FIXPOINT]);;

(* If g agrees with f along the whole f-orbit of x, the two iterate          *)
(* sequences from x coincide.                                                *)
let ITER_AGREE = prove
 (`!(f:A->A) g x. (!k. g (ITER k f x) = f (ITER k f x)) ==>
 !k. ITER k g x = ITER k f x`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `k:num` th)) THEN ASM_REWRITE_TAC[]);;

(* h intertwines f and g on s ==> h intertwines ITER^n f and ITER^n g.       *)
let ITER_INTERTWINE = prove
 (`!f g (s:A->bool) (h:A->B).
     (!y. y IN s ==> f y IN s) /\
     (!x. x IN s ==> h(f x) = g(h x))
     ==> !n x. x IN s ==> h(ITER n f x) = ITER n g (h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ITER n (f:A->A) x IN s` ASSUME_TAC THENL
   [SPEC_TAC(`n:num`,`m:num`) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[ITER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B)(f(ITER n f x)) = g(h(ITER n (f:A->A) x))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let ITER_INJECTIVE = prove
 (`!(f:A->A) n x y.
     (!u v. f u = f v ==> u = v) /\ ITER n f x = ITER n f y ==> x = y`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN ASM_MESON_TAC[]);;

let ITER_CANCEL = prove
 (`!(f:A->A) i j x.
     (!u v. f u = f v ==> u = v) /\
     i < j /\
     ITER i f x = ITER j f x
     ==> ITER (j - i) f x = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ITER_INJECTIVE THEN
  MAP_EVERY EXISTS_TAC [`f:A->A`; `i:num`] THEN
  ASM_SIMP_TAC[ITER_ADD; ARITH_RULE `i < j ==> i + j - i = j`] THEN
  ASM_MESON_TAC[]);;

let ITER_PERIOD = prove
 (`!(f:A->A) z d k r.
     ITER d f z = z ==> ITER (k * d + r) f z = ITER r f z`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM ITER_ADD; GSYM ITER_MUL] THEN ASM_SIMP_TAC[ITER_FIXPOINT]);;

let ITER_MOD = prove
 (`!(f:A->A) z d n.
     0 < d /\ ITER d f z = z ==> ITER n f z = ITER (n MOD d) f z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:A->A`; `z:A`; `d:num`; `n DIV d`; `n MOD d`]
    ITER_PERIOD) THEN
  ASM_REWRITE_TAC[DIVISION_SIMP]);;

(* ------------------------------------------------------------------------- *)
(* Permutations, the periods of their orbits, and transpositions.            *)
(* ------------------------------------------------------------------------- *)

(* A permutation of s fixes every point outside s (three names in use).      *)
let PERMUTES_FIX_OUTSIDE = prove
 (`!p s (x:A). p permutes s /\ ~(x IN s) ==> p x = x`,
  REWRITE_TAC[permutes] THEN MESON_TAC[]);;

let PERMUTES_INJ = prove
 (`!(f:A->A) s x y. f permutes s ==> f x = f y ==> x = y`,
  MESON_TAC[PERMUTES_INJECTIVE]);;

(* A property holds on all of s iff it holds at p x for all x in s.          *)
let PERMUTES_FORALL_IN = prove
 (`!(p:A->A) s P.
     p permutes s ==> ((!x. x IN s ==> P(p x)) <=> (!x. x IN s ==> P x))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM(MATCH_MP PERMUTES_IMAGE th)]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE]);;

let ITER_PERMUTES_IN = prove
 (`!(f:A->A) s (x:A) n. f permutes s /\ x IN s ==> ITER n f x IN s`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ITER; PERMUTES_IN_IMAGE]);;

(* The period of x under a permutation of a finite set (library              *)
(* ORDER_EXISTENCE_FINITE), and the distinctness of the iterates below it.   *)
let ORBIT_PERIOD_EXISTS = prove
 (`!(f:A->A) s x.
     FINITE s /\ f permutes s /\ x IN s
     ==> ?d. 0 < d /\ (!n. ITER n f x = x <=> d divides n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(=):A->A->bool`; `f:A->A`; `x:A`]
    ORDER_EXISTENCE_FINITE) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `IMAGE (=) (s:A->bool)` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    GEN_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_MESON_TAC[ITER_PERMUTES_IN];
    ASM_MESON_TAC[PERMUTES_INJECTIVE]]);;

let ORBIT_ITER_DISTINCT = prove
 (`!(f:A->A) z d i j.
     (!u v. f u = f v ==> u = v) /\
     (!n. ITER n f z = z <=> d divides n) /\
     i < d /\ j < d /\
     ITER i f z = ITER j f z
     ==> i = j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. a < b /\ b < d /\ ITER a f z = ITER b (f:A->A) z ==> F`
   (fun th -> ASM_MESON_TAC[th; LT_CASES]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `a:num`; `b:num`; `z:A`] ITER_CANCEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_ARITH_TAC);;

(* Swap is an involution                                                     *)
let SWAP_INVOLUTION = prove
 (`!a b x:A. swap(a,b) (swap(a,b) x) = x`,
  REWRITE_TAC[swap] THEN MESON_TAC[]);;

(* Skipping z: swap(z, f(z)) o f permutes s DELETE z (library                *)
(* PERMUTES_INSERT_LEMMA); at a fixed point the skip is f itself.            *)
let PERMUTES_SWAP_COMPOSE = prove
 (`!(f:A->A) s z.
     f permutes s /\ z IN s ==> (swap(z, f z) o f) permutes (s DELETE z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_INSERT_LEMMA THEN
  ASM_SIMP_TAC[INSERT_DELETE]);;

let SKIP_FIXED_POINT = prove
 (`!(f:A->A) z. f z = z ==> swap(z, f z) o f = f`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SWAP_REFL; I_O_ID]);;

(* Conjugation by injective function commutes with swap                      *)
let SWAP_CONJUGATE_INJ = prove
 (`!(g:A->A) a b.
    (!x y. g x = g y ==> x = y)
    ==> g o swap(a,b) = swap(g a, g b) o g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; swap] THEN
  X_GEN_TAC `x:A` THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* Inverse of swap composed with permutation                                 *)
let INVERSE_SWAP_COMPOSE = prove
 (`!(f:A->A) s a b.
    f permutes s
    ==> inverse(swap(a,b) o f) = inverse f o swap(a,b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; SWAP_INVOLUTION]);;

(* Commuting swap past inverse of permutation (library SWAP_CONJUGATE)       *)
let SWAP_INVERSE_COMMUTE = prove
 (`!(g:A->A) s a b.
    g permutes s
    ==> swap(a,b) o inverse g = inverse g o swap(g a, g b)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP SWAP_CONJUGATE th)]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  ASM_REWRITE_TAC[o_ASSOC; I_O_ID]);;

(* Transposition composition identity (library SWAP_COMMON)                  *)
let SWAP_COMPOSE_IDENTITY = prove
 (`!a b c:A. ~(a = b) /\ ~(a = c) /\ ~(b = c)
    ==> swap(a,c) o swap(a,b) = swap(c,b) o swap(a,c)`,
  MESON_TAC[SWAP_COMMON]);;

(* Iterates of swap-composed function agree when no hits                     *)
let ITER_SWAP_AGREE = prove
 (`!(f:A->A) a b n.
     (!k. 0 < k /\ k <= n ==> ~(ITER k f a = a) /\ ~(ITER k f a = b))
     ==> ITER n (swap(a,b) o f) a = ITER n f a`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `ITER n (swap(a:A,b) o f) a = ITER n f a` SUBST1_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `~(f(ITER n f a):A = a) /\ ~(f(ITER n f a) = b)` MP_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN REWRITE_TAC[ITER; LE_REFL] THEN
   ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]];
   DISCH_THEN(fun th -> SIMP_TAC[MATCH_MP SWAP_OTHER th])]);;

(* ------------------------------------------------------------------------- *)
(* Finite sets, cardinality and injective maps.                              *)
(* ------------------------------------------------------------------------- *)

(* x IN (\z. MEM z l) <=> MEM x l (predicate-as-set membership).             *)
let IN_MEM_LAM = prove
 (`!(x:B) l. x IN (\z. MEM z l) <=> MEM x l`, REWRITE_TAC[IN_ELIM_THM]);;

let CARD_INS_STEP = prove
 (`!(x:A) s n. FINITE s /\ ~(x IN s) /\ CARD s = n ==>
 CARD(x INSERT s) = SUC n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES]);;

(* Inclusion-exclusion for two sets (library CARD_UNION_GEN).                *)
let CARD_UNION_INTER_EQ = prove
 (`!s t:A->bool. FINITE s /\ FINITE t
     ==> CARD(s UNION t) + CARD(s INTER t) = CARD s + CARD t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARD_UNION_GEN] THEN
  MATCH_MP_TAC(ARITH_RULE `c <= a ==> (a + b) - c + c = a + b`) THEN
  ASM_SIMP_TAC[CARD_SUBSET; INTER_SUBSET]);;

(* A finite set has at least two elements iff it has two distinct ones.      *)
let CARD_GE2 = prove
 (`!s:A->bool. FINITE s ==>
               (1 < CARD s <=> ?a b. a IN s /\ b IN s /\ ~(a = b))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:A->bool` CARD_LE_1) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[]);;

(* Any set of cardinality > 2 contains three distinct elements.              *)
let THREE_DISTINCT = prove
 (`!s:B->bool. 2 < CARD s
     ==> ?a b c. a IN s /\ b IN s /\ c IN s /\ ~(a = b) /\
     ~(a = c) /\ ~(b = c)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`3`; `s:B->bool`] CHOOSE_SUBSET_STRONG) THEN
  ANTS_TAC THENL [DISCH_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(t:B->bool) HAS_SIZE 3` THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B`
  (X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `b:B`; `c:B`] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM SET_TAC[]);;

(* Injective function has unique preimage                                    *)
let INJ_SELECT = prove
 (`!f:A->B s t x. INJ f s t /\ x IN s ==> (@y. y IN s /\ f y = f x) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN UNDISCH_TAC `INJ (f:A->B) s t` THEN
    REWRITE_TAC[INJ] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let INJ_ON_IMAGE_SUBSET = prove
 (`!(h:A->B) s a b.
     (!x y. x IN s /\ y IN s ==> (h x = h y <=> x = y)) /\
     a SUBSET s /\ b SUBSET s /\ IMAGE h a = IMAGE h b ==> a = b`,
  REPEAT STRIP_TAC THEN ASM SET_TAC[]);;

(* Functions with the same kernel on a finite set have images of the same    *)
(* cardinality: both are images of the pairing x |-> (ff x,gg x) under an    *)
(* injective projection.                                                     *)
let CARD_IMAGE_KERNEL = prove
 (`!(ff:A->B) (gg:A->C) s.
     FINITE s /\ (!x y. x IN s /\ y IN s ==> (ff x = ff y <=> gg x = gg y))
     ==> CARD(IMAGE ff s) = CARD(IMAGE gg s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (ff:A->B) s = IMAGE FST (IMAGE (\x. ff x,(gg:A->C) x) s) /\
    IMAGE gg s = IMAGE SND (IMAGE (\x. ff x,gg x) s)`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\x. (ff:A->B) x,(gg:A->C) x) s)` THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
               PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

(* A subset t closed under a map f that is injective on the finite superset  *)
(* s is mapped onto itself (library SURJECTIVE_IFF_INJECTIVE), so no point   *)
(* of s outside t is mapped into t.                                          *)
let PERM_COMPL_CLOSED = prove
 (`!(f:A->A) s t.
     FINITE s /\ t SUBSET s /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     (!x. x IN t ==> f x IN t)
     ==> !x. x IN s /\ ~(x IN t) ==> ~(f x IN t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:A->bool`; `f:A->A`] SURJECTIVE_IFF_INJECTIVE) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]];
                  ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lists: the head, the tail and the last element.                           *)
(* ------------------------------------------------------------------------- *)

(* HD of a nonempty list is a member.                                        *)
let HD_MEM = prove
 (`!(r:(A)list). ~(r = []) ==> MEM (HD r) r`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[HD; MEM] THEN MESON_TAC[]);;

let MEM_TL_IMP = prove
 (`!l:A list z. ~(l = []) /\ MEM z (TL l) ==> MEM z l`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[NOT_CONS_NIL; TL; MEM] THEN MESON_TAC[]);;

(* MEM through two TL layers (guarded).                                      *)
let MEM_TL_TL_IMP = prove
 (`!l:A list z. ~(l = []) /\ ~(TL l = []) /\ MEM z (TL(TL l)) ==> MEM z l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEM_TL_IMP THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_TL_IMP THEN ASM_REWRITE_TAC[]);;

(* The last element of a nonempty list is a member (two names in use).       *)
let MEM_LAST = prove
 (`!(l:(A)list). ~(l = []) ==> MEM (LAST l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; LAST; MEM] THEN
  ASM_CASES_TAC `t:(A)list = []` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let LAST_CONS_NE = prove
 (`!(h:A) t. ~(t = []) ==> LAST (h :: t) = LAST t`,
  REWRITE_TAC[LAST] THEN MESON_TAC[]);;

(* LAST of a snoc (two names in use) and of a cons-append (library           *)
(* LAST_APPEND).                                                             *)
let LAST_APPEND_SING = prove
 (`!l x:B. LAST(APPEND l [x]) = x`,
  REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL; LAST]);;

let LAST_SNOC' = prove
 (`!(r:(A)list) w. LAST (APPEND r [w]) = w`,
  REWRITE_TAC[LAST_APPEND_SING]);;

let LAST_CONS_SNOC = prove
 (`!z (r:(A)list) w. LAST (CONS z (APPEND r [w])) = w`,
  SIMP_TAC[LAST; LAST_APPEND; APPEND_EQ_NIL; NOT_CONS_NIL]);;

(* LAST skips a cons prefix when the appended tail is nonempty.              *)
let LAST_CONS_APPEND = prove
 (`!(q:(A)list) q' x. ~(q' = []) ==> LAST (CONS x (APPEND q q')) = LAST q'`,
  SIMP_TAC[LAST; LAST_APPEND; APPEND_EQ_NIL]);;

let LAST_MAP = prove
 (`!f:A->B l. ~(l = []) ==> LAST(MAP f l) = f(LAST l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; LAST; MAP_EQ_NIL] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let MEM_BUTLAST = prove
 (`!(x:A) l. MEM x (BUTLAST l) ==> MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[BUTLAST; MEM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let LENGTH_BUTLAST_1 = prove
 (`!l:(A)list. ~(l = []) ==> LENGTH (BUTLAST l) = LENGTH l - 1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP APPEND_BUTLAST_LAST) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th])
  THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;

(* A nonempty list is a snoc (library APPEND_BUTLAST_LAST).                  *)
let SNOC_DECOMP = prove
 (`!l:(A)list. ~(l = []) ==> ?m w. l = APPEND m [w]`,
  MESON_TAC[APPEND_BUTLAST_LAST]);;

(* ------------------------------------------------------------------------- *)
(* Lists: decomposition by length (LENGTH_NIL_CASES is the library           *)
(* LENGTH_EQ_CONS; two names each for length 2 and for splitting an append). *)
(* ------------------------------------------------------------------------- *)

let LENGTH_NIL_CASES = prove
 (`!l:(A)list n. LENGTH l = SUC n ==> ?h t. l = CONS h t /\ LENGTH t = n`,
  REWRITE_TAC[LENGTH_EQ_CONS]);;

let LIST_LENGTH_2 = prove
 (`!l:A list. LENGTH l = 2 ==> ?a b. l = [a; b]`,
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let LIST_LENGTH_GE_2 = prove
 (`!l:A list. 2 <= LENGTH l ==> ?a b r. l = CONS a (CONS b r)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(ARITH_RULE
   `2 <= LENGTH(l:A list) ==> LENGTH l = SUC(SUC(LENGTH l - 2))`) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`LENGTH(l:A list) - 2`,`m:num`) THEN
  REWRITE_TAC[LENGTH_EQ_CONS] THEN MESON_TAC[]);;

let LIST_HD2_TL2 = prove
 (`!l:(A)list. 2 <= LENGTH l ==> CONS (HD l) (CONS (HD(TL l)) (TL(TL l))) = l`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LIST_LENGTH_GE_2) THEN
  ASM_REWRITE_TAC[HD; TL]);;

let LIST_LENGTH_GE_3 = prove
 (`!l:A list. 3 <= LENGTH l ==> ?a b c r. l = CONS a (CONS b (CONS c r))`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(ARITH_RULE
   `3 <= LENGTH(l:A list) ==> LENGTH l = SUC(SUC(SUC(LENGTH l - 3)))`) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`LENGTH(l:A list) - 3`,`m:num`) THEN
  REWRITE_TAC[LENGTH_EQ_CONS] THEN MESON_TAC[]);;

(* >2 elements => at least 3 => structural [x;y;z;t].                        *)
let LEN3 = prove
 (`!l:(A)list. 2 < LENGTH l ==> ?x y z t. l = CONS x (CONS y (CONS z t))`,
  REWRITE_TAC[ARITH_RULE `2 < n <=> 3 <= n`; LIST_LENGTH_GE_3]);;

let LENGTH3_HDTL = prove
 (`!(qs:(A)list). 3 <= LENGTH qs
     ==> qs = CONS (HD qs)
     (CONS (HD (TL qs)) (CONS (HD (TL (TL qs))) (TL (TL (TL qs)))))`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LIST_LENGTH_GE_3) THEN
  ASM_REWRITE_TAC[HD; TL]);;

let LENGTH_TL3 = prove
 (`!l:(A)list. 3 <= LENGTH l ==> LENGTH (TL (TL (TL l))) = LENGTH l - 3`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LIST_LENGTH_GE_3) THEN
  ASM_REWRITE_TAC[TL; LENGTH] THEN ARITH_TAC);;

let APPEND_EQ_SPLIT = prove
 (`!(l1:(A)list) m1 l2 m2. LENGTH l1 = LENGTH m1
     ==> (APPEND l1 l2 = APPEND m1 m2 <=> l1 = m1 /\ l2 = m2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; APPEND; NOT_SUC; SUC_INJ; CONS_11; GSYM CONJ_ASSOC] THEN
  ASM_SIMP_TAC[]);;

let APPEND_EQ_SAME_LENGTH = prove
 (`!(a:(A)list) b c d. LENGTH a = LENGTH c ==>
                       (APPEND a b = APPEND c d <=> a = c /\ b = d)`,
  MATCH_ACCEPT_TAC APPEND_EQ_SPLIT);;

(* ------------------------------------------------------------------------- *)
(* Lists: splitting at a member (MEM_SPLIT is the library                    *)
(* MEM_APPEND_DECOMPOSE, FIRST_OCC_SPLIT is MEM_APPEND_DECOMPOSE_LEFT).      *)
(* ------------------------------------------------------------------------- *)

let MEM_SPLIT = prove
 (`!(y:A) p. MEM y p ==> ?p1 p2. p = APPEND p1 (CONS y p2)`,
  MESON_TAC[MEM_APPEND_DECOMPOSE]);;

(* first-occurrence split: MEM x l ==> l = a ++ x :: b with x not in a.      *)
let FIRST_OCC_SPLIT = prove
 (`!(x:A) l. MEM x l ==> ?a b. l = APPEND a (CONS x b) /\ ~MEM x a`,
  MESON_TAC[MEM_APPEND_DECOMPOSE_LEFT]);;

let FIRST_HIT_SPLIT = prove
 (`!P (l:(A)list). ?l1 l2. l = APPEND l1 l2 /\ ALL (\z. ~P z) l1 /\
                           (l2 = [] \/ ~(l2 = []) /\ P (HD l2))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [MAP_EVERY EXISTS_TAC [`[]:(A)list`; `[]:(A)list`] THEN
    REWRITE_TAC[APPEND; ALL]; ALL_TAC] THEN
  ASM_CASES_TAC `(P:A->bool) h` THENL
   [MAP_EVERY EXISTS_TAC [`[]:(A)list`; `CONS (h:A) t`] THEN
    ASM_REWRITE_TAC[APPEND; ALL; HD; NOT_CONS_NIL];
    FIRST_X_ASSUM(X_CHOOSE_THEN `l1:(A)list` (X_CHOOSE_THEN `l2:(A)list`
      STRIP_ASSUME_TAC) o check(fun th -> is_exists(concl th))) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:A) l1`; `l2:(A)list`] THEN
    ASM_REWRITE_TAC[APPEND; ALL]]);;

(* Decomposition of APPEND p q = APPEND p1 (a :: p2)                         *)
let APPEND_EQ_DECOMPOSE = prove
 (`!(p:(A)list) q p1 p2 a.
    APPEND p q = APPEND p1 (CONS a p2) ==>
    (?r. p = APPEND p1 (CONS a r) /\ p2 = APPEND r q) \/
    (?r. p1 = APPEND p r /\ q = APPEND r (CONS a p2))`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[APPEND] THEN MESON_TAC[];
    X_GEN_TAC `h:A` THEN X_GEN_TAC `t:(A)list` THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THEN
    SUBGOAL_THEN `(p1:(A)list) = [] \/ ?h' t'. p1 = CONS h' t'` MP_TAC THENL
     [MESON_TAC[list_CASES]; ALL_TAC] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[APPEND; CONS_11] THEN STRIP_TAC THEN
      DISJ1_TAC THEN EXISTS_TAC `t:(A)list` THEN ASM_REWRITE_TAC[APPEND];
      ASM_REWRITE_TAC[APPEND; CONS_11] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
        [`q:(A)list`; `t':(A)list`; `p2:(A)list`; `a:A`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [DISJ1_TAC THEN EXISTS_TAC `r:(A)list` THEN ASM_REWRITE_TAC[APPEND];
        DISJ2_TAC THEN EXISTS_TAC `r:(A)list` THEN
        ASM_REWRITE_TAC[APPEND]]]]);;

(* APPEND normal forms used to expose the (prefix ++ x :: suffix) shape.     *)
let NF1 = prove
 (`!(c1:A list) x c2 d.
     APPEND (APPEND c1 (CONS x c2)) d = APPEND c1 (CONS x (APPEND c2 d))`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let NF2 = prove
 (`!(d:A list) c1 x c2.
     APPEND d (APPEND c1 (CONS x c2)) = APPEND (APPEND d c1) (CONS x c2)`,
  REWRITE_TAC[APPEND_ASSOC]);;

(* a ++ (h :: t) = (a ++ [h]) ++ t  -- turns a walk-cons into                *)
(*                                  extend-then-tail                         *)
let APPEND_CONS_SNOC = prove
 (`!(a:(A)list) h t. APPEND a (CONS h t) = APPEND (APPEND a [h]) t`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

(* ------------------------------------------------------------------------- *)
(* Lists: ALL, EX, MEM, REVERSE and FILTER (forms of the library ALL_MEM).   *)
(* ------------------------------------------------------------------------- *)

let ALL_MEM_SELF = prove
 (`!(r:(A)list). ALL (\x. MEM x r) r`,
  GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN SIMP_TAC[]);;

(* ALL_MEM as a forward MP rule (ALL_MEM itself is orientated wrong for      *)
(* REWRITE)                                                                  *)
let ALL_MEM_D = prove
 (`!P (l:C list) x. ALL P l /\ MEM x l ==> P x`, MESON_TAC[ALL_MEM]);;

let ALL_MEM_TRANS = prove
 (`!P (l1:(A)list) l2. ALL (\z. MEM z l2) l1 /\ ALL P l2 ==> ALL P l1`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

let EX_APPEND = prove
 (`!P l1 l2:A list. EX P (APPEND l1 l2) <=> EX P l1 \/ EX P l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; EX; DISJ_ASSOC]);;

let MEM_COND_SING = prove
 (`!b (x:A) z. MEM z (if b then [x] else []) <=> b /\ z = x`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM]);;

let LENGTH_COND_SING = prove
 (`!b (x:A). LENGTH (if b then [x] else []) = if b then 1 else 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
  ARITH_TAC);;

(* MEM commutes with REVERSE                                                 *)
let MEM_REVERSE = prove
 (`!x:A l. MEM x (REVERSE l) <=> MEM x l`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[REVERSE; MEM; MEM_APPEND] THEN MESON_TAC[]);;

(* ALL P is invariant under REVERSE.                                         *)
let ALL_REVERSE = prove
 (`!P (l:A list). ALL P (REVERSE l) <=> ALL P l`,
  REWRITE_TAC[GSYM ALL_MEM; MEM_REVERSE]);;

let FILTER_FILTER = prove
 (`!P Q (l:A list). FILTER P (FILTER Q l) = FILTER (\x. Q x /\ P x) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN
  ASM_CASES_TAC `(Q:A->bool) h` THEN ASM_REWRITE_TAC[FILTER] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let FILTER_NONE = prove
 (`!P (l:A list). ALL (\x. ~P x) l ==> FILTER P l = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; FILTER] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let FILTER_EQ_MEM = prove
 (`!(P:A->bool) Q l. (!x. MEM x l ==> (P x <=> Q x)) ==>
                     FILTER P l = FILTER Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MEM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

let LENGTH_FILTER_REVERSE = prove
 (`!P l:A list. LENGTH (FILTER P (REVERSE l)) = LENGTH (FILTER P l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[REVERSE; FILTER; LENGTH; FILTER_APPEND; LENGTH_APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER; LENGTH] THEN ARITH_TAC);;

let COUNT_NEGB = prove
 (`!l. LENGTH(FILTER (\b. b) (MAP (\b. ~b) l)) =
       LENGTH(FILTER (\b:bool. ~b) l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; FILTER; LENGTH] THEN
  ASM_CASES_TAC `h:bool` THEN ASM_REWRITE_TAC[FILTER; LENGTH]);;

let MAP_NOT_REPLICATE_F = prove
 (`!n. MAP (\b:bool. ~b) (REPLICATE n F) = REPLICATE n T`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; MAP]);;

(* ------------------------------------------------------------------------- *)
(* Lists: EL, MAP, REVERSE, ZIP and MAP2.                                    *)
(* ------------------------------------------------------------------------- *)

(* EL in a reversed list                                                     *)
let EL_REVERSE = prove
 (`!(l:A list) i. i < LENGTH l ==> EL i (REVERSE l) = EL (LENGTH l - 1 - i) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  REWRITE_TAC[REVERSE; EL_APPEND; LENGTH_REVERSE; LT_SUC_LE; LE_LT] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUB_REFL; LT_REFL; EL; HD; ARITH_RULE
   `i < n ==> SUC n - 1 - i = SUC(n - 1 - i)`; ARITH_RULE `SUC n - 1 - n = 0`]
  THEN REWRITE_TAC[TL]);;

(* MAP f l1 = MAP g l2 implies pointwise equality via EL                     *)
let MAP_EL_EQ = prove
 (`!f:A->B g:C->B l1 l2.
    MAP f l1 = MAP g l2
    ==> (!i. i < LENGTH l1 ==> f(EL i l1) = g(EL i l2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EL i (MAP (f:A->B) l1) = EL i (MAP (g:C->B) l2)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `i < LENGTH(l2:C list)` ASSUME_TAC THENL
   [UNDISCH_TAC `MAP (f:A->B) l1 = MAP (g:C->B) l2` THEN
    DISCH_THEN(MP_TAC o AP_TERM `LENGTH:B list->num`) THEN
    REWRITE_TAC[LENGTH_MAP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP]);;

(* Border matching: same position in parallel lists                          *)
let BORDER_MATCH = prove
 (`!(bGr:E list) (bGd:A list) (hd:A->B) (hr:E->B) (kd:A->C) (kr:E->C) xr xd.
    PAIRWISE (\x y. ~(x = y)) bGr /\
    INJ hd (set_of_list bGd) (:B) /\
    MAP hr bGr = MAP hd (REVERSE bGd) /\
    MAP kr bGr = MAP kd (REVERSE bGd) /\
    MEM xr bGr /\ MEM xd bGd /\ hd xd = hr xr
    ==> kd xd = kr xr`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?i. i < LENGTH(bGr:E list) /\ xr = EL i bGr`
   (X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [ASM_MESON_TAC[MEM_EXISTS_EL]; ALL_TAC] THEN
  SUBGOAL_THEN `i < LENGTH(REVERSE(bGd:A list))` ASSUME_TAC THENL
   [UNDISCH_TAC `i < LENGTH(bGr:E list)` THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:B list->num`) THEN
    REWRITE_TAC[LENGTH_MAP] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kr:E->C`; `kd:A->C`; `bGr:E list`; `REVERSE(bGd:A list)`]
    MAP_EL_EQ) THEN
  MP_TAC(ISPECL [`hr:E->B`; `hd:A->B`; `bGr:E list`; `REVERSE(bGd:A list)`]
    MAP_EL_EQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o REWRITE_RULE[INJ]) THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN
  MP_TAC(ISPECL [`REVERSE(bGd:A list)`; `i:num`] MEM_EL) THEN
  ASM_REWRITE_TAC[MEM_REVERSE]);;

let EL_ZIP_FST = prove
 (`!(l1:A list) (l2:B list) i.
     LENGTH l1 = LENGTH l2 /\ i < LENGTH l1 ==>
     FST (EL i (ZIP l1 l2)) = EL i l1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l1:A list`; `l2:B list`] MAP_FST_ZIP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th])
  THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EL_MAP THEN
  ASM_SIMP_TAC[LENGTH_ZIP] THEN ASM_MESON_TAC[]);;

(* REPLICATE and EL as recursions on the numeral argument (for evaluation).  *)

let REPLICATE_NUM =
 prove(`!n (x:A). REPLICATE n x = if n = 0 then []
 else CONS x (REPLICATE (n - 1) x)`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; NOT_SUC; SUC_SUB1]);;

let EL_NUM =
  prove(`!n (l:A list). EL n l = if n = 0 then HD l else EL (n - 1) (TL l)`,
  INDUCT_TAC THEN REWRITE_TAC[EL; NOT_SUC; SUC_SUB1]);;

(* ------------------------------------------------------------------------- *)
(* Lists: PAIRWISE, and distinct lists (PAIRWISE (\x y. ~(x = y))).          *)
(* PAIRWISE_IMP_MEM and PAIRWISE_FROM_MEM are the library PAIRWISE_IMPLIES;  *)
(* two names each for injectivity of EL and for distinctness of REVERSE.     *)
(* ------------------------------------------------------------------------- *)

let PAIRWISE_IMP_MEM = prove
 (`!(P:A->A->bool) Q l. (!a b. MEM a l /\ MEM b l /\ P a b ==> Q a b) /\
                        PAIRWISE P l ==> PAIRWISE Q l`,
  MESON_TAC[PAIRWISE_IMPLIES]);;

let PAIRWISE_FROM_MEM = prove
 (`!(r:A->A->bool) l. (!x y. MEM x l /\ MEM y l /\ ~(x = y) ==> r x y) /\
                      PAIRWISE (\x y. ~(x = y)) l
                      ==> PAIRWISE r l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_IMPLIES THEN
  EXISTS_TAC `\x y:A. ~(x = y)` THEN ASM_SIMP_TAC[]);;

let PAIRWISE_FILTER_GEN = prove
 (`!(R:A->A->bool) P l. PAIRWISE R l ==> PAIRWISE R (FILTER P l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[PAIRWISE; ALL_FILTER] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

let PAIRWISE_APPEND_SYM_MEM = prove
 (`!(R:num->num->bool) l m.
     (!x y. MEM x (APPEND l m) /\ MEM y (APPEND l m) ==> (R x y <=> R y x))
     ==> (PAIRWISE R (APPEND l m) <=> PAIRWISE R (APPEND m l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MEM_APPEND] THEN DISCH_TAC THEN
  REWRITE_TAC[PAIRWISE_APPEND] THEN
  MATCH_MP_TAC(TAUT `(c <=> c') ==> (a /\ b /\ c <=> b /\ a /\ c')`) THEN
  EQ_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let PAIRWISE_REVERSE = prove
 (`!R:A->A->bool l. PAIRWISE R (REVERSE l) <=> PAIRWISE (\x y. R y x) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[REVERSE; PAIRWISE; PAIRWISE_APPEND; MEM; ALL] THEN
  ASM_REWRITE_TAC[MEM_REVERSE; GSYM ALL_MEM] THEN MESON_TAC[]);;

let PAIRWISE_REVERSE_SYM = prove
 (`!(R:A->A->bool) l. (!x y. R x y ==> R y x) ==>
                      (PAIRWISE R (REVERSE l) <=> PAIRWISE R l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PAIRWISE_REVERSE] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  ASM_MESON_TAC[]);;

let PAIRWISE_DISTINCT_REVERSE = prove
 (`!(r:(A)list). PAIRWISE (\x y. ~(x = y)) r ==>
                 PAIRWISE (\x y. ~(x = y)) (REVERSE r)`,
  SIMP_TAC[PAIRWISE_REVERSE_SYM]);;

(* REVERSE preserves duplicate-freeness (the symmetric distinctness          *)
(* relation).                                                                *)
let PAIRWISE_NEQ_REVERSE = prove
 (`!l:(A)list. PAIRWISE (\x y. ~(x = y)) l ==>
               PAIRWISE (\x y. ~(x = y)) (REVERSE l)`,
  MATCH_ACCEPT_TAC PAIRWISE_DISTINCT_REVERSE);;

(* PAIRWISE under an injective MAP (library PAIRWISE_MAP).                   *)
let PAIRWISE_INJ_MAP = prove
 (`!(f:A->B) l.
     (!a b. MEM a l /\ MEM b l /\ f a = f b ==> a = b) /\
     PAIRWISE (\x y. ~(x=y)) l
     ==> PAIRWISE (\x y. ~(x=y)) (MAP f l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PAIRWISE_MAP] THEN
  MATCH_MP_TAC PAIRWISE_IMPLIES THEN EXISTS_TAC `\x y:A. ~(x = y)` THEN
  ASM_MESON_TAC[]);;

(* PAIRWISE-distinct list whose members lie in a finite set has LENGTH <=    *)
(* CARD.                                                                     *)
let PAIRWISE_LENGTH_LE_CARD = prove
 (`!(s:A->bool) l. FINITE s /\ PAIRWISE (\a b. ~(a = b)) l /\
                   (!y. MEM y l ==> y IN s)
                   ==> LENGTH l <= CARD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `set_of_list (l:(A)list) HAS_SIZE LENGTH l` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE_SET_OF_LIST]; ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_SUBSET THEN
  ASM_REWRITE_TAC[SUBSET; IN_SET_OF_LIST]);;

(* EL injective on distinct lists.                                           *)
let EL_PAIRWISE_INJ = prove
 (`!(r:(A)list) i j. PAIRWISE (\x y. ~(x = y)) r /\ i < LENGTH r /\
                     j < LENGTH r /\ EL i r = EL j r ==> i = j`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT; PAIRWISE] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN
  INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC; SUC_INJ; NOT_SUC] THEN
  ASM_MESON_TAC[MEM_EL]);;

(* In a distinct list, a non-final element differs from the last.            *)
let MEM_BUTLAST_NEQ_LAST = prove
 (`!(l:(A)list) u. PAIRWISE (\a b. ~(a = b)) l /\ MEM u (BUTLAST l) ==>
                   ~(u = LAST l)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[BUTLAST; MEM]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`h:A`; `t:(A)list`] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `u:A` THEN
  ASM_CASES_TAC `t:(A)list = []` THENL
   [ASM_REWRITE_TAC[BUTLAST; MEM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[BUTLAST; LAST; PAIRWISE; MEM] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\b:A. ~(h = b)) t` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(MP_TAC o SPEC `LAST (t:(A)list)`) THEN ASM_SIMP_TAC[MEM_LAST];
    REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;
