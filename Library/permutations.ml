(* ========================================================================= *)
(* Permutations, both general and specifically on finite sets.               *)
(* ========================================================================= *)

parse_as_infix("permutes",(12,"right"));;

let permutes = new_definition
 `p permutes s <=> (!x. ~(x IN s) ==> p(x) = x) /\ (!y. ?!x. p x = y)`;;

(* ------------------------------------------------------------------------- *)
(* Inverse function (on whole universe).                                     *)
(* ------------------------------------------------------------------------- *)

let inverse = new_definition
 `inverse(f) = \y. @x. f x = y`;;

let SURJECTIVE_INVERSE = prove
 (`!f. (!y. ?x. f x = y) <=> !y. f(inverse f y) = y`,
  REWRITE_TAC[SURJECTIVE_RIGHT_INVERSE; inverse] THEN MESON_TAC[]);;

let SURJECTIVE_INVERSE_o = prove
 (`!f. (!y. ?x. f x = y) <=> (f o inverse f = I)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; SURJECTIVE_INVERSE]);;

let INJECTIVE_INVERSE = prove
 (`!f. (!x x'. f x = f x' ==> x = x') <=> !x. inverse f (f x) = x`,
  MESON_TAC[inverse]);;

let INJECTIVE_INVERSE_o = prove
 (`!f. (!x x'. f x = f x' ==> x = x') <=> (inverse f o f = I)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; INJECTIVE_INVERSE]);;

let INVERSE_UNIQUE_o = prove
 (`!f g. f o g = I /\ g o f = I ==> inverse f = g`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  MESON_TAC[INJECTIVE_INVERSE; SURJECTIVE_INVERSE]);;

let INVERSE_I = prove
 (`inverse I = I`,
  MATCH_MP_TAC INVERSE_UNIQUE_o THEN REWRITE_TAC[I_O_ID]);;

(* ------------------------------------------------------------------------- *)
(* Transpositions.                                                           *)
(* ------------------------------------------------------------------------- *)

let swap = new_definition
 `swap(i,j) k = if k = i then j else if k = j then i else k`;;

let SWAP_REFL = prove
 (`!a. swap(a,a) = I`,
  REWRITE_TAC[FUN_EQ_THM; swap; I_THM] THEN MESON_TAC[]);;

let SWAP_SYM = prove
 (`!a b. swap(a,b) = swap(b,a)`,
  REWRITE_TAC[FUN_EQ_THM; swap; I_THM] THEN MESON_TAC[]);;

let SWAP_IDEMPOTENT = prove
 (`!a b. swap(a,b) o swap(a,b) = I`,
  REWRITE_TAC[FUN_EQ_THM; swap; o_THM; I_THM] THEN MESON_TAC[]);;

let INVERSE_SWAP = prove
 (`!a b. inverse(swap(a,b)) = swap(a,b)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  REWRITE_TAC[SWAP_SYM; SWAP_IDEMPOTENT]);;

let SWAP_GALOIS = prove
 (`!a b x y. x = swap(a,b) y <=> y = swap(a,b) x`,
  REWRITE_TAC[swap] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic consequences of the definition.                                     *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_IN_IMAGE = prove
 (`!p s x. p permutes s ==> (p(x) IN s <=> x IN s)`,
  REWRITE_TAC[permutes] THEN MESON_TAC[]);;

let PERMUTES_IMAGE = prove
 (`!p s. p permutes s ==> IMAGE p s = s`,
  REWRITE_TAC[permutes; EXTENSION; IN_IMAGE] THEN MESON_TAC[]);;

let PERMUTES_INJECTIVE = prove
 (`!p s. p permutes s ==> !x y. p(x) = p(y) <=> x = y`,
  REWRITE_TAC[permutes] THEN MESON_TAC[]);;

let PERMUTES_SURJECTIVE = prove
 (`!p s. p permutes s ==> !y. ?x. p(x) = y`,
  REWRITE_TAC[permutes] THEN MESON_TAC[]);;

let PERMUTES_INVERSES_o = prove
 (`!p s. p permutes s ==> p o inverse(p) = I /\ inverse(p) o p = I`,
  REWRITE_TAC[GSYM INJECTIVE_INVERSE_o; GSYM SURJECTIVE_INVERSE_o] THEN
  REWRITE_TAC[permutes] THEN MESON_TAC[]);;

let PERMUTES_INVERSES = prove
 (`!p s. p permutes s
         ==> (!x. p(inverse p x) = x) /\ (!x. inverse p (p x) = x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM]);;

let PERMUTES_SUBSET = prove
 (`!p s t. p permutes s /\ s SUBSET t ==> p permutes t`,
  REWRITE_TAC[permutes; SUBSET] THEN MESON_TAC[]);;

let PERMUTES_EMPTY = prove
 (`!p. p permutes {} <=> p = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM; permutes; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let PERMUTES_SING = prove
 (`!p a.  p permutes {a} <=> p = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM; permutes; IN_SING] THEN MESON_TAC[]);;

let PERMUTES_UNIV = prove
 (`!p. p permutes UNIV <=> !y:A. ?!x. p x = y`,
  REWRITE_TAC[permutes; IN_UNIV] THEN MESON_TAC[]);;

let PERMUTES_INVERSE_EQ = prove
 (`!p s. p permutes s ==> !x y. inverse p y = x <=> p x = y`,
  REWRITE_TAC[permutes; inverse] THEN MESON_TAC[]);;

let PERMUTES_SWAP = prove
 (`!a b s. a IN s /\ b IN s ==> swap(a,b) permutes s`,
  REWRITE_TAC[permutes; swap] THEN MESON_TAC[]);;

let PERMUTES_SUPERSET = prove
 (`!p s t. p permutes s /\ (!x. x IN (s DIFF t) ==> p(x) = x)
           ==> p permutes t`,
  REWRITE_TAC[permutes; IN_DIFF] THEN MESON_TAC[]);;

let PERMUTES_BIJECTIONS = prove
 (`!p q. (!x. x IN s ==> p x IN s) /\ (!x. ~(x IN s) ==> p x = x) /\
         (!x. x IN s ==> q x IN s) /\ (!x. ~(x IN s) ==> q x = x) /\
         (!x. p(q x) = x) /\ (!x. q(p x) = x)
         ==> p permutes s`,
  REWRITE_TAC[permutes] THEN MESON_TAC[]);;

let PERMUTES_INVERSE_FUNCTION = prove
 (`!s p:A->A.
        p permutes s <=>
        ?q. (!x. ~(x IN s) ==> p x = x) /\
            (!x. x IN s ==> p x IN s) /\
            (!x. x IN s ==> p(q x) = x /\ q(p x) = x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `inverse p:A->A` THEN
    ASM_MESON_TAC[permutes; PERMUTES_INVERSES];
    STRIP_TAC THEN ASM_SIMP_TAC[permutes; SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
  ASM_CASES_TAC `(x:A) IN s` THENL
   [EXISTS_TAC `(q:A->A) x`; EXISTS_TAC `x:A`] THEN
  ASM_MESON_TAC[]]);;

let PERMUTES_ALT = prove
 (`!(p:A->A) s.
        p permutes s <=>
        (!x. x IN s ==> p x IN s) /\
        (!x. ~(x IN s) ==> p x = x) /\
        (!y. y IN s ==> ?!x. x IN s /\ p x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[permutes] THEN
  EQ_TAC THEN SIMP_TAC[] THENL [MESON_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `!s. (!y. ~(y IN s) ==> P y) /\ (!y. y IN s ==> P y) ==> !y. P y`) THEN
  EXISTS_TAC `IMAGE (p:A->A) s` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  ASM SET_TAC[]);;

let PERMUTES_RESTRICT_SET = prove
 (`!Q p s:A->bool.
        p permutes s /\ (!x. x IN s ==> (Q(p x) <=> Q x))
        ==> (\i. if Q i then p i else i) permutes {x | x IN s /\ Q x}`,
  REWRITE_TAC[PERMUTES_ALT] THEN SET_TAC[]);;

let PERMUTES_RESTRICT = prove
 (`!Q p s:A->bool.
        p permutes s /\ (!x. x IN s ==> (Q(p x) <=> Q x))
        ==> (\i. if Q i then p i else i) permutes s`,
  REWRITE_TAC[PERMUTES_ALT] THEN SET_TAC[]);;

let PERMUTES_CARTESIAN_PRODUCT = prove
 (`!(p:A->A) (q:B->B) s t.
        p permutes s /\ q permutes t
        ==> (\(i,j). if i IN s /\ j IN t then p i,q j else i,j)
            permutes (s CROSS t)`,
  REWRITE_TAC[permutes; EXISTS_UNIQUE_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; PAIR_EQ; IN_CROSS] THEN
  REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let PERMUTES_TRANSFER_BIJECTIONS = prove
 (`!(f:A->B) f' p s t.
        (!x. f'(f x) = x) /\ (!y. f(f' y) = y) /\
        (!x. x IN s ==> f x IN t) /\
        (!y. y IN t ==> f' y IN s)
        ==> ((f' o p o f) permutes s <=> p permutes t)`,
  REWRITE_TAC[permutes; o_THM] THEN MESON_TAC[]);;

let PERMUTES_TRANSFER = prove
 (`!(f:A->B) p q s.
        p permutes s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        (!x. x IN s ==> q(f x) = f(p x)) /\
        (!y. ~(y IN IMAGE f s) ==> q y = y)
        ==> q permutes (IMAGE f s)`,
  SIMP_TAC[PERMUTES_ALT] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Group properties.                                                         *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_ID = prove
 (`!s:A->bool. (\x. x) permutes s`,
  REWRITE_TAC[permutes] THEN MESON_TAC[]);;

let PERMUTES_I = prove
 (`!s. I permutes s`,
  REWRITE_TAC[permutes; I_THM] THEN MESON_TAC[]);;

let PERMUTES_COMPOSE = prove
 (`!p q s. p permutes s /\ q permutes s ==> (q o p) permutes s`,
  REWRITE_TAC[permutes; o_THM] THEN METIS_TAC[]);;

let PERMUTES_INVERSE = prove
 (`!p s. p permutes s ==> inverse(p) permutes s`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_INVERSE_EQ) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[permutes] THEN MESON_TAC[]);;

let PERMUTES_INVERSE_INVERSE = prove
 (`!p. p permutes s ==> inverse(inverse p) = p`,
  SIMP_TAC[FUN_EQ_THM] THEN MESON_TAC[PERMUTES_INVERSE_EQ; PERMUTES_INVERSE]);;

(* ------------------------------------------------------------------------- *)
(* The number of permutations on a finite set.                               *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_INSERT_LEMMA = prove
 (`!p a:A s. p permutes (a INSERT s) ==> (swap(a,p(a)) o p) permutes s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_SUPERSET THEN
  EXISTS_TAC `(a:A) INSERT s` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PERMUTES_SWAP; PERMUTES_IN_IMAGE;
                  IN_INSERT; PERMUTES_COMPOSE];
    REWRITE_TAC[o_THM; swap; IN_INSERT; IN_DIFF] THEN ASM_MESON_TAC[]]);;

let PERMUTES_INSERT = prove
 (`{p:A->A | p permutes (a INSERT s)} =
        IMAGE (\(b,p). swap(a,b) o p)
              {(b,p) | b IN a INSERT s /\ p IN {p | p permutes s}}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_PAIR_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN
  X_GEN_TAC `p:A->A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN EQ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY EXISTS_TAC
      [`(p:A->A) a`; `swap(a,p a) o (p:A->A)`] THEN
    ASM_SIMP_TAC[SWAP_IDEMPOTENT; o_ASSOC; I_O_ID; PERMUTES_INSERT_LEMMA] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_INSERT];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`b:A`; `q:A->A`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PERMUTES_COMPOSE THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[PERMUTES_SUBSET; SUBSET; IN_INSERT];
      MATCH_MP_TAC PERMUTES_SWAP THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_INSERT]]]);;

let HAS_SIZE_PERMUTATIONS = prove
 (`!s:A->bool n. s HAS_SIZE n ==> {p | p permutes s} HAS_SIZE (FACT n)`,
  REWRITE_TAC[HAS_SIZE; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PERMUTES_EMPTY; CARD_CLAUSES; SET_RULE `{x | x = a} = {a}`] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN REWRITE_TAC[GSYM HAS_SIZE] THEN
  STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[FACT; PERMUTES_INSERT] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ASM_SIMP_TAC[HAS_SIZE_PRODUCT; HAS_SIZE; FINITE_INSERT; CARD_CLAUSES] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM; PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `q:A->A`; `c:A`; `r:A->A`] THEN
  STRIP_TAC THEN SUBGOAL_THEN `c:A = b` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C AP_THM `a:A`) THEN REWRITE_TAC[o_THM; swap] THEN
    SUBGOAL_THEN `(q:A->A) a = a /\ (r:A->A) a = a` (fun t -> SIMP_TAC[t]) THEN
    ASM_MESON_TAC[permutes];
    FIRST_X_ASSUM(MP_TAC o AP_TERM `(\q:A->A. swap(a:A,b) o q)`) THEN
    ASM_SIMP_TAC[SWAP_IDEMPOTENT; o_ASSOC; I_O_ID]]);;

let FINITE_PERMUTATIONS = prove
 (`!s. FINITE s ==> FINITE {p | p permutes s}`,
  MESON_TAC[HAS_SIZE_PERMUTATIONS; HAS_SIZE]);;

let CARD_PERMUTATIONS = prove
 (`!s. FINITE s ==> CARD {p | p permutes s} = FACT(CARD s)`,
  MESON_TAC[HAS_SIZE; HAS_SIZE_PERMUTATIONS]);;

(* ------------------------------------------------------------------------- *)
(* Alternative characterizations of permutation of finite set.               *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_FINITE_INJECTIVE = prove
 (`!s:A->bool p.
        FINITE s
        ==> (p permutes s <=>
             (!x. ~(x IN s) ==> p x = x) /\
             (!x. x IN s ==> p x IN s) /\
             (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y))`,
  REWRITE_TAC[permutes] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `p:A->A` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] SURJECTIVE_IFF_INJECTIVE)) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IMP_IMP; GSYM CONJ_ASSOC] THEN
  STRIP_TAC THEN X_GEN_TAC `y:A` THEN
  ASM_CASES_TAC `(y:A) IN s` THEN ASM_MESON_TAC[]);;

let PERMUTES_FINITE_SURJECTIVE = prove
 (`!s:A->bool p.
        FINITE s
        ==> (p permutes s <=>
             (!x. ~(x IN s) ==> p x = x) /\ (!x. x IN s ==> p x IN s) /\
             (!y. y IN s ==> ?x. x IN s /\ p x = y))`,
  REWRITE_TAC[permutes] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `p:A->A` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] SURJECTIVE_IFF_INJECTIVE)) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IMP_IMP; GSYM CONJ_ASSOC] THEN
  STRIP_TAC THEN X_GEN_TAC `y:A` THEN
  ASM_CASES_TAC `(y:A) IN s` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Permutations of index set for iterated operations.                        *)
(* ------------------------------------------------------------------------- *)

let ITERATE_PERMUTE = prove
 (`!op. monoidal op
        ==> !f p s. p permutes s ==> iterate op s f = iterate op s (f o p)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_BIJECTION) THEN
  ASM_MESON_TAC[permutes]);;

let NSUM_PERMUTE = prove
 (`!f p s. p permutes s ==> nsum s f = nsum s (f o p)`,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_PERMUTE_NUMSEG = prove
 (`!f p m n. p permutes m..n ==> nsum(m..n) f = nsum(m..n) (f o p)`,
  MESON_TAC[NSUM_PERMUTE; FINITE_NUMSEG]);;

let SUM_PERMUTE = prove
 (`!f p s. p permutes s ==> sum s f = sum s (f o p)`,
  REWRITE_TAC[sum] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_PERMUTE_NUMSEG = prove
 (`!f p m n. p permutes m..n ==> sum(m..n) f = sum(m..n) (f o p)`,
  MESON_TAC[SUM_PERMUTE; FINITE_NUMSEG]);;

(* ------------------------------------------------------------------------- *)
(* Various combinations of transpositions with 2, 1 and 0 common elements.   *)
(* ------------------------------------------------------------------------- *)

let SWAP_COMMON = prove
 (`!a b c:A. ~(a = c) /\ ~(b = c)
             ==> swap(a,b) o swap(a,c) = swap(b,c) o swap(a,b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; swap; o_THM; I_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN
  MAP_EVERY ASM_CASES_TAC [`x:A = a`; `x:A = b`; `x:A = c`] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let SWAP_COMMON' = prove
 (`!a b c:A. ~(a = b) /\ ~(a = c)
             ==> swap(a,c) o swap(b,c) = swap(b,c) o swap(a,b)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SWAP_SYM] THEN
  ASM_SIMP_TAC[GSYM SWAP_COMMON] THEN REWRITE_TAC[SWAP_SYM]);;

let SWAP_INDEPENDENT = prove
 (`!a b c d:A. ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d)
               ==> swap(a,b) o swap(c,d) = swap(c,d) o swap(a,b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; swap; o_THM; I_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN
  MAP_EVERY ASM_CASES_TAC [`x:A = a`; `x:A = b`; `x:A = c`] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Permutations as transposition sequences.                                  *)
(* ------------------------------------------------------------------------- *)

let swapseq_RULES,swapseq_INDUCT,swapseq_CASES = new_inductive_definition
 `(swapseq 0 I) /\
  (!a b p n. swapseq n p /\ ~(a = b) ==> swapseq (SUC n) (swap(a,b) o p))`;;

let permutation = new_definition
 `permutation p <=> ?n. swapseq n p`;;

(* ------------------------------------------------------------------------- *)
(* Some closure properties of the set of permutations, with lengths.         *)
(* ------------------------------------------------------------------------- *)

let SWAPSEQ_I = CONJUNCT1 swapseq_RULES;;

let PERMUTATION_I = prove
 (`permutation I`,
  REWRITE_TAC[permutation] THEN MESON_TAC[SWAPSEQ_I]);;

let SWAPSEQ_SWAP = prove
 (`!a b. swapseq (if a = b then 0 else 1) (swap(a,b))`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[num_CONV `1`] THEN
  ASM_MESON_TAC[swapseq_RULES; I_O_ID; SWAPSEQ_I; SWAP_REFL]);;

let PERMUTATION_SWAP = prove
 (`!a b. permutation(swap(a,b))`,
  REWRITE_TAC[permutation] THEN MESON_TAC[SWAPSEQ_SWAP]);;

let SWAPSEQ_COMPOSE = prove
 (`!n p m q. swapseq n p /\ swapseq m q ==> swapseq (n + m) (p o q)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC swapseq_INDUCT THEN
  REWRITE_TAC[ADD_CLAUSES; I_O_ID; GSYM o_ASSOC] THEN
  MESON_TAC[swapseq_RULES]);;

let PERMUTATION_COMPOSE = prove
 (`!p q. permutation p /\ permutation q ==> permutation(p o q)`,
  REWRITE_TAC[permutation] THEN MESON_TAC[SWAPSEQ_COMPOSE]);;

let SWAPSEQ_ENDSWAP = prove
 (`!n p a b:A. swapseq n p /\ ~(a = b) ==> swapseq (SUC n) (p o swap(a,b))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC swapseq_INDUCT THEN REWRITE_TAC[I_O_ID; GSYM o_ASSOC] THEN
  MESON_TAC[o_ASSOC; swapseq_RULES; I_O_ID]);;

let SWAPSEQ_INVERSE_EXISTS = prove
 (`!n p:A->A. swapseq n p ==> ?q. swapseq n q /\ p o q = I /\ q o p = I`,
  MATCH_MP_TAC swapseq_INDUCT THEN CONJ_TAC THENL
   [MESON_TAC[I_O_ID; swapseq_RULES]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `q:A->A`; `a:A`; `b:A`] SWAPSEQ_ENDSWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `(q:A->A) o swap (a,b)` THEN
  ASM_REWRITE_TAC[GSYM o_ASSOC] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o RAND_CONV) [o_ASSOC] THEN
  ASM_REWRITE_TAC[SWAP_IDEMPOTENT; I_O_ID]);;

let SWAPSEQ_INVERSE = prove
 (`!n p. swapseq n p ==> swapseq n (inverse p)`,
  MESON_TAC[SWAPSEQ_INVERSE_EXISTS; INVERSE_UNIQUE_o]);;

let PERMUTATION_INVERSE = prove
 (`!p. permutation p ==> permutation(inverse p)`,
  REWRITE_TAC[permutation] THEN MESON_TAC[SWAPSEQ_INVERSE]);;

(* ------------------------------------------------------------------------- *)
(* The identity map only has even transposition sequences.                   *)
(* ------------------------------------------------------------------------- *)

let SYMMETRY_LEMMA = prove
 (`(!a b c d. P a b c d ==> P a b d c) /\
   (!a b c d. ~(a = b) /\ ~(c = d) /\
              (a = c /\ b = d \/ a = c /\ ~(b = d) \/ ~(a = c) /\ b = d \/
               ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d))
              ==> P a b c d)
   ==> (!a b c d:A. ~(a = b) /\ ~(c = d) ==> P a b c d)`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`a:A = c`; `a:A = d`; `b:A = c`; `b:A = d`] THEN
  ASM_MESON_TAC[]);;

let SWAP_GENERAL = prove
 (`!a b c d:A.
        ~(a = b) /\ ~(c = d)
        ==> swap(a,b) o swap(c,d) = I \/
            ?x y z. ~(x = a) /\ ~(y = a) /\ ~(z = a) /\ ~(x = y) /\
                    swap(a,b) o swap(c,d) = swap(x,y) o swap(a,z)`,
  MATCH_MP_TAC SYMMETRY_LEMMA THEN CONJ_TAC THENL
   [REWRITE_TAC[SWAP_SYM] THEN SIMP_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THENL
   [MESON_TAC[SWAP_IDEMPOTENT];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`b:A`; `d:A`; `b:A`] THEN
    ASM_MESON_TAC[SWAP_COMMON];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`c:A`; `d:A`; `c:A`] THEN
    ASM_MESON_TAC[SWAP_COMMON'];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`c:A`; `d:A`; `b:A`] THEN
    ASM_MESON_TAC[SWAP_INDEPENDENT]]);;

let FIXING_SWAPSEQ_DECREASE = prove
 (`!n p a b:A.
      swapseq n p /\ ~(a = b) /\ (swap(a,b) o p) a = a
      ==> ~(n = 0) /\ swapseq (n - 1) (swap(a,b) o p)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [swapseq_CASES] THEN
  REWRITE_TAC[NOT_SUC] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[I_THM; o_THM; swap] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:A`; `d:A`; `q:A->A`; `m:num`] THEN
  REWRITE_TAC[SUC_INJ; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[o_ASSOC] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:A`; `b:A`; `c:A`; `d:A`] SWAP_GENERAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[I_O_ID; SUC_SUB1; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `z:A`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`q:A->A`; `a:A`; `z:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check(is_eq o concl)) THEN
    REWRITE_TAC[GSYM o_ASSOC] THEN
    ABBREV_TAC `r:A->A = swap(a:A,z) o q` THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; swap] THEN ASM_MESON_TAC[];
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[NOT_SUC; SUC_SUB1; GSYM o_ASSOC] THEN
    ASM_MESON_TAC[swapseq_RULES]]);;

let SWAPSEQ_IDENTITY_EVEN = prove
 (`!n. swapseq n (I:A->A) ==> EVEN n`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [swapseq_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (SUBST_ALL_TAC o CONJUNCT1) MP_TAC) THEN
  REWRITE_TAC[EVEN; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`; `p:A->A`; `m:num`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  MP_TAC(SPECL [`m:num`; `p:A->A`; `a:A`; `b:A`] FIXING_SWAPSEQ_DECREASE) THEN
  ASM_REWRITE_TAC[I_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m - 1`) THEN
  UNDISCH_THEN `SUC m = n` (SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `m - 1 < SUC m`] THEN UNDISCH_TAC `~(m = 0)` THEN
  SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[SUC_SUB1; EVEN]);;

(* ------------------------------------------------------------------------- *)
(* Therefore we have a welldefined notion of parity.                         *)
(* ------------------------------------------------------------------------- *)

let evenperm = new_definition `evenperm(p) = EVEN(@n. swapseq n p)`;;

let SWAPSEQ_EVEN_EVEN = prove
 (`!m n p:A->A. swapseq m p /\ swapseq n p ==> (EVEN m <=> EVEN n)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SWAPSEQ_INVERSE_EXISTS) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `swapseq (n + m) :(A->A)->bool`) THEN
  ASM_SIMP_TAC[SWAPSEQ_COMPOSE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SWAPSEQ_IDENTITY_EVEN) THEN
  SIMP_TAC[EVEN_ADD]);;

let EVENPERM_UNIQUE = prove
 (`!n p b. swapseq n p /\ EVEN n = b ==> evenperm p = b`,
  REWRITE_TAC[evenperm] THEN MESON_TAC[SWAPSEQ_EVEN_EVEN]);;

(* ------------------------------------------------------------------------- *)
(* And it has the expected composition properties.                           *)
(* ------------------------------------------------------------------------- *)

let EVENPERM_I = prove
 (`evenperm I = T`,
  MATCH_MP_TAC EVENPERM_UNIQUE THEN MESON_TAC[swapseq_RULES; EVEN]);;

let EVENPERM_ID = prove
 (`evenperm(\x:A. x)`,
  REWRITE_TAC[GSYM I_DEF; EVENPERM_I]);;

let EVENPERM_SWAP = prove
 (`!a b:A. evenperm(swap(a,b)) = (a = b)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EVENPERM_UNIQUE THEN
  MESON_TAC[SWAPSEQ_SWAP; NUM_RED_CONV `EVEN 0`; NUM_RED_CONV `EVEN 1`]);;

let EVENPERM_COMPOSE = prove
 (`!p q. permutation p /\ permutation q
         ==> evenperm (p o q) = (evenperm p = evenperm q)`,
  REWRITE_TAC[permutation; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
               ASSUME_TAC(MATCH_MP SWAPSEQ_COMPOSE th)) THEN
  ASM_MESON_TAC[EVENPERM_UNIQUE; SWAPSEQ_COMPOSE; EVEN_ADD]);;

let EVENPERM_INVERSE = prove
 (`!p. permutation p ==> evenperm(inverse p) = evenperm p`,
  REWRITE_TAC[permutation] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EVENPERM_UNIQUE THEN
  ASM_MESON_TAC[SWAPSEQ_INVERSE; EVENPERM_UNIQUE]);;

(* ------------------------------------------------------------------------- *)
(* A more abstract characterization of permutations.                         *)
(* ------------------------------------------------------------------------- *)

let PERMUTATION_BIJECTIVE = prove
 (`!p. permutation p ==> !y. ?!x. p(x) = y`,
  REWRITE_TAC[permutation] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SWAPSEQ_INVERSE_EXISTS) THEN
  REWRITE_TAC[FUN_EQ_THM; I_THM; o_THM; LEFT_IMP_EXISTS_THM] THEN
  MESON_TAC[]);;

let PERMUTATION_FINITE_SUPPORT = prove
 (`!p. permutation p ==> FINITE {x:A | ~(p x = x)}`,
  REWRITE_TAC[permutation; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC swapseq_INDUCT THEN
  REWRITE_TAC[I_THM; FINITE_RULES; SET_RULE `{x | F} = {}`] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`; `p:A->A`] THEN
  STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(a:A) INSERT b INSERT {x | ~(p x = x)}` THEN
  ASM_REWRITE_TAC[FINITE_INSERT; SUBSET; IN_INSERT; IN_ELIM_THM] THEN
  REWRITE_TAC[o_THM; swap] THEN MESON_TAC[]);;

let PERMUTATION_LEMMA = prove
 (`!s p:A->A.
       FINITE s /\
       (!y. ?!x. p(x) = y) /\ (!x. ~(x IN s) ==> p x = x)
       ==> permutation p`,
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `p:A->A = I` (fun th -> REWRITE_TAC[th; PERMUTATION_I]) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; I_THM];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `permutation((swap(a,p(a)) o swap(a,p(a))) o (p:A->A))`
  MP_TAC THENL [ALL_TAC; REWRITE_TAC[SWAP_IDEMPOTENT; I_O_ID]] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN MATCH_MP_TAC PERMUTATION_COMPOSE THEN
  REWRITE_TAC[PERMUTATION_SWAP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `!y. ?!x. (p:A->A) x = y` THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM; swap; o_THM] THEN
    ASM_CASES_TAC `(p:A->A) a = a` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[TAUT
     `(if p then x else y) = a <=> if p then x = a else y = a`] THEN
    REWRITE_TAC[TAUT `(if p then x else y) <=> p /\ x \/ ~p /\ y`] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[swap; o_THM] THEN
    ASM_CASES_TAC `(p:A->A) a = a` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

let PERMUTATION = prove
 (`!p. permutation p <=> (!y. ?!x. p(x) = y) /\ FINITE {x:A | ~(p(x) = x)}`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[PERMUTATION_BIJECTIVE; PERMUTATION_FINITE_SUPPORT] THEN
  STRIP_TAC THEN MATCH_MP_TAC PERMUTATION_LEMMA THEN
  EXISTS_TAC `{x:A | ~(p x = x)}` THEN
  ASM_SIMP_TAC[IN_ELIM_THM]);;

let PERMUTATION_INVERSE_WORKS = prove
 (`!p. permutation p ==> inverse p o p = I /\ p o inverse p = I`,
  MESON_TAC[PERMUTATION_BIJECTIVE; SURJECTIVE_INVERSE_o;
            INJECTIVE_INVERSE_o]);;

let PERMUTATION_INVERSE_COMPOSE = prove
 (`!p q. permutation p /\ permutation q
         ==> inverse(p o q) = inverse q o inverse p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERSE_UNIQUE_o THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP PERMUTATION_INVERSE_WORKS)) THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [o_ASSOC] THEN
  ASM_REWRITE_TAC[I_O_ID]);;

let PERMUTATION_COMPOSE_EQ = prove
 (`(!p q:A->A. permutation(p) ==> (permutation(p o q) <=> permutation q)) /\
   (!p q:A->A. permutation(q) ==> (permutation(p o q) <=> permutation p))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PERMUTATION_INVERSE) THEN
  EQ_TAC THEN ASM_SIMP_TAC[PERMUTATION_COMPOSE] THENL
   [DISCH_THEN(MP_TAC o SPEC `inverse(p:A->A)` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] PERMUTATION_COMPOSE));
    DISCH_THEN(MP_TAC o SPEC `inverse(q:A->A)` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] PERMUTATION_COMPOSE))] THEN
  ASM_SIMP_TAC[GSYM o_ASSOC; PERMUTATION_INVERSE_WORKS] THEN
  ASM_SIMP_TAC[o_ASSOC; PERMUTATION_INVERSE_WORKS] THEN
  REWRITE_TAC[I_O_ID]);;

let PERMUTATION_COMPOSE_SWAP = prove
 (`(!p a b:A. permutation(swap(a,b) o p) <=> permutation p) /\
   (!p a b:A. permutation(p o swap(a,b)) <=> permutation p)`,
  SIMP_TAC[PERMUTATION_COMPOSE_EQ; PERMUTATION_SWAP]);;

(* ------------------------------------------------------------------------- *)
(* Relation to "permutes".                                                   *)
(* ------------------------------------------------------------------------- *)

let PERMUTATION_PERMUTES = prove
 (`!p:A->A. permutation p <=> ?s. FINITE s /\ p permutes s`,
  GEN_TAC THEN REWRITE_TAC[PERMUTATION; permutes] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `{x:A | ~(p x = x)}` THEN ASM_SIMP_TAC[IN_ELIM_THM];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; SUBSET] THEN ASM_MESON_TAC[]]);;

let PERMUTATION_RESTRICT = prove
 (`!Q (p:A->A).
        permutation p /\ (!x. Q(p x) <=> Q x)
        ==> permutation (\i. if Q i then p i else i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
  REWRITE_TAC[PERMUTATION_PERMUTES] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[PERMUTES_RESTRICT]);;

(* ------------------------------------------------------------------------- *)
(* Hence a sort of induction principle composing by swaps.                   *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_INDUCT = prove
 (`!P s. FINITE s /\
         P I /\
         (!a b:A p. a IN s /\ b IN s /\ P p /\ permutation p
                    ==> P (swap(a,b) o p))
         ==> (!p. p permutes s ==> P p)`,
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b ==> a ==> c ==> d`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_REWRITE_TAC[PERMUTES_EMPTY; IN_INSERT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p = swap(x,p x) o swap(x,p x) o (p:A->A)` SUBST1_TAC THENL
   [REWRITE_TAC[o_ASSOC; SWAP_IDEMPOTENT; I_O_ID]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN ASSUME_TAC th) THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_INSERT; PERMUTES_INSERT_LEMMA;
                PERMUTATION_PERMUTES; FINITE_INSERT; PERMUTATION_COMPOSE;
                PERMUTATION_SWAP]);;

let PERMUTES_INDUCT_STRONG = prove
 (`!P s:A->bool.
        FINITE s /\
        P I /\
        (!a b p. a IN s /\ b IN s /\ ~(a = b) /\ P p /\ p permutes s
                 ==> P (swap(a,b) o p))
        ==> !p. p permutes s ==> P p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q <=> p ==> p /\ q`] THEN
  MATCH_MP_TAC PERMUTES_INDUCT THEN
  ASM_SIMP_TAC[PERMUTES_I; PERMUTES_COMPOSE; PERMUTES_SWAP] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN
  ASM_CASES_TAC `a:A = b` THEN ASM_SIMP_TAC[SWAP_REFL; I_O_ID]);;

(* ------------------------------------------------------------------------- *)
(* Sign of a permutation as a real number.                                   *)
(* ------------------------------------------------------------------------- *)

let sign = new_definition
 `(sign p):real = if evenperm p then &1 else -- &1`;;

let SIGN_NZ = prove
 (`!p. ~(sign p = &0)`,
  REWRITE_TAC[sign] THEN REAL_ARITH_TAC);;

let SIGN_I = prove
 (`sign I = &1`,
  REWRITE_TAC[sign; EVENPERM_I]);;

let SIGN_ID = prove
 (`sign(\x:A. x) = &1`,
  REWRITE_TAC[sign; EVENPERM_ID]);;

let SIGN_INVERSE = prove
 (`!p. permutation p ==> sign(inverse p) = sign p`,
  SIMP_TAC[sign; EVENPERM_INVERSE] THEN REAL_ARITH_TAC);;

let SIGN_COMPOSE = prove
 (`!p q. permutation p /\ permutation q ==> sign(p o q) = sign(p) * sign(q)`,
  SIMP_TAC[sign; EVENPERM_COMPOSE] THEN REAL_ARITH_TAC);;

let SIGN_SWAP = prove
 (`!a b. sign(swap(a,b)) = if a = b then &1 else -- &1`,
  REWRITE_TAC[sign; EVENPERM_SWAP]);;

let SIGN_IDEMPOTENT = prove
 (`!p. sign(p) * sign(p) = &1`,
  GEN_TAC THEN REWRITE_TAC[sign] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let REAL_ABS_SIGN = prove
 (`!p. abs(sign p) = &1`,
  REWRITE_TAC[sign] THEN REAL_ARITH_TAC);;

let REAL_SGN_SIGN = prove
 (`!p:A->A. real_sgn(sign p) = sign p`,
  GEN_TAC THEN REWRITE_TAC[sign] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_SGN_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let EVENPERM_TRANSFER = prove
 (`!(f:A->B) s p q.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        p permutes s /\
        (!x. x IN s ==> q(f x) = f(p x)) /\
        (!y. ~(y IN IMAGE f s) ==> q y = y)
        ==> (evenperm q <=> evenperm p)`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  SUBGOAL_THEN
   `!p q. (!x. x IN s ==> q (f x) = f (p x)) /\
          (!y. ~(y IN IMAGE f s) ==> q y = y) <=>
          q = \x. if x IN IMAGE f s then (f:A->B) (p(g x)) else x`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM SET_TAC[];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2]] THEN
  MATCH_MP_TAC PERMUTES_INDUCT_STRONG THEN
  ASM_REWRITE_TAC[I_THM; o_THM] THEN
  SUBGOAL_THEN
   `(\x. if x IN IMAGE (f:A->B) s then f (g x) else x) = I`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; I_THM] THEN ASM SET_TAC[];
    REWRITE_TAC[EVENPERM_I]] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`; `p:A->A`] THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EVENPERM_COMPOSE o rand o snd) THEN
  REWRITE_TAC[PERMUTATION_SWAP] THEN REWRITE_TAC[PERMUTATION_PERMUTES] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `evenperm(swap(a,b)) = evenperm(swap((f:A->B) a,f b))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EVENPERM_SWAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) EVENPERM_COMPOSE o rand o snd) THEN
  REWRITE_TAC[PERMUTATION_SWAP] THEN ANTS_TAC THENL
   [REWRITE_TAC[PERMUTATION_PERMUTES] THEN
    EXISTS_TAC `IMAGE (f:A->B) s` THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    MATCH_MP_TAC PERMUTES_TRANSFER THEN EXISTS_TAC `p:A->A` THEN
    ASM SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; o_DEF; swap] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PERMUTES_ALT]) THEN
  X_GEN_TAC `y:B` THEN REWRITE_TAC[IN_IMAGE] THEN
  ASM_CASES_TAC `?x. y = (f:A->B) x /\ x IN s` THEN
  ASM_REWRITE_TAC[] THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x:A`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

let SIGN_TRANSFER = prove
 (`!(f:A->B) s p q.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        p permutes s /\
        (!x. x IN s ==> q(f x) = f(p x)) /\
        (!y. ~(y IN IMAGE f s) ==> q y = y)
        ==> sign q = sign p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sign] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP EVENPERM_TRANSFER) THEN
  REWRITE_TAC[]);;

let SIGN_CARTESIAN_PRODUCT = prove
 (`!(p:A->A) (q:B->B) s t.
        FINITE s /\ FINITE t /\ p permutes s /\ q permutes t
        ==> sign (\(i,j). if i IN s /\ j IN t then p i,q j else i,j) =
            sign p pow CARD t * sign q pow CARD s`,

  let lemma1 = prove
   (`!p (s:A->bool) (t:B->bool).
          p permutes s /\ FINITE s /\ FINITE t
          ==> sign (\(i,j). if i IN s /\ j IN t then p i,j else i,j) =
              sign p pow CARD t`,
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [REWRITE_TAC[CARD_CLAUSES; NOT_IN_EMPTY] THEN
      REWRITE_TAC[GSYM LAMBDA_PAIR_THM; SIGN_ID; real_pow];
      MAP_EVERY X_GEN_TAC [`b:B`; `t:B->bool`] THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `(\(i:A,j:B). if i IN s /\ j IN b INSERT t then p i,j else i,j) =
      (\(i,j). if i IN s /\ j IN {b} then p i,j else i,j) o
      (\(i,j). if i IN s /\ j IN t then p i,j else i,j)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN
      MAP_EVERY X_GEN_TAC [`i:A`; `j:B`] THEN
      ASM_CASES_TAC `(i:A) IN s` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
      ASM_CASES_TAC `j:B = b` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
      ASM_CASES_TAC `(j:B) IN t` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SIGN_COMPOSE o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PERMUTATION_PERMUTES] THEN CONJ_TAC THENL
       [EXISTS_TAC `(s:A->bool) CROSS {b:B}`;
        EXISTS_TAC `(s:A->bool) CROSS (t:B->bool)`] THEN
      ASM_REWRITE_TAC[FINITE_CROSS_EQ; FINITE_SING] THEN
      MATCH_MP_TAC PERMUTES_CARTESIAN_PRODUCT THEN
      ASM_REWRITE_TAC[PERMUTES_ID];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; real_pow; IN_SING] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SIGN_TRANSFER THEN
    EXISTS_TAC `\x:A. x,(b:B)` THEN EXISTS_TAC `s:A->bool` THEN
    ASM_SIMP_TAC[PAIR_EQ; IN_IMAGE; FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[]) in
  let lemma2 = prove
   (`!p (s:A->bool) (t:B->bool).
          FINITE s /\ p permutes t /\ FINITE t
          ==> sign (\(i:A,j:B). if i IN s /\ j IN t then i,p j else i,j) =
              sign p pow CARD s`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p:B->B`; `t:B->bool`; `s:A->bool`]
      lemma1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SIGN_TRANSFER THEN
    EXISTS_TAC `\(i:B,j:A). j,i` THEN
    EXISTS_TAC `(t:B->bool) CROSS (s:A->bool)` THEN
    ASM_REWRITE_TAC[FINITE_CROSS_EQ; FORALL_PAIR_THM; IN_CROSS] THEN
    SIMP_TAC[PAIR_EQ; IN_IMAGE; IN_CROSS; EXISTS_PAIR_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC PERMUTES_CARTESIAN_PRODUCT THEN
    ASM_REWRITE_TAC[PERMUTES_ID]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\(i,j). if i IN s /\ j IN t then (p:A->A) i,(q:B->B) j else i,j) =
    (\(i,j). if i IN s /\ j IN t then p i,j else i,j) o
    (\(i,j). if i IN s /\ j IN t then i,q j else i,j)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN REPEAT GEN_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PERMUTES_ALT]) THEN ASM SET_TAC[];
    W(MP_TAC o PART_MATCH (lhand o rand) SIGN_COMPOSE o lhand o snd)] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PERMUTATION_PERMUTES] THEN CONJ_TAC THEN
    EXISTS_TAC `(s:A->bool) CROSS (t:B->bool)` THEN
    ASM_SIMP_TAC[FINITE_CROSS_EQ; PERMUTES_CARTESIAN_PRODUCT; PERMUTES_ID];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[lemma1; lemma2]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas about permutations.                                           *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_NUMSET_LE = prove
 (`!p s:num->bool. p permutes s /\ (!i. i IN s ==> p(i) <= i) ==> p = I`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; I_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(n:num) IN s` THENL [ALL_TAC; ASM_MESON_TAC[permutes]] THEN
  ASM_SIMP_TAC[GSYM LE_ANTISYM] THEN REWRITE_TAC[GSYM NOT_LT] THEN
  ASM_MESON_TAC[PERMUTES_INJECTIVE; LT_REFL]);;

let PERMUTES_NUMSET_GE = prove
 (`!p s:num->bool. p permutes s /\ (!i. i IN s ==> i <= p(i)) ==> p = I`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`inverse(p:num->num)`; `s:num->bool`] PERMUTES_NUMSET_LE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[PERMUTES_INVERSE; PERMUTES_INVERSES; PERMUTES_IN_IMAGE];
    ASM_MESON_TAC[PERMUTES_INVERSE_INVERSE; INVERSE_I]]);;

let IMAGE_INVERSE_PERMUTATIONS = prove
 (`!s:A->bool. {inverse p | p permutes s} = {p | p permutes s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[PERMUTES_INVERSE_INVERSE; PERMUTES_INVERSE]);;

let IMAGE_COMPOSE_PERMUTATIONS_L = prove
 (`!s q:A->A. q permutes s ==> {q o p | p permutes s} = {p | p permutes s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `p:A->A` THEN EQ_TAC THENL
   [ASM_MESON_TAC[PERMUTES_COMPOSE];
    DISCH_TAC THEN EXISTS_TAC `inverse(q:A->A) o (p:A->A)` THEN
    ASM_SIMP_TAC[o_ASSOC; PERMUTES_INVERSE; PERMUTES_COMPOSE] THEN
    ASM_MESON_TAC[PERMUTES_INVERSES_o; I_O_ID]]);;

let IMAGE_COMPOSE_PERMUTATIONS_R = prove
 (`!s q:A->A. q permutes s ==> {p o q | p permutes s} = {p | p permutes s}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `p:A->A` THEN EQ_TAC THENL
   [ASM_MESON_TAC[PERMUTES_COMPOSE];
    DISCH_TAC THEN EXISTS_TAC `(p:A->A) o inverse(q:A->A)` THEN
    ASM_SIMP_TAC[GSYM o_ASSOC; PERMUTES_INVERSE; PERMUTES_COMPOSE] THEN
    ASM_MESON_TAC[PERMUTES_INVERSES_o; I_O_ID]]);;

let PERMUTES_IN_NUMSEG = prove
 (`!p n i. p permutes 1..n /\ i IN 1..n ==> 1 <= p(i) /\ p(i) <= n`,
  REWRITE_TAC[permutes; IN_NUMSEG] THEN MESON_TAC[]);;

let SUM_PERMUTATIONS_INVERSE = prove
 (`!f m n. sum {p | p permutes m..n} f =
           sum {p | p permutes m..n} (\p. f(inverse p))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM IMAGE_INVERSE_PERMUTATIONS] THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [SET_RULE `{f x | p x} = IMAGE f {x | p x}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; IN_ELIM_THM] THEN
  MESON_TAC[PERMUTES_INVERSE_INVERSE]);;

let SUM_PERMUTATIONS_COMPOSE_L = prove
 (`!f m n q.
        q permutes m..n
        ==> sum {p | p permutes m..n} f =
            sum {p | p permutes m..n} (\p. f(q o p))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_L th)]) THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [SET_RULE `{f x | p x} = IMAGE f {x | p x}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\p:num->num. inverse(q:num->num) o p`) THEN
  REWRITE_TAC[o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_O_ID]);;

let SUM_PERMUTATIONS_COMPOSE_R = prove
 (`!f m n q.
        q permutes m..n
        ==> sum {p | p permutes m..n} f =
            sum {p | p permutes m..n} (\p. f(p o q))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [GSYM(MATCH_MP IMAGE_COMPOSE_PERMUTATIONS_R th)]) THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV)
   [SET_RULE `{f x | p x} = IMAGE f {x | p x}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MATCH_MP_TAC SUM_IMAGE THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\p:num->num. p o inverse(q:num->num)`) THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  EVERY_ASSUM(CONJUNCTS_THEN SUBST1_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
  REWRITE_TAC[I_O_ID]);;

let CARD_EVEN_PERMUTATIONS = prove
 (`!s:A->bool. FINITE s /\ 2 <= CARD s
               ==> 2 * CARD {p | p permutes s /\ evenperm p} = FACT(CARD s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a b:A. a IN s /\ b IN s /\ ~(a = b)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`2`; `s:A->bool`] CHOOSE_SUBSET_STRONG) THEN
    ASM_REWRITE_TAC[HAS_SIZE_CONV `s HAS_SIZE 2`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:A->A. p permutes s ==> permutation p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTATION_PERMUTES]; ALL_TAC] THEN
  SUBGOAL_THEN `!Q. FINITE {p:A->A | p permutes s /\ Q p}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{p | p permutes s /\ Q p} =
                            {p | p IN {p | p permutes s} /\ Q p}`] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_PERMUTATIONS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FACT(CARD s) = CARD ({p | p permutes s /\ evenperm p} UNION
                         IMAGE (\p. swap(a:A,b) o p)
                               {p | p permutes s /\ evenperm p})`
  SUBST1_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CARD_PERMUTATIONS) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> P(f x)) /\ (!x. f(f x) = x) /\
      (!x. P x ==> Q x \/ Q(f x))
      ==> {x | P x} = {x | P x /\ Q x} UNION IMAGE f {x | P x /\ Q x}`) THEN
    ASM_SIMP_TAC[PERMUTES_COMPOSE; PERMUTES_SWAP; SWAP_IDEMPOTENT; o_ASSOC;
      I_O_ID; EVENPERM_COMPOSE; PERMUTATION_SWAP; EVENPERM_SWAP] THEN
    CONV_TAC TAUT;
    W(MP_TAC o PART_MATCH (lhs o rand) CARD_UNION o rand o snd) THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN ANTS_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. P x ==> ~P(f x)) ==> {x | P x} INTER IMAGE f {x | P x} = {}`) THEN
      ASM_SIMP_TAC[IN_ELIM_THM; EVENPERM_COMPOSE; PERMUTATION_SWAP] THEN
      ASM_REWRITE_TAC[EVENPERM_SWAP];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `b = a ==> 2 * a = a + b`) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(MESON[]
     `(!x. f(f x) = x) ==> (!x y. P x /\ P y /\ f x = f y ==> x = y)`) THEN
    ASM_SIMP_TAC[SWAP_IDEMPOTENT; o_ASSOC; I_O_ID]]);;

(* ------------------------------------------------------------------------- *)
(* The special case of involutions.                                          *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_INVOLUTION = prove
 (`!p s:A->bool. (!x. p(p x) = x) /\ (!x. ~(x IN s) ==> p x = x)
                 ==> p permutes s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `p:A->A` THEN ASM_MESON_TAC[]);;

let SIGN_INVOLUTION = prove
 (`!p:A->A s. FINITE s /\ (!x. p(p x) = x) /\ (!x. ~(x IN s) ==> p x = x)
              ==> sign p = --(&1) pow (CARD {x | ~(p x = x)} DIV 2)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  WF_INDUCT_TAC `CARD(s:A->bool)` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `p:A->A = I` THEN
  ASM_SIMP_TAC[I_THM; EMPTY_GSPEC; CARD_CLAUSES; SIGN_I; DIV_0; real_pow;
               ARITH_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; I_THM; NOT_FORALL_THM] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:A) IN s /\ p a IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:A) DELETE (p a)`) THEN
  ASM_SIMP_TAC[CARD_DELETE; FINITE_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[CARD_EQ_0; ARITH_RULE `n - 1 - 1 < n <=> ~(n = 0)`] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `permutation(p:A->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTATION_PERMUTES; PERMUTES_INVOLUTION]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `p o swap(a:A,p a)`) THEN
  ASM_SIMP_TAC[SIGN_COMPOSE; PERMUTATION_SWAP; SIGN_SWAP] THEN
  REWRITE_TAC[o_THM; swap] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_RING `-- &1 * a:real = b ==> s * -- &1 = a ==> s = b`) THEN
  SUBGOAL_THEN
   `{x | ~(p (if x = a then p a else if x = p a then a else x) = x)} =
    {x:A | ~(p x = x)} DELETE a DELETE (p a)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {x:A | ~(p x = x)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[CARD_DELETE; IN_ELIM_THM; FINITE_DELETE; IN_DELETE]] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `m + 2 = n ==> SUC(m DIV 2) = n DIV 2`) THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= n ==> n - 1 - 1 + 2 = n`) THEN
  TRANS_TAC LE_TRANS `CARD {a:A,p a}` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; IN_SING; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC CARD_SUBSET THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Cyclic permutations realized via modular addition.                        *)
(* ------------------------------------------------------------------------- *)

let PERMUTES_CYCLIC = prove
 (`!n. (\i. if i < n then (i + 1) MOD n else i) permutes {i | i < n}`,
  GEN_TAC THEN SIMP_TAC[PERMUTES_FINITE_INJECTIVE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IMP_CONJ; IN_ELIM_THM] THEN SIMP_TAC[] THEN
  SIMP_TAC[MOD_CASES; ARITH_RULE `x < n ==> x + 1 < 2 * n`] THEN ARITH_TAC);;

let PERMUTES_CYCLIC_N = prove
 (`!n k. (\i. if i < n then (i + k) MOD n else i) permutes {i | i < n}`,
  GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[ADD_CLAUSES; MOD_LT; COND_ID; PERMUTES_ID] THEN
  SUBGOAL_THEN
   `(\i. if i < n then SUC(i + k) MOD n else i) =
    (\i. if i < n then (i + 1) MOD n else i) o
    (\i. if i < n then (i + k) MOD n else i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[CONJUNCT1 LT] THEN
    ASM_CASES_TAC `m:num < n` THEN ASM_REWRITE_TAC[MOD_LT_EQ] THEN
    REWRITE_TAC[ADD1] THEN MESON_TAC[MOD_ADD_MOD; MOD_MOD_REFL];
    MATCH_MP_TAC PERMUTES_COMPOSE THEN
    ASM_REWRITE_TAC[PERMUTES_CYCLIC]]);;

let PERMUTATION_CYCLIC = prove
 (`!n. permutation (\i. if i < n then (i + 1) MOD n else i)`,
  GEN_TAC THEN REWRITE_TAC[PERMUTATION_PERMUTES] THEN
  EXISTS_TAC `{i:num | i < n}` THEN
  ASM_REWRITE_TAC[PERMUTES_CYCLIC; FINITE_NUMSEG_LT]);;

let PERMUTATION_CYCLIC_N = prove
 (`!n k. permutation (\i. if i < n then (i + k) MOD n else i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PERMUTATION_PERMUTES] THEN
  EXISTS_TAC `{i:num | i < n}` THEN
  ASM_REWRITE_TAC[PERMUTES_CYCLIC_N; FINITE_NUMSEG_LT]);;

let EVENPERM_CYCLIC = prove
 (`!n. evenperm(\i. if i < n then (i + 1) MOD n else i) <=> n = 0 \/ ODD n`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT; EVENPERM_ID; ODD] THEN
  REWRITE_TAC[NOT_SUC] THEN
  SUBGOAL_THEN
   `(\i. if i < SUC n then (i + 1) MOD SUC n else i) =
    (swap(0,n)) o (\i. if i <  n then (i + 1) MOD n else i)`
  SUBST1_TAC THENL
   [SIMP_TAC[MOD_CASES; ARITH_RULE `x < n ==> x + 1 < 2 * n`] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; swap] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[ARITH_RULE `m + 1 < SUC n <=> m < n`] THEN
    X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `m + 1 < n` THEN
    ASM_SIMP_TAC[ARITH_RULE `m + 1 < n ==> m < n /\ m < SUC n`] THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `m:num < n` THEN
    ASM_SIMP_TAC[ARITH_RULE `m < n ==> m < SUC n`] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[EVENPERM_COMPOSE; PERMUTATION_SWAP; PERMUTATION_CYCLIC] THEN
    REWRITE_TAC[EVENPERM_SWAP] THEN
    MESON_TAC[ODD]]);;

let EVENPERM_CYCLIC_N = prove
 (`!n k. evenperm(\i. if i < n then (i + k) MOD n else i) <=>
         n = 0 \/ ODD n \/ EVEN k`,
  GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[ADD_CLAUSES; MOD_LT; COND_ID; EVENPERM_ID; ARITH] THEN
  SUBGOAL_THEN
   `(\i. if i < n then SUC(i + k) MOD n else i) =
    (\i. if i < n then (i + 1) MOD n else i) o
    (\i. if i < n then (i + k) MOD n else i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[CONJUNCT1 LT] THEN
    ASM_CASES_TAC `m:num < n` THEN ASM_REWRITE_TAC[MOD_LT_EQ] THEN
    REWRITE_TAC[ADD1] THEN MESON_TAC[MOD_ADD_MOD; MOD_MOD_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EVENPERM_COMPOSE; PERMUTATION_CYCLIC_N] THEN
  REWRITE_TAC[EVENPERM_CYCLIC; EVEN; NOT_EVEN] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[NOT_EVEN]);;

let SIGN_CYCLIC = prove
 (`!n. sign(\i. if i < n then (i + 1) MOD n else i) = --(&1) pow (n - 1)`,
  GEN_TAC THEN REWRITE_TAC[sign; EVENPERM_CYCLIC] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE; EVEN_SUB; ARITH; NOT_EVEN] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[LE_REFL; ARITH] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 1 \/ n = 0`]);;

let SIGN_CYCLIC_N = prove
 (`!n k. sign(\i. if i < n then (i + k) MOD n else i) =
         --(&1) pow (k * (n - 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sign; EVENPERM_CYCLIC_N] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE; EVEN_MULT;
              EVEN_SUB; ARITH; NOT_EVEN] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[LE_REFL; ARITH] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 1 \/ n = 0`] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Conversion for `{p | p permutes s}` where s is a set enumeration.         *)
(* ------------------------------------------------------------------------- *)

let PERMSET_CONV =
  let pth_empty = prove
   (`{p | p permutes {}} = {I}`,
    REWRITE_TAC[PERMUTES_EMPTY] THEN SET_TAC[])
  and pth_cross = SET_RULE
    `IMAGE f {x,y | x IN {} /\ y IN t} = {} /\
     IMAGE f {x,y | x IN (a INSERT s) /\ y IN t} =
     (IMAGE (\y. f(a,y)) t) UNION (IMAGE f {x,y | x IN s /\ y IN t})`
  and pth_union = SET_RULE
    `{} UNION t = t /\
     (x INSERT s) UNION t = x INSERT (s UNION t)` in
  let rec PERMSET_CONV tm =
   (GEN_REWRITE_CONV I [pth_empty] ORELSEC
    (GEN_REWRITE_CONV I [PERMUTES_INSERT] THENC
     ONCE_DEPTH_CONV PERMSET_CONV THENC
     REWRITE_CONV[pth_cross] THENC
     REWRITE_CONV[IMAGE_CLAUSES] THENC
     REWRITE_CONV[pth_union] THENC
    REWRITE_CONV[SWAP_REFL; I_O_ID])) tm in
  PERMSET_CONV;;

(* ------------------------------------------------------------------------- *)
(* Sum over a set of permutations (could generalize to iteration).           *)
(* ------------------------------------------------------------------------- *)

let SUM_OVER_PERMUTATIONS_INSERT = prove
 (`!f a s. FINITE s /\ ~(a IN s)
           ==> sum {p:A->A | p permutes (a INSERT s)} f =
               sum (a INSERT s)
                   (\b. sum {p | p permutes s} (\q. f(swap(a,b) o q)))`,
  let lemma = prove
   (`(\(b,p). f (swap (a,b) o p)) = f o (\(b,p). swap(a,b) o p)`,
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[PERMUTES_INSERT] THEN
  ASM_SIMP_TAC[FINITE_PERMUTATIONS; FINITE_INSERT; SUM_SUM_PRODUCT] THEN
  REWRITE_TAC[lemma] THEN MATCH_MP_TAC SUM_IMAGE THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `p:A->A`; `c:A`; `q:A->A`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C AP_THM `a:A`) THEN
    REWRITE_TAC[o_THM; swap] THEN ASM_MESON_TAC[permutes];
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `(\p:A->A. swap(a:A,c) o p)`) THEN
    REWRITE_TAC[o_ASSOC; SWAP_IDEMPOTENT; I_O_ID]]);;

let SUM_OVER_PERMUTATIONS_NUMSEG = prove
 (`!f m n. m <= n
           ==> sum {p | p permutes (m..n)} f =
               sum(m..n) (\i. sum {p | p permutes (m+1..n)}
                                  (\q. f(swap(m,i) o q)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM NUMSEG_LREC] THEN
  MATCH_MP_TAC SUM_OVER_PERMUTATIONS_INSERT THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ARITH_TAC);;
