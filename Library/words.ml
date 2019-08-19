(* ========================================================================= *)
(*          Theory of machine words using finite indexing types.             *)
(*                                                                           *)
(* Introduces a type `:N word` of N-bit words (N being a type of size N).    *)
(* Note that this builds in a priori the assumption the wordsize is nonzero. *)
(* Some abbreviations like `:byte` = `8 word` are often used for brevity.    *)
(*                                                                           *)
(* Mappings `val:N word->num` and `word:num->N word` for unsigned values,    *)
(* and similar 2s-complement `ival:N word->int` and `iword:int->word`, cast  *)
(* (reducing modulo word in one direction) between words and numbers.        *)
(* The `bit` function gives a specific bit as a Boolean.                     *)
(*                                                                           *)
(* The usual operations are provided like `word_add`, `word_xor`; currently  *)
(* for explicitness we don't overload the usual operators. Some have signed  *)
(* and unsigned variants (e.g. `word_ushr` is unsigned/logical shift right,  *)
(* while `word_ishr` is signed/arithmetical shift right).                    *)
(*                                                                           *)
(* Some simple decision procedures for proving basic equalities are here too *)
(* and have limited and somewhat complementary scopes:                       *)
(*  - WORD_RULE for simple algebraic properties                              *)
(*  - WORD_BITWISE_RULE for bitwise-type properties of logical operations    *)
(*  - WORD_ARITH for things involving numerical values                       *)
(* ========================================================================= *)

let HAS_SIZE_8 = HAS_SIZE_DIMINDEX_RULE `:8`;;
let HAS_SIZE_16 = HAS_SIZE_DIMINDEX_RULE `:16`;;
let HAS_SIZE_32 = HAS_SIZE_DIMINDEX_RULE `:32`;;
let HAS_SIZE_64 = HAS_SIZE_DIMINDEX_RULE `:64`;;
let HAS_SIZE_128 = HAS_SIZE_DIMINDEX_RULE `:128`;;
let HAS_SIZE_256 = HAS_SIZE_DIMINDEX_RULE `:256`;;
let HAS_SIZE_512 = HAS_SIZE_DIMINDEX_RULE `:512`;;

let DIMINDEX_8 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_8;;
let DIMINDEX_16 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_16;;
let DIMINDEX_32 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_32;;
let DIMINDEX_64 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_64;;
let DIMINDEX_128 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_128;;
let DIMINDEX_256 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_256;;
let DIMINDEX_512 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_512;;

(* ------------------------------------------------------------------------- *)
(* Pre-cache some sizes to speed up computation (only affects efficiency).   *)
(* ------------------------------------------------------------------------- *)

let word_sizes = ref ([]:thm list);;
let word_pow2sizes = ref ([]:thm list);;

let word_SIZE_CONV = ref NO_CONV;;
let word_POW2SIZE_CONV = ref NO_CONV;;

let add_word_sizes =
  let ptm = `(EXP) 2` in
  let sumconv = GEN_REWRITE_CONV I [DIMINDEX_FINITE_SUM] in
  let rec conv tm =
    ((sumconv THENC BINOP_CONV conv THENC NUM_ADD_CONV) ORELSEC
     DIMINDEX_CONV) tm in
  let conv2 tm =
    match tm with
      Comb(t,d) when t = ptm -> (RAND_CONV conv THENC NUM_EXP_CONV) tm
    | _ -> failwith "conv2" in
  let _ = (word_SIZE_CONV := conv; word_POW2SIZE_CONV := conv2) in
  fun l -> let m = !word_sizes
           and m2 = !word_pow2sizes
           and l2 = map (CONV_RULE(RAND_CONV NUM_EXP_CONV) o AP_TERM ptm) l in
           if subset l m then () else
           (word_sizes := union l m;
            word_pow2sizes := union l2 m2;
            word_SIZE_CONV :=
             (GEN_REWRITE_CONV I (!word_sizes) ORELSEC conv);
            word_POW2SIZE_CONV :=
             (GEN_REWRITE_CONV I (!word_pow2sizes) ORELSEC conv2));;

add_word_sizes [DIMINDEX_1; DIMINDEX_2; DIMINDEX_3; DIMINDEX_4];;

add_word_sizes [DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64];;

add_word_sizes [DIMINDEX_128; DIMINDEX_256; DIMINDEX_512];;

(* ------------------------------------------------------------------------- *)
(* Pushing and pulling to combine nested MOD or rem terms.                   *)
(* ------------------------------------------------------------------------- *)

let MOD_DOWN_CONV =
  let MOD_SUC_MOD = METIS[ADD1; MOD_ADD_MOD; MOD_MOD_REFL]
   `(SUC(m MOD n)) MOD n = SUC m MOD n` in
  let addmul_conv = GEN_REWRITE_CONV I
    [GSYM MOD_SUC_MOD; GSYM MOD_ADD_MOD; GSYM MOD_MULT_MOD2; GSYM MOD_EXP_MOD]
  and mod_conv = GEN_REWRITE_CONV I [MOD_MOD_REFL] in
  let rec downconv tm =
   ((addmul_conv THENC LAND_CONV downconv) ORELSEC
    (mod_conv THENC downconv) ORELSEC
    SUB_CONV downconv) tm
  and upconv =
    GEN_REWRITE_CONV DEPTH_CONV
     [MOD_SUC_MOD; MOD_ADD_MOD; MOD_MULT_MOD2; MOD_EXP_MOD; MOD_MOD_REFL] in
  downconv THENC upconv;;

let INT_REM_DOWN_CONV =
  let addmul_conv = GEN_REWRITE_CONV I
    [GSYM INT_NEG_REM; GSYM INT_ADD_REM; GSYM INT_SUB_REM;
     GSYM INT_MUL_REM; GSYM INT_POW_REM]
  and mod_conv = GEN_REWRITE_CONV I [INT_REM_REM] in
  let rec downconv tm =
   ((addmul_conv THENC LAND_CONV downconv) ORELSEC
    (mod_conv THENC downconv) ORELSEC
    SUB_CONV downconv) tm
  and upconv =
    GEN_REWRITE_CONV DEPTH_CONV
     [INT_NEG_REM; INT_ADD_REM; INT_SUB_REM; INT_MUL_REM;
      INT_POW_REM; INT_REM_REM] in
  downconv THENC upconv;;

(* ------------------------------------------------------------------------- *)
(* Some generic lemmas about digit sums.                                     *)
(* ------------------------------------------------------------------------- *)

let DIGITSUM_WORKS_GEN = prove
 (`!B n k.
    nsum {i | i < k} (\i. B EXP i * n DIV (B EXP i) MOD B) = n MOD (B EXP k)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; NSUM_CLAUSES; MOD_1; EXP; FINITE_NUMSEG_LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; LT_REFL] THEN
  MESON_TAC[MOD_MULT_MOD; MULT_SYM]);;

let DIGITSUM_WORKS = prove
 (`!B n k.
        n < B EXP k
        ==> nsum {i | i < k} (\i. B EXP i * n DIV (B EXP i) MOD B) = n`,
  SIMP_TAC[DIGITSUM_WORKS_GEN; MOD_LT]);;

let DIGITSUM_BOUND = prove
 (`!B b k. (!i. i < k ==> b i < B)
           ==> nsum {i | i < k} (\i. B EXP i * b i) < B EXP k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; ARITH] THEN
  REWRITE_TAC[LT] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE
   `s < e /\ e * (x + 1) <= e * b ==> s + e * x < b * e`) THEN
  ASM_SIMP_TAC[LE_MULT_LCANCEL; ARITH_RULE `b + 1 <= c <=> b < c`]);;

let DIGITSUM_SPLIT = prove
 (`!B b s n.
        FINITE s
        ==> B EXP n * nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i) +
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i) =
            nsum s (\i. B EXP i * b i)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL; MULT_ASSOC; GSYM EXP_ADD] THEN
  SIMP_TAC[ARITH_RULE `n:num <= i ==> n + i - n = i`] THEN
  MATCH_MP_TAC NSUM_UNION_EQ THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  SET_TAC[]);;

let DIGITSUM_DIV,DIGITSUM_MOD = (CONJ_PAIR o prove)
 (`(!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) =
            nsum {i | i IN s /\ n <= i} (\i. B EXP (i - n) * b i)) /\
   (!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) MOD (B EXP n) =
            nsum {i | i IN s /\ i < n} (\i. B EXP i * b i))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `B = 0` THENL
   [ASM_REWRITE_TAC[CONJUNCT1 LT; SET_RULE `(!x. ~(x IN s)) <=> s = {}`] THEN
    SIMP_TAC[EMPTY_GSPEC; NOT_IN_EMPTY; CONJUNCT1 NSUM_CLAUSES] THEN
    REWRITE_TAC[DIV_0; MOD_0];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [MULT_SYM] THEN
    MATCH_MP_TAC(GSYM DIGITSUM_SPLIT) THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[SET_RULE
     `{x | x IN s /\ P x} = {x | x IN {y | P y} /\ x IN s}`] THEN
    REWRITE_TAC[NSUM_RESTRICT_SET; MESON[MULT_CLAUSES]
     `(if p then a * b else 0) = a * (if p then b else 0)`] THEN
    MATCH_MP_TAC DIGITSUM_BOUND THEN ASM_MESON_TAC[LE_1]]);;

let DIGITSUM_MOD_NUMSEG = prove
 (`!B b m n.
        (!i. i < m ==> b i < B)
        ==> nsum {i | i < m} (\i. B EXP i * b i) MOD (B EXP n) =
            nsum {i | i < MIN m n} (\i. B EXP i * b i)`,
  SIMP_TAC[DIGITSUM_MOD; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  REWRITE_TAC[ARITH_RULE `i < MIN m n <=> i < m /\ i < n`]);;

let DIGITSUM_DIV_NUMSEG = prove
 (`!B b m n.
        (!i. i < m ==> b i < B)
        ==> nsum {i | i < m} (\i. B EXP i * b i) DIV (B EXP n) =
            nsum {i | i < m - n} (\i. B EXP i * b(i + n))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIGITSUM_DIV; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `{i:num | i < m /\ n <= i} = IMAGE (\i. i + n) {i | i < m - n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; ARITH_RULE
     `x:num = y + n <=> y = x - n /\ n <= x`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN ARITH_TAC;
    SIMP_TAC[NSUM_IMAGE; EQ_ADD_RCANCEL; o_DEF; ADD_SUB]]);;

let DIGITSUM_DIV_MOD = prove
 (`!B b s n.
        FINITE s /\ (!i. i IN s ==> b i < B)
        ==> nsum s (\i. B EXP i * b i) DIV (B EXP n) MOD B =
            if n IN s then b n else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_MOD] THEN
  REWRITE_TAC[MESON[EXP; MULT_SYM] `B EXP n * B = B EXP SUC n`] THEN
  ASM_SIMP_TAC[DIGITSUM_MOD] THEN
  ASM_SIMP_TAC[DIGITSUM_DIV; FINITE_RESTRICT; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; ARITH_RULE `i < SUC n /\ n <= i <=> i = n`] THEN
  REWRITE_TAC[MESON[] `i IN s /\ i = n <=> n IN s /\ i = n`] THEN
  ASM_CASES_TAC `(n:num) IN s` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; NSUM_CLAUSES] THEN
  REWRITE_TAC[SING_GSPEC; NSUM_SING; SUB_REFL; MULT_CLAUSES; EXP]);;

(* ------------------------------------------------------------------------- *)
(* Mapping a Boolean to the natural number 1 (true) or 0 (false)             *)
(* ------------------------------------------------------------------------- *)

let bitval = new_definition
 `bitval b = if b then 1 else 0`;;

let BITVAL_CLAUSES = prove
 (`bitval F = 0 /\ bitval T = 1`,
  REWRITE_TAC[bitval]);;

let BITVAL_BOUND = prove
 (`!b. bitval b <= 1`,
  REWRITE_TAC[bitval] THEN ARITH_TAC);;

let BITVAL_BOUND_ALT = prove
 (`!b. bitval b < 2`,
  REWRITE_TAC[bitval] THEN ARITH_TAC);;

let BITVAL_EQ_0 = prove
 (`!b. bitval b = 0 <=> ~b`,
  GEN_TAC THEN REWRITE_TAC[bitval] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_EQ_1 = prove
 (`!b. bitval b = 1 <=> b`,
  GEN_TAC THEN REWRITE_TAC[bitval] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_NOT = prove
 (`!b. bitval(~b) = 1 - bitval b`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_AND = prove
 (`!b c. bitval(b /\ c) = bitval b * bitval c`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_OR = prove
 (`!b c. bitval(b \/ c) = (bitval b + bitval c) - bitval b * bitval c`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_IFF = prove
 (`!b c. bitval(b <=> c) =
         (1 + 2 * bitval b * bitval c) - (bitval b + bitval c)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BITVAL_XOR = prove
 (`!b c. bitval(~(b <=> c)) = (bitval b + bitval c) - 2 * bitval b * bitval c`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let INT_BITVAL_NOT = prove
 (`!b. &(bitval(~b)):int = &1 - &(bitval b)`,
  SIMP_TAC[BITVAL_NOT; GSYM INT_OF_NUM_SUB; BITVAL_BOUND]);;

let BITVAL_ODD = prove
 (`!n. bitval(ODD n) = n MOD 2`,
  REWRITE_TAC[bitval; GSYM NOT_EVEN; MOD_2_CASES; COND_SWAP]);;

(* ------------------------------------------------------------------------- *)
(* Some more binary-specific lemmas.                                         *)
(* ------------------------------------------------------------------------- *)

let ODD_MOD_POW2 = prove
 (`!n k. ODD(n MOD 2 EXP k) <=> ~(k = 0) /\ ODD n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[MOD_1; EXP; ODD] THEN
  REWRITE_TAC[MESON[ODD_MOD; EXP_1] `ODD n <=> n MOD (2 EXP 1) = 1`] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> MIN k 1 = 1`]);;

let BINARY_DIGITSUM_BOUND = prove
 (`!b k. nsum {i | i < k} (\i. 2 EXP i * bitval(b i)) < 2 EXP k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIGITSUM_BOUND THEN
  REWRITE_TAC[BITVAL_BOUND_ALT]);;

let BINARY_DIGITSUM_SPLIT = prove
 (`!b s n.
        FINITE s
        ==> 2 EXP n *
            nsum {i | i IN s /\ n <= i} (\i. 2 EXP (i - n) * bitval(b i)) +
            nsum {i | i IN s /\ i < n} (\i. 2 EXP i * bitval(b i)) =
            nsum s (\i. 2 EXP i * bitval(b i))`,
  MATCH_ACCEPT_TAC DIGITSUM_SPLIT);;

let BINARY_DIGITSUM_DIV = prove
 (`!b s n.
        FINITE s
        ==> nsum s (\i. 2 EXP i * bitval(b i)) DIV (2 EXP n) =
            nsum {i | i IN s /\ n <= i} (\i. 2 EXP (i - n) * bitval(b i))`,
  SIMP_TAC[DIGITSUM_DIV; BITVAL_BOUND_ALT]);;

let BINARY_DIGITSUM_MOD = prove
 (`!b s n.
        FINITE s
        ==> nsum s (\i. 2 EXP i * bitval(b i)) MOD (2 EXP n) =
            nsum {i | i IN s /\ i < n} (\i. 2 EXP i * bitval(b i))`,
  SIMP_TAC[DIGITSUM_MOD; BITVAL_BOUND_ALT]);;

(* ------------------------------------------------------------------------- *)
(* The type "N word" is in bijection with "bool^N"                           *)
(* ------------------------------------------------------------------------- *)

let word_tybij =
  let th = prove (`?x:bool^N. T`,REWRITE_TAC[]) in
  REWRITE_RULE[]
   (new_type_definition "word" ("mk_word","bitvector") th);;

let WORD_EQ_BITVECTOR = prove
 (`!v w:N word. v = w <=> bitvector v = bitvector w`,
  MESON_TAC[word_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Set up some specific sizes that we want.                                  *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("nybble",`:(4)word`);;
new_type_abbrev("byte",`:(8)word`);;
new_type_abbrev("int16",`:(16)word`);;
new_type_abbrev("int32",`:(32)word`);;
new_type_abbrev("int64",`:(64)word`);;
new_type_abbrev("int128",`:(128)word`);;

(* ------------------------------------------------------------------------- *)
(* Individual selection of bits, indexing from 0 as usual.                   *)
(* ------------------------------------------------------------------------- *)

let bit = new_definition
 `bit i (w:N word) =
    if i < dimindex(:N) then (bitvector w)$(i + 1)
    else F`;;

let WORD_EQ_BITS_ALT = prove
 (`!v w:N word. v = w <=> !i. i < dimindex(:N) ==> bit i v = bit i w`,
  REPEAT GEN_TAC THEN SIMP_TAC[WORD_EQ_BITVECTOR; bit; CART_EQ] THEN
  MESON_TAC[ARITH_RULE `i < n ==> 1 <= i + 1 /\ i + 1 <= n`;
            ARITH_RULE `1 <= i /\ i <= n ==> i = (i - 1) + 1 /\ i - 1 < n`]);;

let WORD_EQ_BITS = prove
 (`!v w:N word. v = w <=> !i. bit i v = bit i w`,
  MESON_TAC[bit; WORD_EQ_BITS_ALT]);;

let BIT_TRIVIAL = prove
 (`!w:(N)word i. dimindex(:N) <= i ==> (bit i w <=> F)`,
  SIMP_TAC[GSYM NOT_LT; bit]);;

(* ------------------------------------------------------------------------- *)
(* Mappings to and from sets of bits.                                        *)
(* ------------------------------------------------------------------------- *)

let bits_of_word = new_definition
 `bits_of_word (w:N word) = {i | bit i w}`;;

let word_of_bits = new_definition
 `word_of_bits s:N word = mk_word(lambda i. (i - 1) IN s)`;;

let IN_BITS_OF_WORD = prove
 (`!(w:N word) i. i IN bits_of_word w <=> bit i w`,
  REWRITE_TAC[bits_of_word; IN_ELIM_THM]);;

let BIT_WORD_OF_BITS = prove
 (`!s i. bit i (word_of_bits s:N word) <=> i < dimindex(:N) /\ i IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit; word_of_bits] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[word_tybij] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   `i < n ==> 1 <= i + 1 /\ i + 1 <= n`)) THEN
  ASM_SIMP_TAC[LAMBDA_BETA; ADD_SUB]);;

let WORD_OF_BITS_EQ = prove
 (`!s t. word_of_bits s:N word = word_of_bits t <=>
         !i. i < dimindex(:N) ==> (i IN s <=> i IN t)`,
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS] THEN MESON_TAC[]);;

let WORD_OF_BITS_OF_WORD = prove
 (`!w:N word. word_of_bits(bits_of_word w) = w`,
  SIMP_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; bits_of_word; IN_ELIM_THM]);;

let BITS_OF_WORD_OF_BITS = prove
 (`!s. bits_of_word(word_of_bits s:N word) = s INTER {i | i < dimindex(:N)}`,
  GEN_TAC THEN REWRITE_TAC[bits_of_word] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; BIT_WORD_OF_BITS] THEN
  CONV_TAC TAUT);;

let BITS_OF_WORD_EQ = prove
 (`!v w:N word. bits_of_word v = bits_of_word w <=> v = w`,
  MESON_TAC[WORD_OF_BITS_OF_WORD]);;

let WORD_OF_BITS = prove
 (`!w:N word. w = word_of_bits {i | bit i w}`,
  REWRITE_TAC[GSYM bits_of_word; WORD_OF_BITS_OF_WORD]);;

let WORD_OF_BITS_ALT = prove
 (`!w:N word. w = word_of_bits {i | i < dimindex(:N) /\ bit i w}`,
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let FINITE_BITS_OF_WORD = prove
 (`!w:N word. FINITE(bits_of_word w)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i | i < dimindex(:N)}` THEN
  REWRITE_TAC[bits_of_word; FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

(* ------------------------------------------------------------------------- *)
(* Mapping to and from natural number values (treating as unsigned word).    *)
(* ------------------------------------------------------------------------- *)

let val_def = new_definition
 `val (w:N word) =
    nsum {i | i < dimindex(:N)} (\i. 2 EXP i * bitval(bit i w))`;;

let word = new_definition
 `(word:num->N word) n =
    mk_word(lambda i. ODD(n DIV (2 EXP (i - 1))))`;;

let BIT_WORD = prove
 (`!i n. bit i (word n:N word) <=> i < dimindex(:N) /\ ODD(n DIV (2 EXP i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[word; word_tybij] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; ADD_SUB; ARITH_RULE `1 <= i + 1`;
               ARITH_RULE `i < n ==> i + 1 <= n`]);;

let BIT_WORD_0 = prove
 (`!i. bit i (word 0:N word) <=> F`,
  REWRITE_TAC[BIT_WORD; DIV_0; ODD]);;

let BITS_OF_WORD_0 = prove
 (`bits_of_word(word 0:N word) = {}`,
  REWRITE_TAC[bits_of_word; BIT_WORD_0; EMPTY_GSPEC]);;

let BITS_OF_WORD_EQ_EMPTY = prove
 (`!w:N word. bits_of_word w = {} <=> w = word 0`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_0]);;

let BITVAL_BIT_WORD = prove
 (`!i n. bitval(bit i (word n:N word)) =
         if i < dimindex(:N) then (n DIV (2 EXP i)) MOD 2 else 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[BIT_WORD; bitval; ODD_MOD] THEN
  ARITH_TAC);;

let WORD_VAL = prove
 (`!w:N word. word(val w) = w`,
  GEN_TAC THEN SIMP_TAC[WORD_EQ_BITS_ALT; val_def; BIT_WORD] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SIMP_TAC[BINARY_DIGITSUM_DIV; FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; GSYM numseg; ARITH_RULE
   `k < n ==> (i < n /\ k <= i <=> k <= i /\ i <= n - 1)`] THEN
  ASM_SIMP_TAC[NSUM_CLAUSES_LEFT; ARITH_RULE `k < n ==> k <= n - 1`] THEN
  MATCH_MP_TAC(MESON[ODD; ODD_ADD]
   `~ODD n /\ (ODD m <=> p) ==> (ODD(m + n) <=> p)`) THEN
  REWRITE_TAC[SUB_REFL; EXP; NOT_ODD; MULT_CLAUSES] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_CLOSED THEN
    SIMP_TAC[EVEN; EVEN_ADD; EVEN_MULT; EVEN_EXP; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let VAL_WORD = prove
 (`!n. val(word n:N word) = n MOD (2 EXP (dimindex(:N)))`,
  GEN_TAC THEN SIMP_TAC[val_def; BITVAL_BIT_WORD] THEN
  SPEC_TAC(`dimindex(:N)`,`k:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; MOD_1] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_MOD] THEN ARITH_TAC);;

let FORALL_WORD = prove
 (`!P. (!x:N word. P x) <=> (!n. P(word n))`,
  MESON_TAC[WORD_VAL]);;

let EXISTS_WORD = prove
 (`!P. (?x:N word. P x) <=> (?n. P(word n))`,
  MESON_TAC[WORD_VAL]);;

let VAL_WORD_0 = prove
 (`val(word 0:(N)word) = 0`,
  SIMP_TAC[VAL_WORD; MOD_0; EXP_EQ_0; ARITH_EQ]);;

let VAL_WORD_1 = prove
 (`val(word 1:(N)word) = 1`,
  REWRITE_TAC[VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `1 = 2 EXP 0`] THEN
  SIMP_TAC[LT_EXP; LE_1; DIMINDEX_GE_1] THEN ARITH_TAC);;

let VAL_WORD_EQ = prove
 (`!n. n < 2 EXP dimindex(:N) ==> val(word n :(N)word) = n`,
  SIMP_TAC[VAL_WORD; MOD_LT]);;

let VAL_EQ = prove
 (`!(v:N word) (w:N word). val v = val w <=> v = w`,
  MESON_TAC[WORD_VAL]);;

let VAL_EQ_0 = prove
 (`!w:(N)word. val w = 0 <=> w = word 0`,
  MESON_TAC[VAL_WORD_0; VAL_EQ]);;

let VAL_EQ_1 = prove
 (`!w:(N)word. val w = 1 <=> w = word 1`,
  MESON_TAC[VAL_WORD_1; VAL_EQ]);;

let WORD_NE_10 = prove
 (`~(word 1:N word = word 0)`,
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_1] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_EQ = prove
 (`!x y. word x:(N)word = word y <=> (x == y) (mod (2 EXP dimindex(:N)))`,
  MESON_TAC[VAL_WORD; WORD_VAL; CONG]);;

let VAL_BOUND = prove
 (`!w:N word. val w < 2 EXP dimindex(:N)`,
  REWRITE_TAC[val_def; BINARY_DIGITSUM_BOUND]);;

let INT_VAL_BOUND = prove
 (`!w:N word. &(val w):int < &2 pow dimindex(:N)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT; VAL_BOUND]);;

let VAL_MOD_REFL = prove
 (`!x:(N)word. (val x) MOD (2 EXP dimindex(:N)) = val x`,
  MESON_TAC[MOD_LT; VAL_BOUND]);;

let VAL_WORD_EQ_EQ = prove
 (`!n. val(word n:N word) = n <=> n < 2 EXP dimindex(:N)`,
  MESON_TAC[VAL_WORD_EQ; VAL_BOUND]);;

let FORALL_VAL_GEN = prove
 (`!P. (!x:N word. P (val x) x) <=>
       !n. n < 2 EXP dimindex(:N) ==> P n (word n)`,
  MESON_TAC[VAL_WORD_EQ; WORD_VAL; VAL_BOUND]);;

let FORALL_VAL = prove
 (`!P. (!x:N word. P(val x)) <=> (!n. n < 2 EXP dimindex(:N) ==> P n)`,
  REWRITE_TAC[FORALL_VAL_GEN]);;

let VAL_CONG = prove
 (`!(v:N word) (w:N word).
        (val v == val w) (mod (2 EXP dimindex(:N))) <=> v = w`,
  REWRITE_TAC[GSYM VAL_EQ; CONG; MOD_MOD_REFL; VAL_MOD_REFL]);;

let WORD_MOD_SIZE = prove
 (`!n. word(n MOD (2 EXP dimindex(:N))):N word = word n`,
  REWRITE_TAC[WORD_EQ; CONG; MOD_MOD_REFL]);;

let VAL_WORD_CONG = prove
 (`!x. (val(word x:N word) == x) (mod (2 EXP (dimindex(:N))))`,
  REWRITE_TAC[VAL_WORD; CONG; MOD_MOD_REFL]);;

let VAL_WORD_GALOIS = prove
 (`!(w:N word) n. val w = n <=> n < 2 EXP dimindex(:N) /\ w = word n`,
  MESON_TAC[WORD_VAL; VAL_WORD_EQ; VAL_BOUND]);;

let WORD_VAL_GALOIS = prove
 (`!(w:N word) n. word n = w <=> n MOD 2 EXP dimindex(:N) = val w`,
  MESON_TAC[VAL_WORD; WORD_MOD_SIZE; WORD_VAL]);;

let BIT_VAL = prove
 (`!(x:N word) i. bit i x <=> ODD(val x DIV (2 EXP i))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  REWRITE_TAC[BIT_WORD; TAUT `(p /\ q <=> q) <=> (~p ==> ~q)`] THEN
  REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
  MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
  ASM_SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; DIMINDEX_NONZERO; COND_ID]);;

let BIT_VAL_MOD = prove
 (`!(x:N word) k.
        bit k x <=> 2 EXP k <= val(x) MOD 2 EXP (k + 1)`,
  REWRITE_TAC[BIT_VAL; GSYM NOT_EVEN; EVEN_MOD; EXP_ADD; EXP_1; DIV_MOD] THEN
  SIMP_TAC[DIV_EQ_0; NOT_LT; EXP_EQ_0; ARITH_EQ]);;

let BIT_LSB = prove
 (`!x:N word. bit 0 x <=> ODD(val x)`,
  REWRITE_TAC[BIT_VAL; EXP; DIV_1]);;

let TWICE_MSB = prove
 (`2 EXP dimindex(:N) = 2 * 2 EXP (dimindex(:N) - 1) /\
   (&2:int) pow dimindex(:N) = &2 * &2 pow (dimindex(:N) - 1)`,
  REWRITE_TAC[GSYM(CONJUNCT2 EXP); GSYM(CONJUNCT2 INT_POW)] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> SUC(n - 1) = n`]);;

let MSB_VAL = prove
 (`!w:N word. bit (dimindex(:N) - 1) w <=> 2 EXP (dimindex(:N) - 1) <= val w`,
  SIMP_TAC[BIT_VAL_MOD; SUB_ADD; DIMINDEX_GE_1; VAL_MOD_REFL]);;

let MSB_INT_VAL = prove
 (`!w:N word.
    bit (dimindex(:N) - 1) w <=> (&2 pow (dimindex(:N) - 1)):int <= &(val w)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LE; MSB_VAL]);;

let VAL_WORD_OF_BITS = prove
 (`!s. val(word_of_bits s:N word) =
       nsum {i | i < dimindex(:N) /\ i IN s} (\i. 2 EXP i)`,
  GEN_TAC THEN SIMP_TAC[val_def; BIT_WORD_OF_BITS; bitval] THEN
  REWRITE_TAC[COND_RAND; MULT_CLAUSES; GSYM NSUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let WORD_OF_BITS_AS_WORD = prove
 (`!s. word_of_bits s:N word =
       word(nsum {i | i < dimindex(:N) /\ i IN s} (\i. 2 EXP i))`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_OF_BITS; VAL_WORD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[GSYM VAL_WORD_OF_BITS; VAL_BOUND]);;

let WORD_OF_BITS_AS_WORD_FINITE = prove
 (`!s. FINITE s ==> word_of_bits s:N word = word(nsum s (\i. 2 EXP i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ; WORD_OF_BITS_AS_WORD] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[NSUM_RESTRICT_SET] THEN
  MATCH_MP_TAC CONG_NSUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[NUMBER_RULE `(n:num == n) (mod p)`] THEN
  REWRITE_TAC[NUMBER_RULE `(0 == n) (mod p) <=> p divides n`] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LT]) THEN
  SIMP_TAC[LE_EXISTS; EXP_ADD; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUMBER_RULE);;

let WORD_OF_BITS_SING_AS_WORD = prove
 (`!s i. word_of_bits {i}:N word = word(2 EXP i)`,
  SIMP_TAC[WORD_OF_BITS_AS_WORD_FINITE; FINITE_SING; NSUM_SING]);;

let VAL_WORD_OF_BITS_SING = prove
 (`!i. val(word_of_bits {i}:N word) = if i < dimindex(:N) then 2 EXP i else 0`,
  GEN_TAC THEN SIMP_TAC[val_def; BIT_WORD_OF_BITS; IN_SING; bitval] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
  SIMP_TAC[MULT_CLAUSES; NSUM_DELTA; IN_ELIM_THM]);;

let WORD_OF_BITS_MASK = prove
 (`!n. word_of_bits {i | i < n}:N word = word(2 EXP n - 1)`,
  GEN_TAC THEN SIMP_TAC[WORD_OF_BITS_AS_WORD_FINITE; FINITE_NUMSEG_LT] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(ARITH_RULE `n + 1 = m ==> n = m - 1`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP] THEN
  ASM_ARITH_TAC);;

let BIT_WORD_POW2 = prove
 (`!k i. bit i (word (2 EXP k):N word) <=> i = k /\ k < dimindex(:N)`,
  REWRITE_TAC[GSYM WORD_OF_BITS_SING_AS_WORD; BIT_WORD_OF_BITS] THEN
  SET_TAC[]);;

let BIT_WORD_1 = prove
 (`!i. bit i (word 1:N word) <=> i = 0`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 = 2 EXP 0`] THEN
  SIMP_TAC[BIT_WORD_POW2; LE_1; DIMINDEX_GE_1]);;

let WORD_OF_BITS_SING_AS_WORD_1 = prove
 (`!s i. word_of_bits {0}:N word = word 1`,
  REWRITE_TAC[WORD_OF_BITS_SING_AS_WORD; EXP]);;

let BITS_OF_WORD_1 = prove
 (`bits_of_word (word 1:N word) = {0}`,
  REWRITE_TAC[bits_of_word; BIT_WORD_1] THEN SET_TAC[]);;

let BIT_WORD_OF_BITS_SING = prove
 (`!k i. bit i (word_of_bits {k}:N word) <=> k < dimindex(:N) /\ i = k`,
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_SING] THEN MESON_TAC[]);;

let VAL_MOD = prove
 (`!(x:N word) k.
        val x MOD 2 EXP k = nsum {i | i < k} (\i. 2 EXP i * bitval(bit i x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[val_def] THEN
  SIMP_TAC[BINARY_DIGITSUM_MOD; FINITE_NUMSEG_LT] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; IMP_CONJ; MULT_EQ_0; BITVAL_EQ_0; NOT_LT] THEN
  MESON_TAC[BIT_TRIVIAL]);;

let VAL_MOD_STEP = prove
 (`!(x:N word) k.
      val x MOD 2 EXP (k + 1) = 2 EXP k * bitval(bit k x) + val x MOD 2 EXP k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_MOD; ARITH_RULE `i < k + 1 <=> i = k \/ i < k`] THEN
  REWRITE_TAC[SET_RULE `{x | x = a \/ P x} = a INSERT {x | P x}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Corresponding signed 2s-complement mappings to and from integers.         *)
(* ------------------------------------------------------------------------- *)

let ival = new_definition
 `(ival:N word->int) w =
    if val(w) < 2 EXP (dimindex(:N) - 1) then &(val w)
    else &(val w) - &2 pow dimindex(:N)`;;

let iword = new_definition
 `(iword:int->N word) x = word(num_of_int(x rem (&2 pow dimindex(:N))))`;;

let word_sgn = new_definition
 `word_sgn (x:N word) = int_sgn(ival x)`;;

let INT_IVAL = prove
 (`!w:N word.
        ival w =
        if &(val w):int < &2 pow (dimindex(:N) - 1) then &(val w)
        else &(val w) - &2 pow dimindex(:N)`,
  REWRITE_TAC[ival; INT_OF_NUM_POW; INT_OF_NUM_LT]);;

let WORD_IWORD = prove
 (`!n. word n:N word = iword(&n)`,
  GEN_TAC THEN REWRITE_TAC[iword; WORD_EQ] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[CONG; MOD_MOD_REFL]);;

let IVAL_VAL = prove
 (`!w:N word.
    ival w =
    &(val w) - &2 pow dimindex(:N) * &(bitval(bit (dimindex(:N) - 1) w))`,
  GEN_TAC THEN REWRITE_TAC[ival; GSYM NOT_LE; GSYM MSB_VAL; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bitval] THEN INT_ARITH_TAC);;

let VAL_IVAL = prove
 (`!w:N word.
    &(val w) =
    ival w + &2 pow dimindex(:N) * &(bitval (bit (dimindex (:N) - 1) w))`,
  REWRITE_TAC[IVAL_VAL] THEN CONV_TAC INT_ARITH);;

let MSB_IVAL = prove
 (`!(w:N word).
        bit (dimindex(:N) - 1) w <=> ival w < &0`,
  GEN_TAC THEN REWRITE_TAC[ival; MSB_VAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  REWRITE_TAC[INT_NOT_LT; INT_OF_NUM_LE; LE_0] THEN
  REWRITE_TAC[INT_ARITH `a - b:int < &0 <=> a < b`] THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_OF_NUM_POW; VAL_BOUND]);;

let IVAL_BOUND = prove
 (`!w:(N)word.
        --(&2 pow (dimindex(:N) - 1)) <= ival w /\
        ival w < &2 pow (dimindex(:N) - 1)`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` VAL_BOUND) THEN
  REWRITE_TAC[ival; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN
  SUBGOAL_THEN `?n. dimindex(:N) = SUC n` (CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[DIMINDEX_NONZERO; num_CASES]; ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1; INT_POW] THEN INT_ARITH_TAC);;

let IVAL_WORD_0 = prove
 (`ival(word 0) = &0`,
  REWRITE_TAC[ival; VAL_WORD_0; EXP_LT_0] THEN CONV_TAC NUM_REDUCE_CONV);;

let IVAL_WORD_1 = prove
 (`ival(word 1:N word) = if dimindex(:N) = 1 then -- &1 else &1`,
  REWRITE_TAC[ival; VAL_WORD_1] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 < x <=> 2 EXP 1 <= x`] THEN
  REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIMINDEX_NONZERO; ARITH_RULE
   `1 <= n - 1 <=> ~(n = 0 \/ n = 1)`] THEN
  ASM_CASES_TAC `dimindex(:N) = 1` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV);;

let VAL_WORD_BITVAL = prove
 (`!b. val(word(bitval b)) = bitval b`,
  MATCH_MP_TAC bool_INDUCT THEN
  REWRITE_TAC[VAL_WORD_1; VAL_WORD_0; BITVAL_CLAUSES]);;

let IVAL_VAL_CONG = prove
 (`!(w:N word). (ival w == &(val w)) (mod (&2 pow (dimindex(:N))))`,
  GEN_TAC THEN REWRITE_TAC[ival] THEN COND_CASES_TAC THEN
  CONV_TAC INTEGER_RULE);;

let IVAL_CONG = prove
 (`!(v:N word) (w:N word).
      (ival v == ival w) (mod (&2 pow (dimindex(:N)))) <=> v = w`,
  REWRITE_TAC[GSYM VAL_CONG; num_congruent; GSYM INT_OF_NUM_POW] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(INTEGER_RULE
   `(x:int == x') (mod n) /\ (y == y') (mod n)
    ==> ((x == y) (mod n) <=> (x' == y') (mod n))`) THEN
  REWRITE_TAC[IVAL_VAL_CONG]);;

let IVAL_EQ = prove
 (`!(v:N word) (w:N word). ival v = ival w <=> v = w`,
  MESON_TAC[NUMBER_RULE `(x:int == x) (mod n)`; IVAL_CONG]);;

let IVAL_EQ_0 = prove
 (`!(v:N word). ival w = &0 <=> w = word 0`,
  REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_0]);;

let IVAL_EQ_1 = prove
 (`!w:N word. ival w = &1 <=> 2 <= dimindex(:N) /\ w = word 1`,
  GEN_TAC THEN REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_1] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> (2 <= n <=> ~(n = 1))`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `w:N word` IVAL_BOUND) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

let IWORD_EQ = prove
 (`!x y. iword x:N word = iword y <=> (x == y) (mod (&2 pow (dimindex(:N))))`,
  REWRITE_TAC[iword; WORD_EQ; num_congruent; GSYM INT_OF_NUM_POW] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_DIVISION; INT_POW_EQ_0;
           INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]);;

let IWORD_REM_SIZE = prove
 (`!n. iword(n rem (&2 pow dimindex(:N))):N word = iword n`,
  REWRITE_TAC[IWORD_EQ; INT_REM_MOD_SELF]);;

let IVAL_IWORD_CONG = prove
 (`!x. (ival(iword x:N word) == x) (mod (&2 pow (dimindex(:N))))`,
  GEN_TAC THEN MP_TAC(SPEC `iword x:N word` IVAL_VAL_CONG) THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(y:int == z) (mod n) ==> (x == y) (mod n) ==> (x == z) (mod n)`) THEN
  REWRITE_TAC[iword] THEN MATCH_MP_TAC(INTEGER_RULE
   `(&(val(word w:N word)):int == &w) (mod n) /\ (&w:int == z) (mod n)
    ==> (&(val(word w:N word)) == z) (mod n)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_POW; GSYM num_congruent] THEN
    REWRITE_TAC[VAL_WORD; CONG; MOD_MOD_REFL];
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_DIVISION; INT_POW_EQ_0;
           INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]]);;

let IVAL_IWORD = prove
 (`!n. --(&2 pow (dimindex (:N) - 1)) <= n /\ n < &2 pow (dimindex (:N) - 1)
       ==> ival(iword n:N word) = n`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `n:int` IVAL_IWORD_CONG) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] INT_CONG_IMP_EQ) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
   `n:int < e1
    ==> --e1 <= n /\ --e1 <= n' /\ n' < e1 /\ &2 * e1 = e
        ==> abs(n' - n) < e`)) THEN
  ASM_REWRITE_TAC[IVAL_BOUND; GSYM(CONJUNCT2 INT_POW)] THEN
  SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> SUC(n - 1) = n`]);;

let IWORD_IVAL = prove
 (`!w:N word. iword(ival w) = w`,
  REWRITE_TAC[GSYM IVAL_CONG; IVAL_IWORD_CONG]);;

let IVAL_IWORD_GALOIS = prove
 (`!(w:N word) n.
        ival w = n <=>
        --(&2 pow (dimindex(:N) - 1)) <= n /\
        n < &2 pow (dimindex(:N) - 1) /\
        w = iword n`,
  MESON_TAC[IVAL_IWORD; IWORD_IVAL; IVAL_BOUND]);;

let BIT_IVAL = prove
 (`!(x:N word) i.
    bit i x <=> i < dimindex(:N) /\ ~(&2 divides (ival x div &2 pow i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_VAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[GSYM NOT_EVEN; EVEN_EXISTS; GSYM divides] THEN
    AP_TERM_TAC THEN REWRITE_TAC[num_divides] THEN MATCH_MP_TAC(INTEGER_RULE
     `(x:int == y) (mod n) ==> (n divides x <=> n divides y)`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_DIV; GSYM INT_OF_NUM_POW] THEN
    MATCH_MP_TAC INT_CONG_DIV2 THEN SIMP_TAC[INT_POW_LE; INT_POS] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!m. (x:int == y) (mod m) /\ n divides m ==> (y == x) (mod n)`) THEN
    EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN REWRITE_TAC[IVAL_VAL_CONG] THEN
    ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POW_ADD; INT_POW] THEN
    CONV_TAC INTEGER_RULE;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
    SIMP_TAC[DIV_EQ_0; ARITH_EQ; EXP_EQ_0] THEN
    TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
    ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; DIMINDEX_NONZERO; COND_ID]]);;

let BIT_IWORD = prove
 (`!i x. bit i (iword x:N word) <=>
         i < dimindex(:N) /\ ~(&2 divides (x div (&2 pow i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIT_IVAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(INTEGER_RULE
   `(x:int == y) (mod n) ==> (n divides x <=> n divides y)`) THEN
  MATCH_MP_TAC INT_CONG_DIV2 THEN SIMP_TAC[INT_POW_LE; INT_POS] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!m. (x:int == y) (mod m) /\ n divides m ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN
  REWRITE_TAC[IVAL_IWORD_CONG] THEN
    ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LT_EXISTS]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[INT_POW_ADD; INT_POW] THEN
    CONV_TAC INTEGER_RULE);;

let INT_REM_IVAL = prove
 (`!(w:N word) k.
        k <= dimindex(:N) ==> (ival w) rem (&2 pow k) = &(val w MOD 2 EXP k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!n:int. (x == y) (mod n) /\ m divides n ==> (x == y) (mod m)`) THEN
  EXISTS_TAC `(&2:int) pow dimindex(:N)` THEN REWRITE_TAC[IVAL_VAL_CONG] THEN
  POP_ASSUM MP_TAC THEN
  SIMP_TAC[LE_EXISTS; INT_POW_ADD; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Some "limiting" values with names in the style of C's "limits.h" macros.  *)
(* ------------------------------------------------------------------------- *)

let word_UINT_MAX = new_definition
 `word_UINT_MAX:N word = word(2 EXP dimindex(:N) - 1)`;;

let word_INT_MIN = new_definition
 `word_INT_MIN:N word = iword(--(&2 pow (dimindex(:N) - 1)))`;;

let word_INT_MAX = new_definition
 `word_INT_MAX:N word = iword(&2 pow (dimindex(:N) - 1) - &1)`;;

let WORD_INT_MIN = prove
 (`word_INT_MIN:N word = word(2 EXP (dimindex(:N) - 1))`,
  REWRITE_TAC[word_INT_MIN; WORD_IWORD; IWORD_EQ; GSYM INT_OF_NUM_POW] THEN
  MATCH_MP_TAC(INTEGER_RULE `&2 * x:int = y ==> (--x == x) (mod y)`) THEN
  REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN
  SIMP_TAC[DIMINDEX_NONZERO; ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`]);;

let WORD_INT_MAX = prove
 (`word_INT_MAX:N word = word(2 EXP (dimindex(:N) - 1) - 1)`,
  REWRITE_TAC[word_INT_MAX; WORD_IWORD] THEN AP_TERM_TAC THEN
  SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_POW; LE_1; EXP_EQ_0; ARITH_EQ]);;

let VAL_WORD_UINT_MAX = prove
 (`val(word_UINT_MAX:N word) = 2 EXP dimindex(:N) - 1`,
  REWRITE_TAC[word_UINT_MAX; VAL_WORD] THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`; EXP_EQ_0] THEN ARITH_TAC);;

let IVAL_WORD_INT_MIN = prove
 (`ival(word_INT_MIN:N word) = --(&2 pow (dimindex(:N) - 1))`,
  REWRITE_TAC[word_INT_MIN] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[INT_LE_REFL; INT_ARITH `--a:int < a <=> &0 < a`] THEN
  SIMP_TAC[INT_LT_POW2]);;

let IVAL_WORD_INT_MAX = prove
 (`ival(word_INT_MAX:N word) = &2 pow (dimindex(:N) - 1) - &1`,
  REWRITE_TAC[word_INT_MAX] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[INT_ARITH `x - &1:int < x`] THEN
  MATCH_MP_TAC(INT_ARITH `&0:int < x ==> --x <= x - &1`) THEN
  SIMP_TAC[INT_LT_POW2]);;

let VAL_BOUND_ALT = prove
 (`!w:N word. val w <= val(word_UINT_MAX:N word)`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` VAL_BOUND) THEN
  REWRITE_TAC[VAL_WORD_UINT_MAX] THEN ARITH_TAC);;

let IVAL_BOUND_ALT = prove
 (`!w:N word. ival(word_INT_MIN:N word) <= ival w /\
              ival w <= ival(word_INT_MAX:N word)`,
  GEN_TAC THEN MP_TAC(ISPEC `w:N word` IVAL_BOUND) THEN
  REWRITE_TAC[IVAL_WORD_INT_MAX; IVAL_WORD_INT_MIN] THEN INT_ARITH_TAC);;

let VAL_WORD_INT_MIN = prove
 (`val(word_INT_MIN:N word) = 2 EXP (dimindex(:N) - 1)`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; VAL_IVAL; GSYM INT_OF_NUM_POW] THEN
  REWRITE_TAC[MSB_IVAL; IVAL_WORD_INT_MIN] THEN
  SIMP_TAC[INT_NEG_LT0; INT_LT_POW2; BITVAL_CLAUSES; INT_MUL_RID] THEN
  REWRITE_TAC[INT_ARITH `--x + y:int = x <=> &2 * x = y`] THEN
  SIMP_TAC[GSYM(CONJUNCT2 INT_POW)] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC(n - 1) = n <=> ~(n = 0)`; DIMINDEX_NONZERO]);;

let INT_VAL_WORD_INT_MIN = prove
 (`&(val(word_INT_MIN:N word)):int = &2 pow (dimindex(:N) - 1)`,
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_EQ; VAL_WORD_INT_MIN]);;

let WORD_INT_MIN_ALT = prove
 (`word_INT_MIN:N word = word_of_bits {dimindex (:N) - 1}`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_INT_MIN; VAL_WORD_OF_BITS_SING] THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> 1 <= n`; DIMINDEX_GE_1]);;

let BIT_WORD_INT_MIN = prove
 (`!i. bit i (word_INT_MIN:N word) <=> i = dimindex(:N) - 1`,
  REWRITE_TAC[WORD_INT_MIN_ALT; BIT_WORD_OF_BITS_SING] THEN
  REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `n - 1 < n <=> 1 <= n`]);;

(* ------------------------------------------------------------------------- *)
(* Population count (= number of 1s in a word), as a mathematical number.    *)
(* ------------------------------------------------------------------------- *)

let word_popcount = new_definition
 `word_popcount (x:N word) = CARD(bits_of_word x)`;;

let HAS_SIZE_BITS_OF_WORD_POPCOUNT = prove
 (`!x:N word. (bits_of_word x) HAS_SIZE word_popcount x`,
  REWRITE_TAC[word_popcount; HAS_SIZE; FINITE_BITS_OF_WORD]);;

let WORD_POPCOUNT_BOUND = prove
 (`!x:N word. word_popcount x <= dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[word_popcount; bits_of_word] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

let WORD_POPCOUNT_EQ_0 = prove
 (`!x:N word. word_popcount x = 0 <=> x = word 0`,
  SIMP_TAC[CARD_EQ_0; word_popcount; FINITE_BITS_OF_WORD] THEN
  REWRITE_TAC[BITS_OF_WORD_EQ_EMPTY]);;

let WORD_POPCOUNT_0 = prove
 (`word_popcount(word 0) = 0`,
  REWRITE_TAC[WORD_POPCOUNT_EQ_0]);;

let WORD_POPCOUNT_1 = prove
 (`word_popcount(word 1) = 1`,
  REWRITE_TAC[word_popcount; BITS_OF_WORD_1; CARD_SING]);;

(* ------------------------------------------------------------------------- *)
(* Parity (= evenness or oddity of the popcount).                            *)
(* ------------------------------------------------------------------------- *)

let word_evenparity = new_definition
 `word_evenparity (x:N word) <=> EVEN(word_popcount x)`;;

let word_oddparity = new_definition
 `word_oddparity (x:N word) <=> ODD(word_popcount x)`;;

let NOT_WORD_EVENPARITY = prove
 (`!x:N word. ~(word_evenparity x) <=> word_oddparity x`,
  REWRITE_TAC[word_evenparity; word_oddparity; NOT_EVEN]);;

let NOT_WORD_ODDPARITY = prove
 (`!x:N word. ~(word_oddparity x) <=> word_evenparity x`,
  REWRITE_TAC[word_evenparity; word_oddparity; NOT_ODD]);;

let WORD_EVENPARITY_0 = prove
 (`word_evenparity(word 0:N word)`,
  REWRITE_TAC[word_evenparity; WORD_POPCOUNT_0; EVEN]);;

let WORD_ODDPARITY_0 = prove
 (`~word_oddparity(word 0:N word)`,
  REWRITE_TAC[NOT_WORD_ODDPARITY; WORD_EVENPARITY_0]);;

let WORD_EVENPARITY_1 = prove
 (`~word_evenparity(word 1:N word)`,
  REWRITE_TAC[word_evenparity; WORD_POPCOUNT_1] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WORD_ODDPARITY_1 = prove
 (`word_oddparity(word 1:N word)`,
  REWRITE_TAC[GSYM NOT_WORD_EVENPARITY; WORD_EVENPARITY_1]);;

(* ------------------------------------------------------------------------- *)
(* Modular arithmetic operations in general, unsigned and signed.            *)
(* ------------------------------------------------------------------------- *)

let modular = new_definition
 `modular op (x:(N)word) (y:(N)word) = word(op (val x) (val y)):(N)word`;;

let VAL_MODULAR = prove
 (`!op x y:(N)word.
        val(modular op x y) = (op (val x) (val y)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[modular; VAL_WORD]);;

let CONG_MODULAR = prove
 (`!op x y:(N)word.
       (val(modular op x y) == op (val x) (val y))
       (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[VAL_MODULAR; CONG_LMOD] THEN CONV_TAC NUMBER_RULE);;

let imodular = new_definition
 `imodular op (x:(N)word) (y:(N)word) =
        iword(op (ival x) (ival y)):(N)word`;;

let CONG_IMODULAR = prove
 (`!op x y:(N)word.
       (ival(imodular op x y) == op (ival x) (ival y))
       (mod (&2 pow (dimindex(:N))))`,
  REWRITE_TAC[imodular; IVAL_IWORD_CONG]);;

(* ------------------------------------------------------------------------- *)
(* Relational operations in general w.r.t. unsigned or signed value.         *)
(* ------------------------------------------------------------------------- *)

let relational2 = new_definition
 `relational2 r (x:(N)word) (y:(N)word) :bool = r (val x) (val y)`;;

let irelational2 = new_definition
 `irelational2 r (x:(N)word) (y:(N)word) :bool = r (ival x) (ival y)`;;

(* ------------------------------------------------------------------------- *)
(* Bitwise operations in general.                                            *)
(* ------------------------------------------------------------------------- *)

let bitwise1 = new_definition
 `(bitwise1 op:N word->N word) x = mk_word(lambda i. op(bitvector x$i))`;;

let bitwise2 = new_definition
 `(bitwise2 op:N word->N word->N word) x y =
        mk_word(lambda i. op (bitvector x$i) (bitvector y$i))`;;

let BIT_BITWISE1 = prove
 (`!op (x:N word) k.
        bit k (bitwise1 op x) <=>
        k < dimindex(:N) /\ op(bit k x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bitwise1; word_tybij] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC);;

let BIT_BITWISE2 = prove
 (`!op (x:N word) (y:N word) k.
        bit k (bitwise2 op x y) <=>
        k < dimindex(:N) /\ op (bit k x) (bit k y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bit] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[bitwise2; word_tybij] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main word operations. Where there is any meaningful difference        *)
(* between unsigned and signed we use a "u" or an "i" in the names.          *)
(* ------------------------------------------------------------------------- *)

let word_not = new_definition
 `word_not = bitwise1 (~)`;;

let BIT_WORD_NOT = prove
 (`!(x:N word) k. bit k (word_not x) <=> k < dimindex(:N) /\ ~bit k x`,
  REWRITE_TAC[word_not; BIT_BITWISE1]);;

let BITS_OF_WORD_NOT = prove
 (`!w:N word. bits_of_word(word_not w) =
              {i | i < dimindex(:N)} DIFF bits_of_word w`,
  REWRITE_TAC[bits_of_word; BIT_WORD_NOT] THEN SET_TAC[]);;

let WORD_OF_BITS_DIFF = prove
 (`!s t. {i | i < dimindex(:N)} SUBSET s
         ==> word_of_bits(s DIFF t):N word = word_not(word_of_bits t)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_NOT] THEN
  REWRITE_TAC[BITS_OF_WORD_OF_BITS] THEN SET_TAC[]);;

let VAL_WORD_NOT = prove
 (`!w:N word. val(word_not w) = 2 EXP dimindex(:N) - 1 - val w`,
  GEN_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `(m + n) + 1 = p ==> m = p - 1 - n`) THEN
  SIMP_TAC[val_def; GSYM NSUM_ADD; FINITE_NUMSEG_LT] THEN
  SIMP_TAC[GSYM LEFT_ADD_DISTRIB; BIT_WORD_NOT] THEN
  SIMP_TAC[BITVAL_NOT; BITVAL_BOUND; SUB_ADD; MULT_CLAUSES] THEN
  SPEC_TAC(`dimindex(:N)`,`k:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; ADD_CLAUSES; MULT_CLAUSES] THEN
  ASM_ARITH_TAC);;

let WORD_POPCOUNT_NOT = prove
 (`!x:N word. word_popcount(word_not x) = dimindex(:N) - word_popcount x`,
  GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
   `x + y:num = z ==> x = z - y`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  REWRITE_TAC[word_popcount] THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; BITS_OF_WORD_NOT] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s DIFF t UNION t = s <=> t SUBSET s`] THEN
  REWRITE_TAC[bits_of_word; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LT]);;

let word_and = new_definition
 `word_and = bitwise2 (/\)`;;

let BIT_WORD_AND = prove
 (`!op (x:N word) (y:N word) k.
        bit k (word_and x y) <=>
        k < dimindex(:N) /\ bit k x /\ bit k y`,
  REWRITE_TAC[word_and; BIT_BITWISE2]);;

let BIT_WORD_AND_ALT = prove
 (`!(x:N word) y k. bit k (word_and x y) <=> bit k x /\ bit k y`,
  MESON_TAC[BIT_WORD_AND; BIT_TRIVIAL; NOT_LT]);;

let BITS_OF_WORD_AND = prove
 (`!v w:N word.
        bits_of_word(word_and v w) = bits_of_word v INTER bits_of_word w`,
  REWRITE_TAC[bits_of_word; BIT_WORD_AND] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_AND_EQ_0 = prove
 (`!v w:N word.
        word_and v w = word 0 <=> DISJOINT (bits_of_word v) (bits_of_word w)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_AND; BITS_OF_WORD_0] THEN
  SET_TAC[]);;

let WORD_OF_BITS_INTER = prove
 (`!s t. word_of_bits(s INTER t):N word =
         word_and (word_of_bits s) (word_of_bits t)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_AND] THEN
  REWRITE_TAC[BITS_OF_WORD_OF_BITS] THEN SET_TAC[]);;

let WORD_AND_WORD_OF_BITS_SING = prove
 (`!(w:N word) k.
        word_and w (word_of_bits {k}) =
        if bit k w then word_of_bits {k} else word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_OF_BITS; BIT_WORD_0] THEN
  ASM SET_TAC[]);;

let WORD_OF_BITS_SING_AND_WORD = prove
 (`!(w:N word) k.
        word_and (word_of_bits {k}) w =
        if bit k w then word_of_bits {k} else word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_OF_BITS; BIT_WORD_0] THEN
  ASM SET_TAC[]);;

let word_or = new_definition
 `word_or = bitwise2 (\/)`;;

let BIT_WORD_OR = prove
 (`!op (x:N word) (y:N word) k.
        bit k (word_or x y) <=>
        k < dimindex(:N) /\ (bit k x \/ bit k y)`,
  REWRITE_TAC[word_or; BIT_BITWISE2]);;

let BIT_WORD_OR_ALT = prove
 (`!(x:N word) y k. bit k (word_or x y) <=> bit k x \/ bit k y`,
  MESON_TAC[BIT_WORD_OR; BIT_TRIVIAL; NOT_LT]);;

let BITS_OF_WORD_OR = prove
 (`!v w:N word.
        bits_of_word(word_or v w) = bits_of_word v UNION bits_of_word w`,
  REWRITE_TAC[bits_of_word; BIT_WORD_OR] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_OF_BITS_UNION = prove
 (`!s t. word_of_bits(s UNION t):N word =
         word_or (word_of_bits s) (word_of_bits t)`,
  REWRITE_TAC[GSYM BITS_OF_WORD_EQ; BITS_OF_WORD_OR] THEN
  REWRITE_TAC[BITS_OF_WORD_OF_BITS] THEN SET_TAC[]);;

let word_xor = new_definition
 `word_xor = bitwise2 (\x y. ~(x <=> y))`;;

let BIT_WORD_XOR = prove
 (`!op (x:N word) (y:N word) k.
        bit k (word_xor x y) <=>
        k < dimindex(:N) /\ ~(bit k x <=> bit k y)`,
  REWRITE_TAC[word_xor; BIT_BITWISE2]);;

let BIT_WORD_XOR_ALT = prove
 (`!(x:N word) y k. bit k (word_xor x y) <=> ~(bit k x <=> bit k y)`,
  MESON_TAC[BIT_WORD_XOR; BIT_TRIVIAL; NOT_LT]);;

let VAL_WORD_ADD_AND_XOR,VAL_WORD_ADD_AND_OR = (CONJ_PAIR o prove)
 (`(!x y:N word. val x + val y = 2 * val(word_and x y) + val(word_xor x y)) /\
   (!x y:N word. val x + val y = val(word_and x y) + val(word_or x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[val_def; GSYM NSUM_LMUL] THEN
  SIMP_TAC[GSYM NSUM_ADD; FINITE_NUMSEG_LT] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; BIT_WORD_AND; BIT_WORD_XOR; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ASM_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let VAL_WORD_OR_DISJOINT = prove
 (`!x y:N word.
        word_and x y = word 0 ==> val(word_or x y) = val x + val y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[VAL_WORD_ADD_AND_OR] THEN
  ASM_REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES]);;

let VAL_WORD_OR_AND_XOR = prove
 (`!x y:N word. val(word_or x y) = val(word_and x y) + val(word_xor x y)`,
  ONCE_REWRITE_TAC[ARITH_RULE `a = b + c <=> b + a = 2 * b + c`] THEN
  MESON_TAC[VAL_WORD_ADD_AND_XOR; VAL_WORD_ADD_AND_OR]);;

let word_add = new_definition
 `word_add = modular (+)`;;

let VAL_WORD_ADD = prove
 (`!x y:(N) word.
        val(word_add x y) = (val(x) + val(y)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_add; VAL_MODULAR]);;

let VAL_WORD_ADD_CASES = prove
 (`!x y:(N) word.
        val(word_add x y) =
        if val x + val y < 2 EXP dimindex(:N) then val x + val y
        else (val x + val y) - 2 EXP dimindex(:N)`,
  SIMP_TAC[VAL_WORD_ADD; VAL_BOUND; MOD_ADD_CASES]);;

let VAL_WORD_ADC_CASES = prove
 (`!c x y:(N) word.
        val(c) < 2
        ==> val(word_add (word_add x y) c) =
            if val x + val y + val c < 2 EXP dimindex(:N)
            then val x + val y + val c
            else (val x + val y + val c) - 2 EXP dimindex(:N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
  MATCH_MP_TAC MOD_CASES THEN MATCH_MP_TAC(ARITH_RULE
   `x < n /\ y < n /\ c < 2 ==> x + y + c < 2 * n`) THEN
  ASM_REWRITE_TAC[VAL_BOUND]);;

let INT_VAL_WORD_ADD_CASES = prove
 (`!x y:(N) word.
      &(val(word_add x y)):int =
      if &(val x) + &(val y):int < &2 pow dimindex(:N) then &(val x) + &(val y)
      else (&(val x) + &(val y)) - &2 pow dimindex(:N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_ADD_CASES] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NOT_LT; INT_OF_NUM_SUB]);;

let CONG_WORD_ADD = prove
 (`!x y:(N)word.
        (val(word_add x y) == val x + val y) (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[word_add; CONG_MODULAR]);;

let WORD_ADD = prove
 (`!x y. word(x + y):N word = word_add (word x) (word y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_CONG] THEN
  MP_TAC(ISPECL [`word x:N word`; `word y:N word`] CONG_WORD_ADD) THEN
  MAP_EVERY (MP_TAC o C ISPEC VAL_WORD_CONG)
   [`x + y:num`; `y:num`; `x:num`] THEN
  CONV_TAC NUMBER_RULE);;

let ICONG_WORD_ADD = prove
 (`!x y:(N)word.
        (ival(word_add x y) == ival x + ival y) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `y:N word`; `word_add x y:N word`] THEN
  MP_TAC(ISPECL [`x:N word`; `y:N word`] CONG_WORD_ADD) THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD] THEN
  CONV_TAC INTEGER_RULE);;

let IWORD_INT_ADD = prove
 (`!x y. iword(x + y):N word = word_add (iword x) (iword y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IVAL_CONG] THEN
  MP_TAC(ISPECL [`iword x:N word`; `iword y:N word`] ICONG_WORD_ADD) THEN
  MAP_EVERY (MP_TAC o C ISPEC IVAL_IWORD_CONG)
   [`x + y:int`; `y:int`; `x:int`] THEN
  CONV_TAC INTEGER_RULE);;

let WORD_ADD_IMODULAR = prove
 (`(word_add:N word->N word->N word) = imodular ( + )`,
  REWRITE_TAC[FUN_EQ_THM; GSYM IVAL_CONG] THEN
  ASM_MESON_TAC[ICONG_WORD_ADD; CONG_IMODULAR; INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)`]);;

let word_sub = new_definition
 `(word_sub:(N)word->(N)word->(N)word) =
        modular (\x y. x + (2 EXP dimindex(:N) - y))`;;

let VAL_WORD_SUB = prove
 (`!x y:(N) word.
        val(word_sub x y) =
        (val(x) + (2 EXP dimindex(:N) - val(y))) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_sub; VAL_MODULAR]);;

let VAL_WORD_SUB_CASES = prove
 (`!x y:(N) word.
        val(word_sub x y) =
        if val y <= val x then val(x) - val(y)
        else val(x) + (2 EXP dimindex(:N) - val(y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT] THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1`;
    MATCH_MP_TAC MOD_LT] THEN
  MAP_EVERY (MP_TAC o C ISPEC VAL_BOUND) [`x:N word`; `y:N word`] THEN
  ASM_ARITH_TAC);;

let INT_VAL_WORD_SUB_CASES = prove
 (`!x y:(N) word.
        &(val(word_sub x y)):int =
        if &(val y):int <= &(val x) then &(val x) - &(val y)
        else &(val x) + (&2 pow dimindex(:N) - &(val y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_POW; INT_OF_NUM_LE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INT_OF_NUM_ADD; INT_OF_NUM_SUB; VAL_BOUND; LT_IMP_LE]);;

let CONG_WORD_SUB = prove
 (`!x y:(N)word.
        (val(word_sub x y) + val y == val x) (mod (2 EXP dimindex(:N)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONG; VAL_MODULAR; word_sub] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  SIMP_TAC[VAL_BOUND; ARITH_RULE `y:num < n ==> (x + n - y) + y = x + n`] THEN
  REWRITE_TAC[GSYM CONG] THEN CONV_TAC NUMBER_RULE);;

let ICONG_WORD_SUB = prove
 (`!x y:N word.
        (ival(word_sub x y) == ival x - ival y) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `y:N word`; `word_sub x y:N word`] THEN
  MP_TAC(ISPECL [`x:N word`; `y:N word`] CONG_WORD_SUB) THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD] THEN
  CONV_TAC INTEGER_RULE);;

let IWORD_INT_SUB = prove
 (`!x y. iword(x - y):N word = word_sub (iword x) (iword y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IVAL_CONG] THEN
  MP_TAC(ISPECL [`iword x:N word`; `iword y:N word`] ICONG_WORD_SUB) THEN
  MAP_EVERY (MP_TAC o C ISPEC IVAL_IWORD_CONG)
   [`x - y:int`; `y:int`; `x:int`] THEN
  CONV_TAC INTEGER_RULE);;

let WORD_SUB_IMODULAR = prove
 (`(word_sub:N word->N word->N word) = imodular ( - )`,
  REWRITE_TAC[FUN_EQ_THM; GSYM IVAL_CONG] THEN
  ASM_MESON_TAC[ICONG_WORD_SUB; CONG_IMODULAR; INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)`]);;

let WORD_SUB = prove
 (`!x y. word(x - y):N word =
         if y <= x then word_sub (word x) (word y) else word 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[WORD_IWORD; GSYM INT_OF_NUM_SUB; IWORD_INT_SUB];
    ASM_MESON_TAC[SUB_EQ_0; LE_CASES]]);;

let word_neg = new_definition
 `word_neg (a:N word) = word_sub (word 0) a`;;

let VAL_WORD_NEG = prove
 (`!x:(N) word.
        val(word_neg x) =
        (2 EXP dimindex(:N) - val(x)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_neg; VAL_WORD_SUB; VAL_WORD_0; ADD_CLAUSES]);;

let VAL_WORD_NEG_CASES = prove
 (`!x:(N) word.
        val(word_neg x) =
        if val x = 0 then 0 else 2 EXP dimindex(:N) - val(x)`,
  REWRITE_TAC[word_neg; VAL_WORD_SUB_CASES; VAL_WORD_0] THEN
  SIMP_TAC[LE; ADD_CLAUSES; SUB_REFL]);;

let INT_VAL_WORD_NEG_CASES = prove
 (`!x:N word.
        &(val(word_neg x)):int =
        if &(val x):int = &0 then &0 else &2 pow dimindex(:N) - &(val x)`,
  SIMP_TAC[INT_OF_NUM_POW; INT_OF_NUM_SUB; LT_IMP_LE; VAL_BOUND] THEN
  REWRITE_TAC[VAL_WORD_NEG_CASES; INT_OF_NUM_EQ] THEN MESON_TAC[]);;

let CONG_WORD_NEG = prove
 (`!x:(N)word.
        (val(word_neg x) + val x == 0) (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[word_neg] THEN MESON_TAC[CONG_WORD_SUB; VAL_WORD_0]);;

let ICONG_WORD_NEG = prove
 (`!x:(N)word.
        (ival(word_neg x) == --(ival x)) (mod (&2 pow dimindex(:N)))`,
  REWRITE_TAC[word_neg] THEN
  MESON_TAC[ICONG_WORD_SUB; INT_SUB_LZERO; IVAL_WORD_0]);;

let IWORD_INT_NEG = prove
 (`!x. iword(--x):N word = word_neg (iword x)`,
  REWRITE_TAC[GSYM INT_SUB_LZERO; word_neg] THEN
  REWRITE_TAC[IWORD_INT_SUB; GSYM WORD_IWORD]);;

let WORD_NEG_AS_ADD = prove
 (`!x:N word. word_neg x = word_add (word_not x) (word 1)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_NEG] THEN
  REWRITE_TAC[MOD_MOD_REFL; VAL_WORD_ADD; VAL_WORD_1; VAL_WORD_NOT] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  SIMP_TAC[VAL_BOUND; ARITH_RULE `n < e ==> (e - 1 - n) + 1 = e - n`]);;

let WORD_NOT_AS_SUB = prove
 (`!x:N word. word_not x = word_sub (word_neg x) (word 1)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_SUB; VAL_WORD_NEG] THEN
  REWRITE_TAC[MOD_MOD_REFL; VAL_WORD_SUB; VAL_WORD_1; VAL_WORD_NOT] THEN
  CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[VAL_BOUND; ARITH_RULE
   `x < e ==> (e - x) + (e - 1) = e + (e - 1 - x)`] THEN
  REWRITE_TAC[GSYM CONG] THEN CONV_TAC NUMBER_RULE);;

let VAL_WORD_NEG_1 = prove
 (`val(word_neg(word 1:N word)) = 2 EXP dimindex(:N) - 1`,
  REWRITE_TAC[VAL_WORD_NEG_CASES; VAL_WORD_1; ARITH_EQ]);;

let IVAL_WORD_NEG_1 = prove
 (`ival(word_neg(word 1:N word)) = -- &1`,
  REWRITE_TAC[ival; VAL_WORD_NEG_1] THEN
  REWRITE_TAC[ARITH_RULE `m - 1 < n <=> ~(n = 0) /\ m <= n`] THEN
  SIMP_TAC[LE_EXP; EXP_EQ_0; ARITH_EQ; DIMINDEX_NONZERO;
           ARITH_RULE `n <= n - 1 <=> n = 0`;
           GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_POW; LE_1] THEN
  INT_ARITH_TAC);;

let IVAL_EQ_MINUS1 = prove
 (`!w:N word. ival w = -- &1 <=> w = word_neg(word 1)`,
  REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_NEG_1]);;

let WORD_NEG_1 = prove
 (`word_neg(word 1:N word) = word_not(word 0)`,
  REWRITE_TAC[WORD_NOT_AS_SUB; word_neg] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; VAL_WORD_SUB_CASES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let word_mul = new_definition
 `word_mul = modular ( * )`;;

let VAL_WORD_MUL = prove
 (`!x y:(N)word.
        val(word_mul x y) = (val(x) * val(y)) MOD (2 EXP dimindex(:N))`,
  REWRITE_TAC[word_mul; VAL_MODULAR]);;

let CONG_WORD_MUL = prove
 (`!x y:(N)word.
        (val(word_mul x y) == val x * val y) (mod (2 EXP dimindex(:N)))`,
  REWRITE_TAC[word_mul; CONG_MODULAR]);;

let WORD_MUL = prove
 (`!x y. word(x * y):N word = word_mul (word x) (word y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_CONG] THEN
  MP_TAC(ISPECL [`word x:N word`; `word y:N word`] CONG_WORD_MUL) THEN
  MAP_EVERY (MP_TAC o C ISPEC VAL_WORD_CONG)
   [`x * y:num`; `y:num`; `x:num`] THEN
  CONV_TAC NUMBER_RULE);;

let ICONG_WORD_MUL = prove
 (`!x y:(N)word.
        (ival(word_mul x y) == ival x * ival y) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x:N word`; `y:N word`] CONG_WORD_MUL) THEN
  MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `y:N word`; `word_mul x y:N word`] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
  CONV_TAC INTEGER_RULE);;

let IWORD_INT_MUL = prove
 (`!x y. iword(x * y):N word = word_mul (iword x) (iword y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IVAL_CONG] THEN
  MP_TAC(ISPECL [`iword x:N word`; `iword y:N word`] ICONG_WORD_MUL) THEN
  MAP_EVERY (MP_TAC o C ISPEC IVAL_IWORD_CONG)
   [`x * y:int`; `y:int`; `x:int`] THEN
  CONV_TAC INTEGER_RULE);;

let WORD_MUL_IMODULAR = prove
 (`(word_mul:N word->N word->N word) = imodular ( * )`,
  REWRITE_TAC[FUN_EQ_THM; GSYM IVAL_CONG] THEN
  ASM_MESON_TAC[ICONG_WORD_MUL; CONG_IMODULAR; INTEGER_RULE
   `(a:int == b) (mod n) /\ (c == b) (mod n) ==> (a == c) (mod n)`]);;

let word_udiv = new_definition
 `word_udiv = modular (DIV)`;;

let VAL_WORD_UDIV = prove
 (`!x y:(N)word.
        val(word_udiv x y) = val(x) DIV val(y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_udiv; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
   `m DIV n <= m /\ m < p ==> m DIV n < p`) THEN
  REWRITE_TAC[VAL_BOUND; DIV_LE]);;

let word_umod = new_definition
 `word_umod = modular (MOD)`;;

let VAL_WORD_UMOD = prove
 (`!x y:(N)word.
        val(word_umod x y) = val(x) MOD val(y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_umod; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
   `m MOD n <= m /\ m < p ==> m MOD n < p`) THEN
  REWRITE_TAC[VAL_BOUND; MOD_LE]);;

let word_umax = new_definition
 `word_umax = modular (MAX)`;;

let word_imax = new_definition
 `word_imax = imodular (max)`;;

let VAL_WORD_UMAX = prove
 (`!x y:(N)word.
        val(word_umax x y) = MAX (val x) (val y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_umax; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `MAX x y < n <=> x < n /\ y < n`] THEN
  REWRITE_TAC[VAL_BOUND]);;

let IVAL_WORD_IMAX = prove
 (`!x y:(N)word.
        ival(word_imax x y) = max (ival x) (ival y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_imax; imodular] THEN
  REWRITE_TAC[INT_MAX] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IWORD_IVAL]);;

let word_umin = new_definition
 `word_umin = modular (MIN)`;;

let word_imin = new_definition
 `word_imin = imodular (min)`;;

let VAL_WORD_UMIN = prove
 (`!x y:(N)word.
        val(word_umin x y) = MIN (val x) (val y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_umin; VAL_MODULAR] THEN
  MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[ARITH_RULE `MIN x y < n <=> x < n \/ y < n`] THEN
  REWRITE_TAC[VAL_BOUND]);;

let IVAL_WORD_IMIN = prove
 (`!x y:(N)word.
        ival(word_imin x y) = min (ival x) (ival y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_imin; imodular] THEN
  REWRITE_TAC[INT_MIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IWORD_IVAL]);;

let word_shl = new_definition
  `word_shl (x:(N)word) n = word((val x) * 2 EXP n):(N)word`;;

let VAL_WORD_SHL = prove
 (`!(x:N word) n.
        val(word_shl x n) = (2 EXP n * val x) MOD (2 EXP dimindex(:N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; MULT_SYM]);;

let CONG_WORD_SHL = prove
 (`!(x:N word) n.
        (val(word_shl x n) == 2 EXP n * val x) (mod (2 EXP dimindex(:N)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SHL; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

let ICONG_WORD_SHL = prove
 (`!(x:N word) n.
        (ival(word_shl x n) == &2 pow n * ival x) (mod (&2 pow dimindex(:N)))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`x:N word`; `n:num`] CONG_WORD_SHL) THEN
  MAP_EVERY (MP_TAC o C SPEC IVAL_VAL_CONG)
   [`x:N word`; `word_shl x n:N word`] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
  CONV_TAC INTEGER_RULE);;

let BIT_WORD_SHL = prove
 (`!(x:N word) m i.
        bit i (word_shl x n) <=>
        n <= i /\ i < dimindex(:N) /\ bit (i - n) x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[bit]] THEN
  REWRITE_TAC[word_shl; BIT_VAL; VAL_WORD] THEN
  SUBGOAL_THEN `dimindex(:N) = i + (dimindex(:N) - i)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD; GSYM DIV_MOD]] THEN
  ASM_SIMP_TAC[ODD_MOD_POW2; ARITH_RULE `i < n ==> ~(n - i = 0)`] THEN
  ASM_CASES_TAC `n:num <= i` THEN ASM_REWRITE_TAC[] THENL
   [AP_TERM_TAC THEN
    SUBGOAL_THEN `i:num = (i - n) + n`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC DIV_MULT2 THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    SUBGOAL_THEN `n:num = i + (n - i)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ONCE_REWRITE_TAC[MULT_SYM]] THEN
    REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ; EXP_EQ_0] THEN
    REWRITE_TAC[ODD_MULT; ODD_EXP] THEN ASM_ARITH_TAC]);;

let WORD_SHL_WORD_OF_BITS = prove
 (`!(x:N word) n.
        word_shl x n =
        word_of_bits {i | n <= i /\ i < dimindex(:N) /\ bit (i - n) x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[BIT_WORD_SHL] THEN SET_TAC[]);;

let WORD_SHL_ZERO = prove
 (`!x:N word. word_shl x 0 = x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; EXP; MULT_CLAUSES] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let WORD_SHL_COMPOSE = prove
 (`!(x:N word) m n. word_shl (word_shl x m) n = word_shl x (m + n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; EXP_ADD] THEN
  REWRITE_TAC[WORD_EQ; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[MULT_ASSOC]);;

let word_ushr = new_definition
  `word_ushr (x:(N)word) n =
        word((val x) DIV (2 EXP n)):(N)word`;;

let VAL_WORD_USHR = prove
 (`!(x:N word) n.
        val(word_ushr x n) = val x DIV (2 EXP n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD] THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC(ARITH_RULE
   `m DIV n <= m /\ m < p ==> m DIV n < p`) THEN
  REWRITE_TAC[VAL_BOUND; DIV_LE]);;

let WORD_USHR_EQ_0 = prove
 (`!(x:N word) n. word_ushr x n = word 0 <=> val x < 2 EXP n`,
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_USHR] THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let BIT_WORD_USHR = prove
 (`!(x:N word) n i.
        bit i (word_ushr x n) <=> bit (i + n) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ushr; BIT_VAL; VAL_WORD] THEN
  REWRITE_TAC[DIV_MOD; DIV_DIV] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; DIMINDEX_NONZERO] THEN
  ARITH_TAC);;

let WORD_USHR_WORD_OF_BITS = prove
 (`!(x:N word) n.
        word_ushr x n =
        word_of_bits {i | i < dimindex(:N) /\ bit (i + n) x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[BIT_WORD_USHR] THEN SET_TAC[]);;

let WORD_USHR_ZERO = prove
 (`!x:N word. word_ushr x 0 = x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; EXP; DIV_1] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let WORD_USHR_COMPOSE = prove
 (`!(x:N word) m n. word_ushr (word_ushr x m) n = word_ushr x (m + n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_ushr] THEN
  REWRITE_TAC[VAL_WORD_USHR] THEN REWRITE_TAC[EXP_ADD; DIV_DIV]);;

let word_ishr = new_definition
  `(word_ishr:N word ->num->N word) x n = iword((ival x) div (&2 pow n))`;;

let IVAL_WORD_ISHR = prove
 (`!(x:N word) n. ival(word_ishr x n) = (ival x) div (&2 pow n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_ishr] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LT_EQ; INT_LT_POW2] THEN
  MP_TAC(ISPEC `x:N word` IVAL_BOUND) THEN
  MATCH_MP_TAC(INT_ARITH
   `&1 * a:int <= t * a
    ==> --a <= x /\ x < a ==> t * --a <= x /\ x < t * a`) THEN
  MATCH_MP_TAC INT_LE_RMUL THEN
  SIMP_TAC[INT_LE_POW2; INT_LT_IMP_LE; INT_LT_POW2]);;

let WORD_ISHR_EQ_0 = prove
 (`!(x:N word) n.
        word_ishr x n = word 0 <=> &0 <= ival x /\ ival x < &2 pow n`,
  REWRITE_TAC[GSYM IVAL_EQ_0; IVAL_WORD_ISHR] THEN
  SIMP_TAC[INT_DIV_EQ_0; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[INT_ABS_POW; INT_ABS_NUM]);;

let BIT_WORD_ISHR = prove
 (`!(w:N word) n i.
        bit i (word_ishr w n) <=>
        if i + n < dimindex(:N) then bit (i + n) w
        else i < dimindex(:N) /\ bit (dimindex(:N) - 1) w`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[BIT_IVAL] THEN ASM_ARITH_TAC] THEN
  ASM_REWRITE_TAC[word_ishr; BIT_IWORD] THEN
  SIMP_TAC[INT_DIV_DIV; INT_POW_LE; INT_POS] THEN
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN REWRITE_TAC[GSYM INT_POW_ADD] THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC[BIT_IVAL]; ALL_TAC] THEN
  REWRITE_TAC[MSB_IVAL; GSYM INT_NOT_LE] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `--(&2 pow (i + n)) <= ival(w:N word) /\ ival w < &2 pow (i + n)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `w:N word` IVAL_BOUND) THEN MATCH_MP_TAC(INT_ARITH
     `a:int <= b ==> --a <= x /\ x < a ==> --b <= x /\ x < b`) THEN
    MATCH_MP_TAC INT_POW_MONO THEN REWRITE_TAC[INT_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ival(w:N word)`; `(&2:int) pow (i + n)`]
        INT_DIV_EQ_0) THEN
  ASM_REWRITE_TAC[INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_POW;
                  INT_ABS_NUM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `-- &1 <= ival(w:N word) div &2 pow (i + n) /\
    ival(w:N word) div &2 pow (i + n) < &1`
  MP_TAC THENL
   [ASM_SIMP_TAC[INT_DIV_LT_EQ; INT_LE_DIV_EQ; INT_LT_POW2] THEN
    ASM_REWRITE_TAC[INT_MUL_RNEG; INT_MUL_RID];
    REWRITE_TAC[INT_ARITH
     `-- &1:int <= x /\ x < &1 <=> x = -- &1 \/ x = &0`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[INTEGER_RULE `(p:int) divides &0`] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INTEGER_RULE `(x:int) divides --y <=> x divides y`] THEN
    REWRITE_TAC[GSYM num_divides; divides; GSYM EVEN_EXISTS] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let WORD_ISHR_WORD_OF_BITS = prove
 (`!(x:N word) n.
        word_ishr x n =
        word_of_bits {i | if i < dimindex(:N) - n then bit (i + n) x
                          else bit (dimindex(:N) - 1) x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WORD_OF_BITS_ALT] THEN
  REWRITE_TAC[WORD_OF_BITS_EQ] THEN X_GEN_TAC `i:num` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; BIT_WORD_ISHR] THEN
  REWRITE_TAC[ARITH_RULE `i + n:num < m <=> i < m - n`]);;

let WORD_ISHR_ZERO = prove
 (`!x:N word. word_ishr x 0 = x`,
  REWRITE_TAC[GSYM IVAL_EQ; IVAL_WORD_ISHR; INT_POW; INT_DIV_1]);;

let WORD_ISHR_COMPOSE = prove
 (`!(x:N word) m n. word_ishr (word_ishr x m) n = word_ishr x (m + n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[word_ishr] THEN
  REWRITE_TAC[IVAL_WORD_ISHR; INT_POW_ADD] THEN
  SIMP_TAC[INT_DIV_DIV; INT_POW_LE; INT_POS]);;

let word_ror = new_definition
 `(word_ror:N word->num->N word) w n =
        word_of_bits {i | bit ((i + n) MOD dimindex(:N)) w}`;;

let word_rol = new_definition
 `(word_rol:N word->num->N word) w n =
        word_of_bits {i | bit (num_of_int((&i - &n) rem &(dimindex(:N)))) w}`;;

let WORD_ROR_ROL_GEN = prove
 (`!(w:N word) n.
        word_ror w n = word_rol w (dimindex(:N) - n MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror; word_rol; WORD_OF_BITS_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o rand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[INT_DIVISION; DIMINDEX_NONZERO; INT_OF_NUM_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; DIVISION; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(k:int == n) (mod d)
    ==> (i + n == i - (d - k)) (mod d)`) THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let WORD_ROL_ROR_GEN = prove
 (`!(w:N word) n.
        word_rol w n = word_ror w (dimindex(:N) - n MOD dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror; word_rol; WORD_OF_BITS_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INT_OF_NUM_OF_INT o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[INT_DIVISION; DIMINDEX_NONZERO; INT_OF_NUM_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; DIVISION; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_EQ; GSYM INT_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; DIVISION; DIMINDEX_NONZERO] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(k:int == n) (mod d)
    ==> (i - n == i + (d - k)) (mod d)`) THEN
  REWRITE_TAC[CONG_LMOD; INT_OF_NUM_REM; GSYM num_congruent] THEN
  CONV_TAC NUMBER_RULE);;

let WORD_ROR_PERIODIC = prove
 (`!(w:N word) m n.
        (m == n) (mod dimindex(:N)) ==> word_ror w m = word_ror w n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
   `(m == n) (mod d) ==> !i:num. (i + m == i + n) (mod d)`)) THEN
  SIMP_TAC[CONG]);;

let WORD_ROR_MOD = prove
 (`!(w:N word) n. word_ror w n = word_ror w (n MOD dimindex(:N))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
  REWRITE_TAC[CONG_RMOD] THEN CONV_TAC NUMBER_RULE);;

let WORD_ROR_EQ_SELF = prove
 (`!(w:N word) n. dimindex(:N) divides n ==> word_ror w n = w`,
  SIMP_TAC[divides; LEFT_IMP_EXISTS_THM; word_ror] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `i + d * n:num = n * d + i`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOD_MULT_ADD] THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_SIMP_TAC[MOD_LT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[BIT_TRIVIAL; NOT_LE]);;

let WORD_ROR_ZERO = prove
 (`!w:N word. word_ror w 0 = w`,
  GEN_TAC THEN MATCH_MP_TAC WORD_ROR_EQ_SELF THEN CONV_TAC NUMBER_RULE);;

let WORD_ROL_PERIODIC = prove
 (`!(w:N word) m n.
        (m == n) (mod dimindex(:N)) ==> word_rol w m = word_rol w n`,
  SIMP_TAC[CONG; WORD_ROL_ROR_GEN]);;

let WORD_ROL_MOD = prove
 (`!(w:N word) n. word_rol w n = word_rol w (n MOD dimindex(:N))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROL_PERIODIC THEN
  REWRITE_TAC[CONG_RMOD] THEN CONV_TAC NUMBER_RULE);;

let WORD_ROL_EQ_SELF = prove
 (`!(w:N word) n. dimindex(:N) divides n ==> word_rol w n = w`,
  REWRITE_TAC[divides] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[GSYM MOD_EQ_0; WORD_ROL_ROR_GEN; SUB_0] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WORD_ROR_EQ_SELF THEN
  CONV_TAC NUMBER_RULE);;

let WORD_ROL_ZERO = prove
 (`!w:N word. word_rol w 0 = w`,
  GEN_TAC THEN MATCH_MP_TAC WORD_ROL_EQ_SELF THEN CONV_TAC NUMBER_RULE);;

let WORD_ROR_ROL = prove
 (`!(w:N word) n.
        n <= dimindex(:N) ==> word_ror w n = word_rol w (dimindex(:N) - n)`,
  REWRITE_TAC[LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_ROR_ROL_GEN; MOD_LT; MOD_REFL; SUB_0; SUB_REFL] THEN
  MATCH_MP_TAC WORD_ROL_PERIODIC THEN CONV_TAC NUMBER_RULE);;

let WORD_ROL_ROR = prove
 (`!(w:N word) n.
        n <= dimindex(:N) ==> word_rol w n = word_ror w (dimindex(:N) - n)`,
  REWRITE_TAC[LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_ROL_ROR_GEN; MOD_LT; MOD_REFL; SUB_0; SUB_REFL] THEN
  MATCH_MP_TAC WORD_ROR_PERIODIC THEN CONV_TAC NUMBER_RULE);;

let WORD_ROR_SHIFTS = prove
 (`!(w:N word) n.
        n <= dimindex(:N)
        ==> word_ror w n =
            word_or (word_ushr w n) (word_shl w (dimindex(:N) - n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ror] THEN
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OF_BITS; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < dimindex(:N)` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; BIT_WORD_USHR; BIT_WORD_SHL] THEN
  REWRITE_TAC[ARITH_RULE `d - n <= i <=> ~(i + n:num < d)`] THEN
  ASM_CASES_TAC `i + n < dimindex(:N)` THEN ASM_SIMP_TAC[MOD_LT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let WORD_ROL_SHIFTS = prove
 (`!(w:N word) n.
        n <= dimindex(:N)
        ==> word_rol w n =
            word_or (word_shl w n) (word_ushr w (dimindex(:N) - n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_ROL_ROR] THEN
  ASM_SIMP_TAC[WORD_ROR_SHIFTS; ARITH_RULE `n - m:num <= n`] THEN
  ASM_SIMP_TAC[ARITH_RULE `m:num <= n ==> n - (n - m) = m`] THEN
  SIMP_TAC[WORD_EQ_BITS; BIT_WORD_OR; DISJ_SYM]);;

let BIT_WORD_ROR = prove
 (`!(w:N word) n i.
        bit i (word_ror w n) =
        if i + n MOD dimindex(:N) < dimindex(:N)
        then bit (i + n MOD dimindex(:N)) w
        else i < dimindex(:N) /\
             bit ((i + n MOD dimindex(:N)) - dimindex(:N)) w`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ROR_MOD] THEN
  SIMP_TAC[WORD_ROR_SHIFTS; MOD_LT_EQ; LT_IMP_LE; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_USHR] THEN
  COND_CASES_TAC THENL
   [ASM_CASES_TAC `bit (i + n MOD dimindex(:N)) (w:N word)` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p /\ q /\ (r <=> r') ==> (p \/ q /\ r <=> r')`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[BIT_TRIVIAL; GSYM NOT_LT];
      ASM_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]]);;

let BIT_WORD_ROL = prove
 (`!(w:N word) n i.
        bit i (word_rol w n) =
        if i < n MOD dimindex(:N)
        then bit (i + (dimindex(:N) - n MOD dimindex(:N))) w
        else i < dimindex(:N) /\ bit (i - n MOD dimindex(:N)) w`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ROL_MOD] THEN
  SIMP_TAC[WORD_ROL_SHIFTS; MOD_LT_EQ; LT_IMP_LE; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_USHR] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT] THENL
   [MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
    TRANS_TAC LT_TRANS `n MOD dimindex(:N)` THEN
    ASM_REWRITE_TAC[MOD_LT_EQ; DIMINDEX_NONZERO];
    ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(q <=> F) ==> (p \/ q <=> p)`) THEN
    MATCH_MP_TAC BIT_TRIVIAL THEN ASM_ARITH_TAC]);;

let WORD_ROR_COMPOSE = prove
 (`!(x:N word) m n. word_ror (word_ror x m) n = word_ror x (m + n)`,
  REWRITE_TAC[word_ror; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
  SIMP_TAC[MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_AC]);;

let WORD_ROL_COMPOSE = prove
 (`!(x:N word) m n. word_rol (word_rol x m) n = word_rol x (m + n)`,
  REWRITE_TAC[WORD_ROL_ROR_GEN; WORD_ROR_COMPOSE] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORD_ROR_PERIODIC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB; LT_IMP_LE; MOD_LT_EQ; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[INTEGER_RULE
   `((n - a) + (n - b):int == (n - c)) (mod n) <=> (a + b == c) (mod n)`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; GSYM num_congruent; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

let VAL_WORD_ROR = prove
 (`!(w:N word) k.
     k <= dimindex(:N)
     ==> val(word_ror w k) =
         2 EXP (dimindex(:N) - k) * val w MOD 2 EXP k + val w DIV 2 EXP k`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
  ASM_SIMP_TAC[WORD_ROR_SHIFTS] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_OR_DISJOINT o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
    SIMP_TAC[BIT_WORD_AND; BIT_WORD_USHR; BIT_WORD_SHL; BIT_WORD_0] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP(MESON[BIT_TRIVIAL; NOT_LE]
     `bit i (w:N word) ==> i < dimindex(:N)`))) THEN
    ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD_SHL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MOD_MULT2; GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let VAL_WORD_ROL = prove
 (`!(w:N word) k.
        k <= dimindex(:N)
        ==> val(word_rol w k) =
            2 EXP k * val w MOD 2 EXP (dimindex(:N) - k) +
            val w DIV 2 EXP (dimindex(:N) - k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_ROL_ROR] THEN
  SIMP_TAC[VAL_WORD_ROR; ARITH_RULE `n - m:num <= n`] THEN
  ASM_SIMP_TAC[ARITH_RULE `k:num <= n ==> n - (n - k) = k`]);;

let word_ule = new_definition `word_ule = relational2 (<=)`;;
let word_uge = new_definition `word_uge = relational2 (>=)`;;
let word_ult = new_definition `word_ult = relational2 (<)`;;
let word_ugt = new_definition `word_ugt = relational2 (>)`;;

let word_ile = new_definition `word_ile = irelational2 (<=)`;;
let word_ige = new_definition `word_ige = irelational2 (>=)`;;
let word_ilt = new_definition `word_ilt = irelational2 (<)`;;
let word_igt = new_definition `word_igt = irelational2 (>)`;;

(* ------------------------------------------------------------------------- *)
(* Simple "propagate signed value modulo" decision procedure.                *)
(* ------------------------------------------------------------------------- *)

let WORD_RULE =
  let IVAL_WORD_ADD_REM = prove
   (`!x y:N word.
          ival(word_add x y) rem (&2 pow dimindex(:N)) =
          ((ival x rem (&2 pow dimindex(:N))) +
           (ival y rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_ADD_REM] THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_ADD])
  and IVAL_WORD_SUB_REM = prove
   (`!x y:N word.
          ival(word_sub x y) rem (&2 pow dimindex(:N)) =
          ((ival x rem (&2 pow dimindex(:N))) -
           (ival y rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_SUB_REM] THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_SUB])
  and IVAL_WORD_NEG_REM = prove
   (`!x:N word.
          ival(word_neg x) rem (&2 pow dimindex(:N)) =
          (--(ival x rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_NEG_REM] THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_NEG])
  and IVAL_WORD_MUL_REM = prove
   (`!x y:N word.
          ival(word_mul x y) rem (&2 pow dimindex(:N)) =
          ((ival x rem (&2 pow dimindex(:N))) *
           (ival y rem (&2 pow dimindex(:N)))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_MUL_REM] THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_MUL])
  and IVAL_IWORD_REM = prove
   (`!x. ival(iword x:N word) rem (&2 pow dimindex(:N)) =
         x rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_REM_EQ; IVAL_IWORD_CONG])
  and IVAL_WORD_REM = prove
   (`!n. ival(word n:N word) rem (&2 pow dimindex(:N)) =
         &n rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[WORD_IWORD; INT_REM_EQ; IVAL_IWORD_CONG])
  and IVAL_WORD_SHL_REM = prove
   (`!(x:N word) n.
      ival(word_shl x n) rem (&2 pow dimindex(:N)) =
      (&2 pow n * ival x rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N))`,
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ; ICONG_WORD_SHL])
  and INT_OF_NUM_REM = prove
   (`&(x + y) rem (&2 pow dimindex(:N)) =
     (&x rem (&2 pow dimindex(:N)) +
      &y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N)) /\
     &(x * y) rem (&2 pow dimindex(:N)) =
     (&x rem (&2 pow dimindex(:N)) *
      &y rem (&2 pow dimindex(:N))) rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[])
  and INT_OF_NUM_VAL_REM = prove
   (`!x:N word. &(val x) rem (&2 pow dimindex(:N)) =
                ival x rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_VAL_CONG])
  and pth = prove
   (`!v w:N word.
          v = w <=>
          ival v rem (&2 pow dimindex(:N)) = ival w rem (&2 pow dimindex(:N))`,
    REWRITE_TAC[INT_REM_EQ; IVAL_CONG]) in
  let WORD_VAL_EQ_CONV =
    GEN_REWRITE_CONV I [pth] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_NOT_AS_SUB] THENC
    GEN_REWRITE_CONV (BINOP_CONV o TOP_DEPTH_CONV)
     [IVAL_WORD_NEG_REM; IVAL_WORD_ADD_REM; IVAL_WORD_SUB_REM;
      IVAL_WORD_MUL_REM; IVAL_IWORD_REM; IVAL_WORD_REM;
      IVAL_WORD_SHL_REM; INT_OF_NUM_REM; INT_OF_NUM_VAL_REM] THENC
    INT_REM_DOWN_CONV THENC
    GEN_REWRITE_CONV I [INT_REM_EQ] in
  fun tm ->
    let avs,bod = strip_forall tm in
    let th = ONCE_DEPTH_CONV WORD_VAL_EQ_CONV bod in
    GENL avs (EQT_ELIM(TRANS th (EQT_INTRO(NUMBER_RULE (rand(concl th))))));;

(* ------------------------------------------------------------------------- *)
(* A somewhat complementary purely bitwise decision procedure.               *)
(* ------------------------------------------------------------------------- *)

let WORD_BITWISE_TAC =
  let WORD_BITWISE_CONV =
    GEN_REWRITE_CONV I [WORD_EQ_BITS_ALT] THENC
    GEN_REWRITE_CONV (BINDER_CONV o RAND_CONV o BINOP_CONV o TOP_DEPTH_CONV)
     [BIT_WORD_NOT; BIT_WORD_AND; BIT_WORD_OR;
      BIT_WORD_XOR; BIT_WORD_OF_BITS; BIT_WORD_0;
      IN_INSERT; NOT_IN_EMPTY; IN_UNIV] in
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_BITWISE_CONV) THEN
  GEN_REWRITE_TAC DEPTH_CONV
   [MESON[] `(!i. i < dimindex(:N) ==> P i) /\
             (!i. i < dimindex(:N) ==> Q i) <=>
             (!i. i < dimindex(:N) ==> P i /\ Q i)`] THEN
  TRY(MATCH_MP_TAC(MESON[]
       `(!i. i < dimindex(:N) ==> P i ==> Q i)
        ==> (!i. i < dimindex(:N) ==> P i)
             ==> (!i. i < dimindex(:N) ==> Q i)`) ORELSE
      MATCH_MP_TAC(MESON[]
       `(!i. i < dimindex(:N) ==> (P i <=> Q i))
        ==> ((!i. i < dimindex(:N) ==> P i) <=>
             (!i. i < dimindex(:N) ==> Q i))`)) THEN
  TRY(GEN_TAC THEN DISCH_TAC) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC TAUT;;

let WORD_BITWISE_RULE tm = prove(tm,WORD_BITWISE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Slightly ad hoc but useful reduction to linear arithmetic.                *)
(* ------------------------------------------------------------------------- *)

let WORD_ARITH_TAC =
  let wordy tm =
    match tm with Var(_,Tyapp("word",[_])) -> true | _ -> false in
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_NOT_AS_SUB] THEN
  REWRITE_TAC[WORD_RULE `word_shl (x:N word) 1 = word_add x x`] THEN
  REWRITE_TAC[word_ile; word_ule; word_ilt; word_ult;
              word_ige; word_uge; word_igt; word_ugt] THEN
  REWRITE_TAC[irelational2; relational2; GSYM VAL_EQ] THEN
  W(MAP_EVERY (MP_TAC o C ISPEC INT_VAL_BOUND) o find_terms wordy o snd) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT;
              GSYM INT_OF_NUM_GE; GSYM INT_OF_NUM_GT] THEN
  REWRITE_TAC[INT_IVAL; INT_VAL_WORD_NEG_CASES; INT_VAL_WORD_ADD_CASES;
              INT_VAL_WORD_SUB_CASES; VAL_WORD_0; VAL_WORD_1] THEN
  REWRITE_TAC[TWICE_MSB] THEN INT_ARITH_TAC;;

let WORD_ARITH tm = prove(tm,WORD_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Zero extension and sign extension (also works for shortening modulo).     *)
(* ------------------------------------------------------------------------- *)

let word_zx = new_definition
 `(word_zx:(M)word->(N)word) w = word(val w)`;;

let VAL_WORD_ZX_GEN = prove
 (`!x. val((word_zx:(M)word->(N)word) x) = val x MOD 2 EXP dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[word_zx; VAL_WORD]);;

let VAL_WORD_ZX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> val((word_zx:(M)word->(N)word) x) = val x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN] THEN
  MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP dimindex(:M)` THEN
  ASM_REWRITE_TAC[LE_EXP; VAL_BOUND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WORD_ZX_ZX = prove
 (`!w. dimindex(:M) <= dimindex(:N)
       ==> (word_zx:N word->M word) ((word_zx:M word->N word) x) = x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> MIN n m = m`] THEN
  REWRITE_TAC[VAL_MOD_REFL]);;

let WORD_ZX_0 = prove
 (`(word_zx:M word->N word) (word 0) = word 0`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_0; MOD_0]);;

let WORD_ZX_1 = prove
 (`(word_zx:M word->N word) (word 1) = word 1`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_1; MOD_EQ_SELF] THEN
  DISJ2_TAC THEN REWRITE_TAC[ARITH_RULE `1 < n <=> 2 EXP 1 <= n`] THEN
  REWRITE_TAC[LE_EXP; DIMINDEX_GE_1; DIMINDEX_NONZERO] THEN ARITH_TAC);;

let word_sx = new_definition
 `(word_sx:(M)word->(N)word) w = iword(ival w)`;;

let IVAL_WORD_SX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> ival((word_sx:(M)word->(N)word) x) = ival x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IVAL_IWORD; word_sx] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  MP_TAC(ISPEC `x:M word` IVAL_BOUND) THEN
  MATCH_MP_TAC(INT_ARITH
   `m:int <= n ==> --m <= x /\ x < m ==> --n <= x /\ x < n`) THEN
  MATCH_MP_TAC INT_POW_MONO THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

let WORD_SX_SX = prove
 (`!x. dimindex(:M) <= dimindex(:N)
       ==> (word_sx:N word->M word) ((word_sx:M word->N word) x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IVAL_EQ] THEN
  ONCE_REWRITE_TAC[word_sx] THEN ASM_SIMP_TAC[IVAL_WORD_SX; IWORD_IVAL]);;

let WORD_SX_0 = prove
 (`(word_sx:M word->N word) (word 0) = word 0`,
  REWRITE_TAC[GSYM IVAL_EQ; word_sx; IVAL_WORD_0; GSYM WORD_IWORD]);;

(* ------------------------------------------------------------------------- *)
(* Conditional AND and OR, with semantics of C's "&&" and "||"               *)
(* ------------------------------------------------------------------------- *)

let word_cand = new_definition
 `(word_cand:N word->N word->N word) x y =
        if ~(x = word 0) /\ ~(y = word 0) then word 1 else word 0`;;

let word_cor = new_definition
 `(word_cor:N word->N word->N word) x y =
        if ~(x = word 0) \/ ~(y = word 0) then word 1 else word 0`;;

let WORD_CAND = prove
 (`!x y:N word.
        word_cand x y = if x = word 0 \/ y = word 0 then word 0 else word 1`,
  REWRITE_TAC[word_cand] THEN MESON_TAC[]);;

let WORD_COR = prove
 (`!x y:N word.
        word_cor x y = if x = word 0 /\ y = word 0 then word 0 else word 1`,
  REWRITE_TAC[word_cor] THEN MESON_TAC[]);;

let WORD_CAND_NE_0 = prove
 (`!x y:N word.
        ~(word_cand x y = word 0) <=> ~(x = word 0) /\ ~(y = word 0)`,
  REWRITE_TAC[word_cand] THEN MESON_TAC[WORD_NE_10]);;

let WORD_COR_NE_0 = prove
 (`!x y:N word.
        ~(word_cor x y = word 0) <=> ~(x = word 0) \/ ~(y = word 0)`,
  REWRITE_TAC[word_cor] THEN MESON_TAC[WORD_NE_10]);;

let WORD_CAND_EQ_0 = prove
 (`!x y:N word.
        word_cand x y = word 0 <=> x = word 0 \/ y = word 0`,
  REWRITE_TAC[word_cand] THEN MESON_TAC[WORD_NE_10]);;

let WORD_COR_EQ_0 = prove
 (`!x y:N word.
        word_cor x y = word 0 <=> x = word 0 /\ y = word 0`,
  REWRITE_TAC[word_cor] THEN MESON_TAC[WORD_NE_10]);;

let VAL_WORD_CAND = prove
 (`!x y:N word.
        val(word_cand x y) =
        if ~(val x = 0) /\ ~(val y = 0) then 1 else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cand; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; VAL_WORD_1]);;

let VAL_WORD_COR = prove
 (`!x y:N word.
        val(word_cor x y) =
        if ~(val x = 0) \/ ~(val y = 0) then 1 else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cor; VAL_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0; VAL_WORD_1]);;

let BIT_WORD_CAND = prove
 (`!i x y:N word.
        bit i (word_cand x y) <=> i = 0 /\ ~(x = word 0) /\ ~(y = word 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cand] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_0; BIT_WORD_1]);;

let BIT_WORD_COR = prove
 (`!i x y:N word.
        bit i (word_cor x y) <=> i = 0 /\ (~(x = word 0) \/ ~(y = word 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_cor] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BIT_WORD_0; BIT_WORD_1]);;

(* ------------------------------------------------------------------------- *)
(* Joining, in a somewhat (over?) general sense; v is the high part, w low.  *)
(* ------------------------------------------------------------------------- *)

let word_join = new_definition
 `(word_join:(M)word->(N)word->(P)word) v w =
        word(2 EXP dimindex(:N) * val v + val w)`;;

let VAL_WORD_JOIN = prove
 (`!v w. val((word_join:(M)word->(N)word->(P)word) v w) =
         (2 EXP dimindex(:N) * val v + val w) MOD 2 EXP dimindex(:P)`,
  REWRITE_TAC[word_join; VAL_WORD]);;

let BIT_WORD_JOIN = prove
 (`!v w i.
        bit i ((word_join:(M)word->(N)word->(P)word) v w) <=>
        i < dimindex(:P) /\
        (if i < dimindex(:N) then bit i w else bit (i - dimindex(:N)) v)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i < dimindex(:P)` THEN
  ASM_SIMP_TAC[BIT_TRIVIAL; GSYM NOT_LT] THEN
  REWRITE_TAC[word_join; BIT_WORD] THEN ASM_REWRITE_TAC[BIT_VAL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [REWRITE_TAC[ODD_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DIV_MOD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
     `d divides e ==> (e * v + w:num == w) (mod d)`) THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    UNDISCH_TAC `i < dimindex(:N)` THEN
    SIMP_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[ARITH_RULE `i + SUC d = SUC i + d`] THEN
    REWRITE_TAC[EXP_ADD; NUMBER_RULE `(a:num) divides a * b`];
    AP_TERM_TAC THEN
    SUBGOAL_THEN `2 EXP i = 2 EXP (dimindex(:N) + i - dimindex(:N))`
    SUBST1_TAC THENL [AP_TERM_TAC THEN ASM_ARITH_TAC; SIMP_TAC[EXP_ADD]] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]]);;

let VAL_WORD_JOIN_SIMPLE = prove
 (`!v w.
        dimindex(:M) + dimindex(:N) = dimindex(:P)
        ==> val((word_join:(M)word->(N)word->(P)word) v w) =
            2 EXP dimindex(:N) * val v + val w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_JOIN] THEN
  MATCH_MP_TAC MOD_LT THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  TRANS_TAC LTE_TRANS
   `2 EXP dimindex(:N) * (2 EXP dimindex(:M) - 1) + 2 EXP dimindex(:N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LET_ADD2 THEN REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN
    DISJ2_TAC THEN MATCH_MP_TAC(ARITH_RULE `a < b ==> a <= b - 1`) THEN
    REWRITE_TAC[VAL_BOUND];
    REWRITE_TAC[LEFT_SUB_DISTRIB; EXP_ADD] THEN MATCH_MP_TAC(ARITH_RULE
     `n * 1 <= n * m ==> n * m - n * 1 + n <= m * n`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Subwords, where the (pos,len) argument is (lsb_position,length)           *)
(* ------------------------------------------------------------------------- *)

let word_subword = new_definition
 `word_subword (w:M word) (pos,len):N word =
        word((val w DIV (2 EXP pos)) MOD (2 EXP len))`;;

let VAL_WORD_SUBWORD = prove
 (`!pos len w:M word.
        val(word_subword w (pos,len):N word) =
        (val w DIV (2 EXP pos)) MOD (2 EXP (MIN len (dimindex(:N))))`,
  REWRITE_TAC[word_subword; VAL_WORD; MOD_MOD_EXP_MIN]);;

let BIT_WORD_SUBWORD = prove
 (`!pos len (w:M word) i.
        bit i (word_subword w (pos,len):N word) <=>
        i < MIN len (dimindex(:N)) /\ bit (pos + i) w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `m < MIN p q <=> m < p /\ m < q`] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN
  ASM_SIMP_TAC[GSYM NOT_LT; BIT_TRIVIAL] THEN
  ASM_REWRITE_TAC[word_subword; BIT_WORD] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; BIT_VAL; DIV_DIV] THEN
  ASM_CASES_TAC `i:num < len` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `i:num < len` THEN
    SIMP_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:num` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ADD_ASSOC] THEN
    SPEC_TAC(`pos + i:num`,`j:num`) THEN REWRITE_TAC[EXP_ADD] THEN
    REWRITE_TAC[GSYM DIV_MOD; ODD_MOD_POW2; NOT_SUC];
    MATCH_MP_TAC(MESON[ODD] `n = 0 ==> ~ODD n`) THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP (pos + len)` THEN
    SIMP_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN
    ASM_ARITH_TAC]);;

let WORD_SUBWORD_0 = prove
 (`!pos len. word_subword (word 0) (pos,len) = word 0`,
  REWRITE_TAC[word_subword; VAL_WORD_0; DIV_0; MOD_0]);;

let WORD_SUBWORD_JOIN_SELF = prove
 (`!(w:N word) k.
        k <= dimindex(:N)
        ==> word_subword (word_join w w:(N tybit0)word) (k,dimindex(:N)) =
            word_ror w k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_JOIN; BIT_WORD_ROR;
              DIMINDEX_TYBIT0; ARITH_RULE `MIN n n = n`] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC o MATCH_MP (ARITH_RULE
   `k:num <= n ==> k = n \/ k < n`)) THEN
  ASM_SIMP_TAC[MOD_REFL; MOD_LT; ADD_CLAUSES;
               ARITH_RULE `(n + i) - n:num = i`;
               ARITH_RULE `~(n + i:num < n)`;
               ARITH_RULE `i < n ==> n + i < 2 * n`] THEN
  REWRITE_TAC[ADD_SYM; TAUT `(p /\ q <=> q) <=> q ==> p`] THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bit recursion equations for "linear" operations.                          *)
(* ------------------------------------------------------------------------- *)

let BIT_WORD_ADD = prove
 (`!x (y:N word) i.
        bit i (word_add x y) <=>
        i < dimindex(:N) /\
        ((bit i x <=> bit i y) <=>
         ~(i = 0) /\
         (bit (i - 1) x /\ bit (i - 1) y \/
          (bit (i - 1) x \/ bit (i - 1) y) /\
          ~(bit (i - 1) (word_add x y))))`,
  let lemma = prove
   (`2 EXP i <= (2 EXP i * b + x) MOD 2 EXP (i + 1) <=>
     (EVEN b <=> 2 EXP i <= x MOD (2 EXP (i + 1)))`,
    SIMP_TAC[EXP_ADD; EXP_1; MOD_MULT_MOD; EXP_EQ_0; ARITH_EQ;
             DIV_MULT_ADD; MOD_MULT_ADD] THEN
    REWRITE_TAC[MOD_2_CASES; EVEN_ADD] THEN
    MAP_EVERY ASM_CASES_TAC [`EVEN b`; `EVEN(x DIV 2 EXP i)`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LE_ADD; NOT_LE] THEN
    SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `i < dimindex(:N)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[NOT_LT; BIT_TRIVIAL]] THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_VAL_MOD] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [BIT_VAL_MOD] THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD; MOD_MOD_EXP_MIN] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [TAUT `~p /\ q <=> ~(~p ==> ~q)`] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; ARITH_RULE
    `~(k = 0) /\ k < n ==> MIN n (k - 1 + 1) = k`] THEN
  ASM_SIMP_TAC[NOT_IMP; ARITH_RULE `k < n ==> MIN n (k + 1) = k + 1`] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[VAL_MOD_STEP; lemma; ARITH_RULE
   `(k * b + x) + (k * c + y):num = k * (b + c) + x + y`] THEN
  BINOP_TAC THENL
   [MAP_EVERY ASM_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    SIMP_TAC[EXP_ADD; EXP_1; MOD_LT; DIVISION; EXP_EQ_0; ARITH_EQ;
             ARITH_RULE `x < n /\ y < n ==> x + y < n * 2`]] THEN
  ASM_CASES_TAC `i = 0` THEN
  ASM_SIMP_TAC[EXP; MOD_1; ADD_CLAUSES; CONJUNCT1 LE;
               EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[MOD_ADD_CASES; DIVISION; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[GSYM NOT_LE] THEN
  MAP_EVERY ABBREV_TAC
   [`m = val(x:N word) MOD 2 EXP i`; `n = val(y:N word) MOD 2 EXP i`] THEN
  SUBGOAL_THEN `m < 2 EXP i /\ n < 2 EXP i` MP_TAC THENL
   [ASM_MESON_TAC[DIVISION; EXP_EQ_0; ARITH_RULE `~(2 = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP i = 2 * 2 EXP(i - 1)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM(CONJUNCT2 EXP); ADD1; SUB_ADD; LE_1];
    ABBREV_TAC `j = i - 1` THEN
    REWRITE_TAC[COND_SWAP; NOT_LE] THEN ASM_ARITH_TAC]);;

let BIT_WORD_SUB = prove
 (`!x (y:N word) i.
        bit i (word_sub x y) <=>
        i < dimindex(:N) /\
        ((bit i x <=> bit i y) <=>
         ~(i = 0) /\
         (~bit (i - 1) x /\ bit (i - 1) y \/
          (~bit (i - 1) x \/ bit (i - 1) y) /\
          bit (i - 1) (word_sub x y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_RULE
   `word_sub x y:N word = word_not(word_add (word_not x) y)`] THEN
  REWRITE_TAC[BIT_WORD_NOT] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [BIT_WORD_ADD] THEN
  ASM_SIMP_TAC[BIT_WORD_NOT; ARITH_RULE `i < n ==> i - 1 < n`] THEN
  REWRITE_TAC[TAUT `~((~p <=> q) <=> r) <=> ((p <=> q) <=> r)`]);;

let BIT_WORD_NEG = prove
 (`!(x:N word) i.
        bit i (word_neg x) <=>
        i < dimindex(:N) /\
        (bit i x <=> i = 0 \/ ~bit (i - 1) x /\ ~bit (i - 1) (word_neg x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_RULE `word_neg x:N word = word_sub (word 0) x`] THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_SUB] THEN
  REWRITE_TAC[BIT_WORD_0] THEN CONV_TAC TAUT);;

let BIT_WORD_ADD_CLAUSES = prove
 (`(!x (y:N word).
        bit 0 (word_add x y) <=> ~(bit 0 x <=> bit 0 y)) /\
   (!x (y:N word) i.
        bit (i + 1) (word_add x y) <=>
        i + 1 < dimindex(:N) /\
        ((bit (i + 1) x <=> bit (i + 1) y) <=>
         (bit i x /\ bit i y \/
          (bit i x \/ bit i y) /\ ~(bit i (word_add x y)))))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_ADD] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_SUB; ADD_EQ_0; ARITH_EQ]);;

let BIT_WORD_SUB_CLAUSES = prove
 (`(!x (y:N word).
        bit 0 (word_sub x y) <=> ~(bit 0 x <=> bit 0 y)) /\
   (!x (y:N word) i.
        bit (i + 1) (word_sub x y) <=>
        i + 1 < dimindex(:N) /\
        ((bit (i + 1) x <=> bit (i + 1) y) <=>
         (~bit i x /\ bit i y \/
          (~bit i x \/ bit i y) /\ bit i (word_sub x y))))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_SUB] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_SUB; ADD_EQ_0; ARITH_EQ]);;

let BIT_WORD_NEG_CLAUSES = prove
 (`(!(x:N word).
        bit 0 (word_neg x) = bit 0 x) /\
   (!(x:N word) i.
        bit (i + 1) (word_neg x) <=>
        i + 1 < dimindex(:N) /\
        (bit (i + 1) x <=> ~bit i x /\ ~bit i (word_neg x)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIT_WORD_NEG] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1; ADD_SUB; ADD_EQ_0; ARITH_EQ]);;

let LE_VAL_MOD_STEP = prove
 (`!(x:N word) (y:N word) i.
        (val x MOD 2 EXP (i + 1)) <= (val y MOD 2 EXP (i + 1)) <=>
        ~bit i x /\ bit i y \/
        (bit i x <=> bit i y) /\ val x MOD 2 EXP i <= val y MOD 2 EXP i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_MOD_STEP] THEN
  MAP_EVERY BOOL_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[LE_ADD_LCANCEL; NOT_LE] THEN TRY(MATCH_MP_TAC LT_IMP_LE) THEN
  MATCH_MP_TAC(ARITH_RULE `x:num < y ==> x < y + z`) THEN
  SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]);;

let LT_VAL_MOD_STEP = prove
 (`!(x:N word) (y:N word) i.
        (val x MOD 2 EXP (i + 1)) < (val y MOD 2 EXP (i + 1)) <=>
        ~bit i x /\ bit i y \/
        (bit i x <=> bit i y) /\ val x MOD 2 EXP i < val y MOD 2 EXP i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_MOD_STEP] THEN
  MAP_EVERY BOOL_CASES_TAC [`bit i (x:N word)`; `bit i (y:N word)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[LT_ADD_LCANCEL; NOT_LT] THEN TRY(MATCH_MP_TAC LT_IMP_LE) THEN
  MATCH_MP_TAC(ARITH_RULE `x:num < y ==> x < y + z`) THEN
  SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Miscellaneous lemmas we don't want to keep regenerating. Many of them in  *)
(* any case need a little bit of manual effort.                              *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD_0 = prove
 (`(!x:N word. word_add x (word 0) = x) /\
   (!x:N word. word_add (word 0) x = x)`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_SYM = prove
 (`!x y:N word. word_add x y = word_add y x`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_ASSOC = prove
 (`!x y z:N word. word_add x (word_add y z) =
                  word_add (word_add x y) z`,
  CONV_TAC WORD_RULE);;

let WORD_ADD_AC = prove
 (`word_add x y = word_add y x /\
   word_add (word_add x y) z = word_add x (word_add y z) /\
   word_add x (word_add y z) = word_add y (word_add x z)`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_0 = prove
 (`(!x:N word. word_mul x (word 0) = word 0) /\
   (!x:N word. word_mul (word 0) x = word 0)`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_SYM = prove
 (`!x y:N word. word_mul x y = word_mul y x`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_ASSOC = prove
 (`!x y z:N word. word_mul x (word_mul y z) =
                  word_mul (word_mul x y) z`,
  CONV_TAC WORD_RULE);;

let WORD_MUL_AC = prove
 (`word_mul x y = word_mul y x /\
   word_mul (word_mul x y) z = word_mul x (word_mul y z) /\
   word_mul x (word_mul y z) = word_mul y (word_mul x z)`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_0 = prove
 (`!x:N word. word_sub x (word 0) = x`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_LZERO = prove
 (`!x:N word. word_sub (word 0) x = word_neg x`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_EQ_0 = prove
 (`!x y:N word. word_sub x y = word 0 <=> x = y`,
  CONV_TAC WORD_RULE);;

let WORD_SUB_REFL = prove
 (`!x:N word. word_sub x x = word 0`,
  CONV_TAC WORD_RULE);;

let WORD_NEG_0 = prove
 (`word_neg (word 0) = word 0`,
  CONV_TAC WORD_RULE);;

let WORD_NEG_EQ_0 = prove
 (`!x:N word. word_neg x = word 0 <=> x = word 0`,
  CONV_TAC WORD_RULE);;

let WORD_AND_REFL = prove
 (`!x:N word. word_and x x = x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_0 = prove
 (`(!x:N word. word_and x (word 0) = word 0) /\
   (!x:N word. word_and (word 0) x = word 0)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_NOT0 = prove
 (`(!x:N word. word_and x (word_not(word 0)) = x) /\
   (!x:N word. word_and (word_not(word 0)) x = x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_SYM = prove
 (`!x y:N word. word_and x y = word_and y x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_REFL = prove
 (`!x:N word. word_or x x = x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_0 = prove
 (`(!x:N word. word_or x (word 0) = x) /\
   (!x:N word. word_or (word 0) x = x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_NOT0 = prove
 (`(!x:N word. word_or x (word_not(word 0)) = word_not(word 0)) /\
   (!x:N word. word_or (word_not(word 0)) x = word_not(word 0))`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_SYM = prove
 (`!x y:N word. word_or x y = word_or y x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_OR_EQ_0 = prove
 (`!x y:N word. word_or x y = word 0 <=> x = word 0 /\ y = word 0`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_EQ_0 = prove
 (`!x y:N word. word_xor x y = word 0 <=> x = y`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_0 = prove
 (`(!x:N word. word_xor x (word 0) = x) /\
   (!x:N word. word_xor (word 0) x = x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_NOT0 = prove
 (`(!x:N word. word_xor x (word_not(word 0)) = word_not x) /\
   (!x:N word. word_xor (word_not(word 0)) x = word_not x)`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_XOR_REFL = prove
 (`!x:N word. word_xor x x = word 0`,
  REWRITE_TAC[WORD_XOR_EQ_0]);;

let WORD_XOR_SYM = prove
 (`!x y:N word. word_xor x y = word_xor y x`,
  CONV_TAC WORD_BITWISE_RULE);;

let WORD_AND_1 = prove
 (`(!x:N word. word_and x (word 1) = if bit 0 x then word 1 else word 0) /\
   (!x:N word. word_and (word 1) x = if bit 0 x then word 1 else word 0)`,
  REWRITE_TAC[WORD_BITWISE_RULE
   `word_and (word 1:N word) x = word_and x (word 1)`] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_1; BIT_WORD_0] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = 0` THEN
  ASM_REWRITE_TAC[BIT_WORD_0] THEN SIMP_TAC[DIMINDEX_GE_1; LE_1]);;

let WORD_NOT_NEG = prove
 (`!x:N word. word_not(word_neg x) = word_sub x (word 1)`,
  GEN_TAC THEN REWRITE_TAC[WORD_NOT_AS_SUB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let WORD_NOT_SUB = prove
 (`!x y:N word.
        word_not(word_sub x y) = word_add (word_not x) y`,
  REWRITE_TAC[WORD_NOT_AS_SUB] THEN CONV_TAC WORD_RULE);;

let WORD_NOT_ADD = prove
 (`!x y:N word.
        word_not(word_add x y) = word_add (word_not x) (word_neg y)`,
  REWRITE_TAC[WORD_NOT_AS_SUB] THEN CONV_TAC WORD_RULE);;

let WORD_SHL_AND = prove
 (`!(v:N word) w n.
        word_shl (word_and v w) n =
        word_and (word_shl v n) (word_shl w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_SHL; BIT_WORD_AND] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `bit (i - n) (v:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i - n) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let WORD_USHR_AND = prove
 (`!(v:N word) w n.
        word_ushr (word_and v w) n =
        word_and (word_ushr v n) (word_ushr w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_AND] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i + n < dimindex(:N)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_SHL_OR = prove
 (`!(v:N word) w n.
        word_shl (word_or v w) n =
        word_or (word_shl v n) (word_shl w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_SHL; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `bit (i - n) (v:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i - n) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let WORD_USHR_OR = prove
 (`!(v:N word) w n.
        word_ushr (word_or v w) n =
        word_or (word_ushr v n) (word_ushr w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_OR] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i + n < dimindex(:N)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_SHL_XOR = prove
 (`!(v:N word) w n.
        word_shl (word_xor v w) n =
        word_xor (word_shl v n) (word_shl w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_SHL; BIT_WORD_XOR] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `bit (i - n) (v:N word)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `bit (i - n) (w:N word)` THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let WORD_USHR_XOR = prove
 (`!(v:N word) w n.
        word_ushr (word_xor v w) n =
        word_xor (word_ushr v n) (word_ushr w n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_USHR; BIT_WORD_XOR] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i + n < dimindex(:N)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN ASM_SIMP_TAC[BIT_TRIVIAL] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let WORD_ADD_XOR_GEN = prove
 (`!x y:N word.
        word_add x y = word_add (word_shl (word_and x y) 1) (word_xor x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_ADD; VAL_WORD_SHL] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXP_1; VAL_WORD_ADD_AND_XOR]);;

let WORD_ADD_OR_GEN = prove
 (`!x y:N word. word_add x y = word_add (word_and x y) (word_or x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_ADD; VAL_WORD_SHL] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_WORD_ADD_AND_OR]);;

let WORD_OR_XOR_GEN = prove
 (`!x y:N word. word_or x y = word_add (word_and x y) (word_xor x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_CONG; CONG; VAL_WORD_ADD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[VAL_WORD_OR_AND_XOR]);;

let WORD_ADD_XOR = prove
 (`!x y:N word. word_and x y = word 0 ==> word_add x y = word_xor x y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_ADD_XOR_GEN] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

let WORD_OR_XOR = prove
 (`!x y:N word. word_and x y = word 0 ==> word_or x y = word_xor x y`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[WORD_OR_XOR_GEN] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_OR = prove
 (`!x y:N word. word_and x y = word 0 ==> word_add x y = word_or x y`,
  SIMP_TAC[WORD_OR_XOR; WORD_ADD_XOR]);;

let WORD_XOR_INT_MIN = prove
 (`!w:N word. word_xor word_INT_MIN w = word_add word_INT_MIN w`,
  GEN_TAC THEN ONCE_REWRITE_TAC[WORD_ADD_XOR_GEN] THEN
  REWRITE_TAC[WORD_RULE `w:N word = word_add x w <=> x = word 0`] THEN
  REWRITE_TAC[WORD_SHL_AND] THEN
  MATCH_MP_TAC(WORD_BITWISE_RULE `x = word 0 ==> word_and x y = word 0`) THEN
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_0; BIT_WORD_SHL; BIT_WORD_INT_MIN] THEN
  ARITH_TAC);;

let WORD_BITVAL_NOT = prove
 (`!b. word(bitval(~b)) = word_sub (word 1) (word(bitval b))`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE);;

let IVAL_WORD_NOT = prove
 (`!x:N word. ival(word_not x) = --(ival x + &1)`,
  REWRITE_TAC[IVAL_IWORD_GALOIS] THEN
  REWRITE_TAC[INT_ARITH `--x:int <= --(y + &1) <=> y < x`] THEN
  REWRITE_TAC[INT_ARITH `--(x + &1):int < y <=> --y <= x`] THEN
  REWRITE_TAC[IVAL_BOUND] THEN
  REWRITE_TAC[IWORD_INT_NEG; IWORD_INT_ADD; IWORD_IVAL; GSYM WORD_IWORD] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas about masks 000..001111..1111 and their values.               *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_AND_MASK = prove
 (`!(x:N word) k.
        val(word_and x (word_of_bits {i | i < k})) = val x MOD (2 EXP k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[val_def] THEN
  SIMP_TAC[BINARY_DIGITSUM_MOD; FINITE_NUMSEG_LT; NSUM_RESTRICT_SET] THEN
  MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; BIT_WORD_AND; IN_ELIM_THM; BIT_WORD_OF_BITS] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bitval] THEN ARITH_TAC);;

let IVAL_WORD_AND_MASK = prove
 (`!(x:N word) k.
        k < dimindex(:N)
        ==> ival(word_and x (word_of_bits {i | i < k})) =
            ival x rem (&2 pow k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INT_REM_IVAL; LT_IMP_LE] THEN
  REWRITE_TAC[GSYM VAL_WORD_AND_MASK; ival] THEN
  MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK] THEN TRANS_TAC LTE_TRANS `2 EXP k` THEN
  SIMP_TAC[DIVISION; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC);;

let VAL_WORD_AND_MASK_WORD = prove
 (`!x k. val(word_and x (word(2 EXP k - 1))) = val x MOD 2 EXP k`,
  REWRITE_TAC[GSYM WORD_OF_BITS_MASK; VAL_WORD_AND_MASK]);;

let WORD_BITMASK = prove
 (`!k. word_of_bits {i | i < k}:N word =
       word_sub (word_of_bits {k}) (word 1)`,
  REWRITE_TAC[WORD_OF_BITS_MASK; WORD_OF_BITS_SING_AS_WORD] THEN
  REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ]);;
