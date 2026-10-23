(* ========================================================================= *)
(* 4CT/chromogram.ml                                                         *)
(*                                                                           *)
(* chromogram.v: chromograms (words over Gpush/Gskip/Gpop0/Gpop1 encoding    *)
(* the chords of a Kempe inversion class), the matching predicate matchg of  *)
(* a chromogram against an edge colouring trace, balance (gram_balanced),    *)
(* the Kempe closure notions, and the algorithmic matching matchpg of a      *)
(* partial trace against a partial chromogram with a bit stack.  The main    *)
(* theorems are MATCHG_BALANCED (a matching trace has a balanced chromogram) *)
(* and MATCHG_PG (matchg on the completed trace and chromogram agrees with   *)
(* matchpg), both by one induction over the trace with a brute-force case    *)
(* split over the symbol, the colour and the top of the bit stack.           *)
(* ========================================================================= *)

needs "4CT/general.ml";;
needs "4CT/color.ml";;

(* ------------------------------------------------------------------------- *)
(* Chromogram symbols, balance and matching.                                 *)
(* ------------------------------------------------------------------------- *)

let gram_symbol_INDUCT,gram_symbol_RECURSION =
  define_type "gram_symbol = Gpush | Gskip | Gpop0 | Gpop1";;

let GRAM_DISTINCT = distinctness "gram_symbol";;
let GRAM_CASES = cases "gram_symbol";;

let gram_balanced = define
 `(gram_balanced d b ([] : gram_symbol list) <=> (d = 0 /\ ~b)) /\
  (gram_balanced d b (CONS s w) <=>
     if s = Gpush then gram_balanced (d + 1) b w
     else if s = Gskip then gram_balanced d (~b) w
     else if s = Gpop0 then (~(d = 0) /\ gram_balanced (d - 1) b w)
     else (~(d = 0) /\ gram_balanced (d - 1) (~b) w))`;;

let matchg = define
 `(matchg (lb:bool list) (et:color list) ([] : gram_symbol list) <=>
    (et:color list) = [] /\ (lb:bool list) = []) /\
  (matchg lb et (CONS (s:gram_symbol) (w:gram_symbol list)) <=>
    ~(et = []) /\
    (if s = Gskip then HD et = Color1 /\ matchg lb (TL et) w
     else if s = Gpush then
       ~(HD et = Color0) /\ ~(HD et = Color1) /\
       matchg (CONS (cbit0 (HD et)) lb) (TL et) w
     else if s = Gpop0 then
       ~(lb = []) /\ ~(HD et = Color0) /\ ~(HD et = Color1) /\
       (cbit0 (HD et) <=> HD lb) /\
       matchg (TL lb) (TL et) w
     else
       ~(lb = []) /\ ~(HD et = Color0) /\ ~(HD et = Color1) /\
       ~(cbit0 (HD et) <=> HD lb) /\
       matchg (TL lb) (TL et) w))`;;

let kempe_closed = new_definition
 `kempe_closed (P : color list -> bool) <=>
    !et. P et ==>
      (!g. P (permt g et)) /\
      (?w. matchg [] et w /\ !et'. matchg [] et' w ==> P et')`;;

let kempe_coclosure = new_definition
 `kempe_coclosure P et <=>
    !P'. kempe_closed P' /\ P' et ==> ?et'. P et' /\ P' et'`;;

(* ------------------------------------------------------------------------- *)
(* The algorithmic side: bit stacks, completion of a partial chromogram,     *)
(* matching of partial traces, and the parity of a bit list.                 *)
(* ------------------------------------------------------------------------- *)

let bit_stack_INDUCT,bit_stack_RECURSION =
  define_type "bit_stack = Bstack0 | Bpush0 bit_stack | Bpush1 bit_stack";;

let stack_of_bitseq = define
 `(stack_of_bitseq ([] : bool list) = Bstack0) /\
  (stack_of_bitseq (CONS b bs) =
    if b then Bpush1 (stack_of_bitseq bs)
    else Bpush0 (stack_of_bitseq bs))`;;

let cgram = define
 `(cgram d b ([] : gram_symbol list) : gram_symbol list =
    [if d = 0 then Gskip else if b then Gpop1 else Gpop0]) /\
  (cgram d b (CONS s w) =
    CONS s (if s = Gpush then cgram (d + 1) b w
            else if s = Gskip then cgram d (~b) w
            else if s = Gpop0 then cgram (d - 1) b w
            else cgram (d - 1) (~b) w))`;;

let matchpg = define
 `(matchpg bs ([] : color list) ([] : gram_symbol list) <=> T) /\
  (matchpg bs ([] : color list) (CONS s (w:gram_symbol list)) <=> F) /\
  (matchpg bs (CONS e (et:color list)) ([] : gram_symbol list) <=> F) /\
  (matchpg bs (CONS e et) (CONS s (w:gram_symbol list)) <=>
    if s = Gskip /\ e = Color1 then matchpg bs et w
    else if s = Gpush /\ e = Color2 then matchpg (Bpush0 bs) et w
    else if s = Gpush /\ e = Color3 then matchpg (Bpush1 bs) et w
    else if s = Gpop0 /\ e = Color2 then
      (?bs'. bs = Bpush0 bs' /\ matchpg bs' et w)
    else if s = Gpop0 /\ e = Color3 then
      (?bs'. bs = Bpush1 bs' /\ matchpg bs' et w)
    else if s = Gpop1 /\ e = Color2 then
      (?bs'. bs = Bpush1 bs' /\ matchpg bs' et w)
    else if s = Gpop1 /\ e = Color3 then
      (?bs'. bs = Bpush0 bs' /\ matchpg bs' et w)
    else F)`;;

let sumb = define
 `(sumb ([] : bool list) <=> F) /\
  (sumb (CONS b bs) <=> ~(b <=> sumb bs))`;;

(* ------------------------------------------------------------------------- *)
(* Small computation rules: the colour bits, addition of a colour to a bit   *)
(* pair, parity and stack of a bit list, iff normalisation, and the case     *)
(* split of a bit list by its head.                                          *)
(* ------------------------------------------------------------------------- *)

let CBIT_CLAUSES = prove
 (`(cbit0 Color0 <=> F) /\ (cbit0 Color1 <=> T) /\
   (cbit0 Color2 <=> F) /\ (cbit0 Color3 <=> T) /\
   (cbit1 Color0 <=> F) /\ (cbit1 Color1 <=> F) /\
   (cbit1 Color2 <=> T) /\ (cbit1 Color3 <=> T)`,
  REWRITE_TAC[cbit0; cbit1; distinctness "color"]);;

let ADDC_0_RIGHT = prove
 (`!c. addc c Color0 = c`,
  REWRITE_TAC[ADDC_0]);;

let ADDC_CCONS = prove
 (`(!p q. addc (ccons p q) Color0 = ccons p q) /\
   (!p q. addc (ccons p q) Color1 = ccons p (~q)) /\
   (!p q. addc (ccons p q) Color2 = ccons (~p) q) /\
   (!p q. addc (ccons p q) Color3 = ccons (~p) (~q))`,
  REPEAT STRIP_TAC THEN BOOL_CASES_TAC `p:bool` THEN
  BOOL_CASES_TAC `q:bool` THEN REWRITE_TAC[ccons; addc_DEF]);;

let SUMB_F = prove
 (`!lb. sumb(CONS F lb) <=> sumb lb`,
  REWRITE_TAC[sumb]);;

let SUMB_T = prove
 (`!lb. sumb(CONS T lb) <=> ~(sumb lb)`,
  REWRITE_TAC[sumb]);;

let STACK_PUSH_F = prove
 (`!lb. stack_of_bitseq(CONS F lb) = Bpush0(stack_of_bitseq lb)`,
  REWRITE_TAC[stack_of_bitseq]);;

let STACK_PUSH_T = prove
 (`!lb. stack_of_bitseq(CONS T lb) = Bpush1(stack_of_bitseq lb)`,
  REWRITE_TAC[stack_of_bitseq]);;

let IFF_NEG_NORM = TAUT
 `((~p <=> q) <=> ~(p <=> q)) /\ ((p <=> ~q) <=> ~(p <=> q))`;;

let BOOL_LIST_CASES = prove
 (`!l:bool list. l = [] \/ (?t. l = CONS F t) \/ (?t. l = CONS T t)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:bool list` list_CASES) THEN
  TRY(BOOL_CASES_TAC `h:bool`) THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sizes, absence of Color0, and the length of a completed chromogram.       *)
(* ------------------------------------------------------------------------- *)

let MATCHG_SIZE = prove
 (`!w et lb. matchg lb et w ==> LENGTH w = LENGTH et`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[matchg] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL; LENGTH; SUC_INJ] THEN
  STRUCT_CASES_TAC(SPEC `h:gram_symbol` GRAM_CASES) THEN
  REWRITE_TAC[GRAM_DISTINCT] THEN ASM_MESON_TAC[]);;

let MATCHG_MEMC0 = prove
 (`!w et lb. matchg lb et w ==> ~(MEM Color0 et)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[matchg] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL; MEM] THEN
  STRUCT_CASES_TAC(SPEC `h:gram_symbol` GRAM_CASES) THEN
  REWRITE_TAC[GRAM_DISTINCT] THEN ASM_MESON_TAC[distinctness "color"]);;

let MATCHPG_SIZE = prove
 (`!w et bs. matchpg bs et w ==> LENGTH w = LENGTH et`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THEN
  REWRITE_TAC[matchpg; LENGTH; SUC_INJ] THEN
  STRUCT_CASES_TAC(SPEC `h:gram_symbol` GRAM_CASES) THEN
  STRUCT_CASES_TAC(SPEC `h':color` (cases "color")) THEN
  REWRITE_TAC[GRAM_DISTINCT; distinctness "color"] THEN ASM_MESON_TAC[]);;

let LENGTH_CGRAM = prove
 (`!w d b. LENGTH(cgram d b w) = LENGTH w + 1`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[cgram; LENGTH] THENL
   [ARITH_TAC;
    STRUCT_CASES_TAC(SPEC `h:gram_symbol` GRAM_CASES) THEN
    ASM_REWRITE_TAC[GRAM_DISTINCT; LENGTH] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Balance: it determines the context, a balanced chromogram is the          *)
(* completion of its own prefix, and a matching trace has a balanced         *)
(* chromogram with the parities of the colour sum (general context lb, then  *)
(* the empty context, where the colour sum is then Color0).                  *)
(* ------------------------------------------------------------------------- *)

let BALANCED_INJ = prove
 (`!w n1 n2 b1 b2. gram_balanced n1 b1 w /\ gram_balanced n2 b2 w
                   ==> n1 = n2 /\ (b1 <=> b2)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[gram_balanced] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC(SPEC `h:gram_symbol` GRAM_CASES) THEN
  REWRITE_TAC[GRAM_DISTINCT] THEN
  ASM_MESON_TAC[EQ_ADD_RCANCEL;
    ARITH_RULE `~(n1 = 0) /\ ~(n2 = 0) /\ n1 - 1 = n2 - 1 ==> n1 = n2`]);;

let BALANCED_CGRAM = prove
 (`!w s d b. gram_balanced d b (CONS s w)
             ==> CONS s w = cgram d b (BUTLAST (CONS s w))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[BUTLAST; gram_balanced] THEN
  REWRITE_TAC[NOT_CONS_NIL; cgram; CONJUNCT1 gram_balanced; CONS_11;
              GSYM ADD1; NOT_SUC] THEN
  STRUCT_CASES_TAC(SPEC `s:gram_symbol` GRAM_CASES) THEN
  REWRITE_TAC[GRAM_DISTINCT] THEN
  TRY(STRIP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[]);;

let MATCHG_BALANCED_GEN = prove
 (`!w et lb. matchg lb et w
             ==> (cbit1 (sumt et) <=> ODD (LENGTH lb)) /\
                 gram_balanced (LENGTH lb) (~(cbit0 (sumt et) <=> sumb lb)) w`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[matchg] THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC[sumt; CBIT_CLAUSES; LENGTH; ODD; sumb; gram_balanced];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; TL] THEN
  STRUCT_CASES_TAC(SPEC `h:gram_symbol` GRAM_CASES) THEN
  STRUCT_CASES_TAC(SPEC `h':color` (cases "color")) THEN
  STRUCT_CASES_TAC(ISPEC `lb:bool list` BOOL_LIST_CASES) THEN
  REWRITE_TAC[GRAM_DISTINCT; distinctness "color"; CBIT_CLAUSES; HD; TL;
              NOT_CONS_NIL] THEN
  FIRST_ASSUM(fun ih -> DISCH_THEN(MP_TAC o MATCH_MP ih)) THEN
  REWRITE_TAC[sumt; CBIT0_ADDC; CBIT1_ADDC; CBIT_CLAUSES; LENGTH; ODD; sumb;
              gram_balanced; GRAM_DISTINCT; GSYM ADD1; NOT_SUC; SUC_SUB1;
              IFF_NEG_NORM]);;

let MATCHG_BALANCED = prove
 (`!w et. matchg [] et w
          ==> ~(cbit1 (sumt et)) /\ gram_balanced 0 (cbit0 (sumt et)) w`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MATCHG_BALANCED_GEN) THEN
  REWRITE_TAC[LENGTH; ODD; sumb]);;

let BALANCED_SUMT0 = prove
 (`!w et. gram_balanced 0 F w /\ matchg [] et w ==> sumt et = Color0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o MATCH_MP MATCHG_BALANCED)) THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`w:gram_symbol list`; `0`; `0`; `F`; `cbit0 (sumt et)`]
    BALANCED_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `sumt et` CCONS_CBITS) THEN ASM_REWRITE_TAC[ccons] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* matchg on the completed trace and chromogram is matchpg on the partial    *)
(* ones.  In the context of the bit list lb with parity b the closing colour *)
(* is ccons (ODD (LENGTH lb)) (~(b <=> sumb lb)) added to the colour sum;    *)
(* the induction over the trace case-splits the symbol, the colour and the   *)
(* head of lb, and in each case one of the five instances of the induction   *)
(* hypothesis is the goal after normalisation.                               *)
(* ------------------------------------------------------------------------- *)

let MATCHG_NIL_CGRAM = prove
 (`!lb d b w. ~(matchg lb [] (cgram d b w))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` list_CASES) THEN
  REWRITE_TAC[cgram; matchg]);;

let MATCHG_PG_GEN = prove
 (`!et lb b w.
     gram_balanced (LENGTH lb) b (cgram (LENGTH lb) b w)
     ==> (matchg lb
           (APPEND et [addc (ccons (ODD(LENGTH lb)) (~(b <=> sumb lb)))
                            (sumt et)])
           (cgram (LENGTH lb) b w) <=>
          matchpg (stack_of_bitseq lb) et w)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THEN
  TRY(MAP_EVERY X_GEN_TAC [`e:color`; `et:color list`] THEN DISCH_TAC) THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` list_CASES) THEN
  REWRITE_TAC[APPEND; sumt; ADDC_0; matchpg; MATCHG_NIL_CGRAM] THENL
   [REWRITE_TAC[cgram] THEN
    STRUCT_CASES_TAC(ISPEC `lb:bool list` BOOL_LIST_CASES) THEN
    TRY(STRUCT_CASES_TAC(ISPEC `t:bool list` BOOL_LIST_CASES)) THEN
    BOOL_CASES_TAC `b:bool` THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_SUB1; ODD; sumb; gram_balanced;
                GRAM_DISTINCT; matchg; NOT_CONS_NIL; HD; TL; GSYM ADD1;
                ccons; CBIT_CLAUSES; distinctness "color"];
    STRUCT_CASES_TAC(SPEC `h:gram_symbol` GRAM_CASES) THEN
    REWRITE_TAC[cgram; matchg; GRAM_DISTINCT; MATCHG_NIL_CGRAM; HD; TL];
    REWRITE_TAC[cgram; matchg; NOT_CONS_NIL; APPEND_EQ_NIL; COND_ID; HD; TL];
    FIRST_X_ASSUM(fun ih ->
      MP_TAC(SPECL [`CONS F lb`; `b:bool`; `t:gram_symbol list`] ih) THEN
      MP_TAC(SPECL [`CONS T lb`; `b:bool`; `t:gram_symbol list`] ih) THEN
      MP_TAC(SPECL [`lb:bool list`; `~b`; `t:gram_symbol list`] ih) THEN
      MP_TAC(SPECL [`TL(lb:bool list)`; `b:bool`; `t:gram_symbol list`]
        ih) THEN
      MP_TAC(SPECL [`TL(lb:bool list)`; `~b`; `t:gram_symbol list`] ih)) THEN
    STRUCT_CASES_TAC(SPEC `h:gram_symbol` GRAM_CASES) THEN
    STRUCT_CASES_TAC(SPEC `e:color` (cases "color")) THEN
    STRUCT_CASES_TAC(ISPEC `lb:bool list` BOOL_LIST_CASES) THEN
    REWRITE_TAC[APPEND; sumt; cgram; matchg; matchpg; gram_balanced;
                GRAM_DISTINCT; distinctness "color"; CBIT_CLAUSES;
                NOT_CONS_NIL; HD; TL; LENGTH; ODD; sumb; stack_of_bitseq;
                GSYM ADD1; NOT_SUC; SUC_SUB1; ADDC_ASSOC; ADDC_CCONS;
                IFF_NEG_NORM; injectivity "bit_stack";
                distinctness "bit_stack"; UNWIND_THM1] THEN
    SIMP_TAC[]]);;

let MATCHG_PG = prove
 (`!et w. gram_balanced 0 F (cgram 0 F w)
          ==> (matchg [] (APPEND et [sumt et]) (cgram 0 F w) <=>
               matchpg Bstack0 et w)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`et:color list`; `[]:bool list`; `F`; `w:gram_symbol list`]
    MATCHG_PG_GEN) THEN
  REWRITE_TAC[LENGTH; ODD; sumb; stack_of_bitseq; ccons; ADDC_0]);;

(* ------------------------------------------------------------------------- *)
(* Invariance of matchpg under the colour swap 2 <-> 3 (the stack bits get   *)
(* negated), hence under the even normalisation etrace.                      *)
(* ------------------------------------------------------------------------- *)

let MATCHPG_FLIP_GEN = prove
 (`!et lb w. matchpg (stack_of_bitseq (MAP (~) lb)) (permt Eperm132 et) w <=>
             matchpg (stack_of_bitseq lb) et w`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THEN
  TRY(MAP_EVERY X_GEN_TAC [`e:color`; `et:color list`] THEN DISCH_TAC) THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `w:gram_symbol list` list_CASES) THEN
  REWRITE_TAC[permt; matchpg] THEN
  FIRST_X_ASSUM(fun ih ->
    MP_TAC(SPECL [`lb:bool list`; `t:gram_symbol list`] ih) THEN
    MP_TAC(SPECL [`CONS F lb`; `t:gram_symbol list`] ih) THEN
    MP_TAC(SPECL [`CONS T lb`; `t:gram_symbol list`] ih) THEN
    MP_TAC(SPECL [`TL(lb:bool list)`; `t:gram_symbol list`] ih)) THEN
  STRUCT_CASES_TAC(SPEC `h:gram_symbol` GRAM_CASES) THEN
  STRUCT_CASES_TAC(SPEC `e:color` (cases "color")) THEN
  STRUCT_CASES_TAC(ISPEC `lb:bool list` BOOL_LIST_CASES) THEN
  REWRITE_TAC[permc_DEF; matchpg; GRAM_DISTINCT; distinctness "color"; MAP;
              stack_of_bitseq; TL; injectivity "bit_stack";
              distinctness "bit_stack"; UNWIND_THM1] THEN
  SIMP_TAC[]);;

let MATCHPG_FLIP = prove
 (`!(et:color list) (w:gram_symbol list).
    matchpg Bstack0 (permt Eperm132 et) w <=> matchpg Bstack0 et w`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`et:color list`; `[]:bool list`; `w:gram_symbol list`]
    MATCHPG_FLIP_GEN) THEN
  REWRITE_TAC[MAP; stack_of_bitseq]);;

let MATCHPG_ETRACE = prove
 (`!(et:color list) (w:gram_symbol list).
    matchpg Bstack0 (etrace et) w <=> matchpg Bstack0 et w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[etrace; etrace_perm] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PERMT_ID; MATCHPG_FLIP]);;
