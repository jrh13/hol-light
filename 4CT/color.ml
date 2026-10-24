(* ========================================================================= *)
(* 4CT/color.ml                                                              *)
(*                                                                           *)
(* color.v: the colour algebra and traces.  The four colours with addc (a    *)
(* Klein 4-group), the six edge permutations permc (the symmetric group on   *)
(* the three nonzero colours), the bits cbit0, cbit1, ccons and the inverse  *)
(* inv_eperm; the trace operations ptrace, sumt, ctrace, trace_col           *)
(* (Gonthier's urtrace: the wrap-around sum comes first), untrace and permt, *)
(* and the even normalisation of traces (even_tail, ttail, even_trace,       *)
(* etrace, etail, eptrace).                                                  *)
(*                                                                           *)
(* Contents:                                                                 *)
(*   0. the types and basic operations                                       *)
(*   1. colour algebra                                                       *)
(*   2. edge permutation algebra                                             *)
(*   3. bit representation                                                   *)
(*   4. inverse permutations                                                 *)
(*   5. trace operations and their basic properties                          *)
(*   6. untrace                                                              *)
(*   7. trace normalisation                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 0. The types and the basic operations.  The list-cons infix :: is         *)
(* declared here, as in general.ml and make.ml, if the session has not done  *)
(* so yet.                                                                   *)
(* ------------------------------------------------------------------------- *)

let () =
  if not (can (assoc "::") (infixes())) then begin
    parse_as_infix("::", (23, "right"));
    override_interface("::", `CONS:A->A list->A list`)
  end;;

let color_INDUCT,color_RECURSION =
  define_type "color = Color0 | Color1 | Color2 | Color3";;

let edge_perm_INDUCT,edge_perm_RECURSION =
  define_type
    "edge_perm = Eperm123 | Eperm132 | Eperm213 | Eperm231 | Eperm312 | \
     Eperm321";;

let addc_DEF = define
 `(addc Color0 (x:color) = x) /\
  (addc Color1 Color0 = Color1) /\
  (addc Color1 Color1 = Color0) /\
  (addc Color1 Color2 = Color3) /\
  (addc Color1 Color3 = Color2) /\
  (addc Color2 Color0 = Color2) /\
  (addc Color2 Color1 = Color3) /\
  (addc Color2 Color2 = Color0) /\
  (addc Color2 Color3 = Color1) /\
  (addc Color3 Color0 = Color3) /\
  (addc Color3 Color1 = Color2) /\
  (addc Color3 Color2 = Color1) /\
  (addc Color3 Color3 = Color0)`;;

let permc_DEF = define
 `(permc Eperm123 (x:color) = x) /\
  (permc Eperm132 Color0 = Color0) /\
  (permc Eperm132 Color1 = Color1) /\
  (permc Eperm132 Color2 = Color3) /\
  (permc Eperm132 Color3 = Color2) /\
  (permc Eperm213 Color0 = Color0) /\
  (permc Eperm213 Color1 = Color2) /\
  (permc Eperm213 Color2 = Color1) /\
  (permc Eperm213 Color3 = Color3) /\
  (permc Eperm231 Color0 = Color0) /\
  (permc Eperm231 Color1 = Color2) /\
  (permc Eperm231 Color2 = Color3) /\
  (permc Eperm231 Color3 = Color1) /\
  (permc Eperm312 Color0 = Color0) /\
  (permc Eperm312 Color1 = Color3) /\
  (permc Eperm312 Color2 = Color1) /\
  (permc Eperm312 Color3 = Color2) /\
  (permc Eperm321 Color0 = Color0) /\
  (permc Eperm321 Color1 = Color3) /\
  (permc Eperm321 Color2 = Color2) /\
  (permc Eperm321 Color3 = Color1)`;;

let edge_rot_DEF = define
 `(edge_rot Color0 = Eperm123) /\
  (edge_rot Color1 = Eperm123) /\
  (edge_rot Color2 = Eperm312) /\
  (edge_rot Color3 = Eperm231)`;;

(* Exhaustion tactics for finite types: case-split all universals            *)
let COLOR_CASES_TAC =
  REPEAT(MATCH_MP_TAC color_INDUCT THEN REPEAT CONJ_TAC);;

let EPERM_CASES_TAC =
  REPEAT(MATCH_MP_TAC edge_perm_INDUCT THEN REPEAT CONJ_TAC);;

let EPERM_COLOR_CASES_TAC =
  REPEAT((MATCH_MP_TAC edge_perm_INDUCT ORELSE
          MATCH_MP_TAC color_INDUCT) THEN REPEAT CONJ_TAC);;

(* ------------------------------------------------------------------------- *)
(* 1. Color algebra -- addc is associative, commutative, self-inverse.       *)
(* ------------------------------------------------------------------------- *)

let ADDC_COMM = prove
 (`!x y. addc x y = addc y x`,
  COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF]);;

let ADDC_ASSOC = prove
 (`!x y z. addc x (addc y z) = addc (addc x y) z`,
  COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF]);;

let ADDC_0 = prove
 (`(!x. addc Color0 x = x) /\ (!x. addc x Color0 = x)`,
  CONJ_TAC THEN COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF]);;

let ADDCC = prove
 (`!x. addc x x = Color0`,
  COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF]);;

let ADDC_CANCEL_L = prove
 (`!x y z. addc x y = addc x z <=> y = z`,
  COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF; distinctness "color"]);;

let ADDC_EQ_0 = prove
 (`!x y. addc x y = Color0 <=> x = y`,
  COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF; distinctness "color"]);;

let ADDC_SYM_CANCEL = prove
 (`!a b c. addc (addc a b) (addc a c) = addc b c`,
  COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF]);;

(* ------------------------------------------------------------------------- *)
(* 2. Edge permutation algebra.                                              *)
(* ------------------------------------------------------------------------- *)

let PERMC_0 = prove
 (`!g. permc g Color0 = Color0`,
  EPERM_CASES_TAC THEN REWRITE_TAC[permc_DEF]);;

let PERMC_INJ = prove
 (`!g x y. permc g x = permc g y ==> x = y`,
  EPERM_COLOR_CASES_TAC THEN
  REWRITE_TAC[permc_DEF; distinctness "color"]);;

let PERMC_ADDC = prove
 (`!g x y. permc g (addc x y) = addc (permc g x) (permc g y)`,
  EPERM_COLOR_CASES_TAC THEN REWRITE_TAC[permc_DEF; addc_DEF]);;

let PERMC_EQ_0 = prove
 (`!g c. permc g c = Color0 <=> c = Color0`,
  EPERM_COLOR_CASES_TAC THEN
  REWRITE_TAC[permc_DEF; distinctness "color"]);;

(* ------------------------------------------------------------------------- *)
(* 3. Bit representation.                                                    *)
(* ------------------------------------------------------------------------- *)

let cbit0 = new_definition
 `cbit0 (c:color) <=> c = Color1 \/ c = Color3`;;

let cbit1 = new_definition
 `cbit1 (c:color) <=> c = Color2 \/ c = Color3`;;

let ccons = new_definition
 `ccons (b1:bool) (b0:bool) =
    if b1 then (if b0 then Color3 else Color2)
    else (if b0 then Color1 else Color0)`;;

let CCONS_CBITS = prove
 (`!c. ccons (cbit1 c) (cbit0 c) = c`,
  COLOR_CASES_TAC THEN
  REWRITE_TAC[cbit0; cbit1; ccons; distinctness "color"]);;

let CBIT1_CCONS = prove
 (`!b1 b0. cbit1(ccons b1 b0) = b1`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `b1:bool` THEN ASM_CASES_TAC `b0:bool` THEN
  ASM_REWRITE_TAC[ccons; cbit1; distinctness "color"]);;

let CBIT0_ADDC = prove
 (`!x y. cbit0(addc x y) = ~(cbit0 x <=> cbit0 y)`,
  COLOR_CASES_TAC THEN
  REWRITE_TAC[cbit0; addc_DEF; distinctness "color"] THEN
  CONV_TAC TAUT);;

let CBIT1_ADDC = prove
 (`!x y. cbit1(addc x y) = ~(cbit1 x <=> cbit1 y)`,
  COLOR_CASES_TAC THEN
  REWRITE_TAC[cbit1; addc_DEF; distinctness "color"] THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* 4. Inverse permutations.                                                  *)
(* ------------------------------------------------------------------------- *)

let inv_eperm = new_definition
 `inv_eperm (g:edge_perm) =
    if g = Eperm231 then Eperm312
    else if g = Eperm312 then Eperm231
    else g`;;

let INV_PERMC = prove
 (`!g c. permc (inv_eperm g) (permc g c) = c`,
  EPERM_COLOR_CASES_TAC THEN
  REWRITE_TAC[inv_eperm; permc_DEF; distinctness "edge_perm"]);;

(* Universal and existential quantification over the finite types.           *)
let FORALL_COLOR = prove
 (`!P. (!c:color. P c) <=> P Color0 /\ P Color1 /\ P Color2 /\ P Color3`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC color_INDUCT THEN ASM_REWRITE_TAC[]);;

let EXISTS_EPERM = prove
 (`!P. (?g:edge_perm. P g) <=>
       P Eperm123 \/ P Eperm132 \/ P Eperm213 \/ P Eperm231 \/
       P Eperm312 \/ P Eperm321`,
  MESON_TAC[cases "edge_perm"]);;

(* Any injective function fixing Color0 is a permc: by cases on the values   *)
(* of f at the four colours, each case decided by rewriting.                 *)
let COLOR_INJ_PERMC = prove
 (`!f. (!x y:color. f x = f y ==> x = y) /\ f Color0 = Color0
       ==> ?g. !c. f c = permc g c`,
  GEN_TAC THEN REWRITE_TAC[FORALL_COLOR; EXISTS_EPERM; permc_DEF] THEN
  MAP_EVERY (fun c ->
    STRUCT_CASES_TAC(SPEC (mk_comb(`f:color->color`,c)) (cases "color")))
   [`Color0`; `Color1`; `Color2`; `Color3`] THEN
  REWRITE_TAC[distinctness "color"]);;

(* ------------------------------------------------------------------------- *)
(* 5. Trace operations (from color.v):                                       *)
(*   ptrace     pairwise sums [c0+c1; c1+c2; ...; c(n-1)+cn];                *)
(*   sumt       the sum of all the colours of a list;                        *)
(*   ctrace     the complete trace: the closing sum prepended to the partial *)
(*              trace (Coq's ctrace appends it; ctrace_a in kempetree.ml);   *)
(*   permt      a colour permutation applied to each element;                *)
(*   trace_col  the cyclic trace of a perimeter colouring;                   *)
(*   untrace    the inverse of the trace, from a starting colour.            *)
(* ------------------------------------------------------------------------- *)

let ptrace = define
 `(ptrace ([] : color list) = []) /\
  (ptrace [c:color] = []) /\
  (ptrace (CONS (c1:color) (CONS c2 rest)) =
     CONS (addc c1 c2) (ptrace (CONS c2 rest)))`;;

let sumt = define
 `(sumt ([] : color list) = Color0) /\
  (sumt (CONS c rest) = addc c (sumt rest))`;;

let ctrace = new_definition
 `ctrace (et : color list) = CONS (sumt et) et`;;

let permt = define
 `(permt (g:edge_perm) ([] : color list) = []) /\
  (permt g (CONS c rest) = CONS (permc g c) (permt g rest))`;;

let head_color = new_definition
 `head_color (et : color list) = if et = [] then Color0 else HD et`;;

let proper_trace = new_definition
 `proper_trace (et : color list) <=>
    ~(et = []) /\ ~(HD et = Color0)`;;

(* trace_col [c0; c1; ...; cn] = [cn+c0; c0+c1; c1+c2; ...; c(n-1)+cn], the  *)
(* wrap-around sum first: Gonthier's urtrace.  His trace = ctrace o ptrace   *)
(* puts it last, i.e. trace = rot 1 (urtrace) (DEFINITION_ALIGNMENT.md,      *)
(* section 5.2).                                                             *)

let trace_DEF = new_definition
 `trace_col (lc : color list) =
    if lc = [] then []
    else ptrace (CONS (LAST lc) lc)`;;

(* untrace: recover coloring from a trace given starting color. untrace c0   *)
(* [e1; e2; ...; en] = [c0; c0+e1; c0+e1+e2; ...]                            *)

let untrace = define
 `(untrace (c0:color) ([] : color list) = [c0]) /\
  (untrace c0 (CONS e rest) = CONS c0 (untrace (addc c0 e) rest))`;;

(* ------------------------------------------------------------------------- *)
(* Basic properties of trace operations.                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_PTRACE = prove
 (`!lc. LENGTH(ptrace lc) = LENGTH lc - 1`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ptrace; LENGTH; SUB_0] THEN
  X_GEN_TAC `c:color` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[ptrace; LENGTH] THEN
  SIMP_TAC[ARITH_RULE `SUC 0 - 1 = 0`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  SIMP_TAC[LENGTH; ARITH_RULE `SUC(SUC n) - 1 = SUC n`;
           ARITH_RULE `SUC n - 1 = n`; SUC_INJ]);;

let LENGTH_PERMT = prove
 (`!g lc. LENGTH(permt g lc) = LENGTH lc`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[permt; LENGTH] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH]);;

let PERMT_ID = prove
 (`!lc. permt Eperm123 lc = lc`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[permt; permc_DEF] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let PERMT_APPEND = prove
 (`!g l1 l2. permt g (APPEND l1 l2) = APPEND (permt g l1) (permt g l2)`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[permt; APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let SUMT_APPEND = prove
 (`!l1 l2. sumt (APPEND l1 l2) = addc (sumt l1) (sumt l2)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[sumt; APPEND; ADDC_0] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ADDC_ASSOC]);;

let SUMT_PERMT = prove
 (`!g et. sumt(permt g et) = permc g (sumt et)`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[sumt; permt; PERMC_0] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[PERMC_ADDC]);;

(* ptrace distributes over permt                                             *)
let PTRACE_PERMT = prove
 (`!g lc. ptrace(permt g lc) = permt g (ptrace lc)`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[permt; ptrace] THEN X_GEN_TAC `c:color` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[permt; ptrace] THEN
  X_GEN_TAC `a0:color` THEN X_GEN_TAC `a1:color list` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[PERMC_ADDC] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[]);;

(* ptrace is invariant under adding a constant                               *)
let PTRACE_ADDC = prove
 (`!c lc. ptrace (MAP (addc c) lc) = ptrace lc`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[MAP; ptrace] THEN
  X_GEN_TAC `c1:color` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[MAP; ptrace] THEN
  X_GEN_TAC `a0:color` THEN X_GEN_TAC `a1:color list` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ADDC_SYM_CANCEL]);;

(* ctrace distributes over permt                                             *)
let CTRACE_PERMT = prove
 (`!g et. ctrace(permt g et) = permt g (ctrace et)`,
  REWRITE_TAC[ctrace; SUMT_PERMT; permt]);;

(* Color0 membership is preserved by permt                                   *)
let MEM_COLOR0_PERMT = prove
 (`!g et. MEM Color0 (permt g et) <=> MEM Color0 et`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[permt; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Color0 = permc g a0) <=> (Color0 = a0)`
    (fun th -> REWRITE_TAC[th]) THEN
  EQ_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `permc (inv_eperm g)`) THEN
    REWRITE_TAC[INV_PERMC; PERMC_0];
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[PERMC_0]]);;

(* permt preserves proper_trace                                              *)
let PROPER_PERMT = prove
 (`!g et. proper_trace(permt g et) <=> proper_trace et`,
  REPEAT GEN_TAC THEN REWRITE_TAC[proper_trace] THEN
  SPEC_TAC(`et:color list`, `et:color list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[permt; NOT_CONS_NIL; HD; PERMC_EQ_0]);;

(* Key telescope lemma: sumt of ptrace = first + last                        *)
let SUMT_PTRACE = prove
 (`!lc. ~(lc = []) ==> sumt(ptrace lc) = addc (HD lc) (LAST lc)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  X_GEN_TAC `c:color` THEN X_GEN_TAC `t:color list` THEN DISCH_TAC THEN
  REWRITE_TAC[HD] THEN
  ASM_CASES_TAC `t:color list = []` THENL
   [ASM_REWRITE_TAC[ptrace; sumt; LAST; ADDCC]; ALL_TAC] THEN
  SUBGOAL_THEN `?h u. t = CONS (h:color) u` MP_TAC THENL
   [ASM_MESON_TAC[list_CASES]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ptrace; sumt] THEN
  SUBGOAL_THEN `LAST (c :: h :: (u:color list)) = LAST (h :: u)`
    SUBST1_TAC THENL
   [REWRITE_TAC[LAST; NOT_CONS_NIL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; HD] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ADDC_ASSOC; ADDCC; ADDC_0] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM ADDC_ASSOC; ADDCC; ADDC_0]);;

(* trace has same length as input                                            *)
let LENGTH_TRACE = prove
 (`!lc. LENGTH(trace_col lc) = LENGTH lc`,
  GEN_TAC THEN REWRITE_TAC[trace_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
  REWRITE_TAC[LENGTH_PTRACE; LENGTH; NOT_CONS_NIL] THEN ARITH_TAC);;

(* sumt of trace is always Color0 (cyclic traces sum to zero)                *)
let SUMT_TRACE = prove
 (`!lc. sumt(trace_col lc) = Color0`,
  GEN_TAC THEN REWRITE_TAC[trace_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[sumt] THEN
  SUBGOAL_THEN `~(CONS (LAST lc) (lc:color list) = [])` ASSUME_TAC THENL
   [REWRITE_TAC[NOT_CONS_NIL]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUMT_PTRACE] THEN REWRITE_TAC[HD] THEN
  SUBGOAL_THEN `LAST(CONS (LAST lc) (lc:color list)) = LAST lc`
    SUBST1_TAC THENL
   [REWRITE_TAC[LAST] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ADDCC]);;

(* trace distributes over permt                                              *)
let TRACE_PERMT = prove
 (`!g lc. trace_col(permt g lc) = permt g (trace_col lc)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace_DEF] THEN
  ASM_CASES_TAC `lc:color list = []` THENL
   [ASM_REWRITE_TAC[permt]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(permt g (lc:color list) = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_PERMT; LENGTH_EQ_NIL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LAST(permt g (lc:color list)) = permc g (LAST lc)`
    SUBST1_TAC THENL
   [UNDISCH_TAC `~(lc:color list = [])` THEN
    SPEC_TAC(`lc:color list`, `lc:color list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL; permt; LAST] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[permt; LAST] THEN
    ASM_MESON_TAC[LENGTH_PERMT; LENGTH_EQ_NIL];
    ALL_TAC] THEN
  SUBGOAL_THEN `CONS (permc g (LAST lc)) (permt g lc) =
                permt g (CONS (LAST (lc:color list)) lc)` SUBST1_TAC THENL
   [REWRITE_TAC[permt]; ALL_TAC] THEN
  REWRITE_TAC[PTRACE_PERMT]);;

(* permt is MAP with permc                                                   *)
let PERMT_MAP = prove
 (`!g lc. permt g lc = MAP (permc g) lc`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[permt; MAP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. Untrace properties.                                                    *)
(* untrace inverts ptrace: ptrace(untrace c0 et) = et. trace_col(untrace c0  *)
(* et) = ctrace et (the cyclic closure).                                     *)
(* ------------------------------------------------------------------------- *)

let PTRACE_SNOC = prove
 (`!lc x. ~(lc = []) ==>
           ptrace(APPEND lc [x]) =
           APPEND (ptrace lc) [addc (LAST lc) (x:color)]`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  X_GEN_TAC `c:color` THEN X_GEN_TAC `t:color list` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN X_GEN_TAC `x:color` THEN
  ASM_CASES_TAC `t:color list = []` THENL
   [ASM_REWRITE_TAC[APPEND; ptrace; LAST]; ALL_TAC] THEN
  SUBGOAL_THEN `?h u. t = CONS (h:color) u` MP_TAC THENL
   [ASM_MESON_TAC[list_CASES]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[APPEND; ptrace; LAST; NOT_CONS_NIL] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:color`) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; APPEND; LAST]);;

(* ------------------------------------------------------------------------- *)
(* 7. Trace normalisation: even_tail, even_trace, etrace.                    *)
(* ------------------------------------------------------------------------- *)

(* even_tail: true if Color2 appears before Color3 in trace                  *)
let even_tail = define
 `(even_tail [] = T) /\
  (even_tail (c :: rest) =
     if c = Color2 then T
     else if c = Color3 then F
     else even_tail rest)`;;

(* ttail: the normalized tail of a trace                                     *)
let ttail = new_definition
  `ttail (et:color list) =
    if proper_trace et then
      if et = [] then [] else permt (edge_rot (HD et)) (TL et)
    else [Color0]`;;

(* even_trace: whether the trace is "even"                                   *)
let even_trace = new_definition
  `even_trace (et:color list) = even_tail (ttail et)`;;

(* etrace_perm: the permutation to apply to make trace even                  *)
let etrace_perm = new_definition
  `etrace_perm (et:color list) =
    if even_trace et then Eperm123 else Eperm132`;;

(* etrace: the even-normalized trace                                         *)
let etrace = new_definition
  `etrace (et:color list) = permt (etrace_perm et) et`;;

(* etail: the normalized even tail                                           *)
let etail = new_definition
  `etail (et:color list) = permt (etrace_perm et) (ttail et)`;;

(* eptrace: standardized tail of partial trace                               *)
let eptrace = new_definition
  `eptrace (lc:color list) = etail (ptrace lc)`;;
