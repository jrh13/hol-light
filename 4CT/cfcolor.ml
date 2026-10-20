(* ========================================================================= *)
(* 4CT/cfcolor.ml                                                            *)
(*                                                                           *)
(* cfcolor.v: the colouring of a configuration map computed from its         *)
(* construction program.  cpcolor cp is the ctree of the even partial ring   *)
(* traces of the colourings of cpmap cp, built by the iterator cpcolor1 (one *)
(* clause per construction step) from the branch constructor cpbranch and    *)
(* the optimised initial production cpcolor0, without ever building the map. *)
(* This file has the definitions and the specification CPBRANCH_SPEC of      *)
(* cpbranch; the correctness theorems (ctree_mem_cpcolor) are in             *)
(* cpcolor_correct.ml.                                                       *)
(* ========================================================================= *)

needs "4CT/cfmap.ml";;
needs "4CT/coloring.ml";;
needs "4CT/ctree.ml";;

(* ------------------------------------------------------------------------- *)
(* ctree_cons_perm g : the colour-permuted node constructor.                 *)
(* ------------------------------------------------------------------------- *)

let ctree_cons_perm = new_definition
 `ctree_cons_perm (g:color->color) =
    palette (ctree_cons_e (g Color0)) (ctree_cons_e (g Color1))
            (ctree_cons_e (g Color2)) (ctree_cons_e (g Color3))`;;

(* ------------------------------------------------------------------------- *)
(* cpbranch : the all-in-one production of a single tree branch from a ring  *)
(* trace. cfcbr2 h and cfcbr1 g are simple list recursions with a constant   *)
(* functional parameter (h : color->ctree->ctree, g : color->color).         *)
(* ------------------------------------------------------------------------- *)

let cfcbr2 = define
 `(cfcbr2 (h:color->ctree->ctree) [] = ctree_simple_leaf) /\
  (cfcbr2 h (CONS e et') = h e (cfcbr2 h et'))`;;

let cfcbr1 = define
 `(cfcbr1 (g:color->color) [] = ctree_simple_leaf) /\
  (cfcbr1 g (CONS e et') =
     if g e = Color0 then CtreeEmpty
     else if g e = Color1 then ctree_cons1 (cfcbr1 g et')
     else if g e = Color2 then ctree_cons2 (cfcbr2 (ctree_cons_perm g) et')
     else ctree_cons2
     (cfcbr2 (ctree_cons_perm (\c. permc Eperm132 (g c))) et'))`;;

let cpbranch = new_definition
 `cpbranch (et:color list) =
    if LENGTH et < 2 then CtreeEmpty
    else if HD(TL et) = Color0 then CtreeEmpty
    else cfcbr1 (permc (edge_rot (HD(TL et)))) (TL(TL et))`;;

(* ------------------------------------------------------------------------- *)
(* cpcolor1 s f et : the generic iterator step, one clause per construction  *)
(* step s. For the current ring trace et, produce the union of the trees f   *)
(* returns on the ring traces of the map obtained by applying s.  The list   *)
(* rotations rot_list and rotr_list (mathcomp rot, rotr) of the CpR and CpRr *)
(* clauses are defined in embed_prelim.ml.                                   *)
(* ------------------------------------------------------------------------- *)

let cpcolor1 = define
 `(cpcolor1 (CpR n) (f:color list->ctree) (et:color list) =
     f (rot_list n et)) /\
  (cpcolor1 CpRr f et =
     (if LENGTH et <= 1 then CtreeEmpty else f (rotr_list 1 et))) /\
  (cpcolor1 CpY f et =
     (if et = [] then CtreeEmpty
      else ctree_union
             (f (CONS (permc Eperm231 (HD et))
                      (CONS (permc Eperm312 (HD et)) (TL et))))
             (f (CONS (permc Eperm312 (HD et))
                      (CONS (permc Eperm231 (HD et)) (TL et)))))) /\
  (cpcolor1 CpH f et =
     (if LENGTH et < 2 then CtreeEmpty
      else if HD et = HD(TL et) then
        ctree_union
          (f (CONS (permc Eperm231 (HD et))
                   (CONS (permc Eperm231 (HD et)) (TL(TL et)))))
          (f (CONS (permc Eperm312 (HD et))
                   (CONS (permc Eperm312 (HD et)) (TL(TL et)))))
      else f (CONS (HD(TL et)) (CONS (HD et) (TL(TL et)))))) /\
  (cpcolor1 CpU f et =
     ctree_union (f (CONS Color1 (CONS Color1 et)))
       (ctree_union (f (CONS Color2 (CONS Color2 et)))
                    (f (CONS Color3 (CONS Color3 et))))) /\
  (cpcolor1 CpK f et =
     (if LENGTH et < 2 then CtreeEmpty
      else if HD et = HD(TL et) then CtreeEmpty
      else f (CONS (addc (HD et) (HD(TL et))) (TL(TL et))))) /\
  (cpcolor1 CpA f et =
     (if LENGTH et < 2 then CtreeEmpty
      else if HD et = HD(TL et) then
        f (if TL(TL et) = [] then et else TL(TL et))
      else CtreeEmpty))`;;

(* ------------------------------------------------------------------------- *)
(* cpcolor0 cp : optimised initial-tree production over the (already         *)
(* reversed) program cp. Leading CpR is skipped; leading CpY/CpU examine     *)
(* fewer colourings; for any other leading step fold cpcolor1 over cp from   *)
(* the base trace.                                                           *)
(* ------------------------------------------------------------------------- *)

let cpcolor0 = define
 `(cpcolor0 [] = ITLIST cpcolor1 [] cpbranch [Color1; Color1]) /\
  (cpcolor0 (CONS (CpR n) cp') = cpcolor0 cp') /\
  (cpcolor0 (CONS CpRr cp') =
     ITLIST cpcolor1 (CONS CpRr cp') cpbranch [Color1; Color1]) /\
  (cpcolor0 (CONS CpY cp') =
     ITLIST cpcolor1 cp' cpbranch [Color1; Color2; Color3]) /\
  (cpcolor0 (CONS CpH cp') =
     ITLIST cpcolor1 (CONS CpH cp') cpbranch [Color1; Color1]) /\
  (cpcolor0 (CONS CpU cp') =
     ctree_union
       (ITLIST cpcolor1 cp' cpbranch [Color1; Color1; Color2; Color2])
       (ITLIST cpcolor1 cp' cpbranch [Color1; Color1; Color1; Color1])) /\
  (cpcolor0 (CONS CpK cp') =
     ITLIST cpcolor1 (CONS CpK cp') cpbranch [Color1; Color1]) /\
  (cpcolor0 (CONS CpA cp') =
     ITLIST cpcolor1 (CONS CpA cp') cpbranch [Color1; Color1])`;;

let cpcolor = new_definition
 `cpcolor (cp:(cpstep)list) = ctree_cons_rot (cpcolor0 (REVERSE cp))`;;

(* ------------------------------------------------------------------------- *)
(* cpbranch_spec : cpbranch et is the singleton tree of the normalised even  *)
(* tail of the partial trace behead et.  (Gonthier cfcolor.v:122.)  Stated   *)
(* with 2 <= LENGTH et, matching cpcolor0's usage (cpbranch is only ever     *)
(* applied to base traces of length >= 2), which sidesteps the junk value of *)
(* the non-total TL on the empty list.                                       *)
(* ------------------------------------------------------------------------- *)

(* Colour-algebra / ctree plumbing used by cpbranch_spec.                    *)
let PERMT_PERMT = prove
 (`!q p et. permt q (permt p et) = MAP (\c. permc q (permc p c)) et`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PERMT_MAP; GSYM MAP_o; o_DEF]);;

let CTREE_CONS_E_C0 = prove
 (`!t. ctree_cons_e Color0 t = CtreeEmpty`,
  REWRITE_TAC[ctree_cons_e; palette; ctree_cons0]);;

let CTREE_CONS_E_C1 = prove
 (`!t. ctree_cons_e Color1 t = ctree_cons1 t`,
  REWRITE_TAC[ctree_cons_e; palette]);;

let CTREE_CONS_E_C2 = prove
 (`!t. ctree_cons_e Color2 t = ctree_cons2 t`,
  REWRITE_TAC[ctree_cons_e; palette]);;

let CTREE_OF_TTAIL_CONS = prove
 (`!c et. ctree_of_ttail (CONS c et) = ctree_cons_e c (ctree_of_ttail et)`,
  REWRITE_TAC[ctree_of_ttail; ITLIST]);;

let CTREE_CONS_PERM_E = prove
 (`!g e t. ctree_cons_perm g e t = ctree_cons_e (g e) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ctree_cons_perm] THEN
  STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
  REWRITE_TAC[palette]);;

(* cfcbr2 (ctree_cons_perm g) traces out ctree_of_ttail of the g-permuted    *)
(* seq.                                                                      *)
let CFCBR2_SPEC = prove
 (`!g et. cfcbr2 (ctree_cons_perm g) et = ctree_of_ttail (MAP g et)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[cfcbr2; MAP; ctree_of_ttail; ITLIST; CTREE_CONS_PERM_E]);;

(* cfcbr1 (permc P) et = the branch tree of the even-normalised P-permuted   *)
(* seq.                                                                      *)
let CFCBR1_SPEC = prove
 (`!P et. cfcbr1 (permc P) et =
          ctree_of_ttail
           (permt (if even_tail (permt P et) then Eperm123 else Eperm132)
                  (permt P et))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[cfcbr1; permt; even_tail; PERMT_MAP; MAP;
                ctree_of_ttail; ITLIST];
    REWRITE_TAC[cfcbr1; permt] THEN
    STRUCT_CASES_TAC(ISPEC `permc P h` (cases "color")) THENL
     [REWRITE_TAC[distinctness "color"; PERMC_0; CTREE_OF_TTAIL_CONS;
                  CTREE_CONS_E_C0];
      REWRITE_TAC[distinctness "color"; even_tail; CTREE_OF_TTAIL_CONS] THEN
      SUBGOAL_THEN
       `permc (if even_tail (permt P t) then Eperm123 else Eperm132) Color1 =
        Color1`
        SUBST1_TAC THENL
       [COND_CASES_TAC THEN REWRITE_TAC[permc_DEF]; ALL_TAC] THEN
      REWRITE_TAC[CTREE_CONS_E_C1] THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM ACCEPT_TAC;
      REWRITE_TAC[distinctness "color"; even_tail; CTREE_OF_TTAIL_CONS] THEN
      REWRITE_TAC[permc_DEF] THEN
      REWRITE_TAC[CTREE_CONS_E_C2; CFCBR2_SPEC; GSYM PERMT_MAP] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PERMT_ID];
      REWRITE_TAC[distinctness "color"; even_tail; CTREE_OF_TTAIL_CONS] THEN
      REWRITE_TAC[permc_DEF] THEN
      REWRITE_TAC[CTREE_CONS_E_C2; CFCBR2_SPEC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PERMT_PERMT]]]);;

let CPBRANCH_SPEC = prove
 (`!et. 2 <= LENGTH et ==> cpbranch et = ctree_of_ttail (etail (TL et))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `et:(color)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH] THEN
  STRUCT_CASES_TAC(ISPEC `t:(color)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH; cpbranch; TL; HD;
              ARITH_RULE `~(SUC(SUC n) < 2)`] THEN
  REWRITE_TAC[etail; ttail; proper_trace; NOT_CONS_NIL; HD; TL] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[permt; PERMC_0; ctree_of_ttail; ITLIST; CTREE_CONS_E_C0;
                  etrace_perm; even_trace; ttail; proper_trace; NOT_CONS_NIL;
                  HD; TL; CFCBR1_SPEC]);;

