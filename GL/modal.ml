(* ========================================================================= *)
(* Syntax and semantics of modal logic.                                      *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(*                                                                           *)
(* Part of this code is copied or adapted from                               *)
(*   John Harrison (2017) The HOL Light Tutorial.                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Syntax of formulae.                                                       *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("&&",(16,"right"));;
parse_as_infix("||",(15,"right"));;
parse_as_infix("-->",(14,"right"));;
parse_as_infix("<->",(13,"right"));;
parse_as_prefix "Not";;
parse_as_prefix "Box";;

let form_INDUCT,form_RECURSION = define_type
  "form = False
        | True
        | Atom string
        | Not form
        | && form form
        | || form form
        | --> form form
        | <-> form form
        | Box form";;

let form_CASES = prove_cases_thm form_INDUCT;;
let form_DISTINCT = distinctness "form";;
let form_INJ = injectivity "form";;

(* ------------------------------------------------------------------------- *)
(* Kripke's Semantics of formulae.                                           *)
(* ------------------------------------------------------------------------- *)

let holds =
  let pth = prove
    (`(!WP. P WP) <=> (!W R. P (W,R))`,
     MATCH_ACCEPT_TAC FORALL_PAIR_THM) in
  (end_itlist CONJ o map (REWRITE_RULE[pth] o GEN_ALL) o CONJUNCTS o
   new_recursive_definition form_RECURSION)
  `(holds WR V False (w:W) <=> F) /\
   (holds WR V True w <=> T) /\
   (holds WR V (Atom s) w <=> V s w) /\
   (holds WR V (Not p) w <=> ~(holds WR V p w)) /\
   (holds WR V (p && q) w <=> holds WR V p w /\ holds WR V q w) /\
   (holds WR V (p || q) w <=> holds WR V p w \/ holds WR V q w) /\
   (holds WR V (p --> q) w <=> holds WR V p w ==> holds WR V q w) /\
   (holds WR V (p <-> q) w <=> holds WR V p w <=> holds WR V q w) /\
   (holds WR V (Box p) w <=>
    !w'. w' IN FST WR /\ SND WR w w' ==> holds WR V p w')`;;

let holds_in = new_definition
  `holds_in (W,R) p <=> !V w. w IN W ==> holds (W,R) V p w`;;

parse_as_infix("|=",(11,"right"));;

let valid = new_definition
  `L: (W->bool)#(W->W->bool)->bool |= p <=> !f. L f ==> holds_in f p`;;

(* ------------------------------------------------------------------------- *)
(* Some model-theoretic lemmas.                                              *)
(* ------------------------------------------------------------------------- *)

let MODAL_TAC =
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds] THEN MESON_TAC[];;

let MODAL_RULE tm = prove(tm,MODAL_TAC);;

let HOLDS_FORALL_LEMMA = prove
 (`!W R P. (!p V. P (holds (W,R) V p)) <=> (!p:W->bool. P p)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  DISCH_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `P (\w:W. holds (W,R) (\a. p) (Atom a) w):bool`
    (MP_TAC o REWRITE_RULE[holds]) THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let MODAL_SCHEMA_TAC =
  REWRITE_TAC[holds_in; holds] THEN MP_TAC HOLDS_FORALL_LEMMA THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]);;

(* ------------------------------------------------------------------------- *)
(* Transitive Noetherian frames.                                             *)
(* ------------------------------------------------------------------------- *)

let MODAL_TRANS = prove
 (`!W R.
     (!w w' w'':W. w IN W /\ w' IN W /\ w'' IN W /\
                   R w w' /\ R w' w''
                   ==> R w w'') <=>
     (!p. holds_in (W,R) (Box p --> Box Box p))`,
  MODAL_SCHEMA_TAC THEN MESON_TAC[]);;

let TRANSNT = new_definition
  `TRANSNT (W:W->bool,R:W->W->bool) <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   (!x y z:W. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z) /\
   WF(\x y. R y x)`;;

(* ------------------------------------------------------------------------- *)
(* Subformulas.                                                              *)
(* ------------------------------------------------------------------------- *)

let IN_MINOR_RULES,IN_MINOR_INDUCT,IN_MINOR_CASES = new_inductive_set
  `(!p. p IN MINOR (Not p)) /\
   (!p q. p IN MINOR (p && q)) /\
   (!p q. q IN MINOR (p && q)) /\
   (!p q. p IN MINOR (p || q)) /\
   (!p q. q IN MINOR (p || q)) /\
   (!p q. p IN MINOR (p --> q)) /\
   (!p q. q IN MINOR (p --> q)) /\
   (!p q. p IN MINOR (p <-> q)) /\
   (!p q. q IN MINOR (p <-> q)) /\
   (!p. p IN MINOR (Box p))`;;

let MINOR_CLAUSES = prove
 (`MINOR False = {} /\
   MINOR True = {} /\
   MINOR (Atom s) = {} /\
   (!p. MINOR (Not p) = {p}) /\
   (!p q. MINOR (p && q) = {p,q}) /\
   (!p q. MINOR (p || q) = {p,q}) /\
   (!p q. MINOR (p --> q) = {p,q}) /\
   (!p q. MINOR (p <-> q) = {p,q}) /\
   (!p. MINOR (Box p) = {p})`,
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; IN_MINOR_CASES;
              distinctness "form"; injectivity "form"] THEN
  MESON_TAC[]);;

parse_as_infix("SUBFORMULA",get_infix_status "SUBSET");;

let SUBFORMULA = new_definition
  `(SUBFORMULA) = RTC (\p q. p IN MINOR q)`;;

let SUBFORMULA_REFL = prove
 (`!p. p SUBFORMULA p`,
  REWRITE_TAC[SUBFORMULA; RTC_REFL]);;

let SUBFORMULA_TRANS = prove
 (`!p q r. p SUBFORMULA q /\ q SUBFORMULA r ==> p SUBFORMULA r`,
  REWRITE_TAC[SUBFORMULA; RTC_TRANS]);;

let SUBFORMULA_CASES_L = prove
 (`!p q. p SUBFORMULA q <=> p = q \/ (?r. p SUBFORMULA r /\ r IN MINOR q)`,
  REWRITE_TAC[SUBFORMULA] THEN MESON_TAC[RTC_CASES_L]);;

let FINITE_SUBFORMULA = prove
 (`!p. FINITE {q | q SUBFORMULA p}`,
  MATCH_MP_TAC form_INDUCT THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SUBFORMULA_CASES_L] THEN
  ASM_REWRITE_TAC[MINOR_CLAUSES; IN_INSERT; NOT_IN_EMPTY;
    SET_RULE `{x | x = a} = {a}`;
    SET_RULE `{q | q = a \/ P q} = a INSERT {q | P q}`;
    SET_RULE `{q | ?r. q SUBFORMULA r /\ r = a} = {q | q SUBFORMULA a}`;
    SET_RULE `{q | ?r. q SUBFORMULA r /\ (r = a0 \/ r = a1)} =
                       {q | q SUBFORMULA a0} UNION {q | q SUBFORMULA a1}`;
    EMPTY_GSPEC; FINITE_UNION;  FINITE_INSERT; FINITE_EMPTY]);;

let FINITE_SUBSET_SUBFORMULAS_LEMMA = prove
 (`!p. FINITE {A | A SUBSET {q | q SUBFORMULA p} UNION
                            {Not q | q SUBFORMULA p}}`,
  REWRITE_TAC[FINITE_POWERSET_EQ; FINITE_UNION; FINITE_SUBFORMULA] THEN
  REWRITE_TAC[SET_RULE `{Not q | q SUBFORMULA p} =
                        IMAGE (Not) {q | q SUBFORMULA p}`] THEN
  GEN_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN
  REWRITE_TAC[FINITE_SUBFORMULA]);;

let SUBFORMULA_INVERSION = prove
 (`(!p. p SUBFORMULA False <=> p = False) /\
   (!p. p SUBFORMULA True <=> p = True) /\
   (!p s. p SUBFORMULA (Atom s) <=> p = Atom s) /\
   (!p q. p SUBFORMULA (Not q) <=> p = Not q \/ p SUBFORMULA q) /\
   (!p q r. p SUBFORMULA (q && r) <=>
            p = q && r \/ p SUBFORMULA q \/ p SUBFORMULA r) /\
   (!p q r. p SUBFORMULA (q || r) <=>
            p = q || r \/ p SUBFORMULA q \/ p SUBFORMULA r) /\
   (!p q r. p SUBFORMULA (q --> r) <=>
            p = q --> r \/ p SUBFORMULA q \/ p SUBFORMULA r) /\
   (!p q r. p SUBFORMULA (q <-> r) <=>
            p = q <-> r \/ p SUBFORMULA q \/ p SUBFORMULA r) /\
   (!p q. p SUBFORMULA (Box q) <=> p = Box q \/ p SUBFORMULA q)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUBFORMULA_CASES_L] THEN
  REWRITE_TAC[MINOR_CLAUSES; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[SUBFORMULA_REFL]);;

let SUBFORMULA_LIST = prove
 (`!p. ?X. NOREPETITION X /\ (!q. MEM q X <=> q SUBFORMULA p)`,
  GEN_TAC THEN EXISTS_TAC `list_of_set {q | q SUBFORMULA p}` THEN
  SIMP_TAC[FINITE_SUBFORMULA; MEM_LIST_OF_SET; IN_ELIM_THM] THEN
  SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SUBFORMULA]);;
  MATCH_MP_TAC NOREPETITION_LIST_OF_SET

(* ------------------------------------------------------------------------- *)
(* Cardinality of the type of formulae.                                      *)
(* ------------------------------------------------------------------------- *)

let COUNTABLE_FORM = prove
 (`COUNTABLE (:form)`,
  (DESTRUCT_TAC "@size. size" o prove_general_recursive_function_exists)
    `?depth.
       depth False = 0 /\
       depth True = 0 /\
       (!a. depth (Atom a) = 0) /\
       (!p. depth (Not p) = depth p + 1) /\
       (!p q. depth (p && q) = MAX (depth p) (depth q) + 1) /\
       (!p q. depth (p || q) = MAX (depth p) (depth q) + 1) /\
       (!p q. depth (p --> q) = MAX (depth p) (depth q) + 1) /\
       (!p q. depth (p <-> q) = MAX (depth p) (depth q) + 1) /\
       (!p. depth (Box p) = depth p + 1)` THEN
  ABBREV_TAC `u n = {p:form | p | size p < n}` THEN
  POP_ASSUM (LABEL_TAC "u") THEN
  SUBGOAL_THEN `(:form) = UNIONS {u n | n | n IN (:num)}` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
   X_GEN_TAC `p:form` THEN EXISTS_TAC `u (size (p:form)+1):form->bool` THEN
   REMOVE_THEN "u" (fun th -> REWRITE_TAC[GSYM th]) THEN
   REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `m < m + 1`] THEN MESON_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC COUNTABLE_UNIONS THEN CONJ_TAC THENL
  [MATCH_MP_TAC COUNTABLE_SUBSET THEN
   EXISTS_TAC `IMAGE u (:num):(form->bool)->bool` THEN
   SIMP_TAC[NUM_COUNTABLE; COUNTABLE_IMAGE] THEN
   REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_IMAGE; IN_UNIV] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN
  INDUCT_TAC THENL
  [REMOVE_THEN "u" (fun th -> REWRITE_TAC[GSYM th]) THEN
   REWRITE_TAC[ARITH_RULE `!n. ~(n < 0)`; EMPTY_GSPEC; COUNTABLE_EMPTY];
   POP_ASSUM (LABEL_TAC "ind")] THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC
    `u (n:num) UNION
     {True, False} UNION
     IMAGE Atom (:string) UNION
     IMAGE (Not) (u n) UNION
     IMAGE (\(op,p,q). op p q)
           ({(&&),(||),(-->),(<->)} CROSS (u n) CROSS (u n)) UNION
     IMAGE (Box) (u n)` THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC[COUNTABLE_UNION; COUNTABLE_INSERT; COUNTABLE_EMPTY] THEN
   ASM_SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_STRING; COUNTABLE_CROSS;
                COUNTABLE_INSERT; COUNTABLE_EMPTY];
   ALL_TAC] THEN
  USE_THEN "u" (SUBST1_TAC o GSYM o SPEC `SUC n`) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  CLAIM_TAC "u_alt" `!p:form n:num. size p < n <=> p IN u n` THENL
  [USE_THEN "u" (fun th -> REWRITE_TAC[GSYM th]) THEN SET_TAC[]; ALL_TAC] THEN
  CLAIM_TAC "max"
    `!p q:form n:num. MAX (size p) (size q) < n <=> p IN u n /\ q IN u n` THENL
  [USE_THEN "u" (fun th -> REWRITE_TAC[GSYM th]) THEN
   SET_TAC[ARITH_RULE `!p q n. MAX p q < n <=> p < n /\ q < n`];
   ALL_TAC] THEN

  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `p:form` (cases "form")) THEN
  HYP REWRITE_TAC "size" [LT_0; IN_UNION; IN_INSERT; NOT_IN_EMPTY;
                          distinctness "form"; GSYM ADD1; LT_SUC] THEN
  HYP REWRITE_TAC "u_alt max" [] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; IN_INSERT; NOT_IN_EMPTY;
              distinctness "form"; injectivity "form"] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bisimulation.                                                             *)
(* ------------------------------------------------------------------------- *)

let BISIMIMULATION = new_definition
  `BISIMIMULATION (W1,R1,V1) (W2,R2,V2) Z <=>
   (!w1:A w2:B.
      Z w1 w2
      ==> w1 IN W1 /\ w2 IN W2 /\
          (!a:string. V1 a w1 <=> V2 a w2) /\
          (!w1'. R1 w1 w1' ==> ?w2'. w2' IN W2 /\ Z w1' w2' /\ R2 w2 w2') /\
          (!w2'. R2 w2 w2' ==> ?w1'. w1' IN W1 /\ Z w1' w2' /\ R1 w1 w1'))`;;

let BISIMIMULATION_HOLDS = prove
 (`!W1 R1 V1 W2 R2 V2 Z p w1:A w2:B.
     BISIMIMULATION (W1,R1,V1) (W2,R2,V2) Z /\
     Z w1 w2
     ==> (holds (W1,R1) V1 p w1 <=> holds (W2,R2) V2 p w2)`,
  SUBGOAL_THEN
    `!W1 R1 V1 W2 R2 V2 Z.
       BISIMIMULATION (W1,R1,V1) (W2,R2,V2) Z
       ==> !p w1:A w2:B.
             Z w1 w2
             ==> (holds (W1,R1) V1 p w1 <=> holds (W2,R2) V2 p w2)`
    (fun th -> MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN DISCH_TAC THEN
  MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC[holds] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bisimilarity.                                                             *)
(* ------------------------------------------------------------------------- *)

let BISIMILAR = new_definition
  `BISIMILAR (W1,R1,V1) (W2,R2,V2) (w1:A) (w2:B) <=>
   ?Z. BISIMIMULATION (W1,R1,V1) (W2,R2,V2) Z /\ Z w1 w2`;;

let BISIMILAR_IN = prove
 (`!W1 R1 V1 W2 R2 V2 w1:A w2:B.
     BISIMILAR (W1,R1,V1) (W2,R2,V2) w1 w2 ==> w1 IN W1 /\ w2 IN W2`,
  REWRITE_TAC[BISIMILAR; BISIMIMULATION] THEN MESON_TAC[]);;

let BISIMILAR_HOLDS = prove
 (`!W1 R1 V1 W2 R2 V2 w1:A w2:B.
     BISIMILAR (W1,R1,V1) (W2,R2,V2) w1 w2
     ==> (!p. holds (W1,R1) V1 p w1 <=> holds (W2,R2) V2 p w2)`,
  REWRITE_TAC[BISIMILAR] THEN MESON_TAC[BISIMIMULATION_HOLDS]);;

let BISIMILAR_HOLDS_IN = prove
 (`!W1 R1 W2 R2.
     (!V1 w1:A. ?V2 w2:B. BISIMILAR (W1,R1,V1) (W2,R2,V2) w1 w2)
     ==> (!p. holds_in (W2,R2) p ==> holds_in (W1,R1) p)`,
  REWRITE_TAC[holds_in] THEN MESON_TAC[BISIMILAR_HOLDS; BISIMILAR_IN]);;

let BISIMILAR_VALID = prove
 (`!L1 L2 .
    (!W1 R1 V1 w1:A.
       L1 (W1,R1) /\ w1 IN W1
       ==> ?W2 R2 V2 w2:B.
             L2 (W2,R2) /\
             BISIMILAR (W1,R1,V1) (W2,R2,V2) w1 w2)
    ==> (!p. L2 |= p ==> L1 |= p)`,
  REWRITE_TAC[valid; holds_in; FORALL_PAIR_THM] THEN
  MESON_TAC[BISIMILAR_HOLDS; BISIMILAR_IN]);;

(* ----------------------------------------------------------------------- *)
(* Further operators.                                                      *)
(* ----------------------------------------------------------------------- *)

parse_as_prefix "Diam";;
parse_as_prefix "Dotbox";;

let diam_DEF = new_definition
  `Diam p = Not Box Not p`;;

let dotbox_DEF = new_definition
  `Dotbox p = (Box p && p)`;;
