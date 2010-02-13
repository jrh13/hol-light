(* ========================================================================= *)
(* Godel's theorem in its true form.                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Classes of formulas, via auxiliary "shared" inductive definition.         *)
(* ------------------------------------------------------------------------- *)

let sigmapi_RULES,sigmapi_INDUCT,sigmapi_CASES = new_inductive_definition
  `(!b n. sigmapi b n False) /\
   (!b n. sigmapi b n True) /\
   (!b n s t. sigmapi b n (s === t)) /\
   (!b n s t. sigmapi b n (s << t)) /\
   (!b n s t. sigmapi b n (s <<= t)) /\
   (!b n p. sigmapi (~b) n p ==> sigmapi b n (Not p)) /\
   (!b n p q. sigmapi b n p /\ sigmapi b n q ==> sigmapi b n (p && q)) /\
   (!b n p q. sigmapi b n p /\ sigmapi b n q ==> sigmapi b n (p || q)) /\
   (!b n p q. sigmapi (~b) n p /\ sigmapi b n q ==> sigmapi b n (p --> q)) /\
   (!b n p q. (!b. sigmapi b n p) /\ (!b. sigmapi b n q)
            ==> sigmapi b n (p <-> q)) /\
   (!n x p. sigmapi T n p /\ ~(n = 0) ==> sigmapi T n (??x p)) /\
   (!n x p. sigmapi F n p /\ ~(n = 0) ==> sigmapi F n (!!x p)) /\
   (!b n x p t. sigmapi b n p /\ ~(x IN FVT t)
            ==> sigmapi b n (??x (V x << t && p))) /\
   (!b n x p t. sigmapi b n p /\ ~(x IN FVT t)
            ==> sigmapi b n (??x (V x <<= t && p))) /\
   (!b n x p t. sigmapi b n p /\ ~(x IN FVT t)
            ==> sigmapi b n (!!x (V x << t --> p))) /\
   (!b n x p t. sigmapi b n p /\ ~(x IN FVT t)
            ==> sigmapi b n (!!x (V x <<= t --> p))) /\
   (!b c n p. sigmapi b n p ==> sigmapi c (n + 1) p)`;;

let SIGMA = new_definition `SIGMA = sigmapi T`;;
let PI = new_definition `PI = sigmapi F`;;
let DELTA = new_definition `DELTA n p <=> SIGMA n p /\ PI n p`;;

let SIGMAPI_PROP = prove
 (`(!n b. sigmapi b n False <=> T) /\
   (!n b. sigmapi b n True <=> T) /\
   (!n b s t. sigmapi b n (s === t) <=> T) /\
   (!n b s t. sigmapi b n (s << t) <=> T) /\
   (!n b s t. sigmapi b n (s <<= t) <=> T) /\
   (!n b p. sigmapi b n (Not p) <=> sigmapi (~b) n p) /\
   (!n b p q. sigmapi b n (p && q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p || q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p --> q) <=> sigmapi (~b) n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p <-> q) <=> (sigmapi b n p /\ sigmapi (~b) n p) /\
                                        (sigmapi b n q /\ sigmapi (~b) n q))`,
   REWRITE_TAC[sigmapi_RULES] THEN
   GEN_REWRITE_TAC DEPTH_CONV [AND_FORALL_THM] THEN
   INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
   REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [sigmapi_CASES] THEN
   REWRITE_TAC[form_DISTINCT; form_INJ] THEN
   REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1;
               FORALL_BOOL_THM] THEN
   REWRITE_TAC[ARITH_RULE `~(0 = n + 1)`] THEN
   REWRITE_TAC[ARITH_RULE `(SUC m = n + 1) <=> (n = m)`; UNWIND_THM2] THEN
   ASM_REWRITE_TAC[] THEN
   BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[ADD1] THEN
   REWRITE_TAC[CONJ_ACI] THEN
   REWRITE_TAC[TAUT `(a \/ b <=> a) <=> (b ==> a)`] THEN
   MESON_TAC[sigmapi_RULES]);;

let SIGMAPI_MONO_LEMMA = prove
 (`(!b n p. sigmapi b n p ==> sigmapi b (n + 1) p) /\
   (!b n p. ~(n = 0) /\ sigmapi b (n - 1) p ==> sigmapi b n p) /\
   (!b n p. ~(n = 0) /\ sigmapi (~b) (n - 1) p ==> sigmapi b n p)`,
  CONJ_TAC THENL
   [REPEAT STRIP_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(n = 0) ==> (n = (n - 1) + 1)`))] THEN
  POP_ASSUM MP_TAC THEN ASM_MESON_TAC[sigmapi_RULES]);;

let SIGMAPI_REV_EXISTS = prove
 (`!n b x p. sigmapi b n (??x p) ==> sigmapi b n p`,
  MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [sigmapi_CASES] THEN
  REWRITE_TAC[form_DISTINCT; form_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SIGMAPI_PROP] THEN
  ASM_MESON_TAC[ARITH_RULE `n < n + 1`; sigmapi_RULES]);;

let SIGMAPI_REV_FORALL = prove
 (`!n b x p. sigmapi b n (!!x p) ==> sigmapi b n p`,
  MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [sigmapi_CASES] THEN
  REWRITE_TAC[form_DISTINCT; form_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SIGMAPI_PROP] THEN
  ASM_MESON_TAC[ARITH_RULE `n < n + 1`; sigmapi_RULES]);;

let SIGMAPI_CLAUSES_CODE = prove
 (`(!n b. sigmapi b n False <=> T) /\
   (!n b. sigmapi b n True <=> T) /\
   (!n b s t. sigmapi b n (s === t) <=> T) /\
   (!n b s t. sigmapi b n (s << t) <=> T) /\
   (!n b s t. sigmapi b n (s <<= t) <=> T) /\
   (!n b p. sigmapi b n (Not p) <=> sigmapi (~b) n p) /\
   (!n b p q. sigmapi b n (p && q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p || q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p --> q) <=> sigmapi (~b) n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p <-> q) <=> (sigmapi b n p /\ sigmapi (~b) n p) /\
                                        (sigmapi b n q /\ sigmapi (~b) n q)) /\
   (!n b x p. sigmapi b n (??x p) <=>
                if b /\ ~(n = 0) \/
                   ?q t. (p = (V x << t && q) \/ p = (V x <<= t && q)) /\
                         ~(x IN FVT t)
                then sigmapi b n p
                else ~(n = 0) /\ sigmapi (~b) (n - 1) (??x p)) /\
   (!n b x p. sigmapi b n (!!x p) <=>
                if ~b /\ ~(n = 0) \/
                   ?q t. (p = (V x << t --> q) \/ p = (V x <<= t --> q)) /\
                         ~(x IN FVT t)
                then sigmapi b n p
                else ~(n = 0) /\ sigmapi (~b) (n - 1) (!!x p))`,
  REWRITE_TAC[SIGMAPI_PROP] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [sigmapi_CASES] THEN
  REWRITE_TAC[form_DISTINCT; form_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ONCE_REWRITE_TAC[TAUT `a \/ b \/ c \/ d <=> (b \/ c) \/ (a \/ d)`] THEN
  REWRITE_TAC[CONJ_ASSOC; OR_EXISTS_THM; GSYM RIGHT_OR_DISTRIB] THEN
  REWRITE_TAC[TAUT 
   `(if b /\ c \/ d then e else c /\ f) <=>                
    d /\ e \/ c /\ ~d /\ (if b then e else f)`] THEN
  MATCH_MP_TAC(TAUT `(a <=> a') /\ (~a' ==> (b <=> b'))
                     ==> (a \/ b <=> a' \/ b')`) THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
     REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
     EQ_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
     REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[SIGMAPI_PROP] THEN
     SIMP_TAC[];
     ALL_TAC]) THEN
  (ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH_RULE `~(0 = n + 1)`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> (n = m + 1 <=> m = n - 1)`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  W(fun (asl,w) -> ASM_CASES_TAC (find_term is_exists w)) THEN
  ASM_REWRITE_TAC[CONTRAPOS_THM] THENL
   [DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CHOOSE_THEN(MP_TAC o MATCH_MP SIGMAPI_REV_EXISTS)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP(last(CONJUNCTS sigmapi_RULES))) THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(n = 0) ==> 1 <= n`];
    ASM_CASES_TAC `b:bool` THEN 
    ASM_REWRITE_TAC[TAUT `(a \/ b <=> a) <=> (b ==> a)`] THENL
     [DISCH_THEN(CHOOSE_THEN(MP_TAC o MATCH_MP SIGMAPI_REV_EXISTS)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP(last(CONJUNCTS sigmapi_RULES))) THEN
      ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(n = 0) ==> 1 <= n`];
      REWRITE_TAC[EXISTS_BOOL_THM] THEN
      REWRITE_TAC[TAUT `(a \/ b <=> a) <=> (b ==> a)`] THEN
      ONCE_REWRITE_TAC[sigmapi_CASES] THEN
      REWRITE_TAC[form_DISTINCT; form_INJ] THEN ASM_MESON_TAC[]];
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CHOOSE_THEN(MP_TAC o MATCH_MP SIGMAPI_REV_FORALL)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP(last(CONJUNCTS sigmapi_RULES))) THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(n = 0) ==> 1 <= n`];
    ASM_CASES_TAC `b:bool` THEN 
    ASM_REWRITE_TAC[TAUT `(a \/ b <=> a) <=> (b ==> a)`] THENL
     [REWRITE_TAC[EXISTS_BOOL_THM] THEN
      REWRITE_TAC[TAUT `(a \/ b <=> a) <=> (b ==> a)`] THEN
      ONCE_REWRITE_TAC[sigmapi_CASES] THEN
      REWRITE_TAC[form_DISTINCT; form_INJ] THEN ASM_MESON_TAC[];
      DISCH_THEN(CHOOSE_THEN(MP_TAC o MATCH_MP SIGMAPI_REV_FORALL)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP(last(CONJUNCTS sigmapi_RULES))) THEN
      ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(n = 0) ==> 1 <= n`]]]);;

let SIGMAPI_CLAUSES = prove
 (`(!n b. sigmapi b n False <=> T) /\
   (!n b. sigmapi b n True <=> T) /\
   (!n b s t. sigmapi b n (s === t) <=> T) /\
   (!n b s t. sigmapi b n (s << t) <=> T) /\
   (!n b s t. sigmapi b n (s <<= t) <=> T) /\
   (!n b p. sigmapi b n (Not p) <=> sigmapi (~b) n p) /\
   (!n b p q. sigmapi b n (p && q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p || q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p --> q) <=> sigmapi (~b) n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p <-> q) <=> (sigmapi b n p /\ sigmapi (~b) n p) /\
                                        (sigmapi b n q /\ sigmapi (~b) n q)) /\
   (!n b x p. sigmapi b n (??x p) <=>
                if b /\ ~(n = 0) \/
                   ?q t. (p = (V x << t && q) \/ p = (V x <<= t && q)) /\
                         ~(x IN FVT t)
                then sigmapi b n p
                else 2 <= n /\ sigmapi (~b) (n - 1) p) /\
   (!n b x p. sigmapi b n (!!x p) <=>
                if ~b /\ ~(n = 0) \/
                   ?q t. (p = (V x << t --> q) \/ p = (V x <<= t --> q)) /\
                         ~(x IN FVT t)
                then sigmapi b n p
                else 2 <= n /\ sigmapi (~b) (n - 1) p)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SIGMAPI_CLAUSES_CODE] THEN
  REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [SIGMAPI_CLAUSES_CODE] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(n - 1 = 0) <=> 2 <= n`] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Show that it respects substitution.                                       *)
(* ------------------------------------------------------------------------- *)

let SIGMAPI_FORMSUBST = prove
 (`!p v n b. sigmapi b n p ==> sigmapi b n (formsubst v p)`,
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[SIGMAPI_CLAUSES; formsubst] THEN SIMP_TAC[] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN MAP_EVERY X_GEN_TAC [`x:num`; `p:form`] THEN
  MATCH_MP_TAC(TAUT `(a ==> b /\ c) ==> (a ==> b) /\ (a ==> c)`) THEN
  DISCH_TAC THEN REWRITE_TAC[AND_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num->term`; `n:num`; `b:bool`] THEN
  REWRITE_TAC[FV] THEN LET_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SIGMAPI_CLAUSES] THEN
  ONCE_REWRITE_TAC[TAUT 
   `((if p \/ q then x else y) ==> (if p \/ q' then x' else y')) <=>
    (p /\ x ==> x') /\ 
    (~p ==> (if q then x else y) ==> (if q' then x' else y'))`] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  CONJ_TAC THEN DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC(TAUT
   `(p ==> p') /\ (x ==> x') /\ (y ==> y') /\ (y ==> x)
    ==> (if p then x else y) ==> (if p' then x' else y')`) THEN
  ASM_SIMP_TAC[SIGMAPI_MONO_LEMMA; ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[formsubst; form_INJ; termsubst] THEN
  REWRITE_TAC[form_DISTINCT] THEN
  ONCE_REWRITE_TAC[TAUT `((a /\ b) /\ c) /\ d <=> b /\ c /\ a /\ d`] THEN
  REWRITE_TAC[UNWIND_THM1; termsubst; VALMOD_BASIC] THEN 
  REWRITE_TAC[TERMSUBST_FVT; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `y:num` THEN REWRITE_TAC[valmod] THEN
  (COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV) [SYM th]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FV; FVT] THEN
  REWRITE_TAC[IN_DELETE; IN_UNION; IN_SING; GSYM DISJ_ASSOC] THEN
  REWRITE_TAC[TAUT `(a \/ b \/ c) /\ ~a <=> ~a /\ b \/ ~a /\ c`] THEN
  (COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]]) THEN
  W(fun (asl,w) -> let t = lhand(rand w) in
                   MP_TAC(SPEC (rand(rand t)) VARIANT_THM) THEN
                   SPEC_TAC(t,`u:num`)) THEN
  REWRITE_TAC[CONTRAPOS_THM; FORMSUBST_FV; IN_ELIM_THM; FV] THEN
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `y:num` THEN
  ASM_REWRITE_TAC[valmod; IN_UNION]);;

(* ------------------------------------------------------------------------- *)
(* Hence all our main concepts are OK.                                       *)
(* ------------------------------------------------------------------------- *)

let SIGMAPI_TAC ths =
  REPEAT STRIP_TAC THEN
  REWRITE_TAC ths THEN
  TRY(MATCH_MP_TAC SIGMAPI_FORMSUBST) THEN
  let ths' = ths @  [SIGMAPI_CLAUSES; form_DISTINCT;
                     form_INJ; GSYM CONJ_ASSOC; UNWIND_THM1; GSYM EXISTS_REFL;
                     FVT; IN_SING; ARITH_EQ] in
  REWRITE_TAC ths' THEN ASM_SIMP_TAC ths';;

let SIGMAPI_DIVIDES = prove
 (`!n s t. sigmapi b n (arith_divides s t)`,
  SIGMAPI_TAC[arith_divides]);;

let SIGMAPI_PRIME = prove
 (`!n t. sigmapi b n (arith_prime t)`,
  SIGMAPI_TAC[arith_prime; SIGMAPI_DIVIDES]);;

let SIGMAPI_PRIMEPOW = prove
 (`!n s t. sigmapi b n (arith_primepow s t)`,
  SIGMAPI_TAC[arith_primepow; SIGMAPI_DIVIDES; SIGMAPI_PRIME]);;

let SIGMAPI_RTC = prove
 (`(!s t. sigmapi T 1 (R s t))
   ==> !s t. sigmapi T 1 (arith_rtc R s t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arith_rtc] THEN
  MATCH_MP_TAC SIGMAPI_FORMSUBST THEN
  REWRITE_TAC[SIGMAPI_CLAUSES; form_INJ; GSYM CONJ_ASSOC; UNWIND_THM1;
              GSYM EXISTS_REFL; FVT; IN_SING; ARITH_EQ; SIGMAPI_DIVIDES;
              SIGMAPI_PRIME; SIGMAPI_PRIMEPOW; form_DISTINCT] THEN
  ASM_REWRITE_TAC[]);;

let SIGMAPI_RTCP = prove
 (`(!s t u. sigmapi T 1 (R s t u))
   ==> !s t u. sigmapi T 1 (arith_rtcp R s t u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arith_rtcp] THEN
  MATCH_MP_TAC SIGMAPI_FORMSUBST THEN
  REWRITE_TAC[SIGMAPI_CLAUSES; form_INJ; GSYM CONJ_ASSOC; UNWIND_THM1;
              GSYM EXISTS_REFL; FVT; IN_SING; ARITH_EQ; SIGMAPI_DIVIDES;
              SIGMAPI_PRIME; SIGMAPI_PRIMEPOW; form_DISTINCT] THEN
  ASM_REWRITE_TAC[]);;

let SIGMAPI_TERM1 = prove
 (`!s t. sigmapi T 1 (arith_term1 s t)`,
  SIGMAPI_TAC[arith_term1]);;

let SIGMAPI_TERM = prove
 (`!t. sigmapi T 1 (arith_term t)`,
  SIGMAPI_TAC[arith_term; SIGMAPI_RTC; SIGMAPI_TERM1]);;

let SIGMAPI_FORM1 = prove
 (`!s t. sigmapi T 1 (arith_form1 s t)`,
  SIGMAPI_TAC[arith_form1; SIGMAPI_TERM]);;

let SIGMAPI_FORM = prove
 (`!t. sigmapi T 1 (arith_form t)`,
  SIGMAPI_TAC[arith_form; SIGMAPI_RTC; SIGMAPI_FORM1]);;

let SIGMAPI_FREETERM1 = prove
 (`!s t u. sigmapi T 1 (arith_freeterm1 s t u)`,
  SIGMAPI_TAC[arith_freeterm1]);;

let SIGMAPI_FREETERM = prove
 (`!s t. sigmapi T 1 (arith_freeterm s t)`,
  SIGMAPI_TAC[arith_freeterm; SIGMAPI_FREETERM1; SIGMAPI_RTCP]);;

let SIGMAPI_FREEFORM1 = prove
 (`!s t u. sigmapi T 1 (arith_freeform1 s t u)`,
  SIGMAPI_TAC[arith_freeform1; SIGMAPI_FREETERM; SIGMAPI_FORM]);;

let SIGMAPI_FREEFORM = prove
 (`!s t. sigmapi T 1 (arith_freeform s t)`,
  SIGMAPI_TAC[arith_freeform; SIGMAPI_FREEFORM1; SIGMAPI_RTCP]);;

let SIGMAPI_AXIOM = prove
 (`!t. sigmapi T 1 (arith_axiom t)`,
  SIGMAPI_TAC[arith_axiom; SIGMAPI_FREEFORM; SIGMAPI_FREETERM; SIGMAPI_FORM;
              SIGMAPI_TERM]);;

let SIGMAPI_PROV1 = prove
 (`!A. (!t. sigmapi T 1 (A t)) ==> !s t. sigmapi T 1 (arith_prov1 A s t)`,
  SIGMAPI_TAC[arith_prov1; SIGMAPI_AXIOM]);;

let SIGMAPI_PROV = prove
 (`(!t. sigmapi T 1 (A t)) ==> !t. sigmapi T 1 (arith_prov A t)`,
  SIGMAPI_TAC[arith_prov; SIGMAPI_PROV1; SIGMAPI_RTC]);;

let SIGMAPI_PRIMRECSTEP = prove
 (`(!s t u. sigmapi T 1 (R s t u))
   ==> !s t. sigmapi T 1 (arith_primrecstep R s t)`,
  SIGMAPI_TAC[arith_primrecstep]);;

let SIGMAPI_PRIMREC = prove
 (`(!s t u. sigmapi T 1 (R s t u))
   ==> !s t. sigmapi T 1 (arith_primrec R c s t)`,
  SIGMAPI_TAC[arith_primrec; SIGMAPI_PRIMRECSTEP; SIGMAPI_RTC]);;

let  SIGMAPI_GNUMERAL1 = prove
 (`!s t. sigmapi T 1 (arith_gnumeral1 s t)`,
  SIGMAPI_TAC[arith_gnumeral1]);;

let SIGMAPI_GNUMERAL = prove
 (`!s t. sigmapi T 1 (arith_gnumeral s t)`,
  SIGMAPI_TAC[arith_gnumeral; arith_gnumeral1';
              SIGMAPI_GNUMERAL1; SIGMAPI_RTC]);;

let SIGMAPI_QSUBST = prove
 (`!x n p.  sigmapi T 1 p ==> sigmapi T 1 (qsubst(x,n) p)`,
  SIGMAPI_TAC[qsubst]);;

let SIGMAPI_QDIAG = prove
 (`!x s t. sigmapi T 1 (arith_qdiag x s t)`,
  SIGMAPI_TAC[arith_qdiag; SIGMAPI_GNUMERAL]);;

let SIGMAPI_DIAGONALIZE = prove
 (`!x p. sigmapi T 1 p ==> sigmapi T 1 (diagonalize x p)`,
  SIGMAPI_TAC[diagonalize; SIGMAPI_QDIAG;
        SIGMAPI_FORMSUBST; LET_DEF; LET_END_DEF]);;

let SIGMAPI_FIXPOINT = prove
 (`!x p. sigmapi T 1 p ==> sigmapi T 1 (fixpoint x p)`,
  SIGMAPI_TAC[fixpoint; qdiag; SIGMAPI_QSUBST; SIGMAPI_DIAGONALIZE]);;

(* ------------------------------------------------------------------------- *)
(* The Godel sentence, "H" being Sigma and "G" being Pi.                     *)
(* ------------------------------------------------------------------------- *)

let hsentence = new_definition
  `hsentence Arep =
    fixpoint 0 (arith_prov Arep (arith_pair (numeral 4) (V 0)))`;;

let gsentence = new_definition
  `gsentence Arep = Not(hsentence Arep)`;;

let FV_HSENTENCE = prove
 (`!Arep. (!t. FV(Arep t) = FVT t) ==> (FV(hsentence Arep) = {})`,
  SIMP_TAC[hsentence; FV_FIXPOINT; FV_PROV] THEN
  REWRITE_TAC[FVT_PAIR; FVT_NUMERAL; FVT; UNION_EMPTY; DELETE_INSERT;
              EMPTY_DELETE]);;

let FV_GSENTENCE = prove
 (`!Arep. (!t. FV(Arep t) = FVT t) ==> (FV(gsentence Arep) = {})`,
  SIMP_TAC[gsentence; FV_HSENTENCE; FV]);;

let SIGMAPI_HSENTENCE = prove
 (`!Arep. (!t. sigmapi T 1 (Arep t)) ==> sigmapi T 1 (hsentence Arep)`,
  SIGMAPI_TAC[hsentence; SIGMAPI_FIXPOINT; SIGMAPI_PROV]);;

let SIGMAPI_GSENTENCE = prove
 (`!Arep. (!t. sigmapi T 1 (Arep t)) ==> sigmapi F 1 (gsentence Arep)`,
  SIGMAPI_TAC[gsentence; SIGMAPI_HSENTENCE]);;

(* ------------------------------------------------------------------------- *)
(* Hence the key fixpoint properties.                                        *)
(* ------------------------------------------------------------------------- *)

let HSENTENCE_FIX_STRONG = prove
 (`!A Arep.
        (!v t. holds v (Arep t) <=> (termval v t) IN IMAGE gform A)
        ==> !v. holds v (hsentence Arep) <=> A |-- Not(hsentence Arep)`,
  REWRITE_TAC[hsentence; true_def; HOLDS_FIXPOINT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ARITH_PROV) THEN
  REWRITE_TAC[IN] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[ARITH_PAIR; TERMVAL_NUMERAL] THEN
  REWRITE_TAC[termval; valmod; GSYM gform] THEN REWRITE_TAC[PROV_THM]);;

let HSENTENCE_FIX = prove
 (`!A Arep.
        (!v t. holds v (Arep t) <=> (termval v t) IN IMAGE gform A)
        ==> (true(hsentence Arep) <=> A |-- Not(hsentence Arep))`,
  REWRITE_TAC[true_def] THEN MESON_TAC[HSENTENCE_FIX_STRONG]);;

let GSENTENCE_FIX = prove
 (`!A Arep.
        (!v t. holds v (Arep t) <=> (termval v t) IN IMAGE gform A)
        ==> (true(gsentence Arep) <=> ~(A |-- gsentence Arep))`,
  REWRITE_TAC[true_def; holds; gsentence] THEN
  MESON_TAC[HSENTENCE_FIX_STRONG]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary concepts.                                                       *)
(* ------------------------------------------------------------------------- *)

let ground = new_definition
  `ground t <=> (FVT t = {})`;;

let complete_for = new_definition
  `complete_for P A <=> !p. P p /\ true p ==> A |-- p`;;

let sound_for = new_definition
  `sound_for P A <=> !p. P p /\ A |-- p ==> true p`;;

let consistent = new_definition
  `consistent A <=> ~(?p. A |-- p /\ A |-- Not p)`;;

(* ------------------------------------------------------------------------- *)
(* The purest and most symmetric and beautiful form of G1.                   *)
(* ------------------------------------------------------------------------- *)

let DEFINABLE_BY_ONEVAR = prove
 (`definable_by (SIGMA 1) s <=>
        ?p x. SIGMA 1 p /\ (FV p = {x}) /\ !v. holds v p <=> (v x) IN s`,
  REWRITE_TAC[definable_by; SIGMA] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:form` (X_CHOOSE_TAC `x:num`)) THEN
  EXISTS_TAC `(V x === V x) && formsubst (\y. if y = x then V x else Z) p` THEN
  EXISTS_TAC `x:num` THEN ASM_SIMP_TAC[SIGMAPI_CLAUSES; SIGMAPI_FORMSUBST] THEN
  ASM_REWRITE_TAC[HOLDS_FORMSUBST; FORMSUBST_FV; FV; holds] THEN
  REWRITE_TAC[COND_RAND; EXTENSION; IN_ELIM_THM; IN_SING; FVT; IN_UNION;
              COND_EXPAND; NOT_IN_EMPTY; o_THM; termval] THEN
  MESON_TAC[]);;

let CLOSED_NOT_TRUE = prove
 (`!p. closed p ==> (true(Not p) <=> ~(true p))`,
  REWRITE_TAC[closed; true_def; holds] THEN
  MESON_TAC[HOLDS_VALUATION; NOT_IN_EMPTY]);;

let CONSISTENT_ALT = prove
 (`!A p. A |-- p /\ A |-- Not p <=> A |-- False`,
  MESON_TAC[proves_RULES; ex_falso; axiom_not; iff_imp1]);;

let G1 = prove
 (`!A. definable_by (SIGMA 1) (IMAGE gform A)
       ==> ?G. PI 1 G /\ closed G /\
               (sound_for (PI 1 INTER closed) A ==> true G /\ ~(A |-- G)) /\
               (sound_for (SIGMA 1 INTER closed) A ==> ~(A |-- Not G))`,
  GEN_TAC THEN
  REWRITE_TAC[sound_for; INTER; IN_ELIM_THM; DEFINABLE_BY_ONEVAR] THEN
  DISCH_THEN(X_CHOOSE_THEN `Arep:form` (X_CHOOSE_THEN `a:num`
        STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`A:form->bool`; `\t. formsubst ((a |-> t) V) Arep`]
         GSENTENCE_FIX) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[HOLDS_FORMSUBST] THEN REWRITE_TAC[termval; valmod; o_THM];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `gsentence (\t. formsubst ((a |-> t) V) Arep)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c /\ d) ==> a /\ b /\ c /\ d`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[PI] THEN MATCH_MP_TAC SIGMAPI_GSENTENCE THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SIGMA]) THEN ASM_SIMP_TAC[SIGMAPI_FORMSUBST];
    REWRITE_TAC[closed] THEN MATCH_MP_TAC FV_GSENTENCE THEN
    ASM_REWRITE_TAC[FORMSUBST_FV; EXTENSION; IN_ELIM_THM; IN_SING;
                    valmod; UNWIND_THM2];
    ALL_TAC] THEN
  ABBREV_TAC `G = gsentence (\t. formsubst ((a |-> t) V) Arep)` THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[IN]; ALL_TAC] THEN
  SUBGOAL_THEN `true(Not G)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN] THEN
    REWRITE_TAC[SIGMA; SIGMAPI_CLAUSES] THEN ASM_MESON_TAC[closed; FV; PI];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CLOSED_NOT_TRUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `true False` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[true_def; holds]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[closed; IN; SIGMA; SIGMAPI_CLAUSES; FV] THEN
  ASM_MESON_TAC[CONSISTENT_ALT]);;

(* ------------------------------------------------------------------------- *)
(* Some more familiar variants.                                              *)
(* ------------------------------------------------------------------------- *)

let COMPLETE_SOUND_SENTENCE = prove
 (`consistent A /\ complete_for (sigmapi (~b) n INTER closed) A
   ==> sound_for (sigmapi b n INTER closed) A`,
  REWRITE_TAC[consistent; sound_for; complete_for; IN; INTER; IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> X_GEN_TAC `p:form` THEN MP_TAC(SPEC `Not p` th)) THEN
  REWRITE_TAC[SIGMAPI_CLAUSES] THEN
  REWRITE_TAC[closed; FV; true_def; holds] THEN
  ASM_MESON_TAC[HOLDS_VALUATION; NOT_IN_EMPTY]);;

let G1_TRAD = prove
 (`!A. consistent A /\
       complete_for (SIGMA 1 INTER closed) A /\
       definable_by (SIGMA 1) (IMAGE gform A)
       ==> ?G. PI 1 G /\ closed G /\ true G /\ ~(A |-- G) /\
               (sound_for (SIGMA 1 INTER closed) A ==> ~(A |-- Not G))`,
  REWRITE_TAC[SIGMA] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `A:form->bool` G1) THEN ASM_REWRITE_TAC[SIGMA; PI] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[COMPLETE_SOUND_SENTENCE]);;

(* ------------------------------------------------------------------------- *)
(* Closures and invariance of truth and provability.                         *)
(* ------------------------------------------------------------------------- *)

let generalize = new_definition
  `generalize vs p = ITLIST (!!) vs p`;;

let TRUE_GENERALIZE = prove
 (`!vs p. true(generalize vs p) <=> true p`,
  REWRITE_TAC[generalize; true_def] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; holds] THEN GEN_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  MESON_TAC[VALMOD_REPEAT]);;

let PROVABLE_GENERALIZE = prove
 (`!A p vs. A |-- generalize vs p <=> A |-- p`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[generalize] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MESON_TAC[spec; gen; FORMSUBST_TRIV; ASSIGN_TRIV]);;

let FV_GENERALIZE = prove
 (`!p vs. FV(generalize vs p) = FV(p) DIFF (set_of_list vs)`,
  GEN_TAC THEN REWRITE_TAC[generalize] THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[set_of_list; DIFF_EMPTY; ITLIST] THEN
   ASM_REWRITE_TAC[FV] THEN SET_TAC[]);;

let closure = new_definition
  `closure p = generalize (list_of_set(FV p)) p`;;

let CLOSED_CLOSURE = prove
 (`!p. closed(closure p)`,
  REWRITE_TAC[closed; closure; FV_GENERALIZE] THEN
  SIMP_TAC[SET_OF_LIST_OF_SET; FV_FINITE; DIFF_EQ_EMPTY]);;

let TRUE_CLOSURE = prove
 (`!p. true(closure p) <=> true p`,
  REWRITE_TAC[closure; TRUE_GENERALIZE]);;

let PROVABLE_CLOSURE = prove
 (`!A p. A |-- closure p <=> A |-- p`,
  REWRITE_TAC[closure; PROVABLE_GENERALIZE]);;

(* ------------------------------------------------------------------------- *)
(* Other stuff.                                                              *)
(* ------------------------------------------------------------------------- *)

let complete = new_definition
  `complete A <=> !p. closed p ==> A |-- p \/ A |-- Not p`;;

let sound = new_definition
  `sound A <=> !p. A |-- p ==> true p`;;

let semcomplete = new_definition
  `semcomplete A <=> !p. true p ==> A |-- p`;;

let DEFINABLE_DEFINABLE_BY = prove
 (`definable = definable_by (\x. T)`,
  REWRITE_TAC[FUN_EQ_THM; definable; definable_by]);;

let DEFINABLE_ONEVAR = prove
 (`definable s <=> ?p x. (FV p = {x}) /\ !v. holds v p <=> (v x) IN s`,
  REWRITE_TAC[definable] THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:form` (X_CHOOSE_TAC `x:num`)) THEN
  EXISTS_TAC `(V x === V x) && formsubst (\y. if y = x then V x else Z) p` THEN
  EXISTS_TAC `x:num` THEN
  ASM_REWRITE_TAC[HOLDS_FORMSUBST; FORMSUBST_FV; FV; holds] THEN
  REWRITE_TAC[COND_RAND; EXTENSION; IN_ELIM_THM; IN_SING; FVT; IN_UNION;
              COND_EXPAND; NOT_IN_EMPTY; o_THM; termval] THEN
  MESON_TAC[]);;

let CLOSED_TRUE_OR_FALSE = prove
 (`!p. closed p ==> true p \/ true(Not p)`,
  REWRITE_TAC[closed; true_def; holds] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[HOLDS_VALUATION; NOT_IN_EMPTY]);;

let SEMCOMPLETE_IMP_COMPLETE = prove
 (`!A. semcomplete A ==> complete A`,
  REWRITE_TAC[semcomplete; complete] THEN MESON_TAC[CLOSED_TRUE_OR_FALSE]);;

let SOUND_CLOSED = prove
 (`sound A = !p. closed p /\ A |-- p ==> true p`,
  REWRITE_TAC[sound] THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MESON_TAC[TRUE_CLOSURE; PROVABLE_CLOSURE; CLOSED_CLOSURE]);;

let SOUND_IMP_CONSISTENT = prove
 (`!A. sound A ==> consistent A`,
  REWRITE_TAC[sound; consistent; CONSISTENT_ALT] THEN
  SUBGOAL_THEN `~(true False)` (fun th -> MESON_TAC[th]) THEN
  REWRITE_TAC[true_def; holds]);;

let SEMCOMPLETE_SOUND_EQ_CONSISTENT = prove
 (`!A. semcomplete A ==> (sound A <=> consistent A)`,
  REWRITE_TAC[semcomplete] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[SOUND_IMP_CONSISTENT] THEN
  REWRITE_TAC[consistent; SOUND_CLOSED] THEN
  ASM_MESON_TAC[CLOSED_TRUE_OR_FALSE]);;
