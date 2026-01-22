(* ========================================================================= *)
(* Proof that provability is definable; weak form of Godel's theorem.        *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Auxiliary predicate: all numbers in an iterated-pair "list".              *)
(* ------------------------------------------------------------------------- *)

let ALLN_DEF =
  let th = prove
   (`!P. ?ALLN. !z.
         ALLN z <=>
                if ?x y. z = NPAIR x y
                then P (@x. ?y. NPAIR x y = z) /\
                     ALLN (@y. ?x. NPAIR x y = z)
                else T`,
    GEN_TAC THEN MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    BINOP_TAC THENL [ALL_TAC; FIRST_ASSUM MATCH_MP_TAC] THEN
    FIRST_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[NPAIR_INJ; RIGHT_EXISTS_AND_THM; EXISTS_REFL;
                SELECT_REFL; NPAIR_LT; LEFT_EXISTS_AND_THM]) in
  new_specification ["ALLN"] (REWRITE_RULE[SKOLEM_THM] th);;

let ALLN = prove
 (`(ALLN P 0 <=> T) /\
   (ALLN P (NPAIR x y) <=> P x /\ ALLN P y)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ALLN_DEF] THEN
  REWRITE_TAC[NPAIR_NONZERO] THEN
  REWRITE_TAC[NPAIR_INJ; LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[EXISTS_REFL; GSYM EXISTS_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Valid term.                                                               *)
(* ------------------------------------------------------------------------- *)

let TERM1 = new_definition
  `TERM1 x y <=>
        (?l u. (x = l) /\ (y = NPAIR (NPAIR 0 u) l)) \/
        (?l. (x = l) /\ (y = NPAIR (NPAIR 1 0) l)) \/
        (?t l. (x = NPAIR t l) /\ (y = NPAIR (NPAIR 2 t) l)) \/
        (?n s t l. ((n = 3) \/ (n = 4)) /\
                   (x = NPAIR s (NPAIR t l)) /\
                   (y = NPAIR (NPAIR n (NPAIR s t)) l))`;;

let TERM = new_definition
  `TERM n <=> RTC TERM1 0 (NPAIR n 0)`;;

let isagterm = new_definition
  `isagterm n <=> ?t. n = gterm t`;;

let TERM_LEMMA1 = prove
 (`!x y. TERM1 x y ==> ALLN isagterm x ==> ALLN isagterm y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TERM1] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; ALLN; isagterm] THEN
  MESON_TAC[gterm; NUMBER_SURJ]);;

let TERM_LEMMA2 = prove
 (`!t a. RTC TERM1 a (NPAIR (gterm t) a)`,
  MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC[gterm] THEN
  MESON_TAC[RTC_INC; RTC_TRANS; TERM1]);;

let TERM_THM = prove
 (`!n. TERM n <=> ?t. n = gterm t`,
  GEN_TAC THEN REWRITE_TAC[TERM] THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[TERM_LEMMA2]] THEN
  SUBGOAL_THEN `!x y. RTC TERM1 x y ==> ALLN isagterm x ==> ALLN isagterm y`
   (fun th -> MESON_TAC[ALLN; isagterm; th]) THEN
  MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[TERM_LEMMA1] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Valid formula.                                                            *)
(* ------------------------------------------------------------------------- *)

let FORM1 = new_definition
  `FORM1 x y <=>
        (?l. (x = l) /\ (y = NPAIR (NPAIR 0 0) l)) \/
        (?l. (x = l) /\ (y = NPAIR (NPAIR 0 1) l)) \/
        (?n s t l. ((n = 1) \/ (n = 2) \/ (n = 3)) /\
                   TERM s /\ TERM t /\
                   (x = l) /\
                   (y = NPAIR (NPAIR n (NPAIR s t)) l)) \/
        (?p l. (x = NPAIR p l) /\
               (y = NPAIR (NPAIR 4 p) l)) \/
        (?n p q l. ((n = 5) \/ (n = 6) \/ (n = 7) \/ (n = 8)) /\
                   (x = NPAIR p (NPAIR q l)) /\
                   (y = NPAIR (NPAIR n (NPAIR p q)) l)) \/
        (?n u p l. ((n = 9) \/ (n = 10)) /\
                   (x = NPAIR p l) /\
                   (y = NPAIR (NPAIR n (NPAIR u p)) l))`;;

let FORM = new_definition
  `FORM n <=> RTC FORM1 0 (NPAIR n 0)`;;

let isagform = new_definition
  `isagform n <=> ?t. n = gform t`;;

let FORM_LEMMA1 = prove
 (`!x y. FORM1 x y ==> ALLN isagform x ==> ALLN isagform y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FORM1] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; ALLN; isagform] THEN
  MESON_TAC[gform; TERM_THM; NUMBER_SURJ]);;

(*** Following really blows up if we just use FORM1
 *** instead of manually breaking up the conjuncts
 ***)

let FORM_LEMMA2 = prove
 (`!p a. RTC FORM1 a (NPAIR (gform p) a)`,
  MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC[gform] THEN
  REPEAT CONJ_TAC THEN
  MESON_TAC[RTC_INC; RTC_TRANS; TERM_THM;
     REWRITE_RULE[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`]
                 (snd(EQ_IMP_RULE (SPEC_ALL FORM1)))]);;

let FORM_THM = prove
 (`!n. FORM n <=> ?p. n = gform p`,
  GEN_TAC THEN REWRITE_TAC[FORM] THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[FORM_LEMMA2]] THEN
  SUBGOAL_THEN `!x y. RTC FORM1 x y ==> ALLN isagform x ==> ALLN isagform y`
   (fun th -> MESON_TAC[ALLN; isagform; th]) THEN
  MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[FORM_LEMMA1] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Term without particular variable.                                         *)
(* ------------------------------------------------------------------------- *)

let FREETERM1 = new_definition
  `FREETERM1 m x y <=>
        (?l u. ~(u = m) /\ (x = l) /\ (y = NPAIR (NPAIR 0 u) l)) \/
        (?l. (x = l) /\ (y = NPAIR (NPAIR 1 0) l)) \/
        (?t l. (x = NPAIR t l) /\ (y = NPAIR (NPAIR 2 t) l)) \/
        (?n s t l. ((n = 3) \/ (n = 4)) /\
                   (x = NPAIR s (NPAIR t l)) /\
                   (y = NPAIR (NPAIR n (NPAIR s t)) l))`;;

let FREETERM = new_definition
  `FREETERM m n <=> RTC (FREETERM1 m) 0 (NPAIR n 0)`;;

let isafterm = new_definition
  `isafterm m n <=> ?t. ~(m IN IMAGE number (FVT t)) /\ (n = gterm t)`;;

let ISAFTERM = prove
 (`(~(number x = m) ==> isafterm m (NPAIR 0 (number x))) /\
   isafterm m (NPAIR 1 0) /\
   (isafterm m t ==> isafterm m (NPAIR 2 t)) /\
   (isafterm m s /\ isafterm m t ==> isafterm m (NPAIR 3 (NPAIR s t))) /\
   (isafterm m s /\ isafterm m t ==> isafterm m (NPAIR 4 (NPAIR s t)))`,
  REWRITE_TAC[isafterm; gterm] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `V x`;
    EXISTS_TAC `Z`;
    DISCH_THEN(X_CHOOSE_THEN `t:term` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Suc t`;
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `t:term` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `s ++ t`;
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `t:term` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `s ** t`] THEN
  ASM_REWRITE_TAC[gterm; FVT; IMAGE_UNION; NOT_IN_EMPTY; IN_SING; IN_UNION;
                  IMAGE_CLAUSES]);;

let FREETERM_LEMMA1 = prove
 (`!m x y. FREETERM1 m x y ==> ALLN (isafterm m) x ==> ALLN (isafterm m) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FREETERM1] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; ALLN] THEN
  MESON_TAC[ISAFTERM; NUMBER_SURJ]);;

let FREETERM_LEMMA2 = prove
 (`!m t a. ~(m IN IMAGE number (FVT t))
           ==> RTC (FREETERM1 m) a (NPAIR (gterm t) a)`,
  GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[gterm; FVT; NOT_IN_EMPTY; IN_SING; IN_UNION;
              IMAGE_CLAUSES; IMAGE_UNION] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  REPEAT CONJ_TAC THEN
  TRY(REPEAT GEN_TAC THEN DISCH_THEN
   (fun th -> GEN_TAC THEN STRIP_TAC THEN MP_TAC th)) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[RTC_INC; RTC_TRANS; FREETERM1]);;

let FREETERM_THM = prove
 (`!m n. FREETERM m n <=> ?t. ~(m IN IMAGE number (FVT(t))) /\ (n = gterm t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FREETERM] THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[FREETERM_LEMMA2]] THEN
  SUBGOAL_THEN `!x y. RTC (FREETERM1 m) x y
                      ==> ALLN (isafterm m) x ==> ALLN (isafterm m) y`
   (fun th -> MESON_TAC[ALLN; isagterm; isafterm; th]) THEN
  MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[FREETERM_LEMMA1] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Formula without particular free variable.                                 *)
(* ------------------------------------------------------------------------- *)

let FREEFORM1 = new_definition
  `FREEFORM1 m x y <=>
        (?l. (x = l) /\ (y = NPAIR (NPAIR 0 0) l)) \/
        (?l. (x = l) /\ (y = NPAIR (NPAIR 0 1) l)) \/
        (?n s t l. ((n = 1) \/ (n = 2) \/ (n = 3)) /\
                   FREETERM m s /\ FREETERM m t /\
                   (x = l) /\
                   (y = NPAIR (NPAIR n (NPAIR s t)) l)) \/
        (?p l. (x = NPAIR p l) /\
               (y = NPAIR (NPAIR 4 p) l)) \/
        (?n p q l. ((n = 5) \/ (n = 6) \/ (n = 7) \/ (n = 8)) /\
                   (x = NPAIR p (NPAIR q l)) /\
                   (y = NPAIR (NPAIR n (NPAIR p q)) l)) \/
        (?n u p l. ((n = 9) \/ (n = 10)) /\
                   (x = NPAIR p l) /\
                   (y = NPAIR (NPAIR n (NPAIR u p)) l)) \/
        (?n p l. ((n = 9) \/ (n = 10)) /\
                 (x = l) /\ FORM p /\
                 (y = NPAIR (NPAIR n (NPAIR m p)) l))`;;

let FREEFORM = new_definition
  `FREEFORM m n <=> RTC (FREEFORM1 m) 0 (NPAIR n 0)`;;

let isafform = new_definition
  `isafform m n <=> ?p. ~(m IN IMAGE number (FV p)) /\ (n = gform p)`;;

let ISAFFORM = prove
 (`isafform m (NPAIR 0 0) /\
   isafform m (NPAIR 0 1) /\
   (isafterm m s /\ isafterm m t ==> isafform m (NPAIR 1 (NPAIR s t))) /\
   (isafterm m s /\ isafterm m t ==> isafform m (NPAIR 2 (NPAIR s t))) /\
   (isafterm m s /\ isafterm m t ==> isafform m (NPAIR 3 (NPAIR s t))) /\
   (isafform m p ==> isafform m (NPAIR 4 p)) /\
   (isafform m p /\ isafform m q ==> isafform m (NPAIR 5 (NPAIR p q))) /\
   (isafform m p /\ isafform m q ==> isafform m (NPAIR 6 (NPAIR p q))) /\
   (isafform m p /\ isafform m q ==> isafform m (NPAIR 7 (NPAIR p q))) /\
   (isafform m p /\ isafform m q ==> isafform m (NPAIR 8 (NPAIR p q))) /\
   (isafform m p ==> isafform m (NPAIR 9 (NPAIR x p))) /\
   (isafform m p ==> isafform m (NPAIR 10 (NPAIR x p))) /\
   (isagform p ==> isafform m (NPAIR 9 (NPAIR m p))) /\
   (isagform p ==> isafform m (NPAIR 10 (NPAIR m p)))`,
  let tac0 = DISCH_THEN(X_CHOOSE_THEN `p:form` STRIP_ASSUME_TAC)
  and  tac1 =
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `s:term` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `t:term` STRIP_ASSUME_TAC))
  and tac2 =
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `p:form` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `q:form` STRIP_ASSUME_TAC)) in
  REWRITE_TAC[isafform; gform; isagform; isafterm] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `False`;
    EXISTS_TAC `True`;
    tac1 THEN EXISTS_TAC `s === t`;
    tac1 THEN EXISTS_TAC `s << t`;
    tac1 THEN EXISTS_TAC `s <<= t`;
    tac0 THEN EXISTS_TAC `Not p`;
    tac2 THEN EXISTS_TAC `p && q`;
    tac2 THEN EXISTS_TAC `p || q`;
    tac2 THEN EXISTS_TAC `p --> q`;
    tac2 THEN EXISTS_TAC `p <-> q`;
    tac0 THEN EXISTS_TAC `!!(denumber x) p`;
    tac0 THEN EXISTS_TAC `??(denumber x) p`;
    tac0 THEN EXISTS_TAC `!!(denumber m) p`;
    tac0 THEN EXISTS_TAC `??(denumber m) p`] THEN
  ASM_REWRITE_TAC[FV; IN_DELETE; NOT_IN_EMPTY; IN_SING; IN_UNION; gform;
                  NUMBER_DENUMBER; IMAGE_CLAUSES; IMAGE_UNION] THEN
  ASM SET_TAC[NUMBER_DENUMBER]);;

let FREEFORM_LEMMA1 = prove
 (`!x y. FREEFORM1 m x y ==> ALLN (isafform m) x ==> ALLN (isafform m) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FREEFORM1] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; ALLN] THEN
  REWRITE_TAC[FREETERM_THM; GSYM isafterm] THEN
  REWRITE_TAC[FORM_THM; GSYM isagform] THEN MESON_TAC[ISAFFORM]);;

let FREEFORM_LEMMA2 = prove
 (`!m p a. ~(m IN IMAGE number (FV p))
           ==> RTC (FREEFORM1 m) a (NPAIR (gform p) a)`,
  let lemma = prove
   (`m IN IMAGE number (s DELETE k) <=>
     m IN IMAGE number s /\ ~(m = number k)`,
    SET_TAC[NUMBER_INJ]) in
  GEN_TAC THEN MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[gform; FV; NOT_IN_EMPTY; IN_DELETE; IN_SING; IN_UNION;
              lemma; IMAGE_UNION; IMAGE_CLAUSES] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  REPEAT CONJ_TAC THEN
  TRY(REPEAT GEN_TAC THEN DISCH_THEN
   (fun th -> GEN_TAC THEN STRIP_TAC THEN MP_TAC th)) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[RTC_INC; RTC_TRANS; FORM_THM;
        REWRITE_RULE[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                     FREETERM_THM]
                 (snd(EQ_IMP_RULE (SPEC_ALL FREEFORM1)))]);;

let FREEFORM_THM = prove
 (`!m n. FREEFORM m n <=> ?p. ~(m IN IMAGE number (FV p)) /\ (n = gform p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FREEFORM] THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[FREEFORM_LEMMA2]] THEN
  SUBGOAL_THEN `!x y. RTC (FREEFORM1 m) x y
                      ==> ALLN (isafform m) x ==> ALLN (isafform m) y`
   (fun th -> MESON_TAC[ALLN; isagform; isafform; th]) THEN
  MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[FREEFORM_LEMMA1] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetization of logical axioms --- autogenerated.                      *)
(* ------------------------------------------------------------------------- *)

let AXIOM,AXIOM_THM =
  let th0 = prove
   (`((?x p. P (number x) (gform p) /\ ~(x IN FV(p))) <=>
      (?x p. FREEFORM x p /\ P x p)) /\
     ((?x t. P (number x) (gterm t) /\ ~(x IN FVT(t))) <=>
      (?x t. FREETERM x t /\ P x t))`,
    REWRITE_TAC[FREETERM_THM; FREEFORM_THM] THEN CONJ_TAC THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
    GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
    REWRITE_TAC[UNWIND_THM2; IN_IMAGE] THEN
    ASM_MESON_TAC[IN_IMAGE; NUMBER_DENUMBER])
  and th1 = prove
   (`((?p. P(gform p)) <=> (?p. FORM(p) /\ P p)) /\
     ((?t. P(gterm t)) <=> (?t. TERM(t) /\ P t))`,
    MESON_TAC[FORM_THM; TERM_THM])
  and th2 = prove
   (`(?x. P(number x)) <=> (?x. P x)`,
    MESON_TAC[NUMBER_DENUMBER]) in
  let th = (REWRITE_CONV[GSYM GFORM_INJ] THENC
          REWRITE_CONV[gform; gterm] THENC
          REWRITE_CONV[th0] THENC REWRITE_CONV[th1] THENC
          REWRITE_CONV[th2] THENC
          REWRITE_CONV[RIGHT_AND_EXISTS_THM])
         (rhs(concl(SPEC `a:form` axiom_CASES))) in
  let dtm = mk_eq(`(AXIOM:num->bool) a`,
                   subst [`a:num`,`gform a`] (rhs(concl th))) in
  let AXIOM = new_definition dtm in
  let AXIOM_THM = prove
   (`!p. AXIOM(gform p) <=> axiom p`,
    REWRITE_TAC[axiom_CASES; AXIOM; th]) in
  AXIOM,AXIOM_THM;;

(* ------------------------------------------------------------------------- *)
(* Prove also that all AXIOMs are in fact numbers of formulas.               *)
(* ------------------------------------------------------------------------- *)

let GTERM_CASES_ALT = prove
 (`(gterm u = NPAIR 0 x <=> u = V(denumber x))`,
  REWRITE_TAC[GSYM GTERM_CASES; NUMBER_DENUMBER]);;

let GFORM_CASES_ALT = prove
 (`(gform r = NPAIR 9 (NPAIR x n) <=>
    (?p. r = !!(denumber x) p /\ gform p = n)) /\
   (gform r = NPAIR 10 (NPAIR x n) <=>
    (?p. r = ??(denumber x) p /\ gform p = n))`,
  REWRITE_TAC[GSYM GFORM_CASES; NUMBER_DENUMBER]);;

let AXIOM_FORMULA = prove
 (`!a. AXIOM a ==> ?p. a = gform p`,
  REWRITE_TAC[AXIOM; FREEFORM_THM; FREETERM_THM; FORM_THM; TERM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINDER_CONV SYM_CONV) THEN
  REWRITE_TAC[GFORM_CASES; GTERM_CASES;
              GTERM_CASES_ALT; GFORM_CASES_ALT] THEN
  MESON_TAC[NUMBER_DENUMBER]);;

let AXIOM_THM_STRONG = prove
 (`!a. AXIOM a <=> ?p. axiom p /\ (a = gform p)`,
  MESON_TAC[AXIOM_THM; AXIOM_FORMULA]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetization of the full logical inference rules.                      *)
(* ------------------------------------------------------------------------- *)

let PROV1 = new_definition
  `PROV1 A x y <=>
        (?a. (AXIOM a \/ a IN A) /\ (y = NPAIR a x)) \/
        (?p q l. (x = NPAIR (NPAIR 7 (NPAIR p q)) (NPAIR p l)) /\
                 (y = NPAIR q l)) \/
        (?p u l. (x = NPAIR p l) /\ (y = NPAIR (NPAIR 9 (NPAIR u p)) l))`;;

let PROV = new_definition
  `PROV A n <=> RTC (PROV1 A) 0 (NPAIR n 0)`;;

let isaprove = new_definition
  `isaprove A n <=> ?p. (gform p = n) /\ A |-- p`;;

let PROV_LEMMA1 = prove
 (`!A p q. PROV1 (IMAGE gform A) x y
           ==> ALLN (isaprove A) x ==> ALLN (isaprove A) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PROV1] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; ALLN] THEN
  REWRITE_TAC[isaprove] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[AXIOM_THM_STRONG; proves_RULES];
    ASM_MESON_TAC[IN_IMAGE; GFORM_INJ; proves_RULES; gform];
    ALL_TAC;
    ASM_MESON_TAC[NUMBER_DENUMBER;
                  IN_IMAGE; GFORM_INJ; proves_RULES; gform]] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[gform; NPAIR_INJ; ARITH_EQ] THEN
  MAP_EVERY X_GEN_TAC [`P:form`; `Q:form`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o GSYM) MP_TAC) THEN
  ASM_REWRITE_TAC[GFORM_INJ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  ASM_MESON_TAC[proves_RULES]);;

let PROV_LEMMA2 = prove
 (`!A p. A |-- p ==> !a. RTC (PROV1 (IMAGE gform A)) a (NPAIR (gform p) a)`,
  GEN_TAC THEN MATCH_MP_TAC proves_INDUCT THEN REWRITE_TAC[gform] THEN
  MESON_TAC[RTC_INC; RTC_TRANS; PROV1; IN_IMAGE; AXIOM_THM]);;

let PROV_THM_STRONG = prove
 (`!A n. PROV (IMAGE gform A) n <=> ?p. A |-- p /\ (gform p = n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PROV] THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[PROV_LEMMA2]] THEN
  SUBGOAL_THEN
   `!x y. RTC (PROV1 (IMAGE gform A)) x y
           ==> ALLN (isaprove A) x ==> ALLN (isaprove A) y`
   (fun th -> MESON_TAC[ALLN; isaprove; GFORM_INJ; th]) THEN
  MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC[PROV_LEMMA1] THEN MESON_TAC[]);;

let PROV_THM = prove
 (`!A p. PROV (IMAGE gform A) (gform p) <=> A |-- p`,
  MESON_TAC[PROV_THM_STRONG; GFORM_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Now really objectify all that.                                            *)
(* ------------------------------------------------------------------------- *)

let arith_term1,ARITH_TERM1 = OBJECTIFY [] "arith_term1" TERM1;;

let FV_TERM1 = prove
 (`!s t. FV(arith_term1 s t) = (FVT s) UNION (FVT t)`,
  FV_TAC[arith_term1; FVT_PAIR; FVT_NUMERAL]);;

let arith_term,ARITH_TERM = OBJECTIFY_RTC ARITH_TERM1 "arith_term" TERM;;

let FV_TERM = prove
 (`!t. FV(arith_term t) = FVT t`,
  FV_TAC[arith_term; FV_RTC; FV_TERM1; FVT_PAIR; FVT_NUMERAL]);;

let arith_form1,ARITH_FORM1 =
 OBJECTIFY [ARITH_TERM] "arith_form1" FORM1;;

let FV_FORM1 = prove
 (`!s t. FV(arith_form1 s t) = (FVT s) UNION (FVT t)`,
  FV_TAC[arith_form1; FV_TERM; FVT_PAIR; FVT_NUMERAL]);;

let arith_form,ARITH_FORM = OBJECTIFY_RTC ARITH_FORM1 "arith_form" FORM;;

let FV_FORM = prove
 (`!t. FV(arith_form t) = FVT t`,
  FV_TAC[arith_form; FV_RTC; FV_FORM1; FVT_PAIR; FVT_NUMERAL]);;

let arith_freeterm1,ARITH_FREETERM1 =
 OBJECTIFY [] "arith_freeterm1" FREETERM1;;

let FV_FREETERM1 = prove
 (`!s t u. FV(arith_freeterm1 s t u) = (FVT s) UNION (FVT t) UNION (FVT u)`,
  FV_TAC[arith_freeterm1; FVT_PAIR; FVT_NUMERAL]);;

let arith_freeterm,ARITH_FREETERM =
  OBJECTIFY_RTCP ARITH_FREETERM1 "arith_freeterm" FREETERM;;

let FV_FREETERM = prove
 (`!s t. FV(arith_freeterm s t) = (FVT s) UNION (FVT t)`,
  FV_TAC[arith_freeterm; FV_RTCP; FV_FREETERM1; FVT_PAIR; FVT_NUMERAL]);;

let arith_freeform1,ARITH_FREEFORM1 =
 OBJECTIFY [ARITH_FREETERM; ARITH_FORM] "arith_freeform1" FREEFORM1;;

let FV_FREEFORM1 = prove
 (`!s t u. FV(arith_freeform1 s t u) = (FVT s) UNION (FVT t) UNION (FVT u)`,
  FV_TAC[arith_freeform1; FV_FREETERM; FV_FORM; FVT_PAIR; FVT_NUMERAL]);;

let arith_freeform,ARITH_FREEFORM =
 OBJECTIFY_RTCP ARITH_FREEFORM1 "arith_freeform" FREEFORM;;

let FV_FREEFORM = prove
 (`!s t. FV(arith_freeform s t) = (FVT s) UNION (FVT t)`,
  FV_TAC[arith_freeform; FV_RTCP; FV_FREEFORM1; FVT_PAIR; FVT_NUMERAL]);;

let arith_axiom,ARITH_AXIOM =
 OBJECTIFY [ARITH_FORM; ARITH_FREEFORM; ARITH_FREETERM; ARITH_TERM]
           "arith_axiom" AXIOM;;

let FV_AXIOM = prove
 (`!t. FV(arith_axiom t) = FVT t`,
  FV_TAC[arith_axiom; FV_FREETERM; FV_FREEFORM; FV_TERM; FV_FORM;
         FVT_PAIR; FVT_NUMERAL]);;

(* ------------------------------------------------------------------------- *)
(* Parametrization by A means it's easier to do these cases manually.        *)
(* ------------------------------------------------------------------------- *)

let arith_prov1,ARITH_PROV1 =
  let PROV1' = REWRITE_RULE[IN] PROV1 in
 OBJECTIFY [ASSUME `!v n. holds v (A n) <=> Ax (termval v n)`; ARITH_AXIOM]
   "arith_prov1" PROV1';;

let ARITH_PROV1 = prove
 (`(!v t. holds v (A t) <=> Ax(termval v t))
   ==> (!v s t.
             holds v (arith_prov1 A s t) <=>
             PROV1 Ax (termval v s) (termval v t))`,
  REWRITE_TAC[arith_prov1; holds; HOLDS_FORMSUBST] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[termval; valmod; o_THM; ARITH_EQ; ARITH_PAIR;
                  TERMVAL_NUMERAL; ARITH_AXIOM] THEN
  REWRITE_TAC[PROV1; IN]);;

let FV_PROV1 = prove
 (`(!t. FV(A t) = FVT t) ==> !s t. FV(arith_prov1 A s t) = FVT(s) UNION FVT(t)`,
  FV_TAC[arith_prov1; FV_AXIOM; FVT_NUMERAL; FVT_PAIR]);;

let arith_prov = new_definition
 `arith_prov A n =
    formsubst ((0 |-> n) V)
        (arith_rtc (arith_prov1 A) (numeral 0)
                   (arith_pair (V 0) (numeral 0)))`;;

let ARITH_PROV = prove
 (`!Ax A. (!v t. holds v (A t) <=> Ax(termval v t))
          ==> !v n. holds v (arith_prov A n) <=> PROV Ax (termval v n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ARITH_PROV1) THEN
  DISCH_THEN(MP_TAC o MATCH_MP ARITH_RTC) THEN
  CONV_TAC(TOP_DEPTH_CONV ETA_CONV) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[arith_prov; HOLDS_FORMSUBST] THEN
  REWRITE_TAC[termval; valmod; o_DEF; TERMVAL_NUMERAL; ARITH_PAIR] THEN
  REWRITE_TAC[PROV]);;

let FV_PROV = prove
 (`(!t. FV(A t) = FVT t) ==> !t. FV(arith_prov A t) = FVT t`,
  FV_TAC[arith_prov; FV_PROV1; FV_RTC; FVT_NUMERAL; FVT_PAIR]);;

(* ------------------------------------------------------------------------- *)
(* Our final conclusion.                                                     *)
(* ------------------------------------------------------------------------- *)

let PROV_DEFINABLE = prove
 (`!Ax. definable {gform p | p IN Ax} ==> definable {gform p | Ax |-- p}`,
  GEN_TAC THEN REWRITE_TAC[definable; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:form` (X_CHOOSE_TAC `x:num`)) THEN
  MP_TAC(SPECL [`IMAGE gform Ax`; `\t. formsubst ((x |-> t) V) A`]
               ARITH_PROV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[HOLDS_FORMSUBST] THEN
    REWRITE_TAC[o_THM; VALMOD_BASIC; IMAGE; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[PROV_THM_STRONG] THEN DISCH_TAC THEN
  EXISTS_TAC `arith_prov (\t. formsubst ((x |-> t) V) A) (V x)` THEN
  ASM_REWRITE_TAC[termval] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The crudest conclusion: truth undefinable, provability not, so:           *)
(* ------------------------------------------------------------------------- *)

let GODEL_CRUDE = prove
 (`!Ax. definable {gform p | p IN Ax} ==> ?p. ~(arithtrue p <=> Ax |-- p)`,
  REPEAT STRIP_TAC THEN MP_TAC TARSKI_THEOREM THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PROV_DEFINABLE) THEN
  MATCH_MP_TAC(TAUT `(~c ==> (a <=> b)) ==> a ==> ~b ==> c`) THEN
  SIMP_TAC[NOT_EXISTS_THM]);;
