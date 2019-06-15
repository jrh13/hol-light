(* ========================================================================= *)
(* Conversion to prenex form.                                                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Quantifier-free formulas.                                                 *)
(* ------------------------------------------------------------------------- *)

let qfree = new_recursive_definition form_RECURSION
  `(qfree False <=> T) /\
   (qfree (Atom n l) <=> T) /\
   (qfree (p --> q) <=> qfree p /\ qfree q) /\
   (qfree (!!x p) <=> F)`;;

let QFREE = prove
 (`(qfree False <=> T) /\
   (qfree True <=> T) /\
   (!a l. qfree (Atom a l) <=> T) /\
   (!p. qfree (Not p) <=> qfree p) /\
   (!p q. qfree (p || q) <=> qfree p /\ qfree q) /\
   (!p q. qfree (p && q) <=> qfree p /\ qfree q) /\
   (!p q. qfree (p --> q) <=> qfree p /\ qfree q) /\
   (!p q. qfree (p <-> q) <=> qfree p /\ qfree q) /\
   (!x p. qfree (!! x p) <=> F) /\
   (!x p. qfree (?? x p) <=> F)`,
  REWRITE_TAC[Not_DEF; True_DEF; Or_DEF; And_DEF;
              Iff_DEF; Exists_DEF; qfree; CONJ_ACI]);;

let QFREE_FORMSUBST = prove
 (`!p v. qfree (formsubst v p) <=> qfree p`,
  MATCH_MP_TAC form_INDUCTION THEN
  ASM_REWRITE_TAC[formsubst; qfree; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let QFREE_BV_EMPTY = prove
 (`!p. qfree(p) <=> (BV(p) = EMPTY)`,
  MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC[qfree; BV] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[EMPTY_UNION] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EXTENSION; IN_INSERT; NOT_IN_EMPTY]) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Prenex and prenex universal formulas.                                     *)
(* ------------------------------------------------------------------------- *)

let prenex_RULES,prenex_INDUCT,prenex_CASES = new_inductive_definition
  `(!p. qfree p ==> prenex p) /\
   (!x p. prenex p ==> prenex (!!x p)) /\
   (!x p. prenex p ==> prenex (??x p))`;;

let universal_RULES,universal_INDUCT,universal_CASES =
  new_inductive_definition
  `(!p. qfree p ==> universal p) /\
   (!x p. universal p ==> universal (!!x p))`;;

let prenex_INDUCT_NOT = prove
 (`!P. (!p. qfree p ==> P p) /\
       (!x p. P p ==> P (!! x p)) /\
       (!x p. P p ==> P (Not p))
       ==> !a. prenex a ==> P a`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC prenex_INDUCT THEN
  REWRITE_TAC[Exists_DEF] THEN ASM_MESON_TAC[]);;

let PRENEX = prove
 (`(prenex False <=> T) /\
   (prenex True <=> T) /\
   (!a l. prenex (Atom a l) <=> T) /\
   (!p. prenex (Not p) <=> qfree p \/ (?q x. (Not p = ??x q) /\ prenex q)) /\
   (!p q. prenex (p || q) <=> qfree p /\ qfree q) /\
   (!p q. prenex (p && q) <=> qfree p /\ qfree q) /\
   (!p q. prenex (p --> q) <=> qfree p /\ qfree q \/
                             (?r x. (p --> q = ??x r) /\ prenex r)) /\
   (!p q. prenex (p <-> q) <=> qfree p /\ qfree q) /\
   (!x p. prenex (!! x p) <=> prenex p) /\
   (!x p. prenex (?? x p) <=> prenex p)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [prenex_CASES] THEN
  REWRITE_TAC[True_DEF; Not_DEF; Or_DEF; And_DEF; Iff_DEF; Exists_DEF] THEN
  REWRITE_TAC[form_DISTINCT; form_INJ; QFREE; CONJ_ACI] THEN
  MESON_TAC[]);;

let FORMSUBST_STRUCTURE_LEMMA = prove
 (`!p i. ((formsubst i p = False) <=> (p = False)) /\
         ((?a l. formsubst i p = Atom a l) <=> (?a l. p = Atom a l)) /\
         ((?q r. formsubst i p = q --> r) <=> (?q r. p = q --> r)) /\
         ((?x q. formsubst i p = !!x q) <=> (?x q. p = !!x q))`,
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[formsubst; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[form_DISTINCT; form_INJ] THEN REPEAT STRIP_TAC THEN
  MESON_TAC[]);;

let FORMSUBST_STRUCTURE_NOT = prove
 (`!p i. (?q. formsubst i p = Not q) <=> (?q. p = Not q)`,
  REWRITE_TAC[Not_DEF; FORMSUBST_STRUCTURE_LEMMA] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `q:form`) THENL
   [MP_TAC(el 2 (CONJUNCTS (SPEC_ALL FORMSUBST_STRUCTURE_LEMMA))) THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`q:form`; `False`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[formsubst; FORMSUBST_STRUCTURE_LEMMA; form_INJ] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[formsubst] THEN MESON_TAC[]]);;

let FORMSUBST_STRUCTURE_EXISTS = prove
 (`!p i. (?x q. formsubst i p = ??x q) <=> (?x q. p = ??x q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[Exists_DEF] THEN EQ_TAC THEN STRIP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[Not_DEF; formsubst; LET_DEF; LET_END_DEF] THEN
             MESON_TAC[]] THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC_ALL FORMSUBST_STRUCTURE_NOT))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `!! x (Not q)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:form` SUBST_ALL_TAC) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[formsubst; Not_DEF; form_INJ; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[GSYM Not_DEF] THEN DISCH_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE(last(CONJUNCTS(SPEC_ALL(SPEC `r:form`
    FORMSUBST_STRUCTURE_LEMMA)))))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:num`; `Not q`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` (X_CHOOSE_THEN `s:form` SUBST_ALL_TAC)) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[formsubst; Not_DEF; form_INJ; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM Not_DEF] THEN MESON_TAC[FORMSUBST_STRUCTURE_NOT]);;

let PRENEX_FORMSUBST_LEMMA = prove
 (`!p. prenex p ==> !i q. (p = formsubst i q) ==> prenex q`,
  MATCH_MP_TAC prenex_INDUCT THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[QFREE_FORMSUBST; prenex_RULES];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`q:form`; `i:num->term`] FORMSUBST_STRUCTURE_LEMMA) THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE o last o CONJUNCTS) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:num`; `p:form`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN
     (X_CHOOSE_THEN `y:num` (X_CHOOSE_THEN `r:form` SUBST_ALL_TAC)) THEN
    UNDISCH_TAC `!! x p = formsubst i (!! y r)` THEN
    REWRITE_TAC[formsubst; form_INJ; PRENEX; LET_DEF; LET_END_DEF] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`q:form`; `i:num->term`] FORMSUBST_STRUCTURE_EXISTS) THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE o last o CONJUNCTS) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:num`; `p:form`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN
     (X_CHOOSE_THEN `y:num` (X_CHOOSE_THEN `r:form` SUBST_ALL_TAC)) THEN
    UNDISCH_TAC `?? x p = formsubst i (?? y r)` THEN
    REWRITE_TAC[PRENEX] THEN
    REWRITE_TAC[Exists_DEF; Not_DEF; formsubst; form_INJ; LET_DEF; LET_END_DEF] THEN
    ASM_MESON_TAC[]]);;

let PRENEX_FORMSUBST = prove
 (`!p i. prenex(formsubst i p) = prenex p`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[PRENEX_FORMSUBST_LEMMA];
    SPEC_TAC(`i:num->term`,`i:num->term`) THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    SPEC_TAC(`p:form`,`p:form`) THEN
    MATCH_MP_TAC prenex_INDUCT THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[formsubst; LET_DEF; LET_END_DEF] THENL
     [ASM_MESON_TAC[QFREE_FORMSUBST; prenex_RULES];
      ASM_REWRITE_TAC[PRENEX];
      REWRITE_TAC[formsubst; Not_DEF; Exists_DEF; LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[GSYM Not_DEF; GSYM Exists_DEF] THEN
      ASM_REWRITE_TAC[PRENEX]]]);;

(* ------------------------------------------------------------------------- *)
(* It's more convenient to argue by non-structural induction here.           *)
(* ------------------------------------------------------------------------- *)

let size = new_recursive_definition form_RECURSION
  `(size False = 1) /\
   (size (Atom p l) = 1) /\
   (size (q --> r) = size q + size r) /\
   (size (!!x q) = 1 + size q)`;;

let SIZE = prove
 (`(size False = 1) /\
   (size True = 2) /\
   (!a l. size (Atom a l) = 1) /\
   (!p. size (Not p) = 1 + size p) /\
   (!p q. size (p || q) = size p + 2 * size q) /\
   (!p q. size (p && q) = size p + 2 * size q + 4) /\
   (!p q. size (p --> q) = size p + size q) /\
   (!p q. size (p <-> q) = 3 * size p + 3 * size q + 4) /\
   (!x p.size (!! x p) = 1 + size p) /\
   (!x p. size (?? x p) = 3 + size p)`,
  REWRITE_TAC[True_DEF; Not_DEF; Or_DEF; And_DEF; Iff_DEF; Exists_DEF; size] THEN
  REPEAT STRIP_TAC THEN ARITH_TAC);;

let SIZE_FORMSUBST = prove
 (`!p i. size (formsubst i p) = size p`,
  MATCH_MP_TAC form_INDUCTION THEN
  ASM_REWRITE_TAC[formsubst; size; LET_END_DEF; LET_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constructive prenexing procedure.                                         *)
(* ------------------------------------------------------------------------- *)

let PPAT_DEF = new_definition
  `PPAT A B C r =
     if ?x p. r = !!x p then
                    A (@x. ?p. r = !!x p)
                      (@p. r = !!(@x. ?p. r = !!x p) p)
                  else if ?x p. r = ??x p then
                    B (@x. ?p. r = ??x p)
                      (@p. r = ??(@x. ?p. r = ??x p) p)
                  else C r`;;

let PRENEX_DISTINCT = prove
 (`!x y p q. ((!!x p = !!y q) <=> (x = y) /\ (p = q)) /\
             ((??x p = ??y q) <=> (x = y) /\ (p = q)) /\
             ~(!!x p = ??y q)`,
  REWRITE_TAC[Exists_DEF; Not_DEF; form_DISTINCT; form_INJ]);;

let PPAT = prove
 (`!A B C. (!x p. PPAT A B C (!!x p) = A x p :A) /\
           (!x p. PPAT A B C (??x p) = B x p) /\
           !r. ~(?x p. r = !!x p) /\ ~(?x p. r = ??x p)
               ==> (PPAT A B C  r = C r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PPAT_DEF] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[PRENEX_DISTINCT] THEN
  (COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]]) THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL; GSYM EXISTS_REFL;
              SELECT_REFL; CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
                                (SPEC_ALL SELECT_REFL)]);;

let SIZE_REC = prove
 (`!H. (!f g x. (!z. size z < size x ==> (f z = g z)) ==> (H f x = H g x))
       ==> (?f. !x. f x = H f x)`,
  MATCH_MP_TAC WF_REC THEN
  REWRITE_TAC[REWRITE_RULE[MEASURE] WF_MEASURE]);;

let PRENEX_RIGHT_EXISTENCE = prove
 (`?Prenex_right.
        (!p x q. Prenex_right p (!!x q) =
                   let y = VARIANT(FV(p) UNION FV(!!x q)) in
                   !!y (Prenex_right p (formsubst (valmod (x,V y) V) q))) /\
        (!p x q. Prenex_right p (??x q) =
                   let y = VARIANT(FV(p) UNION FV(??x q)) in
                   ??y (Prenex_right p (formsubst (valmod (x,V y) V) q))) /\
        (!p q. qfree q ==> (Prenex_right p q = p --> q))`,
  SUBGOAL_THEN
   `!p. ?Prenex_right. !r. Prenex_right r =
           PPAT (\x q. let y = VARIANT(FV(p) UNION FV(!!x q)) in
                 !!y (Prenex_right (formsubst (valmod (x,V y) V) q)))
                (\x q. let y = VARIANT(FV(p) UNION FV(??x q)) in
                 ??y (Prenex_right (formsubst (valmod (x,V y) V) q)))
                (\q. p --> q) r`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SIZE_REC THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[PPAT_DEF] THEN
    ASM_CASES_TAC `?x p. r = !!x p` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
      REWRITE_TAC[form_DISTINCT; form_INJ] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL; GSYM EXISTS_REFL;
              SELECT_REFL; CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
                                (SPEC_ALL SELECT_REFL)] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[SIZE_FORMSUBST; SIZE] THEN ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
    REWRITE_TAC[PRENEX_DISTINCT] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL; GSYM EXISTS_REFL;
              SELECT_REFL; CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
                                (SPEC_ALL SELECT_REFL)] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SIZE_FORMSUBST; SIZE] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `Prenex_right:form->form->form`) THEN
  EXISTS_TAC `Prenex_right:form->form->form` THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC[PPAT] THEN
  UNDISCH_TAC `qfree q` THEN REWRITE_TAC[PPAT_DEF] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  COND_CASES_TAC THENL [POP_ASSUM(STRIP_ASSUME_TAC) THEN
                        ASM_REWRITE_TAC[QFREE]; ALL_TAC] THEN
  COND_CASES_TAC THENL [POP_ASSUM(STRIP_ASSUME_TAC) THEN
                        ASM_REWRITE_TAC[QFREE]; ALL_TAC] THEN
  REWRITE_TAC[]);;

let PRENEX_RIGHT = new_specification ["Prenex_right"] PRENEX_RIGHT_EXISTENCE;;

let PRENEX_LEFT_EXISTENCE = prove
 (`?Prenex_left.
        (!p x q. Prenex_left (!!x q) p =
                   let y = VARIANT(FV(!!x q) UNION FV(p)) in
                   ??y (Prenex_left (formsubst (valmod (x,V y) V) q) p)) /\
        (!p x q. Prenex_left (??x q) p =
                   let y = VARIANT(FV(??x q) UNION FV(p)) in
                   !!y (Prenex_left (formsubst (valmod (x,V y) V) q) p)) /\
        (!p q. qfree q ==> (Prenex_left q p = Prenex_right q p))`,
  SUBGOAL_THEN
   `!p. ?Prenex_left. !r. Prenex_left r =
           PPAT (\x q. let y = VARIANT(FV(!!x q) UNION FV(p)) in
                 ??y (Prenex_left (formsubst (valmod (x,V y) V) q)))
                (\x q. let y = VARIANT(FV(??x q) UNION FV(p)) in
                 !!y (Prenex_left (formsubst (valmod (x,V y) V) q)))
                (\q. Prenex_right q p) r`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SIZE_REC THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[PPAT_DEF] THEN
    ASM_CASES_TAC `?x p. r = !!x p` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
      REWRITE_TAC[form_DISTINCT; form_INJ] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL; GSYM EXISTS_REFL;
              SELECT_REFL; CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
                                (SPEC_ALL SELECT_REFL)] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[SIZE_FORMSUBST; SIZE] THEN ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC)) THEN
    REWRITE_TAC[PRENEX_DISTINCT] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL; GSYM EXISTS_REFL;
              SELECT_REFL; CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
                                (SPEC_ALL SELECT_REFL)] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SIZE_FORMSUBST; SIZE] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `Prenex_left:form->form->form`) THEN
  EXISTS_TAC `\q p. (Prenex_left:form->form->form) p q` THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC[PPAT] THEN
  UNDISCH_TAC `qfree q` THEN REWRITE_TAC[PPAT_DEF] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  COND_CASES_TAC THENL [POP_ASSUM(STRIP_ASSUME_TAC) THEN
                        ASM_REWRITE_TAC[QFREE]; ALL_TAC] THEN
  COND_CASES_TAC THENL [POP_ASSUM(STRIP_ASSUME_TAC) THEN
                        ASM_REWRITE_TAC[QFREE]; ALL_TAC] THEN
  REWRITE_TAC[]);;

let PRENEX_LEFT = new_specification ["Prenex_left"] PRENEX_LEFT_EXISTENCE;;

let Prenex_DEF = new_recursive_definition form_RECURSION
  `(Prenex False = False) /\
   (Prenex (Atom a l) = Atom a l) /\
   (Prenex (p --> q) = Prenex_left (Prenex p) (Prenex q)) /\
   (Prenex (!!x p) = !!x (Prenex p))`;;

(* ------------------------------------------------------------------------- *)
(* Proof that it does indeed prenex.                                         *)
(* ------------------------------------------------------------------------- *)

let PRENEX_RIGHT_FORALL = prove
 (`~(Dom M :A->bool = EMPTY)
   ==> (holds M v (p --> !!x q) <=>
        holds M v (!! (VARIANT (FV(p) UNION FV(!!x q)))
                      (p --> formsubst (valmod
                               (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q)))`,
  DISCH_TAC THEN
  ABBREV_TAC `y = VARIANT (FV(p) UNION FV(!!x q))` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `holds M (v:num->A)
                    (p --> !!y (formsubst (valmod (x,V y) V) q))` THEN
  SUBGOAL_THEN `~(y IN FV(p)) /\ ~(y IN FV(!!x q))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM IN_UNION] THEN
    EXPAND_TAC "y" THEN REWRITE_TAC[VARIANT_THM; GSYM FV]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[holds] THEN
    MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
    DISCH_TAC THEN REWRITE_TAC[HOLDS; HOLDS_FORMSUBST] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
    DISCH_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
    X_GEN_TAC `z:num` THEN DISCH_TAC THEN
    REWRITE_TAC[valmod; o_THM] THEN
    COND_CASES_TAC THEN REWRITE_TAC[termval] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(y IN FV(!!x q))` THEN
    ASM_REWRITE_TAC[FV; IN_DELETE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[HOLDS] THEN
    SUBGOAL_THEN `!v a:A. holds M (valmod (y,a) v) p = holds M v p`
    (fun th -> REWRITE_TAC[th]) THENL
    [ALL_TAC; ASM_CASES_TAC `holds M (v:num->A) p` THEN ASM_REWRITE_TAC[]] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
    GEN_TAC THEN REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[]]);;

let PRENEX_RIGHT_EXISTS = prove
 (`~(Dom M :A->bool = EMPTY)
   ==> (holds M v (p --> ??x q) <=>
        holds M v (?? (VARIANT (FV(p) UNION FV(??x q)))
                      (p --> formsubst (valmod
                               (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q)))`,
  DISCH_TAC THEN
  ABBREV_TAC `y = VARIANT (FV(p) UNION FV(??x q))` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `holds M (v:num->A)
                    (p --> ??y (formsubst (valmod (x,V y) V) q))` THEN
  SUBGOAL_THEN `~(y IN FV(p)) /\ ~(y IN FV(??x q))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM IN_UNION] THEN
    EXPAND_TAC "y" THEN REWRITE_TAC[VARIANT_THM; GSYM FV]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[holds] THEN
    MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
    DISCH_TAC THEN REWRITE_TAC[HOLDS; HOLDS_FORMSUBST] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a /\ b) <=> (a /\ c))`) THEN
    DISCH_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
    X_GEN_TAC `z:num` THEN DISCH_TAC THEN
    REWRITE_TAC[valmod; o_THM] THEN
    COND_CASES_TAC THEN REWRITE_TAC[termval] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(y IN FV(??x q))` THEN
    ASM_REWRITE_TAC[FV; Not_DEF; Exists_DEF; UNION_EMPTY; IN_DELETE] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[HOLDS] THEN
    SUBGOAL_THEN `!v a:A. holds M (valmod (y,a) v) p = holds M v p`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
      GEN_TAC THEN REWRITE_TAC[valmod] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_CASES_TAC `holds M (v:num->A) p` THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]]]);;

let PRENEX_DUALITY_LEMMAS = prove
 (`(holds M v (??x p --> q) <=> holds M v (Not q --> !!x (Not p))) /\
   (holds M v (!!x p --> q) <=> holds M v (Not q --> ??x (Not p)))`,
  REWRITE_TAC[HOLDS] THEN MESON_TAC[]);;

let PRENEX_LEFT_FORALL = prove
 (`~(Dom M :A->bool = EMPTY)
   ==> (holds M v (!!x p --> q) <=>
        holds M v (?? (VARIANT (FV(!!x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(!!x p) UNION FV(q)))) V) p --> q)))`,
  DISCH_TAC THEN REWRITE_TAC[PRENEX_DUALITY_LEMMAS] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PRENEX_RIGHT_EXISTS th]) THEN
  REWRITE_TAC[Exists_DEF; Not_DEF; FV; UNION_EMPTY; UNION_COMM] THEN
  REWRITE_TAC[holds; formsubst; TAUT `(~a ==> ~b) <=> (b ==> a)`]);;

let PRENEX_LEFT_EXISTS = prove
 (`~(Dom M :A->bool = EMPTY)
   ==> (holds M v (??x p --> q) <=>
        holds M v (!! (VARIANT (FV(??x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(??x p) UNION FV(q)))) V) p --> q)))`,
  DISCH_TAC THEN REWRITE_TAC[PRENEX_DUALITY_LEMMAS] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PRENEX_RIGHT_FORALL th]) THEN
  REWRITE_TAC[Exists_DEF; Not_DEF; FV; UNION_EMPTY; UNION_COMM] THEN
  REWRITE_TAC[holds; formsubst; TAUT `(~a ==> ~b) <=> (b ==> a)`]);;

(* ------------------------------------------------------------------------- *)
(* Extras about free variables.                                              *)
(* ------------------------------------------------------------------------- *)

let PRENEX_RIGHT_FORALL_FV = prove
 (`FV(p --> !!x q) = FV(!! (VARIANT (FV(p) UNION FV(!!x q)))
                           (p --> formsubst (valmod
                              (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q))`,
  let lemma = prove
   (`(s UNION t) DELETE x = (s DELETE x) UNION (t DELETE x)`,SET_TAC[]) in
  REWRITE_TAC[FV; FORMSUBST_RENAME; lemma] THEN
  MP_TAC(SPEC `p --> !!x q` VARIANT_THM) THEN
  REWRITE_TAC[EXTENSION; FV; IN_UNION; IN_DELETE] THEN MESON_TAC[]);;

let PRENEX_RIGHT_EXISTS_FV = prove
 (`FV(p --> ??x q) =
   FV(?? (VARIANT (FV(p) UNION FV(??x q)))
           (p --> formsubst (valmod
                   (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q))`,
  let lemma = prove
   (`(s UNION t) DELETE x = (s DELETE x) UNION (t DELETE x)`,SET_TAC[]) in
  REWRITE_TAC[FV; FV_EXISTS; FORMSUBST_RENAME; lemma] THEN
  MP_TAC(SPEC `p --> ??x q` VARIANT_THM) THEN
  REWRITE_TAC[EXTENSION; FV; FV_EXISTS; IN_UNION; IN_DELETE] THEN
  MESON_TAC[]);;

let PRENEX_LEFT_FORALL_FV = prove
 (`FV(!!x p --> q) =
   FV(?? (VARIANT (FV(!!x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(!!x p) UNION FV(q)))) V) p --> q))`,
  let lemma = prove
   (`(s UNION t) DELETE x = (s DELETE x) UNION (t DELETE x)`,SET_TAC[]) in
  REWRITE_TAC[FV; FV_EXISTS; FORMSUBST_RENAME; lemma] THEN
  MP_TAC(SPEC `!!x p --> q` VARIANT_THM) THEN
  REWRITE_TAC[EXTENSION; FV; FV_EXISTS; IN_UNION; IN_DELETE] THEN
  MESON_TAC[]);;

let PRENEX_LEFT_EXISTS_FV = prove
 (`FV(??x p --> q) =
   FV(!! (VARIANT (FV(??x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(??x p) UNION FV(q)))) V) p --> q))`,
  let lemma = prove
   (`(s UNION t) DELETE x = (s DELETE x) UNION (t DELETE x)`,SET_TAC[]) in
  REWRITE_TAC[FV; FV_EXISTS; FORMSUBST_RENAME; lemma] THEN
  MP_TAC(SPEC `??x p --> q` VARIANT_THM) THEN
  REWRITE_TAC[EXTENSION; FV; FV_EXISTS; IN_UNION; IN_DELETE] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* And extras about the language.                                            *)
(* ------------------------------------------------------------------------- *)

let PRENEX_RIGHT_FORALL_LANGUAGE = prove
 (`language {(p --> !!x q)} = language {(!! (VARIANT (FV(p) UNION FV(!!x q)))
                           (p --> formsubst (valmod
                              (x,V(VARIANT (FV(p) UNION FV(!!x q)))) V) q))}`,
  REWRITE_TAC[LANGUAGE_1; functions_form; predicates_form] THEN
  REWRITE_TAC[REWRITE_RULE[PAIR_EQ; LANGUAGE_1] FORMSUBST_LANGUAGE_RENAME]);;

let PRENEX_RIGHT_EXISTS_LANGUAGE = prove
 (`language {(p --> ??x q)} =
   language {(?? (VARIANT (FV(p) UNION FV(??x q)))
           (p --> formsubst (valmod
                   (x,V(VARIANT (FV(p) UNION FV(??x q)))) V) q))}`,
  REWRITE_TAC[LANGUAGE_1; functions_form; predicates_form;
              Exists_DEF; Not_DEF; UNION_EMPTY] THEN
  REWRITE_TAC[REWRITE_RULE[PAIR_EQ; LANGUAGE_1] FORMSUBST_LANGUAGE_RENAME]);;

let PRENEX_LEFT_FORALL_LANGUAGE = prove
 (`language {(!!x p --> q)} =
   language {(?? (VARIANT (FV(!!x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(!!x p) UNION FV(q)))) V) p --> q))}`,
  REWRITE_TAC[LANGUAGE_1; functions_form; predicates_form;
              Exists_DEF; Not_DEF; UNION_EMPTY] THEN
  REWRITE_TAC[REWRITE_RULE[PAIR_EQ; LANGUAGE_1] FORMSUBST_LANGUAGE_RENAME]);;

let PRENEX_LEFT_EXISTS_LANGUAGE = prove
 (`language {(??x p --> q)} =
   language {(!! (VARIANT (FV(??x p) UNION FV(q)))
                      (formsubst (valmod
                        (x,V(VARIANT (FV(??x p) UNION FV(q)))) V) p --> q))}`,
  REWRITE_TAC[LANGUAGE_1; functions_form; predicates_form;
              Exists_DEF; Not_DEF; UNION_EMPTY] THEN
  REWRITE_TAC[REWRITE_RULE[PAIR_EQ; LANGUAGE_1] FORMSUBST_LANGUAGE_RENAME]);;

(* ------------------------------------------------------------------------- *)
(* Proofs that things work properly.                                         *)
(* ------------------------------------------------------------------------- *)

let PRENEX_LEMMA_FORALL = prove
 (`P /\
   (FV r1 = FV r2) /\
   (language {r1} = language {r2}) /\
   (!M v. ~(Dom M :A->bool = EMPTY) ==> (holds M v p <=> holds M v q))
   ==> P /\
       (FV(!!z r1) = FV(!!z r2)) /\
       (language {(!!z r1)} = language {(!!z r2)}) /\
       !M v. ~(Dom M :A->bool = EMPTY)
               ==> (holds M v (!!x p) <=> holds M v (!!x q))`,
  REWRITE_TAC[LANGUAGE_1; PAIR_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FV; functions_form; predicates_form] THEN
  ASM_SIMP_TAC[HOLDS]);;

let PRENEX_LEMMA_EXISTS = prove
 (`P /\
   (FV r1 = FV r2) /\
   (language {r1} = language {r2}) /\
   (!M v. ~(Dom M :A->bool = EMPTY) ==> (holds M v p <=> holds M v q))
   ==> P /\
       (FV(??z r1) = FV(??z r2)) /\
       (language {(??z r1)} = language {(??z r2)}) /\
       !M v. ~(Dom M :A->bool = EMPTY)
               ==> (holds M v (??x p) <=> holds M v (??x q))`,
  REWRITE_TAC[LANGUAGE_1; PAIR_EQ] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[FV; FV_EXISTS] THEN
  ASM_SIMP_TAC[HOLDS] THEN
  ASM_REWRITE_TAC[Exists_DEF; Not_DEF; functions_form; predicates_form]);;

let PRENEX_RIGHT_THM = prove
 (`!p q. qfree p /\ prenex q
         ==> prenex (Prenex_right p q) /\
             (FV(Prenex_right p q) = FV(p --> q)) /\
             (language {(Prenex_right p q)} = language {(p --> q)}) /\
             (!M v. ~(Dom M :A->bool = EMPTY)
                    ==> (holds M v (Prenex_right p q) <=>
                         holds M v (p --> q)))`,
  SUBGOAL_THEN
   `!p. qfree p
        ==> !n q. prenex(q) /\ (size(q) = n)
                  ==> prenex (Prenex_right p q) /\
                      (FV(Prenex_right p q) = FV(p --> q)) /\
                      (language {(Prenex_right p q)} = language {(p --> q)}) /\
                      (!M v. ~(Dom M :A->bool = EMPTY)
                              ==> (holds M v (Prenex_right p q) <=>
                                   holds M v (p --> q)))`
  (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [prenex_CASES]) THENL
   [ASM_SIMP_TAC [PRENEX_RIGHT; PRENEX]; ALL_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[PRENEX_RIGHT] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; PRENEX] THEN
  SIMP_TAC [PRENEX_RIGHT_FORALL; PRENEX_RIGHT_EXISTS] THEN
  REWRITE_TAC[PRENEX_RIGHT_FORALL_FV; PRENEX_RIGHT_FORALL_LANGUAGE] THEN
  REWRITE_TAC[PRENEX_RIGHT_EXISTS_FV; PRENEX_RIGHT_EXISTS_LANGUAGE] THENL
   [MATCH_MP_TAC PRENEX_LEMMA_FORALL; MATCH_MP_TAC PRENEX_LEMMA_EXISTS] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM;
                              IMP_IMP]) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `size p'` THEN
  REWRITE_TAC[PRENEX_FORMSUBST; SIZE_FORMSUBST] THEN
  UNDISCH_TAC `size q = n` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[SIZE] THEN ARITH_TAC);;

let PRENEX_LEFT_THM = prove
 (`!p q. prenex p /\ prenex q
         ==> prenex (Prenex_left p q) /\
             (FV(Prenex_left p q) = FV(p --> q)) /\
             (language {(Prenex_left p q)} = language {(p --> q)}) /\
             (!M v. ~(Dom M :A->bool = EMPTY)
                    ==> (holds M v (Prenex_left p q) <=> holds M v (p --> q)))`,
  SUBGOAL_THEN
   `!q. prenex(q)
        ==> !n p. prenex(p) /\ (size(p) = n)
                  ==> prenex (Prenex_left p q) /\
                      (FV(Prenex_left p q) = FV(p --> q)) /\
                      (language {(Prenex_left p q)} = language {(p --> q)}) /\
                      (!M v. ~(Dom M :A->bool = EMPTY)
                              ==> (holds M v (Prenex_left p q) <=>
                                   holds M v (p --> q)))`
  (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [prenex_CASES]) THENL
   [ASM_SIMP_TAC [PRENEX_LEFT; PRENEX] THEN
    MATCH_MP_TAC PRENEX_RIGHT_THM THEN ASM_REWRITE_TAC[];
    ALL_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[PRENEX_LEFT] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; PRENEX] THEN
  SIMP_TAC [PRENEX_LEFT_FORALL; PRENEX_LEFT_EXISTS] THEN
  REWRITE_TAC[PRENEX_LEFT_FORALL_FV; PRENEX_LEFT_FORALL_LANGUAGE] THEN
  REWRITE_TAC[PRENEX_LEFT_EXISTS_FV; PRENEX_LEFT_EXISTS_LANGUAGE] THENL
   [MATCH_MP_TAC PRENEX_LEMMA_EXISTS; MATCH_MP_TAC PRENEX_LEMMA_FORALL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM;
                              IMP_IMP]) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `size p'` THEN
  REWRITE_TAC[PRENEX_FORMSUBST; SIZE_FORMSUBST] THEN
  UNDISCH_TAC `size p = n` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[SIZE] THEN ARITH_TAC);;

let PRENEX_THM = prove
 (`!p. prenex(Prenex p) /\
       (FV(Prenex p) = FV(p)) /\
       (language {(Prenex p)} = language {p}) /\
       !M v. ~(Dom M = EMPTY)
             ==> (holds M (v:num->A) (Prenex p) <=> holds M v p)`,
  MATCH_MP_TAC form_INDUCTION THEN
  REWRITE_TAC[PRENEX; Prenex_DEF] THEN REWRITE_TAC[HOLDS] THEN
  MP_TAC PRENEX_LEFT_THM THEN
  REWRITE_TAC[HOLDS; FV; LANGUAGE_1; PAIR_EQ] THEN
  REWRITE_TAC[functions_form; predicates_form] THEN
  MESON_TAC[]);;
