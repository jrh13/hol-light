(* ========================================================================= *)
(* First order logic with equality.                                          *)
(* ========================================================================= *)

parse_as_infix("===",(18,"right"));;

(* ------------------------------------------------------------------------- *)
(* Convenient shorthand for equality predicate.                              *)
(* ------------------------------------------------------------------------- *)

let Equal_DEF = new_definition
  `s === t = Atom 0 [s; t]`;;

(* ------------------------------------------------------------------------- *)
(* Universal closure.                                                        *)
(* ------------------------------------------------------------------------- *)

let uclose = new_definition
  `uclose p = ITLIST (!!) (list_of_set(FV p)) p`;;

(* ------------------------------------------------------------------------- *)
(* Definition of normal model.                                               *)
(* ------------------------------------------------------------------------- *)

let normal = new_definition
  `normal fns M <=>
        !s t v. valuation(M) v /\
                s IN terms fns /\
                t IN terms fns
                ==> (holds M v (s === t) <=> (termval M v s = termval M v t))`;;

(* ------------------------------------------------------------------------- *)
(* Equality "axioms" for functions and predicates.                           *)
(* ------------------------------------------------------------------------- *)

let Varpairs_DEF = new_recursive_definition num_RECURSION
  `(Varpairs 0 = []) /\
   (Varpairs (SUC n) = CONS (V(2 * n),V(2 * n + 1)) (Varpairs n))`;;

let Eqaxiom_Func = new_definition
  `Eqaxiom_Func (f,n) =
     uclose (ITLIST (&&) (MAP (\(s,t). s === t) (Varpairs n)) True
             --> Fn f (MAP FST (Varpairs n)) === Fn f (MAP SND (Varpairs n)))`;;

let Eqaxiom_Pred = new_definition
  `Eqaxiom_Pred (p,n) =
     uclose (ITLIST (&&) (MAP (\(s,t). s === t) (Varpairs n)) True
             --> (Atom p (MAP FST (Varpairs n))
                  <-> Atom p (MAP SND (Varpairs n))))`;;

let Eqaxioms_DEF = new_definition
  `Eqaxioms L = { (!! 0 (V 0 === V 0)) } UNION
                { (!!0 (!!1 (!!2
                        (V 0 === V 1 --> (V 2 === V 1 --> V 0 === V 2))))) } UNION
                { Eqaxiom_Func fa | fa IN (FST L) } UNION
                { Eqaxiom_Pred pa | pa IN (SND L) }`;;

let DOWNFROM = new_recursive_definition num_RECURSION
  `(DOWNFROM 0 = []) /\
   (DOWNFROM (SUC n) = CONS n (DOWNFROM n))`;;

(* ------------------------------------------------------------------------- *)
(* Various stupid lemmas.                                                    *)
(* ------------------------------------------------------------------------- *)

let SATISFIES_UNION = prove
 (`!M s t. M satisfies (s UNION t) <=> M satisfies s /\ M satisfies t`,
  REWRITE_TAC[satisfies; IN_UNION] THEN MESON_TAC[]);;

let HOLDS_UCLOSE_ALL = prove
 (`!M x p. (!v:num->A. valuation(M) v ==> holds M v p)
           ==> !v. valuation(M) v ==> holds M v (uclose p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[uclose] THEN
  SPEC_TAC(`list_of_set(FV p)`,`l:num list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[uclose; ITLIST] THEN
  REWRITE_TAC[holds] THEN ASM_SIMP_TAC[VALUATION_VALMOD]);;

let HOLDS_UCLOSE_ALL_EQ = prove
 (`!M. ~(Dom M :A->bool = {})
       ==> !p. (!v. valuation(M) v ==> holds M v (uclose p)) <=>
               (!v. valuation(M) v ==> holds M v p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[uclose] THEN
  SPEC_TAC(`list_of_set(FV p)`,`l:num list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[uclose; ITLIST] THEN
  ASM_REWRITE_TAC[HOLDS_UCLOSE]);;

let UCLOSE_FV_LEMMA = prove
 (`!l p. FV(ITLIST !! l p) = FV(p) DIFF (set_of_list l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; FV; set_of_list] THEN SET_TAC[]);;

let UCLOSE_CLOSED = prove
 (`!p. FV(uclose p) = EMPTY`,
  GEN_TAC THEN REWRITE_TAC[uclose; UCLOSE_FV_LEMMA] THEN
  SIMP_TAC[SET_OF_LIST_OF_SET; FV_FINITE] THEN SET_TAC[]);;

let HOLDS_UCLOSE_ANY = prove
 (`!M (v:num->A) p.
       holds M v (uclose p)
       ==> ~(Dom M = EMPTY)
           ==> !w. valuation(M) w ==> holds M w p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!w:num->A. valuation(M) w ==> holds M w (uclose p)`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `holds M (v:num->A) (uclose p)` THEN
    MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC HOLDS_VALUATION THEN
    REWRITE_TAC[UCLOSE_CLOSED; NOT_IN_EMPTY];
    REWRITE_TAC[uclose] THEN
    SPEC_TAC(`list_of_set(FV p)`,`l:num list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST] THEN
    ASM_REWRITE_TAC[HOLDS_UCLOSE]]);;

let SATISFIES_NOT = prove
 (`~(Dom M :A->bool = {})
   ==> (M satisfies E /\ ~(M satisfies {p}) <=>
        M satisfies (Not (uclose p) INSERT E))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[satisfies; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[TAUT
   `(a /\ (b \/ c) ==> d) <=> (a /\ c ==> d) /\ (a /\ b ==> d)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[EXISTS_REFL] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
        [GSYM(MATCH_MP HOLDS_UCLOSE_ALL_EQ th)]) THEN
  REWRITE_TAC[HOLDS] THEN
  ASM_MESON_TAC[VALUATION_EXISTS; HOLDS_VALUATION;
                UCLOSE_CLOSED; NOT_IN_EMPTY]);;

let FUNCTIONS_FORM_UCLOSE = prove
 (`functions_form(uclose p) = functions_form p`,
  REWRITE_TAC[uclose] THEN
  SPEC_TAC(`list_of_set (FV p)`,`l:num list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; functions_form]);;

let PREDICATES_FORM_UCLOSE = prove
 (`predicates_form(uclose p) = predicates_form p`,
  REWRITE_TAC[uclose] THEN
  SPEC_TAC(`list_of_set (FV p)`,`l:num list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; predicates_form]);;

let HOLDS_ANDS = prove
 (`!l. holds M v (ITLIST (&&) l True) <=> ALL (holds M v) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; ALL; HOLDS]);;

let LENGTH_VARPAIRS = prove
 (`!n. LENGTH (Varpairs n) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[Varpairs_DEF; LENGTH]);;

let MAP_FST_VARPAIRS = prove
 (`!n. MAP FST (Varpairs n) = MAP (\n. V(2 * n)) (DOWNFROM n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[Varpairs_DEF; DOWNFROM; MAP]);;

let MAP_SND_VARPAIRS = prove
 (`!n. MAP SND (Varpairs n) = MAP (\n. V(2 * n + 1)) (DOWNFROM n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[Varpairs_DEF; DOWNFROM; MAP]);;

let MULT_DIV_LEMMA = prove
 (`(!n. (2 * n) DIV 2 = n) /\
   (!n. (2 * n + 1) DIV 2 = n)`,
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `1` THEN REWRITE_TAC[MULT_AC; ARITH]);;

let PAIR_LEMMA = prove
 (`!z. (\(x,y). P x y) z = P (FST z) (SND z)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let FORALL_VARPAIRS = prove
 (`!n. ALL P (Varpairs n) <=>
        ALL (\n. P (V (2 * n),V (2 * n + 1))) (DOWNFROM n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; Varpairs_DEF; DOWNFROM]);;

let FORALL2_VARPAIRS = prove
 (`!n. ALL (\p. Pred M a [termval M v (FST p); termval M v (SND p)])
              (Varpairs n) <=>
       ALL2 (\x y. Pred M a [x;y])
               (MAP (termval M v) (MAP FST (Varpairs n)))
               (MAP (termval M v) (MAP SND (Varpairs n)))`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[Varpairs_DEF; ALL; ALL2; MAP]);;

let FORALL2_FORALL = prove
 (`!l. ALL2 (\x y. P x y) (MAP f l) (MAP g l) <=>
       ALL (\x. P (f x) (g x)) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; MAP; ALL2]);;

let FORALL_DOWNFROM = prove
 (`!n. ALL P (DOWNFROM n) <=> !k. k < n ==> P k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[DOWNFROM; ALL; LT] THEN MESON_TAC[]);;

let MAP_INDEXED = prove
 (`!l:A list. MAP (\n. EL ((LENGTH l - 1) - n) l) (DOWNFROM (LENGTH l)) = l`,
  let lemma = prove
   (`!k n. k < n ==> (SUC n - 1 - k = SUC (n - 1 - k))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`] THEN
    REWRITE_TAC[LT_EXISTS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `(m + SUC n) - 1 = m + n`; ADD_SUB2]) in
  ONCE_REWRITE_TAC[lemma] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LENGTH; DOWNFROM; EL] THEN
  REWRITE_TAC[ARITH_RULE `(SUC n - 1) - n = 0`; EL; HD] THEN
  AP_TERM_TAC THEN
  POP_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[FORALL_DOWNFROM] THEN
  GEN_TAC THEN SPEC_TAC(`LENGTH (t:A list)`,`n:num`) THEN
  MESON_TAC[EL; TL; lemma]);;

let RECONSTRUCT_TERMVAL = prove
 (`!M a f1 f2.
        (MAP (termval M (\n. if 2 * LENGTH l <= n then a
                             else if EVEN(n)
                             then f1 (EL ((LENGTH l - 1) - (n DIV 2)) l)
                             else f2 (EL ((LENGTH l - 1) - (n DIV 2)) l)))
             (MAP FST (Varpairs (LENGTH l))) = MAP f1 l) /\
        (MAP (termval M (\n. if 2 * LENGTH l <= n then a
                             else if EVEN(n)
                             then f1 (EL ((LENGTH l - 1) - (n DIV 2)) l)
                             else f2 (EL ((LENGTH l - 1) - (n DIV 2)) l)))
             (MAP SND (Varpairs (LENGTH l))) = MAP f2 l)`,
  let lemma = prove
   (`!L K. L <= K
           ==> (MAP (\n. if K <= n then a else f n) (DOWNFROM L) =
                MAP f (DOWNFROM L))`,
    INDUCT_TAC THEN REWRITE_TAC[MAP; DOWNFROM] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `SUC L <= K ==> L <= K /\ ~(K <= L)`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ANTE_RES_THEN SUBST1_TAC) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP_FST_VARPAIRS; MAP_SND_VARPAIRS] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF; termval] THEN
  REWRITE_TAC[LE_MULT_LCANCEL; ARITH] THEN
  REWRITE_TAC[EVEN_MULT; EVEN_ADD; MULT_DIV_LEMMA; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `2 * x <= 2 * y + 1 <=> x <= y`] THEN
  SIMP_TAC[lemma; LE_REFL] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  REWRITE_TAC[MAP_o; MAP_INDEXED]);;

let FORALL_TERMS_STRONG = prove
 (`!s t. terms (functions s) t <=> functions_term t SUBSET (functions s)`,
  let lemma0 = prove
   (`(a INSERT b) SUBSET s <=> a IN s /\ b SUBSET s`,
    SET_TAC[]) in
  let lemma1 = prove
   (`s UNION t SUBSET u <=> s SUBSET u /\ t SUBSET u`,
    SET_TAC[]) in
  let lemma2 = prove
   (`!l. LIST_UNION l SUBSET s <=> ALL (\x. x SUBSET s) l`,
    LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LIST_UNION; EMPTY_SUBSET] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lemma1]) in
  GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
  REWRITE_TAC[EMPTY_SUBSET; functions_term] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[terms_CASES] THEN
    REWRITE_TAC[term_INJ; term_DISTINCT] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[terms_CASES] THEN
  REWRITE_TAC[term_INJ; term_DISTINCT] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM1; lemma0] THEN AP_TERM_TAC THEN
  REWRITE_TAC[lemma2] THEN REWRITE_TAC[ALL_MAP; o_DEF] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`l:term list`,`l:term list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  ASM_MESON_TAC[]);;

let FORALL_TERMS_RAW = prove
 (`!s t. terms (functions s) t ==> functions_term t SUBSET (functions s)`,
  REWRITE_TAC[FORALL_TERMS_STRONG]);;

let FORALL_TERMS_INDEXED = prove
 (`!l n. ALL (terms (functions s)) l /\ n < LENGTH l
         ==> functions_term (EL n l) SUBSET functions s`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_SUC; LT_0; EL; HD] THENL
   [MESON_TAC[FORALL_TERMS_RAW];
    REWRITE_TAC[TL] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The key theorem.                                                          *)
(* ------------------------------------------------------------------------- *)

let NORMAL_THM = prove
 (`(?M:(A->bool)#(num->A list->A)#(num->A list->bool).
        interpretation (language s) M /\
        ~(Dom M = EMPTY) /\
        normal (functions s) M /\
        M satisfies s) <=>
   (?M:(A->bool)#(num->A list->A)#(num->A list->bool).
        interpretation (language s) M /\
        ~(Dom M = EMPTY) /\
        M satisfies (s UNION Eqaxioms (language s)))`,
  let lemma0 = prove
   (`a SUBSET s /\ b SUBSET s ==> (a UNION b) SUBSET s`,SET_TAC[]) in
  let lemma1 = prove
   (`a IN s /\ b SUBSET s ==> (a INSERT b) SUBSET s`,SET_TAC[]) in
  let lemma2 = prove
   (`!l. ALL (\x. x SUBSET s) l ==> LIST_UNION l SUBSET s`,
    LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LIST_UNION; EMPTY_SUBSET] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma0 THEN ASM_MESON_TAC[]) in
  let lemma3 = prove
   (`{x} SUBSET s <=> x IN s`,
    SET_TAC[]) in
  let lemma4a = prove
   (`s UNION t SUBSET u <=> s SUBSET u /\ t SUBSET u`,
    SET_TAC[]) in
  let lemma4 = prove
   (`!l. LIST_UNION l SUBSET s <=> ALL (\x. x SUBSET s) l`,
    LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LIST_UNION; EMPTY_SUBSET] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lemma4a]) in
  let slemma1 = prove
   (`(s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u`,
    SET_TAC[]) in
  let clemma1 = prove
   (`canonize o valmod (x,a) v = valmod (x,canonize a) (canonize o v)`,
    REWRITE_TAC[FUN_EQ_THM; o_THM; valmod] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]) in
  REWRITE_TAC[Eqaxioms_DEF; SATISFIES_UNION] THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `M:(A->bool)#(num->A list->A)#(num->A list->bool)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[satisfies] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[normal]) THEN
      ASM_SIMP_TAC[holds; IN; terms_RULES; VALUATION_VALMOD];
      RULE_ASSUM_TAC(REWRITE_RULE[normal]) THEN
      REWRITE_TAC[holds; IN] THEN
      ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
          [IN; terms_RULES; VALUATION_VALMOD];
      UNDISCH_TAC `valuation M (v:num->A)` THEN
      SPEC_TAC(`v:num->A`,`v:num->A`) THEN
      SUBST_ALL_TAC(SYM(ISPEC `fa:num#num` PAIR)) THEN
      PURE_REWRITE_TAC[Eqaxiom_Func] THEN
      MATCH_MP_TAC HOLDS_UCLOSE_ALL THEN
      REWRITE_TAC[holds] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[language; normal]) THEN
      GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC[HOLDS_ANDS] THEN
      REWRITE_TAC[ALL_MAP] THEN
      FIRST_ASSUM(MP_TAC o SPECL
       [`Fn (FST fa) (MAP FST (Varpairs (SND fa)))`;
        `Fn (FST fa) (MAP SND (Varpairs (SND fa)))`;
        `v:num->A`]) THEN
      W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
       [ASM_REWRITE_TAC[IN] THEN CONJ_TAC THEN
        MATCH_MP_TAC(CONJUNCT2(SPEC_ALL terms_RULES)) THEN
        ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_VARPAIRS] THEN
        SPEC_TAC(`SND(fa:num#num)`,`n:num`) THEN
        INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; Varpairs_DEF; MAP] THEN
        MESON_TAC[terms_RULES];
        DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      REWRITE_TAC[termval] THEN REWRITE_TAC[GSYM MAP_o] THEN
      DISCH_THEN(fun th -> AP_TERM_TAC THEN MP_TAC th) THEN
      SPEC_TAC(`SND(fa:num#num)`,`n:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[Varpairs_DEF; ALL; MAP] THEN
      REWRITE_TAC[o_THM] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      ASM_SIMP_TAC[terms_RULES; IN];
      UNDISCH_TAC `valuation M (v:num->A)` THEN
      SPEC_TAC(`v:num->A`,`v:num->A`) THEN
      SUBST_ALL_TAC(SYM(ISPEC `pa:num#num` PAIR)) THEN
      PURE_REWRITE_TAC[Eqaxiom_Pred] THEN
      MATCH_MP_TAC HOLDS_UCLOSE_ALL THEN
      REWRITE_TAC[HOLDS] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[language; normal]) THEN
      GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC[HOLDS_ANDS] THEN
      REWRITE_TAC[ALL_MAP] THEN
      REWRITE_TAC[termval] THEN REWRITE_TAC[GSYM MAP_o] THEN
      DISCH_THEN(fun th -> AP_TERM_TAC THEN MP_TAC th) THEN
      SPEC_TAC(`SND(pa:num#num)`,`n:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[Varpairs_DEF; ALL; MAP] THEN
      REWRITE_TAC[o_THM] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      ASM_SIMP_TAC[terms_RULES; IN]]; ALL_TAC] THEN
  ABBREV_TAC `equiv = \a:A b. a IN Dom(M) /\ b IN Dom(M) /\
                              Pred(M) 0 [a; b]` THEN
  ABBREV_TAC `canonize = \a:A. @b:A. equiv a b` THEN
  ABBREV_TAC `M' = { a:A | a IN Dom(M) /\ (a = canonize a) },
                   (\f l. canonize(Fun(M) f l)),Pred(M)` THEN
  EXISTS_TAC `M':(A->bool)#(num->A list->A)#(num->A list->bool)` THEN
  REWRITE_TAC[normal] THEN
  SUBGOAL_THEN `!a:A. equiv a a <=> a IN Dom(M)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "equiv" THEN
    UNDISCH_TAC `(M:(A->bool)#(num->A list->A)#(num->A list->bool))
                 satisfies { (!!0 (V 0 === V 0)) }` THEN
    REWRITE_TAC[satisfies; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `\x:num. a:A`) THEN
    ASM_REWRITE_TAC[valuation] THEN SIMP_TAC[holds] THEN
    REWRITE_TAC[Equal_DEF; holds] THEN
    DISCH_THEN(MP_TAC o SPEC `!!0 (Atom 0 [V 0; V 0])`) THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `a:A IN Dom(M)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `a:A`) THEN
    ASM_REWRITE_TAC[MAP; termval; valmod]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:A. equiv a (canonize a :A) <=> a IN Dom(M)` ASSUME_TAC THENL
   [EXPAND_TAC "canonize" THEN
    GEN_TAC THEN CONV_TAC(LAND_CONV SELECT_CONV) THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:A b c. equiv a b ==> equiv c b ==> equiv a c`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "equiv" THEN
    STRIP_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `(M:(A->bool)#(num->A list->A)#(num->A list->bool))
                 satisfies
                 { (!!0 (!!1 (!!2
                      (V 0 === V 1 --> (V 2 === V 1 --> V 0 === V 2))))) }` THEN
    REWRITE_TAC[satisfies; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `valmod (0,a) (valmod (1,b) (\n. c:A))`) THEN
    ASM_SIMP_TAC[VALUATION_VALMOD; valuation] THEN
    DISCH_THEN(MP_TAC o SPEC
     `!!0 (!!1 (!!2 (V 0 === V 1 --> (V 2 === V 1 --> V 0 === V 2))))`) THEN
    REWRITE_TAC[holds; valmod; Equal_DEF; MAP; termval; ARITH_EQ] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:A b. equiv a b ==> equiv b a`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:A b. equiv a b ==> (canonize a :A = canonize b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "canonize" THEN
    AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(Dom M' :A->bool = EMPTY)` ASSUME_TAC THENL
   [EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
    UNDISCH_TAC `~(Dom M :A->bool = EMPTY)` THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    EXISTS_TAC `(canonize:A->A) a` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(equiv:A->A->bool) a (canonize a)`
      (fun th -> ASM_MESON_TAC[th]) THEN
    EXPAND_TAC "canonize" THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `a:A` THEN EXPAND_TAC "equiv" THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(M:(A->bool)#(num->A list->A)#(num->A list->bool))
                 satisfies
               { (!!0 (V 0 === V 0)) }` THEN
    REWRITE_TAC[satisfies; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPECL [`\n:num. a:A`;  `!! 0 (V 0 === V 0)`]) THEN
    ASM_REWRITE_TAC[valuation] THEN
    REWRITE_TAC[holds; Equal_DEF; MAP; termval; valmod] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[interpretation; language] THEN
    EXPAND_TAC "M'" THEN REWRITE_TAC[Fun_DEF; Dom_DEF] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(equiv:A->A->bool) (Fun M f l) (canonize (Fun M f l))`
      (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[language; interpretation]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ALL_IMP THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC (lhand(concl th)) THEN
                      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!t v. valuation M (v:num->A) /\
                      t IN terms (functions s)
                      ==> (termval M' (canonize o v) t =
                           (canonize:A->A) (termval M v t))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    GEN_TAC THEN EXPAND_TAC "M'" THEN
    DISCH_THEN(ASSUME_TAC o GSYM o
      REWRITE_RULE[valuation; Dom_DEF; IN_ELIM_THM]) THEN
    MATCH_MP_TAC term_INDUCT THEN
    ASM_REWRITE_TAC[termval; Fun_DEF] THEN REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `f:num` THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXPAND_TAC "equiv" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 termval)] THEN
      MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
      EXISTS_TAC `functions s` THEN
      ASM_REWRITE_TAC[valuation] THEN
      UNDISCH_TAC `interpretation (language s)
                   (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
      REWRITE_TAC[language] THEN
      MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
      MATCH_MP_TAC FORALL_TERMS_RAW THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN ASM_REWRITE_TAC[];

      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[interpretation; language]) THEN
      UNDISCH_TAC `Fn f l IN terms (functions s)` THEN
      REWRITE_TAC[IN; LENGTH_MAP] THEN ONCE_REWRITE_TAC[terms_CASES] THEN
      REWRITE_TAC[term_INJ; term_DISTINCT] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:num` MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `L:term list` MP_TAC) THEN
      DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN
                           REWRITE_TAC[GSYM(CONJUNCT1 th)]) THEN
      REWRITE_TAC[IN] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ALL_MAP] THEN
      MATCH_MP_TAC ALL_IMP THEN
      FIRST_ASSUM(fun th -> EXISTS_TAC (lhand(concl th)) THEN
                      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC]) THEN
      X_GEN_TAC `u:term` THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(termval M' ((canonize:A->A) o v) u) IN (Dom M')`
      MP_TAC THENL
       [MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
        EXISTS_TAC `ppp:num#num->bool` THEN CONJ_TAC THENL
         [UNDISCH_TAC `interpretation (language s)
                 (M':(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
          REWRITE_TAC[language] THEN
          MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
          UNDISCH_TAC `terms (functions s) u` THEN
          SPEC_TAC(`functions s`,`fns:num#num->bool`) THEN
          SPEC_TAC(`u:term`,`u:term`) THEN
          MATCH_MP_TAC term_INDUCT THEN
          REWRITE_TAC[functions_term; EMPTY_SUBSET] THEN
          REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
          GEN_REWRITE_TAC LAND_CONV [terms_CASES] THEN
          REWRITE_TAC[term_INJ; term_DISTINCT] THEN
          DISCH_THEN(X_CHOOSE_THEN `g:num` MP_TAC) THEN
          DISCH_THEN(X_CHOOSE_THEN `L:term list` MP_TAC) THEN
          DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN
                               REWRITE_TAC[GSYM(CONJUNCT1 th)]) THEN
          STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC lemma2 THEN
          REWRITE_TAC[ALL_MAP] THEN
          MATCH_MP_TAC ALL_IMP THEN EXISTS_TAC
            `\u. !fns. terms fns u ==> functions_term u SUBSET fns` THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_THM] THEN
          X_GEN_TAC `tt:term` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          UNDISCH_TAC `MEM (tt:term) l'` THEN
          UNDISCH_TAC `ALL (terms fns) l'` THEN
          SPEC_TAC(`l':term list`,`ll:term list`) THEN
          LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MEM] THEN
          ASM_MESON_TAC[];
          REWRITE_TAC[valuation; o_THM] THEN
          X_GEN_TAC `x:num` THEN EXPAND_TAC "M'" THEN
          REWRITE_TAC[Dom_DEF] THEN REWRITE_TAC[IN_ELIM_THM] THEN
          ASM_MESON_TAC[]];
        REWRITE_TAC[IN] THEN
        EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        SIMP_TAC[IN]];

      UNDISCH_TAC `(M:(A->bool)#(num->A list->A)#(num->A list->bool))
                   satisfies {Eqaxiom_Func fa | fa IN FST (language s)}` THEN
      REWRITE_TAC[satisfies; IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `Eqaxiom_Func (f,LENGTH (l:term list))`) THEN
      REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `(f:num,LENGTH(l:term list))`) THEN
      REWRITE_TAC[] THEN
      REWRITE_TAC[Eqaxiom_Func] THEN
      SUBGOAL_THEN `?a:A. a IN Dom(M)` CHOOSE_TAC THENL
       [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `\n:num. a:A`) THEN
      ASM_REWRITE_TAC[valuation] THEN
      UNDISCH_TAC `Fn f l IN terms (functions s)` THEN
      REWRITE_TAC[IN] THEN ONCE_REWRITE_TAC[terms_CASES] THEN
      REWRITE_TAC[term_INJ; term_DISTINCT] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:num` MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `L:term list` MP_TAC) THEN
      DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN
                           REWRITE_TAC[GSYM(CONJUNCT1 th)]) THEN
      REWRITE_TAC[language; IN] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP HOLDS_UCLOSE_ANY) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[holds; HOLDS_ANDS; Equal_DEF; MAP; GSYM MAP_o] THEN
      REWRITE_TAC[termval] THEN
      REWRITE_TAC[ALL_MAP; o_DEF; PAIR_LEMMA; holds] THEN
      REWRITE_TAC[MAP] THEN
      REWRITE_TAC[FORALL2_VARPAIRS] THEN
      DISCH_THEN(MP_TAC o SPEC
       `\n:num. if 2 * LENGTH l <= n then a
                else if EVEN(n)
                then termval M v
                       (EL ((LENGTH l - 1) - (n DIV 2)) l) :A
                else termval M' (canonize o v)
                       (EL ((LENGTH l - 1) - (n DIV 2)) l)`) THEN
      REWRITE_TAC[RECONSTRUCT_TERMVAL] THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
      REWRITE_TAC[IMP_IMP] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [o_DEF] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[FORALL2_FORALL] THEN CONJ_TAC THENL
       [REWRITE_TAC[valuation] THEN X_GEN_TAC `k:num` THEN
        ASM_CASES_TAC `2 * LENGTH (l:term list) <= k` THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
         [MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
          EXISTS_TAC `ppp:num#num->bool` THEN
          ASM_REWRITE_TAC[valuation] THEN
          UNDISCH_TAC `interpretation (language s)
              (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
          REWRITE_TAC[language] THEN
          MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
          MATCH_MP_TAC FORALL_TERMS_INDEXED THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `~(2 * LENGTH (l:term list) <= k)` THEN
          REWRITE_TAC[ARITH_RULE `~(2 * n <= k) ==> n - 1 - m < n`];
          SUBGOAL_THEN `termval M' ((canonize:A->A) o v)
                                   (EL (LENGTH l - 1 - k DIV 2) l) IN
                        (Dom M' :A->bool)` MP_TAC THENL
           [MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
            EXISTS_TAC `ppp:num#num->bool` THEN
            ASM_REWRITE_TAC[valuation] THEN CONJ_TAC THENL
             [UNDISCH_TAC `interpretation (language s)
                (M':(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
              REWRITE_TAC[language] THEN
              MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
              MATCH_MP_TAC FORALL_TERMS_INDEXED THEN
              ASM_REWRITE_TAC[] THEN
              UNDISCH_TAC `~(2 * LENGTH (l:term list) <= k)` THEN
              REWRITE_TAC[ARITH_RULE `~(2 * n <= k) ==> n - 1 - m < n`];
              EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF; o_THM] THEN
              ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
            EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
            ASM_REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]];
        MATCH_MP_TAC ALL_IMP THEN
        EXISTS_TAC `\t. terms (functions s) t /\
                        (t IN terms (functions s)
                         ==> (termval M' (canonize o v) t =
                              (canonize:A->A) (termval M v t)))` THEN
        REWRITE_TAC[GSYM AND_ALL] THEN
        CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `(equiv:A->A->bool) (termval M v x)
                                         (termval M' (canonize o v) x)`
        MP_TAC THENL [ALL_TAC; EXPAND_TAC "equiv" THEN SIMP_TAC[]] THEN
        SUBGOAL_THEN `!a b. (a = canonize b) /\ b IN Dom(M)
                            ==> (equiv:A->A->bool) b a`
        MATCH_MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[IN]; ALL_TAC] THEN
        MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
        EXISTS_TAC `functions s` THEN
        ASM_REWRITE_TAC[valuation] THEN
        UNDISCH_TAC `interpretation (language s)
                     (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
        REWRITE_TAC[language] THEN
        MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
        MATCH_MP_TAC FORALL_TERMS_RAW THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p v. valuation M (v:num->A) /\
          (functions_form p) SUBSET (functions s) /\
          (predicates_form p) SUBSET (predicates s)
          ==> (holds M' ((canonize:A->A) o v) p <=> holds M v p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC[holds; functions_form; predicates_form] THEN
    REWRITE_TAC[slemma1] THEN REPEAT CONJ_TAC THENL
     [ALL_TAC;
      MESON_TAC[];
      REPEAT GEN_TAC THEN
      DISCH_THEN(fun th -> SIMP_TAC[GSYM th; VALUATION_VALMOD]) THEN
      REWRITE_TAC[clemma1] THEN GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `!P. (!a:A. a IN Dom(M') ==> P a) <=>
                        (!a:A. a IN Dom(M) ==> P(canonize a))`
        (fun th -> REWRITE_TAC[th]) THEN
      GEN_TAC THEN EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]] THEN
    X_GEN_TAC `p:num` THEN X_GEN_TAC `l:term list` THEN GEN_TAC THEN
    REWRITE_TAC[lemma3; lemma4; ALL_MAP] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[o_DEF]) THEN
    EXPAND_TAC "M'" THEN REWRITE_TAC[Pred_DEF] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(M:(A->bool)#(num->A list->A)#(num->A list->bool))
                 satisfies {Eqaxiom_Pred pa | pa IN SND (language s)}` THEN
    REWRITE_TAC[satisfies; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `Eqaxiom_Pred (p,LENGTH (l:term list))`) THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(p:num,LENGTH(l:term list))`) THEN
    REWRITE_TAC[] THEN
    REWRITE_TAC[Eqaxiom_Pred] THEN
    SUBGOAL_THEN `?a:A. a IN Dom(M)` CHOOSE_TAC THENL
     [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `\n:num. a:A`) THEN
    ASM_REWRITE_TAC[valuation] THEN
    ASM_REWRITE_TAC[language] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOLDS_UCLOSE_ANY) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HOLDS; HOLDS_ANDS; Equal_DEF; MAP; GSYM MAP_o] THEN
    REWRITE_TAC[MAP_o] THEN
    DISCH_THEN(MP_TAC o SPEC
     `\n:num. if 2 * LENGTH l <= n then a
              else if EVEN(n)
              then termval M v
                     (EL ((LENGTH l - 1) - (n DIV 2)) l) :A
              else termval M' (canonize o v)
                     (EL ((LENGTH l - 1) - (n DIV 2)) l)`) THEN
    REWRITE_TAC[RECONSTRUCT_TERMVAL] THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(fun th -> CONV_TAC SYM_CONV THEN MATCH_MP_TAC th) THEN
    REWRITE_TAC[FORALL2_FORALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[valuation] THEN X_GEN_TAC `k:num` THEN
      ASM_CASES_TAC `2 * LENGTH (l:term list) <= k` THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
        EXISTS_TAC `ppp:num#num->bool` THEN
        ASM_REWRITE_TAC[valuation] THEN
        UNDISCH_TAC `interpretation (language s)
            (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
        REWRITE_TAC[language] THEN
        MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
        MATCH_MP_TAC FORALL_TERMS_INDEXED THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC ALL_IMP THEN
          EXISTS_TAC `\x. functions_term x SUBSET functions s` THEN
          ASM_REWRITE_TAC[] THEN
          SIMP_TAC[FORALL_TERMS_STRONG];
          UNDISCH_TAC `~(2 * LENGTH (l:term list) <= k)` THEN
          REWRITE_TAC[ARITH_RULE `~(2 * n <= k) ==> n - 1 - m < n`]];
        SUBGOAL_THEN `termval M' ((canonize:A->A) o v)
                                 (EL (LENGTH l - 1 - k DIV 2) l) IN
                      (Dom M' :A->bool)` MP_TAC THENL
         [MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
          EXISTS_TAC `ppp:num#num->bool` THEN
          ASM_REWRITE_TAC[valuation] THEN CONJ_TAC THENL
           [UNDISCH_TAC `interpretation (language s)
              (M':(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
            REWRITE_TAC[language] THEN
            MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
            MATCH_MP_TAC FORALL_TERMS_INDEXED THEN
            ASM_REWRITE_TAC[] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[GSYM FORALL_TERMS_STRONG]) THEN
            RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV ETA_CONV)) THEN
            ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `~(2 * LENGTH (l:term list) <= k)` THEN
            REWRITE_TAC[ARITH_RULE `~(2 * n <= k) ==> n - 1 - m < n`];
            EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF; o_THM] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[valuation]) THEN
            ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
          EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
          ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]];
      REWRITE_TAC[ALL_MAP] THEN
      REWRITE_TAC[PAIR_LEMMA; o_DEF] THEN
      REWRITE_TAC[holds; MAP; termval] THEN
      REWRITE_TAC[FORALL2_VARPAIRS] THEN
      REWRITE_TAC[GSYM MAP_o] THEN
      REWRITE_TAC[FORALL2_FORALL] THEN
      REWRITE_TAC[o_DEF; FORALL2_VARPAIRS] THEN
      REWRITE_TAC[RECONSTRUCT_TERMVAL] THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
      REWRITE_TAC[FORALL2_FORALL] THEN
      REWRITE_TAC[GSYM o_DEF] THEN
      ONCE_REWRITE_TAC[o_DEF] THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC `\x. functions_term x SUBSET functions s` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM FORALL_TERMS_STRONG] THEN
      X_GEN_TAC `t:term` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[IN] THEN
      SUBGOAL_THEN `(equiv:A->A->bool) (termval M v t)
                                       (canonize (termval M v t))`
      MP_TAC THENL
       [SUBGOAL_THEN `termval M v t IN (Dom(M):A->bool)`
          (fun th -> ASM_MESON_TAC[th]) THEN
        MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
        EXISTS_TAC `functions s` THEN
        ASM_REWRITE_TAC[valuation] THEN
        UNDISCH_TAC `interpretation (language s)
                     (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
        REWRITE_TAC[language] THEN
        MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
        MATCH_MP_TAC FORALL_TERMS_RAW THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "equiv" THEN SIMP_TAC[]]]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:term` THEN X_GEN_TAC `u:term` THEN
    X_GEN_TAC `v:num->A` THEN STRIP_TAC THEN
    REWRITE_TAC[Equal_DEF; holds; MAP] THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "M'" THEN REWRITE_TAC[Pred_DEF] THEN
    SUBGOAL_THEN `termval M v t IN (Dom(M):A->bool) /\
                  termval M v u IN Dom(M)`
    ASSUME_TAC THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC INTERPRETATION_TERMVAL THEN
      EXISTS_TAC `ppp:num#num->bool` THEN
      UNDISCH_TAC `valuation M' (v:num->A)` THEN
      EXPAND_TAC "M'" THEN REWRITE_TAC[valuation; Dom_DEF] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `interpretation (language s)
                    (M:(A->bool)#(num->A list->A)#(num->A list->bool))` THEN
      REWRITE_TAC[language] THEN
      MATCH_MP_TAC INTERPRETATION_SUBLANGUAGE THEN
      MATCH_MP_TAC FORALL_TERMS_RAW THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN `canonize o (v:num->A) = v`
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN
      REWRITE_TAC[o_THM] THEN
      UNDISCH_TAC `valuation M' (v:num->A)` THEN
      REWRITE_TAC[valuation] THEN
      EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `valuation M (v:num->A)` ASSUME_TAC THENL
     [UNDISCH_TAC `valuation M' (v:num->A)` THEN
      REWRITE_TAC[valuation] THEN
      EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(equiv:A->A->bool) ((canonize:A->A) (termval M v t))
                                   (canonize (termval M v u))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "equiv" THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(equiv:A->A->bool) (termval M v t) (termval M v u)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[satisfies] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `canonize o (v:num->A) = v`
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN
    REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `valuation M' (v:num->A)` THEN
    REWRITE_TAC[valuation] THEN
    EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `valuation M (v:num->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `valuation M' (v:num->A)` THEN
    REWRITE_TAC[valuation] THEN
    EXPAND_TAC "M'" THEN REWRITE_TAC[Dom_DEF] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `functions_form p SUBSET functions s /\
                predicates_form p SUBSET predicates s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[functions; predicates] THEN
    UNDISCH_TAC `p:form IN s` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[satisfies]) THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Compactness and Lowenheim-Skolem for normal models.                       *)
(* ------------------------------------------------------------------------- *)

let FUNCTIONS_SUBSET = prove
 (`!s t. t SUBSET s ==> functions t SUBSET functions s`,
  REWRITE_TAC[SUBSET; functions; IN_ELIM_THM; IN_UNIONS] THEN MESON_TAC[]);;

let INTERPRETATION_MODIFY_LANGUAGE = prove
 (`!s s' t.
        t SUBSET s /\
        (?M. interpretation (language s) M /\
             ~(Dom M :A->bool = EMPTY) /\
             M satisfies t)
        ==> ?M. interpretation (language s') M /\
                ~(Dom M :A->bool = EMPTY) /\
                M satisfies t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `Dom(M):A->bool,
              (\g zs. if (g,LENGTH zs) IN functions s then Fun(M) g zs
                      else @a. a IN Dom(M)),
              Pred(M)` THEN
  REWRITE_TAC[Dom_DEF; Fun_DEF; Pred_DEF; interpretation; language] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE [language; interpretation]) THEN
      ASM_REWRITE_TAC[];
      CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [satisfies]) THEN
    REWRITE_TAC[satisfies] THEN
    ASM_REWRITE_TAC[valuation; Dom_DEF] THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
    STRIP_TAC THEN SPEC_TAC(`v:num->A`,`v:num->A`) THEN
    MATCH_MP_TAC HOLDS_FUNCTIONS THEN
    REWRITE_TAC[Dom_DEF; Fun_DEF; Pred_DEF] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_UNIONS; functions; SUBSET;
                                IN_ELIM_THM]) THEN
    ASM_MESON_TAC[]]);;

let INTERPRETATION_RESTRICT_LANGUAGE = prove
 (`!s s' t.
        s' SUBSET s /\
        (?M. interpretation (language s) M /\
             ~(Dom M :A->bool = EMPTY) /\
             M satisfies t)
        ==> ?M. interpretation (language s') M /\
                ~(Dom M :A->bool = EMPTY) /\
                M satisfies t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBSET; language; interpretation] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[FUNCTIONS_SUBSET; SUBSET]);;

let FUNCTIONS_INSERT = prove
 (`functions(p INSERT s) = functions_form p UNION functions s`,
  REWRITE_TAC[EXTENSION; functions; IN_UNION; IN_INSERT;
              IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let FUNCTIONS_UNION = prove
 (`functions (s UNION t) = functions s UNION functions t`,
  REWRITE_TAC[EXTENSION; functions; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let PREDICATES_UNION = prove
 (`predicates (s UNION t) = predicates s UNION predicates t`,
  REWRITE_TAC[EXTENSION; predicates; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let FUNCTIONS_FORM_UCLOSE = prove
 (`functions_form(uclose p) = functions_form p`,
  REWRITE_TAC[uclose] THEN
  SPEC_TAC(`list_of_set(FV p)`,`l:num list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; functions_form]);;

let FUNCTIONS_TERM_FNV1 = prove
 (`functions_term (Fn p (MAP FST (Varpairs n))) = {(p,n)}`,
  REWRITE_TAC[functions_term; LENGTH_MAP; LENGTH_VARPAIRS] THEN
  AP_TERM_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN
  REWRITE_TAC[MAP; Varpairs_DEF; functions_term; LIST_UNION] THEN
  ASM_REWRITE_TAC[UNION_EMPTY]);;

let FUNCTIONS_FORM_FNV1 = prove
 (`!n. LIST_UNION (MAP functions_term (MAP FST (Varpairs n))) = EMPTY`,
  INDUCT_TAC THEN
  REWRITE_TAC[MAP; Varpairs_DEF; functions_term; LIST_UNION] THEN
  ASM_REWRITE_TAC[UNION_EMPTY]);;

let FUNCTIONS_FORM_FNV2 = prove
 (`!n. LIST_UNION (MAP functions_term (MAP SND (Varpairs n))) = EMPTY`,
  INDUCT_TAC THEN
  REWRITE_TAC[MAP; Varpairs_DEF; functions_term; LIST_UNION] THEN
  ASM_REWRITE_TAC[UNION_EMPTY]);;

let FUNCTIONS_TERM_FNV2 = prove
 (`functions_term (Fn p (MAP SND (Varpairs n))) = {(p,n)}`,
  REWRITE_TAC[functions_term; LENGTH_MAP; LENGTH_VARPAIRS] THEN
  AP_TERM_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN
  REWRITE_TAC[MAP; Varpairs_DEF; functions_term; LIST_UNION] THEN
  ASM_REWRITE_TAC[UNION_EMPTY]);;

let FUNCTIONS_EQCONJ = prove
 (`!n. functions_form(ITLIST (&&) (MAP (\(s,t). Atom 0 [s; t])
                                       (Varpairs n)) True) = EMPTY`,
  INDUCT_TAC THEN
  REWRITE_TAC[Varpairs_DEF; ITLIST; MAP; True_DEF;
       Not_DEF; functions_form; UNION_EMPTY; PAIR_LEMMA; And_DEF; Or_DEF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[True_DEF; Not_DEF]) THEN
  ASM_REWRITE_TAC[LIST_UNION; functions_term; UNION_EMPTY]);;

let FUNCTIONS_EQAXIOM_FUNC = prove
 (`!fa. functions_form (Eqaxiom_Func fa) = {fa}`,
  REWRITE_TAC[FORALL_PAIR_THM; Eqaxiom_Func] THEN
  REWRITE_TAC[FUNCTIONS_FORM_UCLOSE] THEN
  REWRITE_TAC[functions_form; Equal_DEF; MAP; LIST_UNION] THEN
  REWRITE_TAC[FUNCTIONS_TERM_FNV1; FUNCTIONS_TERM_FNV2] THEN
  REWRITE_TAC[FUNCTIONS_EQCONJ] THEN
  REWRITE_TAC[UNION_EMPTY; UNION_IDEMPOT]);;

let FUNCTIONS_EQAXIOM_PRED = prove
 (`!pa. functions_form (Eqaxiom_Pred pa) = EMPTY`,
  REWRITE_TAC[FORALL_PAIR_THM; Eqaxiom_Pred] THEN
  REWRITE_TAC[FUNCTIONS_FORM_UCLOSE] THEN
  REWRITE_TAC[functions_form; Equal_DEF; MAP; LIST_UNION] THEN
  REWRITE_TAC[FUNCTIONS_TERM_FNV1; FUNCTIONS_TERM_FNV2] THEN
  REWRITE_TAC[FUNCTIONS_EQCONJ] THEN
  REWRITE_TAC[functions_form; Iff_DEF; And_DEF; Not_DEF; Or_DEF] THEN
  REWRITE_TAC[FUNCTIONS_FORM_FNV1; FUNCTIONS_FORM_FNV2] THEN
  REWRITE_TAC[UNION_EMPTY; UNION_IDEMPOT]);;

let FUNCTIONS_EQAXIOM = prove
 (`functions (Eqaxioms (language s)) = functions s`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[functions; Eqaxioms_DEF; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[language] THEN GEN_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV o BINDER_CONV o
                   LAND_CONV o ONCE_DEPTH_CONV) [CONJ_SYM] THEN
  REWRITE_TAC[OR_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_OR_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
  REWRITE_TAC[EXISTS_OR_THM; GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[functions_form; Equal_DEF; LIST_UNION; MAP] THEN
  REWRITE_TAC[functions_term; IN_UNION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[FUNCTIONS_EQAXIOM_FUNC; FUNCTIONS_EQAXIOM_PRED] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[functions; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERPRETATION_EQAXIOMS = prove
 (`interpretation (language s) M =
   interpretation (language (s UNION (Eqaxioms (language s)))) M`,
  REWRITE_TAC[interpretation; language] THEN
  REWRITE_TAC[FUNCTIONS_UNION] THEN
  REWRITE_TAC[GSYM language; FUNCTIONS_EQAXIOM] THEN
  REWRITE_TAC[UNION_IDEMPOT]);;

let TERMS_SUBSET = prove
 (`!f1 f2. f1 SUBSET f2 ==> terms f1 SUBSET terms f2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN] THEN
  MATCH_MP_TAC terms_INDUCT THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[terms_CASES] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[terms_CASES] THEN
    DISJ2_TAC THEN RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV ETA_CONV)) THEN
    ASM_MESON_TAC[SUBSET]]);;

let EQAXIOMS_UNION = prove
 (`Eqaxioms (language (s UNION t)) =
   Eqaxioms (language s) UNION Eqaxioms (language t)`,
  REWRITE_TAC[Eqaxioms_DEF; language; FUNCTIONS_UNION; PREDICATES_UNION] THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let EQAXIOMS_SUBSET = prove
 (`s SUBSET t ==> Eqaxioms (language s) SUBSET Eqaxioms (language t)`,
  REWRITE_TAC[SUBSET_UNION_ABSORPTION; GSYM EQAXIOMS_UNION] THEN SIMP_TAC[]);;

let IN_EQAXIOMS = prove
 (`p IN Eqaxioms (language s)
   ==> (s = EMPTY) \/ ?q. q IN s /\ p IN Eqaxioms (language {q})`,
  REWRITE_TAC[Eqaxioms_DEF; language] THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[functions; predicates; IN_UNIONS; IN_ELIM_THM] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let COMPACT_LS_NORM_LEMMA1 = prove
 (`(!t. FINITE t /\ t SUBSET s
        ==> ?M. interpretation (language s) M /\
                ~(Dom M :A->bool = EMPTY) /\
                normal (functions s) M /\
                M satisfies t)
   ==> (!t. FINITE t /\ t SUBSET s
            ==> ?M. interpretation (language t) M /\
                    ~(Dom M :A->bool = EMPTY) /\
                    normal (functions t) M /\
                    M satisfies t)`,
  let lemma = prove
   (`(!t. P t ==> !M. Q t M ==> R t M)
     ==> (!t. P t ==> ?M. Q t M) ==> (!t. P t ==> ?M. R t M)`,
    MESON_TAC[]) in
  MATCH_MP_TAC lemma THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  REWRITE_TAC[interpretation; normal; language] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBSET; FUNCTIONS_SUBSET; TERMS_SUBSET]);;

let COMPACT_LS_NORM_LEMMA2a = prove
 (`FINITE t /\ t SUBSET Eqaxioms (language s)
   ==> ?s0. FINITE s0 /\ s0 SUBSET s /\ t SUBSET Eqaxioms (language s0)`,
  let lemma = prove
   (`(x INSERT s SUBSET t <=> x IN t /\ s SUBSET t) /\
     (u UNION s SUBSET t <=> u SUBSET t /\ s SUBSET t)`,
    SET_TAC[]) in
  REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`t:form->bool`,`t:form->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[EMPTY_SUBSET] THEN CONJ_TAC THENL
   [EXISTS_TAC `EMPTY:form->bool` THEN
    REWRITE_TAC[EMPTY_SUBSET; FINITE_RULES]; ALL_TAC] THEN
  REWRITE_TAC[lemma] THEN
  X_GEN_TAC `p:form` THEN X_GEN_TAC `t:form->bool` THEN DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (ANTE_RES_THEN MP_TAC)) THEN
  POP_ASSUM(K ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:form->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `s:form->bool = EMPTY` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN EXISTS_TAC `s0:form->bool` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[EQAXIOMS_SUBSET; SUBSET; EMPTY_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP IN_EQAXIOMS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:form` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{(q:form)} UNION s0` THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_UNION; lemma] THEN
  REWRITE_TAC[FINITE_RULES; EMPTY_SUBSET] THEN
  ASM_REWRITE_TAC[EQAXIOMS_UNION; IN_UNION] THEN
  UNDISCH_TAC `t SUBSET Eqaxioms (language s0)` THEN SET_TAC[]);;

let COMPACT_LS_NORM_LEMMA2 = prove
 (`!t. FINITE t /\ t SUBSET s UNION (Eqaxioms (language s))
       ==> ?u. t SUBSET (u UNION (Eqaxioms (language u))) /\
               FINITE u /\ u SUBSET s`,
  let lemma = prove
   (`(s:A->bool) SUBSET (t UNION u)
     ==> ?s0 s1. (s = s0 UNION s1) /\ s0 SUBSET t /\ s1 SUBSET u`,
    DISCH_THEN(fun th ->
      EXISTS_TAC `(s:A->bool) INTER t` THEN
      EXISTS_TAC `(s:A->bool) INTER u` THEN
      MP_TAC th) THEN
    SET_TAC[]) in
  let slemma1 = prove
   (`(s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u`,
    SET_TAC[]) in
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:form->bool` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:form->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[FINITE_UNION] THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
    ASSUME_TAC(CONJUNCT1 th1) THEN
    ASSUME_TAC(CONJUNCT1 th2) THEN
    MP_TAC(CONJ (CONJUNCT2 th1) (CONJUNCT2 th2)))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_LS_NORM_LEMMA2a) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:form->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(b:form->bool) UNION s0` THEN
  ASM_REWRITE_TAC[slemma1; FINITE_UNION] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EQAXIOMS_UNION] THEN
  UNDISCH_TAC `e SUBSET Eqaxioms (language s0)` THEN SET_TAC[]);;

let COMPACT_LS_NORM = prove
 (`(!t. FINITE t /\ t SUBSET s ==> ?M. interpretation(language s) M /\
                                       ~(Dom(M):A->bool = EMPTY) /\
                                       normal (functions s) M /\
                                       M satisfies t)
   ==> ?C. interpretation (language s) C /\
           ~(Dom(C):term->bool = EMPTY) /\
           normal (functions s) C /\
           C satisfies s`,
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_LS_NORM_LEMMA1) THEN
  REWRITE_TAC[NORMAL_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC INTERPRETATION_RESTRICT_LANGUAGE THEN
  EXISTS_TAC `s UNION (Eqaxioms (language s))` THEN
  REWRITE_TAC[SUBSET_UNION] THEN
  MATCH_MP_TAC COMPACT_LS THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_LS_NORM_LEMMA2) THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [INTERPRETATION_EQAXIOMS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT]
    INTERPRETATION_MODIFY_LANGUAGE)) THEN
  DISCH_THEN(MP_TAC o SPEC `s:form->bool`) THEN
  REWRITE_TAC[SUBSET_REFL] THEN
  REWRITE_TAC[GSYM INTERPRETATION_EQAXIOMS] THEN
  REWRITE_TAC[satisfies] THEN ASM_MESON_TAC[SUBSET]);;
