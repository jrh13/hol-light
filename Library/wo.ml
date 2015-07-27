(* ========================================================================= *)
(* Proof of some useful AC equivalents like wellordering and Zorn's Lemma.   *)
(*                                                                           *)
(* This is a straight port of the old HOL88 wellorder library. I started to  *)
(* clean up the proofs to exploit first order automation, but didn't have    *)
(* the patience to persist till the end. Anyway, the proofs work!            *)
(* ========================================================================= *)

let PBETA_TAC = CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV);;

let EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
  check((=) s o fst o dest_var o rhs o concl)) THEN BETA_TAC;;

let SUBSET_PRED = prove
 (`!P Q. P SUBSET Q <=> !x. P x ==> Q x`,
  REWRITE_TAC[SUBSET; IN]);;

let UNIONS_PRED = prove
 (`UNIONS P = \x. ?p. P p /\ p x`,
  REWRITE_TAC[UNIONS; FUN_EQ_THM; IN_ELIM_THM; IN]);;

(* ======================================================================== *)
(* (1) Definitions and general lemmas.                                      *)
(* ======================================================================== *)

(* ------------------------------------------------------------------------ *)
(* Irreflexive version of an ordering.                                      *)
(* ------------------------------------------------------------------------ *)

let less = new_definition
  `(less l)(x,y) <=> (l:A#A->bool)(x,y) /\ ~(x = y)`;;

(* ------------------------------------------------------------------------ *)
(* Field of an uncurried binary relation                                    *)
(* ------------------------------------------------------------------------ *)

let fl = new_definition
  `fl(l:A#A->bool) x <=> ?y:A. l(x,y) \/ l(y,x)`;;

(* ------------------------------------------------------------------------ *)
(* Partial order (we infer the domain from the field of the relation)       *)
(* ------------------------------------------------------------------------ *)

let poset = new_definition
  `poset (l:A#A->bool) <=>
       (!x. fl(l) x ==> l(x,x)) /\
       (!x y z. l(x,y) /\ l(y,z) ==> l(x,z)) /\
       (!x y. l(x,y) /\ l(y,x) ==> (x = y))`;;

(* ------------------------------------------------------------------------ *)
(* Chain in a poset (Defined as a subset of the field, not the ordering)    *)
(* ------------------------------------------------------------------------ *)

let chain = new_definition
  `chain(l:A#A->bool) P <=> (!x y. P x /\ P y ==> l(x,y) \/ l(y,x))`;;

(* ------------------------------------------------------------------------- *)
(* Total order.                                                              *)
(* ------------------------------------------------------------------------- *)

let toset = new_definition
 `toset (l:A#A->bool) <=>
        poset l /\ !x y. x IN fl(l) /\ y IN fl(l) ==> l(x,y) \/ l(y,x)`;;

(* ------------------------------------------------------------------------ *)
(* Wellorder                                                                *)
(* ------------------------------------------------------------------------ *)

let woset = new_definition
 `woset (l:A#A->bool) <=>
       (!x. fl(l) x ==> l(x,x)) /\
       (!x y z. l(x,y) /\ l(y,z) ==> l(x,z)) /\
       (!x y. l(x,y) /\ l(y,x) ==> (x = y)) /\
       (!x y. fl(l) x /\ fl(l) y ==> l(x,y) \/ l(y,x)) /\
       (!P. (!x. P x ==> fl(l) x) /\ (?x. P x) ==>
            (?y. P y /\ (!z. P z ==> l(y,z))))`;;

(* ------------------------------------------------------------------------ *)
(* General (reflexive) notion of initial segment.                           *)
(* ------------------------------------------------------------------------ *)

parse_as_infix("inseg",(12,"right"));;

let inseg = new_definition
  `(l:A#A->bool) inseg m <=> !x y. l(x,y) <=> m(x,y) /\ fl(l) y`;;

let INSEG_ANTISYM = prove
 (`!l m:A#A->bool. l inseg m /\ m inseg l ==> l = m`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[inseg] THEN MESON_TAC[]);;

let INSEG_REFL = prove
 (`!l:A#A->bool. l inseg l`,
  REWRITE_TAC[inseg; fl] THEN MESON_TAC[]);;

let INSEG_TRANS = prove
 (`!l m n:A#A->bool. l inseg m /\ m inseg n ==> l inseg n`,
  REWRITE_TAC[inseg; fl] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Specific form of initial segment: `all elements in fl(l) less than a`.   *)
(* ------------------------------------------------------------------------ *)

let linseg = new_definition
  `linseg (l:A#A->bool) a = \(x,y). l(x,y) /\ (less l)(y,a)`;;

(* ------------------------------------------------------------------------ *)
(* `Ordinals`, i.e. canonical wosets using choice operator.                 *)
(* ------------------------------------------------------------------------ *)

let ordinal = new_definition
  `ordinal(l:A#A->bool) <=>
    woset(l) /\ (!x. fl(l) x ==> (x = (@) (\y. ~(less l)(y,x))))`;;

(* ------------------------------------------------------------------------ *)
(* Now useful things about the orderings                                    *)
(* ------------------------------------------------------------------------ *)

let [POSET_REFL; POSET_TRANS; POSET_ANTISYM] =
  map (GEN `l:A#A->bool` o DISCH_ALL)
  (CONJUNCTS(PURE_ONCE_REWRITE_RULE[poset] (ASSUME `poset (l:A#A->bool)`)));;

let POSET_FLEQ = prove
 (`!l:A#A->bool. poset l ==> (!x. fl(l) x <=> l(x,x))`,
  MESON_TAC[POSET_REFL; fl]);;

let CHAIN_SUBSET = prove
 (`!(l:A#A->bool) P Q. chain(l) P /\ Q SUBSET P ==> chain(l) Q`,
  REWRITE_TAC[chain; SUBSET_PRED] THEN MESON_TAC[]);;

let [WOSET_REFL; WOSET_TRANS; WOSET_ANTISYM; WOSET_TOTAL; WOSET_WELL] =
  map (GEN `l:A#A->bool` o DISCH_ALL)
    (CONJUNCTS(PURE_ONCE_REWRITE_RULE[woset] (ASSUME `woset (l:A#A->bool)`)));;

let WOSET_POSET = prove
 (`!l:A#A->bool. woset l ==> poset l`,
  GEN_TAC THEN REWRITE_TAC[woset; poset] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

let WOSET_FLEQ = prove
 (`!l:A#A->bool. woset l ==> (!x. fl(l) x <=> l(x,x))`,
  MESON_TAC[WOSET_POSET; POSET_FLEQ]);;

let WOSET_TRANS_LESS = prove
 (`!l:A#A->bool. woset l ==>
       !x y z. (less l)(x,y) /\ l(y,z) ==> (less l)(x,z)`,
  REWRITE_TAC[woset; less] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Wellfoundedness (in two slightly different senses) and either totality   *)
(* or antisymmetry are sufficient for a wellorder.                          *)
(* ------------------------------------------------------------------------ *)

let WOSET = prove
 (`!l:A#A->bool.
        woset l <=>
        (!x y. l(x,y) /\ l(y,x) ==> (x = y)) /\
        (!P. (!x. P x ==> fl(l) x) /\ (?x. P x) ==>
             (?y. P y /\ (!z. P z ==> l(y,z))))`,
  GEN_TAC THEN REWRITE_TAC[woset] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(!x y z. l(x,y) /\ l(y,z) ==> l(x,z)) /\
                (!x:A y. fl(l) x /\ fl(l) y ==> l(x,y) \/ l(y,x))`
  MP_TAC THENL [ALL_TAC; MESON_TAC[]] THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `\w:A. (w = x) \/ (w = y) \/ (w = z)`) THEN
    REWRITE_TAC[fl];
    FIRST_ASSUM(MP_TAC o SPEC `\w:A. (w = x) \/ (w = y)`)] THEN
  ASM_MESON_TAC[]);;

let WOSET_WF = prove
 (`!l:A#A->bool.
        woset l <=>
        WF(\x y. l(x,y) /\ ~(x = y)) /\
        (!x y. fl l x /\ fl l y ==> l(x,y) \/ l(y,x))`,
  GEN_TAC THEN
  ASM_CASES_TAC `!x y:A. fl l x /\ fl l y ==> l(x,y) \/ l(y,x)` THENL
   [ASM_REWRITE_TAC[WOSET]; ASM_REWRITE_TAC[woset]] THEN
  ASM_CASES_TAC `!x y:A. l(x,y) /\ l(y,x) ==> x = y` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[WF];
    DISCH_THEN(MP_TAC o MATCH_MP WF_ANTISYM) THEN ASM_MESON_TAC[]] THEN
  EQ_TAC THENL [DISCH_TAC; MATCH_MP_TAC MONO_FORALL THEN ASM_MESON_TAC[]] THEN
  X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\x:A. P x /\ fl l x`) THEN
  REWRITE_TAC[fl] THEN ASM_MESON_TAC[]);;

let WOSET_FINITE_TOSET = prove
 (`!l:A#A->bool. toset l /\ FINITE(fl l) ==> woset l`,
  SIMP_TAC[toset; WOSET_WF; poset; IN] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WF_FINITE THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; X_GEN_TAC `a:A`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    FINITE_SUBSET)) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[fl; IN] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Misc lemmas.                                                             *)
(* ------------------------------------------------------------------------ *)

let PAIRED_EXT = prove
 (`!(l:A#B->C) m. (!x y. l(x,y) = m(x,y)) <=> (l = m)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:A#B` THEN
  SUBST1_TAC(SYM(SPEC `p:A#B` PAIR)) THEN POP_ASSUM MATCH_ACCEPT_TAC);;

let WOSET_TRANS_LE = prove
 (`!l:A#A->bool. woset l ==>
       !x y z. l(x,y) /\ (less l)(y,z) ==> (less l)(x,z)`,
  REWRITE_TAC[less] THEN MESON_TAC[WOSET_TRANS; WOSET_ANTISYM]);;

let WOSET_WELL_CONTRAPOS = prove
 (`!l:A#A->bool. woset l ==>
                (!P. (!x. P x ==> fl(l) x) /\ (?x. P x) ==>
                     (?y. P y /\ (!z. (less l)(z,y) ==> ~P z)))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `P:A->bool` o MATCH_MP WOSET_WELL) THEN
  ASM_MESON_TAC[WOSET_TRANS_LE; less]);;

let WOSET_TOTAL_LE = prove
 (`!l:A#A->bool. woset l
                 ==> !x y. fl(l) x /\ fl(l) y ==> l(x,y) \/ (less l)(y,x)`,
  REWRITE_TAC[less] THEN MESON_TAC[WOSET_REFL; WOSET_TOTAL]);;

let WOSET_TOTAL_LT = prove
 (`!l:A#A->bool. woset l ==>
     !x y. fl(l) x /\ fl(l) y ==> (x = y) \/ (less l)(x,y) \/ (less l)(y,x)`,
  REWRITE_TAC[less] THEN MESON_TAC[WOSET_TOTAL]);;

(* ======================================================================== *)
(* (2) AXIOM OF CHOICE ==> CANTOR-ZERMELO WELLORDERING THEOREM              *)
(* ======================================================================== *)

(* ------------------------------------------------------------------------ *)
(* UNIONS of initial segments is an initial segment.                        *)
(* ------------------------------------------------------------------------ *)

let UNION_FL = prove
 (`!P (l:A#A->bool). fl(UNIONS P) x <=> ?l. P l /\ fl(l) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIONS_PRED; fl] THEN MESON_TAC[]);;

let UNION_INSEG = prove
 (`!P (l:A#A->bool). (!m. P m ==> m inseg l) ==> (UNIONS P) inseg l`,
  REWRITE_TAC[inseg; UNION_FL; UNIONS_PRED] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Initial segment of a woset is a woset.                                   *)
(* ------------------------------------------------------------------------ *)

let INSEG_SUBSET = prove
 (`!(l:A#A->bool) m. m inseg l ==> !x y. m(x,y) ==> l(x,y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inseg] THEN MESON_TAC[]);;

let INSEG_SUBSET_FL = prove
 (`!(l:A#A->bool) m. m inseg l ==> !x. fl(m) x ==> fl(l) x`,
  REWRITE_TAC[fl] THEN MESON_TAC[INSEG_SUBSET]);;

let INSEG_WOSET = prove
 (`!(l:A#A->bool) m. m inseg l /\ woset l ==> woset m`,
  REWRITE_TAC[inseg] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[WOSET] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[WOSET_ANTISYM];
    GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC_ALL o MATCH_MP WOSET_WELL) THEN
    ASM_MESON_TAC[fl]]);;

let INSEG_ORDINAL = prove
 (`!l m:A#A->bool. m inseg l /\ ordinal l ==> ordinal m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinal] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INSEG_WOSET]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INSEG_SUBSET_FL) THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN ASM_REWRITE_TAC[less]);;

(* ------------------------------------------------------------------------ *)
(* Properties of segments of the `linseg` form.                             *)
(* ------------------------------------------------------------------------ *)

let LINSEG_INSEG = prove
 (`!(l:A#A->bool) a. woset l ==> (linseg l a) inseg l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inseg; linseg; fl] THEN PBETA_TAC THEN
  ASM_MESON_TAC[WOSET_TRANS_LE]);;

let LINSEG_WOSET = prove
 (`!(l:A#A->bool) a. woset l ==> woset(linseg l a)`,
  MESON_TAC[INSEG_WOSET; LINSEG_INSEG]);;

let LINSEG_FL = prove
 (`!(l:A#A->bool) a x. woset l ==> (fl (linseg l a) x <=> (less l)(x,a))`,
  REWRITE_TAC[fl; linseg; less] THEN PBETA_TAC THEN
  MESON_TAC[WOSET_REFL; WOSET_TRANS; WOSET_ANTISYM; fl]);;

(* ------------------------------------------------------------------------ *)
(* Key fact: a proper initial segment is of the special form.               *)
(* ------------------------------------------------------------------------ *)

let INSEG_PROPER_SUBSET = prove
 (`!(l:A#A->bool) m. m inseg l /\ ~(l = m) ==>
                   ?x y. l(x,y) /\ ~m(x,y)`,
  REWRITE_TAC[GSYM PAIRED_EXT] THEN MESON_TAC[INSEG_SUBSET]);;

let INSEG_PROPER_SUBSET_FL = prove
 (`!(l:A#A->bool) m. m inseg l /\ ~(l = m) ==>
                   ?a. fl(l) a /\ ~fl(m) a`,
  MESON_TAC[INSEG_PROPER_SUBSET; fl; inseg]);;

let INSEG_LINSEG = prove
 (`!(l:A#A->bool) m. woset l ==>
      (m inseg l <=> (m = l) \/ (?a. fl(l) a /\ (m = linseg l a)))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m:A#A->bool = l` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[inseg; fl] THEN MESON_TAC[]; ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[LINSEG_INSEG]] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL_CONTRAPOS) THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. fl(l) x /\ ~fl(m) x`) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[linseg; GSYM PAIRED_EXT] THEN PBETA_TAC THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
   [ASM_MESON_TAC[INSEG_PROPER_SUBSET_FL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[INSEG_SUBSET; INSEG_SUBSET_FL; fl;
    WOSET_TOTAL_LE; less; inseg]);;

(* ------------------------------------------------------------------------ *)
(* A proper initial segment can be extended by its bounding element.        *)
(* ------------------------------------------------------------------------ *)

let EXTEND_FL = prove
 (`!(l:A#A->bool) x. woset l ==> (fl (\(x,y). l(x,y) /\ l(y,a)) x <=> l(x,a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fl] THEN PBETA_TAC THEN
  ASM_MESON_TAC[WOSET_TRANS; WOSET_REFL; fl]);;

let EXTEND_INSEG = prove
 (`!(l:A#A->bool) a. woset l /\ fl(l) a ==> (\(x,y). l(x,y) /\ l(y,a)) inseg l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inseg] THEN PBETA_TAC THEN
  REPEAT GEN_TAC THEN IMP_RES_THEN (fun t ->REWRITE_TAC[t]) EXTEND_FL);;

let EXTEND_LINSEG = prove
 (`!(l:A#A->bool) a. woset l /\ fl(l) a ==>
       (\(x,y). linseg l a (x,y) \/ (y = a) /\ (fl(linseg l a) x \/ (x = a)))
                inseg l`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC (MATCH_MP EXTEND_INSEG th)) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM PAIRED_EXT] THEN PBETA_TAC THEN
  REPEAT GEN_TAC THEN IMP_RES_THEN (fun th -> REWRITE_TAC[th]) LINSEG_FL THEN
  REWRITE_TAC[linseg; less] THEN PBETA_TAC THEN ASM_MESON_TAC[WOSET_REFL]);;

(* ------------------------------------------------------------------------ *)
(* Key canonicality property of ordinals.                                   *)
(* ------------------------------------------------------------------------ *)

let ORDINAL_CHAINED_LEMMA = prove
 (`!(k:A#A->bool) l m. ordinal(l) /\ ordinal(m)
                       ==> k inseg l /\ k inseg m
                           ==> (k = l) \/ (k = m) \/ ?a. fl(l) a /\ fl(m) a /\
                                                         (k = linseg l a) /\
                                                         (k = linseg m a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinal] THEN STRIP_TAC THEN
  EVERY_ASSUM(fun th -> TRY
    (fun g -> REWRITE_TAC[MATCH_MP INSEG_LINSEG th] g)) THEN
  ASM_CASES_TAC `k:A#A->bool = l` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k:A#A->bool = m` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a:A = b` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_ASSUM(fun th -> SUBST1_TAC(MATCH_MP th (ASSUME `fl(l) (a:A)`))) THEN
  FIRST_ASSUM(fun th -> SUBST1_TAC(MATCH_MP th (ASSUME `fl(m) (b:A)`))) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `k = linseg m (b:A)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linseg; GSYM PAIRED_EXT] THEN PBETA_TAC THEN
  ASM_MESON_TAC[WOSET_REFL; less; fl]);;

let ORDINAL_CHAINED = prove
 (`!(l:A#A->bool) m. ordinal(l) /\ ordinal(m) ==> m inseg l \/ l inseg m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[ordinal] th) THEN
                       ASSUME_TAC (MATCH_MP ORDINAL_CHAINED_LEMMA th)) THEN
  MP_TAC(SPEC `\k:A#A->bool. k inseg l /\ k inseg m` UNION_INSEG) THEN
  DISCH_THEN(fun th ->
    MP_TAC(CONJ (SPEC `l:A#A->bool` th) (SPEC `m:A#A->bool` th))) THEN
  REWRITE_TAC[TAUT `(a /\ b ==> a) /\ (a /\ b ==> b)`] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
                       FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN MP_TAC o
                       C MATCH_MP th)) THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ASSUME `UNIONS (\k. k inseg l /\ k inseg m) = linseg l (a:A)`) THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `(a:A,a)`) THEN
  REWRITE_TAC[linseg] THEN PBETA_TAC THEN REWRITE_TAC[less] THEN
  REWRITE_TAC[UNIONS_PRED] THEN EXISTS_TAC
  `\(x,y). linseg l a (x,y) \/ (y = a) /\ (fl(linseg l a) x \/ (x = a:A))` THEN
  PBETA_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `UNIONS (\k. k inseg l /\ k inseg m) = linseg l (a:A)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC EXTEND_LINSEG THEN ASM_REWRITE_TAC[]);;

let ORDINAL_FL_UNIQUE = prove
 (`!l m:A#A->bool.
        ordinal l /\ ordinal m /\ fl l = fl m ==> l = m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A#A->bool`; `m:A#A->bool`]
        ORDINAL_CHAINED) THEN
  REWRITE_TAC[inseg; FUN_EQ_THM; FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[fl]);;

let ORDINAL_FL_SUBSET = prove
 (`!l m:A#A->bool.
        ordinal l /\ ordinal m /\ fl l SUBSET fl m ==> l inseg m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A#A->bool`; `m:A#A->bool`]
        ORDINAL_CHAINED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[INSEG_REFL] `x = y ==> x inseg y`) THEN
  MATCH_MP_TAC ORDINAL_FL_UNIQUE THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INSEG_SUBSET_FL) THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Proof that any none-universe ordinal can be extended to its "successor". *)
(* ------------------------------------------------------------------------ *)

let FL_SUC = prove
 (`!(l:A#A->bool) a.
     fl(\(x,y). l(x,y) \/ (y = a) /\ (fl(l) x \/ (x = a))) x <=>
     fl(l) x \/ (x = a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fl] THEN PBETA_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY DISJ1_TAC THEN
  ASM_MESON_TAC[]);;

let ORDINAL_SUC = prove
 (`!l:A#A->bool. ordinal(l) /\ (?x. ~(fl(l) x)) ==>
                 ordinal(\(x,y). l(x,y) \/ (y = @y. ~fl(l) y) /\
                                           (fl(l) x \/ (x = @y. ~fl(l) y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ordinal] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `a:A = @y. ~fl(l) y` THEN
  SUBGOAL_THEN `~fl(l:A#A->bool) a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN CONV_TAC SELECT_CONV THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PBETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[WOSET] THEN PBETA_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[WOSET_ANTISYM]; ALL_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~fl(l:A#A->bool) a` THEN CONV_TAC CONTRAPOS_CONV THEN
      DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl) THEN
      DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[fl] THENL
       [EXISTS_TAC `y:A`; EXISTS_TAC `x:A`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `P:A->bool` THEN REWRITE_TAC[FL_SUC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `w:A`)) THEN
      IMP_RES_THEN (MP_TAC o SPEC `\x:A. P x /\ fl(l) x`) WOSET_WELL THEN
      BETA_TAC THEN REWRITE_TAC[TAUT `a /\ b ==> b`] THEN
      ASM_CASES_TAC `?x:A. P x /\ fl(l) x` THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[];
        FIRST_ASSUM(MP_TAC o SPEC `w:A` o
          GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        ASM_MESON_TAC[]]];
    X_GEN_TAC `z:A` THEN REWRITE_TAC[FL_SUC; less] THEN
    PBETA_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
     [UNDISCH_TAC `!x:A. fl l x ==> (x = (@y. ~less l (y,x)))` THEN
      DISCH_THEN(IMP_RES_THEN MP_TAC) THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `y:A` THEN
      BETA_TAC THEN REWRITE_TAC[less] THEN AP_TERM_TAC THEN
      ASM_CASES_TAC `y:A = z` THEN ASM_REWRITE_TAC[] THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `fl(l:A#A->bool) z` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `z:A = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [SYM(ASSUME `(@y:A. ~fl(l) y) = a`)] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `y:A` THEN
      BETA_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `y:A = a` THEN ASM_REWRITE_TAC[] THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[fl] THEN EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------ *)
(* The union of a set of ordinals is an ordinal.                            *)
(* ------------------------------------------------------------------------ *)

let ORDINAL_UNION = prove
 (`!P. (!l:A#A->bool. P l ==> ordinal(l)) ==> ordinal(UNIONS P)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ordinal; WOSET] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN REWRITE_TAC[UNIONS_PRED] THEN
    BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `l:A#A->bool` (CONJUNCTS_THEN2 (ANTE_RES_THEN ASSUME_TAC)
        ASSUME_TAC))
     (X_CHOOSE_THEN `m:A#A->bool` (CONJUNCTS_THEN2 (ANTE_RES_THEN ASSUME_TAC)
        ASSUME_TAC))) THEN
    MP_TAC(SPECL [`l:A#A->bool`; `m:A#A->bool`] ORDINAL_CHAINED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THENL
     [MP_TAC(SPEC `l:A#A->bool` WOSET_ANTISYM);
      MP_TAC(SPEC `m:A#A->bool` WOSET_ANTISYM)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ordinal]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `Q:A->bool` THEN REWRITE_TAC[UNION_FL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `a:A`)) THEN
    MP_TAC(ASSUME `!x:A. Q x ==> (?l. P l /\ fl l x)`) THEN
    DISCH_THEN(IMP_RES_THEN
      (X_CHOOSE_THEN `l:A#A->bool` STRIP_ASSUME_TAC)) THEN
    IMP_RES_THEN ASSUME_TAC (ASSUME `!l:A#A->bool. P l ==> ordinal l`) THEN
    ASSUME_TAC(CONJUNCT1
      (REWRITE_RULE[ordinal] (ASSUME `ordinal(l:A#A->bool)`))) THEN
    IMP_RES_THEN(MP_TAC o SPEC `\x:A. fl(l) x /\ Q x`) WOSET_WELL THEN
    BETA_TAC THEN REWRITE_TAC[TAUT `a /\ b ==> a`] THEN
    SUBGOAL_THEN `?x:A. fl(l) x /\ Q x` (fun th -> REWRITE_TAC[th]) THENL
     [EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ANTE_RES_THEN MP_TAC (ASSUME `(Q:A->bool) x`) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:A#A->bool` STRIP_ASSUME_TAC) THEN
    ANTE_RES_THEN ASSUME_TAC (ASSUME `(P:(A#A->bool)->bool) m`) THEN
    MP_TAC(SPECL [`l:A#A->bool`; `m:A#A->bool`] ORDINAL_CHAINED) THEN
    ASM_REWRITE_TAC[UNIONS_PRED] THEN BETA_TAC THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [EXISTS_TAC `l:A#A->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET_FL THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `m:A#A->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `b:A`] o REWRITE_RULE[inseg]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      IMP_RES_THEN (MP_TAC o SPEC `b:A`) INSEG_SUBSET_FL THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(CONJUNCT1(REWRITE_RULE[ordinal]
        (ASSUME `ordinal(m:A#A->bool)`))) THEN
      DISCH_THEN(MP_TAC o SPECL [`b:A`; `x:A`] o MATCH_MP WOSET_TOTAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[fl] THEN
      EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN REWRITE_TAC[UNION_FL] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:A#A->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ASSUME `!l:A#A->bool. P l ==> ordinal l`) THEN
    DISCH_THEN(IMP_RES_THEN MP_TAC) THEN REWRITE_TAC[ordinal] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    REPEAT AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `y:A` THEN BETA_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC `y:A = x` THEN ASM_REWRITE_TAC[less; UNIONS_PRED] THEN
    BETA_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [EXISTS_TAC `l:A#A->bool` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(X_CHOOSE_THEN `m:A#A->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `ordinal(l:A#A->bool) /\ ordinal(m:A#A->bool)` MP_TAC THENL
       [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(DISJ_CASES_TAC o MATCH_MP ORDINAL_CHAINED)] THENL
       [IMP_RES_THEN MATCH_MP_TAC INSEG_SUBSET THEN ASM_REWRITE_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------ *)
(* Consequently, every type can be wellordered (and by an ordinal).         *)
(* ------------------------------------------------------------------------ *)

let ORDINAL_UNION_LEMMA = prove
 (`!(l:A#A->bool) x. ordinal l ==> fl(l) x ==> fl(UNIONS(ordinal)) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_FL] THEN
  EXISTS_TAC `l:A#A->bool` THEN ASM_REWRITE_TAC[]);;

let ORDINAL_UP = prove
 (`!l:A#A->bool. ordinal(l) ==> (!x. fl(l) x) \/
                          (?m x. ordinal(m) /\ fl(m) x /\ ~fl(l) x)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT `a \/ b <=> ~a ==> b`] THEN
  GEN_REWRITE_TAC LAND_CONV [NOT_FORALL_THM] THEN DISCH_TAC THEN
  MP_TAC(SPEC `l:A#A->bool` ORDINAL_SUC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC
   [`\(x,y). l(x,y) \/ (y = @y:A. ~fl l y) /\ (fl(l) x \/ (x = @y. ~fl l y))`;
    `@y. ~fl(l:A#A->bool) y`] THEN
  ASM_REWRITE_TAC[FL_SUC] THEN
  CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]);;

let WO_ORDINAL = prove
 (`?l:A#A->bool. ordinal(l) /\ !x. fl(l) x`,
  EXISTS_TAC `UNIONS (ordinal:(A#A->bool)->bool)` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC ORDINAL_UNION THEN REWRITE_TAC[];
    DISCH_THEN(DISJ_CASES_TAC o MATCH_MP ORDINAL_UP) THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM(X_CHOOSE_THEN `m:A#A->bool`
     (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
    IMP_RES_THEN (IMP_RES_THEN MP_TAC) ORDINAL_UNION_LEMMA THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------ *)
(* At least -- every set can be wellordered.                                *)
(* ------------------------------------------------------------------------ *)

let FL_RESTRICT = prove
 (`!l. woset l ==>
       !P. fl(\(x:A,y). P x /\ P y /\ l(x,y)) x <=> P x /\ fl(l) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fl] THEN PBETA_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
  IMP_RES_THEN MATCH_MP_TAC WOSET_REFL THEN
  REWRITE_TAC[fl] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]);;

let WO = prove
 (`!P. ?l:A#A->bool. woset l /\ (fl(l) = P)`,
  GEN_TAC THEN X_CHOOSE_THEN `l:A#A->bool` STRIP_ASSUME_TAC
   (REWRITE_RULE[ordinal] WO_ORDINAL) THEN
  EXISTS_TAC `\(x:A,y). P x /\ P y /\ l(x,y)` THEN REWRITE_TAC[WOSET] THEN
  PBETA_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FL_RESTRICT th]) THEN
  PBETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WOSET_ANTISYM) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `Q:A->bool` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WOSET_WELL) THEN
    DISCH_THEN(MP_TAC o SPEC `Q:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Moreover, the ordinals themselves are wellordered by "inseg".             *)
(* ------------------------------------------------------------------------- *)

let WF_INSEG_WOSET = prove
 (`WF(\(x:A#A->bool) y. woset x /\ woset y /\ x inseg y /\ ~(x = y))`,
  REWRITE_TAC[WF] THEN X_GEN_TAC `P:(A#A->bool)->bool` THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(?x. P x) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [NOT_FORALL_THM] THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x:A#A->bool. P x ==> woset x` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. ?(a:A) z. P y ==> P z /\ fl y a /\ linseg y a = z`
  MP_TAC THENL
   [X_GEN_TAC `y:A#A->bool` THEN
    ASM_CASES_TAC `(P:(A#A->bool)->bool) y` THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:A#A->bool`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INSEG_LINSEG];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:(A#A->bool)->A`; `l:(A#A->bool)->(A#A->bool)`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `z:A#A->bool`) THEN
  SUBGOAL_THEN `woset(z:A#A->bool)` MP_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[woset]] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `{(a:(A#A->bool)->A) x | P x /\ x inseg z}`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[TAUT `P /\ x = y <=> x = y /\ P`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM; SWAP_FORALL_THM] THEN
  REWRITE_TAC[UNWIND_THM2; FORALL_UNWIND_THM2; IMP_CONJ;
              RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM; SWAP_FORALL_THM] THEN
  REWRITE_TAC[UNWIND_THM2; FORALL_UNWIND_THM2; IMP_CONJ;
              RIGHT_FORALL_IMP_THM; NOT_IMP] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INSEG_SUBSET_FL]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INSEG_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A#A->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `(l:(A#A->bool)->(A#A->bool)) w`) THEN
  ASM_SIMP_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LINSEG_INSEG; INSEG_TRANS]; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th ->
   MP_TAC(SPEC `(l:(A#A->bool)->(A#A->bool)) w` th) THEN
   MP_TAC(SPEC `w:A#A->bool` th)) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `fl ((l:(A#A->bool)->(A#A->bool)) w) (a (l w))` THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
  ASM_SIMP_TAC[LINSEG_FL; less] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[inseg]) THEN ASM_MESON_TAC[]);;

let WOSET_INSEG_ORDINAL = prove
 (`woset (\(x:A#A->bool,y). ordinal x /\ ordinal y /\ x inseg y)`,
  REWRITE_TAC[WOSET_WF; fl] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[ORDINAL_CHAINED]] THEN
  MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] WF_SUBSET)
        WF_INSEG_WOSET) THEN
  SIMP_TAC[ordinal]);;

(* ======================================================================== *)
(* (3) CANTOR-ZERMELO WELL-ORDERING THEOREM ==> HAUSDORFF MAXIMAL PRINCIPLE *)
(* ======================================================================== *)

let HP = prove
 (`!l:A#A->bool. poset l ==>
        ?P. chain(l) P /\ !Q. chain(l) Q  /\ P SUBSET Q ==> (Q = P)`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `w:A#A->bool` MP_TAC (SPEC `\x:A. T` WO) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN BETA_TAC THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  IMP_RES_THEN (MP_TAC o SPEC `\x:A. fl(l) x`) WOSET_WELL THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `?x:A. fl(l) x` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC);
    FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    EXISTS_TAC `\x:A. F` THEN REWRITE_TAC[chain; SUBSET_PRED] THEN
    GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:A` MP_TAC o
      GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`u:A`; `u:A`]) THEN
    IMP_RES_THEN(ASSUME_TAC o GSYM) POSET_FLEQ THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `?f. !x. f x = if fl(l) x /\
                                 (!y. less w (y,x) ==> l (x,f y) \/ l (f y,x))
                              then (x:A) else b`
  (CHOOSE_TAC o GSYM) THENL
   [SUBGOAL_THEN `WF(\x:A y. (less w)(x,y))` MP_TAC THENL
     [REWRITE_TAC[WF] THEN GEN_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC_ALL o MATCH_MP WOSET_WELL) THEN
      ASM_REWRITE_TAC[less] THEN ASM_MESON_TAC[WOSET_ANTISYM];
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP WF_REC) THEN
      REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]]; ALL_TAC] THEN
  IMP_RES_THEN(IMP_RES_THEN ASSUME_TAC) POSET_REFL THEN
  SUBGOAL_THEN `(f:A->A) b = b` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `b:A`) THEN
    REWRITE_TAC[COND_ID] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. fl(l:A#A->bool) (f x)` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:A`) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ANTE_RES_THEN (ASSUME_TAC o GEN_ALL) o SPEC_ALL) THEN
  SUBGOAL_THEN `!x:A. (l:A#A->bool)(b,f x) \/ l(f x,b)` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `x:A` (ASSUME `!x:A. (w:A#A->bool)(b,f x)`)) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:A`) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x:A = b` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(less w)(b:A,x)` MP_TAC THENL
     [ASM_REWRITE_TAC[less] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th o CONJUNCT2)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. l((f:A->A) x,f y) \/ l(f y,f x)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    IMP_RES_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) WOSET_TOTAL_LT THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
     [ASM_REWRITE_TAC[] THEN IMP_RES_THEN MATCH_MP_TAC POSET_REFL;
      ONCE_REWRITE_TAC[DISJ_SYM] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `y:A`);
      FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:A`)] THEN
    TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(IMP_RES_THEN ACCEPT_TAC o CONJUNCT2); ALL_TAC] THEN
  EXISTS_TAC `\y:A. ?x:A. y = f(x)` THEN
  SUBGOAL_THEN `chain(l:A#A->bool)(\y. ?x:A. y = f x)` ASSUME_TAC THENL
   [REWRITE_TAC[chain] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN(CHOOSE_THEN SUBST1_TAC)); ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [DISCH_TAC THEN BETA_TAC THEN EXISTS_TAC `z:A` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `z:A`) THEN
    SUBGOAL_THEN `fl(l:A#A->bool) z /\
                  !y. (less w)(y,z) ==> l(z,f y) \/ l(f y,z)`
    (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [UNDISCH_TAC `chain(l:A#A->bool) Q` THEN REWRITE_TAC[chain] THEN
      DISCH_THEN(MP_TAC o SPECL [`z:A`; `z:A`]) THEN ASM_REWRITE_TAC[fl] THEN
      DISCH_TAC THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      UNDISCH_TAC `chain(l:A#A->bool) Q` THEN REWRITE_TAC[chain] THEN
      DISCH_THEN(MP_TAC o SPECL [`z:A`; `(f:A->A) y`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET_PRED]) THEN
      BETA_TAC THEN EXISTS_TAC `y:A` THEN REFL_TAC];
    SPEC_TAC(`z:A`,`z:A`) THEN ASM_REWRITE_TAC[GSYM SUBSET_PRED]]);;

(* ======================================================================== *)
(* (4) HAUSDORFF MAXIMAL PRINCIPLE ==> ZORN'S LEMMA                         *)
(* ======================================================================== *)

let ZL = prove
 (`!l:A#A->bool. poset l /\
           (!P. chain(l) P ==> (?y. fl(l) y /\ !x. P x ==> l(x,y))) ==>
        ?y. fl(l) y /\ !x. l(y,x) ==> (y = x)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `M:A->bool` STRIP_ASSUME_TAC o MATCH_MP HP) THEN
  UNDISCH_TAC `!P. chain(l:A#A->bool) P
                   ==> (?y. fl(l) y /\ !x. P x ==> l(x,y))` THEN
  DISCH_THEN(MP_TAC o SPEC `M:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN
  DISCH_TAC THEN GEN_REWRITE_TAC I [TAUT `a <=> ~ ~a`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `chain(l) (\x:A. M x \/ (x = z))` MP_TAC THENL
   [REWRITE_TAC[chain] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN DISJ_CASES_TAC) THEN
    ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `chain(l:A#A->bool) M` THEN REWRITE_TAC[chain] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
      EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISJ2_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_TRANS) THEN
      EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP POSET_REFL) THEN
      REWRITE_TAC[fl] THEN EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `M SUBSET (\x:A. M x \/ (x = z))` MP_TAC THENL
   [REWRITE_TAC[SUBSET_PRED] THEN GEN_TAC THEN BETA_TAC THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `(a ==> b ==> c) <=> (b /\ a ==> c)`] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `z:A`) THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`m:A`; `z:A`] o MATCH_MP POSET_ANTISYM) THEN
  ASM_REWRITE_TAC[]);;

(* ======================================================================== *)
(* (5) ZORN'S LEMMA ==> KURATOWSKI'S LEMMA                                  *)
(* ======================================================================== *)

let KL_POSET_LEMMA = prove
 (`poset (\(c1,c2). C SUBSET c1 /\ c1 SUBSET c2 /\ chain(l:A#A->bool) c2)`,
  REWRITE_TAC[poset] THEN PBETA_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN REWRITE_TAC[fl] THEN PBETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `Q:A->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THENL
     [MATCH_MP_TAC CHAIN_SUBSET; MATCH_MP_TAC SUBSET_TRANS];
    GEN_TAC THEN X_GEN_TAC `Q:A->bool` THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM] THEN
  TRY(EXISTS_TAC `Q:A->bool`) THEN ASM_REWRITE_TAC[]);;

let KL = prove
 (`!l:A#A->bool. poset l ==>
        !C. chain(l) C ==>
            ?P. (chain(l) P /\ C SUBSET P) /\
                (!R. chain(l) R /\ P SUBSET R ==> (R = P))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\(c1,c2). C SUBSET c1 /\ c1 SUBSET c2 /\
                          chain(l:A#A->bool) c2` ZL) THEN PBETA_TAC THEN
  REWRITE_TAC[KL_POSET_LEMMA; MATCH_MP POSET_FLEQ KL_POSET_LEMMA] THEN
  PBETA_TAC THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
  funpow 2 (fst o dest_imp) o snd) THENL
   [X_GEN_TAC `P:(A->bool)->bool` THEN GEN_REWRITE_TAC LAND_CONV [chain] THEN
    PBETA_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `?D:A->bool. P D` THENL
     [EXISTS_TAC `UNIONS(P) :A->bool` THEN REWRITE_TAC[SUBSET_REFL] THEN
      FIRST_ASSUM(X_CHOOSE_TAC `D:A->bool`) THEN
      FIRST_ASSUM(MP_TAC o SPECL [`D:A->bool`; `D:A->bool`]) THEN
      REWRITE_TAC[ASSUME `(P:(A->bool)->bool) D`; SUBSET_REFL] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c) ==> (a /\ b) /\ c`) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[UNIONS_PRED; SUBSET_PRED] THEN REPEAT STRIP_TAC THEN
        BETA_TAC THEN EXISTS_TAC `D:A->bool` THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET_PRED]) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[chain; UNIONS_PRED] THEN
        MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
        BETA_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
         (X_CHOOSE_TAC `A:A->bool`) (X_CHOOSE_TAC `B:A->bool`)) THEN
        FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
        DISCH_THEN(MP_TAC o SPECL [`A:A->bool`; `B:A->bool`]) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
         [UNDISCH_TAC `chain(l:A#A->bool) B`;
          UNDISCH_TAC `chain(l:A#A->bool) A`] THEN
        REWRITE_TAC[chain] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET_PRED]) THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC THEN X_GEN_TAC `X:A->bool` THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o SPECL [`X:A->bool`; `X:A->bool`]) THEN
        REWRITE_TAC[] THEN DISCH_THEN(IMP_RES_THEN STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_PRED; SUBSET_PRED] THEN
        REPEAT STRIP_TAC THEN BETA_TAC THEN EXISTS_TAC `X:A->bool` THEN
        ASM_REWRITE_TAC[]];
      EXISTS_TAC `C:A->bool` THEN
      FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[SUBSET_REFL]];
    DISCH_THEN(X_CHOOSE_THEN `D:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `D:A->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Special case of Zorn's Lemma for restriction of subset lattice.           *)
(* ------------------------------------------------------------------------- *)

let POSET_RESTRICTED_SUBSET = prove
 (`!P. poset(\(x,y). P(x) /\ P(y) /\ x SUBSET y)`,
  GEN_TAC THEN REWRITE_TAC[poset; fl] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[SUBSET; EXTENSION] THEN MESON_TAC[]);;

let FL_RESTRICTED_SUBSET = prove
 (`!P. fl(\(x,y). P(x) /\ P(y) /\ x SUBSET y) = P`,
  REWRITE_TAC[fl; FORALL_PAIR_THM; FUN_EQ_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[SUBSET_REFL]);;

let ZL_SUBSETS = prove
 (`!P. (!c. (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> ?z. P z /\ (!x. x IN c ==> x SUBSET z))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))`,
  GEN_TAC THEN
  MP_TAC(ISPEC `\(x,y). P(x:A->bool) /\ P(y) /\ x SUBSET y` ZL) THEN
  REWRITE_TAC[POSET_RESTRICTED_SUBSET; FL_RESTRICTED_SUBSET] THEN
  REWRITE_TAC[chain] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[IN] THEN MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
   [MATCH_MP_TAC MONO_FORALL; ALL_TAC] THEN
  MESON_TAC[]);;

let ZL_SUBSETS_UNIONS = prove
 (`!P. (!c. (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> P(UNIONS c))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ZL_SUBSETS THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `UNIONS(c:(A->bool)->bool)` THEN
  ASM_MESON_TAC[SUBSET; IN_UNIONS]);;

let ZL_SUBSETS_UNIONS_NONEMPTY = prove
 (`!P. (?x. P x) /\
       (!c. (?x. x IN c) /\
            (!x. x IN c ==> P x) /\
            (!x y. x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x)
            ==> P(UNIONS c))
       ==> ?a:A->bool. P a /\ (!x. P x /\ a SUBSET x ==> (a = x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ZL_SUBSETS THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `?x:A->bool. x IN c` THENL
   [EXISTS_TAC `UNIONS(c:(A->bool)->bool)` THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[SUBSET; IN_UNIONS];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A form of Tukey's lemma.                                                  *)
(* ------------------------------------------------------------------------- *)

let TUKEY = prove
 (`!s:(A->bool)->bool.
        ~(s = {}) /\
        (!t. (!c. FINITE c /\ c SUBSET t ==> c IN s) <=> t IN s)
        ==> ?u. u IN s /\ !v. v IN s /\ u SUBSET v ==> u = v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ZL_SUBSETS_UNIONS_NONEMPTY THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)->bool` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
  SUBGOAL_THEN
   `!d. FINITE d ==> d SUBSET UNIONS c ==> ?e:A->bool. e IN c /\ d SUBSET e`
  MP_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_FORALL THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INSERT_SUBSET] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Also the order extension theorem, using Abian's proof.                    *)
(* ------------------------------------------------------------------------- *)

let OEP = prove
 (`!p:A#A->bool. poset p ==> ?t. toset t /\ fl(t) = fl(p) /\ p SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `fl(p:A#A->bool)` WO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A#A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `t = \(x:A,y:A). fl p x /\ fl p y /\
                    (x = y \/
                     ?i. fl p i /\
                         (!j. w(j,i) /\ ~(j = i) ==> (p(j,x) <=> p(j,y))) /\
                         ~p(i,x) /\ p(i,y))` THEN
  EXISTS_TAC `t:A#A->bool` THEN
  SUBGOAL_THEN
   `!x:A y:A. fl p x /\ fl p y /\ ~(x = y)
              ==> ?i. fl p i /\
                      (!j:A. w(j,i) /\ ~(j = i) ==> (p(j,x) <=> p(j,y))) /\
                      ~(p(i,x) <=> p(i,y))`
  (LABEL_TAC "*") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN ASM_SIMP_TAC[] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPEC `\i:A. fl p i /\ ~(p(i,x) <=> p(i,y))`) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [poset]) THEN ASM_MESON_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:A` THEN
       ASM_MESON_TAC[fl]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A y:A. p(x,y) ==> t(x,y)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[fl]; ALL_TAC]) THEN
    ASM_CASES_TAC `x:A = y` THENL [ASM_MESON_TAC[fl]; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`x:A`; `y:A`]) THEN ASM_SIMP_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[fl]; MATCH_MP_TAC MONO_EXISTS] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [poset]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[fl] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[toset; poset]] THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [poset]) THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `z:A`] THEN
    ASM_CASES_TAC `x:A = z` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN
    ASM_CASES_TAC `y:A = z` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN
    ASM_CASES_TAC `y:A = x` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN
    ASM_CASES_TAC `fl p (x:A)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `fl p (y:A)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `fl p (z:A)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `n:A` STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN
    REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPECL [`m:A`; `n:A`] o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[fl]; ALL_TAC] THEN STRIP_TAC THENL
     [EXISTS_TAC `m:A`; EXISTS_TAC `n:A`] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    ASM_CASES_TAC `y:A = x` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `fl p (x:A)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `fl p (y:A)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `n:A` STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [woset]) THEN
    REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPECL [`m:A`; `n:A`] o CONJUNCT1) THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    ASM_CASES_TAC `y:A = x` THEN ASM_REWRITE_TAC[IN] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_REWRITE_TAC[OR_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    MESON_TAC[]]);;
