(* ========================================================================= *)
(* Axiomatic of the modal provability logic GL.                              *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2021.              *)
(*                                                                           *)
(* The initial part of this code has been adapted from the proof of the      *)
(* Godel incompleteness theorems formalized by John Harrison, distributed    *)
(* with HOL Light in the subdirectory Arithmetic.                            *)
(* ========================================================================= *)

let GLaxiom_RULES,GLaxiom_INDUCT,GLaxiom_CASES = new_inductive_definition
  `(!p q. GLaxiom (p --> (q --> p))) /\
   (!p q r. GLaxiom ((p --> q --> r) --> (p --> q) --> (p --> r))) /\
   (!p. GLaxiom (((p --> False) --> False) --> p)) /\
   (!p q. GLaxiom ((p <-> q) --> p --> q)) /\
   (!p q. GLaxiom ((p <-> q) --> q --> p)) /\
   (!p q. GLaxiom ((p --> q) --> (q --> p) --> (p <-> q))) /\
   GLaxiom (True <-> False --> False) /\
   (!p. GLaxiom (Not p <-> p --> False)) /\
   (!p q. GLaxiom (p && q <-> (p --> q --> False) --> False)) /\
   (!p q. GLaxiom (p || q <-> Not(Not p && Not q))) /\
   (!p q. GLaxiom (Box (p --> q) --> Box p --> Box q)) /\
   (!p. GLaxiom (Box (Box p --> p) --> Box p))`;;

(* ------------------------------------------------------------------------- *)
(* Rules.                                                                    *)
(* ------------------------------------------------------------------------- *)

let GLproves_RULES,GLproves_INDUCT,GLproves_CASES = new_inductive_definition
  `(!p. GLaxiom p ==> |-- p) /\
   (!p q. |-- (p --> q) /\ |-- p ==> |-- q) /\
   (!p. |-- p ==> |-- (Box p))`;;

(* ------------------------------------------------------------------------- *)
(* The primitive basis, separated into its named components.                 *)
(* ------------------------------------------------------------------------- *)

let GL_axiom_addimp = prove
 (`!p q. |-- (p --> (q --> p))`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_distribimp = prove
 (`!p q r. |-- ((p --> q --> r) --> (p --> q) --> (p --> r))`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_doubleneg = prove
 (`!p. |-- (((p --> False) --> False) --> p)`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_iffimp1 = prove
 (`!p q. |-- ((p <-> q) --> p --> q)`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_iffimp2 = prove
 (`!p q. |-- ((p <-> q) --> q --> p)`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_impiff = prove
 (`!p q. |-- ((p --> q) --> (q --> p) --> (p <-> q))`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_true = prove
 (`|-- (True <-> (False --> False))`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_not = prove
 (`!p. |-- (Not p <-> (p --> False))`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_and = prove
 (`!p q. |-- ((p && q) <-> (p --> q --> False) --> False)`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_or = prove
 (`!p q. |-- ((p || q) <-> Not(Not p && Not q))`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_boximp = prove
 (`!p q. |-- (Box (p --> q) --> Box p --> Box q)`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_axiom_lob = prove
 (`!p. |-- (Box (Box p --> p) --> Box p)`,
  MESON_TAC[GLproves_RULES; GLaxiom_RULES]);;

let GL_modusponens = prove
 (`!p. |-- (p --> q) /\ |-- p ==> |-- q`,
  MESON_TAC[GLproves_RULES]);;

let GL_necessitation = prove
 (`!p. |-- p ==> |-- (Box p)`,
  MESON_TAC[GLproves_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. transitive noetherian frames.                   *)
(* ------------------------------------------------------------------------- *)

let LOB_IMP_TRANSNT = prove
 (`!W R. (!x y:W. R x y ==> x IN W /\ y IN W) /\
         (!p. holds_in (W,R) (Box(Box p --> p) --> Box p))
         ==> (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z) /\
             WF (\x y. R y x)`,
  MODAL_SCHEMA_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [X_GEN_TAC `w:W` THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`\v:W. v IN W /\ R w v /\ !w''. w'' IN W /\ R v w'' ==> R w w''`;
      `w:W`]) THEN
   MESON_TAC[];
   REWRITE_TAC[WF_IND] THEN X_GEN_TAC `P:W->bool` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `\x:W. !w:W. x IN W /\ R w x ==> P x`) THEN
   MATCH_MP_TAC MONO_FORALL THEN ASM_MESON_TAC[]]);;

let TRANSNT_IMP_LOB = prove
 (`!W R. (!x y:W. R x y ==> x IN W /\ y IN W) /\
         (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z) /\
         WF (\x y. R y x)
         ==> (!p. holds_in (W,R) (Box(Box p --> p) --> Box p))`,
  MODAL_SCHEMA_TAC THEN REWRITE_TAC[WF_IND] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let TRANSNT_EQ_LOB = prove
 (`!W R. (!x y:W. R x y ==> x IN W /\ y IN W)
         ==> ((!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z
                       ==> R x z) /\
              WF (\x y. R y x) <=>
              (!p. holds_in (W,R) (Box(Box p --> p) --> Box p)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [MATCH_MP_TAC TRANSNT_IMP_LOB THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC LOB_IMP_TRANSNT THEN ASM_REWRITE_TAC[]]);;

let GLAXIOMS_TRANSNT_VALID = prove
 (`!p. GLaxiom p ==> TRANSNT:(W->bool)#(W->W->bool)->bool |= p`,
  MATCH_MP_TAC GLaxiom_INDUCT THEN REWRITE_TAC[valid] THEN FIX_TAC "f" THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  SPEC_TAC (`f:(W->bool)#(W->W->bool)`,`f:(W->bool)#(W->W->bool)`) THEN
  MATCH_MP_TAC (MESON[PAIR_SURJECTIVE]
    `(!W:W->bool R:W->W->bool. P (W,R)) ==> (!f. P f)`) THEN
  REWRITE_TAC[TRANSNT] THEN REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  TRY (STRIP_TAC THEN MATCH_MP_TAC TRANSNT_IMP_LOB THEN
       ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MODAL_TAC);;

let GL_TRANSNT_VALID = prove
 (`!p. (|-- p) ==> TRANSNT:(W->bool)#(W->W->bool)->bool |= p`,
  MATCH_MP_TAC GLproves_INDUCT THEN REWRITE_TAC[GLAXIOMS_TRANSNT_VALID] THEN
  MODAL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Proof of soundness w.r.t. ITF                                             *)
(* ------------------------------------------------------------------------- *)

let ITF = new_definition
  `ITF (W:W->bool,R:W->W->bool) <=>
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> ~R x x) /\
   (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)`;;

let ITF_NT = prove
 (`!W R:W->W->bool. ITF(W,R) ==> TRANSNT(W,R)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ITF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[TRANSNT] THEN MATCH_MP_TAC WF_FINITE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `W:W->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let GL_ITF_VALID = prove
 (`!p. |-- p ==> ITF:(W->bool)#(W->W->bool)->bool |= p`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `TRANSNT:(W->bool)#(W->W->bool)->bool |= p` MP_TAC THENL
  [ASM_SIMP_TAC[GL_TRANSNT_VALID];
   REWRITE_TAC[valid; FORALL_PAIR_THM] THEN MESON_TAC[ITF_NT]]);;

let GL_consistent = prove
 (`~ |-- False`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] GL_ITF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              ITF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some purely propositional schemas and derived rules.                      *)
(* ------------------------------------------------------------------------- *)

let GL_iff_imp1 = prove
 (`!p q. |-- (p <-> q) ==> |-- (p --> q)`,
  MESON_TAC[GL_modusponens; GL_axiom_iffimp1]);;

let GL_iff_imp2 = prove
 (`!p q. |-- (p <-> q) ==> |-- (q --> p)`,
  MESON_TAC[GL_modusponens; GL_axiom_iffimp2]);;

let GL_imp_antisym = prove
 (`!p q. |-- (p --> q) /\ |-- (q --> p) ==> |-- (p <-> q)`,
  MESON_TAC[GL_modusponens; GL_axiom_impiff]);;

let GL_add_assum = prove
 (`!p q. |-- q ==> |-- (p --> q)`,
  MESON_TAC[GL_modusponens; GL_axiom_addimp]);;

let GL_imp_refl_th = prove
 (`!p. |-- (p --> p)`,
  MESON_TAC[GL_modusponens; GL_axiom_distribimp; GL_axiom_addimp]);;

let GL_imp_add_assum = prove
 (`!p q r. |-- (q --> r) ==> |-- ((p --> q) --> (p --> r))`,
  MESON_TAC[GL_modusponens; GL_axiom_distribimp; GL_add_assum]);;

let GL_imp_unduplicate = prove
 (`!p q. |-- (p --> p --> q) ==> |-- (p --> q)`,
  MESON_TAC[GL_modusponens; GL_axiom_distribimp; GL_imp_refl_th]);;

let GL_imp_trans = prove
 (`!p q. |-- (p --> q) /\ |-- (q --> r) ==> |-- (p --> r)`,
  MESON_TAC[GL_modusponens; GL_imp_add_assum]);;

let GL_imp_swap = prove
 (`!p q r. |-- (p --> q --> r) ==> |-- (q --> p --> r)`,
  MESON_TAC[GL_imp_trans; GL_axiom_addimp; GL_modusponens;
            GL_axiom_distribimp]);;

let GL_imp_trans_chain_2 = prove
 (`!p q1 q2 r. |-- (p --> q1) /\ |-- (p --> q2) /\ |-- (q1 --> q2 --> r)
               ==> |-- (p --> r)`,
  ASM_MESON_TAC[GL_imp_trans; GL_imp_swap; GL_imp_unduplicate]);;

let GL_imp_trans_th = prove
 (`!p q r. |-- ((q --> r) --> (p --> q) --> (p --> r))`,
  MESON_TAC[GL_imp_trans; GL_axiom_addimp; GL_axiom_distribimp]);;

let GLimp_add_concl = prove
 (`!p q r. |-- (p --> q) ==> |-- ((q --> r) --> (p --> r))`,
  MESON_TAC[GL_modusponens; GL_imp_swap; GL_imp_trans_th]);;

let GL_imp_trans2 = prove
 (`!p q r s. |-- (p --> q --> r) /\ |-- (r --> s) ==> |-- (p --> q --> s)`,
  MESON_TAC[GL_imp_add_assum; GL_modusponens; GL_imp_trans_th]);;

let GL_imp_swap_th = prove
 (`!p q r. |-- ((p --> q --> r) --> (q --> p --> r))`,
  MESON_TAC[GL_imp_trans; GL_axiom_distribimp; GLimp_add_concl;
            GL_axiom_addimp]);;

let GL_contrapos = prove
 (`!p q. |-- (p --> q) ==> |-- (Not q --> Not p)`,
  MESON_TAC[GL_imp_trans; GL_iff_imp1; GL_axiom_not;
            GLimp_add_concl; GL_iff_imp2]);;

let GL_imp_truefalse_th = prove
 (`!p q. |-- ((q --> False) --> p --> (p --> q) --> False)`,
  MESON_TAC[GL_imp_trans; GL_imp_trans_th; GL_imp_swap_th]);;

let GL_imp_insert = prove
 (`!p q r. |-- (p --> r) ==> |-- (p --> q --> r)`,
  MESON_TAC[GL_imp_trans; GL_axiom_addimp]);;

let GL_imp_mono_th = prove
 (`|-- ((p' --> p) --> (q --> q') --> (p --> q) --> (p' --> q'))`,
  MESON_TAC[GL_imp_trans; GL_imp_swap; GL_imp_trans_th]);;

let GL_ex_falso_th = prove
 (`!p. |-- (False --> p)`,
  MESON_TAC[GL_imp_trans; GL_axiom_addimp; GL_axiom_doubleneg]);;

let GL_ex_falso = prove
 (`!p. |-- False ==> |-- p`,
  MESON_TAC[GL_ex_falso_th; GL_modusponens]);;

let GL_imp_contr_th = prove
 (`!p q. |-- ((p --> False) --> (p --> q))`,
  MESON_TAC[GL_imp_add_assum; GL_ex_falso_th]);;

let GL_contrad = prove
 (`!p. |-- ((p --> False) --> p) ==> |-- p`,
  MESON_TAC[GL_modusponens; GL_axiom_distribimp;
            GL_imp_refl_th; GL_axiom_doubleneg]);;

let GL_bool_cases = prove
 (`!p q. |-- (p --> q) /\ |-- ((p --> False) --> q) ==> |-- q`,
  MESON_TAC[GL_contrad; GL_imp_trans; GLimp_add_concl]);;

let GL_imp_false_rule = prove
 (`!p q r. |-- ((q --> False) --> p --> r)
           ==> |-- (((p --> q) --> False) --> r)`,
  MESON_TAC[GLimp_add_concl; GL_imp_add_assum; GL_ex_falso_th;
            GL_axiom_addimp; GL_imp_swap; GL_imp_trans;
            GL_axiom_doubleneg; GL_imp_unduplicate]);;

let GL_imp_true_rule = prove
 (`!p q r. |-- ((p --> False) --> r) /\ |-- (q --> r)
           ==> |-- ((p --> q) --> r)`,
  MESON_TAC[GL_imp_insert; GL_imp_swap; GL_modusponens;
            GL_imp_trans_th; GL_bool_cases]);;

let GL_truth_th = prove
 (`|-- True`,
  MESON_TAC[GL_modusponens; GL_axiom_true; GL_imp_refl_th; GL_iff_imp2]);;

let GL_and_left_th = prove
 (`!p q. |-- (p && q --> p)`,
  MESON_TAC[GL_imp_add_assum; GL_axiom_addimp; GL_imp_trans; GLimp_add_concl;
            GL_axiom_doubleneg; GL_imp_trans; GL_iff_imp1; GL_axiom_and]);;

let GL_and_right_th = prove
 (`!p q. |-- (p && q --> q)`,
  MESON_TAC[GL_axiom_addimp; GL_imp_trans; GLimp_add_concl; GL_axiom_doubleneg;
            GL_iff_imp1; GL_axiom_and]);;

let GL_and_pair_th = prove
 (`!p q. |-- (p --> q --> p && q)`,
  MESON_TAC[GL_iff_imp2; GL_axiom_and; GL_imp_swap_th; GL_imp_add_assum;
            GL_imp_trans2; GL_modusponens; GL_imp_swap; GL_imp_refl_th]);;

let GL_and = prove
 (`!p q. |-- (p && q) <=> |-- p /\ |-- q`,
  MESON_TAC[GL_and_left_th; GL_and_right_th; GL_and_pair_th; GL_modusponens]);;

let GL_and_elim = prove
 (`!p q r. |-- (r --> p && q) ==> |-- (r --> q)  /\ |-- (r --> p)`,
  MESON_TAC[GL_and_left_th; GL_and_right_th; GL_imp_trans]);;

let GL_shunt = prove
 (`!p q r. |-- (p && q --> r) ==> |-- (p --> q --> r)`,
  MESON_TAC[GL_modusponens; GL_imp_add_assum; GL_and_pair_th]);;

let GL_ante_conj = prove
 (`!p q r. |-- (p --> q --> r) ==> |-- (p && q --> r)`,
  MESON_TAC[GL_imp_trans_chain_2; GL_and_left_th; GL_and_right_th]);;

let GL_modusponens_th = prove
 (`!p q. |-- ((p --> q) && p --> q)`,
  MESON_TAC[GL_imp_refl_th; GL_ante_conj]);;

let GL_not_not_false_th = prove
 (`!p. |-- ((p --> False) --> False <-> p)`,
  MESON_TAC[GL_imp_antisym; GL_axiom_doubleneg; GL_imp_swap; GL_imp_refl_th]);;

let GL_iff_sym = prove
 (`!p q. |-- (p <-> q) <=> |-- (q <-> p)`,
  MESON_TAC[GL_iff_imp1; GL_iff_imp2; GL_imp_antisym]);;

let GL_iff_trans = prove
 (`!p q r. |-- (p <-> q) /\ |-- (q <-> r) ==> |-- (p <-> r)`,
  MESON_TAC[GL_iff_imp1; GL_iff_imp2; GL_imp_trans; GL_imp_antisym]);;

let GL_not_not_th = prove
 (`!p. |-- (Not (Not p) <-> p)`,
  MESON_TAC[GL_iff_trans; GL_not_not_false_th; GL_axiom_not;
            GL_imp_antisym; GLimp_add_concl; GL_iff_imp1; GL_iff_imp2]);;

let GL_contrapos_eq = prove
 (`!p q. |-- (Not p --> Not q) <=> |-- (q --> p)`,
  MESON_TAC[GL_contrapos; GL_not_not_th; GL_iff_imp1;
            GL_iff_imp2; GL_imp_trans]);;

let GL_or_left_th = prove
 (`!p q. |-- (q --> p || q)`,
  MESON_TAC[GL_imp_trans; GL_not_not_th; GL_iff_imp2; GL_and_right_th;
            GL_contrapos; GL_axiom_or]);;

let GL_or_right_th = prove
 (`!p q. |-- (p --> p || q)`,
  MESON_TAC[GL_imp_trans; GL_not_not_th; GL_iff_imp2; GL_and_left_th;
            GL_contrapos; GL_axiom_or]);;

let GL_ante_disj = prove
 (`!p q r. |-- (p --> r) /\ |-- (q --> r)
             ==> |-- (p || q --> r)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM GL_contrapos_eq] THEN
  MESON_TAC[GL_imp_trans; GL_imp_trans_chain_2; GL_and_pair_th;
            GL_contrapos_eq; GL_not_not_th; GL_axiom_or; GL_iff_imp1;
            GL_iff_imp2; GL_imp_trans]);;

let GL_iff_def_th = prove
 (`!p q. |-- ((p <-> q) <-> (p --> q) && (q --> p))`,
  MESON_TAC[GL_imp_antisym; GL_imp_trans_chain_2; GL_axiom_iffimp1;
            GL_axiom_iffimp2; GL_and_pair_th; GL_axiom_impiff;
            GL_imp_trans_chain_2; GL_and_left_th; GL_and_right_th]);;

let GL_iff_refl_th = prove
 (`!p. |-- (p <-> p)`,
  MESON_TAC[GL_imp_antisym; GL_imp_refl_th]);;

let GL_imp_box = prove
 (`!p q. |-- (p --> q) ==> |-- (Box p --> Box q)`,
  MESON_TAC[GL_modusponens; GL_necessitation; GL_axiom_boximp]);;

let GL_box_moduspones = prove
 (`!p q. |-- (p --> q) /\ |-- (Box p) ==> |-- (Box q)`,
  MESON_TAC[GL_imp_box; GL_modusponens]);;

let GL_box_and = prove
 (`!p q. |-- (Box(p && q)) ==> |-- (Box p && Box q)`,
 MESON_TAC[GL_and_left_th; GL_and_right_th; GL_imp_box;
           GL_box_moduspones; GL_and]);;

 let GL_box_and_inv = prove
  (`!p q. |-- (Box p && Box q) ==> |-- (Box (p && q))`,
  MESON_TAC[GL_and_pair_th; GL_imp_box; GL_axiom_boximp;
            GL_imp_trans; GL_ante_conj; GL_modusponens]);;

let GL_and_comm = prove
 (`!p q . |-- (p && q) <=> |-- (q && p)`,
 MESON_TAC[GL_and]);;

let GL_and_assoc = prove
 (`!p q r. |-- ((p && q) && r) <=> |-- (p && (q && r))`,
 MESON_TAC[GL_and]);;

let GL_disj_imp = prove
 (`!p q r. |-- (p || q --> r) <=> |-- (p --> r) /\ |-- (q --> r)`,
  MESON_TAC[GL_ante_disj; GL_or_right_th; GL_or_left_th; GL_imp_trans]);;

let GL_or_elim = prove
 (`!p q r. |-- (p || q) /\ |-- (p --> r) /\ |-- (q --> r) ==> |-- r`,
  MESON_TAC[GL_disj_imp; GL_modusponens]);;

let GL_or_comm = prove
 (`!p q . |-- (p || q) <=> |-- (q || p)`,
  MESON_TAC[GL_or_right_th; GL_or_left_th; GL_modusponens; GL_disj_imp]);;

let GL_or_assoc = prove
 (`!p q r. |-- ((p || q) || r) <=> |-- (p || (q || r))`,
  MESON_TAC[GL_or_right_th; GL_or_left_th; GL_modusponens; GL_disj_imp]);;

let GL_or_intror = prove
 (`!p q. |-- q ==> |-- (p || q)`,
  MESON_TAC[GL_or_left_th; GL_modusponens]);;

let GL_or_introl = prove
 (`!p q. |-- p ==> |-- (p || q)`,
  MESON_TAC[GL_or_right_th; GL_modusponens]);;

let GL_or_transl = prove
 (`!p q r. |-- (p --> q) ==> |-- (p --> q || r)`,
  MESON_TAC[GL_or_right_th; GL_imp_trans]);;

let GL_or_transr = prove
 (`!p q r. |-- (p --> r) ==> |-- (p --> q || r)`,
  MESON_TAC[GL_or_left_th; GL_imp_trans]);;

let GL_frege = prove
 (`!p q r. |-- (p --> q --> r) /\ |-- (p --> q) ==> |-- (p --> r)`,
  MESON_TAC[GL_axiom_distribimp; GL_modusponens; GL_shunt; GL_ante_conj]);;

let GL_and_intro = prove
(`!p q r. |-- (p --> q) /\ |-- (p --> r) ==> |-- (p --> q && r)`,
 MESON_TAC[GL_and_pair_th; GL_imp_trans_chain_2]);;

let GL_not_def = prove
 (`!p. |-- (Not p) <=> |-- (p --> False)`,
   MESON_TAC[GL_axiom_not; GL_modusponens; GL_iff_imp1; GL_iff_imp2]);;

let GL_NC = prove
 (`!p. |-- (p  && Not p) <=> |-- False`,
  MESON_TAC[GL_not_def; GL_modusponens; GL_and; GL_ex_falso]);;

  let GL_nc_th = prove
   (`!p. |-- (p && Not p --> False)`,
    MESON_TAC[GL_ante_conj; GL_imp_swap; GL_axiom_not;
              GL_axiom_iffimp1; GL_modusponens]);;

let GL_imp_clauses = prove
 (`(!p. |-- (p --> True)) /\
   (!p. |-- (p --> False) <=> |-- (Not p)) /\
   (!p. |-- (True --> p) <=> |-- p) /\
   (!p. |-- (False --> p))`,
  SIMP_TAC[GL_truth_th; GL_add_assum; GL_not_def; GL_ex_falso_th] THEN
  GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[GL_modusponens; GL_truth_th];
   MESON_TAC[GL_add_assum]]);;

let GL_and_left_true_th = prove
 (`!p. |-- (True && p <-> p)`,
  GEN_TAC THEN MATCH_MP_TAC GL_imp_antisym THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC GL_and_right_th; ALL_TAC] THEN
  MATCH_MP_TAC GL_and_intro THEN REWRITE_TAC[GL_imp_refl_th; GL_imp_clauses]);;

let GL_or_and_distr = prove
 (`!p q r. |-- ((p || q) && r) ==> |-- ((p && r) || (q && r))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GL_and] THEN STRIP_TAC THEN
  MATCH_MP_TAC GL_or_elim THEN EXISTS_TAC `p:form` THEN
  EXISTS_TAC `q :form` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_or_transl THEN MATCH_MP_TAC GL_and_intro THEN
   REWRITE_TAC[GL_imp_refl_th] THEN ASM_SIMP_TAC[GL_add_assum];
   MATCH_MP_TAC GL_or_transr THEN MATCH_MP_TAC GL_and_intro THEN
   REWRITE_TAC[GL_imp_refl_th] THEN ASM_SIMP_TAC[GL_add_assum]]);;

let GL_and_or_distr = prove
 (`!p q r. |-- ((p && q) || r) ==> |-- ((p || r) && (q || r))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GL_and] THEN DISCH_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC GL_or_elim THEN
  MAP_EVERY EXISTS_TAC [`p && q`; `r:form`] THEN
  ASM_REWRITE_TAC[GL_or_left_th] THEN MATCH_MP_TAC GL_or_transl THEN
  ASM_REWRITE_TAC[GL_and_left_th; GL_and_right_th]);;

let GL_or_and_distr_inv = prove
 (`!p q r. |-- ((p && r) || (q && r)) ==> |-- ((p || q) && r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC GL_or_elim THEN
  MAP_EVERY EXISTS_TAC [`p && r`; `q && r`] THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM (K ALL_TAC) THEN CONJ_TAC THEN MATCH_MP_TAC GL_and_intro THEN
  CONJ_TAC THEN REWRITE_TAC[GL_and_left_th; GL_and_right_th] THENL
  [MATCH_MP_TAC GL_or_transl THEN MATCH_ACCEPT_TAC GL_and_left_th;
   MATCH_MP_TAC GL_or_transr THEN MATCH_ACCEPT_TAC GL_and_left_th]);;

let GL_or_and_distr_equiv = prove
(`!p q r. |-- ((p || q) && r) <=> |-- ((p && r) || (q && r))`,
 MESON_TAC[GL_or_and_distr; GL_or_and_distr_inv]);;

let GL_and_or_distr_inv_prelim = prove
 (`!p q r. |-- ((p || r) && (q || r)) ==> |-- (q --> (p && q) || r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GL_and] THEN INTRO_TAC "pr qr" THEN
  MATCH_MP_TAC (SPECL [`p:form`; `r:form`] GL_or_elim) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "pr" (K ALL_TAC) THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_shunt THEN MATCH_ACCEPT_TAC GL_or_right_th; ALL_TAC] THEN
  MATCH_MP_TAC GL_imp_insert THEN MATCH_ACCEPT_TAC GL_or_left_th);;

let GL_and_or_distr_inv = prove
 (`!p q r. |-- ((p || r) && (q || r)) ==> |-- ((p && q) || r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GL_and] THEN INTRO_TAC "pr qr" THEN
  MATCH_MP_TAC (SPECL [`p:form`; `r:form`] GL_or_elim) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "pr" (K ALL_TAC) THEN
  REWRITE_TAC[GL_or_left_th] THEN
  MATCH_MP_TAC (SPECL [`q:form`; `r:form`] GL_or_elim) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "qr" (K ALL_TAC) THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_imp_swap THEN MATCH_MP_TAC GL_shunt THEN
   MATCH_ACCEPT_TAC GL_or_right_th;
   MATCH_MP_TAC GL_imp_insert THEN MATCH_ACCEPT_TAC GL_or_left_th]);;

let GL_and_or_distr_equiv = prove
 (`!p q r. |-- ((p && q) || r) <=> |-- ((p || r) && (q || r))`,
  MESON_TAC[GL_and_or_distr; GL_and_or_distr_inv]);;

let GL_DOUBLENEG_CL = prove
 (`!p. |-- (Not(Not p)) ==> |-- p`,
 MESON_TAC[GL_not_not_th; GL_modusponens; GL_iff_imp1; GL_iff_imp2]);;

let GL_DOUBLENEG = prove
 (`!p. |-- p ==> |-- (Not(Not p))`,
  MESON_TAC[GL_not_not_th; GL_modusponens; GL_iff_imp1; GL_iff_imp2]);;

let GL_and_eq_or = prove
 (`!p q. |-- (p || q) <=> |-- (Not(Not p && Not q))`,
  MESON_TAC[GL_modusponens; GL_axiom_or; GL_iff_imp1; GL_iff_imp2]);;

let GL_tnd_th = prove
 (`!p. |-- (p || Not p)`,
  GEN_TAC THEN REWRITE_TAC[GL_and_eq_or] THEN
  REWRITE_TAC[GL_not_def] THEN MESON_TAC[GL_nc_th]);;

let GL_iff_mp = prove
 (`!p q. |-- (p <-> q) /\ |-- p ==> |-- q`,
  MESON_TAC[GL_iff_imp1; GL_modusponens]);;

let GL_and_subst = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> (|-- (p && q) <=> |-- (p' && q'))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GL_and] THEN
  ASM_MESON_TAC[GL_iff_mp; GL_iff_sym]);;

let GL_imp_mono_th = prove
 (`!p p' q q'. |-- ((p' --> p) && (q --> q') --> (p --> q) --> (p' --> q'))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_ante_conj THEN
  MATCH_ACCEPT_TAC GL_imp_mono_th);;

let GL_imp_mono = prove
 (`!p p' q q'. |-- (p' --> p) /\ |-- (q --> q')
               ==> |-- ((p --> q) --> (p' --> q'))`,
  REWRITE_TAC[GSYM GL_and] THEN MESON_TAC[GL_modusponens; GL_imp_mono_th]);;

let GL_iff = prove
 (`!p q. |-- (p <-> q) ==> (|-- p <=> |-- q)`,
  MESON_TAC[GL_iff_imp1; GL_iff_imp2; GL_modusponens]);;

let GL_iff_def = prove
 (`!p q. |-- (p <-> q) <=> |-- (p --> q) /\ |-- (q --> p)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[GL_iff_imp1; GL_iff_imp2];
   MATCH_ACCEPT_TAC GL_imp_antisym]);;

let GL_not_subst = prove
 (`!p q. |-- (p <-> q) ==> |-- (Not p <-> Not q)`,
  MESON_TAC[GL_iff_def; GL_iff_imp2; GL_contrapos]);;

let GL_and_rigth_true_th = prove
 (`!p. |-- (p && True <-> p)`,
  GEN_TAC THEN REWRITE_TAC[GL_iff_def] THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC GL_and_left_th; ALL_TAC] THEN
  MATCH_MP_TAC GL_and_intro THEN REWRITE_TAC[GL_imp_refl_th] THEN
  MATCH_MP_TAC GL_add_assum THEN
  MATCH_ACCEPT_TAC GL_truth_th);;

let GL_and_comm_th = prove
 (`!p q. |-- (p && q <-> q && p)`,
  SUBGOAL_THEN `!p q. |-- (p && q --> q && p)`
    (fun th -> MESON_TAC[th; GL_iff_def]) THEN
  MESON_TAC[GL_and_intro; GL_and_left_th; GL_and_right_th]);;

let GL_and_assoc_th = prove
 (`!p q r. |-- ((p && q) && r <-> p && (q && r))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_imp_antisym THEN CONJ_TAC THEN
  MATCH_MP_TAC GL_and_intro THEN
  MESON_TAC[GL_and_left_th; GL_and_right_th; GL_imp_trans; GL_and_intro]);;

let GL_and_subst_th = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> |-- (p && q <-> p' && q')`,
  SUBGOAL_THEN
    `!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
                 ==> |-- (p && q --> p' && q')`
    (fun th -> MESON_TAC[th; GL_iff_def]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GL_and_intro THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `p:form` THEN
   REWRITE_TAC[GL_and_left_th] THEN ASM_SIMP_TAC[GL_iff_imp1];
   MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `q:form` THEN
   REWRITE_TAC[GL_and_right_th] THEN ASM_SIMP_TAC[GL_iff_imp1]]);;

let GL_imp_subst = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> |-- ((p --> q) <-> (p' --> q'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GL_iff_def] THEN
  POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
  SUBGOAL_THEN `!p q p' q'.
                  |-- (p <-> p') /\ |-- (q <-> q')
                  ==> |-- ((p --> q) --> (p' --> q'))`
    (fun th -> MESON_TAC[th; GL_iff_sym]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC GL_imp_mono THEN
  ASM_MESON_TAC[GL_iff_imp1; GL_iff_sym]);;

let GL_de_morgan_and_th = prove
 (`!p q. |-- (Not (p && q) <-> Not p || Not q)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `Not (Not (Not p) && Not (Not q))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_not_subst THEN ONCE_REWRITE_TAC[GL_iff_sym] THEN
   MATCH_MP_TAC GL_and_subst_th THEN CONJ_TAC THEN
   MATCH_ACCEPT_TAC GL_not_not_th;
   ONCE_REWRITE_TAC[GL_iff_sym] THEN MATCH_ACCEPT_TAC GL_axiom_or]);;

let GL_iff_sym_th = prove
 (`!p q. |-- ((p <-> q) <-> (q <-> p))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN ASM_REWRITE_TAC[GL_iff_def_th] THEN
  ONCE_REWRITE_TAC[GL_iff_sym] THEN MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `(q --> p) && (p --> q)` THEN
REWRITE_TAC[GL_iff_def_th; GL_and_comm_th]);;

let GL_iff_true_th = prove
 (`(!p. |-- ((p <-> True) <-> p)) /\
   (!p. |-- ((True <-> p) <-> p))`,
  CLAIM_TAC "1" `!p. |-- ((p <-> True) <-> p)` THENL
  [GEN_TAC THEN MATCH_MP_TAC GL_imp_antisym THEN CONJ_TAC THENL
   [MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `True --> p` THEN CONJ_TAC THENL
    [MATCH_ACCEPT_TAC GL_axiom_iffimp2; ALL_TAC] THEN
    MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(True --> p) && True` THEN
    REWRITE_TAC[GL_modusponens_th] THEN MATCH_MP_TAC GL_and_intro THEN
    REWRITE_TAC[GL_imp_refl_th] THEN MATCH_MP_TAC GL_add_assum THEN
    MATCH_ACCEPT_TAC GL_truth_th;
    ALL_TAC] THEN
   MATCH_MP_TAC GL_imp_trans THEN
   EXISTS_TAC `(p --> True) && (True --> p)` THEN
   CONJ_TAC THENL [ALL_TAC; MESON_TAC[GL_iff_def_th; GL_iff_imp2]] THEN
   MATCH_MP_TAC GL_and_intro THEN REWRITE_TAC[GL_axiom_addimp] THEN
   SIMP_TAC[GL_add_assum; GL_truth_th];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `p <-> True` THEN ASM_REWRITE_TAC[GL_iff_sym_th]);;

let GL_or_subst_th = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> |-- (p || q <-> p' || q')`,
  SUBGOAL_THEN
    `!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
                 ==> |-- (p || q --> p' || q')`
    (fun th -> MESON_TAC[th; GL_iff_sym; GL_iff_def]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GL_disj_imp] THEN CONJ_TAC THEN
  MATCH_MP_TAC GL_frege THENL
  [EXISTS_TAC `p':form` THEN CONJ_TAC THENL
   [MATCH_MP_TAC GL_add_assum THEN MATCH_ACCEPT_TAC GL_or_right_th;
    ASM_SIMP_TAC[GL_iff_imp1]];
   EXISTS_TAC `q':form` THEN CONJ_TAC THENL
   [MATCH_MP_TAC GL_add_assum THEN MATCH_ACCEPT_TAC GL_or_left_th;
    ASM_SIMP_TAC[GL_iff_imp1]]]);;

let GL_or_subst_right = prove
 (`!p q1 q2. |-- (q1 <-> q2) ==> |-- (p || q1 <-> p || q2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GL_or_subst_th THEN
  ASM_REWRITE_TAC[GL_iff_refl_th]);;

let GL_or_rid_th = prove
 (`!p. |-- (p || False <-> p)`,
  GEN_TAC THEN REWRITE_TAC[GL_iff_def] THEN CONJ_TAC THENL
  [REWRITE_TAC[GL_disj_imp; GL_imp_refl_th; GL_ex_falso_th];
   MATCH_ACCEPT_TAC GL_or_right_th]);;

let GL_or_lid_th = prove
 (`!p. |-- (False || p <-> p)`,
  GEN_TAC THEN REWRITE_TAC[GL_iff_def] THEN CONJ_TAC THENL
  [REWRITE_TAC[GL_disj_imp; GL_imp_refl_th; GL_ex_falso_th];
   MATCH_ACCEPT_TAC GL_or_left_th]);;

let GL_or_assoc_left_th = prove
 (`!p q r. |-- (p || (q || r) --> (p || q) || r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GL_disj_imp] THEN
  MESON_TAC[GL_or_left_th; GL_or_right_th; GL_imp_trans]);;

let GL_or_assoc_right_th = prove
 (`!p q r. |-- ((p || q) || r --> p || (q || r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GL_disj_imp] THEN
  MESON_TAC[GL_or_left_th; GL_or_right_th; GL_imp_trans]);;

let GL_or_assoc_th = prove
 (`!p q r. |-- (p || (q || r) <-> (p || q) || r)`,
  REWRITE_TAC[GL_iff_def; GL_or_assoc_left_th; GL_or_assoc_right_th]);;

let GL_and_or_ldistrib_th = prove
 (`!p q r. |-- (p && (q || r) <-> p && q || p && r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GL_iff_def; GL_disj_imp] THEN
  REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC GL_and_intro) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC GL_ante_conj THENL
  [MATCH_MP_TAC GL_imp_swap THEN REWRITE_TAC[GL_disj_imp] THEN
  CONJ_TAC THEN MATCH_MP_TAC GL_imp_swap THEN MATCH_MP_TAC GL_shunt THENL
   [MATCH_ACCEPT_TAC GL_or_right_th; MATCH_ACCEPT_TAC GL_or_left_th];
   MATCH_ACCEPT_TAC GL_axiom_addimp;
   MATCH_MP_TAC GL_add_assum THEN MATCH_ACCEPT_TAC GL_or_right_th;
   MATCH_ACCEPT_TAC GL_axiom_addimp;
   MATCH_MP_TAC GL_add_assum THEN MATCH_ACCEPT_TAC GL_or_left_th]);;

let GL_not_true_th = prove
 (`|-- (Not True <-> False)`,
  REWRITE_TAC[GL_iff_def; GL_ex_falso_th; GSYM GL_not_def] THEN
  MATCH_MP_TAC GL_iff_mp THEN EXISTS_TAC `True` THEN
  REWRITE_TAC[GL_truth_th] THEN ONCE_REWRITE_TAC[GL_iff_sym] THEN
  MATCH_ACCEPT_TAC GL_not_not_th);;

let GL_and_subst_right_th = prove
 (`!p q1 q2. |-- ((q1 <-> q2) --> (p && q1 <-> p && q2))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_imp_trans THEN
  EXISTS_TAC `(p && q1 --> p && q2) && (p && q2 --> p && q1)` THEN
  CONJ_TAC THENL
  [ALL_TAC; MATCH_MP_TAC GL_iff_imp2 THEN MATCH_ACCEPT_TAC GL_iff_def_th] THEN
  SUBGOAL_THEN `!p q1 q2. |-- ((q1 <-> q2) --> (p && q1 --> p && q2))`
    (fun th -> MATCH_MP_TAC GL_and_intro THEN
      MESON_TAC[th; GL_and_comm_th; GL_imp_trans; GL_iff_def_th;
                GL_iff_imp1; GL_iff_imp2]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_shunt THEN MATCH_MP_TAC GL_and_intro THEN
  CONJ_TAC THENL
  [MESON_TAC[GL_and_left_th; GL_and_right_th; GL_imp_trans]; ALL_TAC] THEN
  MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(q1 <-> q2) && q1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC GL_and_intro THEN REWRITE_TAC[GL_and_left_th] THEN
   MESON_TAC[GL_and_right_th; GL_imp_trans];
   MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(q1 --> q2) && q1` THEN
   REWRITE_TAC[GL_modusponens_th] THEN MATCH_MP_TAC GL_and_intro THEN
   REWRITE_TAC[GL_and_right_th] THEN MATCH_MP_TAC GL_imp_trans THEN
   EXISTS_TAC `(q1 <-> q2)` THEN REWRITE_TAC[GL_and_left_th] THEN
   MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(q1 --> q2) && (q2 --> q1)` THEN
   REWRITE_TAC[GL_and_left_th] THEN MATCH_MP_TAC GL_iff_imp1 THEN
   MATCH_ACCEPT_TAC GL_iff_def_th]);;

let GL_and_subst_left_th = prove
 (`!p1 p2 q. |-- ((p1 <-> p2) --> (p1 && q <-> p2 && q))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_imp_trans THEN
  EXISTS_TAC `(p1 && q --> p2 && q) && (p2 && q --> p1 && q)` THEN
  CONJ_TAC THENL
  [ALL_TAC; MATCH_MP_TAC GL_iff_imp2 THEN MATCH_ACCEPT_TAC GL_iff_def_th] THEN
  SUBGOAL_THEN `!p1 p2 q. |-- ((p1 <-> p2) --> (p1 && q --> p2 && q))`
    (fun th -> MATCH_MP_TAC GL_and_intro THEN
      MESON_TAC[th; GL_and_comm_th; GL_imp_trans; GL_iff_def_th;
                GL_iff_imp1; GL_iff_imp2]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_shunt THEN MATCH_MP_TAC GL_and_intro THEN
  CONJ_TAC THENL
  [ALL_TAC; MESON_TAC[GL_and_left_th; GL_and_right_th; GL_imp_trans]] THEN
  MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(p1 <-> p2) && p1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC GL_and_intro THEN REWRITE_TAC[GL_and_left_th] THEN
   MESON_TAC[GL_and_right_th; GL_and_left_th; GL_imp_trans];
   MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(p1 --> p2) && p1` THEN
   REWRITE_TAC[GL_modusponens_th] THEN MATCH_MP_TAC GL_and_intro THEN
   REWRITE_TAC[GL_and_right_th] THEN MATCH_MP_TAC GL_imp_trans THEN
   EXISTS_TAC `(p1 <-> p2)` THEN REWRITE_TAC[GL_and_left_th] THEN
   MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(p1 --> p2) && (p2 --> p1)` THEN
   REWRITE_TAC[GL_and_left_th] THEN MATCH_MP_TAC GL_iff_imp1 THEN
   MATCH_ACCEPT_TAC GL_iff_def_th]);;

let GL_contrapos_th = prove
 (`!p q. |-- ((p --> q) --> (Not q --> Not p))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_imp_swap THEN
  MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(q --> False)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_iff_imp1 THEN MATCH_ACCEPT_TAC GL_axiom_not;
   MATCH_MP_TAC GL_shunt THEN MATCH_MP_TAC GL_imp_trans THEN
   EXISTS_TAC `p --> False` THEN CONJ_TAC THENL
   [MESON_TAC[GL_ante_conj; GL_imp_trans_th];
    MESON_TAC[GL_axiom_not; GL_iff_imp2]]]);;

let GL_contrapos_eq_th = prove
 (`!p q. |-- ((p --> q) <-> (Not q --> Not p))`,
  SUBGOAL_THEN `!p q. |-- ((Not q --> Not p) --> (p --> q))`
    (fun th -> MESON_TAC[th; GL_iff_def; GL_contrapos_th]) THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC GL_imp_trans THEN
  EXISTS_TAC `Not (Not p) --> Not (Not q)` THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC GL_contrapos_th; ALL_TAC] THEN
  MATCH_MP_TAC GL_iff_imp1 THEN MATCH_MP_TAC GL_imp_subst THEN
  MESON_TAC[GL_not_not_th]);;

let GL_iff_sym_th = prove
 (`!p q. |-- ((p <-> q) --> (q <-> p))`,
  REPEAT  GEN_TAC THEN MATCH_MP_TAC GL_imp_trans THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN CONJ_TAC THENL
  [MESON_TAC[GL_iff_def_th; GL_iff_imp1]; ALL_TAC] THEN
  MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(q --> p) && (p --> q)` THEN
  CONJ_TAC THENL
  [MESON_TAC[GL_and_comm_th; GL_iff_imp1];
   MESON_TAC[GL_iff_def_th; GL_iff_imp2]]);;

let GL_de_morgan_or_th = prove
 (`!p q. |-- (Not (p || q) <-> Not p && Not q)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `Not (Not (Not p && Not q))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_not_subst THEN MATCH_ACCEPT_TAC GL_axiom_or;
  MATCH_ACCEPT_TAC GL_not_not_th]);;

let GL_crysippus_th = prove
 (`!p q. |-- (Not (p --> q) <-> p && Not q)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `(p --> Not q --> False) --> False` THEN CONJ_TAC THENL
  [ALL_TAC; MESON_TAC[GL_axiom_and; GL_iff_sym]] THEN
  MATCH_MP_TAC GL_iff_trans THEN EXISTS_TAC `Not (p --> Not q --> False)` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_ACCEPT_TAC GL_axiom_not] THEN
  MATCH_MP_TAC GL_not_subst THEN
  MATCH_MP_TAC GL_imp_subst THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC GL_iff_refl_th; ALL_TAC] THEN
  MATCH_MP_TAC GL_iff_trans THEN EXISTS_TAC `Not (Not q)` THEN CONJ_TAC THENL
  [MESON_TAC[GL_not_not_th; GL_iff_sym]; MATCH_ACCEPT_TAC GL_axiom_not]);;

(* ------------------------------------------------------------------------- *)
(* Substitution.                                                             *)
(* ------------------------------------------------------------------------- *)

let SUBST = new_recursive_definition form_RECURSION
  `(!f. SUBST f True = True) /\
   (!f. SUBST f False = False) /\
   (!f a. SUBST f (Atom a) = f a) /\
   (!f p. SUBST f (Not p) = Not (SUBST f p)) /\
   (!f p q. SUBST f (p && q) = SUBST f p && SUBST f q) /\
   (!f p q. SUBST f (p || q) = SUBST f p || SUBST f q) /\
   (!f p q. SUBST f (p --> q) = SUBST f p --> SUBST f q) /\
   (!f p q. SUBST f (p <-> q) = SUBST f p <-> SUBST f q) /\
   (!f p. SUBST f (Box p) = Box (SUBST f p))`;;

let SUBST_IMP = prove
 (`!f p. |-- p ==> |-- (SUBST f p)`,
  GEN_TAC THEN MATCH_MP_TAC GLproves_INDUCT THEN REWRITE_TAC[SUBST] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC GLaxiom_INDUCT THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC (CONJUNCT1 GLproves_RULES) THEN
   REWRITE_TAC[GLaxiom_RULES; SUBST];
   ALL_TAC] THEN
  REWRITE_TAC[SUBST; GLproves_RULES]);;

let SUBSTITUTION_LEMMA = prove
 (`!f p q. |-- (p <-> q) ==> |-- (SUBST f p <-> SUBST f q)`,
  REWRITE_TAC[GSYM SUBST; SUBST_IMP]);;

(* ------------------------------------------------------------------------- *)
(* SUBST_IFF.                                                                *)
(* ------------------------------------------------------------------------- *)

let GL_iff_subst = prove
 (`!p p' q q'. |-- (p <-> p') /\ |-- (q <-> q')
               ==> |-- ((p <-> q) <-> (p' <-> q'))`,
  SUBGOAL_THEN `!p q p' q'.
                |-- (p <-> p') /\ |-- (q <-> q')
                ==> |-- ((p <-> q) --> (p' <-> q'))`
    (fun th -> REPEAT STRIP_TAC THEN REWRITE_TAC[GL_iff_def] THEN
                ASM_MESON_TAC[th; GL_iff_sym]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GL_imp_trans THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN
  CONJ_TAC THENL [MESON_TAC[GL_iff_def_th; GL_iff_imp1]; ALL_TAC] THEN
  MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `(p' --> q') && (q' --> p')` THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[GL_iff_def_th; GL_iff_imp2]] THEN
  MATCH_MP_TAC GL_and_intro THEN CONJ_TAC THEN MATCH_MP_TAC GL_ante_conj THENL
  [MATCH_MP_TAC GL_imp_insert THEN MATCH_MP_TAC GL_imp_swap THEN
   MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `p:form` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[GL_iff_imp2]; ALL_TAC] THEN
   MATCH_MP_TAC GL_shunt THEN MATCH_MP_TAC GL_imp_trans THEN
   EXISTS_TAC `q:form` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[GL_iff_imp1]] THEN
   MATCH_MP_TAC GL_ante_conj THEN MATCH_MP_TAC GL_imp_swap THEN
   MATCH_ACCEPT_TAC GL_imp_refl_th;
   ALL_TAC] THEN
  MATCH_MP_TAC GL_add_assum THEN MATCH_MP_TAC GL_imp_swap THEN
  MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `q:form` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[GL_iff_imp2]; ALL_TAC] THEN
  MATCH_MP_TAC GL_imp_swap THEN MATCH_MP_TAC GL_imp_add_assum THEN
  ASM_MESON_TAC[GL_iff_imp1]);;

let GL_box_iff_th = prove
 (`!p q. |-- (Box (p <-> q) --> (Box p <-> Box q))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GL_imp_trans THEN
  EXISTS_TAC `(Box p --> Box q) && (Box q --> Box p)` THEN CONJ_TAC THENL
  [ALL_TAC; MATCH_MP_TAC GL_iff_imp2 THEN MATCH_ACCEPT_TAC GL_iff_def_th] THEN
  MATCH_MP_TAC GL_and_intro THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `Box (p --> q)` THEN
   REWRITE_TAC[GL_axiom_boximp] THEN MATCH_MP_TAC GL_imp_box THEN
   MATCH_ACCEPT_TAC GL_axiom_iffimp1;
   MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `Box (q --> p)` THEN
   REWRITE_TAC[GL_axiom_boximp] THEN MATCH_MP_TAC GL_imp_box THEN
   MATCH_ACCEPT_TAC GL_axiom_iffimp2]);;

let GL_box_iff = prove
 (`!p q. |-- (Box (p <-> q)) ==> |-- (Box p <-> Box q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GL_imp_antisym THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_modusponens THEN EXISTS_TAC `Box (p --> q)` THEN
   REWRITE_TAC[GL_axiom_boximp] THEN
   MATCH_MP_TAC GL_box_moduspones THEN EXISTS_TAC `(p <-> q)` THEN
   ASM_REWRITE_TAC[GL_axiom_iffimp1];
   MATCH_MP_TAC GL_modusponens THEN EXISTS_TAC `Box (q --> p)` THEN
   REWRITE_TAC[GL_axiom_boximp] THEN
   MATCH_MP_TAC GL_box_moduspones THEN EXISTS_TAC `(p <-> q)` THEN
   ASM_REWRITE_TAC[GL_axiom_iffimp2]]);;

let GL_box_subst = prove
 (`!p q. |-- (p <-> q) ==> |-- (Box p <-> Box q)`,
  SIMP_TAC[GL_box_iff; GL_necessitation]);;

let SUBST_IFF = prove
 (`!f g p. (!a. |-- (f a <-> g a)) ==> |-- (SUBST f p <-> SUBST g p)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC form_INDUCT THEN
  ASM_REWRITE_TAC[SUBST; GL_iff_refl_th] THEN REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC GL_not_subst THEN POP_ASSUM MATCH_ACCEPT_TAC;
   MATCH_MP_TAC GL_and_subst_th THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC GL_or_subst_th THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC GL_imp_subst THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC GL_iff_subst THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC GL_box_subst THEN POP_ASSUM MATCH_ACCEPT_TAC]);;

(* ----------------------------------------------------------------------- *)
(* Some modal propositional schemas and derived rules.                     *)
(* ----------------------------------------------------------------------- *)

let GL_box_and_th = prove
 (`!p q. |-- (Box(p && q) --> (Box p && Box q))`,
  MESON_TAC[GL_and_intro; GL_imp_box;GL_and_left_th;GL_and_right_th]);;

let GL_box_and_inv_th = prove
 (`!p q. |-- ((Box p && Box q) --> Box (p && q))`,
  MESON_TAC[GL_ante_conj; GL_imp_trans; GL_imp_box; GL_and_pair_th;
            GL_axiom_boximp; GL_shunt]);;

let GL_schema_4 = prove
 (`!p. |-- (Box p --> Box (Box p))`,
  MESON_TAC[GL_axiom_lob; GL_imp_box; GL_and_pair_th; GL_and_intro;
    GL_shunt; GL_imp_trans;GL_and_right_th;GL_and_left_th;GL_box_and_th]);;

let GL_dot_box = prove
 (`!p. |-- (Box p --> Box p && Box (Box p))`,
  MESON_TAC[GL_imp_refl_th; GL_schema_4; GL_and_intro]);;
