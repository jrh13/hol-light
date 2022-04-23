(* ========================================================================= *)
(* Alternative axiomatization of the modal provability logic GL.             *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* ========================================================================= *)

let K4LRaxiom_RULES,K4LRaxiom_INDUCT,K4LRaxiom_CASES = new_inductive_definition
  `(!p q. K4LRaxiom (p --> (q --> p))) /\
   (!p q r. K4LRaxiom ((p --> q --> r) --> (p --> q) --> (p --> r))) /\
   (!p. K4LRaxiom (((p --> False) --> False) --> p)) /\
   (!p q. K4LRaxiom ((p <-> q) --> p --> q)) /\
   (!p q. K4LRaxiom ((p <-> q) --> q --> p)) /\
   (!p q. K4LRaxiom ((p --> q) --> (q --> p) --> (p <-> q))) /\
   K4LRaxiom (True <-> False --> False) /\
   (!p. K4LRaxiom (Not p <-> p --> False)) /\
   (!p q. K4LRaxiom (p && q <-> (p --> q --> False) --> False)) /\
   (!p q. K4LRaxiom (p || q <-> Not(Not p && Not q))) /\
   (!p q. K4LRaxiom (Box (p --> q) --> Box p --> Box q)) /\
   (!p. K4LRaxiom (Box p --> Box (Box p)))`;;

(* ------------------------------------------------------------------------- *)
(* Rules.                                                                    *)
(* ------------------------------------------------------------------------- *)

let K4LRproves_RULES,K4LRproves_INDUCT,K4LRproves_CASES =
  new_inductive_definition
  `(!p. K4LRaxiom p ==> |~ p) /\
   (!p q. |~ (p --> q) /\ |~ p ==> |~ q) /\
   (!p. |~ p ==> |~ (Box p)) /\
   (!p . |~ (Box p --> p) ==> |~ p)`;;

(* ------------------------------------------------------------------------- *)
(* Propositional lemmas.                                                     *)
(* ------------------------------------------------------------------------- *)

let K4LR_axiom_addimp = prove
 (`!p q. |~ (p --> (q --> p))`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_distribimp = prove
 (`!p q r. |~ ((p --> q --> r) --> (p --> q) --> (p --> r))`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_doubleneg = prove
 (`!p. |~ (((p --> False) --> False) --> p)`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_iffimp1 = prove
 (`!p q. |~ ((p <-> q) --> p --> q)`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_iffimp2 = prove
 (`!p q. |~ ((p <-> q) --> q --> p)`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_impiff = prove
 (`!p q. |~ ((p --> q) --> (q --> p) --> (p <-> q))`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_true = prove
 (`|~ (True <-> (False --> False))`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_not = prove
 (`!p. |~ (Not p <-> (p --> False))`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_and = prove
 (`!p q. |~ ((p && q) <-> (p --> q --> False) --> False)`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_or = prove
 (`!p q. |~ ((p || q) <-> Not(Not p && Not q))`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_boximp = prove
 (`!p q. |~ (Box (p --> q) --> Box p --> Box q)`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_axiom_4 = prove
 (`!p. |~ (Box p --> Box (Box p))`,
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES]);;

let K4LR_modusponens = prove
 (`!p. |~ (p --> q) /\ |~ p ==> |~ q`,
  MESON_TAC[K4LRproves_RULES]);;

let K4LR_necessitation = prove
 (`!p. |~ p ==> |~ (Box p)`,
  MESON_TAC[K4LRproves_RULES]);;

let K4LR_lobrule = prove
 (`!p. |~ (Box p --> p) ==> |~ p`,
 MESON_TAC[K4LRproves_RULES]);;

let K4LR_iff_imp1 = prove
 (`!p q. |~ (p <-> q) ==> |~ (p --> q)`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_iffimp1]);;

let K4LR_iff_imp2 = prove
 (`!p q. |~ (p <-> q) ==> |~ (q --> p)`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_iffimp2]);;

let K4LR_imp_antisym = prove
 (`!p q. |~ (p --> q) /\ |~ (q --> p) ==> |~ (p <-> q)`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_impiff]);;

let K4LR_add_assum = prove
 (`!p q. |~ q ==> |~ (p --> q)`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_addimp]);;

let K4LR_imp_refl_th = prove
 (`!p. |~ (p --> p)`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_distribimp; K4LR_axiom_addimp]);;

let K4LR_imp_add_assum = prove
 (`!p q r. |~ (q --> r) ==> |~ ((p --> q) --> (p --> r))`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_distribimp; K4LR_add_assum]);;

let K4LR_imp_unduplicate = prove
 (`!p q. |~ (p --> p --> q) ==> |~ (p --> q)`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_distribimp; K4LR_imp_refl_th]);;

let K4LR_imp_trans = prove
 (`!p q. |~ (p --> q) /\ |~ (q --> r) ==> |~ (p --> r)`,
  MESON_TAC[K4LR_modusponens; K4LR_imp_add_assum]);;

let K4LR_imp_swap = prove
 (`!p q r. |~ (p --> q --> r) ==> |~ (q --> p --> r)`,
  MESON_TAC[K4LR_imp_trans; K4LR_axiom_addimp; K4LR_modusponens;
            K4LR_axiom_distribimp]);;

let K4LR_imp_trans_chain_2 = prove
 (`!p q1 q2 r. |~ (p --> q1) /\ |~ (p --> q2) /\ |~ (q1 --> q2 --> r)
               ==> |~ (p --> r)`,
  ASM_MESON_TAC[K4LR_imp_trans; K4LR_imp_swap; K4LR_imp_unduplicate]);;

let K4LR_imp_trans_th = prove
 (`!p q r. |~ ((q --> r) --> (p --> q) --> (p --> r))`,
  MESON_TAC[K4LR_imp_trans; K4LR_axiom_addimp; K4LR_axiom_distribimp]);;

let K4LR_imp_add_concl = prove
 (`!p q r. |~ (p --> q) ==> |~ ((q --> r) --> (p --> r))`,
  MESON_TAC[K4LR_modusponens; K4LR_imp_swap; K4LR_imp_trans_th]);;

let K4LR_imp_trans2 = prove
 (`!p q r s. |~ (p --> q --> r) /\ |~ (r --> s) ==> |~ (p --> q --> s)`,
  MESON_TAC[K4LR_imp_add_assum; K4LR_modusponens; K4LR_imp_trans_th]);;

let K4LR_imp_swap_th = prove
 (`!p q r. |~ ((p --> q --> r) --> (q --> p --> r))`,
  MESON_TAC[K4LR_imp_trans; K4LR_axiom_distribimp; K4LR_imp_add_concl;
            K4LR_axiom_addimp]);;

let K4LR_contrapos = prove
 (`!p q. |~ (p --> q) ==> |~ (Not q --> Not p)`,
  MESON_TAC[K4LR_imp_trans; K4LR_iff_imp1; K4LR_axiom_not;
            K4LR_imp_add_concl; K4LR_iff_imp2]);;

let K4LR_imp_truefalse_th = prove
 (`!p q. |~ ((q --> False) --> p --> (p --> q) --> False)`,
  MESON_TAC[K4LR_imp_trans; K4LR_imp_trans_th; K4LR_imp_swap_th]);;

let K4LR_imp_insert = prove
 (`!p q r. |~ (p --> r) ==> |~ (p --> q --> r)`,
  MESON_TAC[K4LR_imp_trans; K4LR_axiom_addimp]);;

let K4LR_imp_mono_th = prove
 (`|~ ((p' --> p) --> (q --> q') --> (p --> q) --> (p' --> q'))`,
  MESON_TAC[K4LR_imp_trans; K4LR_imp_swap; K4LR_imp_trans_th]);;

let K4LR_ex_falso_th = prove
 (`!p. |~ (False --> p)`,
  MESON_TAC[K4LR_imp_trans; K4LR_axiom_addimp; K4LR_axiom_doubleneg]);;

let K4LR_ex_falso = prove
 (`!p. |~ False ==> |~ p`,
  MESON_TAC[K4LR_ex_falso_th; K4LR_modusponens]);;

let K4LR_imp_contr_th = prove
 (`!p q. |~ ((p --> False) --> (p --> q))`,
  MESON_TAC[K4LR_imp_add_assum; K4LR_ex_falso_th]);;

let K4LR_contrad = prove
 (`!p. |~ ((p --> False) --> p) ==> |~ p`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_distribimp;
            K4LR_imp_refl_th; K4LR_axiom_doubleneg]);;

let K4LR_bool_cases = prove
 (`!p q. |~ (p --> q) /\ |~ ((p --> False) --> q) ==> |~ q`,
  MESON_TAC[K4LR_contrad; K4LR_imp_trans; K4LR_imp_add_concl]);;

let K4LR_imp_false_rule = prove
 (`!p q r. |~ ((q --> False) --> p --> r)
           ==> |~ (((p --> q) --> False) --> r)`,
  MESON_TAC[K4LR_imp_add_concl; K4LR_imp_add_assum; K4LR_ex_falso_th;
            K4LR_axiom_addimp; K4LR_imp_swap; K4LR_imp_trans;
            K4LR_axiom_doubleneg; K4LR_imp_unduplicate]);;

let K4LR_imp_true_rule = prove
 (`!p q r. |~ ((p --> False) --> r) /\ |~ (q --> r)
           ==> |~ ((p --> q) --> r)`,
  MESON_TAC[K4LR_imp_insert; K4LR_imp_swap; K4LR_modusponens;
            K4LR_imp_trans_th; K4LR_bool_cases]);;

let K4LR_truth_th = prove
 (`|~ True`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_true;
            K4LR_imp_refl_th; K4LR_iff_imp2]);;

let K4LR_and_left_th = prove
 (`!p q. |~ (p && q --> p)`,
  MESON_TAC[K4LR_imp_add_assum; K4LR_axiom_addimp; K4LR_imp_trans;
            K4LR_imp_add_concl; K4LR_axiom_doubleneg; K4LR_imp_trans;
            K4LR_iff_imp1; K4LR_axiom_and]);;

let K4LR_and_right_th = prove
 (`!p q. |~ (p && q --> q)`,
  MESON_TAC[K4LR_axiom_addimp; K4LR_imp_trans; K4LR_imp_add_concl;
            K4LR_axiom_doubleneg; K4LR_iff_imp1; K4LR_axiom_and]);;

let K4LR_and_pair_th = prove
 (`!p q. |~ (p --> q --> p && q)`,
  MESON_TAC[K4LR_iff_imp2; K4LR_axiom_and; K4LR_imp_swap_th;
            K4LR_imp_add_assum; K4LR_imp_trans2; K4LR_modusponens;
            K4LR_imp_swap; K4LR_imp_refl_th]);;

let K4LR_and = prove
 (`!p q. |~ (p && q) <=> |~ p /\ |~ q`,
  MESON_TAC[K4LR_and_left_th; K4LR_and_right_th; K4LR_and_pair_th;
            K4LR_modusponens]);;

let K4LR_and_elim = prove
 (`!p q r. |~ (r --> p && q) ==> |~ (r --> q)  /\ |~ (r --> p)`,
  MESON_TAC[K4LR_and_left_th; K4LR_and_right_th; K4LR_imp_trans]);;

let K4LR_shunt = prove
 (`!p q r. |~ (p && q --> r) ==> |~ (p --> q --> r)`,
  MESON_TAC[K4LR_modusponens; K4LR_imp_add_assum; K4LR_and_pair_th]);;

let K4LR_ante_conj = prove
 (`!p q r. |~ (p --> q --> r) ==> |~ (p && q --> r)`,
  MESON_TAC[K4LR_imp_trans_chain_2; K4LR_and_left_th; K4LR_and_right_th]);;

let K4LR_modusponens_th = prove
 (`!p q. |~ ((p --> q) && p --> q)`,
  MESON_TAC[K4LR_imp_refl_th; K4LR_ante_conj]);;

let K4LR_not_not_false_th = prove
 (`!p. |~ ((p --> False) --> False <-> p)`,
  MESON_TAC[K4LR_imp_antisym; K4LR_axiom_doubleneg; K4LR_imp_swap;
            K4LR_imp_refl_th]);;

let K4LR_iff_sym = prove
 (`!p q. |~ (p <-> q) <=> |~ (q <-> p)`,
  MESON_TAC[K4LR_iff_imp1; K4LR_iff_imp2; K4LR_imp_antisym]);;

let K4LR_iff_trans = prove
 (`!p q r. |~ (p <-> q) /\ |~ (q <-> r) ==> |~ (p <-> r)`,
  MESON_TAC[K4LR_iff_imp1; K4LR_iff_imp2; K4LR_imp_trans; K4LR_imp_antisym]);;

let K4LR_not_not_th = prove
 (`!p. |~ (Not (Not p) <-> p)`,
  MESON_TAC[K4LR_iff_trans; K4LR_not_not_false_th; K4LR_axiom_not;
            K4LR_imp_antisym; K4LR_imp_add_concl; K4LR_iff_imp1;
            K4LR_iff_imp2]);;

let K4LR_contrapos_eq = prove
 (`!p q. |~ (Not p --> Not q) <=> |~ (q --> p)`,
  MESON_TAC[K4LR_contrapos; K4LR_not_not_th; K4LR_iff_imp1;
            K4LR_iff_imp2; K4LR_imp_trans]);;

let K4LR_or_left_th = prove
 (`!p q. |~ (q --> p || q)`,
  MESON_TAC[K4LR_imp_trans; K4LR_not_not_th; K4LR_iff_imp2;
            K4LR_and_right_th; K4LR_contrapos; K4LR_axiom_or]);;

let K4LR_or_right_th = prove
 (`!p q. |~ (p --> p || q)`,
  MESON_TAC[K4LR_imp_trans; K4LR_not_not_th; K4LR_iff_imp2;
            K4LR_and_left_th; K4LR_contrapos; K4LR_axiom_or]);;

let K4LR_ante_disj = prove
 (`!p q r. |~ (p --> r) /\ |~ (q --> r) ==> |~ (p || q --> r)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM K4LR_contrapos_eq] THEN
  MESON_TAC[K4LR_imp_trans; K4LR_imp_trans_chain_2; K4LR_and_pair_th;
            K4LR_contrapos_eq; K4LR_not_not_th; K4LR_axiom_or; K4LR_iff_imp1;
            K4LR_iff_imp2; K4LR_imp_trans]);;

let K4LR_iff_def_th = prove
 (`!p q. |~ ((p <-> q) <-> (p --> q) && (q --> p))`,
  MESON_TAC[K4LR_imp_antisym; K4LR_imp_trans_chain_2; K4LR_axiom_iffimp1;
            K4LR_axiom_iffimp2; K4LR_and_pair_th; K4LR_axiom_impiff;
            K4LR_imp_trans_chain_2; K4LR_and_left_th; K4LR_and_right_th]);;

let K4LR_iff_refl_th = prove
 (`!p. |~ (p <-> p)`,
  MESON_TAC[K4LR_imp_antisym; K4LR_imp_refl_th]);;

let K4LR_imp_box = prove
 (`!p q. |~ (p --> q) ==> |~ (Box p --> Box q)`,
  MESON_TAC[K4LR_modusponens; K4LR_necessitation; K4LR_axiom_boximp]);;

let K4LR_box_moduspones = prove
 (`!p q. |~ (p --> q) /\ |~ (Box p) ==> |~ (Box q)`,
  MESON_TAC[K4LR_imp_box; K4LR_modusponens]);;

let K4LR_box_and = prove
 (`!p q. |~ (Box(p && q)) ==> |~ (Box p && Box q)`,
  MESON_TAC[K4LR_and_left_th; K4LR_and_right_th; K4LR_imp_box;
            K4LR_box_moduspones; K4LR_and]);;

 let K4LR_box_and_inv = prove
  (`!p q. |~ (Box p && Box q) ==> |~ (Box (p && q))`,
   MESON_TAC[K4LR_and_pair_th; K4LR_imp_box; K4LR_axiom_boximp;
             K4LR_imp_trans; K4LR_ante_conj; K4LR_modusponens]);;

let K4LR_and_comm = prove
 (`!p q . |~ (p && q) <=> |~ (q && p)`,
  MESON_TAC[K4LR_and]);;

let K4LR_and_assoc = prove
 (`!p q r. |~ ((p && q) && r) <=> |~ (p && (q && r))`,
  MESON_TAC[K4LR_and]);;

let K4LR_disj_imp = prove
 (`!p q r. |~ (p || q --> r) <=> |~ (p --> r) /\ |~ (q --> r)`,
  MESON_TAC[K4LR_ante_disj; K4LR_or_right_th; K4LR_or_left_th;
            K4LR_imp_trans]);;

let K4LR_or_elim = prove
 (`!p q r. |~ (p || q) /\ |~ (p --> r) /\ |~ (q --> r) ==> |~ r`,
  MESON_TAC[K4LR_disj_imp; K4LR_modusponens]);;

let K4LR_or_comm = prove
 (`!p q . |~ (p || q) <=> |~ (q || p)`,
  MESON_TAC[K4LR_or_right_th; K4LR_or_left_th; K4LR_modusponens;
            K4LR_disj_imp]);;

let K4LR_or_assoc = prove
 (`!p q r. |~ ((p || q) || r) <=> |~ (p || (q || r))`,
  MESON_TAC[K4LR_or_right_th; K4LR_or_left_th; K4LR_modusponens;
            K4LR_disj_imp]);;

let K4LR_or_intror = prove
 (`!p q. |~ q ==> |~ (p || q)`,
  MESON_TAC[K4LR_or_left_th; K4LR_modusponens]);;

let K4LR_or_introl = prove
 (`!p q. |~ p ==> |~ (p || q)`,
  MESON_TAC[K4LR_or_right_th; K4LR_modusponens]);;

let K4LR_or_transl = prove
 (`!p q r. |~ (p --> q) ==> |~ (p --> q || r)`,
  MESON_TAC[K4LR_or_right_th; K4LR_imp_trans]);;

let K4LR_or_transr = prove
 (`!p q r. |~ (p --> r) ==> |~ (p --> q || r)`,
  MESON_TAC[K4LR_or_left_th; K4LR_imp_trans]);;

let K4LR_frege = prove
 (`!p q r. |~ (p --> q --> r) /\ |~ (p --> q) ==> |~ (p --> r)`,
  MESON_TAC[K4LR_axiom_distribimp; K4LR_modusponens; K4LR_shunt;
            K4LR_ante_conj]);;

let K4LR_and_intro = prove
 (`!p q r. |~ (p --> q) /\ |~ (p --> r) ==> |~ (p --> q && r)`,
  MESON_TAC[K4LR_and_pair_th; K4LR_imp_trans_chain_2]);;

let K4LR_not_def = prove
 (`!p. |~ (Not p) <=> |~ (p --> False)`,
   MESON_TAC[K4LR_axiom_not; K4LR_modusponens; K4LR_iff_imp1;
             K4LR_iff_imp2]);;

let K4LR_NC = prove
 (`!p. |~ (p  && Not p) <=> |~ False`,
  MESON_TAC[K4LR_not_def; K4LR_modusponens; K4LR_and; K4LR_ex_falso]);;

  let K4LR_nc_th = prove
   (`!p. |~ (p && Not p --> False)`,
    MESON_TAC[K4LR_ante_conj; K4LR_imp_swap; K4LR_axiom_not;
              K4LR_axiom_iffimp1; K4LR_modusponens]);;

let K4LR_imp_clauses = prove
 (`(!p. |~ (p --> True)) /\
   (!p. |~ (p --> False) <=> |~ (Not p)) /\
   (!p. |~ (True --> p) <=> |~ p) /\
   (!p. |~ (False --> p))`,
  SIMP_TAC[K4LR_truth_th; K4LR_add_assum; K4LR_not_def; K4LR_ex_falso_th] THEN
  GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[K4LR_modusponens; K4LR_truth_th];
   MESON_TAC[K4LR_add_assum]]);;

let K4LR_and_left_true_th = prove
 (`!p. |~ (True && p <-> p)`,
  GEN_TAC THEN MATCH_MP_TAC K4LR_imp_antisym THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC K4LR_and_right_th; ALL_TAC] THEN
  MATCH_MP_TAC K4LR_and_intro THEN
  REWRITE_TAC[K4LR_imp_refl_th; K4LR_imp_clauses]);;

let K4LR_or_and_distr = prove
 (`!p q r. |~ ((p || q) && r) ==> |~ ((p && r) || (q && r))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[K4LR_and] THEN STRIP_TAC THEN
  MATCH_MP_TAC K4LR_or_elim THEN EXISTS_TAC `p:form` THEN
  EXISTS_TAC `q :form` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_or_transl THEN MATCH_MP_TAC K4LR_and_intro THEN
   REWRITE_TAC[K4LR_imp_refl_th] THEN ASM_SIMP_TAC[K4LR_add_assum];
   MATCH_MP_TAC K4LR_or_transr THEN MATCH_MP_TAC K4LR_and_intro THEN
   REWRITE_TAC[K4LR_imp_refl_th] THEN ASM_SIMP_TAC[K4LR_add_assum]]);;

let K4LR_and_or_distr = prove
 (`!p q r. |~ ((p && q) || r) ==> |~ ((p || r) && (q || r))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[K4LR_and] THEN DISCH_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC K4LR_or_elim THEN
  MAP_EVERY EXISTS_TAC [`p && q`; `r:form`] THEN
  ASM_REWRITE_TAC[K4LR_or_left_th] THEN MATCH_MP_TAC K4LR_or_transl THEN
  ASM_REWRITE_TAC[K4LR_and_left_th; K4LR_and_right_th]);;

let K4LR_or_and_distr_inv = prove
 (`!p q r. |~ ((p && r) || (q && r)) ==> |~ ((p || q) && r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC K4LR_or_elim THEN
  MAP_EVERY EXISTS_TAC [`p && r`; `q && r`] THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM (K ALL_TAC) THEN CONJ_TAC THEN MATCH_MP_TAC K4LR_and_intro THEN
  CONJ_TAC THEN REWRITE_TAC[K4LR_and_left_th; K4LR_and_right_th] THENL
  [MATCH_MP_TAC K4LR_or_transl THEN MATCH_ACCEPT_TAC K4LR_and_left_th;
   MATCH_MP_TAC K4LR_or_transr THEN MATCH_ACCEPT_TAC K4LR_and_left_th]);;

let K4LR_or_and_distr_equiv = prove
 (`!p q r. |~ ((p || q) && r) <=> |~ ((p && r) || (q && r))`,
  MESON_TAC[K4LR_or_and_distr; K4LR_or_and_distr_inv]);;

let K4LR_and_or_distr_inv_prelim = prove
 (`!p q r. |~ ((p || r) && (q || r)) ==> |~ (q --> (p && q) || r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K4LR_and] THEN INTRO_TAC "pr qr" THEN
  MATCH_MP_TAC (SPECL [`p:form`; `r:form`] K4LR_or_elim) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "pr" (K ALL_TAC) THEN CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_shunt THEN MATCH_ACCEPT_TAC K4LR_or_right_th;
   ALL_TAC] THEN
  MATCH_MP_TAC K4LR_imp_insert THEN MATCH_ACCEPT_TAC K4LR_or_left_th);;

let K4LR_and_or_distr_inv = prove
 (`!p q r. |~ ((p || r) && (q || r)) ==> |~ ((p && q) || r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K4LR_and] THEN INTRO_TAC "pr qr" THEN
  MATCH_MP_TAC (SPECL [`p:form`; `r:form`] K4LR_or_elim) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "pr" (K ALL_TAC) THEN
  REWRITE_TAC[K4LR_or_left_th] THEN
  MATCH_MP_TAC (SPECL [`q:form`; `r:form`] K4LR_or_elim) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "qr" (K ALL_TAC) THEN CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_imp_swap THEN MATCH_MP_TAC K4LR_shunt THEN
   MATCH_ACCEPT_TAC K4LR_or_right_th;
   MATCH_MP_TAC K4LR_imp_insert THEN MATCH_ACCEPT_TAC K4LR_or_left_th]);;

let K4LR_and_or_distr_equiv = prove
 (`!p q r. |~ ((p && q) || r) <=> |~ ((p || r) && (q || r))`,
  MESON_TAC[K4LR_and_or_distr; K4LR_and_or_distr_inv]);;

let K4LR_DOUBLENEG_CL = prove
 (`!p. |~ (Not(Not p)) ==> |~ p`,
 MESON_TAC[K4LR_not_not_th; K4LR_modusponens; K4LR_iff_imp1; K4LR_iff_imp2]);;

let K4LR_DOUBLENEG = prove
 (`!p. |~ p ==> |~ (Not(Not p))`,
  MESON_TAC[K4LR_not_not_th; K4LR_modusponens; K4LR_iff_imp1; K4LR_iff_imp2]);;

let K4LR_and_eq_or = prove
 (`!p q. |~ (p || q) <=> |~ (Not(Not p && Not q))`,
  MESON_TAC[K4LR_modusponens; K4LR_axiom_or; K4LR_iff_imp1; K4LR_iff_imp2]);;

let K4LR_tnd_th = prove
 (`!p. |~ (p || Not p)`,
  GEN_TAC THEN REWRITE_TAC[K4LR_and_eq_or] THEN
  REWRITE_TAC[K4LR_not_def] THEN MESON_TAC[K4LR_nc_th]);;

let K4LR_iff_mp = prove
 (`!p q. |~ (p <-> q) /\ |~ p ==> |~ q`,
  MESON_TAC[K4LR_iff_imp1; K4LR_modusponens]);;

let K4LR_and_subst = prove
 (`!p p' q q'. |~ (p <-> p') /\ |~ (q <-> q')
               ==> (|~ (p && q) <=> |~ (p' && q'))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[K4LR_and] THEN
  ASM_MESON_TAC[K4LR_iff_mp; K4LR_iff_sym]);;

let K4LR_imp_mono_th = prove
 (`!p p' q q'. |~ ((p' --> p) && (q --> q') --> (p --> q) --> (p' --> q'))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_ante_conj THEN
  MATCH_ACCEPT_TAC K4LR_imp_mono_th);;

let K4LR_imp_mono = prove
 (`!p p' q q'. |~ (p' --> p) /\ |~ (q --> q')
               ==> |~ ((p --> q) --> (p' --> q'))`,
  REWRITE_TAC[GSYM K4LR_and] THEN
  MESON_TAC[K4LR_modusponens;K4LR_imp_mono_th]);;

let K4LR_iff = prove
 (`!p q. |~ (p <-> q) ==> (|~ p <=> |~ q)`,
  MESON_TAC[K4LR_iff_imp1; K4LR_iff_imp2; K4LR_modusponens]);;

let K4LR_iff_def = prove
 (`!p q. |~ (p <-> q) <=> |~ (p --> q) /\ |~ (q --> p)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[K4LR_iff_imp1; K4LR_iff_imp2];
   MATCH_ACCEPT_TAC K4LR_imp_antisym]);;

let K4LR_not_subst = prove
 (`!p q. |~ (p <-> q) ==> |~ (Not p <-> Not q)`,
  MESON_TAC[K4LR_iff_def; K4LR_iff_imp2; K4LR_contrapos]);;

let K4LR_and_rigth_true_th = prove
 (`!p. |~ (p && True <-> p)`,
  GEN_TAC THEN REWRITE_TAC[K4LR_iff_def] THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC K4LR_and_left_th; ALL_TAC] THEN
  MATCH_MP_TAC K4LR_and_intro THEN REWRITE_TAC[K4LR_imp_refl_th] THEN
  MATCH_MP_TAC K4LR_add_assum THEN MATCH_ACCEPT_TAC K4LR_truth_th);;

let K4LR_and_comm_th = prove
 (`!p q. |~ (p && q <-> q && p)`,
  SUBGOAL_THEN `!p q. |~ (p && q --> q && p)`
    (fun th -> MESON_TAC[th; K4LR_iff_def]) THEN
  MESON_TAC[K4LR_and_intro; K4LR_and_left_th; K4LR_and_right_th]);;

let K4LR_and_assoc_th = prove
 (`!p q r. |~ ((p && q) && r <-> p && (q && r))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_imp_antisym THEN CONJ_TAC THEN
  MATCH_MP_TAC K4LR_and_intro THEN
  MESON_TAC[K4LR_and_left_th; K4LR_and_right_th;
            K4LR_imp_trans; K4LR_and_intro]);;

let K4LR_and_subst_th = prove
 (`!p p' q q'. |~ (p <-> p') /\ |~ (q <-> q')
               ==> |~ (p && q <-> p' && q')`,
  SUBGOAL_THEN
    `!p p' q q'. |~ (p <-> p') /\ |~ (q <-> q')
                 ==> |~ (p && q --> p' && q')`
    (fun th -> MESON_TAC[th; K4LR_iff_def]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC K4LR_and_intro THEN CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `p:form` THEN
   REWRITE_TAC[K4LR_and_left_th] THEN ASM_SIMP_TAC[K4LR_iff_imp1];
   MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `q:form` THEN
   REWRITE_TAC[K4LR_and_right_th] THEN ASM_SIMP_TAC[K4LR_iff_imp1]]);;

let K4LR_imp_subst = prove
 (`!p p' q q'. |~ (p <-> p') /\ |~ (q <-> q')
               ==> |~ ((p --> q) <-> (p' --> q'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[K4LR_iff_def] THEN
  POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
  SUBGOAL_THEN `!p q p' q'.
                  |~ (p <-> p') /\ |~ (q <-> q')
                  ==> |~ ((p --> q) --> (p' --> q'))`
    (fun th -> MESON_TAC[th; K4LR_iff_sym]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC K4LR_imp_mono THEN
  ASM_MESON_TAC[K4LR_iff_imp1; K4LR_iff_sym]);;

let K4LR_de_morgan_and_th = prove
 (`!p q. |~ (Not (p && q) <-> Not p || Not q)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_iff_trans THEN
  EXISTS_TAC `Not (Not (Not p) && Not (Not q))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_not_subst THEN ONCE_REWRITE_TAC[K4LR_iff_sym] THEN
   MATCH_MP_TAC K4LR_and_subst_th THEN CONJ_TAC THEN
   MATCH_ACCEPT_TAC K4LR_not_not_th;
   ONCE_REWRITE_TAC[K4LR_iff_sym] THEN MATCH_ACCEPT_TAC K4LR_axiom_or]);;

let K4LR_iff_sym_th = prove
 (`!p q. |~ ((p <-> q) <-> (q <-> p))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_iff_trans THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN
  ASM_REWRITE_TAC[K4LR_iff_def_th] THEN
  ONCE_REWRITE_TAC[K4LR_iff_sym] THEN MATCH_MP_TAC K4LR_iff_trans THEN
  EXISTS_TAC `(q --> p) && (p --> q)` THEN
  REWRITE_TAC[K4LR_iff_def_th; K4LR_and_comm_th]);;

let K4LR_iff_true_th = prove
 (`(!p. |~ ((p <-> True) <-> p)) /\
   (!p. |~ ((True <-> p) <-> p))`,
  CLAIM_TAC "1" `!p. |~ ((p <-> True) <-> p)` THENL
  [GEN_TAC THEN MATCH_MP_TAC K4LR_imp_antisym THEN CONJ_TAC THENL
   [MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `True --> p` THEN
    CONJ_TAC THENL
    [MATCH_ACCEPT_TAC K4LR_axiom_iffimp2; ALL_TAC] THEN
    MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `(True --> p) && True` THEN
    REWRITE_TAC[K4LR_modusponens_th] THEN MATCH_MP_TAC K4LR_and_intro THEN
    REWRITE_TAC[K4LR_imp_refl_th] THEN MATCH_MP_TAC K4LR_add_assum THEN
    MATCH_ACCEPT_TAC K4LR_truth_th;
    ALL_TAC] THEN
   MATCH_MP_TAC K4LR_imp_trans THEN
   EXISTS_TAC `(p --> True) && (True --> p)` THEN
   CONJ_TAC THENL [ALL_TAC; MESON_TAC[K4LR_iff_def_th; K4LR_iff_imp2]] THEN
   MATCH_MP_TAC K4LR_and_intro THEN REWRITE_TAC[K4LR_axiom_addimp] THEN
   SIMP_TAC[K4LR_add_assum; K4LR_truth_th];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC K4LR_iff_trans THEN
  EXISTS_TAC `p <-> True` THEN ASM_REWRITE_TAC[K4LR_iff_sym_th]);;

let K4LR_or_subst_th = prove
 (`!p p' q q'. |~ (p <-> p') /\ |~ (q <-> q')
               ==> |~ (p || q <-> p' || q')`,
  SUBGOAL_THEN
    `!p p' q q'. |~ (p <-> p') /\ |~ (q <-> q')
                 ==> |~ (p || q --> p' || q')`
    (fun th -> MESON_TAC[th; K4LR_iff_sym; K4LR_iff_def]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[K4LR_disj_imp] THEN CONJ_TAC THEN
  MATCH_MP_TAC K4LR_frege THENL
  [EXISTS_TAC `p':form` THEN CONJ_TAC THENL
   [MATCH_MP_TAC K4LR_add_assum THEN MATCH_ACCEPT_TAC K4LR_or_right_th;
    ASM_SIMP_TAC[K4LR_iff_imp1]];
   EXISTS_TAC `q':form` THEN CONJ_TAC THENL
   [MATCH_MP_TAC K4LR_add_assum THEN MATCH_ACCEPT_TAC K4LR_or_left_th;
    ASM_SIMP_TAC[K4LR_iff_imp1]]]);;

let K4LR_or_subst_right = prove
 (`!p q1 q2. |~ (q1 <-> q2) ==> |~ (p || q1 <-> p || q2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC K4LR_or_subst_th THEN
  ASM_REWRITE_TAC[K4LR_iff_refl_th]);;

let K4LR_or_rid_th = prove
 (`!p. |~ (p || False <-> p)`,
  GEN_TAC THEN REWRITE_TAC[K4LR_iff_def] THEN CONJ_TAC THENL
  [REWRITE_TAC[K4LR_disj_imp; K4LR_imp_refl_th; K4LR_ex_falso_th];
   MATCH_ACCEPT_TAC K4LR_or_right_th]);;

let K4LR_or_lid_th = prove
 (`!p. |~ (False || p <-> p)`,
  GEN_TAC THEN REWRITE_TAC[K4LR_iff_def] THEN CONJ_TAC THENL
  [REWRITE_TAC[K4LR_disj_imp; K4LR_imp_refl_th; K4LR_ex_falso_th];
   MATCH_ACCEPT_TAC K4LR_or_left_th]);;

let K4LR_or_assoc_left_th = prove
 (`!p q r. |~ (p || (q || r) --> (p || q) || r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K4LR_disj_imp] THEN
  MESON_TAC[K4LR_or_left_th; K4LR_or_right_th; K4LR_imp_trans]);;

let K4LR_or_assoc_right_th = prove
 (`!p q r. |~ ((p || q) || r --> p || (q || r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K4LR_disj_imp] THEN
  MESON_TAC[K4LR_or_left_th; K4LR_or_right_th; K4LR_imp_trans]);;

let K4LR_or_assoc_th = prove
 (`!p q r. |~ (p || (q || r) <-> (p || q) || r)`,
  REWRITE_TAC[K4LR_iff_def; K4LR_or_assoc_left_th; K4LR_or_assoc_right_th]);;

let K4LR_and_or_ldistrib_th = prove
 (`!p q r. |~ (p && (q || r) <-> p && q || p && r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[K4LR_iff_def; K4LR_disj_imp] THEN
  REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC K4LR_and_intro) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC K4LR_ante_conj THENL
  [MATCH_MP_TAC K4LR_imp_swap THEN REWRITE_TAC[K4LR_disj_imp] THEN
  CONJ_TAC THEN MATCH_MP_TAC K4LR_imp_swap THEN MATCH_MP_TAC K4LR_shunt THENL
   [MATCH_ACCEPT_TAC K4LR_or_right_th; MATCH_ACCEPT_TAC K4LR_or_left_th];
   MATCH_ACCEPT_TAC K4LR_axiom_addimp;
   MATCH_MP_TAC K4LR_add_assum THEN MATCH_ACCEPT_TAC K4LR_or_right_th;
   MATCH_ACCEPT_TAC K4LR_axiom_addimp;
   MATCH_MP_TAC K4LR_add_assum THEN MATCH_ACCEPT_TAC K4LR_or_left_th]);;

let K4LR_not_true_th = prove
 (`|~ (Not True <-> False)`,
  REWRITE_TAC[K4LR_iff_def; K4LR_ex_falso_th; GSYM K4LR_not_def] THEN
  MATCH_MP_TAC K4LR_iff_mp THEN EXISTS_TAC `True` THEN
  REWRITE_TAC[K4LR_truth_th] THEN ONCE_REWRITE_TAC[K4LR_iff_sym] THEN
  MATCH_ACCEPT_TAC K4LR_not_not_th);;

let K4LR_and_subst_right_th = prove
 (`!p q1 q2. |~ ((q1 <-> q2) --> (p && q1 <-> p && q2))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_imp_trans THEN
  EXISTS_TAC `(p && q1 --> p && q2) && (p && q2 --> p && q1)` THEN
  CONJ_TAC THENL
  [ALL_TAC;
   MATCH_MP_TAC K4LR_iff_imp2 THEN MATCH_ACCEPT_TAC K4LR_iff_def_th] THEN
  SUBGOAL_THEN `!p q1 q2. |~ ((q1 <-> q2) --> (p && q1 --> p && q2))`
    (fun th -> MATCH_MP_TAC K4LR_and_intro THEN
      MESON_TAC[th; K4LR_and_comm_th; K4LR_imp_trans; K4LR_iff_def_th;
                K4LR_iff_imp1; K4LR_iff_imp2]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_shunt THEN
  MATCH_MP_TAC K4LR_and_intro THEN CONJ_TAC THENL
  [MESON_TAC[K4LR_and_left_th; K4LR_and_right_th; K4LR_imp_trans];
   ALL_TAC] THEN
  MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `(q1 <-> q2) && q1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_and_intro THEN REWRITE_TAC[K4LR_and_left_th] THEN
   MESON_TAC[K4LR_and_right_th; K4LR_imp_trans];
   MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `(q1 --> q2) && q1` THEN
   REWRITE_TAC[K4LR_modusponens_th] THEN MATCH_MP_TAC K4LR_and_intro THEN
   REWRITE_TAC[K4LR_and_right_th] THEN MATCH_MP_TAC K4LR_imp_trans THEN
   EXISTS_TAC `(q1 <-> q2)` THEN REWRITE_TAC[K4LR_and_left_th] THEN
   MATCH_MP_TAC K4LR_imp_trans THEN
   EXISTS_TAC `(q1 --> q2) && (q2 --> q1)` THEN
   REWRITE_TAC[K4LR_and_left_th] THEN MATCH_MP_TAC K4LR_iff_imp1 THEN
   MATCH_ACCEPT_TAC K4LR_iff_def_th]);;

let K4LR_and_subst_left_th = prove
 (`!p1 p2 q. |~ ((p1 <-> p2) --> (p1 && q <-> p2 && q))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_imp_trans THEN
  EXISTS_TAC `(p1 && q --> p2 && q) && (p2 && q --> p1 && q)` THEN
  CONJ_TAC THENL
  [ALL_TAC;
   MATCH_MP_TAC K4LR_iff_imp2 THEN MATCH_ACCEPT_TAC K4LR_iff_def_th] THEN
  SUBGOAL_THEN `!p1 p2 q. |~ ((p1 <-> p2) --> (p1 && q --> p2 && q))`
    (fun th -> MATCH_MP_TAC K4LR_and_intro THEN
      MESON_TAC[th; K4LR_and_comm_th; K4LR_imp_trans; K4LR_iff_def_th;
                K4LR_iff_imp1; K4LR_iff_imp2]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_shunt THEN MATCH_MP_TAC
  K4LR_and_intro THEN CONJ_TAC THENL
  [ALL_TAC;
   MESON_TAC[K4LR_and_left_th; K4LR_and_right_th; K4LR_imp_trans]] THEN
  MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `(p1 <-> p2) && p1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_and_intro THEN REWRITE_TAC[K4LR_and_left_th] THEN
   MESON_TAC[K4LR_and_right_th; K4LR_and_left_th; K4LR_imp_trans];
   MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `(p1 --> p2) && p1` THEN
   REWRITE_TAC[K4LR_modusponens_th] THEN MATCH_MP_TAC K4LR_and_intro THEN
   REWRITE_TAC[K4LR_and_right_th] THEN MATCH_MP_TAC K4LR_imp_trans THEN
   EXISTS_TAC `(p1 <-> p2)` THEN REWRITE_TAC[K4LR_and_left_th] THEN
   MATCH_MP_TAC K4LR_imp_trans THEN
   EXISTS_TAC `(p1 --> p2) && (p2 --> p1)` THEN
   REWRITE_TAC[K4LR_and_left_th] THEN MATCH_MP_TAC K4LR_iff_imp1 THEN
   MATCH_ACCEPT_TAC K4LR_iff_def_th]);;

let K4LR_contrapos_th = prove
 (`!p q. |~ ((p --> q) --> (Not q --> Not p))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_imp_swap THEN
  MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `(q --> False)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_iff_imp1 THEN MATCH_ACCEPT_TAC K4LR_axiom_not;
   MATCH_MP_TAC K4LR_shunt THEN MATCH_MP_TAC K4LR_imp_trans THEN
   EXISTS_TAC `p --> False` THEN CONJ_TAC THENL
   [MESON_TAC[K4LR_ante_conj; K4LR_imp_trans_th];
    MESON_TAC[K4LR_axiom_not; K4LR_iff_imp2]]]);;

let K4LR_contrapos_eq_th = prove
 (`!p q. |~ ((p --> q) <-> (Not q --> Not p))`,
  SUBGOAL_THEN `!p q. |~ ((Not q --> Not p) --> (p --> q))`
    (fun th -> MESON_TAC[th; K4LR_iff_def; K4LR_contrapos_th]) THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC K4LR_imp_trans THEN
  EXISTS_TAC `Not (Not p) --> Not (Not q)` THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC K4LR_contrapos_th; ALL_TAC] THEN
  MATCH_MP_TAC K4LR_iff_imp1 THEN MATCH_MP_TAC K4LR_imp_subst THEN
  MESON_TAC[K4LR_not_not_th]);;

let K4LR_iff_sym_th = prove
 (`!p q. |~ ((p <-> q) --> (q <-> p))`,
  REPEAT  GEN_TAC THEN MATCH_MP_TAC K4LR_imp_trans THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN CONJ_TAC THENL
  [MESON_TAC[K4LR_iff_def_th; K4LR_iff_imp1]; ALL_TAC] THEN
  MATCH_MP_TAC K4LR_imp_trans THEN EXISTS_TAC `(q --> p) && (p --> q)` THEN
  CONJ_TAC THENL
  [MESON_TAC[K4LR_and_comm_th; K4LR_iff_imp1];
   MESON_TAC[K4LR_iff_def_th; K4LR_iff_imp2]]);;

let K4LR_de_morgan_or_th = prove
 (`!p q. |~ (Not (p || q) <-> Not p && Not q)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_iff_trans THEN
  EXISTS_TAC `Not (Not (Not p && Not q))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_not_subst THEN MATCH_ACCEPT_TAC K4LR_axiom_or;
   MATCH_ACCEPT_TAC K4LR_not_not_th]);;

let K4LR_crysippus_th = prove
 (`!p q. |~ (Not (p --> q) <-> p && Not q)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC K4LR_iff_trans THEN
  EXISTS_TAC `(p --> Not q --> False) --> False` THEN CONJ_TAC THENL
  [ALL_TAC; MESON_TAC[K4LR_axiom_and; K4LR_iff_sym]] THEN
  MATCH_MP_TAC K4LR_iff_trans THEN
  EXISTS_TAC `Not (p --> Not q --> False)` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_ACCEPT_TAC K4LR_axiom_not] THEN
  MATCH_MP_TAC K4LR_not_subst THEN MATCH_MP_TAC K4LR_imp_subst THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC K4LR_iff_refl_th; ALL_TAC] THEN
  MATCH_MP_TAC K4LR_iff_trans THEN EXISTS_TAC `Not (Not q)` THEN
  CONJ_TAC THENL
  [MESON_TAC[K4LR_not_not_th; K4LR_iff_sym];
   MATCH_ACCEPT_TAC K4LR_axiom_not]);;

let K4LR_frege_th = prove
 (`!p q r. |~ (p --> q --> r) ==> |~((p --> q) --> (p --> r))`,
  MESON_TAC[K4LR_axiom_distribimp; K4LR_modusponens]);;

(* ------------------------------------------------------------------------- *)
(* K4LR C= GL                                                                *)
(* ------------------------------------------------------------------------- *)

let GL_proves_K4LRaxioms = prove
 (`!p. K4LRaxiom p ==> |-- p`,
  MATCH_MP_TAC K4LRaxiom_INDUCT THEN
  MESON_TAC[GLproves_RULES; GLaxiom_RULES; GL_schema_4]);;

let GL_proves_Lob_rule = prove
 (`!p. |-- (Box p --> p) ==> |-- p`,
  MESON_TAC[GL_necessitation; GL_modusponens; GL_axiom_lob]);;

let K4LRproves_subset_GLproves = prove
 (`!p. |~ p ==> |-- p`,
  MATCH_MP_TAC K4LRproves_INDUCT THEN
  MESON_TAC[GL_proves_K4LRaxioms; GL_modusponens;
            GL_necessitation; GL_proves_Lob_rule]);;

(* ------------------------------------------------------------------------- *)
(* GL C= K4LR                                                                *)
(* ------------------------------------------------------------------------- *)

let K4LR_proves_Lob_axiom = prove
 (`!p. |~ (Box (Box p --> p) --> Box p)`,
  GEN_TAC THEN MATCH_MP_TAC K4LR_lobrule THEN MATCH_MP_TAC K4LR_imp_trans THEN
  EXISTS_TAC `Box (Box p --> p) --> Box (Box p)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC K4LR_imp_swap THEN MATCH_MP_TAC K4LR_imp_trans THEN
   EXISTS_TAC `Box(Box(Box p --> p))` THEN CONJ_TAC THENL
   [MESON_TAC[K4LR_axiom_4];
    MATCH_MP_TAC K4LR_imp_swap THEN MESON_TAC[K4LR_axiom_boximp]];
   MATCH_MP_TAC K4LR_frege_th THEN MESON_TAC[K4LR_axiom_boximp]]);;

let K4LR_proves_GLaxioms = prove
 (`!p. GLaxiom p ==> |~ p`,
  MATCH_MP_TAC GLaxiom_INDUCT THEN
  MESON_TAC[K4LRproves_RULES; K4LRaxiom_RULES; K4LR_proves_Lob_axiom]);;

let GLproves_subset_K4LRproves = prove
 (`!p. |-- p ==> |~ p`,
  MATCH_MP_TAC GLproves_INDUCT THEN
  MESON_TAC[K4LR_proves_GLaxioms; K4LR_modusponens;
            K4LR_necessitation; K4LR_proves_Lob_axiom]);;

(* ------------------------------------------------------------------------- *)
(* GL = K4LR                                                                 *)
(* ------------------------------------------------------------------------- *)

let GL_equiv_K4LR = prove
 (`!p. |-- p <=> |~ p`,
  MESON_TAC[GLproves_subset_K4LRproves; K4LRproves_subset_GLproves]);;
