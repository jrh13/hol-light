(* ========================================================================= *)
(* Some tests.                                                               *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* ========================================================================= *)

let SORT_BOX_TAC     = Rule_gl.SORT_BOX_TAC;;
let BOX_RIGHT_TAC    = Rule_gl.BOX_RIGHT_TAC;;
let GL_RIGHT_TAC     = Rule_gl.GL_RIGHT_TAC;;
let GL_STEP_TAC      = Rule_gl.GL_STEP_TAC;;
let INNER_GL_TAC     = Rule_gl.INNER_GL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Example of countermodel.                                                  *)
(* There exists an arithmetical sentece p such that it is consistent with PA *)
(* that both p is undecidable and it is provable that p is decidable         *)
(* ------------------------------------------------------------------------- *)

g `!p . |-- (Box (Box p || Box (Not p)) --> (Box p || Box (Not p)))`;;
e GL_TAC;;
!the_gl_countermodel;;

(* CPU time (user): 2.80908 *)
let test_prove tm =
  try prove(tm,GL_TAC) with Failure _ -> failwith (string_of_term tm)
in
time (map test_prove)
 [`!p. |-- (Not (Box p) && Box (Box p --> p)
            --> Diam (Not p && Box p && (Box p --> p) && Box (Box p --> p)))`;
  `!p q. |-- (Box (q <-> (Box q --> p)) --> (Box (Box p --> p) --> Box p))`;
  `!p. |-- (Box (Box p --> p) <-> Box p)`;
  `!p. |-- (Dotbox (Box p) <-> Box p)`;
  `!p. |-- (Dotbox (Box p) <-> Box (Dotbox p))`;
  `!p. |-- (Dotbox p <-> (Dotbox (Dotbox p)))`;
  `!p q. |-- (Diam p && Box q --> Diam (p && q))`;
  `!p q. |-- (Box (p && q) --> Box p && Box q)`;
  `!p. |-- (Box (Box p --> p) <-> Box (Box p && p))`;
  `|-- (Box (Diam False) --> Box False)`;
  `!p. |-- (Box (p <-> Box p) <-> Box (p <-> True))`;
  `!p. |-- (Box (p <-> Box p) --> Box (p <-> True))`;
  `!p. |-- (Box (p <-> True) --> Box (p <-> Box p))`;
  `!p. |-- (Box (p <-> Not (Box p)) <-> Box (p <-> Not (Box False)))`;
  `!p. |-- (Box (p <-> Box (Not p)) <-> Box (p <-> (Box False)))`;
  `!p. |-- (Box (p <-> Not (Box (Not p))) <-> Box (p <-> False))`;
  `!p. |-- (Box ((Box p --> p) --> Not (Box (Box False)))
            -->  Box (Box False))`];;

(* ------------------------------------------------------------------------- *)
(* Further tests.                                                            *)
(* ------------------------------------------------------------------------- *)

(* CPU time (user): 7.212676 *)
let gl_theorems =
 [("GL_Godel_sentence_equiconsistent_consistency",
   `Box (p <-> Not Box p) <-> Box (p <-> Not Box False)`);
  ("GL_PA_ignorance", `Box False <-> Box Diam p`);
  ("GL_PA_undecidability_of_consistency",
   `Not Box Box False --> Not Box Not Box False && Not Box Not Not Box False`);
  ("GL_and_assoc_th", `(p && q) && r <-> p && q && r`);
  ("GL_and_comm_th", `p && q <-> q && p`);
  ("GL_and_left_th", `p && q --> p`);
  ("GL_and_left_true_th", `True && p <-> p`);
  ("GL_and_or_ldistrib_th", `p && (q || r) <-> p && q || p && r`);
  ("GL_and_pair_th", `p --> q --> p && q`);
  ("GL_and_right_th", `p && q --> q`);
  ("GL_and_rigth_true_th", `p && True <-> p`);
  ("GL_and_subst_left_th", `(p1 <-> p2) --> (p1 && q <-> p2 && q)`);
  ("GL_and_subst_right_th", `(q1 <-> q2) --> (p && q1 <-> p && q2)`);
  ("GL_arithmetical_fixpoint",
   `Dotbox (p <-> Not Box (q --> p)) <-> Dotbox (p <-> Diam q)`);
  ("GL_axiom_addimp", `p --> q --> p`);
  ("GL_axiom_and", `p && q <-> (p --> q --> False) --> False`);
  ("GL_axiom_boximp", `Box (p --> q) --> Box p --> Box q`);
  ("GL_axiom_distribimp", `(p --> q --> r) --> (p --> q) --> p --> r`);
  ("GL_axiom_doubleneg", `((p --> False) --> False) --> p`);
  ("GL_axiom_iffimp1", `(p <-> q) --> p --> q`);
  ("GL_axiom_iffimp2", `(p <-> q) --> q --> p`);
  ("GL_axiom_impiff", `(p --> q) --> (q --> p) --> (p <-> q)`);
  ("GL_axiom_lob", `Box (Box p --> p) --> Box p`);
  ("GL_axiom_not", `Not p <-> p --> False`);
  ("GL_axiom_or", `p || q <-> Not (Not p && Not q)`);
  ("GL_axiom_true", `True <-> False --> False`);
  ("GL_box_and_inv_th", `Box p && Box q --> Box (p && q)`);
  ("GL_box_and_th", `Box (p && q) --> Box p && Box q`);
  ("GL_box_iff_th", `Box (p <-> q) --> (Box p <-> Box q)`);
  ("GL_contrapos_eq_th", `p --> q <-> Not q --> Not p`);
  ("GL_contrapos_th", `(p --> q) --> Not q --> Not p`);
  ("GL_crysippus_th", `Not (p --> q) <-> p && Not q`);
  ("GL_de_morgan_and_th", `Not (p && q) <-> Not p || Not q`);
  ("GL_de_morgan_or_th", `Not (p || q) <-> Not p && Not q`);
  ("GL_dot_box", `Box p --> Box p && Box Box p`);
  ("GL_ex_falso_th", `False --> p`);
  ("GL_iff_def_th", `(p <-> q) <-> (p --> q) && (q --> p)`);
  ("GL_iff_refl_th", `p <-> p`);
  ("GL_iff_sym_th", `(p <-> q) --> (q <-> p)`);
  ("GL_imp_contr_th", `(p --> False) --> p --> q`);
  ("GL_imp_mono_th", `(p' --> p) && (q --> q') --> (p --> q) --> p' --> q'`);
  ("GL_imp_refl_th", `p --> p`);
  ("GL_imp_swap_th", `(p --> q --> r) --> q --> p --> r`);
  ("GL_imp_trans_th", `(q --> r) --> (p --> q) --> p --> r`);
  ("GL_imp_truefalse_th", `(q --> False) --> p --> (p --> q) --> False`);
  ("GL_modusponens_th", `(p --> q) && p --> q`);
  ("GL_nc_th", `p && Not p --> False`);
  ("GL_not_not_false_th", `(p --> False) --> False <-> p`);
  ("GL_not_not_th", `Not Not p <-> p`);
  ("GL_not_true_th", `Not True <-> False`);
  ("GL_or_assoc_left_th", `p || q || r --> (p || q) || r`);
  ("GL_or_assoc_right_th", `(p || q) || r --> p || q || r`);
  ("GL_or_assoc_th", `p || q || r <-> (p || q) || r`);
  ("GL_or_left_th", `q --> p || q`); ("GL_or_lid_th", `False || p <-> p`);
  ("GL_or_rid_th", `p || False <-> p`); ("GL_or_right_th", `p --> p || q`);
  ("GL_reflection_and_iterated_consistency",
   `Box ((Box p --> p) --> Diam Diam True) -->
    Diam Diam True -->
    Box p -->
    p`);
  ("GL_schema_4", `Box p --> Box Box p`);
  ("GL_second_incompleteness_theorem",
   `Not Box False --> Not Box Diam True`);
  ("GL_tnd_th", `p || Not p`); ("GL_truth_th", `True`);
  ("GL_undecidability_of_Godels_formula",
   `Box (p <-> Not Box p) && Not Box Box False -->
    Not Box p && Not Box Not p`);
  ("GL_undecidability_of_godels_formula",
   `Box (p <-> Not Box p) && Not Box Box False -->
    Not Box p && Not Box Not p`)] in
let test_prove (s,tm) =
  let th = try GL_RULE (mk_comb(`|--`,tm))
           with Failure _ -> failwith s in
  s,th in
time (map test_prove) gl_theorems;;

(* ------------------------------------------------------------------------- *)
(* Further tests.                                                            *)
(* ------------------------------------------------------------------------- *)

(* CPU time (user): 20.190578 *)
g `!p q. |-- ( Dotbox (p <-> (q && (Box (p --> q) --> Box Not p))) <->
               Dotbox (p <-> (q && Box Not q)) )`;;
time e GL_TAC;;
top_thm();;

(* CPU time (user): 279.073357 *)
(* About 5 min. *)
g `!p q.
     |-- ( Dotbox (p <-> (Diam p --> q && Not Box (p --> q))) <->
           Dotbox (p <-> (Diam True --> q && Not Box (Box False --> q))) )`;;
time e GL_TAC;;
top_thm();;
