(* ========================================================================= *)
(* A "proof" of Pythagoras's theorem. Of course something similar is         *)
(* implicit in the definition of "norm", but maybe this is still nontrivial. *)
(* ========================================================================= *)

needs "Multivariate/misc.ml";;
needs "Multivariate/vectors.ml";;

(* ------------------------------------------------------------------------- *)
(* Direct vector proof (could replace 2 by N and the proof still runs).      *)
(* ------------------------------------------------------------------------- *)

let PYTHAGORAS = prove
 (`!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  REWRITE_TAC[NORM_POW_2; orthogonal; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* A more explicit and laborious "componentwise" specifically for 2-vectors. *)
(* ------------------------------------------------------------------------- *)

let PYTHAGORAS = prove
 (`!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  SIMP_TAC[NORM_POW_2; orthogonal; dot; SUM_2; DIMINDEX_2;
           VECTOR_SUB_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;
