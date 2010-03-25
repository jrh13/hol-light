(* ========================================================================= *)
(* Cantor's theorem.                                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Ad hoc version for whole type.                                            *)
(* ------------------------------------------------------------------------- *)

let CANTOR_THM_INJ = prove
 (`~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))`,
  REWRITE_TAC[INJECTIVE_LEFT_INVERSE; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:(A->bool)->A`; `g:A->(A->bool)`] THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. ~(g x x)`) THEN MESON_TAC[]);;

let CANTOR_THM_SURJ = prove
 (`~(?f:A->(A->bool). !s. ?x. f x = s)`,
  REWRITE_TAC[SURJECTIVE_RIGHT_INVERSE; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:A->(A->bool)`; `f:(A->bool)->A`] THEN
  DISCH_THEN(MP_TAC o SPEC `\x:A. ~(g x x)`) THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Proper version for any set, in terms of cardinality operators.            *)
(* ------------------------------------------------------------------------- *)

let CANTOR = prove
 (`!s:A->bool. s <_c {t | t SUBSET s}`,
  GEN_TAC THEN REWRITE_TAC[lt_c] THEN CONJ_TAC THENL
   [REWRITE_TAC[le_c] THEN EXISTS_TAC `(=):A->A->bool` THEN
    REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM; SUBSET; IN] THEN MESON_TAC[];
    REWRITE_TAC[LE_C; IN_ELIM_THM; SURJECTIVE_RIGHT_INVERSE] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `g:A->(A->bool)` THEN
    DISCH_THEN(MP_TAC o SPEC `\x:A. s(x) /\ ~(g x x)`) THEN
    REWRITE_TAC[SUBSET; IN; FUN_EQ_THM] THEN MESON_TAC[]]);;
