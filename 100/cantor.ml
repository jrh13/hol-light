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

(* ------------------------------------------------------------------------- *)
(* More explicit "injective" version as in Paul Taylor's book.               *)
(* ------------------------------------------------------------------------- *)

let CANTOR_THM_INJ' = prove
 (`~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))`,
  STRIP_TAC THEN
  ABBREV_TAC `(g:A->A->bool) = \a. { b | !s. f(s) = a ==> b IN s}` THEN
  MP_TAC(ISPEC `g:A->A->bool`
   (REWRITE_RULE[NOT_EXISTS_THM] CANTOR_THM_SURJ)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Another sequence of versions (Lawvere, Cantor, Taylor) taken from         *)
(* http://ncatlab.org/nlab/show/Cantor%27s+theorem.                          *)
(* ------------------------------------------------------------------------- *)

let CANTOR_LAWVERE = prove
 (`!h:A->(A->B).
        (!f:A->B. ?x:A. h(x) = f) ==> !n:B->B. ?x. n(x) = x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g:A->B = \a. (n:B->B) (h a a)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM]) THEN
  ASM_MESON_TAC[]);;

let CANTOR = prove
 (`!f:A->(A->bool). ~(!s. ?x. f x = s)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CANTOR_LAWVERE) THEN
  DISCH_THEN(MP_TAC o SPEC `(~)`) THEN MESON_TAC[]);;

let CANTOR_TAYLOR = prove
 (`!f:(A->bool)->A. ~(!x y. f(x) = f(y) ==> x = y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\a:A.  { b:A | !s. f(s) = a ==> b IN s}`
   (REWRITE_RULE[NOT_EXISTS_THM] CANTOR)) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let SURJECTIVE_COMPOSE = prove
 (`(!y. ?x. f(x) = y) /\ (!z. ?y. g(y) = z)
   ==> (!z. ?x. (g o f) x = z)`,
  MESON_TAC[o_THM]);;

let INJECTIVE_SURJECTIVE_PREIMAGE = prove
 (`!f:A->B. (!x y. f(x) = f(y) ==> x = y) ==> !t. ?s. {x | f(x) IN s} = t`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `IMAGE (f:A->B) t` THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ASM_MESON_TAC[]);;

let CANTOR_JOHNSTONE = prove
 (`!i:B->S f:B->S->bool.
        ~((!x y. i(x) = i(y) ==> x = y) /\ (!s. ?z. f(z) = s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `(IMAGE (f:B->S->bool)) o (\s:S->bool. {x | i(x) IN s})`
    (REWRITE_RULE[NOT_EXISTS_THM] CANTOR)) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SURJECTIVE_COMPOSE THEN
  ASM_REWRITE_TAC[SURJECTIVE_IMAGE] THEN
  MATCH_MP_TAC INJECTIVE_SURJECTIVE_PREIMAGE THEN
  ASM_REWRITE_TAC[]);;
