(* ---------------------------------------------------------------------- *)
(*  List                                                                  *)
(* ---------------------------------------------------------------------- *)

let NOT_NIL = prove_by_refinement(
  `!l. ~(l = []) <=> ?(h:A) t. l = CONS h t`,
(* {{{ Proof *)

[
  STRIP_TAC THEN EQ_TAC;
  MESON_TAC[list_CASES];
  STRIP_TAC;
  ASM_MESON_TAC[NOT_CONS_NIL];
]);;

(* }}} *)

let LIST_REWRITES = ref [
NOT_CONS_NIL;
HD;
TL;
CONS_11;
LENGTH;
LAST;
list_CASES;
NOT_NIL;
];;

let LIST_SIMP_TAC = REWRITE_TAC (
  !LIST_REWRITES
);;

let extend_list_rewrites l =
  LIST_REWRITES := !LIST_REWRITES @ l;;

BASIC_REWRITES := !LIST_REWRITES @ !BASIC_REWRITES;;
