
let matinsert_lem0 = prove_by_refinement(
  `!S. (!x. P x) ==> (!x. S x ==> P x)`,
(* {{{ Proof *)
  [MESON_TAC[]]);;
(* }}} *)
