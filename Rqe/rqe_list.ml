
let aacons_tm = `CONS:A -> A list -> A list` ;;
let HD_CONV conv tm =
  let h::rest = dest_list tm in
  let ty = type_of h in
  let thm = conv h in
  let thm2 = REFL (mk_list(rest,ty)) in
  let cs = inst [ty,aty] aacons_tm in
    MK_COMB ((AP_TERM cs thm),thm2);;

let TL_CONV conv tm =
(*   try *)
    let h::t = dest_list tm in
    let lty = type_of h in
    let cs = inst [lty,aty] aacons_tm in
      MK_COMB ((AP_TERM cs (REFL h)), (LIST_CONV conv (mk_list(t,lty))))
(*   with _ -> failwith "TL_CONV" *)

let rec EL_CONV conv i tm =
  if i = 0 then HD_CONV conv tm
  else
    let h::t = dest_list tm in
    let lty = type_of h in
    let cs = inst [lty,aty] aacons_tm in
      MK_COMB ((AP_TERM cs (REFL h)), (EL_CONV conv (i - 1) (mk_list(t,lty))))


(*

  let conv = (REWRITE_CONV[ARITH_RULE `x + x = &2 * x`])
  let tm = `[&5 + &5; &6 + &6; &7 + &7]`
  HD_CONV conv tm
  TL_CONV conv tm
  HD_CONV(TL_CONV conv) tm
  CONS_CONV conv tm
  EL_CONV conv 0 tm
  EL_CONV conv 1 tm
  EL_CONV conv 2 tm

*)

let NOT_CONS = prove_by_refinement(
  `!l. (~ ?(h:A) t. (l = CONS h t)) ==> (l = [])`,
(* {{{ Proof *)

[
  MESON_TAC[list_CASES];
]);;

(* }}} *)

let REMOVE = new_recursive_definition list_RECURSION
  `(REMOVE x [] = []) /\
   (REMOVE x (CONS (h:A) t) =
     let rest = REMOVE x t in
       if x = h then rest else CONS h rest)`;;

let CHOP_LIST = new_recursive_definition num_RECURSION
  `(CHOP_LIST 0 l = [],l) /\
   (CHOP_LIST (SUC n) l =
     let a,b = CHOP_LIST n (TL l) in
      CONS (HD l) a,b)`;;

let REM_NIL = prove(
 `REMOVE x [] = []`,
 MESON_TAC[REMOVE]);;

let REM_FALSE = prove_by_refinement(
 `!x l. ~(MEM x (REMOVE x l))`,
(* {{{ Proof *)
[
 STRIP_TAC;
 LIST_INDUCT_TAC;
 ASM_MESON_TAC[MEM;REM_NIL];
 CASES_ON `x = h`;
 ASM_REWRITE_TAC[];
 ASM_REWRITE_TAC[REMOVE;LET_DEF;LET_END_DEF];
 ASM_MESON_TAC[];
 ASM_REWRITE_TAC[REMOVE;LET_DEF;LET_END_DEF];
 ASM_MESON_TAC[MEM];
]);;
(* }}} *)

let MEM_REMOVE = prove_by_refinement(
  `!x y z l. MEM x (REMOVE y l) ==> MEM x (REMOVE y (CONS z l))`,
(* {{{ Proof *)
[
  REPEAT_N 3 STRIP_TAC;
  CASES_ON `y = z`;
  ASM_REWRITE_TAC[REMOVE;LET_DEF;LET_END_DEF];
  ASM_REWRITE_TAC[REMOVE;LET_DEF;LET_END_DEF];
  ASM_MESON_TAC[MEM];
]);;
(* }}} *)

let REM_NEQ = prove_by_refinement(
  `!x x1 l. MEM x l /\ ~(x = x1) ==> MEM x (REMOVE x1 l)`,
(* {{{ Proof *)
[
  STRIP_TAC THEN STRIP_TAC;
  LIST_INDUCT_TAC;
  MESON_TAC[MEM];
  CASES_ON `x = h`;
  POP_ASSUM SUBST1_TAC;
  STRIP_TAC;
  ASM_REWRITE_TAC[REMOVE;LET_DEF;LET_END_DEF;COND_CLAUSES;MEM];
  STRIP_TAC;
  CLAIM `MEM x t`;
  ASM_MESON_TAC[MEM];
  STRIP_TAC;
  CLAIM `MEM x (REMOVE x1 t)`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  MATCH_MP_TAC MEM_REMOVE;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)


let LAST_SING = prove_by_refinement(
  `!h. LAST [h] = h`,
(* {{{ Proof *)

[
  MESON_TAC[LAST];
]);;

(* }}} *)

let LAST_CONS = prove_by_refinement(
  `!h t. ~(t = []) ==> (LAST (CONS h t) = LAST t)`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[LAST];
]);;
(* }}} *)


let LAST_CONS_CONS = prove_by_refinement(
  `!h1 h2 t. ~(t = []) ==> (LAST (CONS h1 (CONS h2 t)) = LAST (CONS h1 t))`,
(* {{{ Proof *)
[
  REWRITE_TAC[LAST;NOT_CONS_NIL];
  MESON_TAC[LAST;NOT_CONS_NIL;COND_CLAUSES];
]);;
(* }}} *)

let HD_APPEND = prove_by_refinement(
  `!h t l. HD (APPEND (CONS h t) l) = h`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[HD;APPEND];
]);;
(* }}} *)

let LENGTH_0 = prove_by_refinement(
  `!l. (LENGTH l = 0) <=> (l = [])`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH];
  ASM_MESON_TAC[LENGTH;NOT_CONS_NIL;ARITH_RULE `~(0 = SUC n)`];
]);;
(* }}} *)

let LENGTH_1 = prove_by_refinement(
  `!l. (LENGTH l = 1) <=> ?x. l = [x]`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  EQ_TAC;
  MESON_TAC[LENGTH;ARITH_RULE `~(1 = 0)`];
  MESON_TAC[NOT_CONS_NIL];
  EQ_TAC;
  REWRITE_TAC[LENGTH;ARITH_RULE `~(0 = 1)`];
  REWRITE_TAC[LENGTH];
  STRIP_TAC;
  CLAIM `LENGTH t = 0`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `t = []`;
  ASM_MESON_TAC[LENGTH_0];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  STRIP_TAC;
  ASM_MESON_TAC[LENGTH;ONE];
]);;
(* }}} *)

let LIST_TRI = prove_by_refinement(
  `!p. (p = []) \/ (?x. p = [x:A]) \/ (?x y t. p = CONS x (CONS y t))`,
(* {{{ Proof *)
[
  STRIP_TAC;
  DISJ_CASES_TAC (ISPEC `p:A list` list_CASES);
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  DISJ_CASES_TAC (ISPEC `t:A list` list_CASES);
  ASM_MESON_TAC[];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let LENGTH_PAIR = prove_by_refinement(
  `!p. (LENGTH p = 2) <=> ?h t. p = [h:A; t]`,
(* {{{ Proof *)
[
  STRIP_TAC THEN EQ_TAC;
  STRIP_TAC;
  MP_TAC (ISPEC `p:A list` list_CASES);
  STRIP_TAC;
  ASM_MESON_TAC[LENGTH_0;ARITH_RULE `~(2 = 0)`];
  MP_TAC (ISPEC `t:A list` list_CASES);
  STRIP_TAC;
  ASM_MESON_TAC[LENGTH_1;ARITH_RULE `~(1 = 2)`];
  MP_TAC (ISPEC `t':A list` list_CASES);
  STRIP_TAC;
  EXISTS_TAC `h:A`;
  EXISTS_TAC `h':A`;
  ASM_MESON_TAC[];
  CLAIM `p = CONS h (CONS h' (CONS h'' t''))`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `2 < LENGTH p`;
  POP_ASSUM SUBST1_TAC;
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  ASM_MESON_TAC[LT_REFL];
  STRIP_TAC;
  ASM_REWRITE_TAC[LENGTH];
  ARITH_TAC;
]);;
(* }}} *)

let LENGTH_SING = prove_by_refinement(
  `!p. (LENGTH p = 1) <=> ?h. p = [h:A]`,
(* {{{ Proof *)
[
  STRIP_TAC THEN EQ_TAC;
  STRIP_TAC;
  MP_TAC (ISPEC `p:A list` list_CASES);
  STRIP_TAC;
  ASM_MESON_TAC[LENGTH_0;ARITH_RULE `~(1 = 0)`];
  MP_TAC (ISPEC `t:A list` list_CASES);
  STRIP_TAC;
  EXISTS_TAC `h:A`;
  ASM_MESON_TAC[];
  CLAIM `p = CONS h (CONS h' t')`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `1 < LENGTH p`;
  POP_ASSUM SUBST1_TAC;
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  STRIP_TAC;
  ASM_REWRITE_TAC[LENGTH;];
  ARITH_TAC;
]);;
(* }}} *)

let TL_NIL = prove_by_refinement(
  `!l. ~(l = []) ==> ((TL l = []) <=> ?x. l = [x])`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC THEN EQ_TAC;
  CLAIM `?h t. l = CONS h t`;
  ASM_MESON_TAC[list_CASES];
  STRIP_TAC;
  ASM_REWRITE_TAC[TL];
  ASM_MESON_TAC !LIST_REWRITES;
  ASM_MESON_TAC !LIST_REWRITES;
]);;
(* }}} *)

let LAST_TL = prove_by_refinement(
  `!l. ~(l = []) /\  ~(TL l = []) ==> (LAST (TL l) = LAST l)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REWRITE_TAC[TL;LAST];
  ASM_MESON_TAC[NOT_CONS_NIL];
]);;
(* }}} *)

let LENGTH_TL = prove_by_refinement(
  `!l. ~(l = []) /\  ~(TL l = []) ==> (LENGTH (TL l) = PRE(LENGTH l))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REPEAT STRIP_TAC;
  LIST_SIMP_TAC;
  NUM_SIMP_TAC;
]);;
(* }}} *)

let LENGTH_NZ = prove_by_refinement(
 `!p. 0 < LENGTH p <=> ~(p = [])`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  EQ_TAC;
  ASM_MESON_TAC[LENGTH;NOT_CONS_NIL;LT_REFL];
  REWRITE_TAC[LENGTH;NOT_CONS_NIL;LT_REFL;NOT_NIL];
  STRIP_TAC THEN ASM_REWRITE_TAC[];
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
]);;
(* }}} *)
