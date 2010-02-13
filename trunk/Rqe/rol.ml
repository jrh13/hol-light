(* ---------------------------------------------------------------------- *)
(*  Util                                                                  *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(*  Real Ordered Lists                                                    *)
(* ---------------------------------------------------------------------- *)

let real_ordered_list = new_recursive_definition list_RECURSION
  `(real_ordered_list [] <=> T) /\
   (real_ordered_list (CONS h t) <=>
      real_ordered_list t /\
      ((t = []) \/ (h < HD t)))`;;

let ROL_EMPTY = EQT_ELIM (CONJUNCT1 real_ordered_list);;

let ROL_SING = prove_by_refinement(
  `!x. real_ordered_list [x]`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_ordered_list];
]);;
(* }}} *)

let ROL_TAIL = prove(
  `!l. ~(l = []) /\ real_ordered_list l ==> real_ordered_list (TL l)`,
(* {{{ Proof *)
  LIST_INDUCT_TAC THEN
  MESON_TAC[real_ordered_list;TL];
);;
(* }}} *)

let EL_CONS = prove_by_refinement(
  `!l h n. EL n t = EL (SUC n) (CONS h t)`,
(* {{{ Proof *)
[
  MESON_TAC[TL;EL];
]);;
(* }}} *)

let NOT_ROL = prove_by_refinement(
  `!l. ~(real_ordered_list l) ==> ?n. EL n l >= EL (SUC n) l`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[real_ordered_list];
  REWRITE_TAC[real_ordered_list;DE_MORGAN_THM];
  STRIP_TAC;
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> MP_TAC (MATCH_MP y x)));
  STRIP_TAC;
  EXISTS_TAC `SUC n`;
  ASM_MESON_TAC[EL_CONS];
  EXISTS_TAC `0`;
  REWRITE_TAC[EL;HD;TL;real_ge];
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;

(* }}} *)

let ROL_CONS = prove_by_refinement(
  `!h t. real_ordered_list (CONS h t) ==> real_ordered_list t`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_ordered_list];
  REPEAT STRIP_TAC;
]);;
(* }}} *)

let ROL_CONS_CONS = prove_by_refinement(
  `!h t. real_ordered_list (CONS h1 (CONS h2 t)) <=>
     real_ordered_list (CONS h2 t) /\ h1 < h2`,
(* {{{ Proof *)

[
  REPEAT GEN_TAC;
  EQ_TAC;
  REWRITE_TAC[real_ordered_list];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL;HD];
  ASM_MESON_TAC[NOT_CONS_NIL];
  ASM_MESON_TAC[HD];
  ASM_MESON_TAC[NOT_CONS_NIL];
  ASM_MESON_TAC[HD];
  REWRITE_TAC[real_ordered_list];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL;HD];
]);;

(* }}} *)

let ROL_APPEND = prove_by_refinement(
  `!l1 l2. real_ordered_list (APPEND l1 l2) ==>
    real_ordered_list l1 /\ real_ordered_list l2`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  MESON_TAC[APPEND;real_ordered_list];
  GEN_TAC;
  REWRITE_TAC[APPEND];
  STRIP_TAC;
  CLAIM `real_ordered_list (APPEND t l2)`;
  ASM_MESON_TAC[ROL_CONS];
  STRIP_TAC;
  CLAIM `real_ordered_list t /\ real_ordered_list l2`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  CASES_ON `t = []`;
  ASM_MESON_TAC[real_ordered_list];
  POP_ASSUM MP_TAC;
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC;
  ASM_REWRITE_TAC[ROL_CONS_CONS];
  CONJ_TAC;
  ASM_MESON_TAC[];
  LABEL_ALL_TAC;
  USE_THEN "Z-4" MP_TAC;
  POP_ASSUM SUBST1_TAC;
  REWRITE_TAC[APPEND];
  ASM_MESON_TAC[ROL_CONS_CONS];
]);;

(* }}} *)

let ROL_CONS_CONS_LT = prove_by_refinement(
  `!h1 h2 t. real_ordered_list (CONS h1 (CONS h2 t)) ==> h1 < h2`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_ordered_list];
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[NOT_CONS_NIL;HD];
]);;
(* }}} *)

let ROL_INSERT_THM = prove_by_refinement(
  `!x l1 l2.
    real_ordered_list l1 /\ real_ordered_list l2 /\
    ~(l1 = []) /\ ~(l2 = []) /\ LAST l1 < x /\ x < HD l2 ==>
      real_ordered_list (APPEND l1 (CONS x l2))`,
(* {{{ Proof *)

[
  GEN_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[APPEND];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[APPEND;LAST_SING;NOT_CONS_NIL];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[ROL_CONS_CONS;real_ordered_list];
  POP_ASSUM MP_TAC;
  REWRITE_TAC[NOT_NIL];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  CLAIM `real_ordered_list (APPEND t (CONS x l2))`;
  REWRITE_ASSUMS[TAUT `(p ==> q ==> r) <=> (p /\ q ==> r)`];
  FIRST_ASSUM MATCH_MP_TAC;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[ROL_CONS];
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  ASM_MESON_TAC[NOT_CONS_NIL];
  ASM_MESON_TAC[NOT_CONS_NIL];
  ASM_MESON_TAC[LAST_CONS;NOT_CONS_NIL];
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  ASM_REWRITE_TAC[];
  LABEL_ALL_TAC;
  USE_THEN "Z-3" (SUBST1_TAC o GSYM);
  REWRITE_TAC[APPEND];
  STRIP_TAC;
  REWRITE_TAC[ROL_CONS_CONS];
  STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  ASM_MESON_TAC[ROL_CONS_CONS];
]);;

(* }}} *)

let ROL_INSERT_FRONT_THM = prove_by_refinement(
  `!x l. real_ordered_list l /\ ~(l = []) /\ x < HD l ==>
    real_ordered_list (CONS x l)`,
(* {{{ Proof *)

[
  REWRITE_TAC[NOT_NIL;AND_IMP_THM];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[ROL_CONS_CONS;HD];
]);;

(* }}} *)

let ROL_CONS_CONS_DELETE = prove_by_refinement(
  `!h1 h2 t. real_ordered_list (CONS h1 (CONS h2 t)) ==>
     real_ordered_list (CONS h1 t)`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_ordered_list];
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
  ASM_MESON_TAC[NOT_CONS_NIL];
  REWRITE_ASSUMS[HD];
  ASM_MESON_TAC[REAL_LT_TRANS];
]);;
(* }}} *)

let LAST_CONS_LT = prove_by_refinement(
  `!x t h. real_ordered_list (CONS h t) /\ LAST (CONS h t) < x ==> h < x`,
(* {{{ Proof *)

[
  GEN_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[LAST];
  REPEAT STRIP_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  CONJ_TAC;
  ASM_MESON_TAC[ROL_CONS_CONS_DELETE];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[LAST];
  ASM_MESON_TAC[LAST;ROL_CONS_CONS;REAL_LT_TRANS];
  ASM_MESON_TAC[LAST_CONS;ROL_CONS_CONS_DELETE;LAST_CONS_CONS];
]);;

(* }}} *)

let ROL_INSERT_BACK_THM = prove_by_refinement(
  `!x l. real_ordered_list l /\ ~(l = []) /\ LAST l < x ==>
    real_ordered_list (APPEND l [x])`,
(* {{{ Proof *)

[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[APPEND;ROL_SING];
  LABEL_ALL_TAC;
  STRIP_TAC;
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[APPEND;ROL_CONS_CONS;ROL_SING];
  ASM_MESON_TAC[LAST;COND_CLAUSES];
  PROVE_ASSUM_ANTECEDENT_TAC 0;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[ROL_CONS];
  ASM_MESON_TAC[];
  ASM_MESON_TAC[LAST_CONS];
  REWRITE_TAC[APPEND];
  REWRITE_TAC[real_ordered_list];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  DISJ2_TAC;
  REWRITE_ASSUMS[NOT_NIL];
  LABEL_ALL_TAC;
  USE_IASSUM 2 MP_TAC;
  STRIP_TAC;
  ASM_REWRITE_TAC[HD_APPEND];
  ASM_MESON_TAC[ROL_CONS_CONS];
]);;

(* }}} *)

(*
  CHOP_REAL_LIST 1 `[&1; &2; &3]` --> |- [&1; &2; &3] = APPEND [&1; &2] [&3]
  let n,l = 1,`[&1; &2; &3]`
*)
let CHOP_REAL_LIST n l =
  let l' = dest_list l in
  let l1',l2' = chop_list n l' in
  let l1,l2 = mk_list (l1',real_ty),mk_list (l2',real_ty) in
  let tm = mk_binop rappend l1 l2 in
    GSYM (REWRITE_CONV [APPEND] tm);;


(*
  ROL_CHOP_LT 2
  let n = 1
*)
let ROL_CHOP_LT n thm =
  let thm' = funpow (n - 1) (MATCH_MP ROL_CONS) thm in
    CONJUNCT2 (PURE_REWRITE_RULE[ROL_CONS_CONS] thm');;

let t1 = prove_by_refinement(
  `real_ordered_list [&1; &2; &3; &4]`,
[
  REWRITE_TAC[HD;real_ordered_list];
  REAL_ARITH_TAC;
]);;

(*
ROL_CHOP_LIST 2 |- real_ordered_list [&1; &2; &3; &4] -->
                   |- real_ordered_list [&1; &2; &3],
                   |- real_ordered_list [&4],
                   |- &3 < &4
let thm = ASSUME `real_ordered_list [&1; &2; &3; &4]`
let n = 2
ROL_CHOP_LIST 2 thm
*)
let ROL_CHOP_LIST n thm =
  let _,l = dest_comb (concl thm) in
  let lthm = CHOP_REAL_LIST n l in
  let thm' = REWRITE_RULE[lthm] thm in
  let thm'' = MATCH_MP ROL_APPEND thm' in
  let [lthm;rthm] = CONJUNCTS thm'' in
  let lt_thm = ROL_CHOP_LT n thm in
    lthm,rthm,lt_thm;;

(*
rol_insert (|- x1 < x4 /\ x4 < x2)
           (|- real_ordered_list [x1; x2; x3]) -->
  (|- real_ordered_list [x1; x4; x2; x3]);

rol_insert (|- &2 < &5 /\ &5 < &6) (|- real_ordered_list [&1; &2; &6]) -->
  (|- real_ordered_list [&1; &2; &5; &6]);

rol_insert (|- x4 < x1)
           (|- real_ordered_list [x1; x2; x3]) -->
  (|- real_ordered_list [x4; x1; x2; x3]);

rol_insert (|- x1 < x4)
           (|- real_ordered_list [x1; x2; x3]) -->
  (|- real_ordered_list [x1; x2; x3; x4]);
*)

let lem1 = prove(
  `!e x l. e < x /\ (LAST l = e) ==> LAST l < x`,
  MESON_TAC[]);;

let ROL_INSERT_MIDDLE place_thm rol_thm =
  let [pl1;pl2] = CONJUNCTS place_thm in
  let list = snd(dest_comb(concl rol_thm)) in
  let new_x,slot =
    let ltl,ltr = dest_conj (concl place_thm) in
    let x1,x4 = dest_binop rlt ltl in
    let _,x2 = dest_binop rlt ltr in
    let n = (index x1 (dest_list list)) + 1 in
      x4,n in
  let lthm,rthm,lt_thm = ROL_CHOP_LIST slot rol_thm in
  let llist = snd(dest_comb(concl lthm)) in
  let hllist = hd (dest_list llist) in
  let tllist = mk_rlist (tl (dest_list llist)) in
  let rlist = snd(dest_comb(concl rthm)) in
  let hrlist = hd (dest_list rlist) in
  let trlist = mk_rlist (tl (dest_list rlist)) in
  let gthm = REWRITE_RULE[AND_IMP_THM] ROL_INSERT_THM in
  let a1 = lthm in
  let a2 = rthm in
  let a3 = ISPECL [hllist;tllist] NOT_CONS_NIL in
  let a4 = ISPECL [hrlist;trlist] NOT_CONS_NIL in
  let l,r = dest_binop rlt (concl pl1) in
  let a5_aux = prove(mk_eq (mk_comb(rlast,llist),l),REWRITE_TAC[LAST;COND_CLAUSES;NOT_CONS_NIL]) in
  let a5 = MATCH_MPL [ISPECL [l;r;llist] (REWRITE_RULE[AND_IMP_THM] lem1);pl1;a5_aux] in
  let a6_aux = ISPECL [trlist;hrlist] (GEN_ALL HD) in
  let a6 = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV[GSYM a6_aux])) pl2 in
  let thm = MATCH_MPL [gthm;a1;a2;a3;a4;a5;a6] in
    REWRITE_RULE[APPEND] thm;;

(*
ROL_INSERT_MIDDLE (ASSUME `x1 < x4 /\ x4 < x2`)
                      (ASSUME `real_ordered_list [x1; x2; x3]`);;

ROL_INSERT_MIDDLE (ASSUME `x1 < x6 /\ x6 < x2`)
                      (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`);;

ROL_INSERT_MIDDLE (ASSUME `x2 < x6 /\ x6 < x3`)
                      (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`);;

ROL_INSERT_MIDDLE (ASSUME `x4 < x6 /\ x6 < x5`)
                      (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`);;

ROL_INSERT_MIDDLE (ASSUME `x2 < x4 /\ x4 < x3`)
                      (ASSUME `real_ordered_list [x1; x2; x3]`);;

*)


let ROL_INSERT_FRONT place_thm rol_thm =
  let _,rlist = dest_comb (concl rol_thm) in
  let h,t = hd (dest_list rlist),mk_rlist (tl (dest_list rlist)) in
  let imp_thm = ISPECL [h;t] (GSYM ROL_CONS_CONS) in
  let imp_thm' = REWRITE_RULE[AND_IMP_THM] (fst (EQ_IMP_RULE imp_thm)) in
    MATCH_MPL[imp_thm';rol_thm;place_thm];;

(*
ROL_INSERT_FRONT (ASSUME `x4 < x1`)
                     (ASSUME `real_ordered_list [x1; x2; x3]`);;
ROL_INSERT_FRONT (ASSUME `x4 < x1`)
                     (ASSUME `real_ordered_list [x1]`);;
*)

let ROL_INSERT_BACK place_thm rol_thm =
  let _,rlist = dest_comb (concl rol_thm) in
  let rlist' = dest_list rlist in
  let h,t = hd rlist',mk_rlist (tl rlist') in
  let lst = last rlist' in
  let b,x = dest_binop rlt (concl place_thm) in
  let imp_thm = REWRITE_RULE[AND_IMP_THM]
                  (ISPECL [x;rlist]  ROL_INSERT_BACK_THM) in
  let a1 = rol_thm in
  let a2 = ISPECL [h;t] NOT_CONS_NIL in
  let a3_aux = prove(mk_eq (mk_comb(rlast,rlist),lst),
                     REWRITE_TAC[LAST;COND_CLAUSES;NOT_CONS_NIL]) in
  let a3 = MATCH_MPL [ISPECL [lst;x;rlist]
                        (REWRITE_RULE[AND_IMP_THM] lem1);place_thm;a3_aux] in
    REWRITE_RULE[APPEND] (MATCH_MPL[imp_thm;a1;a2;a3]);;

(*
ROL_INSERT_BACK (ASSUME `x3 < x4`)
                (ASSUME `real_ordered_list [x1; x2; x3]`);;
*)

let ROL_INSERT place_thm rol_thm =
  let place_thm' = REWRITE_RULE[real_gt] place_thm in
  if is_conj (concl place_thm') then ROL_INSERT_MIDDLE place_thm' rol_thm
  else
    let _,rlist = dest_comb (concl rol_thm) in
    let rlist' = dest_list rlist in
    let h = hd rlist' in
    let l,r = dest_binop rlt (concl place_thm') in
      if r = h then ROL_INSERT_FRONT place_thm' rol_thm
      else ROL_INSERT_BACK place_thm' rol_thm;;

(*
let k00 = ROL_INSERT (ASSUME `x1 < x4 /\ x4 < x2`)
           (ASSUME `real_ordered_list [x1; x2; x3]`);;

rol_thms k00

PARTITION_LINE_CONV `[x1; x4; x2; x3:real]`

ROL_INSERT (ASSUME `x4 < x1`)
           (ASSUME `real_ordered_list [x1]`);;

ROL_INSERT (ASSUME `x3 < x4`)
           (ASSUME `real_ordered_list [x1; x2; x3]`);;

*)


(*
  rol_thms |- real_ordered_list [x;y;z]

  --->

  |- x < y; |- y < z

*)
let rol_thms rol_thm =
  let thm = REWRITE_RULE[real_ordered_list;NOT_CONS_NIL;HD] rol_thm in
    rev(CONJUNCTS thm);;
(*
let rol_thm = ASSUME `real_ordered_list [x;y;z]`
rol_thms rol_thm
*)

let lem = prove(`!x. ?y. y = x`,MESON_TAC[]);;

let rec interleave l1 l2 =
  match l1 with
      [] -> l2
    | h::t ->
        match l2 with
            [] -> l1
          | h1::t1 -> h::h1::(interleave t t1);;


let lem0 = prove(`?x:real. T`,MESON_TAC[]);;

let lem1 = prove_by_refinement(
  `!x. (?y. y < x) /\ (?y. y = x) /\ (?y. x < y)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  EXISTS_TAC `x - &1`;
  REAL_ARITH_TAC;
  MESON_TAC[];
  EXISTS_TAC `x + &1`;
  REAL_ARITH_TAC;
]);;
(* }}} *)

let rol_nonempty_thms rol_thm =
  let pts = dest_list (snd(dest_comb(concl rol_thm))) in
  if length pts = 0 then [lem0] else
  if length pts = 1 then CONJUNCTS (ISPEC (hd pts) lem1) else
  let rthms = rol_thms rol_thm in
  let pt_thms = map (C ISPEC lem) pts in
  let left_thm = ISPEC (hd pts) REAL_GT_EXISTS in
  let right_thm = ISPEC (last pts) REAL_LT_EXISTS in
  let int_thms = map (MATCH_MP REAL_DENSE) rthms in
  let thms = interleave pt_thms int_thms in
    left_thm::thms @ [right_thm];;


(*
  rol_nonempty_thms (ASSUME `real_ordered_list [y]`)
*)

let lem0 = prove_by_refinement(
  `real_ordered_list []`,
(* {{{ Proof *)
[REWRITE_TAC[real_ordered_list]]);;
(* }}} *)

let lem1 = prove_by_refinement(
  `!x y. x < y ==> real_ordered_list [x; y]`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_ordered_list;NOT_CONS_NIL;HD];
]);;
(* }}} *)

let lem2 = prove_by_refinement(
  `!x y. x < y ==> real_ordered_list (CONS y t) ==>
     real_ordered_list (CONS x (CONS y t))`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[real_ordered_list;NOT_CONS_NIL;HD;TL];
]);;
(* }}} *)

let mk_rol ord_thms =
  match ord_thms with
      [] -> lem0
    | [x] -> MATCH_MP lem1 x
    | h1::h2::rest ->
        itlist (fun x y -> MATCH_MPL[lem2;x;y]) (butlast ord_thms) (MATCH_MP lem1 (last ord_thms));;

(*
let k0 = rol_thms (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`)
mk_rol k0
*)

let real_nil = `[]:real list`;;
let ROL_NIL = prove(mk_comb (`real_ordered_list`,real_nil),REWRITE_TAC[real_ordered_list]);;

let ROL_REMOVE x rol_thm =
  let list = dest_list (snd (dest_comb (concl rol_thm))) in
  if length list = 0 then failwith "ROL_REMOVE: 0"
  else if length list = 1 then
    if x = hd list then ROL_NIL
    else failwith "ROL_REMOVE: Not an elem"
  else if length list = 2 then
    let l::r::[] = list in
      if l = x then ISPEC r ROL_SING
      else if r = x then ISPEC l ROL_SING
      else failwith "ROL_REMOVE: Not an elem"
  else
  let ord_thms = rol_thms rol_thm in
  let partition_fun thm =
    let l,r = dest_binop rlt (concl thm) in
      not (x = l) && not (x = r) in
  let ord_thms',elim_thms = partition partition_fun ord_thms in
  if length elim_thms = 1 then mk_rol ord_thms' else
  let [xy_thm; yz_thm] = elim_thms in
  let connect_thm = MATCH_MP REAL_LT_TRANS (CONJ xy_thm yz_thm) in
  let rec insert xz_thm thms =
    match thms with
        [] -> [connect_thm]
      | h::t ->
          let l,r = dest_binop rlt (concl h) in
          let l1,r1 = dest_binop rlt (concl xz_thm) in
          if (r1 = l) then xz_thm::h::t else h::insert xz_thm t in
  let ord_thms'' = insert connect_thm ord_thms' in
    mk_rol ord_thms'';;


(*
ROL_REMOVE `x1:real` (ASSUME `real_ordered_list [x1]`)
ROL_REMOVE `x1:real` (ASSUME `real_ordered_list [x1; x3]`)
ROL_REMOVE `x3:real` (ASSUME `real_ordered_list [x1; x3]`)
ROL_REMOVE `x3:real` (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`)
ROL_REMOVE `x1:real` (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`)
ROL_REMOVE `x5:real` (ASSUME `real_ordered_list [x1; x2; x3; x4; x5]`)

ROL_REMOVE `-- &1` (ASSUME `real_ordered_list [-- &1; &0; &1]`)
let rol_thm =  (ASSUME `real_ordered_list [-- &1; &0; &1]`)
let x = `&0`
*)

let lem = prove(
  `!y x. x < y \/ (x = y) \/ y < x`,
(* {{{ Proof *)
REAL_ARITH_TAC);;
(* }}} *)

let lem2 = prove(
  `!x y z. y < z ==> (y < x <=> (y < x /\ x < z) \/ (x = z) \/ z < x)`,
(* {{{ Proof *)
  REAL_ARITH_TAC);;
(* }}} *)


let ROL_COVERS rol_thm =
  let pts = dest_list (snd(dest_comb(concl rol_thm))) in
  if length pts = 1 then ISPEC (hd pts) lem else
  let thms = rol_thms rol_thm in
  let thms' = map (MATCH_MP lem2) thms in
  let base = ISPEC (hd pts) lem in
    itlist (fun x y -> ONCE_REWRITE_RULE[MATCH_MP lem2 x] y) (rev thms) base;;

(*
ROL_COVERS (ASSUME `real_ordered_list [x; y; z]`)
ROL_COVERS (ASSUME `real_ordered_list [x; y]`)
ROL_COVERS (ASSUME `real_ordered_list [x]`)

*)
