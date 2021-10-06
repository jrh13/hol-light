(* ------------------------------------------------------------------------- *)
(* Evaluate a quantifier-free formula given a sign matrix row for its polys. *)
(* ------------------------------------------------------------------------- *)

(*
let rec testform pmat fm =
  match fm with
      Atom(R(a,[p;Fn("0",[])])) ->
        let s = assoc p pmat in
          if a = "=" then s = Zero
          else if a = "<=" then s = Zero || s = Negative
          else if a = ">=" then s = Zero || s = Positive
          else if a = "<" then s = Negative
          else if a = ">" then s = Positive
          else failwith "testform: unknown literal"
    | False -> false
    | True -> true
    | Not(p) -> not(testform pmat p)
    | And(p,q) -> testform pmat p && testform pmat q
    | Or(p,q) -> testform pmat p || testform pmat q
    | Imp(p,q) -> not(testform pmat p) || testform pmat q
    | Iff(p,q) -> (testform pmat p = testform pmat q)
    | _ -> failwith "testform: non-propositional formula";;

The model version of testform takes a row of the sign matrix in the form
 (p_1,s_1),(p_2,s_2),...,(p_n,s_n)
The corresponding argument of TESTFORM is a theorem representing
an `interpsigns` proposition.  This is natural.  The next argument,
the formula to be tested, is the same.

*)

(* ====================================================================== *)
(*  Theorems                                                              *)
(* ====================================================================== *)

(* --------------------------------  T   -------------------------------- *)

let t_thm = prove(`!set:real->bool. (!x. set x ==> T)`,MESON_TAC[]);;

(* --------------------------------  F  --------------------------------- *)

let f_thm = prove(`!set:real->bool. ~(?x. set x /\ F)`,MESON_TAC[]);;

(* --------------------------------  ~  --------------------------------- *)

let neg_thm_p = prove(
  `!P set. (!x. set x ==> P x) ==> (~ ?x. set x /\ ~ P x)`,MESON_TAC[]);;

let neg_thm_n = prove(
  `!P set. (~ ?x. set x /\ P x) ==> (!x. set x ==> ~ P x)`,MESON_TAC[]);;

(* --------------------------------  /\  -------------------------------- *)

let and_thm_pp = prove(
  `!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==> (!x. set x ==> Q x) ==>
        (!x. set x ==> (P x /\ Q x))`,MESON_TAC[]);;

let and_thm_pn = prove(
  `!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==>
     (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ P x /\ Q x)`,MESON_TAC[]);;

let and_thm_np = prove(
  `!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
          (!x. set x ==> Q x) ==> (~ ?x. set x /\ P x /\ Q x)`,MESON_TAC[]);;

let and_thm_nn = prove(
  `!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
    (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ P x /\ Q x)`,MESON_TAC[]);;

(* --------------------------------  \/  -------------------------------- *)

let or_thm_p = prove(
`!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==> (!x. set x ==> (P x \/ Q x))`,
  MESON_TAC[]);;

let or_thm_q = prove(
  `!P Q set. (?x. set x) ==> (!x. set x ==> Q x) ==> (!x. set x ==> (P x \/ Q x))`,
  MESON_TAC[]);;

let or_thm_nn =
  prove(`!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
          (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ (P x \/ Q x))`,MESON_TAC[]);;

(* -------------------------------  ==>  -------------------------------- *)

let imp_thm_pp =
  prove(`!P Q set. (?x. set x) ==> (!x. set x ==> Q x) ==>
        (!x. set x ==> (P x ==> Q x))`,MESON_TAC[]);;

let imp_thm_pn =
  prove(`!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==>
        (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ (P x ==> Q x))`,MESON_TAC[]);;

let imp_thm_n =
  prove(`!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
     (!x. set x ==> (P x ==> Q x))`,MESON_TAC[]);;

(* --------------------------------  =  --------------------------------- *)

let iff_thm_pp = prove(
  `!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==> (!x. set x ==> Q x) ==>
        (!x. set x ==> (P x <=> Q x))`,MESON_TAC[]);;

let iff_thm_pn = prove(
  `!P Q set. (?x. set x) ==> (!x. set x ==> P x) ==>
     (~ ?x. set x /\ Q x) ==> (~ ?x. set x /\ (P x <=> Q x))`,MESON_TAC[]);;

let iff_thm_np = prove(
  `!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
          (!x. set x ==> Q x) ==> (~ ?x. set x /\ (P x <=> Q x))`,MESON_TAC[]);;

let iff_thm_nn = prove(
  `!P Q set. (?x. set x) ==> (~ ?x. set x /\ P x) ==>
    (~ ?x. set x /\ Q x) ==> (!x. set x ==> (P x <=> Q x))`,MESON_TAC[]);;

(* ---------------------------------------------------------------------- *)
(*  Atoms                                                                 *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------  ?x. p x < &0  --------------------------- *)

let eq_lt_thm = prove(
  `!P set. (!x. set x ==> (P x = &0)) ==> ~ ?x. set x /\ P x < &0`,
  MESON_TAC[REAL_LT_LE]);;

let gt_lt_thm = prove(
  `!P set. (!x. set x ==> (P x > &0)) ==> ~ ?x. set x /\ P x < &0`,
  MESON_TAC[real_gt;REAL_LT_REFL;REAL_LT_TRANS]);;

(* ---------------------------  ?x. p x = &0  --------------------------- *)

let lt_eq_thm = prove(
  `!P set. (!x. set x ==> (P x < &0)) ==> ~ ?x. set x /\ (P x = &0)`,
  MESON_TAC[REAL_LT_LE]);;

let gt_eq_thm = prove(
  `!P set. (!x. set x ==> (P x > &0)) ==> ~ ?x. set x /\ (P x = &0)`,
  MESON_TAC[real_gt;REAL_LT_LE]);;

(* ---------------------------  ?x. p x > &0  --------------------------- *)

let eq_gt_thm = prove(
  `!P set. (!x. set x ==> (P x = &0)) ==> ~ ?x. set x /\ (P x > &0)`,
  MESON_TAC[real_gt;REAL_LT_LE]);;

let lt_gt_thm = prove(
  `!P set. (!x. set x ==> (P x < &0)) ==> ~ ?x. set x /\ (P x > &0)`,
  MESON_TAC[real_gt;REAL_LT_LE;REAL_LT_TRANS]);;

(* --------------------------  ?x. p x <= &0  --------------------------- *)

let lt_le_thm = prove(
  `!P set. (!x. set x ==> (P x < &0)) ==> !x. set x ==> (P x <= &0)`,
  MESON_TAC[real_gt;REAL_LT_LE;REAL_LT_TRANS]);;

let eq_le_thm = prove(
  `!P set. (!x. set x ==> (P x = &0)) ==> (!x. set x ==> (P x <= &0))`,
  MESON_TAC[real_gt;REAL_LT_LE;REAL_LT_TRANS;real_le]);;

let gt_le_thm = prove(
  `!P set. (!x. set x ==> (P x > &0)) ==> ~ ?x. set x /\ (P x <= &0)`,
  MESON_TAC[real_gt;REAL_LT_LE;REAL_LT_TRANS;real_le]);;

(* --------------------------  ?x. p x >= &0  --------------------------- *)

let lt_ge_thm = prove(
  `!P set. (!x. set x ==> (P x < &0)) ==> ~ ?x. set x /\ (P x >= &0)`,
  MESON_TAC[real_gt;REAL_LT_LE;REAL_LT_TRANS;real_ge]);;

let eq_ge_thm = prove(
  `!P set. (!x. set x ==> (P x = &0)) ==> (!x. set x ==> (P x >= &0))`,
  MESON_TAC[real_gt;REAL_LT_LE;REAL_LT_TRANS;real_ge;real_le]);;

let gt_ge_thm = prove(
  `!P set. (!x. set x ==> (P x > &0)) ==> (!x. set x ==> (P x >= &0))`,
  MESON_TAC[real_gt;REAL_LT_LE;REAL_LT_TRANS;real_ge;real_le]);;

(* let lookup_sign isigns_thm fm =  *)
(*   let asms,_ = dest_thm isigns_thm in *)
(*   let    *)


let NOT_EXISTS_CONJ_THM = prove_by_refinement(
  `~(?x. P x /\ Q x) ==> (!x. P x ==> ~Q x)`,
(* {{{ Proof *)
[
  MESON_TAC[];
]);;
(* }}} *)

let testform_itlem = prove_by_refinement(
  `(!x. P x ==> ~Q x) ==> (!x. P2 x ==> ~Q x) ==> (!x. P x \/ P2 x ==> ~ Q x)`,
(* {{{ Proof *)
[MESON_TAC[]]);;
(* }}} *)
