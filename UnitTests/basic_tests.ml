(* ========================================================================= *)
(*                          HOL LIGHT unit tests                             *)
(* ========================================================================= *)

let assert_conv conv tm tm' =
  let asl,etm = dest_thm(conv tm) in
  assert (asl = [] && is_eq etm && lhs etm = tm && rhs etm = tm');;

(* ------------------------------------------------------------------------- *)
(* Test verbose descriptive names for quantifiers/logical consts.            *)
(* ------------------------------------------------------------------------- *)

assert (`T` = `true`);;
assert (`F` = `false`);;
assert (`!(x:A). P x` = `forall (x:A). P x`);;
assert (`?(x:A). P x` = `exists (x:A). P x`);;
assert (`?!(x:A). P x` = `existsunique (x:A). P x`);;

(* ------------------------------------------------------------------------- *)
(* Test COMPUTE_CONVs.                                                       *)
(* ------------------------------------------------------------------------- *)

assert (rhs (concl (NUM_COMPUTE_CONV `if x then 1 + 2 else 3 + 4`))
              = `if x then 1 + 2 else 3 + 4`);;
assert (rhs (concl (NUM_COMPUTE_CONV `if true then 1 + 2 else 3 + 4`))
              = `3`);;
assert (rhs (concl (NUM_COMPUTE_CONV `\x. x + (1 + 2)`))
        = `\x. x + (1 + 2)`);;
assert (rhs (concl (NUM_COMPUTE_CONV `(\x. x + (1 + 2)) (3 + 4)`))
        = `10`);;
(* Arguments are reduced when the fn is a constant. *)
assert (rhs (concl (NUM_COMPUTE_CONV `(unknown_fn:num->num) (1+2)`))
        = `(unknown_fn:num->num) 3`);;

(* ------------------------------------------------------------------------- *)
(* Test list-specific evaluation conversions.                                *)
(* ------------------------------------------------------------------------- *)

assert_conv LIST_OF_SEQ_CONV
 `list_of_seq (\i. f(i + 17):B) 3` `[f (0 + 17):B; f (1 + 17); f (2 + 17)]`;;

assert_conv EL_CONV `EL 1 [0;1;2;3;4]` `1`;;

assert_conv LENGTH_CONV `LENGTH[1;2;3;4;5]` `5`;;

assert_conv REVERSE_CONV `REVERSE[a:X;b;c;d]` `[d:X;c;b;a]`;;

(* ------------------------------------------------------------------------- *)
(* Test basic_compset.                                                       *)
(* ------------------------------------------------------------------------- *)

let _ =
  let open Compute in
  let cs = basic_compset() in
  let cv = CBV_CONV cs in
  let wcv = WEAK_CBV_CONV cs in begin

  (* Generalized abstraction *)
  assert (rhs (concl (wcv `(\((x,y),(z,w)). x + y + z + w) ((1,2),(3,4))`)) =
          `1 + 2 + 3 + 4`);
  assert (rhs (concl (cv `(\((x,y),(z,w)). x + y + z + w) ((1,2),(3,4))`)) =
          `1 + 2 + 3 + 4`);

  (* Abstraction body is not reduced if WEAK_CBV is used *)
  assert (rhs (concl (wcv
          `(\((x,y),(z,w)):(num#num)#(num#num). true /\ true)`)) =
        `(\((x,y),(z,w)):(num#num)#(num#num). true /\ true)`);
  assert (rhs (concl (cv
          `(\((x,y),(z,w)):(num#num)#(num#num). true /\ true)`)) =
          `(\((x,y),(z,w)):(num#num)#(num#num). true)`);

  (* Match *)
  assert (
    rhs (concl (wcv `match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z`)) =
    `[3; 4; 5]`);
  assert (
    rhs (concl (cv `match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z`)) =
    `[3; 4; 5]`);

  (* Let *)
  assert (rhs (concl (wcv `let x = 1 in x + 2`)) = `1 + 2`);
  assert (rhs (concl (cv `let x = 1 in x + 2`)) = `1 + 2`);
  end;;


(* ------------------------------------------------------------------------- *)
(* Test benign redefinition when polymorphic type is involved.               *)
(* ------------------------------------------------------------------------- *)

let _ = define `(h_benign:A list -> num) [] = 0 /\
                h_benign (CONS _ t) = 1 + h_benign t`;;
let _ = define `(h_benign:A list -> num) [] = 0 /\
                h_benign (CONS _ t) = 1 + h_benign t`;;


(* ------------------------------------------------------------------------- *)
(* Test benign redefinition of an inductive datatype.                        *)
(* ------------------------------------------------------------------------- *)

let _ = new_inductive_definition
  `(forall s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (forall s s'' n. (exists s'. step s s' /\ steps step n s' s'')
      ==> steps step (n+1) s s'')`;;
let _ = new_inductive_definition
  `(forall s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (forall s s'' n. (exists s'. step s s' /\ steps step n s' s'')
      ==> steps step (n+1) s s'')`;;

(* ------------------------------------------------------------------------- *)
(* Test benign redefinition of a coinductive definition.                     *)
(* ------------------------------------------------------------------------- *)

let _ = new_coinductive_definition
  `forall s s'. step s s' /\ diverges (step:S->S->bool) s'
                ==> diverges step s`;;
let _ = new_coinductive_definition
  `forall s s'. step s s' /\ diverges (step:S->S->bool) s'
                ==> diverges step s`;;


(* ------------------------------------------------------------------------- *)
(* Test the 'er' command of the subgoal package.                             *)
(* Each test case has a proof in the THEN form, followed by g-e(er) form.    *)
(* ------------------------------------------------------------------------- *)

(* case 1: 'er' has to rotate 1 subgoal *)
prove(`x + 1 = 1 + x /\ 1 + 1 = 2`,
    CONJ_TAC THENL [
        ALL_TAC;
        ARITH_TAC
    ] THEN REWRITE_TAC[ADD_SYM]);;
g `x + 1 = 1 + x /\ 1 + 1 = 2`;;
e(CONJ_TAC);;
	er(ALL_TAC);; (* rotates 1 subgoal *)
	e(ARITH_TAC);;
e(REWRITE_TAC[ADD_SYM]);;
top_thm();;

(* case 2: 'er' has to rotate 2 subgoals *)
prove(`(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2`,
    CONJ_TAC THENL [
        CONJ_TAC;
        ARITH_TAC
    ] THEN REWRITE_TAC[ADD_AC]);;
g `(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2`;;
e(CONJ_TAC);;
	er(CONJ_TAC);; (* rotates 2 subgoals *)
	e(ARITH_TAC);;
e(REWRITE_TAC[ADD_AC]);;
e(REWRITE_TAC[ADD_AC]);;
top_thm();;

(* case 2': 'er' has to rotate 2 subgoals. There is b(). *)
prove(`(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2`,
    CONJ_TAC THENL [
        CONJ_TAC;
        ARITH_TAC
    ] THEN REWRITE_TAC[ADD_AC]);;
g `(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2`;;
e(CONJ_TAC);;
	er(CONJ_TAC);; (* rotates 2 subgoals *)
	b();;
	er(CONJ_TAC);; (* rotates 2 subgoals *)
	e(ARITH_TAC);;
e(REWRITE_TAC[ADD_AC]);;
e(REWRITE_TAC[ADD_AC]);;
top_thm();;

(* case 3: 'er' has to rotate 0 subgoal *)
prove(`x + 1 = 1 + x /\ 1 + 1 = 2`,
    CONJ_TAC THENL [
        ARITH_TAC;
        ARITH_TAC
    ]);;
g `x + 1 = 1 + x /\ 1 + 1 = 2`;;
e(CONJ_TAC);;
	er(ARITH_TAC);; (* does not rotate since ARITH_TAC discharges the subgoal *)
	e(ARITH_TAC);;
top_thm();;


(* ------------------------------------------------------------------------- *)
(* Test functions in lib.                                                    *)
(* ------------------------------------------------------------------------- *)

assert (find_index ((=) 10) [0;10;20] = Some 1);;
assert (find_index ((=) 99) [0;10;20] = None);;
assert (index 10 [0;10;20] = 1);;
assert (not (can (index 99) [0;10;20]));;


(* ------------------------------------------------------------------------- *)
(* Test bignum.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Z.pow (Z.of_int 0) 0 is 1.
   Num.power_num (Num.num_of_int 0) (Num.num_of_int 0) is also 1. *)
assert (power_num (num 0) (num 0) = num 1);;
assert (pow (num 0) 0 = num 1);;

assert (power_num (num 2) (num 3) = num 8);;
assert (power_num (num 1 // num 2) (num 3) = (num 1 // num 8));;
assert (power_num (num 1 // num 2) (num 4) = (num 1 // num 16));;
assert (power_num (num 1 // num 2) (num (-3)) = num 8);;
assert (power_num (num 1 // num 2) (num (-4)) = num 16);;
assert (power_num (num 1 // num 2) (num 0) = num 1);;
assert (pow (num 2) 3 = num 8);;
assert (pow (num 1 // num 2) 3 = (num 1 // num 8));;
assert (pow (num 1 // num 2) 4 = (num 1 // num 16));;
assert (pow (num 1 // num 2) (-3) = num 8);;
assert (pow (num 1 // num 2) (-4) = num 16);;
assert (pow (num 1 // num 2) 0 = num 1);;

(* ------------------------------------------------------------------------- *)
(* Test UNIFY_REFL_TAC.                                                      *)
(* ------------------------------------------------------------------------- *)

let UNIFY_REFL_TAC_TEST = prove(`?x. 1 = x`, META_EXISTS_TAC THEN UNIFY_REFL_TAC);;
let UNIFY_REFL_TAC_TEST2 = prove(`?f. y + z = f y z`,
                META_EXISTS_TAC THEN UNIFY_REFL_TAC);;
let UNIFY_REFL_TAC_TEST3 = prove(`?f. y + 1 = f y 0`,
                META_EXISTS_TAC THEN UNIFY_REFL_TAC);;


(* ------------------------------------------------------------------------- *)
(* Test instantiation of variables in the conditions of conditional rewrites *)
(* that are not determined by the LHS (find_witnesses and satisfy_prover).   *)
(* ------------------------------------------------------------------------- *)

let simp_test conv thl tm =
  let th = conv thl tm in
  assert (lhs(concl th) = tm && subset (hyp th) (itlist (union o hyp) thl []));
  rhs(concl th);;

let _ =
  let rule = ASSUME `!s:B x:A. P s x ==> f x = x`
  and rrule = ASSUME `!s:B x:A. P s x ==> (f:A->A) x = g s x`
  and fact = ASSUME `(P:B->A->bool) c q` and tm = `(f:A->A) q` in
  (* A variable only in the condition, or also in the RHS *)
  assert (simp_test SIMP_CONV [rule; fact] tm = `q:A`);
  assert (simp_test PURE_SIMP_CONV [rule; fact] tm = `q:A`);
  assert (simp_test ONCE_SIMP_CONV [rule; fact] tm = `q:A`);
  assert (simp_test SIMP_CONV [rrule; fact] tm = `(g:B->A->A) c q`);
  (* No suitable fact, including one at a different type: no change *)
  assert (simp_test SIMP_CONV [rule] tm = tm);
  assert (simp_test SIMP_CONV [rule; ASSUME `(P:B->A->bool) c z`] tm = tm);
  assert (simp_test SIMP_CONV [rule; ASSUME `(P:B->bool->bool) c T`] tm = tm);
  (* Plain rewriting is unaffected *)
  assert (rhs(concl(REWRITE_CONV [rule; fact] tm)) = tm);;

let _ =
  let rule = ASSUME `!s:B x:A. P s x /\ Q s x ==> f x = x`
  and tm = `(f:A->A) q` in
  (* Backtrack over facts until all the conjuncts agree on the witness *)
  assert (simp_test SIMP_CONV
           [rule; ASSUME `(P:B->A->bool) c q`; ASSUME `(P:B->A->bool) d q`;
            ASSUME `(Q:B->A->bool) d q`] tm = `q:A`);
  assert (simp_test SIMP_CONV
           [rule; ASSUME `(P:B->A->bool) c q`; ASSUME `(Q:B->A->bool) d q`]
           tm = tm);
  (* Separate existential and RHS variables solved together *)
  let rule' = ASSUME `!s:B t:C x:A. P s x /\ R t x ==> (f:A->A) x = g s x` in
  assert (simp_test SIMP_CONV
           [rule'; ASSUME `(P:B->A->bool) c q`; ASSUME `(R:C->A->bool) d q`]
           tm = `(g:B->A->A) c q`);;

let _ =
  let rule = ASSUME `!s:B x:A. P s x ==> f x = x` in
  (* Facts from the context, e.g. an antecedent or the assumptions *)
  assert (simp_test SIMP_CONV [rule]
           `(P:B->A->bool) c q ==> (f:A->A) q = q` = `T`);
  ignore(prove(`(!s:B x:A. P s x ==> f x = x) /\ P c q ==> f q = q`,
               STRIP_TAC THEN ASM_SIMP_TAC[]));;

let _ =
  (* An instance with the LHS inside the RHS is not used, avoiding a loop *)
  let rule = ASSUME `!s:A x:A. P s x ==> (f:A->A) x = g s x` in
  assert (simp_test SIMP_CONV [rule; ASSUME `(P:A->A->bool) (f q) q`]
           `(f:A->A) q` = `(f:A->A) q`);
  (* Instantiated permutative rewrites must decrease in the term ordering *)
  let rule = ASSUME `!x:A y:A. R x y ==> (f:A->A) x = f y`
  and facts = [ASSUME `(R:A->A->bool) a b`; ASSUME `(R:A->A->bool) b a`] in
  let check tm = let tm' = simp_test SIMP_CONV (rule::facts) tm in
                 assert (tm' = tm || term_order tm tm') in
  check `(f:A->A) a`; check `(f:A->A) b`;;

(* ------------------------------------------------------------------------- *)
(* Test MESON on unapplied and partially applied equalities when there is a  *)
(* variable in head position (ASM_FOL_TAC used to fail on these).            *)
(* ------------------------------------------------------------------------- *)

let _ = MESON[] `ALL2 (=) (l:num list) m /\ (!f:num->bool. f 1) ==> ALL2 (=) l m`;;

let _ = MESON[] `(!g:num->num->bool. P g ==> Q (g 1)) /\ P (=) ==> Q ((=) 1)`;;

(* ------------------------------------------------------------------------- *)
(* Test that X_CHOOSE_TAC rejects a variable that is free in the hypotheses  *)
(* of an assumption, whose use would make the justification fail.           *)
(* ------------------------------------------------------------------------- *)

let _ =
  let th = ADD_ASSUM `x = 0` TRUTH in
  let gl = (["",th],`T`) and xth = ASSUME `?x. x = 1` in
  (try ignore(X_CHOOSE_TAC `x:num` xth gl); assert false
   with Failure _ -> () | Assert_failure _ as e -> raise e);
  ignore(TAC_PROOF(gl,X_CHOOSE_TAC `y:num` xth THEN ACCEPT_TAC th));;

(* ------------------------------------------------------------------------- *)
(* Test that the simplifier keeps simplifying where a congruence rule may    *)
(* apply: the range of a sum after its body, and a term that becomes an     *)
(* implication.                                                              *)
(* ------------------------------------------------------------------------- *)

let _ =
  let simp thl tm = rhs(concl(SIMP_CONV thl tm)) in
  assert (simp [ADD_CLAUSES] `nsum(0..n+0) (\i. i + 0)` = `nsum(0..n) (\i. i)`);
  assert (simp [ADD_CLAUSES] `nsum(0..n+0) (\i. if i <= n then 1 else 0)` =
          `nsum(0..n) (\i. 1)`);
  assert (simp [] `(if T then (==>) else (\/)) p (p /\ r)` = `p ==> r`);;

(* ------------------------------------------------------------------------- *)
(* Test that the simplifier keeps facts about free variables off bound       *)
(* variables of the same names, also under many such binders (each used to   *)
(* double the time) and under a congruence rule with a bound variable.       *)
(* ------------------------------------------------------------------------- *)

let _ =
  let vs = map (fun i -> mk_var("x"^string_of_int i,`:num`)) (1--10) in
  let fty = itlist (fun _ ty -> mk_fun_ty `:num` ty) vs `:num` in
  let f = mk_var("f",fty) and g = mk_var("g",fty) in
  let facts = map (fun v -> ASSUME(mk_eq(v,`0`))) vs in
  let eqn l r = list_mk_forall(vs,mk_eq(l,r)) in
  let tm = eqn (mk_comb(mk_comb(`(+):num->num->num`,list_mk_comb(f,vs)),`0`))
               (list_mk_comb(g,vs)) in
  let th = SIMP_CONV (ADD_CLAUSES::facts) tm in
  assert (rhs(concl th) = eqn (list_mk_comb(f,vs)) (list_mk_comb(g,vs)));
  let th' = SIMP_CONV [ADD_CLAUSES; ASSUME `i = 5`] `nsum(0..n) (\i. i + 0)` in
  assert (aconv (rhs(concl th')) `nsum(0..n) (\i. i)`);;

(* ------------------------------------------------------------------------- *)
(* Test ASM_ARITH_TAC and ASM_REAL_ARITH_TAC with many irrelevant            *)
(* assumptions, and with assumptions that only the fallback to all of them   *)
(* can use.                                                                  *)
(* ------------------------------------------------------------------------- *)

let _ =
  let asm tms = map (fun t -> "",ASSUME t) tms in
  let ys = map (fun i -> mk_eq(mk_var("y"^string_of_int i,`:num`),
                               mk_small_numeral i)) (1--40) in
  ignore(TAC_PROOF((asm(`x < 2`::ys),`x + 1 <= 2`),ASM_ARITH_TAC));
  ignore(TAC_PROOF((asm[`x < 2 /\ P(x:num)`],`x < 3`),ASM_ARITH_TAC));
  ignore(TAC_PROOF((asm[`F`; `y = 1`],`x < 3`),ASM_ARITH_TAC));
  ignore(TAC_PROOF((asm[`&0 < x`; `y = &1`],`&0 <= x / &2`),ASM_REAL_ARITH_TAC));
  ignore(TAC_PROOF((asm[`&0 < x`; `y = &1`],`&0 <= x + y`),ASM_REAL_ARITH_TAC));;

(* ------------------------------------------------------------------------- *)
(* Test genvar_index and genvars: the variables avoid every variable named   *)
(* like them in the terms, free or bound, whatever its type, never have the  *)
(* names of genvar, and the results depend only on the arguments, whatever  *)
(* was called before.                                                        *)
(* ------------------------------------------------------------------------- *)

let _ =
  let v s ty = mk_var(s,ty) in
  let tm1 = mk_abs(v "_v3" `:num`,mk_eq(v "_v1" `:num`,v "x" `:num`))
  and tm2 = mk_eq(v "_v10" `:bool`,v "_v007" `:bool`)
  and tm3 = mk_eq(v "_v12'" `:bool`,mk_eq(v "_v" `:bool`,v "_20" `:bool`)) in
  let tys = [`:num`; `:bool`; `:num`] in
  let call1() = genvar_index [tm1;tm2;tm3],genvars [tm1;tm2;tm3] tys
  and call2() = genvar_index [tm1],genvars [tm3] tys in
  let r1 = (11,[v "_v11" `:num`; v "_v12" `:bool`; v "_v13" `:num`])
  and r2 = (4,[v "_v1" `:num`; v "_v2" `:bool`; v "_v3" `:num`]) in
  assert (genvar_index [] = 1 && genvars [tm1] [] = []);
  assert (genvar_index [`0`; v "_v0" `:num`] = 1 &&
          genvars [`0`] [`:num`] = [v "_v1" `:num`]);
  assert (call1() = r1);
  assert (call2() = r2);
  ignore(map genvar tys);
  assert (call2() = r2 && call1() = r1 && call2() = r2);
  let g1 = genvar `:num` in
  let gvs = genvars [g1] [`:num`; `:num`] in
  let g2 = genvar `:num` in
  assert (gvs = [v "_v1" `:num`; v "_v2" `:num`] &&
          not(mem g1 gvs) && not(mem g2 gvs));
  let asl = ["",ASSUME(mk_eq(v "_v5" `:num`,v "_v2" `:num`));
             "",ADD_ASSUM (mk_eq(v "_v7" `:bool`,`T`)) (ASSUME `x = 1`)] in
  assert (genvar_index_goal ([],tm3) = 1 &&
          genvar_index_goal (asl,tm1) = 8 &&
          genvar_index_goal (tl asl,tm2) = 11);;

(* ------------------------------------------------------------------------- *)
(* Test that ABS_CONV and the simplifier rename a bound variable that is     *)
(* free in a fact of the context apart from the context, even when the       *)
(* context has a variable named like the first choice.                       *)
(* ------------------------------------------------------------------------- *)

let _ =
  let ths = [ASSUME `x = 1`; ASSUME `_v1 = 2`; ADD_CLAUSES] in
  assert (rhs(concl(REWRITE_CONV ths `\x. x + 0`)) = `\x:num. x`);
  assert (rhs(concl(SIMP_CONV ths `\x. x + 0`)) = `\x:num. x`);;

(* ------------------------------------------------------------------------- *)
(* Test that new_definition keeps the user's variables in the underlying     *)
(* definition.                                                               *)
(* ------------------------------------------------------------------------- *)

let _ =
  let _ = new_definition `genvar_test_def (f:num->num) (x,y) = f x + y` in
  assert (concl(hd(definitions())) =
          `genvar_test_def = \(f:num->num) (p:num#num). f (FST p) + SND p`);;

(* ------------------------------------------------------------------------- *)
(* Test that GEN_BETA_CONV gives the term itself as the left-hand side.      *)
(* ------------------------------------------------------------------------- *)

let _ =
  let tm = `(\(x,y). x + y) (1,2)` in
  assert (lhs(concl(GEN_BETA_CONV tm)) = tm);;

(* ------------------------------------------------------------------------- *)
(* Test pa_j preprocessor.                                                   *)
(* ------------------------------------------------------------------------- *)

unset_jrh_lexer;;

(* Pfunction_cases must be supported *)
let test_fn = function
  | Unix.ADDR_UNIX _ -> ()
  | Unix.ADDR_INET _ -> ();;

set_jrh_lexer;;

(* ------------------------------------------------------------------------- *)
(* Test check_axioms.                                                        *)
(* ------------------------------------------------------------------------- *)

new_axiom `k = 1`;;
try
  check_axioms (); (* check_axioms must raise Failure *)
  assert false;
with Failure _ -> () | Assert_failure _ as e -> raise e;;
