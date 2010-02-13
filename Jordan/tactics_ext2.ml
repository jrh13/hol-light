
(* ------------------------------------------------------------------ *)
(* MORE RECENT ADDITIONS *)
(* ------------------------------------------------------------------ *)



(* abbrev_type copied from definitions_group.ml *)

let pthm = prove_by_refinement(
  `(\ (x:A) .T) (@(x:A). T)`,
  [BETA_TAC]);;

let abbrev_type ty s = let (a,b) = new_basic_type_definition s
   ("mk_"^s,"dest_"^s)
   (INST_TYPE [ty,`:A`] pthm) in
   let abst t = list_mk_forall ((frees t), t) in
   let a' = abst (concl a) in
   let b' = abst (rhs (concl b)) in
   (
   prove_by_refinement(a',[REWRITE_TAC[a]]),
   prove_by_refinement(b',[REWRITE_TAC[GSYM b]]));;


(* ------------------------------------------------------------------ *)
(* KILL IN *)
(* ------------------------------------------------------------------ *)

let un = REWRITE_RULE[IN];;

(* ------------------------------------------------------------------ *)

let SUBCONJ_TAC =
  MATCH_MP_TAC (TAUT `A /\ (A ==>B) ==> (A /\ B)`) THEN CONJ_TAC;;

let PROOF_BY_CONTR_TAC =
  MATCH_MP_TAC (TAUT `(~A ==> F) ==> A`) THEN DISCH_TAC;;



(* ------------------------------------------------------------------ *)
(* some general tactics *)
(* ------------------------------------------------------------------ *)

(* before adding assumption to hypothesis list, cleanse it
   of unnecessary conditions *)


let CLEAN_ASSUME_TAC th =
   MP_TAC th THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let CLEAN_THEN th ttac =
   MP_TAC th THEN ASM_REWRITE_TAC[] THEN DISCH_THEN ttac;;

(* looks for a hypothesis by matching a subterm *)
let (UNDISCH_FIND_TAC: term -> tactic) =
 fun tm (asl,w) ->
   let p = can (term_match[] tm)  in
   try let sthm,_ = remove
     (fun (_,asm) -> can (find_term p) (concl ( asm))) asl in
     UNDISCH_TAC (concl (snd sthm)) (asl,w)
   with Failure _ -> failwith "UNDISCH_FIND_TAC";;

let (UNDISCH_FIND_THEN: term -> thm_tactic -> tactic) =
 fun tm ttac (asl,w) ->
   let p = can (term_match[] tm)  in
   try let sthm,_ = remove
     (fun (_,asm) -> can (find_term p) (concl ( asm))) asl in
     UNDISCH_THEN (concl (snd sthm)) ttac (asl,w)
   with Failure _ -> failwith "UNDISCH_FIND_TAC";;

(* ------------------------------------------------------------------ *)
(* NAME_CONFLICT_TAC : eliminate name conflicts in a term *)
(* ------------------------------------------------------------------ *)

let relabel_bound_conv tm =
 let rec vars_and_constants tm acc =
   match tm with
    | Var _ -> tm::acc
    | Const _ -> tm::acc
    | Comb(a,b) -> vars_and_constants b (vars_and_constants a acc)
    | Abs(a,b) -> a::(vars_and_constants b acc) in
 let relabel_bound tm =
   match tm with
    | Abs(x,t) ->
        let avoids = filter ((!=) x) (vars_and_constants tm []) in
        let x' = mk_primed_var avoids x in
        if (x=x') then failwith "relabel_bound" else (alpha x' tm)
    | _ -> failwith "relabel_bound" in
 DEPTH_CONV (fun t -> ALPHA t (relabel_bound t)) tm;;

(* example *)
let _ =
  let bad_term = mk_abs (`x:bool`,`(x:num)+1=2`) in
  relabel_bound_conv bad_term;;

let NAME_CONFLICT_CONV = relabel_bound_conv;;

let NAME_CONFLICT_TAC =  CONV_TAC (relabel_bound_conv);;

(* renames  given bound variables *)
let alpha_conv env tm = ALPHA tm (deep_alpha env tm);;

(* replaces given alpha-equivalent terms with- the term itself *)
let unify_alpha_tac = SUBST_ALL_TAC o REFL;;

let rec get_abs tm acc = match tm with
   Abs(u,v) -> get_abs v (tm::acc)
  |Comb(u,v) -> get_abs u (get_abs v acc)
  |_ -> acc;;

(* for purposes such as sorting, it helps if ALL ALPHA-equiv
   abstractions are replaced by equal abstractions *)
let (alpha_tac:tactic) =
  fun  (asl,w' ) ->
  EVERY (map unify_alpha_tac (get_abs w' [])) (asl,w');;

(* ------------------------------------------------------------------ *)
(* SELECT ELIMINATION.
   SELECT_TAC should work whenever there is a single predicate selected.
   Something more sophisticated might be needed when there
   is (@)A and (@)B
   in the same formula.
   Useful for proving statements such as  `1 + (@x. (x=3)) = 4` *)
(* ------------------------------------------------------------------ *)

(* spec form of SELECT_AX *)
let select_thm select_fn select_exist =
  BETA_RULE (ISPECL [select_fn;select_exist]
             SELECT_AX);;

(* example *)
select_thm
    `\m. (X:num->bool) m /\ (!n. X n ==> m <=| n)` `n:num`;;

let SELECT_EXIST = prove_by_refinement(
  `!(P:A->bool) Q. (?y. P y) /\ (!t. (P t ==> Q t)) ==> Q ((@) P)`,
  (* {{{ proof *)

  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  UNDISCH_FIND_TAC `(?)`;
  DISCH_THEN CHOOSE_TAC;
  ASSUME_TAC (ISPECL[`P:(A->bool)`;`y:A`] SELECT_AX);
  ASM_MESON_TAC[];
  ]);;

  (* }}} *)

let SELECT_THM = prove_by_refinement(
  `!(P:A->bool) Q. (((?y. P y) ==> (!t. (P t ==> Q t))) /\ ((~(?y. P y)) ==>
     (!t. Q t))) ==> Q ((@) P)`,
  (* {{{ proof *)
  [
  MESON_TAC[SELECT_EXIST];
  ]);;
  (* }}} *)

let SELECT_TAC  =
  (* explicitly pull apart the clause Q((@) P),
     because MATCH_MP_TAC isn't powerful
     enough to do this by itself. *)
  let unbeta = prove(
  `!(P:A->bool) (Q:A->bool). (Q ((@) P)) <=> (\t. Q t) ((@) P)`,MESON_TAC[]) in
  let unbeta_tac = CONV_TAC (HIGHER_REWRITE_CONV[unbeta] true) in
  unbeta_tac THEN (MATCH_MP_TAC SELECT_THM) THEN BETA_TAC THEN CONJ_TAC
   THENL[
     (DISCH_THEN (fun t-> ALL_TAC)) THEN GEN_TAC;
     DISCH_TAC THEN GEN_TAC];;

(* EXAMPLE:

# g `(R:A->bool) ((@) S)`;;
val it : Core.goalstack = 1 subgoal (1 total)

`R ((@) S)`

# e SELECT_TAC ;;
val it : Core.goalstack = 2 subgoals (2 total)

 0 [`~(?y. S y)`]

`R t`

`S t ==> R t`

*)


(* ------------------------------------------------------------------ *)
(* TYPE_THEN and TYPEL_THEN  calculate the types of the terms supplied
   in a proof, avoiding the hassle of working them out by hand.
   It locates the terms among the free variables in the goal.
   Ambiguious if a free variables have name conflicts.

   Now TYPE_THEN handles general terms.
*)
(* ------------------------------------------------------------------ *)


let rec type_set: (string*term) list  -> (term list*term) -> (term list*term)=
  fun typinfo (acclist,utm) -> match acclist with
    | [] -> (acclist,utm)
    | (Var(s,_) as a)::rest ->
         let a' = (assocd s typinfo a) in
           if (a = a') then type_set typinfo (rest,utm)
           else let inst = instantiate (term_match [] a a') in
             type_set typinfo ((map inst rest),inst utm)
    | _ -> failwith "type_set: variable expected"
  ;;

let has_stv t =
  let typ = (type_vars_in_term t) in
  can (find (fun ty -> (is_vartype ty) && ((dest_vartype ty).[0] = '?'))) typ;;


let TYPE_THEN: term  -> (term -> tactic) -> tactic =
  fun t (tac:term->tactic) (asl,w) ->
  let avoids = itlist (union o frees o concl o snd) asl
                               (frees w) in
  let strip  = fun t-> (match t with
       |Var(s,_) -> (s,t) | _ -> failwith "TYPE_THEN" ) in
  let typinfo = map strip avoids in
  let t' = (snd (type_set typinfo ((frees t),t))) in
    (warn ((has_stv t')) "TYPE_THEN: unresolved type variables");
    tac t' (asl,w);;

(* this version must take variables *)
let TYPEL_THEN: term list -> (term list -> tactic) -> tactic =
  fun t (tac:term list->tactic) (asl,w) ->
  let avoids = itlist (union o frees o concl o snd) asl
                               (frees w) in
  let strip  = fun t-> (match t with
       |Var(s,_) -> (s,t) | _ -> failwith "TYPE_THEN" ) in
  let typinfo = map strip avoids in
  let t' = map (fun u -> snd (type_set typinfo ((frees u),u))) t in
    (warn ((can (find has_stv) t')) "TYPEL_THEN: unresolved type vars");
     tac t' (asl,w);;

(* trivial example *)

let _ = prove_by_refinement(`!y. y:num = y`,
 [
   GEN_TAC;
   TYPE_THEN `y:A` (fun t -> ASSUME_TAC(ISPEC t (TAUT `!x:B. x=x`)));
   UNDISCH_TAC `y:num = y`; (* evidence that `y:A` was retyped as `y:num` *)
   MESON_TAC[];
 ]);;


(* ------------------------------------------------------------------ *)
(* SAVE the goalstate, and retrieve later *)
(* ------------------------------------------------------------------ *)

let (save_goal,get_goal) =
  let goal_buffer  = ref [] in
  let save_goal s =
     goal_buffer := (s,!current_goalstack )::!goal_buffer in
  let get_goal (s:string) = (current_goalstack:= assoc s !goal_buffer) in
  (save_goal,get_goal);;


(* ------------------------------------------------------------------ *)
(* ordered rewrites with general ord function .
   This allows rewrites with an arbitrary condition
    -- adapted from simp.ml *)
(* ------------------------------------------------------------------ *)



let net_of_thm_ord ord rep force th =
  let t = concl th in
  let lconsts = freesl (hyp th) in
  let matchable = can o term_match lconsts in
  try let l,r = dest_eq t in
      if rep & free_in l r then
       let th' = EQT_INTRO th in
       enter lconsts (l,(1,REWR_CONV th'))
      else if rep & matchable l r & matchable r l then
        enter lconsts (l,(1,ORDERED_REWR_CONV ord th))
      else if force then
        enter lconsts (l,(1,ORDERED_REWR_CONV ord th))
      else enter lconsts (l,(1,REWR_CONV th))
  with Failure _ ->
      let l,r = dest_eq(rand t) in
      if rep & free_in l r then
       let tm = lhand t in
       let th' = DISCH tm (EQT_INTRO(UNDISCH th)) in
       enter lconsts (l,(3,IMP_REWR_CONV th'))
      else if rep &  matchable l r & matchable r l then
        enter lconsts (l,(3,ORDERED_IMP_REWR_CONV ord th))
      else enter lconsts(l,(3,IMP_REWR_CONV th));;

let GENERAL_REWRITE_ORD_CONV ord rep force (cnvl:conv->conv) (builtin_net:gconv net) thl =
  let thl_canon = itlist (mk_rewrites false) thl [] in
  let final_net = itlist (net_of_thm_ord ord rep force ) thl_canon builtin_net in
  cnvl (REWRITES_CONV final_net);;

let GEN_REWRITE_ORD_CONV ord force (cnvl:conv->conv) thl =
  GENERAL_REWRITE_ORD_CONV ord false force cnvl empty_net thl;;

let PURE_REWRITE_ORD_CONV ord force thl =
  GENERAL_REWRITE_ORD_CONV ord true force TOP_DEPTH_CONV empty_net thl;;

let REWRITE_ORD_CONV ord force thl =
  GENERAL_REWRITE_ORD_CONV ord true force TOP_DEPTH_CONV (basic_net()) thl;;

let PURE_ONCE_REWRITE_ORD_CONV ord force thl =
  GENERAL_REWRITE_ORD_CONV ord false force ONCE_DEPTH_CONV empty_net thl;;

let ONCE_REWRITE_ORD_CONV ord force thl =
  GENERAL_REWRITE_ORD_CONV ord false force ONCE_DEPTH_CONV (basic_net()) thl;;

let REWRITE_ORD_TAC ord force thl = CONV_TAC(REWRITE_ORD_CONV ord force thl);;




(* ------------------------------------------------------------------ *)
(* poly reduction *)
(* ------------------------------------------------------------------ *)


(* move vars  leftward *)
(* if ord old_lhs new_rhs THEN swap *)


let new_factor_order t1 t2 =
  try let t1v = fst(dest_binop `( *. )` t1) in
      let t2v = fst(dest_binop `( *. )` t2) in
  if (is_var t1v) & (is_var t2v) then term_order t1v t2v
  else if (is_var t2v) then true else false
  with Failure _  -> false ;;

(* false if it contains a variable or abstraction. *)
let rec is_arith_const tm =
  if is_var tm then false else
  if is_abs tm then false else
  if is_comb tm then
     let (a,b) = (dest_comb tm) in
     is_arith_const (a) & is_arith_const (b)
  else true;;

(* const leftward *)
let new_factor_order2 t1 t2 =
  try let t1v = fst(dest_binop `( *. )` t1) in
      let t2v = fst(dest_binop `( *. )` t2) in
  if (is_var t1v) & (is_var t2v) then term_order t1v t2v
  else if (is_arith_const t2v) then true else false
  with Failure _  -> false ;;

let rec mon_sz tm =
  if is_var tm then
    Int (Hashtbl.hash tm)
  else
  try let (a,b) = dest_binop `( *. )` tm in
    (mon_sz a) */ (mon_sz b)
  with Failure _ -> Int 1;;

let rec new_summand_order t1 t2 =
  try let t1v = fst(dest_binop `( +. )` t1) in
      let t2v = fst(dest_binop `( +. )` t2) in
  (mon_sz t2v >/ mon_sz t1v)
  with Failure _  -> false ;;

let rec new_distrib_order t1 t2 =
  try let t2v = fst(dest_binop `( *. )` t2) in
  if (is_arith_const t2v) then true else false
  with Failure _  ->
    try
      let t2' = fst(dest_binop `( +. )` t2) in
      new_distrib_order t1 t2'
    with Failure _ -> false ;;

let real_poly_conv =
  (* same side *)
  ONCE_REWRITE_CONV [GSYM REAL_SUB_0] THENC
  (* expand ALL *)
  REWRITE_CONV[real_div;REAL_RDISTRIB;REAL_SUB_RDISTRIB;
  pow;
  GSYM REAL_MUL_ASSOC;GSYM REAL_ADD_ASSOC;
   REAL_ARITH `(x -. (--y) = x + y) /\ (x - y = x + (-- y)) /\
               (--(x + y) = --x + (--y)) /\ (--(x - y) = --x + y)`;
   REAL_ARITH
       `(x*.(-- y) = -- (x*. y)) /\ (--. (--. x) = x) /\
       ((--. x)*.y = --.(x*.y))`;
         REAL_SUB_LDISTRIB;REAL_LDISTRIB] THENC
  (* move constants rightward on monomials *)
   REWRITE_ORD_CONV new_factor_order false [REAL_MUL_AC;] THENC
   GEN_REWRITE_CONV ONCE_DEPTH_CONV
           [REAL_ARITH `-- x = (x*(-- &.1))`] THENC
   REWRITE_CONV[GSYM REAL_MUL_ASSOC] THENC
   REAL_RAT_REDUCE_CONV THENC
   (* collect like monomials *)
   REWRITE_ORD_CONV new_summand_order false [REAL_ADD_AC;] THENC
   (* move constants leftward AND collect them together *)
   REWRITE_ORD_CONV new_factor_order2 false [REAL_MUL_AC;] THENC
   REWRITE_ORD_CONV new_distrib_order true [
        REAL_ARITH `(a*b +. d*b = (a+d)*b) /\
             (a*b + b = (a+ &.1)*b ) /\ ( b + a*b = (a+ &.1)*b) /\
             (a*b +. d*b +e = (a+d)*b + e) /\
             (a*b + b + e= (a+. &.1)* b +e ) /\
             ( b + a*b + e = (a + &.1)*b +e) `;] THENC
   REAL_RAT_REDUCE_CONV THENC
   REWRITE_CONV[REAL_ARITH `(&.0 * x = &.0) /\ (x + &.0 = x) /\
              (&.0 + x = x)`];;

let real_poly_tac = CONV_TAC real_poly_conv;;

let test_real_poly_tac = prove_by_refinement(
  `!x y . (x + (&.2)*y)*(x- (&.2)*y) = (x*x -. (&.4)*y*y)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  real_poly_tac;
  ]);;
  (* }}} *)




(* ------------------------------------------------------------------ *)
(* REAL INEQUALITIES *)


(* Take inequality certificate A + B1 + B2 +.... + P = C as a term.
   Prove it as an inequality.
   Reduce to an ineq (A < C) WITH side conditions
      0 <= Bi,  0 < P.

   If (not strict), write as an ineq (A <= C) WITH side conditions
      0 <= Bi.

   Expand each Bi (or P) that is a product U*V as 0 <= U /\ 0 <= V.
   To prevent expansion of Bi write (U*V) as (&0 + (U*V)).

   CALL as
   ineq_le_tac `A + B1 + B2 = C`;

   *)
(* ------------------------------------------------------------------ *)


let strict_lemma = prove_by_refinement(
  `!A B C. (A+B = C) ==> ((&.0 <. B) ==> (A <. C)  )`,
  (* {{{ proof *)
  [
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let weak_lemma = prove_by_refinement(
  `!A B C. (A+B = C) ==> ((&.0 <=. B) ==> (A <=. C))`,
  (* {{{ proof *)
  [
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let strip_lt_lemma = prove_by_refinement(
  `!B1 B2 C. ((&.0 <. (B1+B2)) ==> C) ==>
         ((&.0 <. B2) ==> ((&.0 <=. B1) ==> C))`,
  (* {{{ proof *)
  [
  ASM_MESON_TAC[REAL_LET_ADD];
  ]);;
  (* }}} *)

let strip_le_lemma = prove_by_refinement(
  `!B1 B2 C. ((&.0 <=. (B1+B2)) ==> C) ==>
         ((&.0 <=. B2) ==> ((&.0 <=. B1) ==> C))`,
  (* {{{ proof *)
  [
  ASM_MESON_TAC[REAL_LE_ADD];
  ]);;
  (* }}} *)

let is_x_prod_le tm =
  try let hyp = fst(dest_binop `( ==> )` tm) in
      let arg = snd(dest_binop `( <=. ) ` hyp) in
      let fac = dest_binop `( *. )` arg in
  true
  with Failure _ -> false;;

let switch_lemma_le_order t1 t2 =
  if (is_x_prod_le t1) & (is_x_prod_le t2) then
  term_order t1 t2 else
  if (is_x_prod_le t2) then true else false;;

let is_x_prod_lt tm =
  try let hyp = fst(dest_binop `( ==> )` tm) in
      let arg = snd(dest_binop `( <. ) ` hyp) in
      let fac = dest_binop `( *. )` arg in
  true
  with Failure _ -> false;;

let switch_lemma_lt_order t1 t2 =
  if (is_x_prod_lt t1) & (is_x_prod_lt t2) then
  term_order t1 t2 else
  if (is_x_prod_lt t2) then true else false;;

let switch_lemma_le = prove_by_refinement(
  `!A B C. ((&.0 <= A) ==> (&.0 <= B) ==> C) =
       ((&.0 <=. B) ==> (&.0 <= A) ==> C)`,
  (* {{{ proof *)
  [
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let switch_lemma_let = prove_by_refinement(
  `!A B C. ((&.0 < A) ==> (&.0 <= B) ==> C) =
       ((&.0 <=. B) ==> (&.0 < A) ==> C)`,
  (* {{{ proof *)
  [
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let switch_lemma_lt = prove_by_refinement(
  `!A B C. ((&.0 < A) ==> (&.0 < B) ==> C) =
       ((&.0 <. B) ==> (&.0 < A)  ==> C)`,
  (* {{{ proof *)
  [
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let expand_prod_lt = prove_by_refinement(
  `!B1 B2 C. (&.0 < B1*B2 ==> C) ==>
              ((&.0 <. B1) ==> (&.0 <. B2) ==> C)`,
  (* {{{ proof *)
  [
  ASM_MESON_TAC[REAL_LT_MUL ];
  ]);;
  (* }}} *)

let expand_prod_le = prove_by_refinement(
  `!B1 B2 C. (&.0 <= B1*B2 ==> C) ==>
              ((&.0 <=. B1) ==> (&.0 <=. B2) ==> C)`,
  (* {{{ proof *)
  [
  ASM_MESON_TAC[REAL_LE_MUL ];
  ]);;
  (* }}} *)


let ineq_cert_gen_tac v cert =
  let DISCH_RULE f = DISCH_THEN (fun t-> MP_TAC (f t)) in
  TYPE_THEN cert
     (MP_TAC o (REWRITE_CONV[REAL_POW_2] THENC real_poly_conv)) THEN
  REWRITE_TAC[] THEN
  DISCH_RULE (MATCH_MP v) THEN
  DISCH_RULE (repeat (MATCH_MP strip_lt_lemma)) THEN
  DISCH_RULE (repeat (MATCH_MP strip_le_lemma)) THEN
  DISCH_RULE (repeat (MATCH_MP expand_prod_lt o
        (CONV_RULE
   (REWRITE_ORD_CONV switch_lemma_lt_order true[switch_lemma_lt])))) THEN
  DISCH_RULE (repeat (MATCH_MP expand_prod_le o
        (CONV_RULE (REWRITE_ORD_CONV switch_lemma_le_order true
                    [switch_lemma_le])) o
      (REWRITE_RULE[switch_lemma_let]))) THEN
  DISCH_RULE (repeat (MATCH_MP
        (TAUT `(A ==> B==>C) ==> (A /\ B ==> C)`))) THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC  REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[REAL_LE_POW_2;
     REAL_ARITH `(&.0 < x ==> &.0 <= x) /\ (&.0 + x = x) /\
          (a <= b ==> &.0 <= b - a) /\
          (a < b ==> &.0 <= b - a) /\
          (~(b < a) ==> &.0 <= b - a) /\
          (~(b <= a) ==> &.0 <= b - a) /\
          (a < b ==> &.0 < b - a) /\
          (~(b <= a) ==> &.0 < b - a)`];;

let ineq_lt_tac = ineq_cert_gen_tac strict_lemma;;
let ineq_le_tac = ineq_cert_gen_tac weak_lemma;;



(* test *)
let test_ineq_tac  = prove_by_refinement(
  `!x y z. (&.0 <= x*y) /\ (&.0 <. z) ==>
             (x*y)  <. x*x + (&.3)*x*y + &.4 `,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  ineq_lt_tac `x * y + x pow 2 + &2 * (&.0 + x * y) + &2 * &2 = x * x + &3 * x * y + &4`;
  ]);;
  (* }}} *)



(* ------------------------------------------------------------------ *)
(* Move quantifier left. Use class.ml and theorems.ml to bubble
   quantifiers towards the head of an expression.  It should move
   quantifiers past other quantifiers, past conjunctions, disjunctions,
   implications, etc.

   val quant_left_CONV : string -> term -> thm = <fun>
   Arguments:
   var_name:string  -- The name of the variable that is to be shifted.

   It tends to return `T` when the conversion fails.

   Example:
   quant_left_CONV "a" `!b. ?a. a = b*4`;;
   val it : thm = |- (!b. ?a. a = b *| 4) <=> (?a. !b. a b = b *| 4)
   *)
(* ------------------------------------------------------------------ *)

let tagb = new_definition `TAGB (x:bool) = x`;;

let is_quant tm = (is_forall tm) or (is_exists tm);;

(*** JRH replaced Comb and Abs with abstract type constructors ***)

let rec tag_quant var_name tm =
  if (is_forall tm && (fst (dest_var (fst (dest_forall tm))) = var_name))
  then mk_comb (`TAGB`,tm)
  else if (is_exists tm && (fst (dest_var (fst (dest_exists tm))) = var_name))   then mk_comb (`TAGB`,tm)
  else match tm with
     | Comb (x,y) -> mk_comb(tag_quant var_name x,tag_quant var_name y)
     | Abs (x,y) -> mk_abs(x,tag_quant var_name y)
     | _ -> tm;;

let quant_left_CONV  =
  (* ~! -> ?~ *)
  let iprove f = prove(f,REWRITE_TAC[tagb] THEN ITAUT_TAC) in
  let NOT_FORALL_TAG = prove(`!P. ~(TAGB(!x. P x)) <=> (?x:A. ~(P x))`,
                             REWRITE_TAC[tagb;NOT_FORALL_THM]) in
 let SKOLEM_TAG =
  prove(`!P. (?y. TAGB (!(x:A). P x ((y:A->B) x))) <=>
     ( (!(x:A). ?y. P x ((y:B))))`,REWRITE_TAC[tagb;SKOLEM_THM]) in
 let SKOLEM_TAG2 =
   prove(`!P. (!x:A. TAGB(?y:B. P x y)) <=> (?y. !x. P x (y x))`,
         REWRITE_TAC[tagb;SKOLEM_THM]) in
 (* !1 !2 -> !2 !1 *)
 let SWAP_FORALL_TAG =
  prove(`!P:A->B->bool. (!x. TAGB(! y. P x y)) <=> (!y x. P x y)`,
    REWRITE_TAC[SWAP_FORALL_THM;tagb]) in
 let SWAP_EXISTS_THM = iprove
  `!P:A->B->bool. (?x. TAGB (?y. P x y)) <=> (?y x. P x y)` in
 (* ! /\ ! -> ! /\ *)
 let AND_FORALL_TAG = prove(`!P Q. (TAGB (!x. P x) /\ TAGB (!x. Q x) <=>
   (!x. P x /\ Q x))`,REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let LEFT_AND_FORALL_TAG = prove(`!P Q. (TAGB (!x. P x) /\  Q) <=>
   (!x. P x /\ Q )`,REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let RIGHT_AND_FORALL_TAG = prove(`!P Q. P /\ TAGB (!x. Q x) <=>
   (!x. P  /\ Q x)`,REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let TRIV_OR_FORALL_TAG = prove
 (`!P Q. TAGB (!x:A. P) \/ TAGB (!x:A. Q) <=> (!x:A. P \/ Q)`,
  REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let RIGHT_IMP_FORALL_TAG = prove
 (`!P Q. (P ==> TAGB (!x:A. Q x)) <=> (!x. P ==> Q x)`,
  REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let OR_EXISTS_THM = iprove
  `!P Q. TAGB (?x. P x) \/ TAGB (?x. Q x) <=> (?x:A. P x \/ Q x)` in
 let LEFT_OR_EXISTS_THM = iprove
 `!P Q. TAGB (?x. P x) \/ Q <=> (?x:A. P x \/ Q)` in
 let RIGHT_OR_EXISTS_THM = iprove
 `!P Q. P \/ TAGB (?x. Q x) <=> (?x:A. P \/ Q x)` in
 let LEFT_AND_EXISTS_THM = iprove
 `!P Q. TAGB (?x:A. P x) /\ Q <=> (?x:A. P x /\ Q)` in
 let RIGHT_AND_EXISTS_THM = iprove
 `!P Q. P /\ TAGB (?x:A. Q x) <=> (?x:A. P /\ Q x)` in
 let TRIV_AND_EXISTS_THM = iprove
 `!P Q. TAGB (?x:A. P) /\ TAGB (?x:A. Q) <=> (?x:A. P /\ Q)` in
 let LEFT_IMP_EXISTS_THM = iprove
 `!P Q. (TAGB (?x:A. P x) ==> Q) <=> (!x. P x ==> Q)` in
 let TRIV_FORALL_IMP_THM = iprove
 `!P Q. (TAGB (?x:A. P) ==> TAGB (!x:A. Q)) <=> (!x:A. P ==> Q) ` in
 let TRIV_EXISTS_IMP_THM = iprove
 `!P Q. (TAGB(!x:A. P) ==> TAGB (?x:A. Q)) <=> (?x:A. P ==> Q) ` in
 let NOT_EXISTS_TAG = prove(
 `!P. ~(TAGB(?x:A. P x)) <=> (!x. ~(P x))`,
 REWRITE_TAC[tagb;NOT_EXISTS_THM]) in
 let LEFT_OR_FORALL_TAG = prove
 (`!P Q. TAGB(!x:A. P x) \/ Q <=> (!x. P x \/ Q)`,
 REWRITE_TAC[tagb;LEFT_OR_FORALL_THM]) in
 let RIGHT_OR_FORALL_TAG = prove
 (`!P Q. P \/ TAGB(!x:A. Q x) <=> (!x. P \/ Q x)`,
  REWRITE_TAC[tagb;RIGHT_OR_FORALL_THM]) in
 let LEFT_IMP_FORALL_TAG = prove
 (`!P Q. (TAGB(!x:A. P x) ==> Q) <=> (?x. P x ==> Q)`,
 REWRITE_TAC[tagb;LEFT_IMP_FORALL_THM]) in
 let RIGHT_IMP_EXISTS_TAG = prove
 (`!P Q. (P ==> TAGB(?x:A. Q x)) <=> (?x:A. P ==> Q x)`,
 REWRITE_TAC[tagb;RIGHT_IMP_EXISTS_THM]) in
  fun var_name tm ->
     REWRITE_RULE [tagb]
       (TOP_SWEEP_CONV
       (GEN_REWRITE_CONV I
         [NOT_FORALL_TAG;SKOLEM_TAG;SKOLEM_TAG2;
          SWAP_FORALL_TAG;SWAP_EXISTS_THM;
          SWAP_EXISTS_THM;
          AND_FORALL_TAG;LEFT_AND_FORALL_TAG;RIGHT_AND_FORALL_TAG;
          TRIV_OR_FORALL_TAG;RIGHT_IMP_FORALL_TAG;
          OR_EXISTS_THM;LEFT_OR_EXISTS_THM;RIGHT_OR_EXISTS_THM;
          LEFT_AND_EXISTS_THM;
          RIGHT_AND_EXISTS_THM;
          TRIV_AND_EXISTS_THM;LEFT_IMP_EXISTS_THM;TRIV_FORALL_IMP_THM;
          TRIV_EXISTS_IMP_THM;NOT_EXISTS_TAG;
          LEFT_OR_FORALL_TAG;RIGHT_OR_FORALL_TAG;LEFT_IMP_FORALL_TAG;
          RIGHT_IMP_EXISTS_TAG;
         ])
       (tag_quant var_name tm));;

(* same, but never pass a quantifier past another. No Skolem, etc. *)
let quant_left_noswap_CONV  =
  (* ~! -> ?~ *)
  let iprove f = prove(f,REWRITE_TAC[tagb] THEN ITAUT_TAC) in
  let NOT_FORALL_TAG = prove(`!P. ~(TAGB(!x. P x)) <=> (?x:A. ~(P x))`,
                             REWRITE_TAC[tagb;NOT_FORALL_THM]) in
 let SKOLEM_TAG =
  prove(`!P. (?y. TAGB (!(x:A). P x ((y:A->B) x))) <=>
     ( (!(x:A). ?y. P x ((y:B))))`,REWRITE_TAC[tagb;SKOLEM_THM]) in
 let SKOLEM_TAG2 =
   prove(`!P. (!x:A. TAGB(?y:B. P x y)) <=> (?y. !x. P x (y x))`,
         REWRITE_TAC[tagb;SKOLEM_THM]) in
 (* !1 !2 -> !2 !1 *)
 let SWAP_FORALL_TAG =
  prove(`!P:A->B->bool. (!x. TAGB(! y. P x y)) <=> (!y x. P x y)`,
    REWRITE_TAC[SWAP_FORALL_THM;tagb]) in
 let SWAP_EXISTS_THM = iprove
  `!P:A->B->bool. (?x. TAGB (?y. P x y)) <=> (?y x. P x y)` in
 (* ! /\ ! -> ! /\ *)
 let AND_FORALL_TAG = prove(`!P Q. (TAGB (!x. P x) /\ TAGB (!x. Q x) <=>
   (!x. P x /\ Q x))`,REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let LEFT_AND_FORALL_TAG = prove(`!P Q. (TAGB (!x. P x) /\  Q) <=>
   (!x. P x /\ Q )`,REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let RIGHT_AND_FORALL_TAG = prove(`!P Q. P /\ TAGB (!x. Q x) <=>
   (!x. P  /\ Q x)`,REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let TRIV_OR_FORALL_TAG = prove
 (`!P Q. TAGB (!x:A. P) \/ TAGB (!x:A. Q) <=> (!x:A. P \/ Q)`,
  REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let RIGHT_IMP_FORALL_TAG = prove
 (`!P Q. (P ==> TAGB (!x:A. Q x)) <=> (!x. P ==> Q x)`,
  REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let OR_EXISTS_THM = iprove
  `!P Q. TAGB (?x. P x) \/ TAGB (?x. Q x) <=> (?x:A. P x \/ Q x)` in
 let LEFT_OR_EXISTS_THM = iprove
 `!P Q. TAGB (?x. P x) \/ Q <=> (?x:A. P x \/ Q)` in
 let RIGHT_OR_EXISTS_THM = iprove
 `!P Q. P \/ TAGB (?x. Q x) <=> (?x:A. P \/ Q x)` in
 let LEFT_AND_EXISTS_THM = iprove
 `!P Q. TAGB (?x:A. P x) /\ Q <=> (?x:A. P x /\ Q)` in
 let RIGHT_AND_EXISTS_THM = iprove
 `!P Q. P /\ TAGB (?x:A. Q x) <=> (?x:A. P /\ Q x)` in
 let TRIV_AND_EXISTS_THM = iprove
 `!P Q. TAGB (?x:A. P) /\ TAGB (?x:A. Q) <=> (?x:A. P /\ Q)` in
 let LEFT_IMP_EXISTS_THM = iprove
 `!P Q. (TAGB (?x:A. P x) ==> Q) <=> (!x. P x ==> Q)` in
 let TRIV_FORALL_IMP_THM = iprove
 `!P Q. (TAGB (?x:A. P) ==> TAGB (!x:A. Q)) <=> (!x:A. P ==> Q) ` in
 let TRIV_EXISTS_IMP_THM = iprove
 `!P Q. (TAGB(!x:A. P) ==> TAGB (?x:A. Q)) <=> (?x:A. P ==> Q) ` in
 let NOT_EXISTS_TAG = prove(
 `!P. ~(TAGB(?x:A. P x)) <=> (!x. ~(P x))`,
 REWRITE_TAC[tagb;NOT_EXISTS_THM]) in
 let LEFT_OR_FORALL_TAG = prove
 (`!P Q. TAGB(!x:A. P x) \/ Q <=> (!x. P x \/ Q)`,
 REWRITE_TAC[tagb;LEFT_OR_FORALL_THM]) in
 let RIGHT_OR_FORALL_TAG = prove
 (`!P Q. P \/ TAGB(!x:A. Q x) <=> (!x. P \/ Q x)`,
  REWRITE_TAC[tagb;RIGHT_OR_FORALL_THM]) in
 let LEFT_IMP_FORALL_TAG = prove
 (`!P Q. (TAGB(!x:A. P x) ==> Q) <=> (?x. P x ==> Q)`,
 REWRITE_TAC[tagb;LEFT_IMP_FORALL_THM]) in
 let RIGHT_IMP_EXISTS_TAG = prove
 (`!P Q. (P ==> TAGB(?x:A. Q x)) <=> (?x:A. P ==> Q x)`,
 REWRITE_TAC[tagb;RIGHT_IMP_EXISTS_THM]) in
  fun var_name tm ->
     REWRITE_RULE [tagb]
       (TOP_SWEEP_CONV
       (GEN_REWRITE_CONV I
         [NOT_FORALL_TAG; (* SKOLEM_TAG;SKOLEM_TAG2; *)
          (* SWAP_FORALL_TAG;SWAP_EXISTS_THM;
          SWAP_EXISTS_THM; *)
          AND_FORALL_TAG;LEFT_AND_FORALL_TAG;RIGHT_AND_FORALL_TAG;
          TRIV_OR_FORALL_TAG;RIGHT_IMP_FORALL_TAG;
          OR_EXISTS_THM;LEFT_OR_EXISTS_THM;RIGHT_OR_EXISTS_THM;
          LEFT_AND_EXISTS_THM;
          RIGHT_AND_EXISTS_THM;
          TRIV_AND_EXISTS_THM;LEFT_IMP_EXISTS_THM;TRIV_FORALL_IMP_THM;
          TRIV_EXISTS_IMP_THM;NOT_EXISTS_TAG;
          LEFT_OR_FORALL_TAG;RIGHT_OR_FORALL_TAG;LEFT_IMP_FORALL_TAG;
          RIGHT_IMP_EXISTS_TAG;
         ])
       (tag_quant var_name tm));;

let quant_right_CONV  =
  (* ~! -> ?~ *)
  let iprove f = prove(f,REWRITE_TAC[tagb] THEN ITAUT_TAC) in
  let NOT_FORALL_TAG = prove(`!P. TAGB(?x:A. ~(P x)) <=> ~((!x. P x))`,
                             REWRITE_TAC[tagb;GSYM NOT_FORALL_THM]) in
 let SKOLEM_TAG =
  prove(`!P. ( TAGB(!(x:A). ?y. P x ((y:B)))) <=>
   (?y.  (!(x:A). P x ((y:A->B) x)))`,
   REWRITE_TAC[tagb;GSYM SKOLEM_THM])
   in
 let SKOLEM_TAG2 =
   prove(`!P. TAGB(?y. !x. P x (y x)) <=> (!x:A. (?y:B. P x y))`,
         REWRITE_TAC[tagb;GSYM SKOLEM_THM]) in
 (* !1 !2 -> !2 !1.. *)
 let SWAP_FORALL_TAG =
  prove(`!P:A->B->bool.  TAGB(!y x. P x y) <=> (!x. (! y. P x y))`,
    REWRITE_TAC[GSYM SWAP_FORALL_THM;tagb]) in
 let SWAP_EXISTS_THM = iprove
  `!P:A->B->bool.  TAGB (?y x. P x y) <=> (?x. (?y. P x y))` in
 (* ! /\ ! -> ! /\ *)
 let AND_FORALL_TAG = iprove`!P Q. TAGB(!x. P x /\ Q x) <=>
   ((!x. P x) /\ (!x. Q x))` in
 let LEFT_AND_FORALL_TAG = prove(`!P Q.
   TAGB(!x. P x /\ Q ) <=> ((!x. P x) /\  Q)`,
   REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let RIGHT_AND_FORALL_TAG = prove(`!P Q.
   TAGB(!x. P  /\ Q x) <=> P /\  (!x. Q x)`,
   REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let TRIV_OR_FORALL_TAG = prove
 (`!P Q.   TAGB(!x:A. P \/ Q) <=>(!x:A. P) \/  (!x:A. Q)`,
  REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let RIGHT_IMP_FORALL_TAG = prove
 (`!P Q. TAGB (!x. P ==> Q x) <=> (P ==>  (!x:A. Q x)) `,
  REWRITE_TAC[tagb] THEN ITAUT_TAC) in
 let OR_EXISTS_THM = iprove
  `!P Q.  TAGB(?x:A. P x \/ Q x) <=> (?x. P x) \/ (?x. Q x) ` in
 let LEFT_OR_EXISTS_THM = iprove
 `!P Q. TAGB (?x:A. P x \/ Q) <=>  (?x. P x) \/ Q ` in
 let RIGHT_OR_EXISTS_THM = iprove
 `!P Q.TAGB (?x:A. P \/ Q x) <=>  P \/ (?x. Q x)` in
 let LEFT_AND_EXISTS_THM = iprove
 `!P Q.TAGB (?x:A. P x /\ Q) <=>  (?x:A. P x) /\ Q` in
 let RIGHT_AND_EXISTS_THM = iprove
 `!P Q. TAGB (?x:A. P /\ Q x) <=>  P /\ (?x:A. Q x) ` in
 let TRIV_AND_EXISTS_THM = iprove
 `!P Q. TAGB(?x:A. P /\ Q) <=>  (?x:A. P) /\  (?x:A. Q) ` in (* *)
 let LEFT_IMP_EXISTS_THM = iprove
 `!P Q. TAGB(!x. P x ==> Q) <=> ( (?x:A. P x) ==> Q) ` in (* *)
 let TRIV_FORALL_IMP_THM = iprove
 `!P Q. TAGB(!x:A. P ==> Q)  <=> ( (?x:A. P) ==>  (!x:A. Q)) ` in
 let TRIV_EXISTS_IMP_THM = iprove
 `!P Q. TAGB(?x:A. P ==> Q)  <=> ((!x:A. P) ==>  (?x:A. Q)) ` in
 let NOT_EXISTS_TAG = prove(
 `!P. TAGB(!x. ~(P x)) <=> ~((?x:A. P x)) `,
 REWRITE_TAC[tagb;NOT_EXISTS_THM]) in
 let LEFT_OR_FORALL_TAG = prove
 (`!P Q. TAGB(!x. P x \/ Q) <=> (!x:A. P x) \/ Q `,
 REWRITE_TAC[tagb;LEFT_OR_FORALL_THM]) in
 let RIGHT_OR_FORALL_TAG = prove
 (`!P Q. TAGB(!x. P \/ Q x) <=> P \/ (!x:A. Q x) `,
  REWRITE_TAC[tagb;RIGHT_OR_FORALL_THM]) in
 let LEFT_IMP_FORALL_TAG = prove
 (`!P Q. TAGB(?x. P x ==> Q) <=> ((!x:A. P x) ==> Q) `,
 REWRITE_TAC[tagb;LEFT_IMP_FORALL_THM]) in
 let RIGHT_IMP_EXISTS_TAG = prove
 (`!P Q. TAGB(?x:A. P ==> Q x) <=> (P ==> (?x:A. Q x)) `,
 REWRITE_TAC[tagb;RIGHT_IMP_EXISTS_THM]) in
  fun var_name tm ->
     REWRITE_RULE [tagb]
       (TOP_SWEEP_CONV
       (GEN_REWRITE_CONV I
         [NOT_FORALL_TAG;SKOLEM_TAG;SKOLEM_TAG2;
          SWAP_FORALL_TAG;SWAP_EXISTS_THM;
          SWAP_EXISTS_THM;
          AND_FORALL_TAG;LEFT_AND_FORALL_TAG;RIGHT_AND_FORALL_TAG;
          TRIV_OR_FORALL_TAG;RIGHT_IMP_FORALL_TAG;
          OR_EXISTS_THM;LEFT_OR_EXISTS_THM;RIGHT_OR_EXISTS_THM;
          LEFT_AND_EXISTS_THM;
          RIGHT_AND_EXISTS_THM;
          TRIV_AND_EXISTS_THM;LEFT_IMP_EXISTS_THM;TRIV_FORALL_IMP_THM;
          TRIV_EXISTS_IMP_THM;NOT_EXISTS_TAG;
          LEFT_OR_FORALL_TAG;RIGHT_OR_FORALL_TAG;LEFT_IMP_FORALL_TAG;
          RIGHT_IMP_EXISTS_TAG;
         ])
       (tag_quant var_name tm));;


(* ------------------------------------------------------------------ *)
(* Dropping Superfluous Quantifiers .
    Example: ?u. (u = t) /\ ...
    We can eliminate the u.
 *)
(* ------------------------------------------------------------------ *)

let mark_term = new_definition `mark_term (u:A) = u`;;

(*** JRH replaced Comb and Abs with explicit constructors ***)

let rec markq qname tm =
  match tm with
   Var (a,b) -> if (a=qname) then mk_icomb (`mark_term:A->A`,tm) else tm
  |Const(_,_) -> tm
  |Comb(s,b) -> mk_comb(markq qname s,markq qname b)
  |Abs (x,t) -> mk_abs(x,markq qname t);;

let rec getquants tm =
  if (is_forall tm) then
     (fst (dest_var (fst (dest_forall tm))))::
        (getquants (snd (dest_forall tm)))
  else if (is_exists tm) then
     (fst (dest_var (fst (dest_exists tm))))::
        (getquants (snd (dest_exists tm)))
  else match tm with
    Comb(s,b) -> (getquants s) @ (getquants b)
  | Abs (x,t) -> (getquants t)
  | _ -> [];;

(* can loop if there are TWO *)
let rewrite_conjs = [
  prove_by_refinement (`!A B C. (A /\ B) /\ C <=> A /\ B /\ C`,[REWRITE_TAC[CONJ_ACI]]);
  prove_by_refinement (`!u. (mark_term (u:A) = mark_term u) <=> T`,[MESON_TAC[]]);
  prove_by_refinement (`!u t. (t = mark_term (u:A)) <=> (mark_term u = t)`,[MESON_TAC[]]);
  prove_by_refinement (`!u a b. (mark_term (u:A) = a) /\ (mark_term u = b) <=> (mark_term u = a) /\ (a = b)`,[MESON_TAC[]]);
  prove_by_refinement (`!u a b B. (mark_term (u:A) = a) /\ (mark_term u = b) /\ B <=> (mark_term u = a) /\ (a = b) /\ B`,[MESON_TAC[]]);
  prove_by_refinement (`!u t A C. A /\ (mark_term (u:A) = t) /\ C <=>
        (mark_term u = t) /\ A /\ C`,[MESON_TAC[]]);
  prove_by_refinement (`!A u t. A /\ (mark_term (u:A) = t)  <=>
        (mark_term u = t) /\ A `,[MESON_TAC[]]);
  prove_by_refinement (`!u t C D. (((mark_term (u:A) = t) /\ C) ==> D) <=>
        ((mark_term (u:A) = t) ==> C ==> D)`,[MESON_TAC[]]);
  prove_by_refinement (`!A u t B. (A ==> (mark_term (u:A) = t) ==> B) <=>
         ((mark_term (u:A) = t) ==> A ==> B)`,[MESON_TAC[]]);
];;

let higher_conjs = [
  prove_by_refinement (`!C u t. ((mark_term u = t) ==> C (mark_term u)) <=>
       ((mark_term u = t) ==> C (t:A))`,[MESON_TAC[mark_term]]);
  prove_by_refinement (`!C u t. ((mark_term u = t) /\ C (mark_term u)) <=>
         ((mark_term u = t) /\ C (t:A))`,[MESON_TAC[mark_term]]);
];;


let dropq_conv  =
  let drop_exist =
    REWRITE_CONV [prove_by_refinement (`!t. ?(u:A). (u = t)`,[MESON_TAC[]])] in
  fun qname tm ->
  let quanlist =  getquants tm in
  let quantleft_CONV = EVERY_CONV
      (map (REPEATC o quant_left_noswap_CONV) quanlist) in
  let qname_conv tm = prove(mk_eq(tm,markq qname tm),
             REWRITE_TAC[mark_term]) in
  let conj_conv = REWRITE_CONV rewrite_conjs in
  let quantright_CONV = (REPEATC (quant_right_CONV qname)) in
  let drop_mark_CONV = REWRITE_CONV [mark_term] in
 (quantleft_CONV THENC qname_conv  THENC conj_conv   THENC
      (ONCE_REWRITE_CONV higher_conjs)
       THENC drop_mark_CONV THENC quantright_CONV THENC
       drop_exist  ) tm ;;


(* Examples : *)
dropq_conv "u" `!P Q R . (?(u:B). (?(x:A). (u = P x) /\ (Q x)) /\ (R u))`;;
dropq_conv "t" `!P Q R. (!(t:B). (?(x:A). P x /\ (t = Q x)) ==> R t)`;;

dropq_conv "u" `?u v.
     ((t * (a + &1) + (&1 - t) *a = u) /\
      (t * (b + &0) + (&1 - t) * b = v)) /\
     a < u /\
     u < r /\
     (v = b)`;;



(* ------------------------------------------------------------------ *)
(*  SOME GENERAL TACTICS FOR THE ASSUMPTION LIST *)
(* ------------------------------------------------------------------ *)

let (%) i = HYP (string_of_int i);;

let WITH i rule = (H_VAL (rule) (HYP (string_of_int i))) ;;

let (UND:int -> tactic) =
 fun i (asl,w) ->
   let name = "Z-"^(string_of_int i) in
   try let thm= assoc name asl in
        let tm = concl (thm) in
       let (_,asl') = partition (fun t-> ((=) name (fst t))) asl in
       null_meta,[asl',mk_imp(tm,w)],
       fun i [th] -> MP th (INSTANTIATE_ALL i thm)
   with Failure _ -> failwith "UND";;

let KILL i =
  (UND i) THEN (DISCH_THEN (fun t -> ALL_TAC));;

let USE i rule = (WITH i rule) THEN (KILL i);;

let CHO i = (UND i) THEN (DISCH_THEN CHOOSE_TAC);;

let X_CHO i t = (UND i) THEN (DISCH_THEN (X_CHOOSE_TAC t));;

let AND i = (UND i) THEN
  (DISCH_THEN (fun t-> (ASSUME_TAC (CONJUNCT1 t)
                          THEN (ASSUME_TAC (CONJUNCT2 t)))));;

let JOIN i j =
   (H_VAL2 CONJ ((%)i) ((%)j)) THEN (KILL i) THEN (KILL j);;

let COPY i = WITH i I;;

let REP n tac = EVERY (replicate tac n);;

let REWR i = (UND i) THEN (ASM_REWRITE_TAC[]) THEN DISCH_TAC;;

let LEFT i t = (USE i (CONV_RULE (quant_left_CONV t)));;

let RIGHT i t =  (USE i (CONV_RULE (quant_right_CONV t)));;

let LEFT_TAC  t = ((CONV_TAC (quant_left_CONV t)));;

let RIGHT_TAC t =  ( (CONV_TAC (quant_right_CONV t)));;

let INR = REWRITE_RULE[IN];;

(*



let rec REP n tac = if (n<=0) then ALL_TAC
  else (tac THEN (REP (n-1) tac));;  (* doesn't seem to work? *)


let COPY i = (UNDISCH_WITH i) THEN (DISCH_THEN (fun t->ALL_TAC));;


MANIPULATING ASSUMPTIONS. (MAKE 0= GOAL)

COPY: int -> tactic   Make a copy in adjacent slot.


EXPAND: int -> tactic.
    conjunction -> two separate.
    exists/goal-forall -> choose.
    goal-if-then -> discharge
EXPAND_TERM: int -> term -> tactic.
    constant -> expand definition or other rewrites associated.
ADD: term -> tactic.

SIMPLIFY: int -> tactic.  Apply simplification rules.


*)

let CONTRAPOSITIVE_TAC = MATCH_MP_TAC (TAUT `(~q ==> ~p) ==> (p ==> q)`)
                           THEN REWRITE_TAC[];;

let REWRT_TAC = (fun t-> REWRITE_TAC[t]);;

let (REDUCE_CONV,REDUCE_TAC) =
 let list = [
   (* reals *)   REAL_NEG_GE0;
   REAL_HALF_DOUBLE;
   REAL_SUB_REFL ;
   REAL_NEG_NEG;
   REAL_LE; LE_0;
   REAL_ADD_LINV;REAL_ADD_RINV;
   REAL_NEG_0;
   REAL_NEG_LE0;
   REAL_NEG_GE0;
   REAL_LE_NEGL;
   REAL_LE_NEGR;
   REAL_LE_NEG;
   REAL_NEG_EQ_0;
   REAL_SUB_RNEG;
   REAL_ARITH `!(x:real). (--x = x) <=>  (x = &.0)`;
   REAL_ARITH `!(a:real) b. (a - b + b) = a`;
   REAL_ADD_LID;
   REAL_ADD_RID ;
   REAL_INV_0;
   REAL_OF_NUM_EQ;
   REAL_OF_NUM_LE;
   REAL_OF_NUM_LT;
   REAL_OF_NUM_ADD;
   REAL_OF_NUM_MUL;
   REAL_POS;
   REAL_MUL_RZERO;
   REAL_MUL_LZERO;
   REAL_LE_01;
   REAL_SUB_RZERO;
   REAL_LE_SQUARE;
   REAL_MUL_RID;
   REAL_MUL_LID;
   REAL_ABS_ZERO;
   REAL_ABS_NUM;
   REAL_ABS_1;
   REAL_ABS_NEG;
   REAL_ABS_POS;
   ABS_ZERO;
   ABS_ABS;
   REAL_NEG_LT0;
   REAL_NEG_GT0;
   REAL_LT_NEG;
   REAL_NEG_MUL2;
   REAL_OF_NUM_POW;
   REAL_LT_INV_EQ;
   REAL_POW_1;
   REAL_INV2;
   prove (`(--. (&.n) < (&.m)) <=> (&.0 < (&.n) + (&.m))`,REAL_ARITH_TAC);
   prove (`(--. (&.n) <= (&.m)) <=> (&.0 <= (&.n) + (&.m))`,REAL_ARITH_TAC);
   prove (`(--. (&.n) = (&.m)) <=> ((&.n) + (&.m) = (&.0))`,REAL_ARITH_TAC);
   prove (`((&.n) < --.(&.m)) <=> ((&.n) + (&.m) <. (&.0))`,REAL_ARITH_TAC);
   prove (`((&.n) <= --.(&.m)) <=> ((&.n) + (&.m) <=. (&.0))`,REAL_ARITH_TAC);
   prove (`((&.n) = --.(&.m)) <=> ((&.n) + (&.m) = (&.0))`,REAL_ARITH_TAC);
   prove (`((&.n) < --.(&.m) + &.r) <=> ((&.n) + (&.m) < (&.r))`,REAL_ARITH_TAC);
   prove (`(--. x = --. y) <=> (x = y)`,REAL_ARITH_TAC);
   prove (`(--(&.n) < --.(&.m) + &.r) <=> ( (&.m) < &.n + (&.r))`,REAL_ARITH_TAC);
   prove (`(--. x = --. y) <=> (x = y)`,REAL_ARITH_TAC);
   prove (`((--. (&.1))*  x < --. y <=> y < x)`,REAL_ARITH_TAC );
   prove (`((--. (&.1))*  x <= --. y <=> y <= x)`,REAL_ARITH_TAC );
   (* num *)
   EXP_1;
   EXP_LT_0;
   ADD_0;
   ARITH_RULE `0+| m  = m`;
   ADD_EQ_0;
   prove (`(0 = m +|n) <=> (m = 0)/\ (n=0)`,MESON_TAC[ADD_EQ_0]);
   EQ_ADD_LCANCEL_0;
   EQ_ADD_RCANCEL_0;
   LT_ADD;
   LT_ADDR;
   ARITH_RULE `(0 = j -| i) <=> (j <=| i)`;
   ARITH_RULE `(j -| i = 0) <=> (j <=| i)`;
   ARITH_RULE `0 -| i = 0`;
   ARITH_RULE `(i<=| j) /\ (j <=| i) <=> (i = j)`;
   ARITH_RULE `0 <| 1`;
   (* SUC *)
   NOT_SUC;
   SUC_INJ;
   PRE;
   ADD_CLAUSES;
   MULT;
   MULT_CLAUSES;
   LE; LT;
   ARITH_RULE `SUC b -| 1 = b`;
   ARITH_RULE `SUC b -| b = 1`;
   prove(`&.(SUC x) - &.x = &.1`,
      REWRITE_TAC [REAL_ARITH `(a -. b=c) <=> (a  = b+.c)`;
      REAL_OF_NUM_ADD;REAL_OF_NUM_EQ] THEN ARITH_TAC);
   (* (o) *)
   o_DEF;
   (* I *)
   I_THM;
   I_O_ID;
   (* pow *)
   REAL_POW_1;
   REAL_POW_ONE;
   (* INT *)
   INT_ADD_LINV;
   INT_ADD_RINV;
   INT_ADD_SUB2;
   INT_EQ_NEG2;
   INT_LE_NEG;
   INT_LE_NEGL;
   INT_LE_NEGR;
   INT_LT_NEG;
   INT_LT_NEG2;
   INT_NEGNEG;
   INT_NEG_0;
   INT_NEG_EQ_0;
   INT_NEG_GE0;
   INT_NEG_GT0;
   INT_NEG_LE0;
   INT_NEG_LT0;
   GSYM INT_NEG_MINUS1;
   INT_NEG_MUL2;
   INT_NEG_NEG;
   (* sets *)
   ] in
(REWRITE_CONV list,REWRITE_TAC list);;





(* prove by squaring *)
let REAL_POW_2_LE = prove_by_refinement(
  `!x y. (&.0 <= x) /\ (&.0 <= y) /\ (x pow 2 <=. y pow 2) ==> (x <=. y)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  MP_TAC (SPECL[` (x:real) pow 2`;`(y:real)pow 2`] SQRT_MONO_LE);
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[REAL_POW_LE];
  ASM_SIMP_TAC[POW_2_SQRT];
  ]);;
  (* }}} *)

(* prove by squaring *)
let REAL_POW_2_LT = prove_by_refinement(
  `!x y. (&.0 <= x) /\ (&.0 <= y) /\ (x pow 2 <. y pow 2) ==> (x <. y)`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  MP_TAC (SPECL[` (x:real) pow 2`;`(y:real)pow 2`] SQRT_MONO_LT);
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[REAL_POW_LE];
  ASM_SIMP_TAC[POW_2_SQRT];
  ]);;

  (* }}} *)

let SQUARE_TAC =
    FIRST[
      MATCH_MP_TAC REAL_LE_LSQRT;
      MATCH_MP_TAC REAL_POW_2_LT;
      MATCH_MP_TAC REAL_POW_2_LE
    ]
    THEN REWRITE_TAC[];;

(****)

let SPEC2_TAC t = SPEC_TAC (t,t);;

let IN_ELIM i = (USE i (REWRITE_RULE[IN]));;

let rec range i n =
  if (n>0) then (i::(range (i+1) (n-1))) else [];;


(* in elimination *)

let (IN_OUT_TAC: tactic) =
   fun (asl,g) -> (REWRITE_TAC [IN] THEN
   (EVERY (map (IN_ELIM) (range 0 (length asl))))) (asl,g);;

let (IWRITE_TAC : thm list -> tactic) =
   fun thlist -> REWRITE_TAC (map INR thlist);;

let (IWRITE_RULE : thm list -> thm -> thm) =
   fun thlist -> REWRITE_RULE (map INR thlist);;

let IMATCH_MP imp ant = MATCH_MP (INR imp) (INR ant);;

let IMATCH_MP_TAC imp  = MATCH_MP_TAC  (INR imp);;


let GBETA_TAC =   (CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV));;
let GBETA_RULE =   (CONV_RULE (TOP_DEPTH_CONV GEN_BETA_CONV));;

(* breaks antecedent into multiple cases *)
let REP_CASES_TAC =
  REPEAT (DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC));;

let TSPEC t i  = TYPE_THEN t (USE i o SPEC);;

let IMP_REAL t i = (USE i (MATCH_MP (REAL_ARITH t)));;

(* goes from f = g to fz = gz *)
let TAPP z i  = TYPE_THEN z (fun u -> (USE i(fun t -> AP_THM t u)));;

(* ONE NEW TACTIC -- DOESN'T WORK!! DON'T USE....
let CONCL_TAC t = let co = snd  (dest_imp (concl t)) in
  SUBGOAL_TAC co THEN (TRY (IMATCH_MP_TAC  t));;
*)

(* subgoal the antecedent of a THM, in order to USE the conclusion *)
let ANT_TAC t = let (ant,co) =   (dest_imp (concl t)) in
  SUBGOAL_TAC ant
  THENL [ALL_TAC;DISCH_THEN (fun u-> MP_TAC (MATCH_MP t u))];;


let TH_INTRO_TAC tl th = TYPEL_THEN tl (fun t-> ANT_TAC (ISPECL t th));;

let THM_INTRO_TAC tl th = TYPEL_THEN tl
  (fun t->
    let s = ISPECL t th in
    if is_imp (concl s) then ANT_TAC s else ASSUME_TAC s);;

let (DISCH_THEN_FULL_REWRITE:tactic) =
      DISCH_THEN (fun t-> REWRITE_TAC[t] THEN
                    (RULE_ASSUM_TAC  (REWRITE_RULE[t])));;

let FULL_REWRITE_TAC t = (REWRITE_TAC t THEN (RULE_ASSUM_TAC (REWRITE_RULE t)));;

(* ------------------------------------------------------------------ *)

let BASIC_TAC  =
  [ GEN_TAC;
    IMATCH_MP_TAC  (TAUT ` (a ==> b ==> C) ==> ( a /\ b ==> C)`);
    DISCH_THEN (CHOOSE_THEN MP_TAC);
    FIRST_ASSUM (fun t-> UNDISCH_TAC (concl t) THEN
              (DISCH_THEN CHOOSE_TAC));
    FIRST_ASSUM (fun t ->
        (if (length (CONJUNCTS t) < 2) then failwith "BASIC_TAC"
         else UNDISCH_TAC (concl t)));
    DISCH_TAC;
  ];;

let REP_BASIC_TAC = REPEAT (CHANGED_TAC (FIRST BASIC_TAC));;

(* ------------------------------------------------------------------ *)

let USE_FIRST rule =
  FIRST_ASSUM (fun t -> (UNDISCH_TAC (concl t) THEN
   (DISCH_THEN (ASSUME_TAC o rule))));;

let WITH_FIRST rule =
  FIRST_ASSUM (fun t -> ASSUME_TAC (rule t));;

let UNDF t = (TYPE_THEN t UNDISCH_FIND_TAC );;

let GRABF t ttac = (UNDF t THEN (DISCH_THEN ttac));;

let USEF t rule =
    (TYPE_THEN t (fun t' -> UNDISCH_FIND_THEN t'
                        (fun u -> ASSUME_TAC (rule u))));;


(* ------------------------------------------------------------------ *)
(* UNIFY_EXISTS_TAC *)
(* ------------------------------------------------------------------ *)

let rec EXISTSL_TAC tml = match tml with
  a::tml' -> EXISTS_TAC a THEN EXISTSL_TAC tml' |
  [] -> ALL_TAC;;

(*
  Goal:  ?x1....xn. P1 /\ ... /\ Pm
  Try to pick ALL of x1...xn to unify ONE or more Pi with terms
  appearing in the assumption list, trying term_unify on
  each Pi with each assumption.
*)
let (UNIFY_EXISTS_TAC:tactic) =
  let run_one wc assum (varl,sofar)  =
    if varl = [] then (varl,sofar) else
      try (
        let wc' = instantiate ([],sofar,[]) wc in
        let (_,ins,_) = term_unify varl wc' assum in
        let insv = map snd ins in
          ( subtract varl insv  , union sofar ins    )
      ) with failure -> (varl,sofar) in
  let run_onel asl wc (varl,sofar)   =
    itlist (run_one wc) asl (varl,sofar) in
  let run_all varl sofar wcl asl =
    itlist (run_onel asl) wcl (varl,sofar) in
  let full_unify (asl,w) =
    let (varl,ws) = strip_exists w in
    let vargl = map genvar (map type_of varl) in
    let wg = instantiate ([],zip vargl varl,[]) ws in
    let wcg = conjuncts wg in
    let (vargl',sofar) = run_all vargl [] wcg ( asl) in
      if (vargl' = []) then
        map (C rev_assoc sofar) (map (C rev_assoc (zip vargl varl)) varl)
      else failwith "full_unify: unification not found " in
  fun (asl,w) ->
    try(
      let asl' = map (concl o snd) asl in
      let asl'' = flat (map (conjuncts ) asl') in
      let varsub = full_unify (asl'',w) in
        EXISTSL_TAC varsub (asl,w)
    ) with failure -> failwith "UNIFY_EXIST_TAC: unification not found.";;

(* partial example *)
let unify_exists_tac_example = try(prove_by_refinement(
  `!C a b v A R TX U SS. (A v /\ (a = v) /\  (C:num->num->bool) a b /\ R a ==>
    ?v v'. TX v' /\ U v v' /\  C v' v /\ SS v)`,
  (* {{{ proof *)

  [
  REP_BASIC_TAC;
  UNIFY_EXISTS_TAC; (* v' -> a  and v -> b *)
  (* not finished. Here is a variant approach. *)
  REP_GEN_TAC;
  DISCH_TAC;
  UNIFY_EXISTS_TAC;
  ])) with failure -> (REFL `T`);;

  (* }}} *)

(* ------------------------------------------------------------------ *)
(* UNIFY_EXISTS conversion *)
(* ------------------------------------------------------------------ *)

(*
   FIRST argument is the "certificate"
   second arg is the goal.
   Example:
   UNIFY_EXISTS `(f:num->bool) x` `?t. (f:num->bool) t`
*)

let (UNIFY_EXISTS:thm -> term -> thm) =
  let run_one wc assum (varl,sofar)  =
    if varl = [] then (varl,sofar) else
      try (
        let wc' = instantiate ([],sofar,[]) wc in
        let (_,ins,_) = term_unify varl wc' assum in
        let insv = map snd ins in
          ( subtract varl insv  , union sofar ins    )
      ) with failure -> (varl,sofar) in
  let run_onel asl wc (varl,sofar)   =
    itlist (run_one wc) asl (varl,sofar) in
  let run_all varl sofar wcl asl =
    itlist (run_onel asl) wcl (varl,sofar) in
  let full_unify (t,w) =
    let (varl,ws) = strip_exists w in
    let vargl = map genvar (map type_of varl) in
    let wg = instantiate ([],zip vargl varl,[]) ws in
    let wcg = conjuncts wg in
    let (vargl',sofar) = run_all vargl [] wcg ( [concl t]) in
      if (vargl' = []) then
        map (C rev_assoc sofar) (map (C rev_assoc (zip vargl varl)) varl)
      else failwith "full_unify: unification not found " in
  fun t w ->
    try(
      if not(is_exists w) then failwith "UNIFY_EXISTS: not EXISTS" else
      let varl' =  (full_unify (t,w)) in
      let (varl,ws) = strip_exists w in
      let varsub = zip varl' varl in
      let varlb = map (fun s->  chop_list s (rev varl))
            (range 1 (length varl)) in
      let targets = map (fun s-> (instantiate ([],varsub,[])
          (list_mk_exists( rev (fst s),  ws)) )) varlb in
      let target_zip  = zip (rev targets) varl' in
      itlist (fun s th  -> EXISTS s  th) target_zip t
    ) with failure -> failwith "UNIFY_EXISTS: unification not found.";;

let unify_exists_example=
   UNIFY_EXISTS (ARITH_RULE `2 = 0+2`) `(?x y. ((x:num) = y))`;;

(* now make a prover for it *)


(* ------------------------------------------------------------------ *)

(*
drop_ant_tac replaces
  0  A ==>B
  1  A
with
  0  B
  1  A
in hypothesis list
*)
let DROP_ANT_TAC pq  =
  UNDISCH_TAC pq THEN (UNDISCH_TAC (fst (dest_imp pq))) THEN
  DISCH_THEN (fun pthm -> ASSUME_TAC pthm THEN
      DISCH_THEN (fun pqthm -> ASSUME_TAC (MATCH_MP pqthm pthm )));;

let (DROP_ALL_ANT_TAC:tactic) =
  fun (asl,w) ->
    let imps = filter (is_imp) (map (concl o snd) asl) in
    MAP_EVERY (TRY o DROP_ANT_TAC) imps (asl,w);;

let drop_ant_tac_example = prove_by_refinement(
  `!A B C D E. (A /\ (A ==> B) /\ (C ==>D) /\ C) ==> (E \/ C \/ B)`,
  (* {{{ proof *)
  [
  REP_BASIC_TAC;
  DROP_ALL_ANT_TAC;
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

(* ------------------------------------------------------------------ *)

(* ASSUME tm, then prove it later. almost the same as asm-cases-tac *)
let (BACK_TAC : term -> tactic) =
  fun tm (asl,w) ->
    let ng = mk_imp (tm,w) in
    (SUBGOAL_TAC ng THENL [ALL_TAC;DISCH_THEN  IMATCH_MP_TAC ]) (asl,w);;

(* --- *)
(* Using hash numbers for tactics *)
(* --- *)

let label_of_hash ((asl,g):goal) (h:int) =
  let one_label h (s,tm) =
    if  (h = hash_of_term (concl tm)) then
      let s1 = String.sub s 2 (String.length s - 2) in
      int_of_string s1
      else failwith "label_of_hash" in
  tryfind (one_label h) asl;;

let HASHIFY m h w = m (label_of_hash w h) w;;
let UNDH = HASHIFY UND;;
let REWRH = HASHIFY REWR;;
let KILLH = HASHIFY KILL;;
let COPYH = HASHIFY COPY;;
let HASHIFY1 m h tm w = m (label_of_hash w h) tm w;;
let USEH = HASHIFY1 USE;;
let LEFTH = HASHIFY1 LEFT;;
let RIGHTH = HASHIFY1 RIGHT;;
let TSPECH tm h w = TSPEC tm (label_of_hash w h) w ;;
