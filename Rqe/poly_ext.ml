let poly_tm = `poly`;;

let dest_poly tm =
  let poly,[l;var] = strip_ncomb 2 tm in
  if not (poly = poly_tm) then failwith "dest_poly: not a poly"
  else l,var;;

let is_poly tm = fst (strip_comb tm) = `poly`;;

(* ------------------------------------------------------------------------- *)
(* Get the lead variable in polynomial; &1 if a constant.                    *)
(* ------------------------------------------------------------------------- *)

let polyvar =
  let dummy_tm = `&1` in
  fun tm -> if is_ratconst tm then dummy_tm else lhand(rand tm);;


(*
let k00 = `&3 * x * y pow 2 + &2 * x pow 2 * y * z + z * x + &3 * y * z`
let k0 = `(&0 + y * (&0 + z * &3)) + x * (((&0 + z * &1) + y * (&0 + y * &3)) +  x * (&0 + y * (&0 + z * &2)))`;;
# polyvar k0;;
val it : Term.term = `x`
*)

(* ---------------------------------------------------------------------- *)
(*  Is a constant polynomial (wrt variable ordering)                      *)
(* ---------------------------------------------------------------------- *)

let is_constant vars p =
  assert (not (vars = []));
  try
    let l,r = dest_plus p in
    let x,r2 = dest_mult r in
      if x = hd vars then false else true
  with _ ->
    if p = hd vars then false else true;;

(* ------------------------------------------------------------------------- *)
(* We only use this as a handy way to do derivatives.                        *)
(* ------------------------------------------------------------------------- *)

let POLY = prove
 (`(poly [] x = &0) /\
   (poly [__c__] x = __c__) /\
   (poly (CONS __h__ __t__) x = __h__ + x * poly __t__ x)`,
   REWRITE_TAC[poly] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Convert in and out of list representations.                               *)
(* ------------------------------------------------------------------------- *)

(* THIS IS BAD CODE!!!  It depends on the names of the variables in POLY *)
let POLY_ENLIST_CONV vars =
  let lem = GEN rx POLY in
  let [cnv_0; cnv_1; cnv_2] =
    map (fun th -> GEN_REWRITE_CONV I [GSYM th]) (CONJUNCTS (ISPEC (hd vars) lem))
  and zero_tm = rzero in
  let rec conv tm =
    if polyvar tm = hd vars then
      (funpow 2 RAND_CONV conv THENC cnv_2) tm
    else if tm = zero_tm then cnv_0 tm
    else cnv_1 tm in
    conv;;


(*
map GSYM (CONJUNCTS (ISPEC (hd vars) lem))

POLY_ENLIST_CONV vars p in

let tm = `&0 + c * &1`



POLY_ENLIST_CONV vars tm

#trace conv
POLY_ENLIST_CONV vars tm
let vars = [ry;rx]
let tm =  `&0 + y * (&0 + x * &1)`


let k1 = rhs(concl (POLY_ENLIST_CONV [`x:real`;`y:real`;`z:real`] k0));;
POLY_ENLIST_CONV [`x:real`;`y:real`;`z:real`] k0;;
val it : Hol.thm =
  |- k0 =
     poly [&0 + y * (&0 + z * &3);
           &0 * z * &1 + y * (&0 + y * &3);
           &0 + y * (&0 + z * &2)] x
*)

let POLY_DELIST_CONV =
  let [cnv_0; cnv_1; cnv_2] =
    map (fun th -> GEN_REWRITE_CONV I [th]) (CONJUNCTS POLY) in
  let rec conv tm =
    (cnv_0 ORELSEC cnv_1 ORELSEC (cnv_2 THENC funpow 2 RAND_CONV conv)) tm in
  conv;;

(*
# POLY_DELIST_CONV `poly [&5; &6; &7] x`;;
val it : Hol.thm = |- poly [&5; &6; &7] x = &5 + x * (&6 + x * &7)
*)

(* ------------------------------------------------------------------------- *)
(* Differentiation within list representation.                               *)
(* ------------------------------------------------------------------------- *)

(* let poly_diff_aux = new_recursive_definition list_RECURSION *)
(*   `(poly_diff_aux n [] = []) /\ *)
(*    (poly_diff_aux n (CONS h t) = CONS (&n * h) (poly_diff_aux (SUC n) t))`;; *)

(* let poly_diff = new_definition *)
(*   `poly_diff l = if l = [] then [] else poly_diff_aux 1 (TL l)`;; *)

let POLY_DIFF_CLAUSES = prove
 (`(poly_diff [] = []) /\
   (poly_diff [c] = []) /\
   (poly_diff (CONS h t) = poly_diff_aux 1 t)`,
  REWRITE_TAC[poly_diff; NOT_CONS_NIL; HD; TL; poly_diff_aux]);;

let POLY_DIFF_LEMMA = prove
 (`!l n x. ((\x. (x pow (SUC n)) * poly l x) diffl
                   ((x pow n) * poly (poly_diff_aux (SUC n) l) x))(x)`,
(* {{{ Proof *)

  LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly; poly_diff_aux; REAL_MUL_RZERO; DIFF_CONST] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:real`] THEN
  REWRITE_TAC[REAL_LDISTRIB; REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] (CONJUNCT2 pow))] THEN
  POP_ASSUM(MP_TAC o SPECL [`SUC n`; `x:real`]) THEN
  SUBGOAL_THEN `(((\x. (x pow (SUC n)) * h)) diffl
                        ((x pow n) * &(SUC n) * h))(x)`
  (fun th -> DISCH_THEN(MP_TAC o CONJ th)) THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MP_TAC(SPEC `\x. x pow (SUC n)` DIFF_CMUL) THEN BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPEC `SUC n` DIFF_POW) THEN REWRITE_TAC[SUC_SUB1] THEN
    DISCH_THEN(MATCH_ACCEPT_TAC o ONCE_REWRITE_RULE[REAL_MUL_SYM]);
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC]]);;

(* }}} *)

let POLY_DIFF = prove
 (`!l x. ((\x. poly l x) diffl (poly (poly_diff l) x))(x)`,
(* {{{ Proof *)

  LIST_INDUCT_TAC THEN REWRITE_TAC[POLY_DIFF_CLAUSES] THEN
  ONCE_REWRITE_TAC[SYM(ETA_CONV `\x. poly l x`)] THEN
  REWRITE_TAC[poly; DIFF_CONST] THEN
  MAP_EVERY X_GEN_TAC [`x:real`] THEN
  MP_TAC(SPECL [`t:(real)list`; `0`; `x:real`] POLY_DIFF_LEMMA) THEN
  REWRITE_TAC[SYM(num_CONV `1`)] THEN REWRITE_TAC[pow; REAL_MUL_LID] THEN
  REWRITE_TAC[POW_1] THEN
  DISCH_THEN(MP_TAC o CONJ (SPECL [`h:real`; `x:real`] DIFF_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD_LID]);;

(* }}} *)

let CANON_POLY_DIFF_CONV =
  let aux_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 poly_diff_aux]
  and aux_conv1 = GEN_REWRITE_CONV I [CONJUNCT2 poly_diff_aux]
  and diff_conv0 = GEN_REWRITE_CONV I (butlast (CONJUNCTS POLY_DIFF_CLAUSES))
  and diff_conv1 = GEN_REWRITE_CONV I [last (CONJUNCTS POLY_DIFF_CLAUSES)] in
  let rec POLY_DIFF_AUX_CONV tm =
   (aux_conv0 ORELSEC
    (aux_conv1 THENC
     RAND_CONV (LAND_CONV NUM_SUC_CONV THENC POLY_DIFF_AUX_CONV))) tm in
  diff_conv0 ORELSEC
  (diff_conv1 THENC POLY_DIFF_AUX_CONV);;

(*

# POLY_DIFF_CONV (mk_comb(`poly_diff`,k2));;
val it : Hol.thm =
  |- poly_diff k2 =
     [&1 * (&0 * z * &1 + y * (&0 + y * &3)); &2 * (&0 + y * (&0 + z * &2))]
*)

(* ------------------------------------------------------------------------- *)
(* Whether the first of two items comes earlier in the list.                 *)
(* ------------------------------------------------------------------------- *)

let rec earlier l x y =
  match l with
    h::t -> if h = y then false
              else if h = x then true
              else earlier t x y
  | [] -> false;;

(* ------------------------------------------------------------------------- *)
(* Add polynomials.                                                          *)
(* ------------------------------------------------------------------------- *)

let POLY_ADD_CONV =
  let [cnv_r; cnv_l; cnv_2; cnv_0] = (map REWR_CONV o CONJUNCTS o REAL_ARITH)
    `(pol1 + (d + y * q) = (pol1 + d) + y * q) /\
     ((c + x * p) + pol2 = (c + pol2) + x * p) /\
     ((c + x * p) + (d + x * q) = (c + d) + x * (p + q)) /\
     (c + x * &0 = c)`
  and dest_add = dest_binop `(+)` in
  let rec POLY_ADD_CONV vars tm =
    let pol1,pol2 = dest_add tm in
    let x = polyvar pol1 and y = polyvar pol2 in
    if not(is_var x) && not(is_var y) then REAL_RAT_REDUCE_CONV tm else
    if not(is_var y) || earlier vars x y then
      (cnv_l THENC LAND_CONV (POLY_ADD_CONV vars)) tm
    else if not(is_var x) || earlier vars y x then
      (cnv_r THENC LAND_CONV (POLY_ADD_CONV vars)) tm
    else
      (cnv_2 THENC COMB_CONV(RAND_CONV(POLY_ADD_CONV vars)) THENC
       TRY_CONV cnv_0) tm in
  POLY_ADD_CONV;;

(*
# POLY_ADD_CONV [`x:real`;`y:real`;`z:real`] (mk_binop `(+)` k0 k0) ;;
val it : Hol.thm =
  |- ((&0 + y * (&0 + z * &3)) +
      x *
      (((&0 + z * &1) + y * (&0 + y * &3)) + x * (&0 + y * (&0 + z * &2)))) +
     (&0 + y * (&0 + z * &3)) +
     x * (((&0 + z * &1) + y * (&0 + y * &3)) + x * (&0 + y * (&0 + z * &2))) =
     (&0 + y * (&0 + z * &6)) +
     x * (((&0 + z * &2) + y * (&0 + y * &6)) + x * (&0 + y * (&0 + z * &4)))
*)

(* ------------------------------------------------------------------------- *)
(* Negate polynomials.                                                       *)
(* ------------------------------------------------------------------------- *)

let POLY_NEG_CONV =
  let cnv = REWR_CONV(REAL_ARITH `--(c + x * p) = --c + x * --p`) in
  let rec POLY_NEG_CONV tm =
    if is_ratconst(rand tm) then REAL_RAT_NEG_CONV tm else
    (cnv THENC COMB_CONV(RAND_CONV POLY_NEG_CONV)) tm in
  POLY_NEG_CONV;;

(* ------------------------------------------------------------------------- *)
(* Subtract polynomials.                                                     *)
(* ------------------------------------------------------------------------- *)

let POLY_SUB_CONV =
  let cnv = REWR_CONV real_sub in
  fun vars -> cnv THENC RAND_CONV POLY_NEG_CONV THENC POLY_ADD_CONV vars;;

(* ------------------------------------------------------------------------- *)
(* Multiply polynomials.                                                     *)
(* ------------------------------------------------------------------------- *)

let POLY_MUL_CONV =
  let [cnv_l1; cnv_r1; cnv_2; cnv_l0; cnv_r0] =
    (map REWR_CONV o CONJUNCTS o REAL_ARITH)
    `(pol1 * (d + y * q) = (pol1 * d) + y * (pol1 * q)) /\
     ((c + x * p) * pol2 = (c * pol2) + x * (p * pol2)) /\
     (pol1 * (d + x * q) = pol1 * d + (&0 + x * pol1 * q)) /\
     (&0 * pol2 = &0) /\
     (pol1 * &0 = &0)`
  and dest_mul = dest_binop `( * )`
  and zero_tm = `&0` in
  let rec POLY_MUL_CONV vars tm =
    let pol1,pol2 = dest_mul tm in
    if pol1 = zero_tm then cnv_l0 tm
    else if pol2 = zero_tm then cnv_r0 tm
    else if is_ratconst pol1 && is_ratconst pol2 then REAL_RAT_MUL_CONV tm else
    let x = polyvar pol1 and y = polyvar pol2 in
    if not(is_var y) || earlier vars x y then
      (cnv_r1 THENC COMB_CONV(RAND_CONV(POLY_MUL_CONV vars))) tm
    else if not(is_var x) || earlier vars y x then
      (cnv_l1 THENC COMB_CONV(RAND_CONV(POLY_MUL_CONV vars))) tm
    else
      (cnv_2 THENC COMB2_CONV (RAND_CONV(POLY_MUL_CONV vars))
                              (funpow 2 RAND_CONV (POLY_MUL_CONV vars)) THENC
       POLY_ADD_CONV vars) tm in
  POLY_MUL_CONV;;

(*

# POLY_MUL_CONV [`x:real`;`y:real`;`z:real`] (mk_binop `( * )` k0 k0) ;;
val it : Hol.thm =
  |- ((&0 + y * (&0 + z * &3)) +
      x *
      (((&0 + z * &1) + y * (&0 + y * &3)) + x * (&0 + y * (&0 + z * &2)))) *
     ((&0 + y * (&0 + z * &3)) +
      x *
      (((&0 + z * &1) + y * (&0 + y * &3)) + x * (&0 + y * (&0 + z * &2)))) =
     (&0 + y * (&0 + y * (&0 + z * (&0 + z * &9)))) +
     x *
     ((&0 + y * ((&0 + z * (&0 + z * &6)) + y * (&0 + y * (&0 + z * &18)))) +
      x *
      (((&0 + z * (&0 + z * &1)) +
        y * (&0 + y * ((&0 + z * (&6 + z * &12)) + y * (&0 + y * &9)))) +
       x *
       ((&0 + y * ((&0 + z * (&0 + z * &4)) + y * (&0 + y * (&0 + z * &12)))) +
        x * (&0 + y * (&0 + y * (&0 + z * (&0 + z * &4)))))))
*)


(* ------------------------------------------------------------------------- *)
(* Exponentiate polynomials.                                                 *)
(* ------------------------------------------------------------------------- *)

let POLY_POW_CONV =
  let [cnv_0; cnv_1] = map REWR_CONV (CONJUNCTS real_pow)
  and zero_tm = `0` in
  let rec POLY_POW_CONV vars tm =
    if rand tm = zero_tm then cnv_0 tm else
    (RAND_CONV num_CONV THENC cnv_1 THENC
     RAND_CONV (POLY_POW_CONV vars) THENC
     POLY_MUL_CONV vars) tm in
  POLY_POW_CONV;;

(*
# POLY_POW_CONV [`x:real`;`y:real`;`z:real`] (mk_binop `(pow)` k0 `2`) ;;
val it : Hol.thm =
  |- ((&0 + y * (&0 + z * &3)) +
      x *
      (((&0 + z * &1) + y * (&0 + y * &3)) + x * (&0 + y * (&0 + z * &2)))) pow
     2 =
     (&0 + y * (&0 + y * (&0 + z * (&0 + z * &9)))) +
     x *
     ((&0 + y * ((&0 + z * (&0 + z * &6)) + y * (&0 + y * (&0 + z * &18)))) +
      x *
      (((&0 + z * (&0 + z * &1)) +
        y * (&0 + y * ((&0 + z * (&6 + z * &12)) + y * (&0 + y * &9)))) +
       x *
       ((&0 + y * ((&0 + z * (&0 + z * &4)) + y * (&0 + y * (&0 + z * &12)))) +
        x * (&0 + y * (&0 + y * (&0 + z * (&0 + z * &4)))))))
*)

(* ------------------------------------------------------------------------- *)
(* Convert expression to canonical polynomials.                              *)
(* ------------------------------------------------------------------------- *)

let POLYNATE_CONV =
  let cnv_var = REWR_CONV(REAL_ARITH `x = &0 + x * &1`)
  and cnv_div = REWR_CONV real_div
  and neg_tm = `(--)`
  and add_tm = `(+)`
  and sub_tm = `(-)`
  and mul_tm = `( * )`
  and pow_tm = `(pow)`
  and div_tm = `(/)` in
  let rec POLYNATE_CONV vars tm =
    if is_var tm then cnv_var tm
    else if is_ratconst tm then REFL tm else
    let lop,r = dest_comb tm in
    if lop = neg_tm
    then (RAND_CONV(POLYNATE_CONV vars) THENC POLY_NEG_CONV) tm else
    let op,l = dest_comb lop in
    if op = pow_tm then
      (LAND_CONV(POLYNATE_CONV vars) THENC POLY_POW_CONV vars) tm
    else if op = div_tm then
      (cnv_div THENC
       COMB2_CONV (RAND_CONV(POLYNATE_CONV vars)) REAL_RAT_REDUCE_CONV THENC
       POLY_MUL_CONV vars) tm else
    let cnv = if op = add_tm then POLY_ADD_CONV
              else if op = sub_tm then POLY_SUB_CONV
              else if op = mul_tm then POLY_MUL_CONV
              else failwith "POLYNATE_CONV: unknown operation" in
    (BINOP_CONV (POLYNATE_CONV vars) THENC cnv vars) tm in
  POLYNATE_CONV;;

(*
POLYNATE_CONV [`x:real`;`y:real`] `x + y`;;
POLYNATE_CONV [`x:real`;`y:real`] `x * y + &2 * y`;;
*)

(* ------------------------------------------------------------------------- *)
(* Pure term manipulation versions; will optimize eventually.                *)
(* ------------------------------------------------------------------------- *)

let poly_add_ =
  let add_tm = `(+)` in
  fun vars p1 p2 ->
    rand(concl(POLY_ADD_CONV vars (mk_comb(mk_comb(add_tm,p1),p2))));;

let poly_sub_ =
  let sub_tm = `(-)` in
  fun vars p1 p2 ->
    rand(concl(POLY_SUB_CONV vars (mk_comb(mk_comb(sub_tm,p1),p2))));;

let poly_mul_ =
  let mul_tm = `( * )` in
  fun vars p1 p2 ->
    rand(concl(POLY_MUL_CONV vars (mk_comb(mk_comb(mul_tm,p1),p2))));;

let poly_neg_ =
  let neg_tm = `(--)` in
  fun p -> rand(concl(POLY_NEG_CONV(mk_comb(neg_tm,p))));;

let poly_pow_ =
  let pow_tm = `(pow)` in
  fun vars p k ->
    rand(concl(POLY_POW_CONV vars
      (mk_comb(mk_comb(pow_tm,p),mk_small_numeral k))));;

(* ------------------------------------------------------------------------- *)
(* Get the degree of a polynomial.                                           *)
(* ------------------------------------------------------------------------- *)

let rec degree_ vars tm =
  if polyvar tm = hd vars then 1 + degree_ vars (funpow 2 rand tm)
  else 0;;

(* ------------------------------------------------------------------------- *)
(* Get the list of coefficients.                                             *)
(* ------------------------------------------------------------------------- *)

let rec coefficients vars tm =
  if polyvar tm = hd vars then (lhand tm)::coefficients vars (funpow 2 rand tm)
  else [tm];;

(* ------------------------------------------------------------------------- *)
(* Get the head constant.                                                    *)
(* ------------------------------------------------------------------------- *)

let head vars p = last(coefficients vars p);;

(* ---------------------------------------------------------------------- *)
(*  Remove the head coefficient                                           *)
(* ---------------------------------------------------------------------- *)

let rec behead vars tm =
  try
    let c,r = dest_plus tm in
    let x,p = dest_mult r in
    if not (x = hd vars) then failwith "" else
    let p' = behead vars p in
      if p' = rzero then c
      else mk_plus c (mk_mult x p')
  with _ -> rzero;;

(*
behead [`x:real`] `&1 + x * (&1 + x * (&0 + y * &1))`
*)


let BEHEAD =
  let lem = ARITH_RULE `a + b * &0 = a` in
  fun vars zthm tm ->
    let tm' = behead vars tm in
      (* note: pure rewrite is ok here, as tm is in canonical form *)
    let thm1 = PURE_REWRITE_CONV[zthm] tm in
    let thm2 = PURE_REWRITE_CONV[lem] (rhs(concl thm1)) in
    let thm3 = TRANS thm1 thm2 in
      thm3;;

let BEHEAD3 =
  let lem = ARITH_RULE `a + b * &0 = a` in
  fun vars zthm tm ->
    let tm' = behead vars tm in
    (* note slight hack here:
       BEHEAD was working fine if
       p = a + x * b where a <> b.  But
       when they were equal, dropping multiple levels
       broke the reconstruction.  Thus, we only do conversion
       on the right except when the head variable has been fully eliminated *)
    let conv =
      let l,r = dest_binop rp tm in
      let l1,r1 = dest_binop rm r in
        if l1 = hd vars then RAND_CONV(PURE_ONCE_REWRITE_CONV[zthm])
        else PURE_ONCE_REWRITE_CONV[zthm] in
    let thm1 = conv tm in
    let thm2 = PURE_REWRITE_CONV[lem] (rhs(concl thm1)) in
    let thm3 = TRANS thm1 thm2 in
      thm3;;

let BEHEAD = BEHEAD3;;


(*
let vars = [`z:real`;`x:real`]
let zthm = (ASSUME `&0 + x * &1 = &0`)
let tm = `(&0 + x * &1) + z * (&0 + x * &1)`
behead vars tm
BEHEAD vars zthm tm
BEHEAD2 vars zthm tm
BEHEAD3 vars zthm tm

let tm = `(&0 + x * &1)`
BEHEAD3 vars zthm tm



let vars = [`x:real`]
let tm = `&1 + x * (&1 + x * (&0 + y * &1))`
let zthm = (ASSUME `&0 + y * &1 = &0`)
BEHEAD vars zthm tm
BEHEAD2 vars zthm tm



*)

(* ------------------------------------------------------------------------- *)
(* Test whether a polynomial is a constant w.r.t. the head variable.         *)
(* ------------------------------------------------------------------------- *)

let is_const_poly vars tm = polyvar tm <> hd vars;;

(* ------------------------------------------------------------------------- *)
(* Get the constant multiple of the "maximal" monomial (implicit lex order)  *)
(* ------------------------------------------------------------------------- *)

let rec headconst p =
  try rat_of_term p with Failure _ -> headconst(funpow 2 rand p);;

(* ------------------------------------------------------------------------- *)
(* Monicize; return |- const * pol = monic-pol                               *)
(* ------------------------------------------------------------------------- *)

let MONIC_CONV =
  let mul_tm = `( * ):real->real->real` in
  fun vars p ->
    let c = Int 1 // headconst p in
    POLY_MUL_CONV vars (mk_comb(mk_comb(mul_tm,term_of_rat c),p));;

(* ------------------------------------------------------------------------- *)
(* Pseudo-division of s by p; head coefficient of p assumed nonzero.         *)
(* Returns |- a^k s = p q + r for some q and r with deg(r) < deg(p).         *)
(* Optimized only for the trivial case of equal head coefficients; no GCDs.  *)
(* ------------------------------------------------------------------------- *)

let PDIVIDE =
  let zero_tm = `&0`
  and add0_tm = `(+) (&0)`
  and add_tm = `(+)`
  and mul_tm = `( * )`
  and pow_tm = `(pow)`
  and one_tm = `&1` in
  let mk_varpow vars k =
    let mulx_tm = mk_comb(mul_tm,hd vars) in
    funpow k (fun t -> mk_comb(add0_tm,mk_comb(mulx_tm,t))) one_tm in
  let rec pdivide_aux vars a n p s =
    if s = zero_tm then (0,zero_tm,s) else
    let b = head vars s and m = degree_ vars s in
    if m < n then (0,zero_tm,s) else
    let xp = mk_varpow vars (m - n) in
    let p' = poly_mul_ vars xp p in
    if a = b then
      let (k,q,r) = pdivide_aux vars a n p (poly_sub_ vars s p') in
      (k,poly_add_ vars q (poly_mul_ vars xp (poly_pow_ vars a k)),r)
    else
      let (k,q,r) = pdivide_aux vars a n p
        (poly_sub_ vars (poly_mul_ vars a s) (poly_mul_ vars b p')) in
      let q' = poly_add_ vars q (poly_mul_ vars b
                (poly_mul_ vars (poly_pow_ vars a k) xp)) in
      (k+1,q',r) in
  fun vars s p ->
    let a = head vars p in
    let (k,q,r) = pdivide_aux vars a (degree_ vars p) p s in
    let th1 = POLY_MUL_CONV vars (mk_comb(mk_comb(mul_tm,q),p)) in
    let th2 = AP_THM (AP_TERM add_tm th1) r in
    let th3 = CONV_RULE(RAND_CONV(POLY_ADD_CONV vars)) th2 in
    let th4 = POLY_POW_CONV vars
     (mk_comb(mk_comb(pow_tm,a),mk_small_numeral k)) in
    let th5 = AP_THM (AP_TERM mul_tm th4) s in
    let th6 = CONV_RULE(RAND_CONV(POLY_MUL_CONV vars)) th5 in
    TRANS th6 (GSYM th3);;

(* ------------------------------------------------------------------------- *)
(* Produce sign theorem for rational constant.                               *)
(* ------------------------------------------------------------------------- *)

let SIGN_CONST =
  let zero = Int 0
  and zero_tm = `&0`
  and eq_tm = `(=):real->real->bool`
  and gt_tm = `(>):real->real->bool`
  and lt_tm = `(<):real->real->bool` in
  fun tm ->
    let x = rat_of_term tm in
    if x =/ zero then
      EQT_ELIM(REAL_RAT_EQ_CONV(mk_comb(mk_comb(eq_tm,tm),zero_tm)))
    else if x >/ zero then
      EQT_ELIM(REAL_RAT_GT_CONV(mk_comb(mk_comb(gt_tm,tm),zero_tm)))
    else
      EQT_ELIM(REAL_RAT_LT_CONV(mk_comb(mk_comb(lt_tm,tm),zero_tm)));;

(*
SIGN_CONST `-- &5`;;
val it : Hol.thm = |- &5 > &0
*)


(* ------------------------------------------------------------------------- *)
(* Differentiation conversion in main representation.                        *)
(* ------------------------------------------------------------------------- *)

let POLY_DERIV_CONV =
  let poly_diff_tm = `poly_diff`
  and pth = GEN_REWRITE_RULE I [SWAP_FORALL_THM] POLY_DIFF in
  fun vars tm ->
    let th1 = POLY_ENLIST_CONV vars tm in
    let th2 = SPECL [hd vars; lhand(rand(concl th1))] pth in
    CONV_RULE(RATOR_CONV
      (COMB2_CONV (RAND_CONV(ABS_CONV(POLY_DELIST_CONV)))
                  (LAND_CONV(CANON_POLY_DIFF_CONV THENC
                             LIST_CONV (POLY_MUL_CONV vars)) THENC
                   POLY_DELIST_CONV))) th2;;

(*
let k0 = (rhs o concl) (POLYNATE_CONV [`x:real`] `x pow 2 * y`);;
let vars = [`x:real`]
let tm = k0
let k1 = concl th2
let k2 = rator k1
let l,r = dest_comb k2

RATOR_CONV
(RAND_CONV(ABS_CONV(POLY_DELIST_CONV))) l
(LAND_CONV(POLY_DIFF_CONV THENC LIST_CONV (CANON_POLY_MUL_CONV vars)) THENC POLY_DELIST_CONV) r
(LAND_CONV(POLY_DIFF_CONV THENC LIST_CONV (CANON_POLY_MUL_CONV vars))) r
(LAND_CONV(POLY_DIFF_CONV)) r


POLY_DERIV_CONV [`x:real`] (rhs(concl((POLYNATE_CONV [`x:real`] `x pow 2 * y`))));;
val it : Hol.thm =
  |- ((\x. &0 + x * (&0 + x * (&0 + y * &1))) diffl &0 + x * (&0 + y * &2)) x
*)

(* ---------------------------------------------------------------------- *)
(*  POLYATOM_CONV                                                         *)
(* ---------------------------------------------------------------------- *)

(*
  This is the AFN_CONV argument to the lifting function LIFT_QELIM_CONV
*)

let lt_lem = prove_by_refinement(
  `!x y. x < y <=> x - y < &0`,
(* {{{ Proof *)
[
  REAL_ARITH_TAC;
]);;
(* }}} *)

let le_lem = prove_by_refinement(
  `!x y. x <= y <=> x - y <= &0`,
(* {{{ Proof *)
[
  REAL_ARITH_TAC;
]);;
(* }}} *)

let eq_lem = prove_by_refinement(
  `!x y. (x = y) <=> (x - y = &0)`,
(* {{{ Proof *)
[
  REAL_ARITH_TAC;
]);;
(* }}} *)

let POLYATOM_CONV vars tm =
  let thm1 = ONCE_REWRITE_CONV[real_gt;real_ge;eq_lem] tm in
  let l,r = dest_eq (concl thm1) in
  let thm2 = ONCE_REWRITE_CONV[lt_lem;le_lem] r in
  let op,l',r' = get_binop (rhs (concl thm2)) in
  let thm3a = POLYNATE_CONV vars l' in
  let thm3b = AP_TERM op thm3a in
  let thm3 = AP_THM thm3b rzero in
    end_itlist TRANS [thm1;thm2;thm3];;

(*

let k0 = `x pow 2 + y * x - &5 > x + &10`
let k0 = `x pow 2 + y * x - &5 >= x + &10`
let k0 = `x pow 2 + y * x - &5 < x + &10`
let k0 = `x pow 2 + y * x - &5 <= x + &10`
let k0 = `x pow 2 + y * x - &5 = x + &10`
let tm = k0;;
let vars = [`x:real`;`y:real`]
POLYATOM_CONV vars  k0

let vars = [`e:real`; `k:real`;`f:real`;`a:real`]
prioritize_real()
let tm = `k < e`

let liouville =
 `&6 * (w pow 2 + x pow 2 + y pow 2 + z pow 2) pow 2 =
   (((w + x) pow 4 + (w + y) pow 4 + (w + z) pow 4 +
     (x + y) pow 4 + (x + z) pow 4 + (y + z) pow 4) +
    ((w - x) pow 4 + (w - y) pow 4 + (w - z) pow 4 +
     (x - y) pow 4 + (x - z) pow 4 + (y - z) pow 4))`

let lvars = [`w:real`;`x:real`;`y:real`; `z:real`]

POLYATOM_CONV lvars liouville

*)

(* ---------------------------------------------------------------------- *)
(*  Factoring                                                             *)
(* ---------------------------------------------------------------------- *)

let weakfactor x pol =
  let rec weakfactor k x pol =
    try
      let ls,rs = dest_plus pol in
      if not (ls = rzero) then failwith "" else
      let lm,rm = dest_mult rs in
      if not (lm = x) then failwith "" else
        weakfactor (k + 1) x rm
    with Failure _ ->
      k,pol in
    weakfactor 0 x pol;;

let poly_var x = mk_plus rzero (mk_mult x rone);;
(*
   poly_var rx
*)

let POW_PROD_SUM = prove_by_refinement(
  `!x n m. (x pow n) * x pow m = x pow (n + m)`,
(* {{{ Proof *)
[
  STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC;
  REWRITE_TAC[real_pow];
  NUM_SIMP_TAC;
  REAL_SIMP_TAC;
  REWRITE_TAC[real_pow];
  REWRITE_TAC[ARITH_RULE `n + SUC m = SUC (n + m)`];
  REWRITE_TAC[real_pow];
  POP_ASSUM (SUBST1_TAC o GSYM);
  REAL_ARITH_TAC;
]);;
(* }}} *)

let lem1 = REAL_ARITH `x * x = x pow 2`;;
let lem2 = GSYM (CONJUNCT2 real_pow);;
let lem3 = REAL_ARITH `!x. x = x pow 1`;;

let SIMP_POW_CONV tm =
  let thm1 = ((REWRITE_CONV [GSYM REAL_MUL_ASSOC;lem1;lem2;POW_PROD_SUM]) THENC (ARITH_SIMP_CONV[])) tm in
  let _,r = dest_eq (concl thm1) in
  if can dest_pow r then thm1 else
  let thm2 = ISPEC r lem3 in
    thm2;;

(*
  SIMP_POW_CONV `x * x * x * x * x`
  SIMP_POW_CONV `x * x * (x * x) * x`
  SIMP_POW_CONV `x * (x * (x * x)) *(x * x)`
  SIMP_POW_CONV `x:real`

*)


let WEAKFACTOR_CONV x pol =
  let k,pol' = weakfactor x pol in
  let thm1 = ((itlist2 (fun x y z -> ((funpow y RAND_CONV) x) THENC z)
               (replicate (GEN_REWRITE_CONV I [REAL_ADD_LID]) k)
               (0--(k-1)) ALL_CONV) THENC
             (PURE_REWRITE_CONV[REAL_MUL_ASSOC])) pol in
  let thm2 = (CONV_RULE (RAND_CONV (LAND_CONV SIMP_POW_CONV))) thm1 in
    thm2;;



(*
  let pol = `&0 + x * (&0 + x * (&0 + y * &1))`
  let pol = `&0 + x * (&0 + x * (&0 + x * (&0 + x * (&0 + x * (&0 + x * (&0 + y * &1))))))`
  let pol = `&0 + x * (&0 + x * (&0 + x * (&0 + x * (&0 + x * (&1 + x * (&0 + y * &1))))))`
  let pol = `&1 + x * (&0 + x * (&0 + y * &1))`
  let pol = `&0 + x * (&1 + x * (&0 + y * &1))`
  WEAKFACTOR_CONV rx pol
  weakfactor rx pol

*)
