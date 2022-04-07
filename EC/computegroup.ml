(* ========================================================================= *)
(* Explicit computations of group operations from extensible clauses.        *)
(* ========================================================================= *)

needs "Library/grouptheory.ml";;
needs "Library/ringtheory.ml";;

let curve_clauses = ref ([]:thm list)
and curvezero_clauses = ref ([]:thm list)
and curveneg_clauses = ref ([]:thm list)
and curveadd_clauses = ref ([]:thm list)
and ecgroup_carriers = ref ([]:thm list)
and ecgroup_ids = ref ([]:thm list)
and ecgroup_invs = ref ([]:thm list)
and ecgroup_muls = ref ([]:thm list);;

(* ------------------------------------------------------------------------- *)
(* Augment store of clauses, both curve types and actual specific curves.    *)
(* ------------------------------------------------------------------------- *)

let add_curve th = (curve_clauses := insert th (!curve_clauses));;
let add_curvezero th = (curvezero_clauses := insert th (!curvezero_clauses));;
let add_curveneg th = (curveneg_clauses := insert th (!curveneg_clauses));;
let add_curveadd th = (curveadd_clauses := insert th (!curveadd_clauses));;

let add_ecgroup defs th =
  let [cth;ith;nth;ath] = CONJUNCTS(PURE_REWRITE_RULE defs th) in
  (ecgroup_carriers := insert cth (!ecgroup_carriers);
   ecgroup_ids := insert ith (!ecgroup_ids);
   ecgroup_invs := insert nth (!ecgroup_invs);
   ecgroup_muls := insert ath (!ecgroup_muls));;

(* ------------------------------------------------------------------------- *)
(* The actual conversions.                                                   *)
(* ------------------------------------------------------------------------- *)

let ECGROUP_CARRIER_CONV tm =
 (GEN_REWRITE_CONV RAND_CONV (!ecgroup_carriers) THENC
  GEN_REWRITE_CONV I [IN] THENC
  GEN_REWRITE_CONV I (!curve_clauses) THENC
  REWRITE_CONV[IN_INTEGER_MOD_RING_CARRIER] THENC
  DEPTH_CONV(INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV)) tm;;

let ECGROUP_ID_CONV tm =
 (GEN_REWRITE_CONV I (!ecgroup_ids) THENC
  TRY_CONV(GEN_REWRITE_CONV I (!curvezero_clauses) THENC
           DEPTH_CONV INTEGER_MOD_RING_RED_CONV)) tm;;

let ECGROUP_INV_CONV tm =
 (GEN_REWRITE_CONV RATOR_CONV (!ecgroup_invs) THENC
  GEN_REWRITE_CONV I (!curveneg_clauses) THENC
  DEPTH_CONV INTEGER_MOD_RING_RED_CONV) tm;;

let ECGROUP_MUL_CONV tm =
 (GEN_REWRITE_CONV (RATOR_CONV o RATOR_CONV) (!ecgroup_muls) THENC
  GEN_REWRITE_CONV I (!curveadd_clauses) THENC
  DEPTH_CONV(INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV) THENC
  REPEATC(let_CONV THENC DEPTH_CONV INTEGER_MOD_RING_RED_CONV)) tm;;

let ECGROUP_POW_CONV =
  let pth = prove
   (`!G x m n.
        x IN group_carrier G
        ==> group_pow G x (2 * n) = group_pow G (group_mul G x x) n`,
   SIMP_TAC[GSYM GROUP_POW_2; GROUP_POW_POW])
  and dth = prove
   (`NUMERAL(BIT0 n) = 2 * NUMERAL n`,
    REWRITE_TAC[MULT_2] THEN REWRITE_TAC[BIT0] THEN
    REWRITE_TAC[NUMERAL]) in
  let num_half_CONV = GEN_REWRITE_CONV I [dth] in
  let conv_0 tm =
   (GEN_REWRITE_CONV I [CONJUNCT1 group_pow] THENC
    ECGROUP_ID_CONV) tm
  and conv_1 = GEN_REWRITE_CONV I [CONJUNCT2 group_pow]
  and conv_2 = PART_MATCH (lhand o rand) pth in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Const("group_pow",_),g),x),ntm) ->
        let n = dest_numeral ntm in
        if n =/ num_0 then conv_0 tm
        else if mod_num n num_2 =/ num_1 then
          (RAND_CONV num_CONV THENC conv_1 THENC
           RAND_CONV conv THENC ECGROUP_MUL_CONV) tm
        else
          let th1 = RAND_CONV num_half_CONV tm in
          let th2 = conv_2 (rand(concl th1)) in
          let th3 = MP th2
           (EQT_ELIM((ECGROUP_CARRIER_CONV(lhand(concl th2))))) in
          let th4 = TRANS th1 th3 in
          CONV_RULE(RAND_CONV(LAND_CONV ECGROUP_MUL_CONV THENC conv)) th4
     | _ -> failwith "ECGROUP_POW_CONV" in
  conv;;
