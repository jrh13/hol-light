type ite = False | True | Atomic of int | Ite of ite*ite*ite;;

let rec norm e =
  match e with
    Ite(False,y,z) -> norm z
  | Ite(True,y,z) -> norm y
  | Ite(Atomic i,y,z) -> Ite(Atomic i,norm y,norm z)
  | Ite(Ite(u,v,w),y,z) -> norm(Ite(u,Ite(v,y,z),Ite(w,y,z)))
  | _ -> e;;

let ite_INDUCT,ite_RECURSION = define_type
 "ite = False | True | Atomic num | Ite ite ite ite";;

let eth = prove_general_recursive_function_exists
 `?norm. (norm False = False) /\
         (norm True = True) /\
         (!i. norm (Atomic i) = Atomic i) /\
         (!y z. norm (Ite False y z) = norm z) /\
         (!y z. norm (Ite True y z) = norm y) /\
         (!i y z. norm (Ite (Atomic i) y z) =
                    Ite (Atomic i) (norm y) (norm z)) /\
         (!u v w y z. norm (Ite (Ite u v w) y z) =
                        norm (Ite u (Ite v y z) (Ite w y z)))`;;

let sizeof = define
 `(sizeof False = 1) /\
  (sizeof True = 1) /\
  (sizeof(Atomic i) = 1) /\
  (sizeof(Ite x y z) = sizeof x * (1 + sizeof y + sizeof z))`;;

let eth' =
  let th = prove
   (hd(hyp eth),
    EXISTS_TAC `MEASURE sizeof` THEN
    REWRITE_TAC[WF_MEASURE; MEASURE_LE; MEASURE; sizeof] THEN ARITH_TAC) in
  PROVE_HYP th eth;;

let norm = new_specification ["norm"] eth';;

let SIZEOF_INDUCT = REWRITE_RULE[WF_IND; MEASURE]  (ISPEC`sizeof` WF_MEASURE);;

let SIZEOF_NZ = prove
 (`!e. ~(sizeof e = 0)`,
  MATCH_MP_TAC ite_INDUCT THEN SIMP_TAC[sizeof; ADD_EQ_0; MULT_EQ_0; ARITH]);;

let ITE_INDUCT = prove
 (`!P. P False /\
       P True /\
       (!i. P(Atomic i)) /\
       (!y z. P z ==> P(Ite False y z)) /\
       (!y z. P y ==> P(Ite True y z)) /\
       (!i y z. P y /\ P z ==> P (Ite (Atomic i) y z)) /\
       (!u v w x y z. P(Ite u (Ite v y z) (Ite w y z))
                      ==> P(Ite (Ite u v w) y z))
       ==> !e. P e`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SIZEOF_INDUCT THEN
  MATCH_MP_TAC ite_INDUCT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ite_INDUCT THEN POP_ASSUM_LIST
   (fun ths -> REPEAT STRIP_TAC THEN FIRST(mapfilter MATCH_MP_TAC ths)) THEN
  REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[sizeof] THEN TRY ARITH_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[MULT_AC; ADD_AC; LT_ADD_LCANCEL] THEN
  REWRITE_TAC[ADD_ASSOC; LT_ADD_RCANCEL] THEN
  MATCH_MP_TAC(ARITH_RULE `~(b = 0) /\ ~(c = 0) ==> a < (b + a) + c`) THEN
  REWRITE_TAC[MULT_EQ_0; SIZEOF_NZ]);;

let normalized = define
 `(normalized False <=> T) /\
  (normalized True <=> T) /\
  (normalized(Atomic a) <=> T) /\
  (normalized(Ite False x y) <=> F) /\
  (normalized(Ite True x y) <=> F) /\
  (normalized(Ite (Atomic a) x y) <=> normalized x /\ normalized y) /\
  (normalized(Ite (Ite u v w) x y) <=> F)`;;

let NORMALIZED_NORM = prove
 (`!e. normalized(norm e)`,
  MATCH_MP_TAC ITE_INDUCT THEN REWRITE_TAC[norm; normalized]);;

let NORMALIZED_INDUCT = prove
 (`P False /\
   P True /\
   (!i. P (Atomic i)) /\
   (!i x y. P x /\ P y ==> P (Ite (Atomic i) x y))
   ==> !e. normalized e ==> P e`,
  STRIP_TAC THEN MATCH_MP_TAC ite_INDUCT THEN ASM_REWRITE_TAC[normalized] THEN
  MATCH_MP_TAC ite_INDUCT THEN ASM_MESON_TAC[normalized]);;

let holds = define
 `(holds v False <=> F) /\
  (holds v True <=> T) /\
  (holds v (Atomic i) <=> v(i)) /\
  (holds v (Ite b x y) <=> if holds v b then holds v x else holds v y)`;;

let HOLDS_NORM = prove
 (`!e v. holds v (norm e) <=> holds v e`,
  MATCH_MP_TAC ITE_INDUCT THEN SIMP_TAC[holds; norm] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

let taut = define
 `(taut (t,f) False <=> F) /\
  (taut (t,f) True <=> T) /\
  (taut (t,f) (Atomic i) <=> MEM i t) /\
  (taut (t,f) (Ite (Atomic i) x y) <=>
      if MEM i t then taut (t,f) x
      else if MEM i f then taut (t,f) y
      else taut (CONS i t,f) x /\ taut (t,CONS i f) y)`;;

let tautology = define `tautology e = taut([],[]) (norm e)`;;

let NORMALIZED_TAUT = prove
 (`!e. normalized e
       ==> !f t. (!a. ~(MEM a t /\ MEM a f))
                 ==> (taut (t,f) e <=>
                      !v. (!a. MEM a t ==> v(a)) /\ (!a. MEM a f ==> ~v(a))
                          ==> holds v e)`,
  MATCH_MP_TAC NORMALIZED_INDUCT THEN REWRITE_TAC[holds; taut] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `\a:num. MEM a t` THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ALL_TAC; DISCH_THEN MATCH_MP_TAC] THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[])] THEN
  ASM_SIMP_TAC[MEM; RIGHT_OR_DISTRIB; LEFT_OR_DISTRIB;
               MESON[] `(!a. ~(MEM a t /\ a = i)) <=> ~(MEM i t)`;
               MESON[] `(!a. ~(a = i /\ MEM a f)) <=> ~(MEM i f)`] THEN
  ASM_REWRITE_TAC[AND_FORALL_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  MESON_TAC[]);;

let TAUTOLOGY = prove
 (`!e. tautology e <=> !v. holds v e`,
  MESON_TAC[tautology; HOLDS_NORM; NORMALIZED_TAUT; MEM; NORMALIZED_NORM]);;

let HOLDS_BACK = prove
 (`!v. (F <=> holds v False) /\
       (T <=> holds v True) /\
       (!i. v i <=> holds v (Atomic i)) /\
       (!p. ~holds v p <=> holds v (Ite p False True)) /\
       (!p q. (holds v p /\ holds v q) <=> holds v (Ite p q False)) /\
       (!p q. (holds v p \/ holds v q) <=> holds v (Ite p True q)) /\
       (!p q. (holds v p <=> holds v q) <=>
                   holds v (Ite p q (Ite q False True))) /\
       (!p q. holds v p ==> holds v q <=> holds v (Ite p q True))`,
  REWRITE_TAC[holds] THEN CONV_TAC TAUT);;

let COND_CONV = GEN_REWRITE_CONV I [COND_CLAUSES];;
let AND_CONV = GEN_REWRITE_CONV I [TAUT `(F /\ a <=> F) /\ (T /\ a <=> a)`];;
let OR_CONV = GEN_REWRITE_CONV I [TAUT `(F \/ a <=> a) /\ (T \/ a <=> T)`];;

let rec COMPUTE_DEPTH_CONV conv tm =
  if is_cond tm then
   (RATOR_CONV(LAND_CONV(COMPUTE_DEPTH_CONV conv)) THENC
    COND_CONV THENC
    COMPUTE_DEPTH_CONV conv) tm
  else if is_conj tm then
   (LAND_CONV (COMPUTE_DEPTH_CONV conv) THENC
    AND_CONV THENC
    COMPUTE_DEPTH_CONV conv) tm
  else if is_disj tm then
   (LAND_CONV (COMPUTE_DEPTH_CONV conv) THENC
    OR_CONV THENC
    COMPUTE_DEPTH_CONV conv) tm
  else
   (SUB_CONV (COMPUTE_DEPTH_CONV conv) THENC
    TRY_CONV(conv THENC COMPUTE_DEPTH_CONV conv)) tm;;

g `!v. v 1 \/ v 2 \/ v 3 \/ v 4 \/ v 5 \/ v 6 \/
       ~v 1 \/ ~v 2 \/ ~v 3 \/ ~v 4 \/ ~v 5 \/ ~v 6`;;

e(MP_TAC HOLDS_BACK THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SPEC_TAC(`v:num->bool`,`v:num->bool`) THEN
  REWRITE_TAC[GSYM TAUTOLOGY; tautology]);;

time e (GEN_REWRITE_TAC COMPUTE_DEPTH_CONV [norm; taut; MEM; ARITH_EQ]);;

ignore(b()); time e (REWRITE_TAC[norm; taut; MEM; ARITH_EQ]);;
