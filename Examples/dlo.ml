(* ========================================================================= *)
(* Dense linear order decision procedure for reals, by Sean McLaughlin.      *)
(* ========================================================================= *)

prioritize_real();;

(* ---------------------------------------------------------------------- *)
(*  Util                                                                  *)
(* ---------------------------------------------------------------------- *)

let list_conj =
  let t_tm = `T` in
  fun l -> if l = [] then t_tm else end_itlist (curry mk_conj) l;;

let mk_lt = mk_binop `(<)`;;

(* ---------------------------------------------------------------------- *)
(*  cnnf                                                                  *)
(* ---------------------------------------------------------------------- *)

let DOUBLE_NEG_CONV =
  let dn_thm = TAUT `!x. ~(~ x) <=> x` in
  let dn_conv =
    fun tm ->
      let tm' = dest_neg (dest_neg tm) in
        ISPEC tm' dn_thm in
    dn_conv;;

let IMP_CONV =
  let i_thm = TAUT `!a b. (a ==> b) <=> (~a \/ b)` in
  let i_conv =
    fun tm ->
      let (a,b) = dest_imp tm in
        ISPECL [a;b] i_thm in
    i_conv;;

let BEQ_CONV =
  let beq_thm = TAUT `!a b. (a = b) <=> (a /\ b \/ ~a /\ ~b)` in
  let beq_conv =
    fun tm ->
      let (a,b) = dest_eq tm in
        ISPECL [a;b] beq_thm in
    beq_conv;;

let NEG_AND_CONV =
  let na_thm = TAUT `!a b. ~(a /\ b) <=> (~a \/ ~b)` in
  let na_conv =
    fun tm ->
      let (a,b) = dest_conj (dest_neg tm) in
        ISPECL [a;b] na_thm in
    na_conv;;

let NEG_OR_CONV =
  let no_thm = TAUT `!a b. ~(a \/ b) <=> (~a /\ ~b)` in
  let no_conv =
    fun tm ->
      let (a,b) = dest_disj (dest_neg tm) in
        ISPECL [a;b] no_thm in
    no_conv;;

let NEG_IMP_CONV =
  let ni_thm = TAUT `!a b. ~(a ==> b) <=> (a /\ ~b)` in
  let ni_conv =
    fun tm ->
      let (a,b) = dest_imp (dest_neg tm) in
        ISPECL [a;b] ni_thm in
    ni_conv;;

let NEG_BEQ_CONV =
  let nbeq_thm = TAUT `!a b. ~(a = b) <=> (a /\ ~b \/ ~a /\ b)` in
  let nbeq_conv =
    fun tm ->
      let (a,b) = dest_eq (dest_neg tm) in
        ISPECL [a;b] nbeq_thm in
    nbeq_conv;;


(* tm = (p /\ q0) \/ (~p /\ q1) *)
let dest_cases tm =
  try
    let (l,r) = dest_disj tm in
    let (p,q0) = dest_conj l in
    let (np,q1) = dest_conj r in
      if mk_neg p = np then (p,q0,q1) else failwith "not a cases term"
  with Failure _ -> failwith "not a cases term";;

let is_cases = can dest_cases;;

let CASES_CONV =
  let c_thm =
    TAUT `!p q0 q1. ~(p /\ q0 \/ ~p /\ q1) <=> (p /\ ~q0 \/ ~p /\ ~q1)` in
  let cc =
    fun tm ->
      let (p,q0,q1) = dest_cases tm in
        ISPECL [p;q0;q1] c_thm in
    cc;;

let QE_SIMPLIFY_CONV =
  let NOT_EXISTS_UNIQUE_THM = prove
   (`~(?!x. P x) <=> (!x. ~P x) \/ ?x x'. P x /\ P x' /\ ~(x = x')`,
    REWRITE_TAC[EXISTS_UNIQUE_THM; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; CONJ_ASSOC]) in
  let tauts =
    [TAUT `~(~p) <=> p`;
     TAUT `~(p /\ q) <=> ~p \/ ~q`;
     TAUT `~(p \/ q) <=> ~p /\ ~q`;
     TAUT `~(p ==> q) <=> p /\ ~q`;
     TAUT `p ==> q <=> ~p \/ q`;
     NOT_FORALL_THM;
     NOT_EXISTS_THM;
     EXISTS_UNIQUE_THM;
     NOT_EXISTS_UNIQUE_THM;
     TAUT `~(p = q) <=> (p /\ ~q) \/ (~p /\ q)`;
     TAUT `(p = q) <=> (p /\ q) \/ (~p /\ ~q)`;
     TAUT `~(p /\ q \/ ~p /\ r) <=> p /\ ~q \/ ~p /\ ~r`] in
  GEN_REWRITE_CONV TOP_SWEEP_CONV tauts;;

let CNNF_CONV =
  let refl_conj = REFL `(/\)`
  and refl_disj = REFL `(\/)` in
  fun lfn_conv ->
    let rec cnnf_conv tm =
      if is_conj tm  then
        let (p,q) = dest_conj tm in
        let thm1 = cnnf_conv p in
        let thm2 = cnnf_conv q in
          MK_COMB (MK_COMB (refl_conj,thm1),thm2)
      else if is_disj tm  then
        let (p,q) = dest_disj tm in
        let thm1 = cnnf_conv p in
        let thm2 = cnnf_conv q in
          MK_COMB (MK_COMB (refl_disj,thm1),thm2)
      else if is_imp tm then
        let (p,q) = dest_imp tm in
        let thm1 = cnnf_conv (mk_neg p) in
        let thm2 = cnnf_conv q in
          TRANS (IMP_CONV tm) (MK_COMB(MK_COMB(refl_disj,thm1),thm2))
      else if is_iff tm then
        let (p,q) = dest_eq tm in
        let pthm = cnnf_conv p in
        let qthm = cnnf_conv q in
        let npthm = cnnf_conv (mk_neg p) in
        let nqthm = cnnf_conv (mk_neg q) in
        let thm1 = MK_COMB(MK_COMB(refl_conj,pthm),qthm) in
        let thm2 = MK_COMB(MK_COMB(refl_conj,npthm),nqthm) in
          TRANS (BEQ_CONV tm) (MK_COMB(MK_COMB(refl_disj,thm1),thm2))
      else if is_neg tm then
        let tm' = dest_neg tm in
          if is_neg tm' then
            let tm'' = dest_neg tm' in
            let thm = cnnf_conv tm in
              TRANS (DOUBLE_NEG_CONV tm'') thm
          else if is_conj tm' then
            let (p,q) = dest_conj tm' in
            let thm1 = cnnf_conv (mk_neg p) in
            let thm2 = cnnf_conv (mk_neg q) in
              TRANS (NEG_AND_CONV tm) (MK_COMB(MK_COMB(refl_disj,thm1),thm2))
          else if is_cases tm' then
            let (p,q0,q1) = dest_cases tm in
            let thm1 = cnnf_conv (mk_conj(p,mk_neg q0)) in
            let thm2 = cnnf_conv (mk_conj(mk_neg p,mk_neg q1)) in
              TRANS (CASES_CONV tm) (MK_COMB(MK_COMB(refl_disj,thm1),thm2))
          else if is_disj tm' then
            let (p,q) = dest_disj tm' in
            let thm1 = cnnf_conv (mk_neg p) in
            let thm2 = cnnf_conv (mk_neg q) in
              TRANS (NEG_OR_CONV tm) (MK_COMB(MK_COMB(refl_conj,thm1),thm2))
          else if is_imp tm' then
            let (p,q) = dest_imp tm' in
            let thm1 = cnnf_conv p in
            let thm2 = cnnf_conv (mk_neg q) in
              TRANS (NEG_IMP_CONV tm) (MK_COMB(MK_COMB(refl_conj,thm1),thm2))
          else if is_iff tm' then
            let (p,q) = dest_eq tm' in
            let pthm = cnnf_conv p in
            let qthm = cnnf_conv q in
            let npthm = cnnf_conv (mk_neg p) in
            let nqthm = cnnf_conv (mk_neg q) in
            let thm1 = MK_COMB (MK_COMB(refl_conj,pthm),nqthm) in
            let thm2 = MK_COMB(MK_COMB(refl_conj,npthm),qthm) in
              TRANS (NEG_BEQ_CONV tm) (MK_COMB(MK_COMB(refl_disj,thm1),thm2))
          else lfn_conv tm
      else lfn_conv tm in
      QE_SIMPLIFY_CONV THENC cnnf_conv THENC QE_SIMPLIFY_CONV;;


(*

let tests = [
`~(a /\ b)`;
`~(a \/ b)`;
`~(a ==> b)`;
`~(a:bool <=> b)`;
`~ ~ a`;
];;

map (CNNF_CONV (fun x -> REFL x)) tests;;
*)


(* ---------------------------------------------------------------------- *)
(*  Real Lists                                                            *)
(* ---------------------------------------------------------------------- *)

let MINL = new_recursive_definition list_RECURSION
  `(MINL [] default = default) /\
   (MINL (CONS h t) default = min h (MINL t default))`;;

let MAXL = new_recursive_definition list_RECURSION
  `(MAXL [] default = default) /\
   (MAXL (CONS h t) default = max h (MAXL t default))`;;

let MAX_LT = prove
 (`!x y z. max x y < z <=> x < z /\ y < z`,
  REWRITE_TAC[real_max] THEN MESON_TAC[REAL_LET_TRANS; REAL_LE_TOTAL]);;

let MIN_GT = prove
 (`!x y z. x < real_min y z <=> x < y /\ x < z`,
  REWRITE_TAC[real_min] THEN MESON_TAC[REAL_LTE_TRANS; REAL_LE_TOTAL]);;

let ALL_LT_LEMMA = prove
 (`!left x lefts. ALL (\l. l < x) (CONS left lefts) <=> MAXL lefts left < x`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAXL; ALL] THEN
  SPEC_TAC(`t:real list`,`t:real list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; MAXL; MAX_LT] THEN ASM_MESON_TAC[MAX_LT]);;

let ALL_GT_LEMMA = prove
 (`!right x rights.
        ALL (\r. x < r) (CONS right rights) <=> x < MINL rights right`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MINL; ALL] THEN
  SPEC_TAC(`t:real list`,`t:real list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; MINL; MIN_GT] THEN ASM_MESON_TAC[MIN_GT]);;

(* ---------------------------------------------------------------------- *)
(*  Axioms                                                                *)
(* ---------------------------------------------------------------------- *)

let REAL_DENSE = prove
 (`!x y. x < y ==> ?z. x < z /\ z < y`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `(x + y) / &2` THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let REAL_LT_EXISTS = prove(`!x. ?y. x < y`,
  GEN_TAC THEN
  EXISTS_TAC `x + &1` THEN
  REAL_ARITH_TAC);;

let REAL_GT_EXISTS = prove(`!x. ?y. y < x`,
  GEN_TAC THEN
  EXISTS_TAC `x - &1` THEN
  REAL_ARITH_TAC);;

(* ---------------------------------------------------------------------- *)
(*  lfn_dlo                                                               *)
(* ---------------------------------------------------------------------- *)

let LFN_DLO_CONV =
  PURE_REWRITE_CONV[
    REAL_ARITH `~(s < t) <=> ((s = t) \/ (t < s))`;
    REAL_ARITH `~(s = t) <=> (s < t \/ t < s)`;
  ];;

(* ------------------------------------------------------------------------- *)
(* Proforma theorems to support the main inference step.                     *)
(* ------------------------------------------------------------------------- *)

let PROFORMA_LEFT = prove
 (`!l ls. (?x. ALL (\l. l < x) (CONS l ls)) <=> T`,
  REWRITE_TAC[ALL_LT_LEMMA] THEN MESON_TAC[REAL_LT_EXISTS]);;

let PROFORMA_RIGHT = prove
 (`!r rs. (?x. ALL (\r. x < r) (CONS r rs)) <=> T`,
  REWRITE_TAC[ALL_GT_LEMMA] THEN MESON_TAC[REAL_GT_EXISTS]);;

let PROFORMA_BOTH = prove
 (`!l ls r rs.
        (?x. ALL (\l. l < x) (CONS l ls) /\ ALL (\r. x < r) (CONS r rs)) <=>
        ALL (\l. ALL (\r. l < r) (CONS r rs)) (CONS l ls)`,
  REWRITE_TAC[ALL_LT_LEMMA; ALL_GT_LEMMA] THEN
  MESON_TAC[REAL_DENSE; REAL_LT_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Deal with ?x. <conjunction of strict inequalities all involving x>        *)
(* ------------------------------------------------------------------------- *)

let mk_rlist = let ty = `:real` in fun x -> mk_list(x,ty);;

let expand_all = PURE_REWRITE_RULE
  [ALL; BETA_THM; GSYM CONJ_ASSOC; TAUT `a /\ T <=> a`];;

let DLO_EQ_CONV fm =
  let x,p = dest_exists fm in
  let xl,xr = partition (fun t -> rand t = x) (conjuncts p) in
  let lefts = map lhand xl and rights = map rand xr in
  let th1 =
    if lefts = [] then SPECL [hd rights; mk_rlist(tl rights)] PROFORMA_RIGHT
    else if rights = [] then SPECL [hd lefts; mk_rlist(tl lefts)] PROFORMA_LEFT
    else SPECL [hd lefts; mk_rlist(tl lefts); hd rights; mk_rlist(tl rights)]
               PROFORMA_BOTH in
  let th2 = CONV_RULE (LAND_CONV(GEN_ALPHA_CONV x)) (expand_all th1) in
  let p' = snd(dest_exists(lhand(concl th2))) in
  let th3 = MK_EXISTS x (CONJ_ACI_RULE(mk_eq(p,p'))) in
  TRANS th3 th2;;

(* ------------------------------------------------------------------------- *)
(* Deal with general ?x. <conjunction of atoms>                              *)
(* ------------------------------------------------------------------------- *)

let eq_triv_conv =
  let pth_triv = prove
   (`((?x. x = x) <=> T) /\
     ((?x. x = t) <=> T) /\
     ((?x. t = x) <=> T) /\
     ((?x. (x = t) /\ P x) <=> P t) /\
     ((?x. (t = x) /\ P x) <=> P t)`,
    MESON_TAC[]) in
  GEN_REWRITE_CONV I [pth_triv]

and eq_refl_conv =
  let pth_refl = prove
   (`(?x. (x = x) /\ P x) <=> (?x. P x)`,
    MESON_TAC[]) in
  GEN_REWRITE_CONV I [pth_refl]

and lt_refl_conv =
  GEN_REWRITE_CONV DEPTH_CONV
   [REAL_LT_REFL; AND_CLAUSES; EXISTS_SIMP];;

let rec DLOBASIC_CONV fm =
  try let x,p = dest_exists fm in
      let cjs = conjuncts p in
      try let eq = find (fun e -> is_eq e && (lhs e = x || rhs e = x)) cjs in
          let cjs' = eq::setify(subtract cjs [eq]) in
          let p' = list_mk_conj cjs' in
          let th1 = MK_EXISTS x (CONJ_ACI_RULE(mk_eq(p,p'))) in
          let fm' = rand(concl th1) in
          try TRANS th1 (eq_triv_conv fm') with Failure _ ->
          TRANS th1 ((eq_refl_conv THENC DLOBASIC_CONV) fm')
      with Failure _ ->
          if mem (mk_lt x x) cjs then lt_refl_conv fm
          else DLO_EQ_CONV fm
  with Failure _ -> (print_qterm fm; failwith "dlobasic");;

(* ------------------------------------------------------------------------- *)
(* Overall quantifier elimination.                                           *)
(* ------------------------------------------------------------------------- *)

let AFN_DLO_CONV vars =
  PURE_REWRITE_CONV[
    REAL_ARITH `s <= t <=> ~(t < s)`;
    REAL_ARITH `s >= t <=> ~(s < t)`;
    REAL_ARITH `s > t <=> t < s`
  ];;

let dest_binop_op tm =
  try
    let f,r = dest_comb tm in
    let op,l = dest_comb f in
      (l,r,op)
  with Failure _ -> failwith "dest_binop_op";;

let forall_thm = prove(`!P. (!x. P x) <=> ~ (?x. ~ P x)`,MESON_TAC[])
and or_exists_conv = PURE_REWRITE_CONV[OR_EXISTS_THM]
and triv_exists_conv = REWR_CONV EXISTS_SIMP
and push_exists_conv = REWR_CONV RIGHT_EXISTS_AND_THM
and not_tm = `(~)`
and or_tm = `(\/)`
and t_tm = `T`
and f_tm = `F`;;

let LIFT_QELIM_CONV afn_conv nfn_conv qfn_conv =
  let rec qelift_conv vars fm =
    if fm = t_tm || fm = f_tm then REFL fm
    else if is_neg fm then
      let thm1 = qelift_conv vars (dest_neg fm) in
        MK_COMB(REFL not_tm,thm1)
    else if is_conj fm || is_disj fm || is_imp fm || is_iff fm then
      let (p,q,op) = dest_binop_op fm in
      let thm1 = qelift_conv vars p in
      let thm2 = qelift_conv vars q in
        MK_COMB(MK_COMB((REFL op),thm1),thm2)
    else if is_forall fm then
      let (x,p) = dest_forall fm in
      let nex_thm = BETA_RULE (ISPEC (mk_abs(x,p)) forall_thm) in
      let elim_thm = qelift_conv vars (mk_exists(x,mk_neg p)) in
        TRANS nex_thm (MK_COMB (REFL not_tm,elim_thm))
    else if is_exists fm then
      let (x,p) = dest_exists fm in
      let thm1 = qelift_conv (x::vars) p in
      let thm1a = MK_EXISTS x thm1 in
      let thm2 = nfn_conv (rhs(concl thm1)) in
      let thm2a = MK_EXISTS x thm2 in
      let djs = disjuncts (rhs (concl thm2)) in
      let djthms = map (qelim x vars) djs in
      let thm3 = end_itlist
        (fun thm1 thm2 -> MK_COMB(MK_COMB (REFL or_tm,thm1),thm2)) djthms in
      let split_ex_thm = GSYM (or_exists_conv (lhs (concl thm3))) in
      let thm3a = TRANS split_ex_thm thm3 in
        TRANS (TRANS thm1a thm2a) thm3a
    else
      afn_conv vars fm
  and qelim x vars p =
    let cjs = conjuncts p in
    let ycjs,ncjs = partition (mem x o frees) cjs in
    if ycjs = [] then triv_exists_conv(mk_exists(x,p))
    else if ncjs = [] then qfn_conv vars (mk_exists(x,p)) else
    let th1 = CONJ_ACI_RULE
     (mk_eq(p,mk_conj(list_mk_conj ncjs,list_mk_conj ycjs))) in
    let th2 = CONV_RULE (RAND_CONV push_exists_conv) (MK_EXISTS x th1) in
    let t1,t2 = dest_comb (rand(concl th2)) in
    TRANS th2 (AP_TERM t1 (qfn_conv vars t2)) in
  fun fm -> ((qelift_conv (frees fm)) THENC QE_SIMPLIFY_CONV) fm;;

let QELIM_DLO_CONV =
  (LIFT_QELIM_CONV AFN_DLO_CONV ((CNNF_CONV LFN_DLO_CONV) THENC DNF_CONV)
    (fun v -> DLOBASIC_CONV)) THENC (REWRITE_CONV[]);;

(* ---------------------------------------------------------------------- *)
(*  Test                                                                  *)
(* ---------------------------------------------------------------------- *)

let tests = [
  `!x y. ?z. z < x /\ z < y`;
  `?z. x < x /\ z < y`;
  `?z. x < z /\ z < y`;
  `!x. x < a ==> x < b`;
  `!a b. (!x. (x < a) <=> (x < b)) <=> (a = b)`; (* long time *)
  `!x. ?y. x < y`;
  `!x y z. x < y /\ y < z ==> x < z`;
  `!x y. x < y \/ (x = y) \/ y < x`;
  `!x y. x < y \/ (x = y) \/ y < x`;
  `?x y. x < y /\ y < x`;
  `!x y. ?z. z < x /\ x < y`;
  `!x y. ?z. z < x /\ z < y`;
  `!x y. x < y ==> ?z. x < z /\ z < y`;
  `!x y. ~(x = y) ==> ?u. u < x /\ (y < u \/ x < y)`;
  `?x. x = x:real`;
  `?x.(x = x) /\ (x = y)`;
  `?z. x < z /\ z < y`;
  `?z. x <= z /\ z <= y`;
  `?z. x < z /\ z <= y`;
  `!x y z. ?u. u < x /\ u < y /\ u < z`;
  `!y. x < y /\ y < z ==> w < z`;
  `!x y . x < y`;
  `?z. z < x /\ x < y`;
  `!a b. (!x. x < a ==> x < b) <=> (a <= b)`;
  `!x. x < a ==> x < b`;
  `!x. x < a ==> x <= b`;
  `!a b. ?x. ~(x = a) \/ ~(x = b) \/ (a = b:real)`;
  `!x y. x <= y \/ x > y`;
  `!x y. x <= y \/ x < y`
];;

map (time QELIM_DLO_CONV) tests;;
