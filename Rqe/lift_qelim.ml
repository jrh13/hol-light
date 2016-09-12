let ACI_CONJ =
  let rec build ths tm =
    if is_conj tm then
      let l,r = dest_conj tm in CONJ (build ths l) (build ths r)
    else find (fun th -> concl th = tm) ths in
    fun p p' ->
      let cjs = CONJUNCTS(ASSUME p) and cjs' = CONJUNCTS(ASSUME p') in
      let th = build cjs p' and th' = build cjs' p in
        IMP_ANTISYM_RULE (DISCH_ALL th) (DISCH_ALL th');;

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
     TAUT `~(p <=> q) <=> (p /\ ~q) \/ (~p /\ q)`;
     TAUT `(p <=> q) <=> (p /\ q) \/ (~p /\ ~q)`;
     TAUT `~(p /\ q \/ ~p /\ r) <=> p /\ ~q \/ ~p /\ ~r`] in
  GEN_REWRITE_CONV TOP_SWEEP_CONV tauts;;

let OR_ASSOC = TAUT `(a \/ b) \/ c <=> a \/ b \/ c`;; 
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
      let (op,p,q) = get_binop fm in
      let thm1 = qelift_conv vars p in
      let thm2 = qelift_conv vars q in
        MK_COMB(MK_COMB((REFL op),thm1),thm2)
    else if is_forall fm then
      let (x,p) = dest_forall fm in
      let nex_thm = BETA_RULE (ISPEC (mk_abs(x,p)) forall_thm) in
      let nex_thm' = CONV_RULE (LAND_CONV (RAND_CONV (ALPHA_CONV x))) nex_thm in
      let nex_thm'' = CONV_RULE (RAND_CONV (RAND_CONV (RAND_CONV (ALPHA_CONV x)))) nex_thm' in
      let elim_thm = qelift_conv vars (mk_exists(x,mk_neg p)) in
        TRANS nex_thm'' (MK_COMB (REFL not_tm,elim_thm))
    else if is_exists fm then
      let (x,p) = dest_exists fm in
      let thm1 = qelift_conv (x::vars) p in
      let thm1a = MK_EXISTS x thm1 in
      let thm1b = PURE_REWRITE_RULE[OR_ASSOC] thm1a in
      let thm2 = nfn_conv (rhs(concl thm1)) in
      let thm2a = MK_EXISTS x thm2 in
      let thm2b = PURE_REWRITE_RULE[OR_ASSOC] thm2a in
      let djs = disjuncts (rhs (concl thm2)) in
      let djthms = map (qelim x vars) djs in
      let thm3 = end_itlist
        (fun thm1 thm2 -> MK_COMB(MK_COMB (REFL or_tm,thm1),thm2)) djthms in
      let split_ex_thm = GSYM (or_exists_conv (lhs (concl thm3))) in
      let thm3a = TRANS split_ex_thm thm3 in
        TRANS (TRANS thm1b thm2b) thm3a
    else
      afn_conv vars fm
  and qelim x vars p =
    let cjs = conjuncts p in
    let ycjs,ncjs = partition (mem x o frees) cjs in
    if ycjs = [] then triv_exists_conv(mk_exists(x,p))
    else if ncjs = [] then qfn_conv vars (mk_exists(x,p)) else
    let th1 = ACI_CONJ p (mk_conj(list_mk_conj ncjs,list_mk_conj ycjs)) in
    let th2 = CONV_RULE (RAND_CONV push_exists_conv) (MK_EXISTS x th1) in
    let t1,t2 = dest_comb (rand(concl th2)) in
    TRANS th2 (AP_TERM t1 (qfn_conv vars t2)) in
  fun fm -> ((qelift_conv (frees fm)) THENC QE_SIMPLIFY_CONV) fm;;



(*
let afn_conv,nfn_conv,qfn_conv = POLYATOM_CONV,(EVALC_CONV THENC SIMPLIFY_CONV),BASIC_REAL_QELIM_CONV 
let LIFT_QELIM_CONV afn_conv nfn_conv qfn_conv = 
  fun fm -> ((qelift_conv (frees fm)) THENC QE_SIMPLIFY_CONV) fm;;


let k0 = (TRANS thm1a thm2a)
let k1 = thm3a
let k2 = CONV_RULE (LAND_CONV (RAND_CONV (ALPHA_CONV `x:real`))) k1
TRANS k0 k2 


let vars = []
let fm,vars = !lqc_fm,!lqc_vars
let fm = `?x y z. x * y * z < &0`
let p = `~((&0 + y * (&0 + x * &1) = &0) <=> (&0 + x * &1 = &0) \/ (&0 + y * &1 = &0))`
#trace qelift_conv
#trace qelim



TRANS (ASSUME `T <=> (?x. x * y > &0)`) (ASSUME `(?z. z * y > &0) <=> F`)

MATCH_TRANS (ASSUME `T <=> (?x. x * y > &0)`) (ASSUME `?z. z * y > &0 <=> F`)
MATCH_EQ_MP (ASSUME `(?x. x * y > &0) <=> F`) (ASSUME `?z. z * y > &0`)

qelift_conv vars fm


let fm = `?x y. x * y = &0`
let fm = `!y. (x * y = &0) <=> (x = &0) \/ (y = &0)`
let fm = `?y. (x * y = &0) <=> (x = &0) \/ (y = &0)`
let fm = `?y. ~ ((x * y = &0) <=> (x = &0) \/ (y = &0))`
let fm = `?x. ~(!y. (x * y = &0) <=> (x = &0) \/ (y = &0))`
let vars = [ry;rx]
let vars = [rx]

let QELIM_DLO_CONV =
  (LIFT_QELIM_CONV AFN_DLO_CONV ((CNNF_CONV LFN_DLO_CONV) THENC DNF_CONV)
    (fun v -> DLOBASIC_CONV)) THENC (REWRITE_CONV[]);;
*)
